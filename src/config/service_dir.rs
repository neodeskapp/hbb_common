//! The Windows service's own folder (L442): `%ProgramData%\<app name>`, which
//! only SYSTEM and Administrators can open. The service's processes run as
//! LocalSystem, whose profile Windows replaces on feature updates, so their
//! config lived in the LocalService profile, which every service running as
//! LOCAL SERVICE can read. The first of the service's processes that needs
//! its config moves it from there.

use std::{
    fs, io,
    path::{Path, PathBuf},
};

use crate::log;

/// The folder in `root` that holds the service's config.
const CONFIG: &str = "config";
/// Where a move copies the config to before it renames it to [`CONFIG`].
const MOVING: &str = "config.moving";
/// The file in the service's folder that one move at a time holds open.
#[cfg(windows)]
const MOVE_LOCK: &str = "move.lock";

/// Log lines of the move, kept until the logger runs: the first process of
/// the service moves its config while its logger asks for its log folder.
static NOTES: std::sync::Mutex<Vec<(log::Level, String)>> = std::sync::Mutex::new(Vec::new());

fn note(level: log::Level, message: String) {
    if level <= log::max_level() {
        log::log!(level, "{message}");
    } else {
        NOTES
            .lock()
            .unwrap_or_else(|err| err.into_inner())
            .push((level, message));
    }
}

/// Writes the kept log lines once the logger runs (L487).
pub(super) fn flush_notes() {
    if log::max_level() == log::LevelFilter::Off {
        return;
    }
    let notes = std::mem::take(&mut *NOTES.lock().unwrap_or_else(|err| err.into_inner()));
    for (level, message) in notes {
        log::log!(level, "{message}");
    }
}

/// Whether `config_dir` is a config folder in LocalSystem's profile, the
/// folder the service's processes get from Windows.
pub(super) fn is_system_profile(config_dir: &Path) -> bool {
    config_dir
        .to_string_lossy()
        .to_lowercase()
        .contains("\\system32\\config\\systemprofile\\")
}

/// The service's config folder, for a process of the service whose config
/// was kept in `old_dir` so far. The first call in a process makes
/// `%ProgramData%\<app_name>` a folder only SYSTEM and Administrators can
/// open and moves the config there; when that fails, the service keeps its
/// config in `old_dir` this time.
#[cfg(windows)]
pub(super) fn config_dir(app_name: &str, old_dir: PathBuf) -> PathBuf {
    static DIRS: std::sync::Mutex<Vec<(String, PathBuf)>> = std::sync::Mutex::new(Vec::new());
    let mut dirs = DIRS.lock().unwrap_or_else(|err| err.into_inner());
    if let Some((_, dir)) = dirs.iter().find(|(name, _)| name == app_name) {
        flush_notes();
        return dir.clone();
    }
    let root = program_data().join(app_name);
    let dir = match prepare(&root, &old_dir) {
        Ok(dir) => dir,
        Err(err) => {
            note(
                log::Level::Error,
                format!(
                    "The service keeps its config in {}, {} could not take it: {err}",
                    old_dir.display(),
                    root.display()
                ),
            );
            old_dir
        }
    };
    dirs.push((app_name.to_owned(), dir.clone()));
    flush_notes();
    dir
}

#[cfg(windows)]
fn program_data() -> PathBuf {
    std::env::var_os("ProgramData")
        .map(PathBuf::from)
        .filter(|path| path.is_absolute())
        .unwrap_or_else(|| PathBuf::from(r"C:\ProgramData"))
}

#[cfg(windows)]
fn prepare(root: &Path, old_dir: &Path) -> io::Result<PathBuf> {
    secure::make_root(root)?;
    let lock = lock(root)?;
    let moved = move_config(old_dir, root);
    drop(lock);
    // A process still waiting for the lock makes the file again
    fs::remove_file(root.join(MOVE_LOCK)).ok();
    moved
}

/// Holds `root\move.lock` open without sharing, so one process of the
/// service moves the config at a time.
#[cfg(windows)]
fn lock(root: &Path) -> io::Result<fs::File> {
    use std::os::windows::fs::OpenOptionsExt;
    const ERROR_SHARING_VIOLATION: i32 = 32;
    let path = root.join(MOVE_LOCK);
    for _ in 0..300 {
        match fs::OpenOptions::new()
            .write(true)
            .create(true)
            .share_mode(0)
            .open(&path)
        {
            Err(err) if err.raw_os_error() == Some(ERROR_SHARING_VIOLATION) => {
                std::thread::sleep(std::time::Duration::from_millis(100));
            }
            result => return result,
        }
    }
    Err(io::Error::new(
        io::ErrorKind::TimedOut,
        "another process of the service holds the move lock",
    ))
}

/// Moves the config folder `old_dir` into `root` once and returns the
/// config folder in `root`. The move copies `old_dir` to `root\config.moving`,
/// renames that to `root\config` and then removes `old_dir`, so
/// `root\config` exists only once it holds the whole config. A `root\config`
/// that exists is the service's config already. When the copy fails, the
/// config stays in `old_dir` (Err).
pub(super) fn move_config(old_dir: &Path, root: &Path) -> io::Result<PathBuf> {
    move_config_with(old_dir, root, &|from, to| fs::copy(from, to).map(|_| ()))
}

/// [`move_config`] with `copy` for each file.
fn move_config_with(old_dir: &Path, root: &Path, copy: &CopyFile) -> io::Result<PathBuf> {
    let dir = root.join(CONFIG);
    if dir.is_dir() {
        // A move whose removal of the old folder failed
        remove_old(old_dir);
        return Ok(dir);
    }
    if !old_dir.is_dir() {
        fs::create_dir_all(&dir)?;
        return Ok(dir);
    }
    let moving = root.join(MOVING);
    if moving.exists() {
        fs::remove_dir_all(&moving)?;
    }
    if let Err(err) = copy_tree(old_dir, &moving, copy) {
        fs::remove_dir_all(&moving).ok();
        return Err(err);
    }
    fs::rename(&moving, &dir)?;
    note(
        log::Level::Info,
        format!(
            "Moved the service's config from {} to {}",
            old_dir.display(),
            dir.display()
        ),
    );
    remove_old(old_dir);
    Ok(dir)
}

fn remove_old(old_dir: &Path) {
    if old_dir.exists() {
        if let Err(err) = fs::remove_dir_all(old_dir) {
            note(
                log::Level::Error,
                format!(
                    "The service's old config folder {} stays: {err}",
                    old_dir.display()
                ),
            );
        }
    }
}

type CopyFile = dyn Fn(&Path, &Path) -> io::Result<()>;

/// Copies the files and folders in `from` to the new folder `to` with
/// `copy`, leaving out links.
fn copy_tree(from: &Path, to: &Path, copy: &CopyFile) -> io::Result<()> {
    fs::create_dir(to)?;
    for entry in fs::read_dir(from)? {
        let entry = entry?;
        let file_type = entry.file_type()?;
        let target = to.join(entry.file_name());
        if file_type.is_dir() {
            copy_tree(&entry.path(), &target, copy)?;
        } else if file_type.is_file() {
            copy(&entry.path(), &target)?;
        }
    }
    Ok(())
}

#[cfg(windows)]
mod secure {
    use super::*;
    use std::{ffi::OsStr, mem, os::windows::ffi::OsStrExt, ptr};
    use winapi::{
        shared::{
            minwindef::{DWORD, FALSE, LPVOID},
            sddl::{ConvertStringSecurityDescriptorToSecurityDescriptorW, SDDL_REVISION_1},
            winerror::ERROR_SUCCESS,
        },
        um::{
            accctrl::SE_FILE_OBJECT,
            aclapi::GetSecurityInfo,
            fileapi::{
                CreateDirectoryW, CreateFileW, GetFileInformationByHandle,
                BY_HANDLE_FILE_INFORMATION, OPEN_EXISTING,
            },
            handleapi::{CloseHandle, INVALID_HANDLE_VALUE},
            minwinbase::SECURITY_ATTRIBUTES,
            securitybaseapi::{GetAce, GetAclInformation, IsWellKnownSid},
            winbase::{LocalFree, FILE_FLAG_BACKUP_SEMANTICS, FILE_FLAG_OPEN_REPARSE_POINT},
            winnt::{
                AclSizeInformation, WinBuiltinAdministratorsSid, WinLocalSystemSid,
                ACCESS_ALLOWED_ACE, ACCESS_ALLOWED_ACE_TYPE, ACCESS_DENIED_ACE_TYPE, ACE_HEADER,
                ACL_SIZE_INFORMATION, DACL_SECURITY_INFORMATION, FILE_ATTRIBUTE_DIRECTORY,
                FILE_ATTRIBUTE_REPARSE_POINT, FILE_SHARE_READ, FILE_SHARE_WRITE, HANDLE,
                OWNER_SECURITY_INFORMATION, PACL, PSECURITY_DESCRIPTOR, PSID, READ_CONTROL,
            },
        },
    };

    /// Full control for SYSTEM and Administrators, inherited by everything
    /// in the folder, and nothing inherited from its parent.
    const SDDL: &str = "D:P(A;OICI;FA;;;SY)(A;OICI;FA;;;BA)";

    /// Makes `root` a folder only SYSTEM and Administrators can open. A
    /// folder or link at that path this did not make (another owner, a DACL
    /// that lets others in, a reparse point) is moved aside first, so
    /// nothing another account put there stays in use.
    pub(super) fn make_root(root: &Path) -> io::Result<()> {
        for _ in 0..3 {
            match fs::symlink_metadata(root) {
                Err(err) if err.kind() == io::ErrorKind::NotFound => {
                    match create_protected_dir(root) {
                        Ok(()) => return Ok(()),
                        Err(err) if err.kind() == io::ErrorKind::AlreadyExists => continue,
                        Err(err) => return Err(err),
                    }
                }
                Err(err) => return Err(err),
                Ok(_) => {
                    if is_protected_dir(root) {
                        return Ok(());
                    }
                    let aside = aside_path(root);
                    let message = format!(
                        "{} is open to other accounts than SYSTEM and Administrators; it moves to {} and the service starts a folder of its own",
                        root.display(),
                        aside.display()
                    );
                    note(log::Level::Warn, message.clone());
                    fs::rename(root, &aside)?;
                    // An administrator sees it in the Application log too
                    let source = root
                        .file_name()
                        .map(|name| name.to_string_lossy().into_owned())
                        .unwrap_or_default();
                    if !crate::platform::windows::write_application_event(
                        &source, true, 1, &message,
                    ) {
                        note(
                            log::Level::Error,
                            "Could not write the move aside to the Application log".to_owned(),
                        );
                    }
                }
            }
        }
        Err(io::Error::new(
            io::ErrorKind::Other,
            "another account keeps making the folder",
        ))
    }

    fn aside_path(root: &Path) -> PathBuf {
        let name = root
            .file_name()
            .map(|name| name.to_string_lossy().into_owned())
            .unwrap_or_default();
        let time = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .map(|time| time.as_secs())
            .unwrap_or_default();
        root.with_file_name(format!("{name}.untrusted-{time}"))
    }

    fn wide(path: &Path) -> Vec<u16> {
        OsStr::new(path).encode_wide().chain(Some(0)).collect()
    }

    struct Handle(HANDLE);

    impl Drop for Handle {
        fn drop(&mut self) {
            unsafe { CloseHandle(self.0) };
        }
    }

    /// Memory Windows allocated with LocalAlloc.
    struct Local(LPVOID);

    impl Drop for Local {
        fn drop(&mut self) {
            if !self.0.is_null() {
                unsafe { LocalFree(self.0) };
            }
        }
    }

    fn create_protected_dir(root: &Path) -> io::Result<()> {
        let sddl: Vec<u16> = OsStr::new(SDDL).encode_wide().chain(Some(0)).collect();
        let mut descriptor: PSECURITY_DESCRIPTOR = ptr::null_mut();
        let ok = unsafe {
            ConvertStringSecurityDescriptorToSecurityDescriptorW(
                sddl.as_ptr(),
                SDDL_REVISION_1 as DWORD,
                &mut descriptor,
                ptr::null_mut(),
            )
        };
        if ok == 0 || descriptor.is_null() {
            return Err(io::Error::last_os_error());
        }
        let _descriptor = Local(descriptor);
        let mut attributes = SECURITY_ATTRIBUTES {
            nLength: mem::size_of::<SECURITY_ATTRIBUTES>() as DWORD,
            lpSecurityDescriptor: descriptor,
            bInheritHandle: FALSE,
        };
        if unsafe { CreateDirectoryW(wide(root).as_ptr(), &mut attributes) } == 0 {
            return Err(io::Error::last_os_error());
        }
        Ok(())
    }

    /// Whether `root` is a folder, not a reparse point, owned by SYSTEM or
    /// Administrators, whose DACL lets no one else in. Read through one
    /// handle that does not follow reparse points.
    fn is_protected_dir(root: &Path) -> bool {
        let handle = unsafe {
            CreateFileW(
                wide(root).as_ptr(),
                READ_CONTROL,
                FILE_SHARE_READ | FILE_SHARE_WRITE,
                ptr::null_mut(),
                OPEN_EXISTING,
                FILE_FLAG_BACKUP_SEMANTICS | FILE_FLAG_OPEN_REPARSE_POINT,
                ptr::null_mut(),
            )
        };
        if handle == INVALID_HANDLE_VALUE {
            return false;
        }
        let handle = Handle(handle);
        let mut info: BY_HANDLE_FILE_INFORMATION = unsafe { mem::zeroed() };
        if unsafe { GetFileInformationByHandle(handle.0, &mut info) } == 0 {
            return false;
        }
        if info.dwFileAttributes & FILE_ATTRIBUTE_REPARSE_POINT != 0
            || info.dwFileAttributes & FILE_ATTRIBUTE_DIRECTORY == 0
        {
            return false;
        }
        let mut owner: PSID = ptr::null_mut();
        let mut dacl: PACL = ptr::null_mut();
        let mut descriptor: PSECURITY_DESCRIPTOR = ptr::null_mut();
        let rc = unsafe {
            GetSecurityInfo(
                handle.0,
                SE_FILE_OBJECT,
                OWNER_SECURITY_INFORMATION | DACL_SECURITY_INFORMATION,
                &mut owner,
                ptr::null_mut(),
                &mut dacl,
                ptr::null_mut(),
                &mut descriptor,
            )
        };
        if rc != ERROR_SUCCESS {
            return false;
        }
        let _descriptor = Local(descriptor);
        is_system_or_admins(owner) && dacl_lets_only_system_and_admins_in(dacl)
    }

    fn is_system_or_admins(sid: PSID) -> bool {
        !sid.is_null()
            && unsafe {
                IsWellKnownSid(sid, WinLocalSystemSid) != 0
                    || IsWellKnownSid(sid, WinBuiltinAdministratorsSid) != 0
            }
    }

    /// No DACL at all lets everyone in.
    fn dacl_lets_only_system_and_admins_in(dacl: PACL) -> bool {
        if dacl.is_null() {
            return false;
        }
        let mut size: ACL_SIZE_INFORMATION = unsafe { mem::zeroed() };
        let ok = unsafe {
            GetAclInformation(
                dacl,
                &mut size as *mut ACL_SIZE_INFORMATION as LPVOID,
                mem::size_of::<ACL_SIZE_INFORMATION>() as DWORD,
                AclSizeInformation,
            )
        };
        if ok == 0 {
            return false;
        }
        (0..size.AceCount).all(|index| {
            let mut ace: LPVOID = ptr::null_mut();
            if unsafe { GetAce(dacl, index, &mut ace) } == 0 || ace.is_null() {
                return false;
            }
            match unsafe { (*(ace as *const ACE_HEADER)).AceType } {
                ACCESS_ALLOWED_ACE_TYPE => {
                    let sid = unsafe { &(*(ace as *const ACCESS_ALLOWED_ACE)).SidStart }
                        as *const DWORD as PSID;
                    is_system_or_admins(sid)
                }
                ACCESS_DENIED_ACE_TYPE => true,
                _ => false,
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn temp_root(name: &str) -> PathBuf {
        let root =
            std::env::temp_dir().join(format!("neodesk-service-dir-{name}-{}", std::process::id()));
        fs::remove_dir_all(&root).ok();
        fs::create_dir_all(&root).unwrap();
        root
    }

    #[test]
    fn only_the_config_folder_of_localsystem_s_profile_is_the_service_s() {
        assert!(is_system_profile(Path::new(
            r"C:\Windows\System32\config\systemprofile\AppData\Roaming\NeoDesk Client\config"
        )));
        assert!(!is_system_profile(Path::new(
            r"C:\Users\tester\AppData\Roaming\NeoDesk Client\config"
        )));
        assert!(!is_system_profile(Path::new(
            r"C:\Windows\ServiceProfiles\LocalService\AppData\Roaming\NeoDesk Client\config"
        )));
    }

    #[test]
    fn the_config_moves_once_with_everything_in_it() {
        let base = temp_root("move");
        let old = base.join("old").join("config");
        fs::create_dir_all(old.join("peers")).unwrap();
        fs::write(old.join("NeoDesk Client.toml"), b"enc_id = 'x'").unwrap();
        fs::write(old.join("NeoDesk Client_local.toml"), b"token").unwrap();
        fs::write(old.join("peers").join("123.toml"), b"peer").unwrap();
        let root = base.join("root");
        fs::create_dir_all(&root).unwrap();

        let dir = move_config(&old, &root).unwrap();
        assert_eq!(dir, root.join(CONFIG));
        assert_eq!(
            fs::read(dir.join("NeoDesk Client.toml")).unwrap(),
            b"enc_id = 'x'"
        );
        assert_eq!(
            fs::read(dir.join("NeoDesk Client_local.toml")).unwrap(),
            b"token"
        );
        assert_eq!(
            fs::read(dir.join("peers").join("123.toml")).unwrap(),
            b"peer"
        );
        assert!(!old.exists(), "the old folder stayed");
        assert!(!root.join(MOVING).exists());

        // Later starts use the moved config and never move again
        fs::write(dir.join("NeoDesk Client.toml"), b"changed").unwrap();
        fs::create_dir_all(&old).unwrap();
        fs::write(old.join("NeoDesk Client.toml"), b"stale").unwrap();
        assert_eq!(move_config(&old, &root).unwrap(), dir);
        assert_eq!(
            fs::read(dir.join("NeoDesk Client.toml")).unwrap(),
            b"changed"
        );
        assert!(!old.exists(), "a stale old folder stayed");
        fs::remove_dir_all(&base).ok();
    }

    #[test]
    fn a_fresh_install_gets_an_empty_config_folder() {
        let base = temp_root("fresh");
        let root = base.join("root");
        fs::create_dir_all(&root).unwrap();
        let dir = move_config(&base.join("missing"), &root).unwrap();
        assert!(dir.is_dir());
        assert_eq!(fs::read_dir(&dir).unwrap().count(), 0);
        fs::remove_dir_all(&base).ok();
    }

    #[test]
    fn an_unfinished_move_leaves_the_config_where_it_was() {
        let base = temp_root("unfinished");
        let old = base.join("old");
        fs::create_dir_all(&old).unwrap();
        fs::write(old.join("NeoDesk Client.toml"), b"enc_id = 'x'").unwrap();
        let root = base.join("root");
        fs::create_dir_all(&root).unwrap();
        // A copy a crash left behind is made again from the old folder
        fs::create_dir_all(root.join(MOVING)).unwrap();
        fs::write(root.join(MOVING).join("partial"), b"").unwrap();

        // A root the move cannot write to keeps the config where it was
        let blocked = base.join("blocked");
        fs::write(&blocked, b"a file, not a folder").unwrap();
        assert!(move_config(&old, &blocked).is_err());
        assert!(old.join("NeoDesk Client.toml").exists());
        assert!(!blocked.join(CONFIG).exists());

        let dir = move_config(&old, &root).unwrap();
        assert!(dir.join("NeoDesk Client.toml").exists());
        assert!(
            !dir.join("partial").exists(),
            "a partial copy went into the config"
        );
        fs::remove_dir_all(&base).ok();
    }

    #[test]
    fn a_copy_that_fails_halfway_leaves_the_config_where_it_was() {
        let base = temp_root("halfway");
        let old = base.join("old");
        fs::create_dir_all(&old).unwrap();
        fs::write(old.join("NeoDesk Client.toml"), b"enc_id = 'x'").unwrap();
        fs::write(old.join("NeoDesk Client2.toml"), b"options").unwrap();
        let root = base.join("root");
        fs::create_dir_all(&root).unwrap();

        // The copy of one file fails, as on a full disk
        let copy = |from: &Path, to: &Path| {
            if from.ends_with("NeoDesk Client2.toml") {
                Err(io::Error::new(io::ErrorKind::Other, "no space left"))
            } else {
                fs::copy(from, to).map(|_| ())
            }
        };
        let moved = move_config_with(&old, &root, &copy);
        assert!(moved.is_err(), "a partial copy became the config");
        assert!(!root.join(CONFIG).exists());
        assert!(!root.join(MOVING).exists());
        assert!(old.join("NeoDesk Client.toml").exists());
        assert!(old.join("NeoDesk Client2.toml").exists());
        fs::remove_dir_all(&base).ok();
    }

    #[cfg(unix)]
    #[test]
    fn links_in_the_old_folder_are_not_followed() {
        let base = temp_root("links");
        let old = base.join("old");
        fs::create_dir_all(&old).unwrap();
        let outside = base.join("outside");
        fs::create_dir_all(&outside).unwrap();
        fs::write(outside.join("secret"), b"not the service's").unwrap();
        std::os::unix::fs::symlink(&outside, old.join("link")).unwrap();
        std::os::unix::fs::symlink(outside.join("secret"), old.join("file-link")).unwrap();
        let root = base.join("root");
        fs::create_dir_all(&root).unwrap();
        let dir = move_config(&old, &root).unwrap();
        assert!(!dir.join("link").exists());
        assert!(!dir.join("file-link").exists());
        assert!(
            outside.join("secret").exists(),
            "the move removed a file it linked to"
        );
        fs::remove_dir_all(&base).ok();
    }
}
