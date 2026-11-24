use std::{
    collections::{HashMap, HashSet},
    fs,
    io::{Read, Write},
    net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr},
    ops::{Deref, DerefMut},
    path::{Path, PathBuf},
    sync::{Mutex, RwLock},
    time::{Duration, Instant, SystemTime},
};

use anyhow::{anyhow, Result};
use bytes::Bytes;
use rand::Rng;
use regex::Regex;
use serde as de;
use serde_derive::{Deserialize, Serialize};
use serde_json;
use sodiumoxide::base64;
use sodiumoxide::crypto::sign;

mod permanent_password;
#[cfg(any(windows, test))]
mod service_dir;

pub use permanent_password::{
    compute_permanent_password_h1, decode_permanent_password_h1_from_storage,
    decode_preset_password_h1_from_storage, local_permanent_password_storage_is_usable_for_auth,
    preset_permanent_password_storage_is_usable_for_auth, ENCRYPT_MAX_LEN,
};
use permanent_password::{
    decode_permanent_password_h1_from_hashed_storage, decrypt_permanent_password_str_or_original,
    encode_permanent_password_encrypted_storage_from_h1, password_is_empty_or_not_hashed,
    preset_permanent_password_storage_matches_plain, DEFAULT_SALT_LEN, PASSWORD_ENC_VERSION,
};

use crate::{
    compress::{compress, decompress},
    log,
    password_security::{
        decrypt_str_or_original, decrypt_vec_or_original, encrypt_str_or_original,
        encrypt_vec_or_original, symmetric_crypt,
    },
};

pub const RENDEZVOUS_TIMEOUT: u64 = 12_000;
pub const CONNECT_TIMEOUT: u64 = 18_000;
pub const READ_TIMEOUT: u64 = 18_000;
// https://github.com/quic-go/quic-go/issues/525#issuecomment-294531351
// https://datatracker.ietf.org/doc/html/draft-hamilton-early-deployment-quic-00#section-6.10
// 15 seconds is recommended by quic, though oneSIP recommend 25 seconds,
// https://www.onsip.com/voip-resources/voip-fundamentals/what-is-nat-keepalive
pub const REG_INTERVAL: i64 = 15_000;
pub const COMPRESS_LEVEL: i32 = 3;
const SERIAL: i32 = 3;

#[cfg(target_os = "macos")]
lazy_static::lazy_static! {
    pub static ref ORG: RwLock<String> = RwLock::new("sk.neode".to_owned());
}

type Size = (i32, i32, i32, i32);
type KeyPair = (Vec<u8>, Vec<u8>);

lazy_static::lazy_static! {
    static ref CONFIG: RwLock<Config> = RwLock::new(Config::load());
    static ref CONFIG2: RwLock<Config2> = RwLock::new(Config2::load());
    static ref LOCAL_CONFIG: RwLock<LocalConfig> = RwLock::new(LocalConfig::load());
    static ref STATUS: RwLock<Status> = RwLock::new(Status::load());
    static ref TRUSTED_DEVICES: RwLock<(Vec<TrustedDevice>, bool)> = Default::default();
    static ref ONLINE: Mutex<HashMap<String, i64>> = Default::default();
    pub static ref PROD_RENDEZVOUS_SERVER: RwLock<String> = RwLock::new("".to_owned());
    pub static ref EXE_RENDEZVOUS_SERVER: RwLock<String> = Default::default();
    pub static ref APP_NAME: RwLock<String> = RwLock::new("NeoDesk Client".to_owned());
    static ref KEY_PAIR: Mutex<Option<KeyPair>> = Default::default();
    static ref USER_DEFAULT_CONFIG: RwLock<(UserDefaultConfig, Instant)> = RwLock::new((UserDefaultConfig::load(), Instant::now()));
    pub static ref NEW_STORED_PEER_CONFIG: Mutex<HashSet<String>> = Default::default();
    pub static ref DEFAULT_SETTINGS: RwLock<HashMap<String, String>> = Default::default();
    pub static ref OVERWRITE_SETTINGS: RwLock<HashMap<String, String>> = Default::default();
    pub static ref DEFAULT_DISPLAY_SETTINGS: RwLock<HashMap<String, String>> = Default::default();
    pub static ref OVERWRITE_DISPLAY_SETTINGS: RwLock<HashMap<String, String>> = Default::default();
    pub static ref DEFAULT_LOCAL_SETTINGS: RwLock<HashMap<String, String>> = Default::default();
    pub static ref OVERWRITE_LOCAL_SETTINGS: RwLock<HashMap<String, String>> = Default::default();
    pub static ref HARD_SETTINGS: RwLock<HashMap<String, String>> = Default::default();
    pub static ref BUILTIN_SETTINGS: RwLock<HashMap<String, String>> = Default::default();
}

/// Whether this process holds the device's secrets, see
/// [`Config::set_holds_secrets`].
static SECRETS_HOLDER: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(true);

/// Options that hold a secret of the device: the 2FA secret. Like the key
/// pair and the stored permanent password, they stay in the process that
/// holds the device's secrets (L442).
pub const SECRET_OPTIONS: &[&str] = &[keys::OPTION_2FA];

/// The device's secrets that a process which does not hold them found in its
/// own config files, the copies an older version left in the person's
/// profile, for the process that holds them (L442).
#[derive(Default, Clone, PartialEq, Serialize, Deserialize)]
pub struct ProfileSecrets {
    /// The key pair (secret key, public key).
    pub key_pair: Option<(Vec<u8>, Vec<u8>)>,
    /// The stored permanent password and its salt.
    pub permanent_password: Option<(String, String)>,
    /// Secret options by name, see [`SECRET_OPTIONS`].
    pub options: HashMap<String, String>,
}

impl std::fmt::Debug for ProfileSecrets {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        // Names only: no secret goes into a log line
        f.debug_struct("ProfileSecrets")
            .field("key_pair", &self.key_pair.is_some())
            .field("permanent_password", &self.permanent_password.is_some())
            .field("options", &self.options.keys().collect::<Vec<_>>())
            .finish()
    }
}

impl ProfileSecrets {
    fn is_empty(&self) -> bool {
        self.key_pair.is_none() && self.permanent_password.is_none() && self.options.is_empty()
    }
}

/// Takes the secret options out of `options`.
fn remove_secret_options(options: &mut HashMap<String, String>) {
    for key in SECRET_OPTIONS {
        options.remove(*key);
    }
}

/// Puts the secret options of `from` into `options` in place of any that
/// `options` has.
fn keep_secret_options(options: &mut HashMap<String, String>, from: &HashMap<String, String>) {
    remove_secret_options(options);
    for key in SECRET_OPTIONS {
        if let Some(value) = from.get(*key) {
            options.insert((*key).to_owned(), value.clone());
        }
    }
}

/// Whether `key_pair` is an Ed25519 secret key and the public key it
/// belongs to.
fn is_ed25519_key_pair((secret_key, public_key): &KeyPair) -> bool {
    let (Some(secret_key), Some(public_key)) = (
        sign::SecretKey::from_slice(secret_key),
        sign::PublicKey::from_slice(public_key),
    ) else {
        return false;
    };
    const PROBE: &[u8] = b"NeoDesk key pair check";
    sign::verify_detached(&sign::sign_detached(PROBE, &secret_key), PROBE, &public_key)
}

#[cfg(target_os = "android")]
lazy_static::lazy_static! {
    pub static ref ANDROID_RUSTLS_PLATFORM_VERIFIER_INITIALIZED: std::sync::atomic::AtomicBool = std::sync::atomic::AtomicBool::new(false);
}

lazy_static::lazy_static! {
    pub static ref APP_DIR: RwLock<String> = Default::default();
}

#[cfg(any(target_os = "android", target_os = "ios"))]
lazy_static::lazy_static! {
    pub static ref APP_HOME_DIR: RwLock<String> = Default::default();
}

pub const LINK_DOCS_HOME: &str = "https://github.com/neodeskapp/neodesk";
pub const LINK_DOCS_X11_REQUIRED: &str = "https://github.com/neodeskapp/neodesk";

/// Official desktop client product id reported to NeoDesk API (sysinfo / login).
pub const NEODESK_CLIENT_PRODUCT: &str = "neodesk-desktop";
/// On-disk / process executable stem (Windows: neodesk.exe). Display name is `APP_NAME`.
pub const EXE_NAME: &str = "neodesk";
/// URI scheme without spaces (APP_NAME may contain spaces).
pub const URI_SCHEME: &str = "neodesk";
/// Previous client scheme. Still accepted so existing `rustdesk://` links keep working.
pub const LEGACY_URI_SCHEME: &str = "rustdesk";

/// Upstream project this client is forked from (AGPL-3.0 attribution).
pub const UPSTREAM_PROJECT_NAME: &str = "RustDesk";
pub const UPSTREAM_REPO_URL: &str = "https://github.com/rustdesk/rustdesk";
/// Source code for this NeoDesk client build (AGPL corresponding source).
pub const FORK_REPO_URL: &str = "https://github.com/neodeskapp/neodesk-client";
pub const LICENSE_SPDX: &str = "AGPL-3.0-only";
pub const LICENSE_NAME: &str = "GNU Affero General Public License v3.0";

lazy_static::lazy_static! {
    pub static ref HELPER_URL: HashMap<&'static str, &'static str> = HashMap::from([
        ("rustdesk docs home", LINK_DOCS_HOME),
        ("rustdesk docs x11-required", LINK_DOCS_X11_REQUIRED),
        ]);
}

const NUM_CHARS: &[char] = &['0', '1', '2', '3', '4', '5', '6', '7', '8', '9'];

const CHARS: &[char] = &[
    '2', '3', '4', '5', '6', '7', '8', '9', 'a', 'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k',
    'm', 'n', 'p', 'q', 'r', 's', 't', 'u', 'v', 'w', 'x', 'y', 'z',
];

/// Empty: NeoDesk never falls back to public rustdesk.com rendezvous.
pub const RENDEZVOUS_SERVERS: &[&str] = &[];
/// Unused as a default peer/rendezvous key; kept only for legacy decode helpers.
/// Configure `key` via Network settings, deploy string, or `custom.txt`.
pub const RS_PUB_KEY: &str = "";

pub const RENDEZVOUS_PORT: i32 = 21116;
pub const RELAY_PORT: i32 = 21117;
pub const WS_RENDEZVOUS_PORT: i32 = 21118;
pub const WS_RELAY_PORT: i32 = 21119;

#[inline]
pub fn is_service_ipc_postfix(postfix: &str) -> bool {
    // `_service` is a protected cross-user IPC channel used by the root service.
    //
    // On Linux Wayland, input injection is implemented via uinput in the root service process.
    // The user `--server` process must be able to connect to these uinput IPC channels, so they
    // must share the same IPC parent directory as `_service`.
    postfix == "_service" || postfix.starts_with("_uinput_")
}

// Keep Linux/macOS IPC parent directory rules in one place to avoid drift between
// `ipc_path()` and Unix `ipc_path_for_uid()`.
#[cfg(any(target_os = "linux", target_os = "macos"))]
#[inline]
fn ipc_parent_dir_for_uid(uid: u32, postfix: &str) -> String {
    // Use EXE_NAME (no spaces) so IPC sockets/pipes stay stable when APP_NAME is a display name.
    let app_name = EXE_NAME;
    if is_service_ipc_postfix(postfix) {
        format!("/tmp/{app_name}-service")
    } else {
        format!("/tmp/{app_name}-{uid}")
    }
}

macro_rules! serde_field_string {
    ($default_func:ident, $de_func:ident, $default_expr:expr) => {
        fn $default_func() -> String {
            $default_expr
        }

        fn $de_func<'de, D>(deserializer: D) -> Result<String, D::Error>
        where
            D: de::Deserializer<'de>,
        {
            let s: String =
                de::Deserialize::deserialize(deserializer).unwrap_or(Self::$default_func());
            if s.is_empty() {
                return Ok(Self::$default_func());
            }
            Ok(s)
        }
    };
}

macro_rules! serde_field_bool {
    ($struct_name: ident, $field_name: literal, $func: ident, $default: literal) => {
        #[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
        pub struct $struct_name {
            #[serde(default = $default, rename = $field_name, deserialize_with = "deserialize_bool")]
            pub v: bool,
        }
        impl Default for $struct_name {
            fn default() -> Self {
                Self { v: Self::$func() }
            }
        }
        impl $struct_name {
            pub fn $func() -> bool {
                UserDefaultConfig::read($field_name) == "Y"
            }
        }
        impl Deref for $struct_name {
            type Target = bool;

            fn deref(&self) -> &Self::Target {
                &self.v
            }
        }
        impl DerefMut for $struct_name {
            fn deref_mut(&mut self) -> &mut Self::Target {
                &mut self.v
            }
        }
    };
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum NetworkType {
    Direct,
    ProxySocks,
}

#[derive(Debug, Default, Serialize, Deserialize, Clone, PartialEq)]
pub struct Config {
    #[serde(
        default,
        skip_serializing_if = "String::is_empty",
        deserialize_with = "deserialize_string"
    )]
    pub id: String, // use
    #[serde(default, deserialize_with = "deserialize_string")]
    enc_id: String, // store
    #[serde(default, deserialize_with = "deserialize_string")]
    password: String,
    #[serde(default, deserialize_with = "deserialize_string")]
    salt: String,
    #[serde(default, deserialize_with = "deserialize_keypair")]
    key_pair: KeyPair, // sk, pk
    #[serde(default, deserialize_with = "deserialize_bool")]
    key_confirmed: bool,
    #[serde(default, deserialize_with = "deserialize_hashmap_string_bool")]
    keys_confirmed: HashMap<String, bool>,
}

#[derive(Debug, Default, PartialEq, Serialize, Deserialize, Clone)]
pub struct Socks5Server {
    #[serde(default, deserialize_with = "deserialize_string")]
    pub proxy: String,
    #[serde(default, deserialize_with = "deserialize_string")]
    pub username: String,
    #[serde(default, deserialize_with = "deserialize_string")]
    pub password: String,
}

// more variable configs
#[derive(Debug, Default, Serialize, Deserialize, Clone, PartialEq)]
pub struct Config2 {
    #[serde(default, deserialize_with = "deserialize_string")]
    rendezvous_server: String,
    #[serde(default, deserialize_with = "deserialize_i32")]
    nat_type: i32,
    #[serde(default, deserialize_with = "deserialize_i32")]
    serial: i32,
    #[serde(default, deserialize_with = "deserialize_string")]
    unlock_pin: String,
    #[serde(default, deserialize_with = "deserialize_string")]
    trusted_devices: String,

    #[serde(default)]
    socks: Option<Socks5Server>,

    // the other scalar value must before this
    #[serde(default, deserialize_with = "deserialize_hashmap_string_string")]
    pub options: HashMap<String, String>,
}

#[derive(Debug, Default, Serialize, Deserialize, Clone, PartialEq)]
pub struct Resolution {
    pub w: i32,
    pub h: i32,
}

#[derive(Debug, Serialize, Deserialize, Clone, PartialEq)]
pub struct PeerConfig {
    #[serde(default, deserialize_with = "deserialize_vec_u8")]
    pub password: Vec<u8>,
    #[serde(default, deserialize_with = "deserialize_size")]
    pub size: Size,
    #[serde(default, deserialize_with = "deserialize_size")]
    pub size_ft: Size,
    #[serde(default, deserialize_with = "deserialize_size")]
    pub size_pf: Size,
    #[serde(
        default = "PeerConfig::default_view_style",
        deserialize_with = "PeerConfig::deserialize_view_style",
        skip_serializing_if = "String::is_empty"
    )]
    pub view_style: String,
    // Image scroll style, scrolledge, scrollbar or scroll auto
    #[serde(
        default = "PeerConfig::default_scroll_style",
        deserialize_with = "PeerConfig::deserialize_scroll_style",
        skip_serializing_if = "String::is_empty"
    )]
    pub scroll_style: String,
    #[serde(
        default = "PeerConfig::default_edge_scroll_edge_thickness",
        deserialize_with = "PeerConfig::deserialize_edge_scroll_edge_thickness"
    )]
    pub edge_scroll_edge_thickness: i32,
    #[serde(
        default = "PeerConfig::default_image_quality",
        deserialize_with = "PeerConfig::deserialize_image_quality",
        skip_serializing_if = "String::is_empty"
    )]
    pub image_quality: String,
    #[serde(
        default = "PeerConfig::default_custom_image_quality",
        deserialize_with = "PeerConfig::deserialize_custom_image_quality",
        skip_serializing_if = "Vec::is_empty"
    )]
    pub custom_image_quality: Vec<i32>,
    #[serde(flatten)]
    pub show_remote_cursor: ShowRemoteCursor,
    #[serde(flatten)]
    pub lock_after_session_end: LockAfterSessionEnd,
    #[serde(flatten)]
    pub terminal_persistent: TerminalPersistent,
    #[serde(flatten)]
    pub privacy_mode: PrivacyMode,
    #[serde(flatten)]
    pub allow_swap_key: AllowSwapKey,
    #[serde(default, deserialize_with = "deserialize_vec_i32_string_i32")]
    pub port_forwards: Vec<(i32, String, i32)>,
    #[serde(default, deserialize_with = "deserialize_i32")]
    pub direct_failures: i32,
    #[serde(flatten)]
    pub disable_audio: DisableAudio,
    #[serde(flatten)]
    pub disable_clipboard: DisableClipboard,
    #[serde(flatten)]
    pub enable_file_copy_paste: EnableFileCopyPaste,
    #[serde(flatten)]
    pub show_quality_monitor: ShowQualityMonitor,
    #[serde(flatten)]
    pub follow_remote_cursor: FollowRemoteCursor,
    #[serde(flatten)]
    pub follow_remote_window: FollowRemoteWindow,
    #[serde(
        default,
        deserialize_with = "deserialize_string",
        skip_serializing_if = "String::is_empty"
    )]
    pub keyboard_mode: String,
    #[serde(flatten)]
    pub view_only: ViewOnly,
    #[serde(flatten)]
    pub show_my_cursor: ShowMyCursor,
    #[serde(flatten)]
    pub sync_init_clipboard: SyncInitClipboard,
    // Mouse wheel or touchpad scroll mode
    #[serde(
        default = "PeerConfig::default_reverse_mouse_wheel",
        deserialize_with = "PeerConfig::deserialize_reverse_mouse_wheel",
        skip_serializing_if = "String::is_empty"
    )]
    pub reverse_mouse_wheel: String,
    #[serde(
        default = "PeerConfig::default_displays_as_individual_windows",
        deserialize_with = "PeerConfig::deserialize_displays_as_individual_windows",
        skip_serializing_if = "String::is_empty"
    )]
    pub displays_as_individual_windows: String,
    #[serde(
        default = "PeerConfig::default_use_all_my_displays_for_the_remote_session",
        deserialize_with = "PeerConfig::deserialize_use_all_my_displays_for_the_remote_session",
        skip_serializing_if = "String::is_empty"
    )]
    pub use_all_my_displays_for_the_remote_session: String,
    #[serde(
        rename = "trackpad-speed",
        default = "PeerConfig::default_trackpad_speed",
        deserialize_with = "PeerConfig::deserialize_trackpad_speed"
    )]
    pub trackpad_speed: i32,

    #[serde(
        default,
        deserialize_with = "deserialize_hashmap_resolutions",
        skip_serializing_if = "HashMap::is_empty"
    )]
    pub custom_resolutions: HashMap<String, Resolution>,

    // The other scalar value must before this
    #[serde(
        default,
        deserialize_with = "deserialize_hashmap_string_string",
        skip_serializing_if = "HashMap::is_empty"
    )]
    pub options: HashMap<String, String>, // not use delete to represent default values
    // Various data for flutter ui
    #[serde(default, deserialize_with = "deserialize_hashmap_string_string")]
    pub ui_flutter: HashMap<String, String>,
    #[serde(default)]
    pub info: PeerInfoSerde,
    #[serde(default)]
    pub transfer: TransferSerde,
}

impl Default for PeerConfig {
    fn default() -> Self {
        Self {
            password: Default::default(),
            size: Default::default(),
            size_ft: Default::default(),
            size_pf: Default::default(),
            view_style: Self::default_view_style(),
            scroll_style: Self::default_scroll_style(),
            edge_scroll_edge_thickness: Self::default_edge_scroll_edge_thickness(),
            image_quality: Self::default_image_quality(),
            custom_image_quality: Self::default_custom_image_quality(),
            show_remote_cursor: Default::default(),
            lock_after_session_end: Default::default(),
            terminal_persistent: Default::default(),
            privacy_mode: Default::default(),
            allow_swap_key: Default::default(),
            port_forwards: Default::default(),
            direct_failures: Default::default(),
            disable_audio: Default::default(),
            disable_clipboard: Default::default(),
            enable_file_copy_paste: Default::default(),
            show_quality_monitor: Default::default(),
            follow_remote_cursor: Default::default(),
            follow_remote_window: Default::default(),
            keyboard_mode: Default::default(),
            view_only: Default::default(),
            show_my_cursor: Default::default(),
            reverse_mouse_wheel: Self::default_reverse_mouse_wheel(),
            displays_as_individual_windows: Self::default_displays_as_individual_windows(),
            use_all_my_displays_for_the_remote_session:
                Self::default_use_all_my_displays_for_the_remote_session(),
            trackpad_speed: Self::default_trackpad_speed(),
            custom_resolutions: Default::default(),
            options: Self::default_options(),
            ui_flutter: Default::default(),
            info: Default::default(),
            transfer: Default::default(),
            sync_init_clipboard: Default::default(),
        }
    }
}

#[derive(Debug, PartialEq, Default, Serialize, Deserialize, Clone)]
pub struct PeerInfoSerde {
    #[serde(default, deserialize_with = "deserialize_string")]
    pub username: String,
    #[serde(default, deserialize_with = "deserialize_string")]
    pub hostname: String,
    #[serde(default, deserialize_with = "deserialize_string")]
    pub platform: String,
}

#[derive(Debug, Default, Serialize, Deserialize, Clone, PartialEq)]
pub struct TransferSerde {
    #[serde(default, deserialize_with = "deserialize_vec_string")]
    pub write_jobs: Vec<String>,
    #[serde(default, deserialize_with = "deserialize_vec_string")]
    pub read_jobs: Vec<String>,
}

#[inline]
pub fn get_online_state() -> i64 {
    let state = *ONLINE.lock().unwrap().values().max().unwrap_or(&0);
    if state > 0 && !Config::get_key_confirmed() {
        -1
    } else {
        state
    }
}

#[cfg(not(any(target_os = "android", target_os = "ios")))]
fn patch(path: PathBuf) -> PathBuf {
    if let Some(_tmp) = path.to_str() {
        #[cfg(windows)]
        return _tmp
            .replace(
                "system32\\config\\systemprofile",
                "ServiceProfiles\\LocalService",
            )
            .into();
        #[cfg(target_os = "macos")]
        return _tmp.replace("Application Support", "Preferences").into();
        #[cfg(target_os = "linux")]
        {
            if _tmp == "/root" {
                if let Ok(user) = crate::platform::linux::run_cmds_trim_newline("whoami") {
                    if user != "root" {
                        let cmd = format!("getent passwd '{}' | awk -F':' '{{print $6}}'", user);
                        if let Ok(output) = crate::platform::linux::run_cmds_trim_newline(&cmd) {
                            return output.into();
                        }
                        return format!("/home/{user}").into();
                    }
                }
            }
        }
    }
    path
}

impl Config2 {
    fn load() -> Config2 {
        let mut config = Config::load_::<Config2>("2");
        let mut store = false;
        if let Some(mut socks) = config.socks {
            let (password, _, store2) =
                decrypt_str_or_original(&socks.password, PASSWORD_ENC_VERSION);
            socks.password = password;
            config.socks = Some(socks);
            store |= store2;
        }
        let (unlock_pin, _, store2) =
            decrypt_str_or_original(&config.unlock_pin, PASSWORD_ENC_VERSION);
        config.unlock_pin = unlock_pin;
        store |= store2;
        if !Config::holds_secrets() {
            // A copy an older version stored stays in the file only (L442)
            remove_secret_options(&mut config.options);
        }
        if store {
            config.store();
        }
        config
    }

    pub fn file() -> PathBuf {
        Config::file_("2")
    }

    fn store(&self) {
        let mut config = self.clone();
        let stored = Config::load_::<Config2>("2");
        if let Some(mut socks) = config.socks {
            let stored_password = stored
                .socks
                .as_ref()
                .map(|socks| socks.password.as_str())
                .unwrap_or_default();
            socks.password =
                keep_encrypted_storage_if_plaintext_unchanged(&socks.password, stored_password);
            config.socks = Some(socks);
        }
        config.unlock_pin =
            keep_encrypted_storage_if_plaintext_unchanged(&config.unlock_pin, &stored.unlock_pin);
        if !Config::holds_secrets() {
            // The file's secret options stay as they are (L442)
            keep_secret_options(&mut config.options, &stored.options);
        }
        Config::store_(&config, "2");
    }

    pub fn get() -> Config2 {
        return CONFIG2.read().unwrap().clone();
    }

    pub fn set(mut cfg: Config2) -> bool {
        if !Config::holds_secrets() {
            remove_secret_options(&mut cfg.options);
        }
        let mut lock = CONFIG2.write().unwrap();
        if *lock == cfg {
            return false;
        }
        *lock = cfg;
        lock.store();
        true
    }

    /// This process's config2 for another process of the client, without the
    /// secret options: they never leave the process that holds them over
    /// IPC (L442).
    pub fn get_for_other_process() -> Config2 {
        let mut config = Self::get();
        remove_secret_options(&mut config.options);
        config
    }

    /// Takes a config2 another process of the client sent and keeps this
    /// process's secret options, whatever the config2 sent carries (L442).
    pub fn set_from_other_process(mut cfg: Config2) -> bool {
        keep_secret_options(&mut cfg.options, &CONFIG2.read().unwrap().options);
        Self::set(cfg)
    }
}

fn keep_encrypted_storage_if_plaintext_unchanged(plain: &str, stored: &str) -> String {
    let (stored_plain, encrypted, _) = decrypt_str_or_original(stored, PASSWORD_ENC_VERSION);
    if encrypted && stored_plain == plain {
        return stored.to_owned();
    }
    encrypt_str_or_original(plain, PASSWORD_ENC_VERSION, ENCRYPT_MAX_LEN)
}

pub fn load_path<T: serde::Serialize + serde::de::DeserializeOwned + Default + std::fmt::Debug>(
    file: PathBuf,
) -> T {
    let cfg = match confy::load_path(&file) {
        Ok(config) => config,
        Err(err) => {
            if let confy::ConfyError::GeneralLoadError(err) = &err {
                if err.kind() == std::io::ErrorKind::NotFound {
                    return T::default();
                }
            }
            log::error!("Failed to load config '{}': {}", file.display(), err);
            T::default()
        }
    };
    cfg
}

#[inline]
pub fn store_path<T: serde::Serialize>(path: PathBuf, cfg: T) -> crate::ResultType<()> {
    #[cfg(not(windows))]
    {
        use std::os::unix::fs::PermissionsExt;
        Ok(confy::store_path_perms(
            path,
            cfg,
            fs::Permissions::from_mode(0o600),
        )?)
    }
    #[cfg(windows)]
    {
        Ok(confy::store_path(path, cfg)?)
    }
}

/// The ID stock RustDesk derives from a MAC address.
#[cfg(not(any(target_os = "android", target_os = "ios")))]
fn stock_id_from_mac(mac: &[u8; 6]) -> u32 {
    let mut id = 0u32;
    for x in &mac[2..] {
        id = (id << 8) | (*x as u32);
    }
    id & 0x1FFFFFFF
}

/// NeoDesk's ID for a MAC address. It stays bound to the computer, so a
/// reinstall keeps it, and flips bits of stock RustDesk's, so a stock
/// RustDesk on the same computer never has the same ID and both can run.
#[cfg(not(any(target_os = "android", target_os = "ios")))]
fn neodesk_id_from_mac(mac: &[u8; 6]) -> u32 {
    const NEODESK_ID_BITS: u32 = 0x0E0D_E5C0;
    stock_id_from_mac(mac) ^ NEODESK_ID_BITS
}

#[cfg(not(any(target_os = "android", target_os = "ios")))]
fn moved_stock_id_for_mac(id: &str, mac: &[u8; 6]) -> Option<String> {
    (id == stock_id_from_mac(mac).to_string()).then(|| neodesk_id_from_mac(mac).to_string())
}

impl Config {
    fn load_<T: serde::Serialize + serde::de::DeserializeOwned + Default + std::fmt::Debug>(
        suffix: &str,
    ) -> T {
        let file = Self::file_(suffix);
        load_path(file)
    }

    fn store_<T: serde::Serialize>(config: &T, suffix: &str) {
        let file = Self::file_(suffix);
        if let Err(err) = store_path(file, config) {
            log::error!("Failed to store {suffix} config: {err}");
        }
    }

    fn load() -> Config {
        let mut config = Config::load_::<Config>("");
        if !Self::holds_secrets() {
            // Copies an older version stored stay in the file only (L442)
            config.key_pair = Default::default();
            config.password.clear();
        }
        let mut store = false;
        if let Err(err) = Self::validate_or_decrypt_permanent_password_storage(&mut config) {
            log::error!("Failed to validate or decrypt permanent password storage: {err}");
        }
        let mut id_valid = false;
        let (id, encrypted, store2) = decrypt_str_or_original(&config.enc_id, PASSWORD_ENC_VERSION);
        if encrypted {
            config.id = id;
            id_valid = true;
            store |= store2;
        } else if
        // Comment out for forward compatible
        // crate::get_modified_time(&Self::file_(""))
        // .checked_sub(std::time::Duration::from_secs(30)) // allow modification during installation
        // .unwrap_or_else(crate::get_exe_time)
        // < crate::get_exe_time()
        // &&
        !config.id.is_empty()
            && config.enc_id.is_empty()
            && !decrypt_str_or_original(&config.id, PASSWORD_ENC_VERSION).1
        {
            id_valid = true;
            store = true;
        }
        if !id_valid {
            log::warn!("ID is invalid, generating new one");
            for _ in 0..3 {
                if let Some(id) = Config::gen_id() {
                    config.id = id;
                    store = true;
                    break;
                } else {
                    log::error!("Failed to generate new id");
                }
            }
        } else if let Some(id) = Config::moved_stock_id(&config.id) {
            log::info!(
                "ID {} is stock RustDesk's on this computer, NeoDesk takes {}",
                config.id,
                id
            );
            config.id = id;
            store = true;
        }
        if store {
            config.store();
        }
        config
    }

    fn validate_or_decrypt_permanent_password_storage(config: &mut Config) -> Result<()> {
        if config.password.is_empty() {
            return Ok(());
        }

        if config.password.starts_with(PASSWORD_ENC_VERSION) {
            let (plain, decrypted, should_store) =
                decrypt_str_or_original(&config.password, PASSWORD_ENC_VERSION);
            if decrypted {
                config.password = plain;
                return Ok(());
            }
            if !should_store {
                return Err(anyhow!("Invalid permanent password encrypted hash storage"));
            }
            return Ok(());
        }

        let (decrypted_storage, decrypted, _) =
            decrypt_permanent_password_str_or_original(&config.password);
        if decrypted {
            Self::ensure_permanent_password_hash_salt(config)?;
            if decode_permanent_password_h1_from_hashed_storage(&decrypted_storage).is_some() {
                return Ok(());
            }
            return Err(anyhow!("Invalid permanent password encrypted hash storage"));
        }

        Ok(())
    }

    fn ensure_permanent_password_hash_salt(config: &Config) -> Result<()> {
        if config.salt.is_empty() {
            return Err(anyhow!(
                "Permanent password hash storage requires a non-empty salt"
            ));
        }
        Ok(())
    }

    fn ensure_permanent_password_salt(config: &mut Config) {
        if config.salt.is_empty() {
            config.salt = Config::get_auto_password(DEFAULT_SALT_LEN);
        }
    }

    fn prepare_config_for_store(config: &mut Config) {
        match Self::validate_or_decrypt_permanent_password_storage(config) {
            Ok(_) => {}
            Err(err) => {
                // This path is for unrecoverable permanent-password storage, such as
                // hashed storage without its salt. Keep unrelated config writes working,
                // but handle future transient migration errors separately.
                log::error!(
                    "Clearing invalid permanent password storage before storing config: {err}"
                );
                config.password.clear();
                config.salt.clear();
            }
        }
    }

    fn store(&self) {
        let mut config = self.clone();
        if Self::holds_secrets() {
            Self::prepare_config_for_store(&mut config);
            if config.key_pair.0.is_empty() {
                // Another process of this client (a join run as `--join`) can
                // have written the device's key pair after this process loaded
                // its config. A config without a key pair must not write it away.
                config.key_pair = Config::load_::<Config>("").key_pair;
            }
            if !config.password.is_empty()
                && decode_permanent_password_h1_from_storage(&config.password).is_none()
            {
                let stored = Config::load_::<Config>("");
                config.password = keep_encrypted_storage_if_plaintext_unchanged(
                    &config.password,
                    &stored.password,
                );
            }
        } else {
            // This process never writes a secret: the key pair and the
            // stored permanent password in the file stay as they are, with
            // the password's salt (L442)
            let stored = Config::load_::<Config>("");
            config.key_pair = stored.key_pair;
            config.password = stored.password;
            config.salt = stored.salt;
        }
        let (stored_id, encrypted, _) =
            decrypt_str_or_original(&config.enc_id, PASSWORD_ENC_VERSION);
        if !encrypted || stored_id != config.id {
            config.enc_id =
                encrypt_str_or_original(&config.id, PASSWORD_ENC_VERSION, ENCRYPT_MAX_LEN);
        }
        config.id = "".to_owned();
        Config::store_(&config, "");
    }

    pub fn file() -> PathBuf {
        Self::file_("")
    }

    fn file_(suffix: &str) -> PathBuf {
        let name = format!("{}{}", *APP_NAME.read().unwrap(), suffix);
        Config::with_extension(Self::path(name))
    }

    pub fn is_empty(&self) -> bool {
        (self.id.is_empty() && self.enc_id.is_empty()) || self.key_pair.0.is_empty()
    }

    /// Get the user's home directory for configuration purposes.
    ///
    /// # Security Note
    /// This function uses `dirs_next::home_dir()` which reads the `$HOME` environment
    /// variable on Unix systems. This is acceptable for user-space operations (config
    /// file storage, logging) where the user may intentionally redirect their home
    /// directory.
    ///
    /// **DO NOT use this function in privileged contexts** (e.g., code executed via
    /// `gtk_sudo` or system services running as root). For privileged operations on
    /// Linux, use `crate::platform::linux::get_home_dir_trusted()` which bypasses
    /// the `$HOME` environment variable and queries the system password database
    /// directly via `getpwuid`.
    ///
    /// Using `$HOME` in privileged contexts creates a confused-deputy vulnerability
    /// where an attacker can manipulate the environment variable to inject malicious
    /// paths into privileged operations.
    pub fn get_home() -> PathBuf {
        #[cfg(any(target_os = "android", target_os = "ios"))]
        return PathBuf::from(APP_HOME_DIR.read().unwrap().as_str());
        #[cfg(not(any(target_os = "android", target_os = "ios")))]
        {
            if let Some(path) = dirs_next::home_dir() {
                patch(path)
            } else if let Ok(path) = std::env::current_dir() {
                path
            } else {
                std::env::temp_dir()
            }
        }
    }

    pub fn path<P: AsRef<Path>>(p: P) -> PathBuf {
        #[cfg(any(target_os = "android", target_os = "ios"))]
        {
            let mut path: PathBuf = APP_DIR.read().unwrap().clone().into();
            path.push(p);
            return path;
        }
        #[cfg(not(any(target_os = "android", target_os = "ios")))]
        {
            #[cfg(not(target_os = "macos"))]
            let org = "".to_owned();
            #[cfg(target_os = "macos")]
            let org = ORG.read().unwrap().clone();
            let app_name = APP_NAME.read().unwrap().clone();
            // /var/root for root
            if let Some(project) = directories_next::ProjectDirs::from("", &org, &app_name) {
                // The Windows service keeps its config in a folder of its own (L442)
                #[cfg(windows)]
                if service_dir::is_system_profile(project.config_dir()) {
                    let mut path = service_dir::config_dir(
                        &app_name,
                        patch(project.config_dir().to_path_buf()),
                    );
                    path.push(p);
                    return path;
                }
                let mut path = patch(project.config_dir().to_path_buf());
                path.push(p);
                return path;
            }
            "".into()
        }
    }

    /// Get the log directory path.
    ///
    /// # Security Note
    /// On macOS, this function uses `dirs_next::home_dir()` which reads the `$HOME`
    /// environment variable. On Linux/Android, it uses `Self::get_home()`.
    /// See [`Self::get_home()`] for security considerations regarding `$HOME` usage.
    #[allow(unreachable_code)]
    pub fn log_path() -> PathBuf {
        #[cfg(target_os = "macos")]
        {
            if let Some(path) = dirs_next::home_dir().as_mut() {
                path.push(format!("Library/Logs/{}", *APP_NAME.read().unwrap()));
                return path.clone();
            }
        }
        #[cfg(target_os = "linux")]
        {
            let mut path = Self::get_home();
            path.push(format!(".local/share/logs/{}", *APP_NAME.read().unwrap()));
            std::fs::create_dir_all(&path).ok();
            return path;
        }
        #[cfg(target_os = "android")]
        {
            let mut path = Self::get_home();
            path.push(format!("{}/Logs", *APP_NAME.read().unwrap()));
            std::fs::create_dir_all(&path).ok();
            return path;
        }
        if let Some(path) = Self::path("").parent() {
            let mut path: PathBuf = path.into();
            path.push("log");
            return path;
        }
        "".into()
    }

    pub fn ipc_path(postfix: &str) -> String {
        #[cfg(windows)]
        {
            // \\ServerName\pipe\PipeName
            // where ServerName is either the name of a remote computer or a period, to specify the local computer.
            // https://docs.microsoft.com/en-us/windows/win32/ipc/pipe-names
            // Use EXE_NAME (no spaces) — APP_NAME may be a multi-word display name.
            format!(
                "\\\\.\\pipe\\{}\\query{}",
                EXE_NAME,
                postfix
            )
        }
        #[cfg(not(windows))]
        {
            #[cfg(target_os = "android")]
            use std::os::unix::fs::PermissionsExt;
            #[cfg(target_os = "android")]
            let mut path: PathBuf =
                format!("{}/{}", *APP_DIR.read().unwrap(), EXE_NAME).into();
            #[cfg(any(target_os = "linux", target_os = "macos"))]
            let mut path: PathBuf = {
                let uid = unsafe { libc::geteuid() as u32 };
                ipc_parent_dir_for_uid(uid, postfix).into()
            };
            #[cfg(not(any(target_os = "android", target_os = "linux", target_os = "macos")))]
            let mut path: PathBuf = format!("/tmp/{}", EXE_NAME).into();
            // Android stores IPC sockets under app-controlled directories. Create the IPC parent
            // dir and enforce the expected mode here. On other Unix platforms, `ipc_path()` is
            // intentionally side-effect free (no mkdir/chmod); callers should enforce directory and
            // socket permissions at the IPC server boundary.
            #[cfg(target_os = "android")]
            {
                fs::create_dir_all(&path).ok();
                let path_mode = if is_service_ipc_postfix(postfix) {
                    0o0711
                } else {
                    0o0700
                };
                fs::set_permissions(&path, fs::Permissions::from_mode(path_mode)).ok();
            }
            path.push(format!("ipc{postfix}"));
            path.to_str().unwrap_or("").to_owned()
        }
    }

    #[cfg(any(target_os = "linux", target_os = "macos"))]
    pub fn ipc_path_for_uid(uid: u32, postfix: &str) -> String {
        let parent = ipc_parent_dir_for_uid(uid, postfix);
        format!("{parent}/ipc{postfix}")
    }

    pub fn icon_path() -> PathBuf {
        let mut path = Self::path("icons");
        if fs::create_dir_all(&path).is_err() {
            path = std::env::temp_dir();
        }
        path
    }

    #[inline]
    pub fn get_any_listen_addr(is_ipv4: bool) -> SocketAddr {
        if is_ipv4 {
            SocketAddr::new(IpAddr::V4(Ipv4Addr::UNSPECIFIED), 0)
        } else {
            SocketAddr::new(IpAddr::V6(Ipv6Addr::UNSPECIFIED), 0)
        }
    }

    pub fn get_rendezvous_server() -> String {
        let mut rendezvous_server = EXE_RENDEZVOUS_SERVER.read().unwrap().clone();
        if rendezvous_server.is_empty() {
            rendezvous_server = Self::get_option("custom-rendezvous-server");
        }
        if rendezvous_server.is_empty() {
            rendezvous_server = PROD_RENDEZVOUS_SERVER.read().unwrap().clone();
        }
        if rendezvous_server.is_empty() {
            rendezvous_server = CONFIG2.read().unwrap().rendezvous_server.clone();
        }
        if rendezvous_server.is_empty() {
            rendezvous_server = Self::get_rendezvous_servers()
                .drain(..)
                .next()
                .unwrap_or_default();
        }
        if !rendezvous_server.is_empty() && !rendezvous_server.contains(':') {
            rendezvous_server = format!("{rendezvous_server}:{RENDEZVOUS_PORT}");
        }
        rendezvous_server
    }

    pub fn get_rendezvous_servers() -> Vec<String> {
        let s = EXE_RENDEZVOUS_SERVER.read().unwrap().clone();
        if !s.is_empty() {
            return vec![s];
        }
        let s = Self::get_option("custom-rendezvous-server");
        if !s.is_empty() {
            return vec![s];
        }
        let s = PROD_RENDEZVOUS_SERVER.read().unwrap().clone();
        if !s.is_empty() {
            return vec![s];
        }
        let serial_obsolute = CONFIG2.read().unwrap().serial > SERIAL;
        if serial_obsolute {
            let ss: Vec<String> = Self::get_option("rendezvous-servers")
                .split(',')
                .filter(|x| x.contains('.'))
                .map(|x| x.to_owned())
                .collect();
            if !ss.is_empty() {
                return ss;
            }
        }
        return RENDEZVOUS_SERVERS.iter().map(|x| x.to_string()).collect();
    }

    pub fn reset_online() {
        *ONLINE.lock().unwrap() = Default::default();
    }

    pub fn update_latency(host: &str, latency: i64) {
        ONLINE.lock().unwrap().insert(host.to_owned(), latency);
        let mut host = "".to_owned();
        let mut delay = i64::MAX;
        for (tmp_host, tmp_delay) in ONLINE.lock().unwrap().iter() {
            if tmp_delay > &0 && tmp_delay < &delay {
                delay = *tmp_delay;
                host = tmp_host.to_string();
            }
        }
        if !host.is_empty() {
            let mut config = CONFIG2.write().unwrap();
            if host != config.rendezvous_server {
                log::debug!("Update rendezvous_server in config to {}", host);
                log::debug!("{:?}", *ONLINE.lock().unwrap());
                config.rendezvous_server = host;
                config.store();
            }
        }
    }

    pub fn set_id(id: &str) {
        let mut config = CONFIG.write().unwrap();
        if id == config.id {
            return;
        }
        config.id = id.into();
        config.store();
    }

    pub fn set_nat_type(nat_type: i32) {
        let mut config = CONFIG2.write().unwrap();
        if nat_type == config.nat_type {
            return;
        }
        config.nat_type = nat_type;
        config.store();
    }

    pub fn get_nat_type() -> i32 {
        CONFIG2.read().unwrap().nat_type
    }

    pub fn set_serial(serial: i32) {
        let mut config = CONFIG2.write().unwrap();
        if serial == config.serial {
            return;
        }
        config.serial = serial;
        config.store();
    }

    pub fn get_serial() -> i32 {
        std::cmp::max(CONFIG2.read().unwrap().serial, SERIAL)
    }

    #[cfg(any(target_os = "android", target_os = "ios"))]
    fn gen_id() -> Option<String> {
        Self::get_auto_id()
    }

    #[cfg(not(any(target_os = "android", target_os = "ios")))]
    fn gen_id() -> Option<String> {
        let hostname_as_id = BUILTIN_SETTINGS
            .read()
            .unwrap()
            .get(keys::OPTION_ALLOW_HOSTNAME_AS_ID)
            .map(|v| option2bool(keys::OPTION_ALLOW_HOSTNAME_AS_ID, v))
            .unwrap_or(false);
        if hostname_as_id {
            match whoami::fallible::hostname() {
                Ok(h) => Some(h.replace(" ", "-")),
                Err(e) => {
                    log::warn!("Failed to get hostname, \"{}\", fallback to auto id", e);
                    Self::get_auto_id()
                }
            }
        } else {
            Self::get_auto_id()
        }
    }

    fn get_auto_id() -> Option<String> {
        #[cfg(any(target_os = "android", target_os = "ios"))]
        {
            return Some(
                rand::thread_rng()
                    .gen_range(1_000_000_000..2_000_000_000)
                    .to_string(),
            );
        }

        #[cfg(not(any(target_os = "android", target_os = "ios")))]
        {
            if let Ok(Some(ma)) = mac_address::get_mac_address() {
                let id = neodesk_id_from_mac(&ma.bytes());
                log::info!("Generated id {}", id);
                Some(id.to_string())
            } else {
                None
            }
        }
    }

    /// NeoDesk's ID for a stored `id` that is the one stock RustDesk derives
    /// on this computer, which 1.5.0-rc.4 and older took as their own.
    #[cfg(not(any(target_os = "android", target_os = "ios")))]
    fn moved_stock_id(id: &str) -> Option<String> {
        let Ok(Some(ma)) = mac_address::get_mac_address() else {
            return None;
        };
        moved_stock_id_for_mac(id, &ma.bytes())
    }

    #[cfg(any(target_os = "android", target_os = "ios"))]
    fn moved_stock_id(_id: &str) -> Option<String> {
        None
    }

    pub fn get_auto_password(length: usize) -> String {
        Self::get_auto_password_with_chars(length, CHARS)
    }

    pub fn get_auto_numeric_password(length: usize) -> String {
        Self::get_auto_password_with_chars(length, NUM_CHARS)
    }

    fn get_auto_password_with_chars(length: usize, chars: &[char]) -> String {
        let mut rng = rand::thread_rng();
        (0..length)
            .map(|_| chars[rng.gen::<usize>() % chars.len()])
            .collect()
    }

    pub fn get_key_confirmed() -> bool {
        CONFIG.read().unwrap().key_confirmed
    }

    pub fn set_key_confirmed(v: bool) {
        let mut config = CONFIG.write().unwrap();
        if config.key_confirmed == v {
            return;
        }
        config.key_confirmed = v;
        if !v {
            config.keys_confirmed = Default::default();
        }
        config.store();
    }

    pub fn get_host_key_confirmed(host: &str) -> bool {
        matches!(CONFIG.read().unwrap().keys_confirmed.get(host), Some(true))
    }

    pub fn set_host_key_confirmed(host: &str, v: bool) {
        if Self::get_host_key_confirmed(host) == v {
            return;
        }
        let mut config = CONFIG.write().unwrap();
        config.keys_confirmed.insert(host.to_owned(), v);
        config.store();
    }

    pub fn get_key_pair() -> KeyPair {
        // lock here to make sure no gen_keypair more than once
        // no use of CONFIG directly here to ensure no recursive calling in Config::load because of password dec which calling this function
        let mut lock = KEY_PAIR.lock().unwrap();
        if let Some(p) = lock.as_ref() {
            return p.clone();
        }
        if !Self::holds_secrets() {
            // Another process holds the device's key (L442)
            return Default::default();
        }
        let mut config = Config::load_::<Config>("");
        if config.key_pair.0.is_empty() {
            log::info!("Generated new keypair for id: {}", config.id);
            let (pk, sk) = sign::gen_keypair();
            let key_pair = (sk.0.to_vec(), pk.0.into());
            config.key_pair = key_pair.clone();
            std::thread::spawn(|| {
                let mut config = CONFIG.write().unwrap();
                config.key_pair = key_pair;
                // No server has confirmed this key yet: register it instead
                // of sending heartbeats for the key the server holds.
                config.key_confirmed = false;
                config.keys_confirmed = Default::default();
                config.store();
            });
        }
        *lock = Some(config.key_pair.clone());
        config.key_pair
    }

    pub fn get_cached_pk() -> Option<Vec<u8>> {
        KEY_PAIR.lock().unwrap().clone().map(|k| k.1)
    }

    /// Whether this process holds the device's secrets: its key pair, the
    /// stored permanent password and the secret options (the 2FA secret,
    /// [`SECRET_OPTIONS`]). True unless the client said otherwise with
    /// [`Config::set_holds_secrets`].
    pub fn holds_secrets() -> bool {
        SECRETS_HOLDER.load(std::sync::atomic::Ordering::SeqCst)
    }

    /// Sets whether this process holds the device's secrets (L442). Once the
    /// client is installed on Windows its service holds them, and the
    /// person's processes (the window, the connection manager) do not. A
    /// process that does not hold them never makes, loads or keeps one: its
    /// key pair is empty, or the holder's public key alone once it learned
    /// it ([`Config::set_holder_public_key`]), and it has no stored permanent
    /// password and no secret option. Storing its config keeps the secrets
    /// in its files as they are, so copies an older version wrote there stay
    /// until [`Config::remove_secrets_from_files`] takes them out.
    pub fn set_holds_secrets(holds: bool) {
        SECRETS_HOLDER.store(holds, std::sync::atomic::Ordering::SeqCst);
        // Loaded again: a holder's key or the public key alone
        *KEY_PAIR.lock().unwrap() = None;
        if !holds {
            let mut config = CONFIG.write().unwrap();
            config.key_pair = Default::default();
            config.password.clear();
            drop(config);
            remove_secret_options(&mut CONFIG2.write().unwrap().options);
        }
    }

    /// The holder's public key, for a process that does not hold the key.
    pub fn set_holder_public_key(public_key: Vec<u8>) {
        if Self::holds_secrets() || public_key.len() != sign::PUBLICKEYBYTES {
            return;
        }
        *KEY_PAIR.lock().unwrap() = Some((Vec::new(), public_key));
    }

    /// The secrets in this process's config files: a key pair with a secret
    /// key, a stored permanent password with its salt, secret options. None
    /// when the files hold none.
    pub fn secrets_in_files() -> Option<ProfileSecrets> {
        let mut config = Config::load_::<Config>("");
        let mut secrets = ProfileSecrets::default();
        if !config.key_pair.0.is_empty() {
            secrets.key_pair = Some(std::mem::take(&mut config.key_pair));
        }
        if !config.password.is_empty()
            && Self::validate_or_decrypt_permanent_password_storage(&mut config).is_ok()
            && !config.password.is_empty()
        {
            secrets.permanent_password = Some((config.password, config.salt));
        }
        let config2 = Config::load_::<Config2>("2");
        for key in SECRET_OPTIONS {
            if let Some(value) = config2.options.get(*key).filter(|value| !value.is_empty()) {
                secrets.options.insert((*key).to_owned(), value.clone());
            }
        }
        (!secrets.is_empty()).then_some(secrets)
    }

    /// Takes the secrets out of the config files of a process that does not
    /// hold them and leaves the rest of the files as they are. False in the
    /// holder, or when the files hold no secret.
    pub fn remove_secrets_from_files() -> bool {
        if Self::holds_secrets() {
            return false;
        }
        let mut removed = false;
        {
            // Holding CONFIG keeps this process's own stores out meanwhile
            let _config = CONFIG.write().unwrap();
            let mut stored = Config::load_::<Config>("");
            if stored.key_pair != KeyPair::default() || !stored.password.is_empty() {
                stored.key_pair = Default::default();
                stored.password.clear();
                Config::store_(&stored, "");
                removed = true;
            }
        }
        {
            let _config2 = CONFIG2.write().unwrap();
            let mut stored = Config::load_::<Config2>("2");
            let before = stored.options.len();
            remove_secret_options(&mut stored.options);
            if stored.options.len() != before {
                Config::store_(&stored, "2");
                removed = true;
            }
        }
        removed
    }

    /// Takes a key pair handed over by a process that does not hold the
    /// device's secrets: the copy an older version left in the person's
    /// profile (L442). Only when this process holds the secrets and has no
    /// key yet, and only an Ed25519 pair whose halves belong together. The
    /// key is registered again, so the server compares it with the one it
    /// holds.
    pub fn adopt_key_pair_if_none(key_pair: KeyPair) -> bool {
        if !Self::holds_secrets() || !is_ed25519_key_pair(&key_pair) {
            return false;
        }
        // Loaded first: loading may decrypt, which takes KEY_PAIR
        drop(CONFIG.read().unwrap());
        {
            let mut lock = KEY_PAIR.lock().unwrap();
            if lock.is_some() || !Config::load_::<Config>("").key_pair.0.is_empty() {
                return false;
            }
            *lock = Some(key_pair.clone());
        }
        let mut config = CONFIG.write().unwrap();
        config.key_pair = key_pair;
        config.key_confirmed = false;
        config.keys_confirmed = Default::default();
        config.store();
        true
    }

    /// Takes a stored permanent password and its salt handed over like
    /// [`Config::adopt_key_pair_if_none`]: only when this process holds the
    /// secrets, has no permanent password of its own and no preset one, and
    /// may change it.
    pub fn adopt_permanent_password_if_none(storage: &str, salt: &str) -> bool {
        if !Self::holds_secrets()
            || storage.is_empty()
            || Self::is_disable_change_permanent_password()
            || Self::has_usable_preset_password()
        {
            return false;
        }
        let mut config = CONFIG.write().unwrap();
        if !config.password.is_empty() {
            return false;
        }
        match Self::apply_permanent_password_storage_for_sync(&mut config, storage, salt) {
            Ok(true) => {
                config.store();
                drop(config);
                Self::clear_trusted_devices();
                true
            }
            _ => false,
        }
    }

    /// Takes a secret option handed over like
    /// [`Config::adopt_key_pair_if_none`]: only when this process holds the
    /// secrets and has no value for it.
    pub fn adopt_secret_option_if_none(key: &str, value: &str) -> bool {
        if !Self::holds_secrets()
            || !SECRET_OPTIONS.contains(&key)
            || value.is_empty()
            || !Self::get_option(key).is_empty()
        {
            return false;
        }
        Self::set_option(key.to_owned(), value.to_owned());
        true
    }

    /// This process's config for another process of the client, without the
    /// key pair and the stored permanent password: they never leave the
    /// process that holds them over IPC (L442).
    pub fn get_for_other_process() -> Config {
        let mut config = Self::get();
        config.key_pair = Default::default();
        config.password.clear();
        config
    }

    /// Takes a config another process of the client sent and keeps this
    /// process's key pair, stored permanent password and salt, whatever the
    /// config sent carries (L442).
    pub fn set_from_other_process(mut cfg: Config) -> bool {
        let own = CONFIG.read().unwrap();
        cfg.key_pair = own.key_pair.clone();
        cfg.password = own.password.clone();
        cfg.salt = own.salt.clone();
        drop(own);
        Self::set(cfg)
    }

    /// Takes the config the person's server process sends the root service
    /// on Linux and macOS. It keeps the root service's key pair; only while
    /// the root service has none does the key pair sent become its key, on a
    /// first start.
    pub fn set_from_user_server(mut cfg: Config) -> bool {
        let adopt = Self::holds_secrets() && Self::get_existing_key_pair().is_none();
        if !adopt {
            cfg.key_pair = CONFIG.read().unwrap().key_pair.clone();
        }
        Self::set(cfg)
    }

    /// Get existing key pair without generating a new one.
    /// Returns None if no key pair exists in cache or config file.
    pub fn get_existing_key_pair() -> Option<KeyPair> {
        let mut lock = KEY_PAIR.lock().unwrap();
        if let Some(p) = lock.as_ref() {
            return Some(p.clone());
        }
        if !Self::holds_secrets() {
            return None;
        }

        // IMPORTANT: this path is called while holding KEY_PAIR lock.
        // Config::load_ must remain a raw conf load/deserialize path and must never
        // call decrypt_* / symmetric_crypt (directly or indirectly), otherwise this
        // can re-enter key loading and deadlock.
        let config = Config::load_::<Config>("");
        if !config.key_pair.0.is_empty() {
            *lock = Some(config.key_pair.clone());
            Some(config.key_pair)
        } else {
            None
        }
    }

    pub fn no_register_device() -> bool {
        BUILTIN_SETTINGS
            .read()
            .unwrap()
            .get(keys::OPTION_REGISTER_DEVICE)
            .map(|v| v == "N")
            .unwrap_or(false)
    }

    pub fn is_disable_change_permanent_password() -> bool {
        BUILTIN_SETTINGS
            .read()
            .unwrap()
            .get(keys::OPTION_DISABLE_CHANGE_PERMANENT_PASSWORD)
            .map(|v| v == "Y")
            .unwrap_or(false)
    }

    pub fn is_disable_change_id() -> bool {
        BUILTIN_SETTINGS
            .read()
            .unwrap()
            .get(keys::OPTION_DISABLE_CHANGE_ID)
            .map(|v| v == "Y")
            .unwrap_or(false)
    }

    pub fn is_disable_unlock_pin() -> bool {
        BUILTIN_SETTINGS
            .read()
            .unwrap()
            .get(keys::OPTION_DISABLE_UNLOCK_PIN)
            .map(|v| v == "Y")
            .unwrap_or(false)
    }

    pub fn get_id() -> String {
        let mut id = CONFIG.read().unwrap().id.clone();
        if id.is_empty() {
            if let Some(tmp) = Config::gen_id() {
                id = tmp;
                Config::set_id(&id);
            }
        }
        id
    }

    pub fn get_id_or(b: String) -> String {
        let a = CONFIG.read().unwrap().id.clone();
        if a.is_empty() {
            b
        } else {
            a
        }
    }

    pub fn get_options() -> HashMap<String, String> {
        let mut res = DEFAULT_SETTINGS.read().unwrap().clone();
        res.extend(CONFIG2.read().unwrap().options.clone());
        res.extend(OVERWRITE_SETTINGS.read().unwrap().clone());
        res
    }

    #[inline]
    fn purify_options(v: &mut HashMap<String, String>) {
        v.retain(|k, v| is_option_can_save(&OVERWRITE_SETTINGS, k, &DEFAULT_SETTINGS, v));
    }

    /// The options for another process of the client, without the secret
    /// options (L442).
    pub fn get_options_for_other_process() -> HashMap<String, String> {
        let mut options = Self::get_options();
        remove_secret_options(&mut options);
        options
    }

    /// Takes the options another process of the client sent and keeps this
    /// process's secret options, whatever the options sent carry (L442).
    pub fn set_options_from_other_process(mut v: HashMap<String, String>) {
        keep_secret_options(&mut v, &CONFIG2.read().unwrap().options);
        Self::set_options(v);
    }

    pub fn set_options(mut v: HashMap<String, String>) {
        Self::purify_options(&mut v);
        if !Self::holds_secrets() {
            remove_secret_options(&mut v);
        }
        let mut config = CONFIG2.write().unwrap();
        if config.options == v {
            return;
        }
        config.options = v;
        config.store();
    }

    pub fn get_option(k: &str) -> String {
        get_or(
            &OVERWRITE_SETTINGS,
            &CONFIG2.read().unwrap().options,
            &DEFAULT_SETTINGS,
            k,
        )
        .unwrap_or_default()
    }

    pub fn get_bool_option(k: &str) -> bool {
        option2bool(k, &Self::get_option(k))
    }

    pub fn set_option(k: String, v: String) {
        if !Self::holds_secrets() && SECRET_OPTIONS.contains(&k.as_str()) {
            // The process that holds the device's secrets sets it (L442)
            return;
        }
        if !is_option_can_save(&OVERWRITE_SETTINGS, &k, &DEFAULT_SETTINGS, &v) {
            let mut config = CONFIG2.write().unwrap();
            if config.options.remove(&k).is_some() {
                config.store();
            }
            return;
        }
        let mut config = CONFIG2.write().unwrap();
        let v2 = if v.is_empty() { None } else { Some(&v) };
        if v2 != config.options.get(&k) {
            if v2.is_none() {
                config.options.remove(&k);
            } else {
                config.options.insert(k, v);
            }
            config.store();
        }
    }

    pub fn update_id() {
        // to-do: how about if one ip register a lot of ids?
        let id = Self::get_id();
        let mut rng = rand::thread_rng();
        let new_id = rng.gen_range(1_000_000_000..2_000_000_000).to_string();
        Config::set_id(&new_id);
        log::info!("id updated from {} to {}", id, new_id);
    }

    /// Sets the local permanent password.
    ///
    /// Returns `true` when the password is accepted or already matches the effective
    /// preset password. Returns `false` when changing the password is disabled or
    /// the new password cannot be prepared for storage.
    pub fn set_permanent_password(password: &str) -> bool {
        if Self::is_disable_change_permanent_password() || !Self::holds_secrets() {
            // A process that does not hold the device's secrets asks the
            // holder to change it (L442)
            return false;
        }
        let (preset_storage, preset_salt) = Self::get_preset_password_storage_and_salt();
        if preset_permanent_password_storage_matches_plain(&preset_storage, &preset_salt, password)
        {
            if CONFIG.read().unwrap().password.is_empty() {
                return true;
            }
        }

        let mut config = CONFIG.write().unwrap();

        let stored = if password.is_empty() {
            Some(String::new())
        } else {
            Self::compute_permanent_password_storage_for_update(&mut config, password)
        };
        let Some(stored) = stored else {
            log::error!("Failed to compute permanent password storage; refusing update");
            return false;
        };
        if stored == config.password {
            return true;
        }
        config.password = stored;
        config.store();
        Self::clear_trusted_devices();
        true
    }

    fn compute_permanent_password_storage_for_update(
        config: &mut Config,
        password: &str,
    ) -> Option<String> {
        // Keep salt stable for user-initiated permanent password updates.
        // Salt should only change when service->user sync updates storage and salt as a pair.
        Self::ensure_permanent_password_salt(config);
        let h1 = compute_permanent_password_h1(password, &config.salt);
        encode_permanent_password_encrypted_storage_from_h1(&h1)
    }

    /// Returns the locally persisted permanent password storage and salt (NOT the hard/preset one).
    ///
    /// This function is side-effect free:
    /// - It does NOT call `get_salt()` (which may auto-generate salt).
    /// - It returns a consistent snapshot under a single lock.
    pub fn get_local_permanent_password_storage_and_salt() -> (String, String) {
        let config = CONFIG.read().unwrap();
        (config.password.clone(), config.salt.clone())
    }

    /// Persist permanent password storage and salt from service->user config sync.
    pub fn set_permanent_password_storage_for_sync(
        storage: &str,
        salt: &str,
    ) -> crate::ResultType<bool> {
        if !Self::holds_secrets() {
            return Ok(false);
        }
        let mut config = CONFIG.write().unwrap();
        if !Self::apply_permanent_password_storage_for_sync(&mut config, storage, salt)? {
            return Ok(false);
        }

        config.store();
        Self::clear_trusted_devices();
        Ok(true)
    }

    fn apply_permanent_password_storage_for_sync(
        config: &mut Config,
        storage: &str,
        salt: &str,
    ) -> Result<bool> {
        if storage.is_empty() {
            if config.password.is_empty() && (salt.is_empty() || config.salt == salt) {
                return Ok(false);
            }
            config.password.clear();
            if !salt.is_empty() {
                config.salt = salt.to_owned();
            }
            return Ok(true);
        }
        if salt.is_empty() {
            return Err(anyhow!(
                "Refusing to persist permanent password storage without salt"
            ));
        }
        if decode_permanent_password_h1_from_storage(storage).is_none() {
            log::error!("Rejecting non-current permanent password storage sync payload");
            return Err(anyhow!("Invalid permanent password storage sync payload"));
        }
        if config.password == storage && config.salt == salt {
            return Ok(false);
        }

        config.password = storage.to_owned();
        config.salt = salt.to_owned();
        Ok(true)
    }

    pub fn has_permanent_password() -> bool {
        let (local_storage, local_salt) = Self::get_local_permanent_password_storage_and_salt();
        if !local_storage.is_empty() {
            return local_permanent_password_storage_is_usable_for_auth(
                &local_storage,
                &local_salt,
            );
        }
        Self::has_usable_preset_password()
    }

    fn has_usable_preset_password() -> bool {
        let (preset_storage, preset_salt) = Self::get_preset_password_storage_and_salt();
        preset_permanent_password_storage_is_usable_for_auth(&preset_storage, &preset_salt)
    }

    pub fn is_using_preset_password() -> bool {
        let (local_storage, _) = Self::get_local_permanent_password_storage_and_salt();
        local_storage.is_empty() && Self::has_usable_preset_password()
    }

    pub fn get_preset_password_storage_and_salt() -> (String, String) {
        let hard_settings = HARD_SETTINGS.read().unwrap();
        let storage = hard_settings.get("password").cloned().unwrap_or_default();
        let salt = hard_settings.get("salt").cloned().unwrap_or_default();
        (storage, salt)
    }

    pub fn get_effective_permanent_password_salt() -> String {
        let (local_storage, local_salt) = Self::get_local_permanent_password_storage_and_salt();
        if !local_storage.is_empty() {
            if local_permanent_password_storage_is_usable_for_auth(&local_storage, &local_salt) {
                return Self::get_salt();
            }
            return String::new();
        }
        let (preset_storage, preset_salt) = Self::get_preset_password_storage_and_salt();
        if !preset_salt.is_empty() {
            if preset_permanent_password_storage_is_usable_for_auth(&preset_storage, &preset_salt) {
                return preset_salt;
            }
            return String::new();
        }
        Self::get_salt()
    }

    pub fn has_local_permanent_password() -> bool {
        let (local_storage, local_salt) = Self::get_local_permanent_password_storage_and_salt();
        local_permanent_password_storage_is_usable_for_auth(&local_storage, &local_salt)
    }

    // This shouldn't happen under normal circumstances because the salt
    // should be automatically generated when migrating to hash storage.
    // Actually, it is better to avoid calling set_salt at all.
    pub fn set_salt(salt: &str) {
        let mut config = CONFIG.write().unwrap();
        if salt == config.salt {
            return;
        }
        if !password_is_empty_or_not_hashed(&config.password) {
            if config.salt.is_empty() {
                log::warn!("Salt is empty but permanent password is hashed and salt is empty");
            } else {
                log::error!("Refusing to set salt because permanent password is hashed");
                return;
            }
        }
        config.salt = salt.into();
        config.store();
    }

    pub fn get_salt() -> String {
        let config = CONFIG.read().unwrap();
        let mut salt = config.salt.clone();
        if salt.is_empty() {
            drop(config);
            salt = Config::get_auto_password(DEFAULT_SALT_LEN);
            Config::set_salt(&salt);
        }
        salt
    }

    pub fn set_socks(socks: Option<Socks5Server>) {
        if OVERWRITE_SETTINGS
            .read()
            .unwrap()
            .contains_key(keys::OPTION_PROXY_URL)
        {
            return;
        }

        let mut config = CONFIG2.write().unwrap();
        if config.socks == socks {
            return;
        }
        if config.socks.is_none() {
            let equal_to_default = |key: &str, value: &str| {
                DEFAULT_SETTINGS
                    .read()
                    .unwrap()
                    .get(key)
                    .map_or(false, |x| *x == value)
            };
            let contains_url = DEFAULT_SETTINGS
                .read()
                .unwrap()
                .get(keys::OPTION_PROXY_URL)
                .is_some();
            let url = equal_to_default(
                keys::OPTION_PROXY_URL,
                &socks.clone().unwrap_or_default().proxy,
            );
            let username = equal_to_default(
                keys::OPTION_PROXY_USERNAME,
                &socks.clone().unwrap_or_default().username,
            );
            let password = equal_to_default(
                keys::OPTION_PROXY_PASSWORD,
                &socks.clone().unwrap_or_default().password,
            );
            if contains_url && url && username && password {
                return;
            }
        }
        config.socks = socks;
        config.store();
    }

    #[inline]
    fn get_socks_from_custom_client_advanced_settings(
        settings: &HashMap<String, String>,
    ) -> Option<Socks5Server> {
        let url = settings.get(keys::OPTION_PROXY_URL)?;
        Some(Socks5Server {
            proxy: url.to_owned(),
            username: settings
                .get(keys::OPTION_PROXY_USERNAME)
                .map(|x| x.to_string())
                .unwrap_or_default(),
            password: settings
                .get(keys::OPTION_PROXY_PASSWORD)
                .map(|x| x.to_string())
                .unwrap_or_default(),
        })
    }

    pub fn get_socks() -> Option<Socks5Server> {
        Self::get_socks_from_custom_client_advanced_settings(&OVERWRITE_SETTINGS.read().unwrap())
            .or(CONFIG2.read().unwrap().socks.clone())
            .or(Self::get_socks_from_custom_client_advanced_settings(
                &DEFAULT_SETTINGS.read().unwrap(),
            ))
    }

    #[inline]
    pub fn is_proxy() -> bool {
        Self::get_network_type() != NetworkType::Direct
    }

    pub fn get_network_type() -> NetworkType {
        if OVERWRITE_SETTINGS
            .read()
            .unwrap()
            .get(keys::OPTION_PROXY_URL)
            .is_some()
        {
            return NetworkType::ProxySocks;
        }
        if CONFIG2.read().unwrap().socks.is_some() {
            return NetworkType::ProxySocks;
        }
        if DEFAULT_SETTINGS
            .read()
            .unwrap()
            .get(keys::OPTION_PROXY_URL)
            .is_some()
        {
            return NetworkType::ProxySocks;
        }
        NetworkType::Direct
    }

    pub fn get_unlock_pin() -> String {
        if Self::is_disable_unlock_pin() {
            return String::new();
        }
        CONFIG2.read().unwrap().unlock_pin.clone()
    }

    pub fn set_unlock_pin(pin: &str) {
        if Self::is_disable_unlock_pin() {
            return;
        }
        let mut config = CONFIG2.write().unwrap();
        if pin == config.unlock_pin {
            return;
        }
        config.unlock_pin = pin.to_string();
        config.store();
    }

    pub fn get_trusted_devices_json() -> String {
        serde_json::to_string(&Self::get_trusted_devices()).unwrap_or_default()
    }

    pub fn get_trusted_devices() -> Vec<TrustedDevice> {
        let (devices, synced) = TRUSTED_DEVICES.read().unwrap().clone();
        if synced {
            return devices;
        }
        let devices = CONFIG2.read().unwrap().trusted_devices.clone();
        let (devices, succ, store) = decrypt_str_or_original(&devices, PASSWORD_ENC_VERSION);
        if succ {
            let mut devices: Vec<TrustedDevice> =
                serde_json::from_str(&devices).unwrap_or_default();
            let len = devices.len();
            devices.retain(|d| !d.outdate());
            if store || devices.len() != len {
                Self::set_trusted_devices(devices.clone());
            }
            *TRUSTED_DEVICES.write().unwrap() = (devices.clone(), true);
            devices
        } else {
            Default::default()
        }
    }

    fn set_trusted_devices(mut trusted_devices: Vec<TrustedDevice>) {
        trusted_devices.retain(|d| !d.outdate());
        let devices = serde_json::to_string(&trusted_devices).unwrap_or_default();
        let max_len = 1024 * 1024;
        if devices.bytes().len() > max_len {
            log::error!("Trusted devices too large: {}", devices.bytes().len());
            return;
        }
        let devices = encrypt_str_or_original(&devices, PASSWORD_ENC_VERSION, max_len);
        let mut config = CONFIG2.write().unwrap();
        config.trusted_devices = devices;
        config.store();
        *TRUSTED_DEVICES.write().unwrap() = (trusted_devices, true);
    }

    pub fn add_trusted_device(device: TrustedDevice) {
        let mut devices = Self::get_trusted_devices();
        devices.retain(|d| d.hwid != device.hwid);
        devices.push(device);
        Self::set_trusted_devices(devices);
    }

    pub fn remove_trusted_devices(hwids: &Vec<Bytes>) {
        let mut devices = Self::get_trusted_devices();
        devices.retain(|d| !hwids.contains(&d.hwid));
        Self::set_trusted_devices(devices);
    }

    pub fn clear_trusted_devices() {
        Self::set_trusted_devices(Default::default());
    }

    pub fn get() -> Config {
        return CONFIG.read().unwrap().clone();
    }

    // TODO: `Config::set()` does not invalidate trusted devices when permanent password/salt changes.
    // This matches historical behavior, but may need revisiting in a separate PR.
    pub fn set(mut cfg: Config) -> bool {
        if !Self::holds_secrets() {
            cfg.key_pair = Default::default();
            cfg.password.clear();
        }
        let mut lock = CONFIG.write().unwrap();
        if *lock == cfg {
            return false;
        }
        *lock = cfg;
        lock.store();
        // Drop CONFIG lock before acquiring KEY_PAIR lock to avoid potential deadlock.
        #[cfg(target_os = "macos")]
        let new_key_pair = lock.key_pair.clone();
        drop(lock);
        #[cfg(target_os = "macos")]
        Self::invalidate_key_pair_cache_if_changed(&new_key_pair);
        true
    }

    /// Invalidate KEY_PAIR cache if it differs from the new key_pair.
    /// Use None to invalidate the cache instead of Some(key_pair).
    /// If we use Some with an empty key_pair, get_key_pair() would always return
    /// the empty key_pair from cache without regenerating.
    /// By clearing the cache, get_key_pair() will reload and regenerate if needed.
    #[cfg(target_os = "macos")]
    fn invalidate_key_pair_cache_if_changed(new_key_pair: &KeyPair) {
        let mut key_pair_cache = KEY_PAIR.lock().unwrap();
        if let Some(cached) = key_pair_cache.as_ref() {
            if cached != new_key_pair {
                *key_pair_cache = None;
                log::info!("key pair cache invalidated");
            }
        }
    }

    fn with_extension(path: PathBuf) -> PathBuf {
        let ext = path.extension();
        if let Some(ext) = ext {
            let ext = format!("{}.toml", ext.to_string_lossy());
            path.with_extension(ext)
        } else {
            path.with_extension("toml")
        }
    }
}

const PEERS: &str = "peers";

impl PeerConfig {
    pub fn load(id: &str) -> PeerConfig {
        let _lock = CONFIG.read().unwrap();
        match confy::load_path(Self::path(id)) {
            Ok(config) => {
                let mut config: PeerConfig = config;
                let mut store = false;
                let (password, _, store2) =
                    decrypt_vec_or_original(&config.password, PASSWORD_ENC_VERSION);
                config.password = password;
                store = store || store2;
                for opt in ["rdp_password", "os-username", "os-password"] {
                    if let Some(v) = config.options.get_mut(opt) {
                        let (encrypted, _, store2) =
                            decrypt_str_or_original(v, PASSWORD_ENC_VERSION);
                        *v = encrypted;
                        store = store || store2;
                    }
                }
                if store {
                    config.store_(id);
                }
                config
            }
            Err(err) => {
                if let confy::ConfyError::GeneralLoadError(err) = &err {
                    if err.kind() == std::io::ErrorKind::NotFound {
                        return Default::default();
                    }
                }
                log::error!("Failed to load peer config '{}': {}", id, err);
                Default::default()
            }
        }
    }

    pub fn store(&self, id: &str) {
        let _lock = CONFIG.read().unwrap();
        self.store_(id);
    }

    fn store_(&self, id: &str) {
        let mut config = self.clone();
        config.password =
            encrypt_vec_or_original(&config.password, PASSWORD_ENC_VERSION, ENCRYPT_MAX_LEN);
        for opt in ["rdp_password", "os-username", "os-password"] {
            if let Some(v) = config.options.get_mut(opt) {
                *v = encrypt_str_or_original(v, PASSWORD_ENC_VERSION, ENCRYPT_MAX_LEN)
            }
        }
        if let Err(err) = store_path(Self::path(id), config) {
            log::error!("Failed to store config: {}", err);
        }
        NEW_STORED_PEER_CONFIG.lock().unwrap().insert(id.to_owned());
    }

    pub fn remove(id: &str) {
        fs::remove_file(Self::path(id)).ok();
    }

    fn path(id: &str) -> PathBuf {
        //If the id contains invalid chars, encode it
        let forbidden_paths = Regex::new(r".*[<>:/\\|\?\*].*");
        let path: PathBuf;
        if let Ok(forbidden_paths) = forbidden_paths {
            let id_encoded = if forbidden_paths.is_match(id) {
                "base64_".to_string() + base64::encode(id, base64::Variant::Original).as_str()
            } else {
                id.to_string()
            };
            path = [PEERS, id_encoded.as_str()].iter().collect();
        } else {
            log::warn!("Regex create failed: {:?}", forbidden_paths.err());
            // fallback for failing to create this regex.
            path = [PEERS, id.replace(":", "_").as_str()].iter().collect();
        }
        Config::with_extension(Config::path(path))
    }

    // The number of peers to load in the first round when showing the peers card list in the main window.
    // When there're too many peers, loading all of them at once will take a long time.
    // We can load them in two rouds, the first round loads the first 100 peers, and the second round loads the rest.
    // Then the UI will show the first 100 peers first, and the rest will be loaded and shown later.
    pub const BATCH_LOADING_COUNT: usize = 100;

    pub fn get_vec_id_modified_time_path(
        id_filters: &Option<Vec<String>>,
    ) -> Vec<(String, SystemTime, PathBuf)> {
        if let Ok(peers) = Config::path(PEERS).read_dir() {
            let mut vec_id_modified_time_path = peers
                .into_iter()
                .filter_map(|res| match res {
                    Ok(res) => {
                        let p = res.path();
                        if p.is_file()
                            && p.extension().map(|p| p.to_str().unwrap_or("")) == Some("toml")
                        {
                            Some(p)
                        } else {
                            None
                        }
                    }
                    _ => None,
                })
                .map(|p| {
                    let id = p
                        .file_stem()
                        .map(|p| p.to_str().unwrap_or(""))
                        .unwrap_or("")
                        .to_owned();

                    let id_decoded_string = if id.starts_with("base64_") && id.len() != 7 {
                        let id_decoded =
                            base64::decode(&id[7..], base64::Variant::Original).unwrap_or_default();
                        String::from_utf8_lossy(&id_decoded).as_ref().to_owned()
                    } else {
                        id
                    };
                    (id_decoded_string, p)
                })
                .filter(|(id, _)| {
                    let Some(filters) = id_filters else {
                        return true;
                    };
                    filters.contains(id)
                })
                .map(|(id, p)| {
                    let t = crate::get_modified_time(&p);
                    (id, t, p)
                })
                .collect::<Vec<_>>();
            vec_id_modified_time_path.sort_unstable_by(|a, b| b.1.cmp(&a.1));
            vec_id_modified_time_path
        } else {
            vec![]
        }
    }

    #[inline]
    async fn preload_file_async(path: PathBuf) {
        let _ = tokio::fs::File::open(path).await;
    }

    #[tokio::main(flavor = "current_thread")]
    async fn preload_peers_async() {
        let now = std::time::Instant::now();
        let vec_id_modified_time_path = Self::get_vec_id_modified_time_path(&None);
        let total_count = vec_id_modified_time_path.len();
        let mut futs = vec![];
        for (_, _, path) in vec_id_modified_time_path.into_iter() {
            futs.push(Self::preload_file_async(path));
            if futs.len() >= Self::BATCH_LOADING_COUNT {
                let first_load_start = std::time::Instant::now();
                futures::future::join_all(futs).await;
                if first_load_start.elapsed().as_millis() < 10 {
                    // No need to preload the rest if the first load is fast.
                    return;
                }
                futs = vec![];
            }
        }
        if !futs.is_empty() {
            futures::future::join_all(futs).await;
        }
        log::info!(
            "Preload peers done in {:?}, batch_count: {}, total: {}",
            now.elapsed(),
            Self::BATCH_LOADING_COUNT,
            total_count
        );
    }

    // We have to preload all peers in a background thread.
    // Because we find that opening files the first time after the system (Windows) booting will be very slow, up to 200~400ms.
    // The reason is that the Windows has "Microsoft Defender Antivirus Service" running in the background, which will scan the file when it's opened the first time.
    // So we have to preload all peers in a background thread to avoid the delay when opening the file the first time.
    // We can temporarily stop "Microsoft Defender Antivirus Service" or add the fold to the white list, to verify this. But don't do this in the release version.
    pub fn preload_peers() {
        std::thread::spawn(|| {
            Self::preload_peers_async();
        });
    }

    pub fn peers(id_filters: Option<Vec<String>>) -> Vec<(String, SystemTime, PeerConfig)> {
        let vec_id_modified_time_path = Self::get_vec_id_modified_time_path(&id_filters);
        Self::batch_peers(
            &vec_id_modified_time_path,
            0,
            Some(vec_id_modified_time_path.len()),
        )
        .0
    }

    pub fn batch_peers(
        all: &Vec<(String, SystemTime, PathBuf)>,
        from: usize,
        to: Option<usize>,
    ) -> (Vec<(String, SystemTime, PeerConfig)>, usize) {
        if from >= all.len() {
            return (vec![], 0);
        }

        let to = match to {
            Some(to) => to.min(all.len()),
            None => (from + Self::BATCH_LOADING_COUNT).min(all.len()),
        };

        // to <= from is unexpected, but we can just return an empty vec in this case.
        if to <= from {
            return (vec![], from);
        }

        let peers: Vec<_> = all[from..to]
            .iter()
            .map(|(id, t, p)| {
                let c = PeerConfig::load(&id);
                if c.info.platform.is_empty() {
                    fs::remove_file(p).ok();
                }
                (id.clone(), t.clone(), c)
            })
            .filter(|p| !p.2.info.platform.is_empty())
            .collect();
        (peers, to)
    }

    pub fn exists(id: &str) -> bool {
        Self::path(id).exists()
    }

    serde_field_string!(
        default_view_style,
        deserialize_view_style,
        UserDefaultConfig::read(keys::OPTION_VIEW_STYLE)
    );
    serde_field_string!(
        default_scroll_style,
        deserialize_scroll_style,
        UserDefaultConfig::read(keys::OPTION_SCROLL_STYLE)
    );
    serde_field_string!(
        default_image_quality,
        deserialize_image_quality,
        UserDefaultConfig::read(keys::OPTION_IMAGE_QUALITY)
    );
    serde_field_string!(
        default_reverse_mouse_wheel,
        deserialize_reverse_mouse_wheel,
        UserDefaultConfig::read(keys::OPTION_REVERSE_MOUSE_WHEEL)
    );
    serde_field_string!(
        default_displays_as_individual_windows,
        deserialize_displays_as_individual_windows,
        UserDefaultConfig::read(keys::OPTION_DISPLAYS_AS_INDIVIDUAL_WINDOWS)
    );
    serde_field_string!(
        default_use_all_my_displays_for_the_remote_session,
        deserialize_use_all_my_displays_for_the_remote_session,
        UserDefaultConfig::read(keys::OPTION_USE_ALL_MY_DISPLAYS_FOR_THE_REMOTE_SESSION)
    );

    fn default_custom_image_quality() -> Vec<i32> {
        let f: f64 = UserDefaultConfig::read(keys::OPTION_CUSTOM_IMAGE_QUALITY)
            .parse()
            .unwrap_or(50.0);
        vec![f as _]
    }

    fn deserialize_custom_image_quality<'de, D>(deserializer: D) -> Result<Vec<i32>, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        let v: Vec<i32> = de::Deserialize::deserialize(deserializer)?;
        if v.len() == 1 && v[0] >= 10 && v[0] <= 0xFFF {
            Ok(v)
        } else {
            Ok(Self::default_custom_image_quality())
        }
    }

    fn default_options() -> HashMap<String, String> {
        let mut mp: HashMap<String, String> = Default::default();
        let _ = [
            keys::OPTION_CODEC_PREFERENCE,
            keys::OPTION_CUSTOM_FPS,
            keys::OPTION_FPS_MODE,
            keys::OPTION_ZOOM_CURSOR,
            keys::OPTION_I444,
            keys::OPTION_SWAP_LEFT_RIGHT_MOUSE,
            keys::OPTION_COLLAPSE_TOOLBAR,
        ]
        .map(|key| {
            mp.insert(key.to_owned(), UserDefaultConfig::read(key));
        });
        mp
    }

    fn default_trackpad_speed() -> i32 {
        UserDefaultConfig::read(keys::OPTION_TRACKPAD_SPEED)
            .parse()
            .unwrap_or(100)
    }

    fn deserialize_trackpad_speed<'de, D>(deserializer: D) -> Result<i32, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        let v: i32 = de::Deserialize::deserialize(deserializer)?;
        if v >= 10 && v <= 1000 {
            Ok(v)
        } else {
            Ok(Self::default_trackpad_speed())
        }
    }

    fn default_edge_scroll_edge_thickness() -> i32 {
        UserDefaultConfig::read(keys::OPTION_EDGE_SCROLL_EDGE_THICKNESS)
            .parse()
            .unwrap_or(100)
    }

    fn deserialize_edge_scroll_edge_thickness<'de, D>(deserializer: D) -> Result<i32, D::Error>
    where
        D: de::Deserializer<'de>,
    {
        let v: i32 = de::Deserialize::deserialize(deserializer)?;
        if v >= 20 && v <= 150 {
            Ok(v)
        } else {
            Ok(Self::default_edge_scroll_edge_thickness())
        }
    }
}

serde_field_bool!(
    ShowRemoteCursor,
    "show_remote_cursor",
    default_show_remote_cursor,
    "ShowRemoteCursor::default_show_remote_cursor"
);
serde_field_bool!(
    FollowRemoteCursor,
    "follow_remote_cursor",
    default_follow_remote_cursor,
    "FollowRemoteCursor::default_follow_remote_cursor"
);

serde_field_bool!(
    FollowRemoteWindow,
    "follow_remote_window",
    default_follow_remote_window,
    "FollowRemoteWindow::default_follow_remote_window"
);
serde_field_bool!(
    ShowQualityMonitor,
    "show_quality_monitor",
    default_show_quality_monitor,
    "ShowQualityMonitor::default_show_quality_monitor"
);
serde_field_bool!(
    DisableAudio,
    "disable_audio",
    default_disable_audio,
    "DisableAudio::default_disable_audio"
);
serde_field_bool!(
    EnableFileCopyPaste,
    "enable-file-copy-paste",
    default_enable_file_copy_paste,
    "EnableFileCopyPaste::default_enable_file_copy_paste"
);
serde_field_bool!(
    DisableClipboard,
    "disable_clipboard",
    default_disable_clipboard,
    "DisableClipboard::default_disable_clipboard"
);
serde_field_bool!(
    LockAfterSessionEnd,
    "lock_after_session_end",
    default_lock_after_session_end,
    "LockAfterSessionEnd::default_lock_after_session_end"
);
serde_field_bool!(
    TerminalPersistent,
    "terminal-persistent",
    default_terminal_persistent,
    "TerminalPersistent::default_terminal_persistent"
);
serde_field_bool!(
    PrivacyMode,
    "privacy_mode",
    default_privacy_mode,
    "PrivacyMode::default_privacy_mode"
);

serde_field_bool!(
    AllowSwapKey,
    "allow_swap_key",
    default_allow_swap_key,
    "AllowSwapKey::default_allow_swap_key"
);

serde_field_bool!(
    ViewOnly,
    "view_only",
    default_view_only,
    "ViewOnly::default_view_only"
);

serde_field_bool!(
    ShowMyCursor,
    "show_my_cursor",
    default_show_my_cursor,
    "ShowMyCursor::default_show_my_cursor"
);

serde_field_bool!(
    SyncInitClipboard,
    "sync-init-clipboard",
    default_sync_init_clipboard,
    "SyncInitClipboard::default_sync_init_clipboard"
);

#[derive(Debug, Default, Serialize, Deserialize, Clone)]
pub struct LocalConfig {
    #[serde(default, deserialize_with = "deserialize_string")]
    remote_id: String, // latest used one
    #[serde(default, deserialize_with = "deserialize_string")]
    kb_layout_type: String,
    #[serde(default, deserialize_with = "deserialize_size")]
    size: Size,
    #[serde(default, deserialize_with = "deserialize_vec_string")]
    pub fav: Vec<String>,
    // NeoDesk incoming-only connection policy. Scalars must come before the
    // maps below: `confy` serialises through `toml` 0.5, which emits maps as
    // tables and rejects any primitive value that follows one. With a scalar
    // after a table every save failed with
    //   "Failed to serialize configuration data into TOML"
    // and the `_local` config silently stopped persisting (issue #497).
    #[serde(default, deserialize_with = "deserialize_string")]
    neodesk_connection_mode: String,
    #[serde(default)]
    neodesk_connection_mode_revision: u64,
    #[serde(default, deserialize_with = "deserialize_string")]
    neodesk_connection_mode_command_id: String,
    #[serde(default, deserialize_with = "deserialize_string")]
    neodesk_connection_mode_status: String,
    #[serde(default, deserialize_with = "deserialize_string")]
    neodesk_connection_mode_error: String,
    // Maps last (see the note above): emitted as TOML tables.
    #[serde(default, deserialize_with = "deserialize_hashmap_string_string")]
    options: HashMap<String, String>,
    // Various data for flutter ui
    #[serde(default, deserialize_with = "deserialize_hashmap_string_string")]
    ui_flutter: HashMap<String, String>,
}

impl LocalConfig {
    fn load() -> LocalConfig {
        Config::load_::<LocalConfig>("_local")
    }

    fn store(&self) {
        Config::store_(self, "_local");
    }

    pub fn get_kb_layout_type() -> String {
        LOCAL_CONFIG.read().unwrap().kb_layout_type.clone()
    }

    pub fn set_kb_layout_type(kb_layout_type: String) {
        let mut config = LOCAL_CONFIG.write().unwrap();
        config.kb_layout_type = kb_layout_type;
        config.store();
    }

    pub fn get_size() -> Size {
        LOCAL_CONFIG.read().unwrap().size
    }

    pub fn set_size(x: i32, y: i32, w: i32, h: i32) {
        let mut config = LOCAL_CONFIG.write().unwrap();
        let size = (x, y, w, h);
        if size == config.size || size.2 < 300 || size.3 < 300 {
            return;
        }
        config.size = size;
        config.store();
    }

    pub fn set_remote_id(remote_id: &str) {
        let mut config = LOCAL_CONFIG.write().unwrap();
        if remote_id == config.remote_id {
            return;
        }
        config.remote_id = remote_id.into();
        config.store();
    }

    pub fn get_remote_id() -> String {
        LOCAL_CONFIG.read().unwrap().remote_id.clone()
    }

    pub fn set_fav(fav: Vec<String>) {
        let mut lock = LOCAL_CONFIG.write().unwrap();
        if lock.fav == fav {
            return;
        }
        lock.fav = fav;
        lock.store();
    }

    pub fn get_fav() -> Vec<String> {
        LOCAL_CONFIG.read().unwrap().fav.clone()
    }

    pub fn get_option(k: &str) -> String {
        get_or(
            &OVERWRITE_LOCAL_SETTINGS,
            &LOCAL_CONFIG.read().unwrap().options,
            &DEFAULT_LOCAL_SETTINGS,
            k,
        )
        .unwrap_or_default()
    }

    // Usually get_option should be used.
    pub fn get_option_from_file(k: &str) -> String {
        get_or(
            &OVERWRITE_LOCAL_SETTINGS,
            &Self::load().options,
            &DEFAULT_LOCAL_SETTINGS,
            k,
        )
        .unwrap_or_default()
    }

    pub fn get_bool_option(k: &str) -> bool {
        option2bool(k, &Self::get_option(k))
    }

    pub fn set_option(k: String, v: String) {
        if !is_option_can_save(&OVERWRITE_LOCAL_SETTINGS, &k, &DEFAULT_LOCAL_SETTINGS, &v) {
            let mut config = LOCAL_CONFIG.write().unwrap();
            if config.options.remove(&k).is_some() {
                config.store();
            }
            return;
        }
        let mut config = LOCAL_CONFIG.write().unwrap();
        // The custom client will explictly set "default" as the default language.
        let is_custom_client_default_lang = k == keys::OPTION_LANGUAGE && v == "default";
        if is_custom_client_default_lang {
            config.options.insert(k, "".to_owned());
            config.store();
            return;
        }
        let v2 = if v.is_empty() { None } else { Some(&v) };
        if v2 != config.options.get(&k) {
            if v2.is_none() {
                config.options.remove(&k);
            } else {
                config.options.insert(k, v);
            }
            config.store();
        }
    }

    pub fn get_flutter_option(k: &str) -> String {
        get_or(
            &OVERWRITE_LOCAL_SETTINGS,
            &LOCAL_CONFIG.read().unwrap().ui_flutter,
            &DEFAULT_LOCAL_SETTINGS,
            k,
        )
        .unwrap_or_default()
    }

    pub fn set_flutter_option(k: String, v: String) {
        let mut config = LOCAL_CONFIG.write().unwrap();
        let v2 = if v.is_empty() { None } else { Some(&v) };
        if v2 != config.ui_flutter.get(&k) {
            if v2.is_none() {
                config.ui_flutter.remove(&k);
            } else {
                config.ui_flutter.insert(k, v);
            }
            config.store();
        }
    }

    pub fn get_connection_mode() -> String {
        LOCAL_CONFIG
            .read()
            .unwrap()
            .neodesk_connection_mode
            .clone()
    }

    pub fn get_connection_mode_revision() -> u64 {
        LOCAL_CONFIG
            .read()
            .unwrap()
            .neodesk_connection_mode_revision
    }

    pub fn get_connection_mode_command_id() -> String {
        LOCAL_CONFIG
            .read()
            .unwrap()
            .neodesk_connection_mode_command_id
            .clone()
    }

    pub fn get_connection_mode_status() -> String {
        LOCAL_CONFIG
            .read()
            .unwrap()
            .neodesk_connection_mode_status
            .clone()
    }

    pub fn get_connection_mode_error() -> String {
        LOCAL_CONFIG
            .read()
            .unwrap()
            .neodesk_connection_mode_error
            .clone()
    }

    pub fn set_connection_mode_policy(
        mode: &str,
        revision: u64,
        command_id: &str,
        status: &str,
        error: &str,
    ) {
        let mut config = LOCAL_CONFIG.write().unwrap();
        config.neodesk_connection_mode = mode.to_owned();
        config.neodesk_connection_mode_revision = revision;
        config.neodesk_connection_mode_command_id = command_id.to_owned();
        config.neodesk_connection_mode_status = status.to_owned();
        config.neodesk_connection_mode_error = error.to_owned();
        config.store();
    }
}

#[derive(Debug, Default, Serialize, Deserialize, Clone)]
pub struct DiscoveryPeer {
    #[serde(default, deserialize_with = "deserialize_string")]
    pub id: String,
    #[serde(default, deserialize_with = "deserialize_string")]
    pub username: String,
    #[serde(default, deserialize_with = "deserialize_string")]
    pub hostname: String,
    #[serde(default, deserialize_with = "deserialize_string")]
    pub platform: String,
    #[serde(default, deserialize_with = "deserialize_bool")]
    pub online: bool,
    #[serde(default, deserialize_with = "deserialize_hashmap_string_string")]
    pub ip_mac: HashMap<String, String>,
}

impl DiscoveryPeer {
    pub fn is_same_peer(&self, other: &DiscoveryPeer) -> bool {
        self.id == other.id && self.username == other.username
    }
}

#[derive(Debug, Default, Serialize, Deserialize, Clone)]
pub struct LanPeers {
    #[serde(default, deserialize_with = "deserialize_vec_discoverypeer")]
    pub peers: Vec<DiscoveryPeer>,
}

impl LanPeers {
    pub fn load() -> LanPeers {
        let _lock = CONFIG.read().unwrap();
        match confy::load_path(Config::file_("_lan_peers")) {
            Ok(peers) => peers,
            Err(err) => {
                log::error!("Failed to load lan peers: {}", err);
                Default::default()
            }
        }
    }

    pub fn store(peers: &[DiscoveryPeer]) {
        let f = LanPeers {
            peers: peers.to_owned(),
        };
        if let Err(err) = store_path(Config::file_("_lan_peers"), f) {
            log::error!("Failed to store lan peers: {}", err);
        }
    }

    pub fn modify_time() -> crate::ResultType<u64> {
        let p = Config::file_("_lan_peers");
        Ok(fs::metadata(p)?
            .modified()?
            .duration_since(SystemTime::UNIX_EPOCH)?
            .as_millis() as _)
    }
}

#[derive(Debug, Default, Serialize, Deserialize, Clone)]
pub struct UserDefaultConfig {
    #[serde(default, deserialize_with = "deserialize_hashmap_string_string")]
    options: HashMap<String, String>,
}

impl UserDefaultConfig {
    fn read(key: &str) -> String {
        let mut cfg = USER_DEFAULT_CONFIG.write().unwrap();
        // we do so, because default config may changed in another process, but we don't sync it
        // but no need to read every time, give a small interval to avoid too many redundant read waste
        if cfg.1.elapsed() > Duration::from_secs(1) {
            *cfg = (Self::load(), Instant::now());
        }
        cfg.0.get(key)
    }

    pub fn load() -> UserDefaultConfig {
        Config::load_::<UserDefaultConfig>("_default")
    }

    #[inline]
    fn store(&self) {
        Config::store_(self, "_default");
    }

    pub fn get(&self, key: &str) -> String {
        match key {
            #[cfg(any(target_os = "android", target_os = "ios"))]
            keys::OPTION_VIEW_STYLE => self.get_string(key, "adaptive", vec!["original"]),
            #[cfg(not(any(target_os = "android", target_os = "ios")))]
            keys::OPTION_VIEW_STYLE => self.get_string(key, "original", vec!["adaptive"]),
            keys::OPTION_SCROLL_STYLE => {
                self.get_string(key, "scrollauto", vec!["scrolledge", "scrollbar"])
            }
            keys::OPTION_IMAGE_QUALITY => {
                self.get_string(key, "balanced", vec!["best", "low", "custom"])
            }
            keys::OPTION_CODEC_PREFERENCE => {
                self.get_string(key, "auto", vec!["vp8", "vp9", "av1", "h264", "h265"])
            }
            keys::OPTION_CUSTOM_IMAGE_QUALITY => self.get_num_string(key, 50.0, 10.0, 0xFFF as f64),
            keys::OPTION_CUSTOM_FPS => self.get_num_string(key, 30.0, 5.0, 120.0),
            keys::OPTION_FPS_MODE => self.get_string(key, "30", vec!["60", "adaptive"]),
            keys::OPTION_ENABLE_FILE_COPY_PASTE => self.get_string(key, "Y", vec!["", "N"]),
            keys::OPTION_EDGE_SCROLL_EDGE_THICKNESS => self.get_num_string(key, 100, 20, 150),
            keys::OPTION_TRACKPAD_SPEED => self.get_num_string(key, 100, 10, 1000),
            _ => self
                .get_after(key)
                .map(|v| v.to_string())
                .unwrap_or_default(),
        }
    }

    pub fn set(&mut self, key: String, value: String) {
        if !is_option_can_save(
            &OVERWRITE_DISPLAY_SETTINGS,
            &key,
            &DEFAULT_DISPLAY_SETTINGS,
            &value,
        ) {
            if self.options.remove(&key).is_some() {
                self.store();
            }
            return;
        }
        if value.is_empty() {
            self.options.remove(&key);
        } else {
            self.options.insert(key, value);
        }
        self.store();
    }

    #[inline]
    fn get_string(&self, key: &str, default: &str, others: Vec<&str>) -> String {
        match self.get_after(key) {
            Some(option) => {
                if others.contains(&option.as_str()) {
                    option.to_owned()
                } else {
                    default.to_owned()
                }
            }
            None => default.to_owned(),
        }
    }

    #[inline]
    fn get_num_string<T>(&self, key: &str, default: T, min: T, max: T) -> String
    where
        T: ToString + std::str::FromStr + std::cmp::PartialOrd + std::marker::Copy,
    {
        match self.get_after(key) {
            Some(option) => {
                let v: T = option.parse().unwrap_or(default);
                if v >= min && v <= max {
                    v.to_string()
                } else {
                    default.to_string()
                }
            }
            None => default.to_string(),
        }
    }

    fn get_after(&self, k: &str) -> Option<String> {
        get_or(
            &OVERWRITE_DISPLAY_SETTINGS,
            &self.options,
            &DEFAULT_DISPLAY_SETTINGS,
            k,
        )
    }
}

#[derive(Debug, Default, Serialize, Deserialize, Clone)]
pub struct AbPeer {
    #[serde(
        default,
        deserialize_with = "deserialize_string",
        skip_serializing_if = "String::is_empty"
    )]
    pub id: String,
    #[serde(
        default,
        deserialize_with = "deserialize_string",
        skip_serializing_if = "String::is_empty"
    )]
    pub hash: String,
    #[serde(
        default,
        deserialize_with = "deserialize_string",
        skip_serializing_if = "String::is_empty"
    )]
    pub username: String,
    #[serde(
        default,
        deserialize_with = "deserialize_string",
        skip_serializing_if = "String::is_empty"
    )]
    pub hostname: String,
    #[serde(
        default,
        deserialize_with = "deserialize_string",
        skip_serializing_if = "String::is_empty"
    )]
    pub platform: String,
    #[serde(
        default,
        deserialize_with = "deserialize_string",
        skip_serializing_if = "String::is_empty"
    )]
    pub alias: String,
    #[serde(default, deserialize_with = "deserialize_vec_string")]
    pub tags: Vec<String>,
}

#[derive(Debug, Default, Serialize, Deserialize, Clone)]
pub struct AbEntry {
    #[serde(
        default,
        deserialize_with = "deserialize_string",
        skip_serializing_if = "String::is_empty"
    )]
    pub guid: String,
    #[serde(
        default,
        deserialize_with = "deserialize_string",
        skip_serializing_if = "String::is_empty"
    )]
    pub name: String,
    #[serde(default, deserialize_with = "deserialize_vec_abpeer")]
    pub peers: Vec<AbPeer>,
    #[serde(default, deserialize_with = "deserialize_vec_string")]
    pub tags: Vec<String>,
    #[serde(
        default,
        deserialize_with = "deserialize_string",
        skip_serializing_if = "String::is_empty"
    )]
    pub tag_colors: String,
}

impl AbEntry {
    pub fn personal(&self) -> bool {
        self.name == "My address book" || self.name == "Legacy address book"
    }
}

#[derive(Debug, Default, Serialize, Deserialize, Clone)]
pub struct Ab {
    #[serde(
        default,
        deserialize_with = "deserialize_string",
        skip_serializing_if = "String::is_empty"
    )]
    pub access_token: String,
    #[serde(default, deserialize_with = "deserialize_vec_abentry")]
    pub ab_entries: Vec<AbEntry>,
}

impl Ab {
    fn path() -> PathBuf {
        let filename = format!("{}_ab", APP_NAME.read().unwrap().clone());
        Config::path(filename)
    }

    pub fn store(json: String) {
        if let Ok(mut file) = std::fs::File::create(Self::path()) {
            let data = compress(json.as_bytes());
            let max_len = 64 * 1024 * 1024;
            if data.len() > max_len {
                // maxlen of function decompress
                log::error!("ab data too large, {} > {}", data.len(), max_len);
                return;
            }
            if let Ok(data) = symmetric_crypt(&data, true) {
                file.write_all(&data).ok();
            }
        };
    }

    pub fn load() -> Ab {
        if let Ok(mut file) = std::fs::File::open(Self::path()) {
            let mut data = vec![];
            if file.read_to_end(&mut data).is_ok() {
                if let Ok(data) = symmetric_crypt(&data, false) {
                    let data = decompress(&data);
                    if let Ok(ab) = serde_json::from_str::<Ab>(&String::from_utf8_lossy(&data)) {
                        return ab;
                    }
                }
            }
        };
        Self::remove();
        Ab::default()
    }

    pub fn remove() {
        std::fs::remove_file(Self::path()).ok();
    }
}

// use default value when field type is wrong
macro_rules! deserialize_default {
    ($func_name:ident, $return_type:ty) => {
        fn $func_name<'de, D>(deserializer: D) -> Result<$return_type, D::Error>
        where
            D: de::Deserializer<'de>,
        {
            Ok(de::Deserialize::deserialize(deserializer).unwrap_or_default())
        }
    };
}

#[derive(Debug, Default, Serialize, Deserialize, Clone)]
pub struct GroupPeer {
    #[serde(
        default,
        deserialize_with = "deserialize_string",
        skip_serializing_if = "String::is_empty"
    )]
    pub id: String,
    #[serde(
        default,
        deserialize_with = "deserialize_string",
        skip_serializing_if = "String::is_empty"
    )]
    pub username: String,
    #[serde(
        default,
        deserialize_with = "deserialize_string",
        skip_serializing_if = "String::is_empty"
    )]
    pub hostname: String,
    #[serde(
        default,
        deserialize_with = "deserialize_string",
        skip_serializing_if = "String::is_empty"
    )]
    pub platform: String,
    #[serde(
        default,
        deserialize_with = "deserialize_string",
        skip_serializing_if = "String::is_empty"
    )]
    pub login_name: String,
}

#[derive(Debug, Default, Serialize, Deserialize, Clone)]
pub struct GroupUser {
    #[serde(
        default,
        deserialize_with = "deserialize_string",
        skip_serializing_if = "String::is_empty"
    )]
    pub name: String,
    #[serde(
        default,
        deserialize_with = "deserialize_string",
        skip_serializing_if = "String::is_empty"
    )]
    pub display_name: String,
}

#[derive(Debug, Default, Serialize, Deserialize, Clone)]
pub struct DeviceGroup {
    #[serde(
        default,
        deserialize_with = "deserialize_string",
        skip_serializing_if = "String::is_empty"
    )]
    pub name: String,
}

#[derive(Debug, Default, Serialize, Deserialize, Clone)]
pub struct Group {
    #[serde(
        default,
        deserialize_with = "deserialize_string",
        skip_serializing_if = "String::is_empty"
    )]
    pub access_token: String,
    #[serde(default, deserialize_with = "deserialize_vec_groupuser")]
    pub users: Vec<GroupUser>,
    #[serde(default, deserialize_with = "deserialize_vec_grouppeer")]
    pub peers: Vec<GroupPeer>,
    #[serde(default, deserialize_with = "deserialize_vec_devicegroup")]
    pub device_groups: Vec<DeviceGroup>,
}

impl Group {
    fn path() -> PathBuf {
        let filename = format!("{}_group", APP_NAME.read().unwrap().clone());
        Config::path(filename)
    }

    pub fn store(json: String) {
        if let Ok(mut file) = std::fs::File::create(Self::path()) {
            let data = compress(json.as_bytes());
            let max_len = 64 * 1024 * 1024;
            if data.len() > max_len {
                // maxlen of function decompress
                return;
            }
            if let Ok(data) = symmetric_crypt(&data, true) {
                file.write_all(&data).ok();
            }
        };
    }

    pub fn load() -> Self {
        if let Ok(mut file) = std::fs::File::open(Self::path()) {
            let mut data = vec![];
            if file.read_to_end(&mut data).is_ok() {
                if let Ok(data) = symmetric_crypt(&data, false) {
                    let data = decompress(&data);
                    if let Ok(group) = serde_json::from_str::<Self>(&String::from_utf8_lossy(&data))
                    {
                        return group;
                    }
                }
            }
        };
        Self::remove();
        Self::default()
    }

    pub fn remove() {
        std::fs::remove_file(Self::path()).ok();
    }
}

#[derive(Debug, Default, Serialize, Deserialize, Clone)]
pub struct TrustedDevice {
    pub hwid: Bytes,
    pub time: i64,
    pub id: String,
    pub name: String,
    pub platform: String,
}

impl TrustedDevice {
    pub fn outdate(&self) -> bool {
        const DAYS_90: i64 = 90 * 24 * 60 * 60 * 1000;
        self.time + DAYS_90 < crate::get_time()
    }
}

deserialize_default!(deserialize_string, String);
deserialize_default!(deserialize_bool, bool);
deserialize_default!(deserialize_i32, i32);
deserialize_default!(deserialize_vec_u8, Vec<u8>);
deserialize_default!(deserialize_vec_string, Vec<String>);
deserialize_default!(deserialize_vec_i32_string_i32, Vec<(i32, String, i32)>);
deserialize_default!(deserialize_vec_discoverypeer, Vec<DiscoveryPeer>);
deserialize_default!(deserialize_vec_abpeer, Vec<AbPeer>);
deserialize_default!(deserialize_vec_abentry, Vec<AbEntry>);
deserialize_default!(deserialize_vec_groupuser, Vec<GroupUser>);
deserialize_default!(deserialize_vec_grouppeer, Vec<GroupPeer>);
deserialize_default!(deserialize_vec_devicegroup, Vec<DeviceGroup>);
deserialize_default!(deserialize_keypair, KeyPair);
deserialize_default!(deserialize_size, Size);
deserialize_default!(deserialize_hashmap_string_string, HashMap<String, String>);
deserialize_default!(deserialize_hashmap_string_bool,  HashMap<String, bool>);
deserialize_default!(deserialize_hashmap_resolutions, HashMap<String, Resolution>);

#[inline]
fn get_or(
    a: &RwLock<HashMap<String, String>>,
    b: &HashMap<String, String>,
    c: &RwLock<HashMap<String, String>>,
    k: &str,
) -> Option<String> {
    a.read()
        .unwrap()
        .get(k)
        .or(b.get(k))
        .or(c.read().unwrap().get(k))
        .cloned()
}

#[inline]
fn is_option_can_save(
    overwrite: &RwLock<HashMap<String, String>>,
    k: &str,
    defaults: &RwLock<HashMap<String, String>>,
    v: &str,
) -> bool {
    if overwrite.read().unwrap().contains_key(k)
        || defaults.read().unwrap().get(k).map_or(false, |x| x == v)
    {
        return false;
    }
    true
}

#[inline]
pub fn is_permanent_incoming_only() -> bool {
    HARD_SETTINGS
        .read()
        .unwrap()
        .get("conn-type")
        .map_or(false, |x| x == ("incoming"))
}

#[inline]
pub fn is_remote_connection_mode_controlled() -> bool {
    !is_permanent_incoming_only()
        && HARD_SETTINGS
            .read()
            .unwrap()
            .get("remote-connection-mode")
            .map_or(false, |x| x == "Y")
}

#[inline]
pub fn is_incoming_only() -> bool {
    is_permanent_incoming_only()
        || (is_remote_connection_mode_controlled()
            && LocalConfig::get_connection_mode() == "incoming-only")
}

#[inline]
pub fn connection_mode() -> &'static str {
    if is_incoming_only() {
        "incoming-only"
    } else {
        "normal"
    }
}

#[inline]
pub fn is_outgoing_only() -> bool {
    HARD_SETTINGS
        .read()
        .unwrap()
        .get("conn-type")
        .map_or(false, |x| x == ("outgoing"))
}

#[inline]
fn is_some_hard_opton(name: &str) -> bool {
    HARD_SETTINGS
        .read()
        .unwrap()
        .get(name)
        .map_or(false, |x| x == ("Y"))
}

#[inline]
pub fn is_disable_tcp_listen() -> bool {
    is_some_hard_opton("disable-tcp-listen")
}

#[inline]
pub fn is_disable_settings() -> bool {
    is_some_hard_opton("disable-settings")
}

#[inline]
pub fn is_disable_ab() -> bool {
    is_some_hard_opton("disable-ab")
}

#[inline]
pub fn is_disable_account() -> bool {
    is_some_hard_opton("disable-account")
}

#[inline]
pub fn is_disable_installation() -> bool {
    is_some_hard_opton("disable-installation")
}

// This function must be kept the same as the one in flutter and sciter code.
// flutter: flutter/lib/common.dart -> option2bool()
// sciter: Does not have the function, but it should be kept the same.
pub fn option2bool(option: &str, value: &str) -> bool {
    if option.starts_with("enable-") {
        value != "N"
    } else if option.starts_with("allow-")
        || option == "stop-service"
        || option == keys::OPTION_DIRECT_SERVER
        || option == "force-always-relay"
    {
        value == "Y"
    } else {
        value != "N"
    }
}

pub fn use_ws() -> bool {
    let option = keys::OPTION_ALLOW_WEBSOCKET;
    option2bool(option, &Config::get_option(option))
}

pub fn allow_insecure_tls_fallback() -> bool {
    let option = keys::OPTION_ALLOW_INSECURE_TLS_FALLBACK;
    option2bool(option, &Config::get_option(option))
}

pub mod keys {
    /// The 2FA secret (TOTP), see [`super::SECRET_OPTIONS`].
    pub const OPTION_2FA: &str = "2fa";
    pub const OPTION_VIEW_ONLY: &str = "view_only";
    pub const OPTION_SHOW_MONITORS_TOOLBAR: &str = "show_monitors_toolbar";
    pub const OPTION_COLLAPSE_TOOLBAR: &str = "collapse_toolbar";
    pub const OPTION_SHOW_REMOTE_CURSOR: &str = "show_remote_cursor";
    pub const OPTION_FOLLOW_REMOTE_CURSOR: &str = "follow_remote_cursor";
    pub const OPTION_FOLLOW_REMOTE_WINDOW: &str = "follow_remote_window";
    pub const OPTION_ZOOM_CURSOR: &str = "zoom-cursor";
    pub const OPTION_SHOW_QUALITY_MONITOR: &str = "show_quality_monitor";
    pub const OPTION_DISABLE_AUDIO: &str = "disable_audio";
    pub const OPTION_ENABLE_REMOTE_PRINTER: &str = "enable-remote-printer";
    pub const OPTION_ENABLE_FILE_COPY_PASTE: &str = "enable-file-copy-paste";
    pub const OPTION_DISABLE_CLIPBOARD: &str = "disable_clipboard";
    pub const OPTION_LOCK_AFTER_SESSION_END: &str = "lock_after_session_end";
    pub const OPTION_PRIVACY_MODE: &str = "privacy_mode";
    pub const OPTION_TOUCH_MODE: &str = "touch-mode";
    pub const OPTION_I444: &str = "i444";
    pub const OPTION_REVERSE_MOUSE_WHEEL: &str = "reverse_mouse_wheel";
    pub const OPTION_SWAP_LEFT_RIGHT_MOUSE: &str = "swap-left-right-mouse";
    pub const OPTION_DISPLAYS_AS_INDIVIDUAL_WINDOWS: &str = "displays_as_individual_windows";
    pub const OPTION_USE_ALL_MY_DISPLAYS_FOR_THE_REMOTE_SESSION: &str =
        "use_all_my_displays_for_the_remote_session";
    pub const OPTION_VIEW_STYLE: &str = "view_style";
    pub const OPTION_SCROLL_STYLE: &str = "scroll_style";
    pub const OPTION_EDGE_SCROLL_EDGE_THICKNESS: &str = "edge-scroll-edge-thickness";
    pub const OPTION_IMAGE_QUALITY: &str = "image_quality";
    pub const OPTION_CUSTOM_IMAGE_QUALITY: &str = "custom_image_quality";
    pub const OPTION_CUSTOM_FPS: &str = "custom-fps";
    pub const OPTION_FPS_MODE: &str = "fps-mode";
    pub const OPTION_CODEC_PREFERENCE: &str = "codec-preference";
    pub const OPTION_SYNC_INIT_CLIPBOARD: &str = "sync-init-clipboard";
    pub const OPTION_THEME: &str = "theme";
    pub const OPTION_LANGUAGE: &str = "lang";
    pub const OPTION_REMOTE_MENUBAR_DRAG_LEFT: &str = "remote-menubar-drag-left";
    pub const OPTION_REMOTE_MENUBAR_DRAG_RIGHT: &str = "remote-menubar-drag-right";
    pub const OPTION_HIDE_AB_TAGS_PANEL: &str = "hideAbTagsPanel";
    pub const OPTION_ENABLE_CONFIRM_CLOSING_TABS: &str = "enable-confirm-closing-tabs";
    pub const OPTION_ENABLE_OPEN_NEW_CONNECTIONS_IN_TABS: &str =
        "enable-open-new-connections-in-tabs";
    pub const OPTION_TEXTURE_RENDER: &str = "use-texture-render";
    // Internal health record written by the texture-render watchdog/probe;
    // "failed-*" flips the texture-render default to opt-in on this machine.
    pub const OPTION_TEXTURE_RENDER_HEALTH: &str = "texture-render-health";
    pub const OPTION_ALLOW_D3D_RENDER: &str = "allow-d3d-render";
    pub const OPTION_ENABLE_CHECK_UPDATE: &str = "enable-check-update";
    pub const OPTION_ALLOW_AUTO_UPDATE: &str = "allow-auto-update";
    pub const OPTION_SYNC_AB_WITH_RECENT_SESSIONS: &str = "sync-ab-with-recent-sessions";
    pub const OPTION_SYNC_AB_TAGS: &str = "sync-ab-tags";
    pub const OPTION_FILTER_AB_BY_INTERSECTION: &str = "filter-ab-by-intersection";
    pub const OPTION_ACCESS_MODE: &str = "access-mode";
    pub const OPTION_ENABLE_KEYBOARD: &str = "enable-keyboard";
    pub const OPTION_ENABLE_CLIPBOARD: &str = "enable-clipboard";
    pub const OPTION_ENABLE_FILE_TRANSFER: &str = "enable-file-transfer";
    pub const OPTION_ENABLE_CAMERA: &str = "enable-camera";
    pub const OPTION_ENABLE_TERMINAL: &str = "enable-terminal";
    pub const OPTION_TERMINAL_PERSISTENT: &str = "terminal-persistent";
    pub const OPTION_ENABLE_AUDIO: &str = "enable-audio";
    pub const OPTION_ENABLE_TUNNEL: &str = "enable-tunnel";
    pub const OPTION_ENABLE_REMOTE_RESTART: &str = "enable-remote-restart";
    pub const OPTION_ENABLE_RECORD_SESSION: &str = "enable-record-session";
    pub const OPTION_ENABLE_BLOCK_INPUT: &str = "enable-block-input";
    pub const OPTION_ENABLE_PRIVACY_MODE: &str = "enable-privacy-mode";
    pub const OPTION_ENABLE_PERM_CHANGE_IN_ACCEPT_WINDOW: &str =
        "enable-perm-change-in-accept-window";
    pub const OPTION_ALLOW_SCOPE_VIOLATION_CLOSE: &str = "allow-scope-violation-close";
    pub const OPTION_ALLOW_SCOPE_VIOLATION_ALARM: &str = "allow-scope-violation-alarm";
    pub const OPTION_ALLOW_REMOTE_CONFIG_MODIFICATION: &str = "allow-remote-config-modification";
    pub const OPTION_ALLOW_NUMERNIC_ONE_TIME_PASSWORD: &str = "allow-numeric-one-time-password";
    pub const OPTION_ENABLE_LAN_DISCOVERY: &str = "enable-lan-discovery";
    pub const OPTION_DIRECT_SERVER: &str = "direct-server";
    pub const OPTION_DIRECT_ACCESS_PORT: &str = "direct-access-port";
    pub const OPTION_WHITELIST: &str = "whitelist";
    pub const OPTION_ID_WHITELIST: &str = "id-whitelist";
    pub const OPTION_ALLOW_AUTO_DISCONNECT: &str = "allow-auto-disconnect";
    pub const OPTION_AUTO_DISCONNECT_TIMEOUT: &str = "auto-disconnect-timeout";
    pub const OPTION_ALLOW_ONLY_CONN_WINDOW_OPEN: &str = "allow-only-conn-window-open";
    pub const OPTION_ALLOW_AUTO_RECORD_INCOMING: &str = "allow-auto-record-incoming";
    pub const OPTION_ALLOW_AUTO_RECORD_OUTGOING: &str = "allow-auto-record-outgoing";
    pub const OPTION_HIDE_RECORDING_BUTTON: &str = "hide-recording-button";
    pub const OPTION_WINDOWS_SERVICE_VIDEO_SAVE_DIRECTORY: &str =
        "windows-service-video-save-directory";
    pub const OPTION_VIDEO_SAVE_DIRECTORY: &str = "video-save-directory";
    pub const OPTION_BRANDING_COMPANY_NAME: &str = "branding-company-name";
    pub const OPTION_BRANDING_PHONE: &str = "branding-phone";
    pub const OPTION_BRANDING_EMAIL: &str = "branding-email";
    pub const OPTION_BRANDING_WEBSITE: &str = "branding-website";
    pub const OPTION_BRANDING_LOGO: &str = "branding-logo";
    pub const OPTION_BRANDING_SOURCE: &str = "branding-source";
    pub const OPTION_BRANDING_REVISION: &str = "branding-revision";
    pub const OPTION_BRANDING_ACCENT_COLOR: &str = "branding-accent-color";
    pub const OPTION_BRANDING_BACKGROUND_COLOR: &str = "branding-background-color";
    pub const OPTION_BRANDING_LOGO_PATH: &str = "branding-logo-path";
    pub const OPTION_BRANDING_SYNCED_API: &str = "branding-synced-api";
    pub const OPTION_ENABLE_ABR: &str = "enable-abr";
    pub const OPTION_ALLOW_REMOVE_WALLPAPER: &str = "allow-remove-wallpaper";
    pub const OPTION_ALLOW_ALWAYS_SOFTWARE_RENDER: &str = "allow-always-software-render";
    pub const OPTION_ENABLE_HWCODEC: &str = "enable-hwcodec";
    pub const OPTION_APPROVE_MODE: &str = "approve-mode";
    pub const OPTION_VERIFICATION_METHOD: &str = "verification-method";
    pub const OPTION_TEMPORARY_PASSWORD_LENGTH: &str = "temporary-password-length";
    pub const OPTION_CUSTOM_RENDEZVOUS_SERVER: &str = "custom-rendezvous-server";
    pub const OPTION_API_SERVER: &str = "api-server";
    pub const OPTION_KEY: &str = "key";
    pub const OPTION_ALLOW_WEBSOCKET: &str = "allow-websocket";
    pub const OPTION_PRESET_ADDRESS_BOOK_NAME: &str = "preset-address-book-name";
    pub const OPTION_PRESET_ADDRESS_BOOK_TAG: &str = "preset-address-book-tag";
    pub const OPTION_PRESET_ADDRESS_BOOK_ALIAS: &str = "preset-address-book-alias";
    pub const OPTION_PRESET_ADDRESS_BOOK_PASSWORD: &str = "preset-address-book-password";
    pub const OPTION_PRESET_ADDRESS_BOOK_NOTE: &str = "preset-address-book-note";
    pub const OPTION_PRESET_DEVICE_USERNAME: &str = "preset-device-username";
    pub const OPTION_PRESET_DEVICE_NAME: &str = "preset-device-name";
    pub const OPTION_PRESET_NOTE: &str = "preset-note";
    pub const OPTION_ENABLE_DIRECTX_CAPTURE: &str = "enable-directx-capture";
    pub const OPTION_ENABLE_ANDROID_SOFTWARE_ENCODING_HALF_SCALE: &str =
        "enable-android-software-encoding-half-scale";
    pub const OPTION_ENABLE_TRUSTED_DEVICES: &str = "enable-trusted-devices";
    pub const OPTION_AV1_TEST: &str = "av1-test";
    pub const OPTION_TRACKPAD_SPEED: &str = "trackpad-speed";
    pub const OPTION_REGISTER_DEVICE: &str = "register-device";
    pub const OPTION_RELAY_SERVER: &str = "relay-server";
    pub const OPTION_ICE_SERVERS: &str = "ice-servers";
    /// Maximum number of files allowed during a single file transfer request.
    ///
    /// Key: `file-transfer-max-files`.
    /// Unit: number of files (not bytes).
    ///
    /// Behaviour:
    /// - If set to a positive integer N, at most N files are allowed.
    /// - If set to 0, a safe built-in default is used (see DEFAULT_MAX_VALIDATED_FILES).
    /// - If unset, negative, or non-integer, no explicit limit is enforced for backward compatibility.
    pub const OPTION_FILE_TRANSFER_MAX_FILES: &str = "file-transfer-max-files";
    pub const OPTION_DISABLE_UDP: &str = "disable-udp";
    pub const OPTION_ALLOW_INSECURE_TLS_FALLBACK: &str = "allow-insecure-tls-fallback";
    pub const OPTION_SHOW_VIRTUAL_MOUSE: &str = "show-virtual-mouse";
    // joystick is the virtual mouse.
    // So `OPTION_SHOW_VIRTUAL_MOUSE` should also be set if `OPTION_SHOW_VIRTUAL_JOYSTICK` is set.
    pub const OPTION_SHOW_VIRTUAL_JOYSTICK: &str = "show-virtual-joystick";
    pub const OPTION_ENABLE_FLUTTER_HTTP_ON_RUST: &str = "enable-flutter-http-on-rust";
    pub const OPTION_ALLOW_ASK_FOR_NOTE: &str = "allow-ask-for-note";

    // built-in options
    pub const OPTION_DISPLAY_NAME: &str = "display-name";
    pub const OPTION_AVATAR: &str = "avatar";
    pub const OPTION_PRESET_DEVICE_GROUP_NAME: &str = "preset-device-group-name";
    pub const OPTION_PRESET_USERNAME: &str = "preset-user-name";
    pub const OPTION_PRESET_STRATEGY_NAME: &str = "preset-strategy-name";
    pub const OPTION_REMOVE_PRESET_PASSWORD_WARNING: &str = "remove-preset-password-warning";
    pub const OPTION_HIDE_GENERAL_SETTINGS: &str = "hide-general-settings";
    pub const OPTION_HIDE_SECURITY_SETTINGS: &str = "hide-security-settings";
    pub const OPTION_HIDE_NETWORK_SETTINGS: &str = "hide-network-settings";
    pub const OPTION_HIDE_SERVER_SETTINGS: &str = "hide-server-settings";
    pub const OPTION_HIDE_PROXY_SETTINGS: &str = "hide-proxy-settings";
    pub const OPTION_HIDE_REMOTE_PRINTER_SETTINGS: &str = "hide-remote-printer-settings";
    pub const OPTION_HIDE_WEBSOCKET_SETTINGS: &str = "hide-websocket-settings";
    pub const OPTION_HIDE_STOP_SERVICE: &str = "hide-stop-service";
    pub const OPTION_ALLOW_COMMAND_LINE_SETTINGS_WHEN_SETTINGS_DISABLED: &str =
        "allow-command-line-settings-when-settings-disabled";

    // Connection punch-through options
    pub const OPTION_ENABLE_UDP_PUNCH: &str = "enable-udp-punch";
    pub const OPTION_ENABLE_IPV6_PUNCH: &str = "enable-ipv6-punch";
    pub const OPTION_HIDE_USERNAME_ON_CARD: &str = "hide-username-on-card";
    pub const OPTION_HIDE_HELP_CARDS: &str = "hide-help-cards";
    pub const OPTION_DEFAULT_CONNECT_PASSWORD: &str = "default-connect-password";
    pub const OPTION_HIDE_TRAY: &str = "hide-tray";
    pub const OPTION_ONE_WAY_CLIPBOARD_REDIRECTION: &str = "one-way-clipboard-redirection";
    pub const OPTION_ALLOW_LOGON_SCREEN_PASSWORD: &str = "allow-logon-screen-password";
    pub const OPTION_ALLOW_DEEP_LINK_PASSWORD: &str = "allow-deep-link-password";
    pub const OPTION_ALLOW_DEEP_LINK_SERVER_SETTINGS: &str = "allow-deep-link-server-settings";
    pub const OPTION_ONE_WAY_FILE_TRANSFER: &str = "one-way-file-transfer";
    pub const OPTION_ALLOW_HTTPS_21114: &str = "allow-https-21114";
    pub const OPTION_USE_RAW_TCP_FOR_API: &str = "use-raw-tcp-for-api";
    pub const OPTION_ALLOW_HOSTNAME_AS_ID: &str = "allow-hostname-as-id";
    pub const OPTION_HIDE_POWERED_BY_ME: &str = "hide-powered-by-me";
    pub const OPTION_MAIN_WINDOW_ALWAYS_ON_TOP: &str = "main-window-always-on-top";
    pub const OPTION_DISABLE_CHANGE_PERMANENT_PASSWORD: &str = "disable-change-permanent-password";
    pub const OPTION_DISABLE_CHANGE_ID: &str = "disable-change-id";
    pub const OPTION_DISABLE_UNLOCK_PIN: &str = "disable-unlock-pin";

    // flutter local options
    pub const OPTION_FLUTTER_REMOTE_MENUBAR_STATE: &str = "remoteMenubarState";
    pub const OPTION_FLUTTER_PEER_SORTING: &str = "peer-sorting";
    pub const OPTION_FLUTTER_PEER_TAB_INDEX: &str = "peer-tab-index";
    pub const OPTION_FLUTTER_PEER_TAB_ORDER: &str = "peer-tab-order";
    pub const OPTION_FLUTTER_PEER_TAB_VISIBLE: &str = "peer-tab-visible";
    pub const OPTION_FLUTTER_PEER_CARD_UI_TYLE: &str = "peer-card-ui-type";
    pub const OPTION_FLUTTER_CURRENT_AB_NAME: &str = "current-ab-name";
    pub const OPTION_ALLOW_REMOTE_CM_MODIFICATION: &str = "allow-remote-cm-modification";

    pub const OPTION_PRINTER_INCOMING_JOB_ACTION: &str = "printer-incomming-job-action";
    pub const OPTION_PRINTER_ALLOW_AUTO_PRINT: &str = "allow-printer-auto-print";
    pub const OPTION_PRINTER_SELECTED_NAME: &str = "printer-selected-name";

    // android floating window options
    pub const OPTION_DISABLE_FLOATING_WINDOW: &str = "disable-floating-window";
    pub const OPTION_FLOATING_WINDOW_SIZE: &str = "floating-window-size";
    pub const OPTION_FLOATING_WINDOW_UNTOUCHABLE: &str = "floating-window-untouchable";
    pub const OPTION_FLOATING_WINDOW_TRANSPARENCY: &str = "floating-window-transparency";
    pub const OPTION_FLOATING_WINDOW_SVG: &str = "floating-window-svg";

    // android keep screen on
    pub const OPTION_KEEP_SCREEN_ON: &str = "keep-screen-on";

    // Server-side: keep host system awake during incoming sessions (Security setting)
    pub const OPTION_KEEP_AWAKE_DURING_INCOMING_SESSIONS: &str =
        "keep-awake-during-incoming-sessions";

    // Client-side: keep client system awake during outgoing sessions (General setting)
    pub const OPTION_KEEP_AWAKE_DURING_OUTGOING_SESSIONS: &str =
        "keep-awake-during-outgoing-sessions";

    pub const OPTION_DISABLE_GROUP_PANEL: &str = "disable-group-panel";
    pub const OPTION_DISABLE_DISCOVERY_PANEL: &str = "disable-discovery-panel";
    pub const OPTION_PRE_ELEVATE_SERVICE: &str = "pre-elevate-service";

    // proxy settings
    // The following options are not real keys, they are just used for custom client advanced settings.
    // The real keys are in Config2::socks.
    pub const OPTION_PROXY_URL: &str = "proxy-url";
    pub const OPTION_PROXY_USERNAME: &str = "proxy-username";
    pub const OPTION_PROXY_PASSWORD: &str = "proxy-password";

    // DEFAULT_DISPLAY_SETTINGS, OVERWRITE_DISPLAY_SETTINGS
    pub const KEYS_DISPLAY_SETTINGS: &[&str] = &[
        OPTION_VIEW_ONLY,
        OPTION_SHOW_MONITORS_TOOLBAR,
        OPTION_COLLAPSE_TOOLBAR,
        OPTION_SHOW_REMOTE_CURSOR,
        OPTION_FOLLOW_REMOTE_CURSOR,
        OPTION_FOLLOW_REMOTE_WINDOW,
        OPTION_ZOOM_CURSOR,
        OPTION_SHOW_QUALITY_MONITOR,
        OPTION_DISABLE_AUDIO,
        OPTION_ENABLE_FILE_COPY_PASTE,
        OPTION_DISABLE_CLIPBOARD,
        OPTION_LOCK_AFTER_SESSION_END,
        OPTION_PRIVACY_MODE,
        OPTION_TOUCH_MODE,
        OPTION_I444,
        OPTION_REVERSE_MOUSE_WHEEL,
        OPTION_SWAP_LEFT_RIGHT_MOUSE,
        OPTION_DISPLAYS_AS_INDIVIDUAL_WINDOWS,
        OPTION_USE_ALL_MY_DISPLAYS_FOR_THE_REMOTE_SESSION,
        OPTION_VIEW_STYLE,
        OPTION_TERMINAL_PERSISTENT,
        OPTION_SCROLL_STYLE,
        OPTION_EDGE_SCROLL_EDGE_THICKNESS,
        OPTION_IMAGE_QUALITY,
        OPTION_CUSTOM_IMAGE_QUALITY,
        OPTION_CUSTOM_FPS,
        OPTION_FPS_MODE,
        OPTION_CODEC_PREFERENCE,
        OPTION_SYNC_INIT_CLIPBOARD,
        OPTION_TRACKPAD_SPEED,
    ];
    // DEFAULT_LOCAL_SETTINGS, OVERWRITE_LOCAL_SETTINGS
    pub const KEYS_LOCAL_SETTINGS: &[&str] = &[
        OPTION_THEME,
        OPTION_LANGUAGE,
        OPTION_ENABLE_CONFIRM_CLOSING_TABS,
        OPTION_ENABLE_OPEN_NEW_CONNECTIONS_IN_TABS,
        OPTION_TEXTURE_RENDER,
        OPTION_ALLOW_D3D_RENDER,
        OPTION_SYNC_AB_WITH_RECENT_SESSIONS,
        OPTION_SYNC_AB_TAGS,
        OPTION_FILTER_AB_BY_INTERSECTION,
        OPTION_REMOTE_MENUBAR_DRAG_LEFT,
        OPTION_REMOTE_MENUBAR_DRAG_RIGHT,
        OPTION_HIDE_AB_TAGS_PANEL,
        OPTION_FLUTTER_REMOTE_MENUBAR_STATE,
        OPTION_FLUTTER_PEER_SORTING,
        OPTION_FLUTTER_PEER_TAB_INDEX,
        OPTION_FLUTTER_PEER_TAB_ORDER,
        OPTION_FLUTTER_PEER_TAB_VISIBLE,
        OPTION_FLUTTER_PEER_CARD_UI_TYLE,
        OPTION_FLUTTER_CURRENT_AB_NAME,
        OPTION_DISABLE_FLOATING_WINDOW,
        OPTION_FLOATING_WINDOW_SIZE,
        OPTION_FLOATING_WINDOW_UNTOUCHABLE,
        OPTION_FLOATING_WINDOW_TRANSPARENCY,
        OPTION_FLOATING_WINDOW_SVG,
        OPTION_KEEP_SCREEN_ON,
        // Client-side: keep client system awake during outgoing sessions (General setting)
        OPTION_KEEP_AWAKE_DURING_OUTGOING_SESSIONS,
        OPTION_DISABLE_GROUP_PANEL,
        OPTION_DISABLE_DISCOVERY_PANEL,
        OPTION_PRE_ELEVATE_SERVICE,
        OPTION_ALLOW_REMOTE_CM_MODIFICATION,
        OPTION_ALLOW_AUTO_RECORD_OUTGOING,
        OPTION_HIDE_RECORDING_BUTTON,
        OPTION_VIDEO_SAVE_DIRECTORY,
        OPTION_BRANDING_COMPANY_NAME,
        OPTION_BRANDING_PHONE,
        OPTION_BRANDING_EMAIL,
        OPTION_BRANDING_WEBSITE,
        OPTION_BRANDING_LOGO,
        OPTION_BRANDING_SOURCE,
        OPTION_BRANDING_REVISION,
        OPTION_BRANDING_ACCENT_COLOR,
        OPTION_BRANDING_LOGO_PATH,
        OPTION_BRANDING_SYNCED_API,
        OPTION_ENABLE_UDP_PUNCH,
        OPTION_ENABLE_IPV6_PUNCH,
        OPTION_TOUCH_MODE,
        OPTION_SHOW_VIRTUAL_MOUSE,
        OPTION_SHOW_VIRTUAL_JOYSTICK,
        OPTION_ENABLE_FLUTTER_HTTP_ON_RUST,
        OPTION_ALLOW_ASK_FOR_NOTE,
    ];
    // DEFAULT_SETTINGS, OVERWRITE_SETTINGS
    pub const KEYS_SETTINGS: &[&str] = &[
        OPTION_ACCESS_MODE,
        OPTION_ENABLE_KEYBOARD,
        OPTION_ENABLE_CLIPBOARD,
        OPTION_ENABLE_FILE_TRANSFER,
        OPTION_ENABLE_CAMERA,
        OPTION_ENABLE_TERMINAL,
        OPTION_ENABLE_REMOTE_PRINTER,
        OPTION_ENABLE_AUDIO,
        OPTION_ENABLE_TUNNEL,
        OPTION_ENABLE_REMOTE_RESTART,
        OPTION_ENABLE_RECORD_SESSION,
        OPTION_ENABLE_BLOCK_INPUT,
        OPTION_ENABLE_PRIVACY_MODE,
        OPTION_ALLOW_SCOPE_VIOLATION_CLOSE,
        OPTION_ALLOW_SCOPE_VIOLATION_ALARM,
        OPTION_ALLOW_REMOTE_CONFIG_MODIFICATION,
        OPTION_ALLOW_NUMERNIC_ONE_TIME_PASSWORD,
        OPTION_ENABLE_LAN_DISCOVERY,
        OPTION_DIRECT_SERVER,
        OPTION_DIRECT_ACCESS_PORT,
        OPTION_WHITELIST,
        OPTION_ID_WHITELIST,
        OPTION_ALLOW_AUTO_DISCONNECT,
        OPTION_AUTO_DISCONNECT_TIMEOUT,
        OPTION_ALLOW_ONLY_CONN_WINDOW_OPEN,
        OPTION_ALLOW_AUTO_RECORD_INCOMING,
        OPTION_WINDOWS_SERVICE_VIDEO_SAVE_DIRECTORY,
        OPTION_ENABLE_ABR,
        OPTION_ALLOW_REMOVE_WALLPAPER,
        OPTION_ALLOW_ALWAYS_SOFTWARE_RENDER,
        OPTION_ENABLE_HWCODEC,
        OPTION_APPROVE_MODE,
        OPTION_VERIFICATION_METHOD,
        OPTION_TEMPORARY_PASSWORD_LENGTH,
        OPTION_PROXY_URL,
        OPTION_PROXY_USERNAME,
        OPTION_PROXY_PASSWORD,
        OPTION_CUSTOM_RENDEZVOUS_SERVER,
        OPTION_API_SERVER,
        OPTION_KEY,
        OPTION_ALLOW_WEBSOCKET,
        OPTION_PRESET_ADDRESS_BOOK_NAME,
        OPTION_PRESET_ADDRESS_BOOK_TAG,
        OPTION_PRESET_ADDRESS_BOOK_ALIAS,
        OPTION_PRESET_ADDRESS_BOOK_PASSWORD,
        OPTION_PRESET_ADDRESS_BOOK_NOTE,
        OPTION_PRESET_DEVICE_USERNAME,
        OPTION_PRESET_DEVICE_NAME,
        OPTION_PRESET_NOTE,
        OPTION_ENABLE_DIRECTX_CAPTURE,
        OPTION_ENABLE_ANDROID_SOFTWARE_ENCODING_HALF_SCALE,
        OPTION_ENABLE_TRUSTED_DEVICES,
        OPTION_RELAY_SERVER,
        OPTION_ICE_SERVERS,
        OPTION_DISABLE_UDP,
        OPTION_ALLOW_INSECURE_TLS_FALLBACK,
        OPTION_KEEP_AWAKE_DURING_INCOMING_SESSIONS,
        OPTION_ALLOW_AUTO_UPDATE,
    ];

    // BUILDIN_SETTINGS
    pub const KEYS_BUILDIN_SETTINGS: &[&str] = &[
        OPTION_DISPLAY_NAME,
        OPTION_AVATAR,
        OPTION_PRESET_DEVICE_GROUP_NAME,
        OPTION_PRESET_USERNAME,
        OPTION_PRESET_STRATEGY_NAME,
        OPTION_REMOVE_PRESET_PASSWORD_WARNING,
        OPTION_HIDE_GENERAL_SETTINGS,
        OPTION_HIDE_SECURITY_SETTINGS,
        OPTION_HIDE_NETWORK_SETTINGS,
        OPTION_HIDE_SERVER_SETTINGS,
        OPTION_HIDE_PROXY_SETTINGS,
        OPTION_HIDE_REMOTE_PRINTER_SETTINGS,
        OPTION_HIDE_WEBSOCKET_SETTINGS,
        OPTION_HIDE_STOP_SERVICE,
        OPTION_HIDE_USERNAME_ON_CARD,
        OPTION_HIDE_HELP_CARDS,
        OPTION_DEFAULT_CONNECT_PASSWORD,
        OPTION_HIDE_TRAY,
        OPTION_ONE_WAY_CLIPBOARD_REDIRECTION,
        OPTION_ALLOW_LOGON_SCREEN_PASSWORD,
        OPTION_ALLOW_DEEP_LINK_PASSWORD,
        OPTION_ALLOW_DEEP_LINK_SERVER_SETTINGS,
        OPTION_ONE_WAY_FILE_TRANSFER,
        OPTION_ALLOW_HTTPS_21114,
        OPTION_ALLOW_HOSTNAME_AS_ID,
        OPTION_REGISTER_DEVICE,
        OPTION_HIDE_POWERED_BY_ME,
        OPTION_MAIN_WINDOW_ALWAYS_ON_TOP,
        OPTION_FILE_TRANSFER_MAX_FILES,
        OPTION_DISABLE_CHANGE_PERMANENT_PASSWORD,
        OPTION_DISABLE_CHANGE_ID,
        OPTION_DISABLE_UNLOCK_PIN,
        OPTION_USE_RAW_TCP_FOR_API,
        OPTION_ENABLE_PERM_CHANGE_IN_ACCEPT_WINDOW,
        OPTION_ALLOW_COMMAND_LINE_SETTINGS_WHEN_SETTINGS_DISABLED,
    ];
}

pub fn common_load<
    T: serde::Serialize + serde::de::DeserializeOwned + Default + std::fmt::Debug,
>(
    suffix: &str,
) -> T {
    Config::load_::<T>(suffix)
}

pub fn common_store<T: serde::Serialize>(config: &T, suffix: &str) {
    Config::store_(config, suffix);
}

#[derive(Debug, Default, Serialize, Deserialize, Clone)]
pub struct Status {
    #[serde(default, deserialize_with = "deserialize_hashmap_string_string")]
    values: HashMap<String, String>,
}

impl Status {
    fn load() -> Status {
        Config::load_::<Status>("_status")
    }

    fn store(&self) {
        Config::store_(self, "_status");
    }

    pub fn get(k: &str) -> String {
        STATUS
            .read()
            .unwrap()
            .values
            .get(k)
            .cloned()
            .unwrap_or_default()
    }

    pub fn set(k: &str, v: String) {
        if Self::get(k) == v {
            return;
        }

        let mut st = STATUS.write().unwrap();
        st.values.insert(k.to_owned(), v);
        st.store();
    }
}

#[cfg(test)]
mod tests {
    use super::{permanent_password::PERMANENT_PASSWORD_ENC_VERSION, *};

    static CONFIG_STATE_TEST_LOCK: Mutex<()> = Mutex::new(());

    struct ConfigStateTestGuard {
        original_config: Config,
        original_hard_settings: HashMap<String, String>,
    }

    struct ConfigFileRestoreGuard {
        path: PathBuf,
        original_content: Option<Vec<u8>>,
    }

    impl ConfigStateTestGuard {
        fn new(config: Config, hard_settings: HashMap<String, String>) -> Self {
            let original_config = Config::get();
            let original_hard_settings = HARD_SETTINGS.read().unwrap().clone();
            *CONFIG.write().unwrap() = config;
            *HARD_SETTINGS.write().unwrap() = hard_settings;
            Self {
                original_config,
                original_hard_settings,
            }
        }
    }

    impl Drop for ConfigStateTestGuard {
        fn drop(&mut self) {
            *CONFIG.write().unwrap() = self.original_config.clone();
            *HARD_SETTINGS.write().unwrap() = self.original_hard_settings.clone();
        }
    }

    impl ConfigFileRestoreGuard {
        fn new(path: PathBuf) -> Self {
            let original_content = fs::read(&path).ok();
            Self {
                path,
                original_content,
            }
        }
    }

    impl Drop for ConfigFileRestoreGuard {
        fn drop(&mut self) {
            if let Some(content) = &self.original_content {
                if let Some(parent) = self.path.parent() {
                    fs::create_dir_all(parent).ok();
                }
                fs::write(&self.path, content).ok();
            } else {
                fs::remove_file(&self.path).ok();
            }
        }
    }

    fn with_config_and_hard_settings<R>(
        config: Config,
        hard_settings: HashMap<String, String>,
        test: impl FnOnce() -> R,
    ) -> R {
        let _guard = CONFIG_STATE_TEST_LOCK.lock().unwrap();
        let _state_guard = ConfigStateTestGuard::new(config, hard_settings);
        test()
    }

    #[test]
    fn remote_connection_mode_requires_explicit_capability() {
        with_config_and_hard_settings(Config::default(), HashMap::new(), || {
            assert!(!is_remote_connection_mode_controlled());
            assert!(!is_incoming_only());
        });

        let mut hard_settings =
            HashMap::from([("remote-connection-mode".to_owned(), "Y".to_owned())]);
        with_config_and_hard_settings(Config::default(), hard_settings.clone(), || {
            assert!(is_remote_connection_mode_controlled());
            assert!(!is_incoming_only());
        });

        hard_settings.insert("conn-type".to_owned(), "incoming".to_owned());
        with_config_and_hard_settings(Config::default(), hard_settings, || {
            assert!(!is_remote_connection_mode_controlled());
            assert!(is_permanent_incoming_only());
            assert!(is_incoming_only());
        });
    }

    #[test]
    fn test_links_point_at_the_neodeskapp_repositories() {
        assert_eq!(FORK_REPO_URL, "https://github.com/neodeskapp/neodesk-client");
        for (name, url) in HELPER_URL.iter() {
            assert!(
                url.starts_with("https://github.com/neodeskapp/neodesk"),
                "{name} points at {url}"
            );
        }
        // The upstream link is AGPL attribution and stays.
        assert_eq!(UPSTREAM_REPO_URL, "https://github.com/rustdesk/rustdesk");
    }

    #[cfg(not(any(target_os = "android", target_os = "ios")))]
    #[test]
    fn test_id_differs_from_stock_rustdesk_on_one_computer() {
        let macs: [[u8; 6]; 5] = [
            [0x52, 0x54, 0x00, 0x12, 0x34, 0x56],
            [0xbc, 0x24, 0x11, 0x41, 0x4a, 0x8e],
            [0x00, 0x00, 0x00, 0x00, 0x00, 0x00],
            [0xff, 0xff, 0xff, 0xff, 0xff, 0xff],
            [0x02, 0x42, 0xac, 0x11, 0x00, 0x02],
        ];
        for mac in &macs {
            let stock = stock_id_from_mac(mac);
            let ours = neodesk_id_from_mac(mac);
            assert_ne!(ours, stock, "{mac:02x?}");
            // Bound to the computer: the same address gives the same ID.
            assert_eq!(ours, neodesk_id_from_mac(mac));
            assert!(ours <= 0x1FFFFFFF);
            // An install that stored stock RustDesk's ID moves to its own;
            // any other ID stays.
            assert_eq!(
                moved_stock_id_for_mac(&stock.to_string(), mac),
                Some(ours.to_string())
            );
            assert_eq!(moved_stock_id_for_mac(&ours.to_string(), mac), None);
            assert_eq!(moved_stock_id_for_mac("123456789x", mac), None);
        }
        // Stock RustDesk's own derivation stays as it is.
        assert_eq!(stock_id_from_mac(&macs[0]), 0x0012_3456);
        assert_eq!(stock_id_from_mac(&macs[3]), 0x1FFF_FFFF);
    }

    #[test]
    fn test_app_identity_is_neodesk() {
        assert_eq!(APP_NAME.read().unwrap().as_str(), "NeoDesk Client");
        #[cfg(target_os = "macos")]
        assert_eq!(ORG.read().unwrap().as_str(), "sk.neode");
        assert_eq!(EXE_NAME, "neodesk");
        assert_eq!(URI_SCHEME, "neodesk");
        assert_eq!(NEODESK_CLIENT_PRODUCT, "neodesk-desktop");
        assert_eq!(crate::VER_TYPE_RUSTDESK_CLIENT, "neodesk-client");
        // The config directory is named after the app.
        let path = Config::path("").to_string_lossy().to_lowercase();
        assert!(path.contains("neodesk"), "{path}");
    }

    #[test]
    fn test_serialize() {
        let cfg: Config = Default::default();
        let res = toml::to_string_pretty(&cfg);
        assert!(res.is_ok());
        let cfg: PeerConfig = Default::default();
        let res = toml::to_string_pretty(&cfg);
        assert!(res.is_ok());
    }

    /// Issue #497: a populated `LocalConfig` must survive the real save path.
    ///
    /// The client persists `_local` through `confy`, which uses `toml` 0.5. That
    /// writer emits `HashMap` fields as tables and rejects a primitive value that
    /// follows one, so `Config::store_` logged
    /// "Failed to serialize configuration data into TOML" on every save and the
    /// config silently stopped persisting.
    ///
    /// `toml::to_string_pretty` cannot catch this: the crate's direct `toml`
    /// dependency is 0.7, which reorders fields. The test therefore goes through
    /// `confy` exactly like production does.
    #[test]
    fn test_local_config_persists_through_confy() {
        let dir = std::env::temp_dir().join(format!(
            "bd-localconfig-{}-{:?}",
            std::process::id(),
            std::thread::current().id()
        ));
        let _ = std::fs::create_dir_all(&dir);
        let path = dir.join("_local.toml");
        let _ = std::fs::remove_file(&path);

        let mut cfg = LocalConfig::default();
        cfg.remote_id = "123456789".to_owned();
        cfg.kb_layout_type = "map".to_owned();
        cfg.size = (100, 200, 800, 600);
        cfg.fav = vec!["111222333".to_owned(), "444555666".to_owned()];
        cfg.neodesk_connection_mode = "incoming-only".to_owned();
        cfg.neodesk_connection_mode_revision = 7;
        cfg.neodesk_connection_mode_command_id = "cmd-42".to_owned();
        cfg.neodesk_connection_mode_status = "applied".to_owned();
        cfg.neodesk_connection_mode_error = String::new();
        cfg.options.insert("enable-audio".to_owned(), "Y".to_owned());
        cfg.options
            .insert("custom-rendezvous-server".to_owned(), "panel.example".to_owned());
        cfg.ui_flutter
            .insert("theme".to_owned(), "dark".to_owned());

        // This is the call `Config::store_::<LocalConfig>` makes.
        confy::store_path(&path, cfg.clone())
            .expect("storing a populated LocalConfig must not fail (issue #497)");

        let text = std::fs::read_to_string(&path).expect("config file must exist");
        let first_table = text.find("\n[").unwrap_or(text.len());
        let mode_pos = text
            .find("neodesk_connection_mode")
            .expect("connection mode must be written");
        assert!(
            mode_pos < first_table,
            "scalar fields must precede map tables:\n{}",
            text
        );

        let parsed: LocalConfig = confy::load_path(&path).expect("stored config must load");
        assert_eq!(parsed.remote_id, cfg.remote_id);
        assert_eq!(parsed.fav, cfg.fav);
        assert_eq!(parsed.size, cfg.size);
        assert_eq!(
            parsed.neodesk_connection_mode,
            cfg.neodesk_connection_mode
        );
        assert_eq!(
            parsed.neodesk_connection_mode_revision,
            cfg.neodesk_connection_mode_revision
        );
        assert_eq!(
            parsed.neodesk_connection_mode_command_id,
            cfg.neodesk_connection_mode_command_id
        );
        assert_eq!(
            parsed.neodesk_connection_mode_status,
            cfg.neodesk_connection_mode_status
        );
        assert_eq!(parsed.options, cfg.options);
        assert_eq!(parsed.ui_flutter, cfg.ui_flutter);

        let _ = std::fs::remove_file(&path);
        let _ = std::fs::remove_dir(&dir);
    }

    /// Even an empty `LocalConfig` must produce valid TOML — this is the state
    /// a fresh install saves on first launch.
    #[test]
    fn test_local_config_default_round_trip() {
        let cfg = LocalConfig::default();
        let text = toml::to_string_pretty(&cfg).expect("default LocalConfig must serialise");
        let parsed: LocalConfig = toml::from_str(&text).expect("default LocalConfig must parse");
        assert_eq!(parsed.remote_id, "");
        assert_eq!(parsed.neodesk_connection_mode, "");
        assert!(parsed.options.is_empty());
        assert!(parsed.ui_flutter.is_empty());
    }

    #[test]
    fn test_hbbs_00_hashed_preset_password_storage_matches_plain_with_salt() {
        let salt = "salt123";
        let h1 = compute_permanent_password_h1("p@ssw0rd", salt);
        let storage = "00".to_owned() + &base64::encode(h1, base64::Variant::Original);
        let hard_settings = HashMap::from([
            ("password".to_owned(), storage),
            ("salt".to_owned(), salt.to_owned()),
        ]);

        with_config_and_hard_settings(Config::default(), hard_settings, || {
            assert!(Config::has_permanent_password());
            assert!(Config::has_usable_preset_password());
            assert!(Config::is_using_preset_password());
            assert_eq!(Config::get_effective_permanent_password_salt(), salt);
        });
    }

    #[test]
    fn test_legacy_plain_preset_password_with_00_hash_shape_without_salt_keeps_old_behavior() {
        let h1 = compute_permanent_password_h1("p@ssw0rd", "salt123");
        let storage = "00".to_owned() + &base64::encode(h1, base64::Variant::Original);
        let hard_settings = HashMap::from([("password".to_owned(), storage.clone())]);

        let mut config = Config::default();
        config.salt = "local1".to_owned();

        with_config_and_hard_settings(config, hard_settings, || {
            assert!(Config::has_permanent_password());
            assert!(Config::has_usable_preset_password());
            assert!(Config::is_using_preset_password());
            assert_eq!(Config::get_effective_permanent_password_salt(), "local1");
        });
    }

    #[test]
    fn test_local_hashed_permanent_password_without_salt_is_not_reported_as_set() {
        let h1 = compute_permanent_password_h1("p@ssw0rd", "salt123");
        let mut config = Config::default();
        config.password = encode_permanent_password_encrypted_storage_from_h1(&h1).unwrap();

        with_config_and_hard_settings(config, HashMap::new(), || {
            assert!(!Config::has_permanent_password());
            assert!(!Config::has_local_permanent_password());
            assert!(!Config::is_using_preset_password());
        });
    }

    #[test]
    fn test_invalid_local_hashed_password_does_not_generate_effective_salt() {
        let h1 = compute_permanent_password_h1("p@ssw0rd", "salt123");
        let mut config = Config::default();
        config.password = encode_permanent_password_encrypted_storage_from_h1(&h1).unwrap();

        with_config_and_hard_settings(config, HashMap::new(), || {
            assert_eq!(Config::get_effective_permanent_password_salt(), "");
            assert_eq!(
                Config::get_local_permanent_password_storage_and_salt().1,
                ""
            );
        });
    }

    #[test]
    fn test_legacy_plain_preset_password_uses_local_salt_for_challenge() {
        let mut config = Config::default();
        config.salt = "local1".to_owned();
        let hard_settings = HashMap::from([("password".to_owned(), "legacy-password".to_owned())]);

        with_config_and_hard_settings(config, hard_settings, || {
            assert_eq!(Config::get_effective_permanent_password_salt(), "local1");
            assert!(Config::has_permanent_password());
            assert!(Config::is_using_preset_password());
        });
    }

    #[test]
    fn test_malformed_preset_password_with_salt_is_not_usable() {
        for storage in ["01secret", "00not-a-valid-hash"] {
            let hard_settings = HashMap::from([
                ("password".to_owned(), storage.to_owned()),
                ("salt".to_owned(), "preset-salt".to_owned()),
            ]);

            with_config_and_hard_settings(Config::default(), hard_settings, || {
                assert_eq!(Config::get_effective_permanent_password_salt(), "");
                assert_eq!(
                    Config::get_local_permanent_password_storage_and_salt().1,
                    ""
                );
                assert!(!Config::has_permanent_password());
                assert!(!Config::is_using_preset_password());
            });
        }
    }

    #[test]
    fn test_validate_or_decrypt_keeps_plaintext_permanent_password_unchanged() {
        let mut cfg = Config::default();
        cfg.password = "p@ssw0rd".to_owned();
        cfg.salt = "".to_owned();
        Config::validate_or_decrypt_permanent_password_storage(&mut cfg).unwrap();
        assert_eq!(cfg.password, "p@ssw0rd");
        assert!(cfg.salt.is_empty());
    }

    #[test]
    fn test_validate_or_decrypt_decrypts_00_permanent_password_without_forcing_store() {
        let mut cfg = Config::default();
        let legacy_storage =
            encrypt_str_or_original("legacy-secret", PASSWORD_ENC_VERSION, ENCRYPT_MAX_LEN);
        cfg.password = legacy_storage;
        cfg.salt = "".to_owned();
        Config::validate_or_decrypt_permanent_password_storage(&mut cfg).unwrap();
        assert_eq!(cfg.password, "legacy-secret");
        assert!(cfg.salt.is_empty());
    }

    #[test]
    fn test_validate_or_decrypt_rejects_corrupted_00_permanent_password_storage() {
        let legacy_storage =
            encrypt_str_or_original("legacy-secret", PASSWORD_ENC_VERSION, ENCRYPT_MAX_LEN);
        let mut invalid_payload = base64::decode(
            &legacy_storage.as_bytes()[PASSWORD_ENC_VERSION.len()..],
            base64::Variant::Original,
        )
        .unwrap();
        *invalid_payload.last_mut().unwrap() ^= 1;

        let mut cfg = Config::default();
        cfg.password = PASSWORD_ENC_VERSION.to_owned()
            + &base64::encode(invalid_payload, base64::Variant::Original);
        cfg.salt = "salt123".to_owned();

        assert!(Config::validate_or_decrypt_permanent_password_storage(&mut cfg).is_err());
    }

    #[test]
    fn test_validate_or_decrypt_rejects_encrypted_hashed_permanent_password_without_salt() {
        let mut cfg = Config::default();
        let h1 = compute_permanent_password_h1("p@ssw0rd", "salt123");
        cfg.password = encode_permanent_password_encrypted_storage_from_h1(&h1).unwrap();
        let original_password = cfg.password.clone();

        assert!(Config::validate_or_decrypt_permanent_password_storage(&mut cfg).is_err());
        assert_eq!(cfg.password, original_password);
        assert!(cfg.salt.is_empty());
    }

    #[test]
    fn test_set_does_not_validate_or_decrypt_permanent_password_storage_in_memory() {
        let mut cfg = Config::default();
        let invalid_payload =
            crate::password_security::symmetric_crypt(b"not-a-hash", true).unwrap();
        let invalid_storage = PERMANENT_PASSWORD_ENC_VERSION.to_owned()
            + &base64::encode(invalid_payload, base64::Variant::Original);
        cfg.password = invalid_storage.clone();
        cfg.id = "123456789".to_owned();

        with_config_and_hard_settings(Config::default(), HashMap::new(), || {
            assert!(Config::set(cfg));

            let updated = Config::get();
            assert_eq!(updated.password, invalid_storage);
            assert!(updated.salt.is_empty());
            assert_eq!(updated.id, "123456789");
        });
    }

    #[test]
    fn test_store_keeps_existing_enc_id_when_id_is_unchanged() {
        let mut cfg = Config::default();
        cfg.id = "123456789".to_owned();
        cfg.enc_id = encrypt_str_or_original(&cfg.id, PASSWORD_ENC_VERSION, ENCRYPT_MAX_LEN);
        let original_enc_id = cfg.enc_id.clone();

        with_config_and_hard_settings(Config::default(), HashMap::new(), || {
            assert!(Config::set(cfg));

            assert_eq!(Config::load().enc_id, original_enc_id);
            assert_eq!(Config::get().id, "123456789");
        });
    }

    #[test]
    fn test_store_rewrites_enc_id_when_id_changes() {
        let original_id = "123456789";
        let updated_id = "987654321";
        let mut cfg = Config::default();
        cfg.id = updated_id.to_owned();
        let original_enc_id =
            encrypt_str_or_original(original_id, PASSWORD_ENC_VERSION, ENCRYPT_MAX_LEN);
        cfg.enc_id = original_enc_id.clone();

        with_config_and_hard_settings(Config::default(), HashMap::new(), || {
            assert!(Config::set(cfg));

            let stored = Config::load().enc_id;
            let (stored_id, encrypted, _) = decrypt_str_or_original(&stored, PASSWORD_ENC_VERSION);
            assert_ne!(stored, original_enc_id);
            assert!(encrypted);
            assert_eq!(stored_id, updated_id);
            assert_eq!(Config::get().id, updated_id);
        });
    }

    #[test]
    fn test_config2_store_keeps_existing_unlock_pin_when_pin_is_unchanged() {
        let _guard = CONFIG_STATE_TEST_LOCK.lock().unwrap();
        let _file_guard = ConfigFileRestoreGuard::new(Config::file_("2"));
        let pin = "123456";
        let original_unlock_pin =
            encrypt_str_or_original(pin, PASSWORD_ENC_VERSION, ENCRYPT_MAX_LEN);
        let mut cfg = Config2 {
            unlock_pin: original_unlock_pin.clone(),
            ..Default::default()
        };
        Config::store_(&cfg, "2");
        let (unlock_pin, decrypted, _) =
            decrypt_str_or_original(&cfg.unlock_pin, PASSWORD_ENC_VERSION);
        assert!(decrypted);
        cfg.unlock_pin = unlock_pin;
        cfg.nat_type = 1;

        cfg.store();

        let stored = Config::load_::<Config2>("2");
        assert_eq!(stored.unlock_pin, original_unlock_pin);
    }

    /// Takes the cached key pair for a test and puts it back afterwards.
    struct KeyPairCacheGuard(Option<KeyPair>);

    impl KeyPairCacheGuard {
        fn new() -> Self {
            Self(KEY_PAIR.lock().unwrap().take())
        }
    }

    impl Drop for KeyPairCacheGuard {
        fn drop(&mut self) {
            *KEY_PAIR.lock().unwrap() = self.0.take();
        }
    }

    // A join run as `--join` writes the device's key pair from its own
    // process while the service's server process runs with a config it
    // loaded before. When the server process then confirms the key and
    // stores its config, the key pair must stay in the file (L438).
    #[test]
    fn test_store_keeps_a_key_pair_another_process_wrote() {
        let _guard = CONFIG_STATE_TEST_LOCK.lock().unwrap();
        let _file_guard = ConfigFileRestoreGuard::new(Config::file());
        let _state_guard = ConfigStateTestGuard::new(Config::default(), HashMap::new());
        let mut joined = Config::default();
        joined.key_pair = (vec![7u8; 64], vec![9u8; 32]);
        Config::store_(&joined, "");

        Config::set_key_confirmed(true);

        let stored = Config::load_::<Config>("");
        assert_eq!(stored.key_pair, joined.key_pair);
        assert!(stored.key_confirmed);
    }

    // A key pair made now is not the key any server confirmed, so the
    // client registers it instead of only sending heartbeats (L438).
    #[test]
    fn test_a_new_key_pair_is_stored_unconfirmed() {
        use std::time::{Duration, Instant};
        let _guard = CONFIG_STATE_TEST_LOCK.lock().unwrap();
        let _file_guard = ConfigFileRestoreGuard::new(Config::file());
        let _key_guard = KeyPairCacheGuard::new();
        let mut confirmed = Config::default();
        confirmed.key_confirmed = true;
        confirmed
            .keys_confirmed
            .insert("10.0.0.1:21116".to_owned(), true);
        Config::store_(&confirmed, "");
        let _state_guard = ConfigStateTestGuard::new(confirmed, HashMap::new());

        let (_, pk) = Config::get_key_pair();

        let deadline = Instant::now() + Duration::from_secs(5);
        loop {
            let stored = Config::load_::<Config>("");
            if stored.key_pair.1 == pk {
                assert!(!stored.key_confirmed);
                assert!(stored.keys_confirmed.is_empty());
                break;
            }
            assert!(Instant::now() < deadline, "the new key pair was not stored");
            std::thread::sleep(Duration::from_millis(20));
        }
        assert!(!Config::get_key_confirmed());
    }

    /// Makes this test process the holder of the device's secrets again
    /// after a test (L442).
    struct SecretsHolderGuard;

    impl Drop for SecretsHolderGuard {
        fn drop(&mut self) {
            Config::set_holds_secrets(true);
        }
    }

    /// Puts CONFIG2 back as it was after a test.
    struct Config2StateGuard(Config2);

    impl Config2StateGuard {
        fn new(config: Config2) -> Self {
            Self(std::mem::replace(&mut *CONFIG2.write().unwrap(), config))
        }
    }

    impl Drop for Config2StateGuard {
        fn drop(&mut self) {
            *CONFIG2.write().unwrap() = std::mem::take(&mut self.0);
        }
    }

    /// A key pair made for the test; nothing prints it.
    fn test_key_pair() -> KeyPair {
        let (pk, sk) = sign::gen_keypair();
        (sk.0.to_vec(), pk.0.to_vec())
    }

    fn stored_key_pair() -> KeyPair {
        Config::load_::<Config>("").key_pair
    }

    /// A stored permanent password and its salt as the holder makes them.
    fn test_permanent_password(password: &str) -> (String, String) {
        let previous = Config::get();
        assert!(Config::set_permanent_password(password));
        let storage_and_salt = Config::get_local_permanent_password_storage_and_salt();
        *CONFIG.write().unwrap() = previous;
        storage_and_salt
    }

    /// Files as an older version left them in the person's profile: the key
    /// pair, a stored permanent password and a 2FA secret, next to settings
    /// that are no secret.
    fn write_profile_with_secrets(
        key_pair: &KeyPair,
        (storage, salt): &(String, String),
        two_fa: &str,
    ) {
        let mut config = Config::default();
        config.key_pair = key_pair.clone();
        config.password = storage.clone();
        config.salt = salt.clone();
        config.id = "123456789".to_owned();
        Config::store_(&config, "");
        let mut config2 = Config2::default();
        config2
            .options
            .insert(keys::OPTION_2FA.to_owned(), two_fa.to_owned());
        config2
            .options
            .insert("custom-rendezvous-server".to_owned(), "example.org".to_owned());
        Config::store_(&config2, "2");
    }

    // A process of the person's (the window of an installed client) does
    // not hold the device's secrets: it never keeps, loads or makes a secret
    // key, a stored permanent password or a 2FA secret, and the copies an
    // older version left in its files stay there as they are until the
    // service holds the secrets (L442).
    #[test]
    fn test_a_process_that_does_not_hold_the_secrets_never_keeps_them() {
        let _guard = CONFIG_STATE_TEST_LOCK.lock().unwrap();
        let _file_guard = ConfigFileRestoreGuard::new(Config::file());
        let _file2_guard = ConfigFileRestoreGuard::new(Config2::file());
        let _key_guard = KeyPairCacheGuard::new();
        let _holder_guard = SecretsHolderGuard;
        let _state_guard = ConfigStateTestGuard::new(Config::default(), HashMap::new());
        let _state2_guard = Config2StateGuard::new(Config2::default());
        let legacy = test_key_pair();
        let password = test_permanent_password("legacy-password");
        write_profile_with_secrets(&legacy, &password, "legacy-2fa");
        *CONFIG.write().unwrap() = Config::load();
        *CONFIG2.write().unwrap() = Config2::load();
        let raw = Config::load_::<Config>("");
        let raw2 = Config::load_::<Config2>("2").options;

        Config::set_holds_secrets(false);

        assert!(
            Config::get().key_pair.0.is_empty(),
            "the secret key stayed in memory"
        );
        assert!(
            Config::get_key_pair().0.is_empty(),
            "get_key_pair gave a secret key"
        );
        assert!(Config::get_existing_key_pair().map_or(true, |k| k.0.is_empty()));
        assert!(
            Config::get_local_permanent_password_storage_and_salt().0.is_empty(),
            "the stored permanent password stayed in memory"
        );
        assert!(
            Config::get_option(keys::OPTION_2FA).is_empty(),
            "the 2FA secret stayed in memory"
        );
        assert_eq!(Config::get_option("custom-rendezvous-server"), "example.org");

        let mut synced = Config::get();
        synced.key_pair = test_key_pair();
        synced.password = password.0.clone();
        // A change that is no secret, so the config is stored
        synced.key_confirmed = !synced.key_confirmed;
        assert!(Config::set(synced));
        let mut synced2 = Config2::get();
        synced2
            .options
            .insert(keys::OPTION_2FA.to_owned(), "synced-2fa".to_owned());
        Config2::set(synced2);
        Config::set_option(keys::OPTION_2FA.to_owned(), "set-2fa".to_owned());
        let mut options = Config::get_options();
        options.insert(keys::OPTION_2FA.to_owned(), "options-2fa".to_owned());
        Config::set_options(options);
        assert!(!Config::set_permanent_password("new-password"));
        assert!(
            Config::get().key_pair.0.is_empty(),
            "a secret key from another process was kept"
        );
        assert!(Config::get_local_permanent_password_storage_and_salt()
            .0
            .is_empty());
        assert!(Config::get_option(keys::OPTION_2FA).is_empty());

        // A process started as one that does not hold them loads none either
        *CONFIG.write().unwrap() = Config::load();
        *CONFIG2.write().unwrap() = Config2::load();
        assert!(Config::get().key_pair.0.is_empty());
        assert!(
            Config::get_local_permanent_password_storage_and_salt()
                .0
                .is_empty(),
            "loading kept the stored permanent password"
        );
        assert!(
            Config::get_option(keys::OPTION_2FA).is_empty(),
            "loading kept the 2FA secret"
        );

        // Neither storing nor a key made in the background changed the files
        std::thread::sleep(Duration::from_millis(200));
        let after = Config::load_::<Config>("");
        assert!(after.key_pair == legacy, "the key pair in the file changed");
        assert!(after.password == raw.password, "the stored password in the file changed");
        assert_eq!(after.salt, raw.salt);
        assert_eq!(
            Config::load_::<Config2>("2").options.get(keys::OPTION_2FA),
            raw2.get(keys::OPTION_2FA),
            "the 2FA secret in the file changed"
        );
    }

    #[test]
    fn test_the_secrets_leave_the_files_of_a_process_that_does_not_hold_them() {
        let _guard = CONFIG_STATE_TEST_LOCK.lock().unwrap();
        let _file_guard = ConfigFileRestoreGuard::new(Config::file());
        let _file2_guard = ConfigFileRestoreGuard::new(Config2::file());
        let _key_guard = KeyPairCacheGuard::new();
        let _holder_guard = SecretsHolderGuard;
        let _state_guard = ConfigStateTestGuard::new(Config::default(), HashMap::new());
        let _state2_guard = Config2StateGuard::new(Config2::default());
        let legacy = test_key_pair();
        let password = test_permanent_password("legacy-password");
        write_profile_with_secrets(&legacy, &password, "legacy-2fa");
        let before = Config::load_::<Config>("");

        // The holder never takes its own secrets out of its files
        assert!(!Config::remove_secrets_from_files());
        let found = Config::secrets_in_files().expect("the files hold secrets");
        assert!(found.key_pair == Some(legacy.clone()));

        Config::set_holds_secrets(false);
        let found = Config::secrets_in_files().expect("the files hold secrets");
        assert!(found.key_pair == Some(legacy));
        assert!(
            found.permanent_password == Some(password.clone()),
            "the stored permanent password was not found as the holder stores it"
        );
        assert_eq!(
            found.options.get(keys::OPTION_2FA).map(String::as_str),
            Some("legacy-2fa")
        );
        assert!(Config::remove_secrets_from_files());
        assert!(Config::secrets_in_files().is_none());
        let after = Config::load_::<Config>("");
        assert!(after.key_pair == KeyPair::default(), "the public key stayed");
        assert!(after.password.is_empty(), "the stored password stayed");
        assert_eq!(after.id, before.id);
        assert_eq!(after.enc_id, before.enc_id);
        assert_eq!(after.salt, password.1);
        let after2 = Config::load_::<Config2>("2");
        assert!(!after2.options.contains_key(keys::OPTION_2FA));
        assert_eq!(
            after2.options.get("custom-rendezvous-server").map(String::as_str),
            Some("example.org")
        );
        assert!(!Config::remove_secrets_from_files());
    }

    #[test]
    fn test_the_holder_takes_handed_over_secrets_only_when_it_has_none() {
        let _guard = CONFIG_STATE_TEST_LOCK.lock().unwrap();
        let _file_guard = ConfigFileRestoreGuard::new(Config::file());
        let _file2_guard = ConfigFileRestoreGuard::new(Config2::file());
        let _key_guard = KeyPairCacheGuard::new();
        let _holder_guard = SecretsHolderGuard;
        let mut confirmed = Config::default();
        confirmed.key_confirmed = true;
        Config::store_(&confirmed, "");
        Config::store_(&Config2::default(), "2");
        let _state_guard = ConfigStateTestGuard::new(confirmed, HashMap::new());
        let _state2_guard = Config2StateGuard::new(Config2::default());

        let mut mismatched = test_key_pair();
        mismatched.1 = test_key_pair().1;
        assert!(!Config::adopt_key_pair_if_none(mismatched));
        assert!(!Config::adopt_key_pair_if_none((vec![1u8; 64], vec![2u8; 32])));
        assert!(stored_key_pair().0.is_empty());

        let handed = test_key_pair();
        assert!(Config::adopt_key_pair_if_none(handed.clone()));
        assert!(Config::get_key_pair() == handed);
        assert!(stored_key_pair() == handed);
        // Registered once, so the server compares it with the key it holds
        assert!(!Config::get_key_confirmed());

        assert!(!Config::adopt_key_pair_if_none(test_key_pair()));
        assert!(Config::get_key_pair() == handed);
        assert!(stored_key_pair() == handed);

        let first = test_permanent_password("first-password");
        let second = test_permanent_password("second-password");
        assert!(!Config::adopt_permanent_password_if_none("not-a-storage", &first.1));
        assert!(!Config::has_local_permanent_password());
        assert!(Config::adopt_permanent_password_if_none(&first.0, &first.1));
        assert!(Config::get_local_permanent_password_storage_and_salt() == first);
        assert!(!Config::adopt_permanent_password_if_none(&second.0, &second.1));
        assert!(
            Config::get_local_permanent_password_storage_and_salt() == first,
            "a handed-over password replaced the holder's own"
        );

        assert!(!Config::adopt_secret_option_if_none("custom-rendezvous-server", "x"));
        assert!(Config::adopt_secret_option_if_none(keys::OPTION_2FA, "first-2fa"));
        assert!(!Config::adopt_secret_option_if_none(keys::OPTION_2FA, "second-2fa"));
        assert_eq!(Config::get_option(keys::OPTION_2FA), "first-2fa");

        // A process that does not hold the secrets takes none
        Config::store_(&Config::default(), "");
        Config::store_(&Config2::default(), "2");
        *KEY_PAIR.lock().unwrap() = None;
        *CONFIG.write().unwrap() = Config::default();
        *CONFIG2.write().unwrap() = Config2::default();
        Config::set_holds_secrets(false);
        assert!(!Config::adopt_key_pair_if_none(test_key_pair()));
        assert!(!Config::adopt_permanent_password_if_none(&first.0, &first.1));
        assert!(!Config::adopt_secret_option_if_none(keys::OPTION_2FA, "first-2fa"));
        assert!(Config::secrets_in_files().is_none());
    }

    #[test]
    fn test_a_config_for_or_from_another_process_does_not_move_the_secrets() {
        let _guard = CONFIG_STATE_TEST_LOCK.lock().unwrap();
        let _file_guard = ConfigFileRestoreGuard::new(Config::file());
        let _file2_guard = ConfigFileRestoreGuard::new(Config2::file());
        let _key_guard = KeyPairCacheGuard::new();
        let _holder_guard = SecretsHolderGuard;
        let _state_guard = ConfigStateTestGuard::new(Config::default(), HashMap::new());
        let _state2_guard = Config2StateGuard::new(Config2::default());
        let own = test_key_pair();
        let own_password = test_permanent_password("own-password");
        write_profile_with_secrets(&own, &own_password, "own-2fa");
        *CONFIG.write().unwrap() = Config::load();
        *CONFIG2.write().unwrap() = Config2::load();

        let for_other = Config::get_for_other_process();
        assert!(
            for_other.key_pair == KeyPair::default(),
            "the config for another process carries the key pair"
        );
        assert!(
            for_other.password.is_empty(),
            "the config for another process carries the stored password"
        );
        assert!(!Config2::get_for_other_process()
            .options
            .contains_key(keys::OPTION_2FA));
        assert!(!Config::get_options_for_other_process().contains_key(keys::OPTION_2FA));
        assert_eq!(
            Config::get_options_for_other_process()
                .get("custom-rendezvous-server")
                .map(String::as_str),
            Some("example.org")
        );

        let planted_password = test_permanent_password("planted-password");
        let mut planted = Config::get();
        planted.key_pair = test_key_pair();
        planted.password = planted_password.0.clone();
        planted.salt = planted_password.1.clone();
        planted.key_confirmed = true;
        Config::set_from_other_process(planted);
        assert!(stored_key_pair() == own, "a key pair sent over IPC replaced the own");
        assert!(
            Config::get_local_permanent_password_storage_and_salt() == own_password,
            "a password sent over IPC replaced the own"
        );
        assert!(Config::get_key_confirmed(), "the rest of the config was not taken");

        let mut planted2 = Config2::get_for_other_process();
        planted2
            .options
            .insert("custom-rendezvous-server".to_owned(), "other.example.org".to_owned());
        Config2::set_from_other_process(planted2.clone());
        assert_eq!(Config::get_option(keys::OPTION_2FA), "own-2fa");
        assert_eq!(
            Config::get_option("custom-rendezvous-server"),
            "other.example.org"
        );
        planted2
            .options
            .insert(keys::OPTION_2FA.to_owned(), "planted-2fa".to_owned());
        Config2::set_from_other_process(planted2);
        assert_eq!(Config::get_option(keys::OPTION_2FA), "own-2fa");
        Config::set_options_from_other_process(Config::get_options_for_other_process());
        assert_eq!(
            Config::get_option(keys::OPTION_2FA),
            "own-2fa",
            "options from another process removed the 2FA secret"
        );

        // The root service on Linux and macOS keeps its key, and without a
        // key yet takes the one the person's server process sends on a
        // first start
        let mut sent = Config::get();
        sent.key_pair = test_key_pair();
        Config::set_from_user_server(sent);
        assert!(stored_key_pair() == own);
        Config::store_(&Config::default(), "");
        *KEY_PAIR.lock().unwrap() = None;
        *CONFIG.write().unwrap() = Config::default();
        let first = test_key_pair();
        let mut sent = Config::default();
        sent.key_pair = first.clone();
        Config::set_from_user_server(sent);
        assert!(stored_key_pair() == first);
    }

    #[test]
    fn test_set_does_not_convert_plaintext_permanent_password_to_storage_format_in_memory() {
        let mut cfg = Config::default();
        cfg.password = "legacy-secret".to_owned();
        cfg.salt = "".to_owned();

        with_config_and_hard_settings(Config::default(), HashMap::new(), || {
            assert!(Config::set(cfg));

            let updated = Config::get();
            assert!(!updated.password.starts_with(PASSWORD_ENC_VERSION));
            assert_eq!(updated.password, "legacy-secret");
            assert!(updated.salt.is_empty());
        });
    }

    #[test]
    fn test_set_keeps_plaintext_permanent_password_with_current_prefix_in_memory() {
        let mut cfg = Config::default();
        cfg.password = "01legacy-secret".to_owned();
        cfg.salt = "".to_owned();

        with_config_and_hard_settings(Config::default(), HashMap::new(), || {
            assert!(Config::set(cfg));

            let updated = Config::get();
            assert_eq!(updated.password, "01legacy-secret");
            assert!(updated.salt.is_empty());
        });
    }

    #[test]
    fn test_validate_or_decrypt_keeps_plaintext_permanent_password_with_current_prefix_and_long_base64(
    ) {
        let mut cfg = Config::default();
        let plain = "01".to_owned() + &base64::encode([42u8; 24], base64::Variant::Original);
        cfg.password = plain.clone();
        cfg.salt = "".to_owned();

        Config::validate_or_decrypt_permanent_password_storage(&mut cfg).unwrap();
        assert_eq!(cfg.password, plain);
        assert!(cfg.salt.is_empty());
    }

    #[test]
    fn test_permanent_password_sync_treats_same_encrypted_hash_as_unchanged() {
        let mut cfg = Config::default();
        cfg.salt = "salt123".to_owned();
        let h1 = compute_permanent_password_h1("p@ssw0rd", &cfg.salt);
        let encrypted_hash_storage =
            encode_permanent_password_encrypted_storage_from_h1(&h1).unwrap();
        cfg.password = encrypted_hash_storage.clone();
        Config::validate_or_decrypt_permanent_password_storage(&mut cfg).unwrap();

        assert!(!Config::apply_permanent_password_storage_for_sync(
            &mut cfg,
            &encrypted_hash_storage,
            "salt123"
        )
        .unwrap());
    }

    #[test]
    fn test_permanent_password_sync_stores_incoming_encrypted_hash_when_local_empty() {
        let salt = "salt123";
        let h1 = compute_permanent_password_h1("p@ssw0rd", salt);
        let incoming = encode_permanent_password_encrypted_storage_from_h1(&h1).unwrap();
        let mut cfg = Config::default();

        assert!(
            Config::apply_permanent_password_storage_for_sync(&mut cfg, &incoming, salt).unwrap()
        );
        assert_eq!(cfg.password, incoming);
        assert_eq!(cfg.salt, salt);
    }

    #[test]
    fn test_permanent_password_sync_rejects_non_current_storage_payloads() {
        let invalid_payload = vec![42u8; sodiumoxide::crypto::secretbox::MACBYTES + 1];
        let invalid_storage = PERMANENT_PASSWORD_ENC_VERSION.to_owned()
            + &base64::encode(invalid_payload, base64::Variant::Original);
        let encrypted_legacy_plaintext =
            encrypt_str_or_original("legacy-secret", PASSWORD_ENC_VERSION, ENCRYPT_MAX_LEN);

        let encrypted = crate::password_security::symmetric_crypt(b"not-a-hash", true).unwrap();
        let encrypted_non_hash = PERMANENT_PASSWORD_ENC_VERSION.to_owned()
            + &base64::encode(encrypted, base64::Variant::Original);
        for storage in [
            "00secret",
            &encrypted_legacy_plaintext,
            &invalid_storage,
            "01invalid",
            &encrypted_non_hash,
        ] {
            let mut cfg = Config::default();
            assert!(Config::apply_permanent_password_storage_for_sync(
                &mut cfg, storage, "salt123"
            )
            .is_err());
            assert!(cfg.password.is_empty());
            assert!(cfg.salt.is_empty());
        }

        let mut cfg = Config::default();
        cfg.password = invalid_storage.clone();
        cfg.salt = "salt123".to_owned();
        assert!(Config::apply_permanent_password_storage_for_sync(
            &mut cfg,
            &invalid_storage,
            "salt123"
        )
        .is_err());
        assert_eq!(cfg.password, invalid_storage);
        assert_eq!(cfg.salt, "salt123");
    }

    #[test]
    fn test_permanent_password_sync_rejects_non_empty_storage_without_salt() {
        let mut cfg = Config::default();
        let h1 = compute_permanent_password_h1("p@ssw0rd", "salt123");
        let incoming = encode_permanent_password_encrypted_storage_from_h1(&h1).unwrap();

        assert!(
            Config::apply_permanent_password_storage_for_sync(&mut cfg, &incoming, "").is_err()
        );
        assert!(cfg.password.is_empty());
        assert!(cfg.salt.is_empty());
    }

    #[test]
    fn test_permanent_password_sync_empty_storage_clears_existing_password() {
        let salt = "salt123";
        let h1 = compute_permanent_password_h1("p@ssw0rd", salt);
        let mut cfg = Config::default();
        cfg.password = encode_permanent_password_encrypted_storage_from_h1(&h1).unwrap();
        cfg.salt = salt.to_owned();

        assert!(Config::apply_permanent_password_storage_for_sync(&mut cfg, "", "").unwrap());
        assert!(cfg.password.is_empty());
        assert_eq!(cfg.salt, salt);
    }

    #[test]
    fn test_permanent_password_sync_empty_storage_uses_incoming_salt() {
        let old_salt = "old-salt";
        let h1 = compute_permanent_password_h1("p@ssw0rd", old_salt);
        let mut cfg = Config::default();
        cfg.password = encode_permanent_password_encrypted_storage_from_h1(&h1).unwrap();
        cfg.salt = old_salt.to_owned();

        assert!(
            Config::apply_permanent_password_storage_for_sync(&mut cfg, "", "new-salt").unwrap()
        );
        assert!(cfg.password.is_empty());
        assert_eq!(cfg.salt, "new-salt");
    }

    #[test]
    fn test_overwrite_settings() {
        DEFAULT_SETTINGS
            .write()
            .unwrap()
            .insert("b".to_string(), "a".to_string());
        DEFAULT_SETTINGS
            .write()
            .unwrap()
            .insert("c".to_string(), "a".to_string());
        CONFIG2
            .write()
            .unwrap()
            .options
            .insert("a".to_string(), "b".to_string());
        CONFIG2
            .write()
            .unwrap()
            .options
            .insert("b".to_string(), "b".to_string());
        OVERWRITE_SETTINGS
            .write()
            .unwrap()
            .insert("b".to_string(), "c".to_string());
        OVERWRITE_SETTINGS
            .write()
            .unwrap()
            .insert("c".to_string(), "f".to_string());
        OVERWRITE_SETTINGS
            .write()
            .unwrap()
            .insert("d".to_string(), "c".to_string());
        let mut res: HashMap<String, String> = Default::default();
        res.insert("b".to_owned(), "c".to_string());
        res.insert("d".to_owned(), "c".to_string());
        res.insert("c".to_owned(), "a".to_string());
        Config::purify_options(&mut res);
        assert!(res.len() == 0);
        res.insert("b".to_owned(), "c".to_string());
        res.insert("d".to_owned(), "c".to_string());
        res.insert("c".to_owned(), "a".to_string());
        res.insert("f".to_owned(), "a".to_string());
        Config::purify_options(&mut res);
        assert!(res.len() == 1);
        res.insert("b".to_owned(), "c".to_string());
        res.insert("d".to_owned(), "c".to_string());
        res.insert("c".to_owned(), "a".to_string());
        res.insert("f".to_owned(), "a".to_string());
        res.insert("e".to_owned(), "d".to_string());
        Config::purify_options(&mut res);
        assert!(res.len() == 2);
        res.insert("b".to_owned(), "c".to_string());
        res.insert("d".to_owned(), "c".to_string());
        res.insert("c".to_owned(), "a".to_string());
        res.insert("f".to_owned(), "a".to_string());
        res.insert("c".to_owned(), "d".to_string());
        res.insert("d".to_owned(), "cc".to_string());
        Config::purify_options(&mut res);
        DEFAULT_SETTINGS
            .write()
            .unwrap()
            .insert("f".to_string(), "c".to_string());
        Config::purify_options(&mut res);
        assert!(res.len() == 2);
        DEFAULT_SETTINGS
            .write()
            .unwrap()
            .insert("f".to_string(), "a".to_string());
        Config::purify_options(&mut res);
        assert!(res.len() == 1);
        let res = Config::get_options();
        assert!(res["a"] == "b");
        assert!(res["c"] == "f");
        assert!(res["b"] == "c");
        assert!(res["d"] == "c");
        assert!(Config::get_option("a") == "b");
        assert!(Config::get_option("c") == "f");
        assert!(Config::get_option("b") == "c");
        assert!(Config::get_option("d") == "c");
        DEFAULT_SETTINGS.write().unwrap().clear();
        OVERWRITE_SETTINGS.write().unwrap().clear();
        CONFIG2.write().unwrap().options.clear();

        DEFAULT_LOCAL_SETTINGS
            .write()
            .unwrap()
            .insert("b".to_string(), "a".to_string());
        DEFAULT_LOCAL_SETTINGS
            .write()
            .unwrap()
            .insert("c".to_string(), "a".to_string());
        LOCAL_CONFIG
            .write()
            .unwrap()
            .options
            .insert("a".to_string(), "b".to_string());
        LOCAL_CONFIG
            .write()
            .unwrap()
            .options
            .insert("b".to_string(), "b".to_string());
        OVERWRITE_LOCAL_SETTINGS
            .write()
            .unwrap()
            .insert("b".to_string(), "c".to_string());
        OVERWRITE_LOCAL_SETTINGS
            .write()
            .unwrap()
            .insert("d".to_string(), "c".to_string());
        assert!(LocalConfig::get_option("a") == "b");
        assert!(LocalConfig::get_option("c") == "a");
        assert!(LocalConfig::get_option("b") == "c");
        assert!(LocalConfig::get_option("d") == "c");
        DEFAULT_LOCAL_SETTINGS.write().unwrap().clear();
        OVERWRITE_LOCAL_SETTINGS.write().unwrap().clear();
        LOCAL_CONFIG.write().unwrap().options.clear();

        DEFAULT_DISPLAY_SETTINGS
            .write()
            .unwrap()
            .insert("b".to_string(), "a".to_string());
        DEFAULT_DISPLAY_SETTINGS
            .write()
            .unwrap()
            .insert("c".to_string(), "a".to_string());
        USER_DEFAULT_CONFIG
            .write()
            .unwrap()
            .0
            .options
            .insert("a".to_string(), "b".to_string());
        USER_DEFAULT_CONFIG
            .write()
            .unwrap()
            .0
            .options
            .insert("b".to_string(), "b".to_string());
        OVERWRITE_DISPLAY_SETTINGS
            .write()
            .unwrap()
            .insert("b".to_string(), "c".to_string());
        OVERWRITE_DISPLAY_SETTINGS
            .write()
            .unwrap()
            .insert("d".to_string(), "c".to_string());
        assert!(UserDefaultConfig::read("a") == "b");
        assert!(UserDefaultConfig::read("c") == "a");
        assert!(UserDefaultConfig::read("b") == "c");
        assert!(UserDefaultConfig::read("d") == "c");
        DEFAULT_DISPLAY_SETTINGS.write().unwrap().clear();
        OVERWRITE_DISPLAY_SETTINGS.write().unwrap().clear();
        LOCAL_CONFIG.write().unwrap().options.clear();
    }

    #[test]
    fn test_config_deserialize() {
        let wrong_type_str = r#"
        id = true
        enc_id = []
        password = 1
        salt = "123456"
        key_pair = {}
        key_confirmed = "1"
        keys_confirmed = 1
        "#;
        let cfg = toml::from_str::<Config>(wrong_type_str);
        assert_eq!(
            cfg,
            Ok(Config {
                salt: "123456".to_string(),
                ..Default::default()
            })
        );

        let wrong_field_str = r#"
        hello = "world"
        key_confirmed = true
        "#;
        let cfg = toml::from_str::<Config>(wrong_field_str);
        assert_eq!(
            cfg,
            Ok(Config {
                key_confirmed: true,
                ..Default::default()
            })
        );
    }

    #[test]
    fn test_peer_config_deserialize() {
        let default_peer_config = toml::from_str::<PeerConfig>("").unwrap();
        // test custom_resolution
        {
            let wrong_type_str = r#"
            view_style = "adaptive"
            scroll_style = "scrollbar"
            custom_resolutions = true
            "#;
            let mut cfg_to_compare = default_peer_config.clone();
            cfg_to_compare.view_style = "adaptive".to_string();
            cfg_to_compare.scroll_style = "scrollbar".to_string();
            let cfg = toml::from_str::<PeerConfig>(wrong_type_str);
            assert_eq!(cfg, Ok(cfg_to_compare), "Failed to test wrong_type_str");

            let wrong_type_str = r#"
            view_style = "adaptive"
            scroll_style = "scrollbar"
            [custom_resolutions.0]
            w = "1920"
            h = 1080
            "#;
            let mut cfg_to_compare = default_peer_config.clone();
            cfg_to_compare.view_style = "adaptive".to_string();
            cfg_to_compare.scroll_style = "scrollbar".to_string();
            let cfg = toml::from_str::<PeerConfig>(wrong_type_str);
            assert_eq!(cfg, Ok(cfg_to_compare), "Failed to test wrong_type_str");

            let wrong_field_str = r#"
            [custom_resolutions.0]
            w = 1920
            h = 1080
            hello = "world"
            [ui_flutter]
            "#;
            let mut cfg_to_compare = default_peer_config.clone();
            cfg_to_compare.custom_resolutions =
                HashMap::from([("0".to_string(), Resolution { w: 1920, h: 1080 })]);
            let cfg = toml::from_str::<PeerConfig>(wrong_field_str);
            assert_eq!(cfg, Ok(cfg_to_compare), "Failed to test wrong_field_str");
        }
    }

    #[test]
    fn test_store_load() {
        let peerconfig_id = "123456789";
        let cfg: PeerConfig = Default::default();
        cfg.store(&peerconfig_id);
        assert_eq!(PeerConfig::load(&peerconfig_id), cfg);

        #[cfg(not(windows))]
        {
            use std::os::unix::fs::PermissionsExt;
            assert_eq!(
                // ignore file type information by masking with 0o777 (see https://stackoverflow.com/a/50045872)
                fs::metadata(PeerConfig::path(&peerconfig_id))
                    .expect("reading metadata failed")
                    .permissions()
                    .mode()
                    & 0o777,
                0o600
            );
        }
    }

    #[test]
    #[cfg(any(target_os = "linux", target_os = "macos"))]
    fn test_uinput_ipc_path_is_shared_across_uids() {
        const ROOT_UID: u32 = 0;
        const USER_UID: u32 = 1000;

        let path_root = Config::ipc_path_for_uid(ROOT_UID, "_uinput_keyboard");
        let path_user = Config::ipc_path_for_uid(USER_UID, "_uinput_keyboard");
        assert_eq!(path_root, path_user);

        let app_name = EXE_NAME;
        assert!(
            path_root.starts_with(&format!("/tmp/{app_name}-service/")),
            "unexpected uinput ipc path: {}",
            path_root
        );

        let non_service_root = Config::ipc_path_for_uid(ROOT_UID, "");
        let non_service_user = Config::ipc_path_for_uid(USER_UID, "");
        assert_ne!(non_service_root, non_service_user);
    }
}
