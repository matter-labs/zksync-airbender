pub fn is_ci() -> bool {
    std::env::var_os("CI").is_some()
}

pub fn log_skip(path: &str) {
    eprintln!("skipping {path} in CI");
}

#[macro_export]
macro_rules! skip_if_ci {
    () => {
        if $crate::is_ci() {
            $crate::log_skip(module_path!());
            return;
        }
    };
    ($ret:expr) => {
        if $crate::is_ci() {
            $crate::log_skip(module_path!());
            return $ret;
        }
    };
}
