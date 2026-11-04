mod mute;

#[allow(unused)]
pub use mute::mute;

#[allow(unused)]
/// Tries to load an environment variable representing a value of T.
///
/// If the variable couldn't be obtained for whatever reason the default value
/// is returned instead. If the variable exists and can be converted to a String
/// then the function attempts conversion, potentially failing.
///
/// # Panics
///
/// If the [`FromStr`] conversion fails.
pub fn env_conf<T>(var: &str, default_value: T) -> T
where
    T: std::str::FromStr,
    <T as std::str::FromStr>::Err: std::fmt::Display,
{
    std::env::var(var)
        .ok()
        .map(|s| {
            T::from_str(&s).unwrap_or_else(|err| {
                panic!(
                    "conversion failed for type {}: {err}",
                    std::any::type_name::<T>()
                )
            })
        })
        .unwrap_or_else(|| default_value)
}
