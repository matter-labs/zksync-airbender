#[cfg(not(feature = "checked_word_memory"))]
mod memcpy_bounds_tests;
#[cfg(not(feature = "checked_word_memory"))]
mod memcpy_tests;
#[cfg(not(feature = "checked_word_memory"))]
mod memmove_tests;
#[cfg(not(feature = "checked_word_memory"))]
mod memset_tests;

#[cfg(feature = "checked_word_memory")]
mod checked_word_tests;
