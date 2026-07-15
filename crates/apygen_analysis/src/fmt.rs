use std::fmt::{Display, Formatter};

pub fn fmt_iterator<T>(
    f: &mut Formatter<'_>,
    mut iterator: impl Iterator<Item = T>,
    separator: &str,
    fmt_element: impl Fn(&mut Formatter<'_>, T) -> std::fmt::Result,
) -> std::fmt::Result {
    let mut element_option = iterator.next();
    while let Some(element) = element_option {
        fmt_element(f, element)?;
        element_option = iterator.next();
        if element_option.is_some() {
            f.write_str(separator)?;
        }
    }
    Ok(())
}

pub fn fmt_display_iterator<T: Display>(
    f: &mut Formatter<'_>,
    iterator: impl Iterator<Item = T>,
    separator: &str,
) -> std::fmt::Result {
    fmt_iterator(f, iterator, separator, |f, element| {
        Display::fmt(&element, f)
    })
}

pub fn fmt_wrapped<T>(
    f: &mut Formatter<'_>,
    iterator: impl Iterator<Item = T>,
    separator: &str,
    prefix: &str,
    suffix: &str,
    fmt_element: impl Fn(&mut Formatter<'_>, T) -> std::fmt::Result,
) -> std::fmt::Result {
    f.write_str(prefix)?;
    fmt_iterator(f, iterator, separator, fmt_element)?;
    f.write_str(suffix)
}

pub fn fmt_display_wrapped<T: Display>(
    f: &mut Formatter<'_>,
    iterator: impl Iterator<Item = T>,
    separator: &str,
    prefix: &str,
    suffix: &str,
) -> std::fmt::Result {
    fmt_wrapped(f, iterator, separator, prefix, suffix, |f, element| {
        Display::fmt(&element, f)
    })
}

pub fn fmt_sequence<T>(
    f: &mut Formatter<'_>,
    iterator: impl Iterator<Item = T>,
    fmt_element: impl Fn(&mut Formatter<'_>, T) -> std::fmt::Result,
) -> std::fmt::Result {
    fmt_iterator(f, iterator, ", ", fmt_element)
}

pub fn fmt_display_sequence<T: Display>(
    f: &mut Formatter<'_>,
    iterator: impl Iterator<Item = T>,
) -> std::fmt::Result {
    fmt_sequence(f, iterator, |f, element| Display::fmt(&element, f))
}

pub fn fmt_set<T>(
    f: &mut Formatter<'_>,
    iterator: impl Iterator<Item = T>,
    fmt_element: impl Fn(&mut Formatter<'_>, T) -> std::fmt::Result,
) -> std::fmt::Result {
    fmt_wrapped(f, iterator, ", ", "{", "}", fmt_element)
}

pub fn fmt_display_set<T: Display>(
    f: &mut Formatter<'_>,
    iterator: impl Iterator<Item = T>,
) -> std::fmt::Result {
    fmt_set(f, iterator, |f, element| Display::fmt(&element, f))
}
