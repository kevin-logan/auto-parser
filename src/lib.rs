/// [`Parser`] is the main trait implemented by the types created by the ebnf! macro
///
/// It supports a few nice to have &str matching functions, including `take` which
/// can be used to parse larger data pieces at a time
pub trait Parser {
    fn match_len(buffer: &str) -> Option<usize>;

    fn take(buffer: &str) -> (Option<&str>, &str) {
        Self::match_len(buffer).map_or((None, buffer), |len| {
            let (matching, remainder) = buffer.split_at(len);
            (Some(matching), remainder)
        })
    }

    fn matches(buffer: &str) -> bool {
        Self::match_len(buffer).is_some_and(|v| v == buffer.len())
    }

    fn prefix_matches(buffer: &str) -> bool {
        Self::match_len(buffer).is_some()
    }
}

/// [`Marcher`] is used internally to march through a buffer and provides matching utilities
/// for some of the common EBNF operations
#[allow(dead_code)]
#[derive(Clone)]
pub struct Marcher<'a>(pub &'a str);

/// The [`MarcherLiteral`] is used by [`Marcher`] so it can accept both literal characters and
/// literal strings for its marching functions
#[allow(dead_code)]
pub enum MarcherLiteral<'a> {
    Character(char),
    String(&'a str),
}

/// implement [`MarcherLiteral`] for `char`
impl<'a> From<char> for MarcherLiteral<'a> {
    fn from(val: char) -> Self {
        Self::Character(val)
    }
}

/// implement [`MarcherLiteral`] for `&str`
impl<'a> From<&'a str> for MarcherLiteral<'a> {
    fn from(val: &'a str) -> Self {
        Self::String(val)
    }
}

#[allow(dead_code)]
impl<'a> Marcher<'a> {
    /// Matches any value that can be converted to a literal and increments the interal
    /// buffer beyond the match, returning the number of bytes matched or None if there
    /// was no match
    pub fn matches_literal(&mut self, val: impl Into<MarcherLiteral<'a>>) -> Option<usize> {
        match val.into() {
            MarcherLiteral::Character(c) => self.matches_exact(c),
            MarcherLiteral::String(s) => self.matches_str(s),
        }
    }

    /// Matches exactly one character (which may be multiple bytes). Increments the internal
    /// buffer and returns the number of bytes matched or None if there was no match
    pub fn matches_exact(&mut self, val: char) -> Option<usize> {
        match self.0.chars().next() {
            Some(c) if c == val => {
                let len = c.len_utf8();
                self.0 = &self.0[len..];
                Some(len)
            }
            _ => None,
        }
    }

    /// Matches any character inclusively between `min` and `max`. Increments the internal
    /// buffer and returns the number of bytes matched or None if there was no match
    pub fn matches_range(&mut self, min: char, max: char) -> Option<usize> {
        match self.0.chars().next() {
            Some(c) if (c >= min && c <= max) => {
                let len = c.len_utf8();
                self.0 = &self.0[len..];
                Some(len)
            }
            _ => None,
        }
    }

    /// Matches a string of characters and increments the internal buffer, returning the
    /// number of bytes matched or None if there was no match
    pub fn matches_str(&mut self, val: &str) -> Option<usize> {
        if self.0.starts_with(val) {
            let len = val.len();
            self.0 = &self.0[len..];
            Some(len)
        } else {
            None
        }
    }

    /// Matches against a given [`Parser`], incrementing the internal buffer by the number
    /// of bytes matched, if any, and returning that value or None if there was no match
    pub fn matches_parser<T: Parser>(&mut self) -> Option<usize> {
        match T::match_len(self.0) {
            Some(len) => {
                self.0 = &self.0[len..];
                Some(len)
            }
            None => None,
        }
    }
}

/// [`ebnf`] is an Extended Backus-Naur Form parser generation macro, and will generate
/// a [`Parser`] implementing type for any rule specified in EBNF syntax.
///
/// When generating a type, the type will be created from the rule name, but made camel
/// case with Parser appended. E.G. `range` will become `RangeParser`.
///
/// See the package tests for examples of most features and grammar.
///
/// There are a few caveats:
/// - Comment syntax has partial support. In EBNF a comment should be specified
///     (* like this *). That syntax does work, but comments do not allow unbalanced
///     parenthesis nor is the closing * in *) actually necessary. E.G:
///     ```
///     use auto_parser::ebnf;
///     ebnf!(range =
///             (['0' ... '9'], '-', '0' ... '9') (* valid comment despite closing )
///             | (* valid traditional comment style *)
///             ('0' ... '9', '-', ['0' ... '9']) (* invalid comment because ( are unbalanced *)
///                                                               ... so it actually ends here )
///     );
///     ```
/// - There is no rules separator (generally ;), so instead of something like:
///     ```compile_fail
///     use auto_parser::ebnf;
///     ebnf!(
///         digit = '0' ... '9';
///         letter = 'a' ... 'z' | 'A' .. 'Z';
///         alphanumeric = digit | letter;
///     );
///     ```
///     you must instead simply use the macro once per rule:
///     ```
///     use auto_parser::ebnf;
///     ebnf!(digit = '0' ... '9');
///     ebnf!(letter = 'a' ... 'z' | 'A' ... 'Z');
///     ebnf!(alphanumeric = digit | letter);
///     ```
///     Note that separate rules can still reference one another despite coming from
///     different macro invocations (as long as they are not circularly dependent)
#[macro_export]
macro_rules! ebnf {
    ($name:ident = $($rule:tt)*) => {
        paste::paste! {
            pub struct [<$name:camel Parser>] {

            }

            impl $crate::Parser for [<$name:camel Parser>] {
                fn match_len(buffer: &str) -> Option<usize> {
                    let mut _marcher = $crate::Marcher(buffer);
                    ebnf!(@parse _marcher, $($rule)*)
                }
            }
        }
    };

    (@parse $marcher:expr, {$($collected:tt)*} <= {}) => {
        // terminal case
        ebnf!(@count $marcher, $($collected)*)
    };
    (@parse $marcher:expr, {$($collected:tt)*} <= {| $($input:tt)*}) => {
        // or
        {
            let original_marcher = $marcher.clone();
            ebnf!(@count $marcher, $($collected)*).or_else(|| {
                // previous branch failed, reset marcher
                $marcher = original_marcher;
                ebnf!(@parse $marcher, $($input)*)
            })
        }
    };
    (@parse $marcher:expr, {$($collected:tt)*} <= {, $($input:tt)*}) => {
        // concat
        if let Some(len) = ebnf!(@count $marcher, $($collected)*) {
            if let Some(remainder_len) = ebnf!(@parse $marcher, $($input)*) {
                Some(len + remainder_len)
            } else {
                None
            }
        } else {
            None
        }
    };
    // supporting comments completely correctly may be very difficult
    // for now, comments must have balanced parenthesis, and the final parenthesis
    // will close the comment even without the *, so
    // (* comment ) is a valid comment when it should not be
    // and (* comment ( *) is not a valid comment when it should be
    (@parse $marcher:expr, {$($collected:tt)*} <= {(* $($comment:tt)* ) $($input:tt)*}) => {
        // skip comment and continue collecting remainder
        ebnf!(@parse $marcher, {$($collected)*} <= {$($input)*})
    };
    (@parse $marcher:expr, {$($collected:tt)*} <= {$first:tt $($input:tt)*}) => {
        // continue collecting
        ebnf!(@parse $marcher, {$($collected)* $first} <= {$($input)*})
    };
    (@parse $marcher:expr, $($input:tt)*) => {
        // entry
        ebnf!(@parse $marcher, {} <= {$($input)*})
    };

    (@count $marcher:expr, $val1:literal ... $val2:literal) => {
        $marcher.matches_range($val1, $val2)
    };
    (@count $marcher:expr, $val_in:literal) => {
        $marcher.matches_literal($val_in)
    };
    (@count $marcher:expr, $parser:ident) => {
        paste::paste! {
            $marcher.matches_parser::<[<$parser:camel Parser>]>()
        }
    };
    (@count $marcher:expr, {$($repetition:tt)*}) => {
        // a repetition always matches, but add up the total while it does
        {
            let mut count = 0;
            while let Some(v) = ebnf!(@parse $marcher, $($repetition)*) {
                count += v;
            }
            Some(count)
        }
    };
    (@count $marcher:expr, [$($repetition:tt)*]) => {
        // an optional always matches, just with 0 when the internal expression isn't a match
        Some(ebnf!(@parse $marcher, $($repetition)*).unwrap_or(0))
    };
    (@count $marcher:expr, ($($grouping:tt)*)) => {
        // grouping just needs to be reparsed
        ebnf!(@parse $marcher, $($grouping)*)
    };
    (@count $marcher:expr, $($unmatched:tt)*) => {
        // count didn't match any simple case, try to parse advance cases
        ebnf!(@count_parse_advanced $marcher, $($unmatched)*)
    };

    (@count_parse_advanced $marcher:expr, {$($collected:tt)*} <= {- $($exclusion:tt)*}) => {
        // exclusion, matched collected but not exclusion
        {
            let mut original_marcher = $marcher.clone();
            ebnf!(@parse $marcher, $($collected)*).and_then(|v| match ebnf!(@parse original_marcher, $($exclusion)*) {
                None => Some(v), // exclusion doesn't match, return match
                _ => None // exclusion matches, return no match
            })
        }
    };
    (@count_parse_advanced $marcher:expr, {$($collected:tt)*} <= {$first:tt $($input:tt)*}) => {
        // continue collecting
        ebnf!(@count_parse_advanced $marcher, {$($collected)* $first} <= {$($input)*})
    };
    (@count_parse_advanced $marcher:expr, $($advanced:tt)*) => {
        // entry point
        ebnf!(@count_parse_advanced $marcher, {} <= {$($advanced)*})
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    ebnf!(letter = 'A' ... 'Z' | 'a' ... 'z');
    ebnf!(digit = '0' ... '9');
    ebnf!(whitespace = { ' ' | '\n' | '\t' | '\r' });

    #[test]
    fn test_simple_sequence() {
        for i in 0..9 {
            assert!(DigitParser::matches(i.to_string().as_str()));
        }
    }

    #[test]
    fn test_simple_alternation() {
        for c in 'a'..'z' {
            assert!(LetterParser::matches(c.to_string().as_str()));
        }
        for c in 'A'..'Z' {
            assert!(LetterParser::matches(c.to_string().as_str()));
        }
    }

    #[test]
    fn test_use_named_rules() {
        ebnf!(ident = letter, { letter | digit | '_' });

        let buf = "Sweet_GamerTag_1337 has joined the game";

        assert!(IdentParser::prefix_matches(buf));
        assert!(!IdentParser::matches(buf));

        let (all_matches, buf) = IdentParser::take(buf);
        assert!(all_matches.is_some_and(|v| v == "Sweet_GamerTag_1337"));
        assert_eq!(buf, " has joined the game");
    }

    #[test]
    fn test_optional_and_comments() {
        ebnf!(
            ssn = digit,
            digit,
            digit,
            ['-'], (* - are optional *)
            digit,
            digit,
            ['-'], (* - are optional *)
            digit,
            digit,
            digit,
            digit
        );

        assert!(SsnParser::matches("123456789"));
        assert!(SsnParser::matches("123-45-6789"));
        assert!(!SsnParser::matches("123 45 6789"));
    }

    #[test]
    fn test_grouping() {
        ebnf!(cat = ('c', 'a', 't') | ('C', 'A', 'T'));

        assert!(CatParser::matches("cat"));
        assert!(CatParser::matches("CAT"));
        assert!(!CatParser::matches("cAT"));
    }

    #[test]
    fn test_str_literal() {
        ebnf!(cat = "cat" | "CAT");
        ebnf!(catwoman = cat, ("woman" | "WOMAN"));

        assert!(CatParser::matches("cat"));
        assert!(CatParser::matches("CAT"));
        assert!(!CatParser::matches("cAT"));

        assert!(CatwomanParser::matches("catwoman"));
        assert!(CatwomanParser::matches("catWOMAN"));
        assert!(CatwomanParser::matches("CATWOMAN"));
        assert!(CatwomanParser::matches("CATwoman"));

        assert!(!CatwomanParser::matches("cATWoMaN"));
    }

    #[test]
    fn test_exclusions() {
        ebnf!(number_word = digit - '0', { digit });
        ebnf!(high_number = digit - ('0' | '1' | '2' | '3' | '4' | '5'));

        assert!(NumberWordParser::matches("10203040"));
        assert!(!NumberWordParser::matches("010203040"));

        for i in 0..9 {
            println!("testing {i}");
            assert_eq!(HighNumberParser::matches(i.to_string().as_str()), i > 5);
        }
    }
}
