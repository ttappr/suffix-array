use core::ops::{AddAssign, SubAssign, Sub, Add};
use core::fmt::{self, Debug, Display};
use core::iter::once;
use core::error::Error;
use core::mem::swap;

const ALPHABET: usize = 256;

/// Constructs arrays and performs the sorting of suffix indices for the given 
/// string.
/// 
/// # Arguments
/// * `s`: A reference to a string. The string will be treated as if it has a
///        final b'\0' byte, which produces a suffix array of length n + 1.
/// 
/// # Generic Types
/// * `T`: The type of the elements in the suffix array. Expected to be one of
///        the primitive unsigned integer types.
/// 
/// # Time Complexity
/// O(n log n)
/// 
/// # Returns
/// A vector of integers representing the suffix array of the string, or 
/// `TError` if the conversion of the indices to type `T` (or vice versa) 
/// fails during construction.
/// 
fn sort_cyclic_shifts<T>(s: &str) -> Result<Vec<T>, TError>
where
    T: Add<Output=T> + AddAssign + Copy + Debug + Default + TryFrom<usize> 
        + TryInto<usize> + PartialEq + Sub<Output=T> + SubAssign,
    <T as TryFrom<usize>>::Error: Debug,
    <T as TryInto<usize>>::Error: Debug,
{
    let zero_t  = T::default();
    let one_t   = tval(1)?;
    let s       = s.as_bytes();
    let n       = s.len() + 1;
    let mut p   = vec![zero_t; n];
    let mut c   = vec![zero_t; n];
    let mut pn  = vec![zero_t; n];
    let mut cn  = vec![zero_t; n];
    let mut cnt = vec![zero_t; ALPHABET.max(n)];
    let mut classes = 1;

    macro_rules! s_wrap {
        [$i:expr] => { s.get($i).map_or(0, |&v| v) }
    }

    for &ch in s.iter().chain(once(&0)) {
        cnt[ch as usize] = fallable_add(cnt[ch as usize], one_t)?;
    }
    for i in 1..ALPHABET {
        cnt[i] = fallable_add(cnt[i], cnt[i - 1])?;
    }
    for (i, &ch) in s.iter().chain(once(&0)).enumerate() {
        cnt[ch as usize] -= one_t;
        p[idx(cnt[ch as usize])?] = tval(i)?;
    }

    c[idx(p[0])?] = zero_t;

    for i in 1..n {
        if s_wrap![idx(p[i])?] != s_wrap![idx(p[i - 1])?] { 
            classes += 1; 
        }
        c[idx(p[i])?] = tval(classes - 1)?;
    }

    let mut h = 0;

    while (1 << h) < n {
        for i in 0..n {
            if idx(p[i])? >= (1 << h) {
                pn[i] = p[i] - tval(1 << h)?;
            } else {
                pn[i] = tval(idx(p[i])? + n - (1 << h))?;
            }
        }
        cnt[0..classes].fill(zero_t);

        for i in 0..n {
            let v = &mut cnt[idx(c[idx(pn[i])?])?];
            *v = fallable_add(*v, one_t)?;
        }
        for i in 1..classes {
            cnt[i] = fallable_add(cnt[i], cnt[i - 1])?;
        }
        for i in (0..n).rev() {
            let v = &mut cnt[idx(c[idx(pn[i])?])?];
            *v -= one_t;
            p[idx(*v)?] = pn[i];
        }
        cn[idx(p[0])?] = zero_t;
        classes = 1;

        for i in 1..n {
            let curr = (c[idx(p[i])?], 
                        c[(idx(p[i])? + (1 << h)) % n]);
            let prev = (c[idx(p[i - 1])?], 
                        c[(idx(p[i - 1])? + (1 << h)) % n]);
            if curr != prev {
                classes += 1;
            }
            cn[idx(p[i])?] = tval(classes - 1)?;
        }
        swap(&mut c, &mut cn);
        h += 1;
    }
    Ok(p)
}

/// Constructs the suffix array of a string.
/// 
/// # Arguments
/// * `s`: A string.
/// 
/// # Generic Types
/// * `T`: The type of the elements in the suffix array. Expected to be one of
///        the primitive unsigned integer types. This type represents the 
///        indices of the sorted suffixes.
/// 
/// # Time Complexity
/// O(n log n)
/// 
/// # Returns
/// A vector of integers representing the sorted suffixes of the string, or
/// `TError` if the conversion of the indices to type `T` (or vice versa)
/// fails during construction.
/// 
pub fn create_suffix_array<T>(s: &str) -> Result<Vec<T>, TError>
where
    T: Add<Output=T> + AddAssign + Copy + Debug + Default + TryFrom<usize> 
        + TryInto<usize> + PartialEq + Sub<Output=T> + SubAssign,
    <T as TryFrom<usize>>::Error: Debug,
    <T as TryInto<usize>>::Error: Debug,
{
    Ok(sort_cyclic_shifts(s)?[1..].to_vec())
}

/// Constructs the LCP array of a string.
/// 
/// # Arguments
/// * `s`: A string.
/// * `p`: A reference to the suffix array of the string.
/// 
/// # Generic Types
/// * `T`: The type of the elements in the LCP array. Expected to be one of the
///        primitive unsigned integer types.
/// 
/// # Time Complexity
/// O(n)
/// 
/// # Returns
/// A vector of integers representing the LCP array of the string, or 
/// `TError` if the conversion of the indices to type `T` (or vice versa)
/// fails during construction.
/// 
pub fn create_lcp<T>(s: &str, p: &[T]) -> Result<Vec<T>, TError> 
where
    T: Add<Output=T> + AddAssign + Copy + Debug + Default + TryFrom<usize> 
        + TryInto<usize> + PartialEq + Sub<Output=T> + SubAssign,
    <T as TryFrom<usize>>::Error: Debug,
    <T as TryInto<usize>>::Error: Debug,
{
    let zero = T::default();
    let n    = s.len();
    let s    = s.as_bytes();
    let mut rank = vec![zero; n];
    let mut lcp  = vec![zero; n - 1];
    let mut k    = 0;

    for i in 0..n {
        rank[idx(p[i])?] = tval(i)?;
    }
    for i in 0..n {
        if idx(rank[i])? == n - 1 {
            k = 0;
            continue;
        }
        let j = idx(p[idx(rank[i])? + 1])?;
        while i + k < n && j + k < n && s[i + k] == s[j + k] {
            k += 1;
        }
        lcp[idx(rank[i])?] = tval(k)?;
        k = k.saturating_sub(1);
    }

    Ok(lcp)
}

/// Converts a value to an index. This function is used to convert the values of
/// the suffix array to indices that can be used to index the target string
/// and other arrays.
/// 
#[inline(always)]
fn idx<T>(n: T) -> Result<usize, TError>
where
    T: TryInto<usize>,
    <T as TryInto<usize>>::Error: Debug,
{
    n.try_into().map_err(|e| TError(format!("{:?}", e)))
}

/// Converts an index to type T. This function is used to convert the indices of
/// the suffix array to the type of the suffix array and other internal arrays.
/// 
#[inline(always)]
fn tval<T>(n: usize) -> Result<T, TError>
where
    T: TryFrom<usize>,
    <T as TryFrom<usize>>::Error: Debug,
{
    n.try_into().map_err(|e| TError(format!("{:?}", e)))
}

/// A fallable subtraction function that returns an error if the subtraction
/// operation underflows. (currently unused in this module)
/// 
#[allow(dead_code)]
#[inline(always)]
fn fallable_sub<T>(a: T, b: T) -> Result<T, TError>
where
    T: TryInto<usize> + TryFrom<usize> + Sub<Output=T> + Debug + Copy,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
{
    use format as f;
    if let Some(c) = idx(a).unwrap().checked_sub(idx(b).unwrap()) {
        tval(c).map_err(|_e| TError(f!("Underflow during subtraction, \
                                        ({:?} - {:?}).", a, b)))
    } else {
        Err(TError(f!("Underflow during subtraction, \
                       ({:?} - {:?}).", a, b)))
    }
}

/// A fallable addition function that returns an error if the addition operation
/// overflows.
/// 
#[inline(always)]
fn fallable_add<T>(a: T, b: T) -> Result<T, TError>
where
    T: TryInto<usize> + TryFrom<usize> + Add<Output=T> + Debug + Copy,
    <T as TryInto<usize>>::Error: Debug,
    <T as TryFrom<usize>>::Error: Debug,
{
    use format as f;
    if let Some(c) = idx(a).unwrap().checked_add(idx(b).unwrap()) {
        tval(c).map_err(|_e| TError(f!("Overflow during addition, \
                                        ({:?} + {:?}).", a, b)))
    } else {
        Err(TError(f!("Overflow during addition, \
                       ({:?} + {:?}).", a, b)))
    }
}

/// A generalized error type that represent errors related to the choice of 
/// index type (also, array value type) used in the suffix array and LCP array 
/// construction.
/// 
#[derive(Debug)]
pub struct TError(pub String);

impl Error for TError {
    fn description(&self) -> &str {
        &self.0
    }
}

impl Display for TError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    #[test]
    fn test_u8_arrays() {
        let s = "banana";

        let sa  = create_suffix_array::<u8>(s).unwrap();
        let lcp = create_lcp(&s, &sa).unwrap();

        assert_eq!(sa,  vec![5, 3, 1, 0, 4, 2]);
        assert_eq!(lcp, vec![1, 3, 0, 0, 2]);
    }

    #[test]
    fn test_u32_arrays() {
        let s = "banana";

        let sa  = create_suffix_array::<u32>(s).unwrap();
        let lcp = create_lcp(&s, &sa).unwrap();

        assert_eq!(sa,  vec![5, 3, 1, 0, 4, 2]);
        assert_eq!(lcp, vec![1, 3, 0, 0, 2]);
    }

    #[test]
    fn test_usize_arrays() {
        let s = "banana";

        let sa  = create_suffix_array::<usize>(s).unwrap();
        let lcp = create_lcp(&s, &sa).unwrap();

        assert_eq!(sa,  vec![5, 3, 1, 0, 4, 2]);
        assert_eq!(lcp, vec![1, 3, 0, 0, 2]);
    }

    #[test]
    fn test_u16_index_type_with_long_string_from_file() {
        use std::cmp::Ordering::{self, *};

        // Read the contents of the file. The file is more than 2^16 bytes long.
        let mut s = fs::read_to_string("./data/sample_65536_bytes.txt")
                    .unwrap();

        // String to find all occurrence of.
        let t = "suffix array".as_bytes();
        let n = t.len();

        // Adjust the length of s so it can be indexed by u16. The lengh of the
        // target string is considered because `s.as_bytes()[i..i + n]` is used
        // in the comparison functions, which can overflow if `i + n` is greater
        // than 2^16.
        s.truncate(65_536 - n);

        // Create the suffix array.
        let sa  = create_suffix_array::<u16>(&s).unwrap();

        // Leftmost search function to find the start of the target string
        // indices.
        let start_fn = |i: &u16| -> Ordering {
            let i = *i as usize;
            match s.as_bytes()[i..i + n].cmp(t) {
                Less => Less,
                Equal => Greater,
                Greater => Greater,
            }
        };

        // Rightmost search function to find the end of the target string 
        // indices.
        let end_fn = |i: &u16| -> Ordering {
            let i = *i as usize;
            match s.as_bytes()[i..i + n].cmp(t) {
                Less => Less,
                Equal => Less,
                Greater => Greater,
            }
        };

        // Locate the start and end of the indices of the target string in the
        // suffix array.
        let start = sa.binary_search_by(start_fn).unwrap_err();
        let end   = sa.binary_search_by(end_fn).unwrap_err();

        // There are 157 occurrences of "suffix array" in the target string 
        // after it is truncated to 65524 bytes.
        assert_eq!(end - start, 157);

        // Verify that the indices from the suffix array all index the target
        // string.
        for i in start..end {
            let j = sa[i] as usize;
            let ss = &s[j..j + n];
            assert_eq!(ss, "suffix array");
        }
    }

    #[test]
    fn test_string_too_large_for_u8() {
        let s = "banana".repeat(500);

        if let Err(e) = create_suffix_array::<u8>(&s) {
            // The function should trap the errors and return them in the 
            // result. If a panic occurs during conversion, then there's a bug 
            // in the code.
            println!("\n{}", e);
        } else {
            panic!("Expected an error!");
        }
    }
}



