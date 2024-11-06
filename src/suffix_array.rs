use core::ops::{AddAssign, SubAssign, Sub, Add};
use core::fmt::Debug;

const ALPHABET: usize = 256;

/// Converts a value to an index. This function is used to convert the values of
/// the suffix array to indices that can be used to index the target string
/// and other arrays.
/// 
#[inline(always)]
fn idx<T>(n: T) -> usize 
where
    T: TryInto<usize>,
    <T as TryInto<usize>>::Error: Debug,
{
    n.try_into().unwrap()
}

/// Constructs arrays and performs the sorting of suffix indices for the given 
/// string.
/// 
/// # Arguments
/// * `s`: A mutable reference to a string.
/// 
/// # Generic Types
/// * `T`: The type of the elements in the suffix array. Expected to be one of
///        the primitive unsigned integer types.
/// 
/// # Time Complexity
/// O(n log n)
/// 
/// # Returns
/// A vector of integers representing the suffix array of the string.
/// 
fn sort_cyclic_shifts<T>(s: &str) -> Vec<T> 
where
    T: Add<Output=T> + AddAssign + Copy + Debug + Default + TryFrom<usize> 
        + TryInto<usize> + PartialEq + Sub<Output=T> + SubAssign,
    <T as TryFrom<usize>>::Error: Debug,
    <T as TryInto<usize>>::Error: Debug,
{
    let zero_t  = T::default();
    let one_t   = TryFrom::try_from(1).unwrap();
    let s       = s.as_bytes();
    let n       = s.len() + 1;
    let mut p   = vec![zero_t; n];
    let mut c   = vec![zero_t; n];
    let mut pn  = vec![zero_t; n];
    let mut cn  = vec![zero_t; n];
    let mut cnt = vec![zero_t; ALPHABET.max(n)];
    let mut classes = 1;

    macro_rules! s_wrap {
        [$i:expr] => { if $i == n - 1 { b'\0' } else { s[$i] } }
    }

    for i in 0..n {
        cnt[s_wrap![i] as usize] += one_t;
    }
    for i in 1..ALPHABET {
        cnt[i] = cnt[i] + cnt[i - 1];
    }
    for i in 0..n {
        cnt[s_wrap![i] as usize] -= one_t;
        p[idx(cnt[s_wrap![i] as usize])] = T::try_from(i).unwrap();
    }
    c[idx(p[0])] = zero_t;

    for i in 1..n {
        if s_wrap![idx(p[i])] != s_wrap![idx(p[i - 1])] { 
            classes += 1; 
        }
        c[idx(p[i])] = T::try_from(classes - 1).unwrap();
    }

    let mut h = 0;

    while (1 << h) < n {
        let pow2_t = T::try_from(1 << h).unwrap();
        for i in 0..n {
            if idx(p[i]) >= (1 << h) {
                pn[i] = p[i] - pow2_t;
            } else {
                pn[i] = T::try_from(idx(p[i]) + n - (1 << h)).unwrap();
            }
        }
        cnt[0..classes].fill(zero_t);

        for i in 0..n {
            cnt[idx(c[idx(pn[i])])] += one_t;
        }
        for i in 1..classes {
            cnt[i] = cnt[i] + cnt[i - 1];
        }
        for i in (0..n).rev() {
            cnt[idx(c[idx(pn[i])])] -= one_t;
            p[idx(cnt[idx(c[idx(pn[i])])])] = pn[i];
        }
        cn[idx(p[0])] = zero_t;
        classes = 1;

        for i in 1..n {
            let curr = (c[idx(p[i])], 
                        c[(idx(p[i]) + (1 << h)) % n]);
            let prev = (c[idx(p[i - 1])], 
                        c[(idx(p[i - 1]) + (1 << h)) % n]);
            if curr != prev {
                classes += 1;
            }
            cn[idx(p[i])] = T::try_from(classes - 1).unwrap();
        }
        std::mem::swap(&mut c, &mut cn);
        h += 1;
    }
    p
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
/// A vector of integers representing the sorted suffixes of the string.
/// 
pub fn create_suffix_array<T>(s: &str) -> Vec<T> 
where
    T: Add<Output=T> + AddAssign + Copy + Debug + Default + TryFrom<usize> 
        + TryInto<usize> + PartialEq + Sub<Output=T> + SubAssign,
    <T as TryFrom<usize>>::Error: Debug,
    <T as TryInto<usize>>::Error: Debug,
{
    sort_cyclic_shifts(s)[1..].to_vec()
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
/// A vector of integers representing the LCP array of the string.
/// 
pub fn create_lcp<T>(s: &str, p: &[T]) -> Vec<T> 
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
        rank[idx(p[i])] = T::try_from(i).unwrap();
    }
    for i in 0..n {
        if idx(rank[i]) == n - 1 {
            k = 0;
            continue;
        }
        let j = idx(p[idx(rank[i]) + 1]);
        while i + k < n && j + k < n && s[i + k] == s[j + k] {
            k += 1;
        }
        lcp[idx(rank[i])] = T::try_from(k).unwrap();
        k = k.saturating_sub(1);
    }

    lcp
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    #[test]
    fn test_u8_arrays() {
        let s = "banana";

        let sa  = create_suffix_array::<u8>(s);
        let lcp = create_lcp(&s, &sa);

        assert_eq!(sa,  vec![5, 3, 1, 0, 4, 2]);
        assert_eq!(lcp, vec![1, 3, 0, 0, 2]);
    }

    #[test]
    fn test_usize_arrays() {
        let s = "banana";

        let sa  = create_suffix_array::<usize>(s);
        let lcp = create_lcp(&s, &sa);

        assert_eq!(sa,  vec![5, 3, 1, 0, 4, 2]);
        assert_eq!(lcp, vec![1, 3, 0, 0, 2]);
    }

    #[test]
    fn test_u16_index_type_with_long_string_from_file() {
        use std::cmp::Ordering::{self, *};

        // Read the contents of the file. The file is more than 2^16 bytes long.
        let mut s = fs::read_to_string("./data/sample.txt").unwrap();

        // String to find all occurrence of.
        let t = "suffix array".as_bytes();
        let n = t.len();

        // Adjust the length of s so it can be indexed by u16. The lengh of the
        // target string is considered because `s.as_bytes()[i..i + n]` is used
        // in the comparison functions, which can overflow if `i + n` is greater
        // than 2^16.
        s.truncate(65_536 - n);

        // Create the suffix array.
        let sa  = create_suffix_array::<u16>(&s);

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

        // Verify that the indices from the suffix array all index the target
        // string.
        for i in start..end {
            let j = sa[i] as usize;
            let ss = &s[j..j + n];
            assert_eq!(ss, "suffix array");
        }
    }
}