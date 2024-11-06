use core::ops::{AddAssign, SubAssign, Sub, Add};
use core::fmt::Debug;

const ALPHABET: usize = 256;

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
        + Into<usize> + PartialEq + Sub<Output=T> + SubAssign,
    <T as TryFrom<usize>>::Error: Debug,
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
        p[cnt[s_wrap![i] as usize].into()] = TryFrom::try_from(i).unwrap();
    }
    c[p[0].into()] = zero_t;

    for i in 1..n {
        if s_wrap![p[i].into()] != s_wrap![p[i - 1].into()] { 
            classes += 1; 
        }
        c[p[i].into()] = TryFrom::try_from(classes - 1).unwrap();
    }

    let mut h = 0;

    while (1 << h) < n {
        let pow2_t = TryFrom::try_from(1 << h).unwrap();
        for i in 0..n {
            if p[i].into() >= (1 << h) {
                pn[i] = p[i] - pow2_t;
            } else {
                pn[i] = TryFrom::try_from(p[i].into() + n - (1 << h)).unwrap();
            }
        }
        cnt[0..classes].fill(zero_t);

        for i in 0..n {
            cnt[c[pn[i].into()].into()] += one_t;
        }
        for i in 1..classes {
            cnt[i] = cnt[i] + cnt[i - 1];
        }
        for i in (0..n).rev() {
            cnt[c[pn[i].into()].into()] -= one_t;
            p[cnt[c[pn[i].into()].into()].into()] = pn[i];
        }
        cn[p[0].into()] = zero_t;
        classes = 1;

        for i in 1..n {
            let curr = (c[p[i].into()], 
                        c[(p[i].into() + (1 << h)) % n]);
            let prev = (c[p[i - 1].into()], 
                        c[(p[i - 1].into() + (1 << h)) % n]);
            if curr != prev {
                classes += 1;
            }
            cn[p[i].into()] = TryFrom::try_from(classes - 1).unwrap();
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
        + Into<usize> + PartialEq + Sub<Output=T> + SubAssign,
    <T as TryFrom<usize>>::Error: Debug,
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
        + Into<usize> + PartialEq + Sub<Output=T> + SubAssign,
    <T as TryFrom<usize>>::Error: Debug,
{
    let zero = T::default();
    let n    = s.len();
    let s    = s.as_bytes();
    let mut rank = vec![zero; n];
    let mut lcp  = vec![zero; n - 1];
    let mut k    = 0;

    for i in 0..n {
        rank[p[i].into()] = TryFrom::try_from(i).unwrap();
    }
    for i in 0..n {
        if rank[i].into() == n - 1 {
            k = 0;
            continue;
        }
        let j = p[rank[i].into() + 1].into();
        while i + k < n && j + k < n && s[i + k] == s[j + k] {
            k += 1;
        }
        lcp[rank[i].into()] = TryFrom::try_from(k).unwrap();
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