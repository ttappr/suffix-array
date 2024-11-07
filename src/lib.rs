//! # Suffix array and LCP array construction.
//! 
//! The suffix array of a string is an array of integers that represents the 
//! lexicographically sorted suffixes of the string. The LCP array of a string
//! is an array of integers that represents the length of the longest common
//! prefix between consecutive suffixes in the suffix array.
//! 
//! The functions of this module are designed to reduce their memory footprints.
//! If, for example, the target string is only 10,000 bytes long, the functions 
//! can internally use `u16` instead of `usize` for their temporary arrays. The 
//! callers must ensure that the type used can represent the largest **byte** 
//! index of the target string.
//! 
//! 
//! ## Complexity
//! - Construction of the suffix array:
//!     - Time complexity: O(n log n)
//!     - Space complexity: O(n)
//! - Construction of the LCP array:
//!    - Time complexity: O(n)
//!    - Space complexity: O(n)
//! 
//! ## Examples
//! ```
//! use suffix_array::*;
//! 
//! let mut s = String::from("banana");
//! let sa = create_suffix_array::<u8>(&mut s).unwrap();
//! let lcp = create_lcp(&s, &sa).unwrap();
//! 
//! assert_eq!(sa, vec![5, 3, 1, 0, 4, 2]);
//! assert_eq!(lcp, vec![1, 3, 0, 0, 2]);
//! ```
//! 
//! ## References
//! - [CP-Algorithms](https://cp-algorithms.com/string/suffix-array.html) 
//!   provides an implementation of the suffix array and LCP array construction
//!   algorithms in C++. The implementation in this module is based on the
//!   implementation provided in the link.
//! - [Wikipedia](https://en.wikipedia.org/wiki/Suffix_array) provides a
//!   detailed explanation of the suffix array data structure.
//! - [Wikipedia](https://en.wikipedia.org/wiki/Longest_common_prefix_array)
//!   provides a detailed explanation of the LCP array data structure.
//! 

mod suffix_array;
pub use suffix_array::*;