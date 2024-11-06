
// https://cp-algorithms.com/string/suffix-array.html

use std::ops::{AddAssign, SubAssign, Sub, Add};
use std::fmt::Debug;

const ALPHABET: usize = 256;

fn sort_cyclic_shifts<T>(s: &str) -> Vec<T> 
where
    T: Add<Output=T> + AddAssign + Copy + Debug + Default + TryFrom<usize> 
        + Into<usize> + PartialEq + Sub<Output=T> + SubAssign,
    <T as TryFrom<usize>>::Error: Debug,
{
    let n = s.len();
    let s = s.as_bytes();
    let mut p = vec![T::default(); n];
    let mut c = vec![T::default(); n];
    let mut pn = vec![T::default(); n];
    let mut cn = vec![T::default(); n];
    let mut cnt = vec![T::default(); ALPHABET.max(n)];
    let mut classes = 1;

    for i in 0..n {
        cnt[s[i] as usize] += TryFrom::try_from(1).unwrap();
    }
    for i in 1..ALPHABET {
        cnt[i] = cnt[i] + cnt[i - 1];
    }
    for i in 0..n {
        cnt[s[i] as usize] -= TryFrom::try_from(1).unwrap();
        p[cnt[s[i] as usize].into()] = TryFrom::try_from(i).unwrap();
    }
    c[p[0].into()] = T::default();

    for i in 1..n {
        if s[p[i].into()] != s[p[i - 1].into()] { 
            classes += 1; 
        }
        c[p[i].into()] = TryFrom::try_from(classes - 1).unwrap();
    }

    let mut h = 0;

    while (1 << h) < n {
        for i in 0..n {
            if p[i].into() >= (1 << h) {
                pn[i] = TryFrom::try_from(p[i].into() - (1 << h)).unwrap();
            } else {
                pn[i] = TryFrom::try_from(p[i].into() + n - (1 << h)).unwrap();
            }
        }
        cnt[0..classes].fill(T::default());

        for i in 0..n {
            cnt[c[pn[i].into()].into()] += TryFrom::try_from(1).unwrap();
        }
        for i in 1..classes {
            cnt[i] = cnt[i] + cnt[i - 1];
        }
        for i in (0..n).rev() {
            cnt[c[pn[i].into()].into()] -= TryFrom::try_from(1).unwrap();
            p[cnt[c[pn[i].into()].into()].into()] = pn[i];
        }
        cn[p[0].into()] = T::default();
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

pub fn create_suffix_array<T>(s: &mut String) -> Vec<T> 
where
    T: Add<Output=T> + AddAssign + Copy + Debug + Default + TryFrom<usize> 
        + Into<usize> + PartialEq + Sub<Output=T> + SubAssign,
    <T as TryFrom<usize>>::Error: Debug,
{
    s.push('\0');
    let sa = sort_cyclic_shifts(&s)[1..].to_vec();
    s.pop();
    sa
}

pub fn create_lcp<T>(s: &str, p: &[T]) -> Vec<T> 
where
    T: Add<Output=T> + AddAssign + Copy + Debug + Default + TryFrom<usize> 
        + Into<usize> + PartialEq + Sub<Output=T> + SubAssign,
    <T as TryFrom<usize>>::Error: Debug,
{
    let n = s.len();
    let s = s.as_bytes();
    let mut rank = vec![T::default(); n];
    let mut lcp = vec![T::default(); n - 1];
    let mut k = 0;

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
        if k > 0 {
            k -= 1;
        }
    }

    lcp
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_1() {
        let mut s = String::from("banana");
        let sa: Vec<u8> = create_suffix_array(&mut s);
        let lcp = create_lcp(&s, &sa);

        assert_eq!(sa, vec![5, 3, 1, 0, 4, 2]);

        assert_eq!(lcp, vec![1, 3, 0, 0, 2]);
    }
}