use std::ops::{AddAssign, SubAssign, Sub, Add};

// https://cp-algorithms.com/string/suffix-array.html

// TODO - Make the type used as indices configurable so 8 bytes isn't used
//        for every character of `s` 5 times over in `sort_cyclic_shifts()`.

const ALPHABET: usize = 256;

fn sort_cyclic_shifts<T>(s: &str) -> Vec<T> 
where
    T: Add<Output=T> + AddAssign + Copy + Default + From<usize> + Into<usize> 
        + PartialEq + Sub<Output=T> + SubAssign,
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
        cnt[s[i] as usize] += 1.into();
    }
    for i in 1..ALPHABET {
        cnt[i] = cnt[i] + cnt[i - 1];
    }
    for i in 0..n {
        cnt[s[i] as usize] -= 1.into();
        p[cnt[s[i] as usize].into()] = i.into();
    }
    c[p[0].into()] = 0.into();

    for i in 1..n {
        if s[p[i].into()] != s[p[i - 1].into()] { 
            classes += 1; 
        }
        c[p[i].into()] = (classes - 1).into();
    }

    let mut h = 0;

    while (1 << h) < n {
        h += 1;
        for i in 0..n {
            if p[i].into() >= (1 << h) {
                pn[i] = (p[i].into() - (1 << h)).into();
            } else {
                pn[i] = (p[i].into() + n - (1 << h)).into();
            }
        }
        cnt[0..classes].fill(0.into());

        for i in 0..n {
            cnt[c[pn[i].into()].into()] += 1.into();
        }
        for i in 1..classes {
            cnt[i] = cnt[i] + cnt[i - 1];
        }
        for i in (0..n).rev() {
            cnt[c[pn[i].into()].into()] -= 1.into();
            p[cnt[c[pn[i].into()].into()].into()] = pn[i];
        }
        cn[p[0].into()] = 0.into();
        classes = 1;

        for i in 1..n {
            let curr = (c[p[i].into()], c[(p[i].into() + (1 << h)) % n]);
            let prev = (c[p[i - 1].into()], c[(p[i - 1].into() + (1 << h)) % n]);
            if curr == prev {
                classes += 1;
            }
            cn[p[i].into()] = (classes - 1).into();
        }
        std::mem::swap(&mut c, &mut cn);
    }
    p
}

pub fn create_suffix_array(s: &mut String) -> Vec<usize> {
    s.push('$');
    let sa = sort_cyclic_shifts(&s)[1..].to_vec();
    s.pop();
    sa
}

pub fn create_lcp(s: &str, p: &[usize]) -> Vec<usize> {
    let n = s.len();
    let s = s.as_bytes();
    let mut rank = vec![0; n];
    let mut lcp = vec![0, n - 1];
    let mut k = 0;

    for i in 0..n {
        rank[p[i]] = i;
    }
    for i in 0..n {
        if rank[i] == n - 1 {
            k = 0;
            continue;
        }
        let j = p[rank[i] + 1];
        while i + k < n && j + k < n && s[i + k] == s[j + k] {
            k += 1;
        }
        lcp[rank[i]] = k;
        if k > 0 {
            k -= 1;
        }
    }

    lcp
}