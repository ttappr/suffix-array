# Suffix Arrays

A simple library for constructing suffix and LCP arrays with a reduced memory
footprint. `create_suffix_array()` is FAST.

Sorting a suffix array with O(n log n) time complexity can be costly in terms
of memory usage. The cyclic sorting algorithm creates five additional arrays
that contain indices and counts. Each of these has the same number of elements
as there are bytes in the target string. The default primitive used for indexing
is 8 bytes. So there could be 40 additional bytes per byte in the target string.

The functions in this crate are designed to allow the index type to be
specified. If the target string is less than 65,536 characters, an index type
of `u16` will use 1/4 the memory as five internal arrays that have `usize` 
elements for sorting.

The caller will have to ensure that the internal array type is large enough to
represent the largest index in the target string.

## Possible changes to be made

The functions may return `Result` types instead of panicking in the future so
if a developer wants to dynamically handle errors and use a larger type on 
failure, they can.