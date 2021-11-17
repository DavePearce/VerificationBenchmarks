// This example is taken from the VerifyThis'19 Competition.
type uint is (int x) where x >= 0

// =================================================================
// Monotonic / Cutpoint Properties
// =================================================================

property non_empty(int[] seq)
where |seq| > 0

property begin_to_end(int[] seq, int b, int e)
where seq[0] == b && seq[|seq|-1] == e

property within_bounds(int[] seq, int n)
where all { k in 0..|seq| | 0 <= seq[k] && seq[k] <= n }

// Sequence [start..end) is monotonically increasing.  For example,
// consider this sequence
//
// +-+-+-+-+-+
// |0|1|2|1|0|
// +-+-+-+-+-+
//  0 1 2 3 4
//
// Then, [0..3) is monotonically increasing, but [2..4) is not.
property increasing(int[] seq, int start, int end)
where all { i in start .. end, j in start .. end | i < j ==> seq[i] < seq[j] }

// Sequence [start..end) is monotonically decreasing.  For example,
// consider this sequence
//
// +-+-+-+-+-+
// |0|1|2|1|0|
// +-+-+-+-+-+
//  0 1 2 3 4
//
// Then, [2..5) is monotonically decreasing, but [1..4) is not.
property decreasing(int[] seq, int start, int end)
where all { i in start .. end, j in start .. end | i < j ==> seq[i] >= seq[j] }

// Sequence [start..end) is either monotonically increasing or
// decreasing.  For example, consider this sequence:
//
// +-+-+-+-+-+
// |0|1|2|1|0|
// +-+-+-+-+-+
//  0 1 2 3 4
//
// Then, [2..5) is monotonically decreasing and [0..3) is
// monotonically increasing.  But, [1..4) is neither increasing nor
// decreasing.
property monotonic(int[] seq, int start, int end)
where increasing(seq,start,end) || decreasing(seq,start,end)

// Sequence [start..end) is a maximal monotonic sequence (i.e. cannot
// be further lengthened without breaking the monotonic propery).
// For example, consider this sequence:
//
// +-+-+-+-+-+
// |0|1|2|1|0|
// +-+-+-+-+-+
//  0 1 2 3 4
//
// Then, [0..2) is monotonically increasing but it is not maximal
// because [0..3) is also monotonically increasing.
property maximal(int[] seq, int start, int end)
where (end >= |seq|) || !monotonic(seq,start,end+1)

// Monotonic property for a set of cutpoints in a given sequence,
// where each cut point identifies the least element in a segment.
// For example, consider this sequence:
//
// +-+-+-+-+-+
// |0|1|2|1|0|
// +-+-+-+-+-+
//  0 1 2 3 4
//
// Then, [0,3,5] is a valid (actually maximal) set of cutpoints.
// Another valid (though not maximal) set is [0,1,3,5].
property monotonic(int[] seq, int[] cut)
// Cut sequence itself be increasing
where increasing(cut,0,|cut|)
// Ensures individual segments are monotonic
where all { k in 1 .. |cut| | monotonic(seq,cut[k-1],cut[k]) }

// Maximal monotonic property for a set of cutpoints.  This means we
// cannot increase the length of any segment without breaking the
// monotonicy property.
property maximal(int[] seq, int[] cut)
// Ensures individual segments are monotonic
where all { k in 1 .. |cut| | maximal(seq,cut[k-1],cut[k]) }

// A monotonic segment
type segment is (int[] items) where monotonic(items,0,|items|)

// =================================================================
// Array Properties
// =================================================================

property reversed(int[] xs, int[] ys, int n)
where all { k in 0..n | xs[k] == ys[|xs|-(k+1)]}

// Two array segments are equal
property equal(int[] xs, int xStart, int[] ys, int yStart, int n)
where all { k in 0..n | xs[k+xStart] == ys[k+yStart]}

// Two arrays are equal
property equal(int[] xs, int[] ys)
where |xs| == |ys|
where all { k in 0..|xs| | xs[k] == ys[k]}

// An array segment and an array are equal
property equal(int[] xs, int start, int end, int[] ys)
where (end-start) == |ys|
where equal(xs,start,ys,0,|ys|)

// One array is the reverse of the other
property reversed(int[] xs, int[] ys)
where |xs| == |ys|
where all { k in 0..|xs| | xs[k] == ys[|xs|-(k+1)]}

// Sequence [start..end) is ordered.
property ordered(int[] seq, int start, int end)
where all { i in start .. end, j in start .. end | i < j ==> seq[i] <= seq[j] }

public property below(int[] src, int s_start, int s_end, int[] dst, int d_start, int d_end)
where all { i in s_start .. s_end, j in d_start .. d_end | src[i] <= dst[j] }

// A ordered array
type ordered is (int[] items) where ordered(items,0,|items|)

// =================================================================
// monotonic segments
// =================================================================

function monotonic_segments(int[] s) -> (ordered[] segs):
    final uint n = |s|
    segs = []
    uint[] cut = [0] // ghost    
    uint x = 0
    uint y = 1   
    //
    while y < n
    // x always starts segment, and y advances to its end
    where y == (x + 1) && x <= n
    // Verification task 1
    where non_empty(cut) && begin_to_end(cut,0,x) && within_bounds(cut,x)
    // Verification task 2
    where monotonic(s,cut)
    // Verification task 3
    where maximal(s,cut):
        //
        ordered incseg
        //
        if s[x] < s[y]:
            while y < n && (s[y-1] < s[y])
            where x < y && y <= n
            // Verification task 2
            where increasing(s,x,y):
                y = y + 1
            incseg = (ordered) slice(s,x,y)
        else:
            while y < n && (s[y-1] >= s[y])
            where x < y && y <= n
            // Verification task 2
            where decreasing(s,x,y):
                y = y + 1
            incseg = (ordered) reverse(slice(s,x,y))
        // Extend the cut
        cut = append(cut,y)
        // Extend segments
        segs = append(segs,incseg)
        x = y
        y = x + 1
    //
    if x < n:
        segs = append(segs, (ordered) slice(s,x,y))
    //
    return segs

// =================================================================
// Append
// =================================================================

// Simple append function which should be in the standard library.
function append<T>(T[] lhs, T rhs) -> (T[] result)
// Cutuence extended by one
ensures |result| == |lhs| + 1
// Every end from original array is retained
ensures all { k in 0..|lhs| | result[k] == lhs[k] }
// End appended
ensures result[|lhs|] == rhs:
    //
    result = [rhs; |lhs| + 1]
    //
    for i in 0..|lhs|
    // Array size unchanged
    where |result| == |lhs| + 1
    // Last end preserved
    where result[|lhs|] == rhs
    // Everything copied over so far
    where all { k in 0..i | result[k] == lhs[k] }:
        result[i] = lhs[i]
    //
    return result

// =================================================================
// Slice
// =================================================================

// Extract a slice [start,end) from original sequence
function slice(int[] seq, uint start, uint end) -> (int[] result)
// Slice cannot be negatively sized!
requires start <= end && end <= |seq|
// Result matches size of slice
ensures |result| == end - start
// Every item matches original sequence
ensures all { k in 0..|result| | result[k] == seq[k+start] }:
    int n = end - start
    int[] slice = [0; n]
    //
    uint i = 0
    uint j = start
    //
    while i < n
    // Ensure relationship
    where j == (i + start)
    // Size of slice unchanged
    where |slice| == n
    // Everything preserved thus far
    where all { k in 0..i | slice[k] == seq[k+start] }:
        slice[i] = seq[j]
        i = i + 1
        j = j + 1
    //
    return slice

// =================================================================
// Reverse
// =================================================================

// Reverse items in an array
function reverse(int[] xs) -> (int[] ys)
// Array is decreasing
requires decreasing(xs,0,|xs|)
// Returned array is same size as input
ensures |xs| == |ys|
// All items in return array in opposite order
ensures reversed(xs,ys,|xs|)
// Resulting array is ordered
ensures ordered(ys,0,|ys|):
    int[] zs = xs
    //
    for i in 0..|xs|
    // Size of array unchanged
    where |xs| == |zs|
    // Everything so far reversed
    where reversed(xs,zs,i):
       xs[i] = zs[|xs| - (i+1)]
    //
    return xs

// =================================================================
// Merge
// =================================================================

// Merge two ordered segements together, forming a single
// ordered segment.  
function merge_pair(ordered s, ordered t) -> (ordered result)
// Resulting array contains both inputs
ensures |result| == |s| + |t|:
    // Calculate size of result
    final int n = |s| + |t|
    // Allocate space for result
    int[] merged = [0;n]
    //
    uint x = 0
    uint y = 0
    uint z = 0     
    //
    while x < |s| && y < |t|
    // Size of array doesn't change
    where |merged| == n
    // Pin amount merged to x + y
    where x <= |s| && y <= |t| && z == x + y
    // Everything so far below s[x..]
    where below(merged,0,z,s,x,|s|)
    // Everything so far below t[y..]    
    where below(merged,0,z,t,y,|t|)
    // Everything so far ordered
    where ordered(merged,0,z):
        if s[x] < t[y]:
            merged[z] = s[x]
            x = x + 1
        else:
            merged[z] = t[y] 
            y = y + 1
        z = z + 1
    // Split
    if x < |s|:
        // Finish off s
        while x < |s|
        // Size of array doesn't change
        where |merged| == n    
        // Pin amount merged to x + y
        where x <= |s| && z == x + y
        // Everything so far below s[x..]
        where below(merged,0,z,s,x,|s|)    
        // Everything so far ordered
        where ordered(merged,0,z):
            merged[z] = s[x]
            x = x + 1
            z = z + 1
    else:
        // Finish off t
        while y < |t|
        // Size of array doesn't change
        where |merged| == n    
        // Pin amount merged to x + y
        where y <= |t| && z == x + y
        // Everything so far below s[x..]
        where below(merged,0,z,t,y,|t|)    
        // Everything so far ordered
        where ordered(merged,0,z):
            merged[z] = t[y]
            y = y + 1
            z = z + 1        
    //
    return (ordered) merged

// =================================================================
// GHC_sort
// =================================================================

function ghc_sort(int[] seq) -> (ordered result):
    // Split out into monotonic segments
    ordered[] segs = monotonic_segments(seq)
    // Now merge all ordered segments together
    result = []
    //
    for i in 0..|segs|:
         result = merge_pair(result,segs[i])
    // Done
    return result    
