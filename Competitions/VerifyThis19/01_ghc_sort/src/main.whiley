// This example is taken from the VerifyThis'19 Competition.
//
// Given a sequence s, the monotonic cutpoints are any indices which
// cut s into segments that are monotonic: each segment's elements are
// either all increasing or all decreasing.  For example:
//
// s = [1,2,3,4,5,7],         cuts = [0,6]
// s = [1,4,7,3,3,5,9],   cuts = [0,3,5,7] (i.e. 1,4,7 | 3,3 | 5,9 )
// s = [6,3,4,2,5,3,7], cuts = [0,2,3,6,7] (i.e. 6,3 | 4,2 | 5,3 | 7 )
//
// This challenge focuses on maximal cut points.  That is, we cannot
// extend any segment further.
type uint is (int x) where x >= 0

property non_empty(int[] seq)
where |seq| > 0

property begin_to_end(int[] seq, int b, int e)
where seq[0] == b && seq[|seq|-1] == e

property within_bounds(int[] seq, int n)
where all { k in 0..|seq| | 0 <= seq[k] && seq[k] <= n }

property reversed(int[] xs, int[] ys, int n)
where all { k in 0..n | xs[k] == ys[|xs|-(k+1)]}

// Sequence [start..end) is sorted.
property sorted(int[] seq, int start, int end)
where all { i in start .. end, j in start .. end | i < j ==> seq[i] <= seq[j] }

public property below(int[] src, int s_start, int s_end, int[] dst, int d_start, int d_end)
where all { i in s_start .. s_end, j in d_start .. d_end | src[i] <= dst[j] }

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

// =================================================================
// find_cut_points
// =================================================================

// This is left as native since it is proved separately in
// 01_findcuts, and there is no need to reprove it here.
native function find_cut_points(int[] s) -> (int[] c)
// Verification task 1
ensures non_empty(c) && begin_to_end(c,0,|s|) && within_bounds(c,|s|)
// Verification task 2
ensures monotonic(s,c)
// Verification task 3
ensures maximal(s,c)

// =================================================================
// GHC_sort
// =================================================================

//function ghc_sort(int[] seq) -> (int[] result)

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
// Resulting array is sorted
ensures sorted(ys,0,|ys|):
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

// Merge two increasing segements together, forming a single
// increasing segment.  
function merge(int[] s, int[] t) -> (int[] result)
// Both segments must be increasing
requires sorted(s,0,|s|) && sorted(t,0,|t|)
// Resulting array contains both inputs
ensures |result| == |s| + |t|
// Resulting array increasing
ensures sorted(result,0,|result|):
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
    // Everything so far sorted
    where sorted(merged,0,z):
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
        // Everything so far sorted
        where sorted(merged,0,z):
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
        // Everything so far sorted
        where sorted(merged,0,z):
            merged[z] = t[y]
            y = y + 1
            z = z + 1        
    //
    return merged
