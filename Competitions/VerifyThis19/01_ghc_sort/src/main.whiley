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

// Sequence [start..end) is sorted.
property sorted(int[] seq, int start, int end)
where all { i in start .. end, j in start .. end | i < j ==> seq[i] <= seq[j] }

public property below(int[] src, int s_start, int s_end, int[] dst, int d_start, int d_end)
where all { i in s_start .. s_end, j in d_start .. d_end | src[i] <= dst[j] }

// A sorted array
type sorted is (int[] items) where sorted(items,0,|items|)

// =================================================================
// find_cut_points
// =================================================================

// This is left as native since it is proved separately in
// 01_findcuts, and there is no need to reprove it here.
native function find_cutpoints(int[] s) -> (uint[] c)
// Verification task 1
ensures non_empty(c) && begin_to_end(c,0,|s|) && within_bounds(c,|s|)
// Verification task 2
ensures monotonic(s,c)
// Verification task 3
ensures maximal(s,c)

// =================================================================
// GHC_sort
// =================================================================

function ghc_sort(int[] seq) -> (sorted result):
    // Identify cut points
    uint[] cuts = find_cutpoints(seq)
    // Raise them to separate (sorted) arrays
    sorted[] segs = sort(raise(seq,cuts))
    // Now merge all sorted segments together
    result = []
    //
    for i in 0..|segs|:
         result = merge(result,segs[i])
    // Done
    return result    

// =================================================================
// Raise
// =================================================================

// Raise a set of cutpoints over a sequence into an array of monotonic
// segments.
function raise(int[] seq, uint[] cuts) -> (segment[] segs)
// Cuts cannot be empty, etc
requires non_empty(cuts) && begin_to_end(cuts,0,|seq|) && within_bounds(cuts,|seq|)
// Cut points define monotonic segments
requires monotonic(seq,cuts)
// One less segment than there are cuts
ensures |segs| == |cuts| - 1
// Every segment matches
ensures all { k in 0..|segs| | equal(seq,cuts[k],cuts[k+1],segs[k]) }:
    int n = |cuts| - 1
    segs = [[]; n]
    //
    for i in 0 .. n
    // Size of segs doesn't change
    where |segs| == n
    // Everything so far matches
    where all { k in 0..i | equal(seq,cuts[k],cuts[k+1],segs[k]) }:
        segs[i] = (segment) slice(seq,cuts[i],cuts[i+1])
    //
    return segs

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
// Sort
// =================================================================

// Given a set of monotonic segments, return a set of sorted segments.
// This is done by iterating through the segments and reversing every
// decreasing segment.
function sort(segment[] segs) -> (sorted[] nsegs)
// Same number of sorteds produced
ensures |segs| == |nsegs|
// Every segment returned either matches its corresponding segment or is its reverse
ensures all { k in 0..|segs| | equal(segs[k],nsegs[k]) || reversed(segs[k],nsegs[k]) }:
    //
    nsegs = [[]; |segs|]
    //
    for i in 0..|segs|
    where |nsegs| == |segs|
    where all { k in 0..i | equal(segs[k],nsegs[k]) || reversed(segs[k],nsegs[k]) }:
        // Extract ith
        segment ith = segs[i]
        // Decide whether increasing or decreasing
        if |ith| <= 1:
            nsegs[i] = (sorted) ith
        else if ith[0] < ith[1]:
            // Increasing seg
            nsegs[i] = (sorted) ith
        else:
            // Decreasing seg
            nsegs[i] = (sorted) reverse(ith)
    //
    return nsegs

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

// Merge two sorted segements together, forming a single
// sorted segment.  
function merge(sorted s, sorted t) -> (sorted result)
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
    return (sorted) merged
