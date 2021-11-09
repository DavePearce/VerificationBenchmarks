property ordered(int[] s, int a, int b)
where all {j in a..b, k in a..b | j < k ==> s[j] <= s[k]}

property increasing(int[] s, int a, int b)
where all {j in a..b, k in a..b | j < k ==> s[j] < s[k]}

property decreasing(int[] s, int a, int b)
where all {j in a..b, k in a..b | j < k ==> s[j] >= s[k]}

property monotonic(int[] s, int a, int b)
where increasing(s,a,b) || decreasing(s,a,b)

property same_contents(int[] a, int[] b)
where |a| == |b|
where all {i in 0..|a| | some {j in 0..|b| | a[i] == b[j]}}
where all {i in 0..|a| | count(a, a[i], |a|-1) == count(b, a[i], |b|-1)} 

property monotonic_cuts(int[] s, int[] c, int b)
where increasing(c, 0, |c|) && |c| > 0
where all {k in 0..|c| | 0 <= c[k] && c[k] <= b}
where c[0] == 0 && c[|c|-1] == b
where all {k in 1..|c| | |s| >= 1 && c[k] <= |s| ==> monotonic(s, c[k-1], c[k])}

function count(int[] array, int item, int index) -> (int out)
requires index >= 0 && index < |array|
ensures out >= 0
ensures |array| == 0 ==> out == 0
ensures |array| != 0 && index == 0 && item == array[0] ==> out == 1
ensures |array| != 0 && index == 0 && item != array[0] ==> out == 0
ensures |array| != 0 && index > 0 && item == array[index] ==> out == count(array, item, index - 1) + 1
ensures |array| != 0 && index > 0 && item != array[index] ==> out == count(array, item, index - 1):
    int i = 0
    if (|array| != 0):
        if (index == 0):
            if (item == array[0]):
                i = 1
            else:
                i = 0
        else:
            if (array[index] == item):
                i = count(array, item, index - 1) + 1
            else:
                i = count(array, item, index - 1)
    return i

function append(int[] a, int[] b) -> (int[] out)
ensures |out| == |a| + |b|
ensures all {i in 0..|a| | a[i] == out[i]} && all {i in 0..|b| | b[i] == out[i + |a|]}:
    int[] r = a
    for j in 0..|b|
    where |r| == |a| + j
    where all {i in 0..|a| | a[i] == r[i]} && all {i in 0..j | b[i] == r[i + |a|]}:
        r = append(r, b[j])
    return r

function append(int[] array, int x) -> (int[] out)
ensures |out| == |array| + 1 && all {i in 0..|array| | array[i] == out[i]}
ensures out[|array|] == x:
    int[] output = [x; |array| + 1]
    for i in 0..|array|
    where |output| == |array| + 1 && output[|array|] == x && all {j in 0..i | array[j] == output[j]}:
        output[i] = array[i]
    return output   

function append(int[][] array, int[] x) -> (int[][] out)
ensures |out| == |array| + 1 && all {i in 0..|array| | array[i] == out[i]}
ensures out[|array|] == x:
    int[][] output = [x; |array| + 1]
    for i in 0..|array|
    where |output| == |array| + 1 && output[|array|] == x && all {j in 0..i | array[j] == output[j]}:
        output[i] = array[i]
    return output       

function slice(int[] a, int start, int end) -> (int[] out)
requires 0 <= start && start <= end && end <= |a|
ensures |out| == end - start
ensures all {i in start..end | a[i] == out[i - start]}:
    int[] s = []
    for i in start..end
    where |s| == i - start
    where all {j in start..i | a[j] == s[j - start]}:
        s = append(s, a[i])
    return s

function reverse(int[] s) -> (int[] r)
requires decreasing(s, 0, |s|)
ensures ordered(r, 0, |r|)
ensures |r| == |s|
//ensures same_contents(r, s)
ensures all {i in 0..|s| | r[i] == s[|s|-1-i]}:
    int[] out = []
    int k = 0
    while k < |s|
    where 0 <= k && k <= |s|
    where |out| == k
    where all {i in 0..k | out[i] == s[|s|-1-i]}
    //where same_contents(out, slice(s, |s|-k, |s|))
    where ordered(out, 0, k):
        out = append(out, s[|s|-1-k])
        k = k + 1
    return out

// break down `a' into monotonic segments
function monotonic_segments(int[] a) -> (int[][] s)
ensures all {k in 0..|s| | ordered(s[k], 0, |s[k]|)}:
    int[][] segs = []
    int[] c = [0]
    int x = 0
    int y = 1

    while y < |a|
    where 0 <= x && x < y && y <= |a| + 1
    where y == x + 1
    where monotonic_cuts(a, c, x)
    where |c| > 0 && c[0] == 0
    where all {k in 0..|segs| | ordered(segs[k], 0, |segs[k]|)}:
        bool inc = (a[x] < a[y])
        while y < |a| && (a[y-1] < a[y] <==> inc)
        where 0 <= x && x < y && y <= |a|
        where monotonic_cuts(a, c, x)
        where monotonic(a, x, y)
        where monotonic_cuts(a, append(c, y), y):
            y = y + 1
        c = append(c, y)
        int[] incseg = slice(a, x, y)
        if decreasing(incseg, 0, |incseg|):
            incseg = reverse(incseg)
        assume ordered(incseg, 0, |incseg|)

        segs = append(segs, incseg)
        x = y
        y = x + 1
    if x < |a|:
        segs = append(segs, slice(a, x, y))
        c = append(c, |a|)
    assume all {k in 0..|segs| | ordered(segs[k], 0, |segs[k]|)}
    return segs

// merge `left' and `right' respecting order
function merge_pair(int[] left, int[] right) -> (int[] m)
requires ordered(left, 0, |left|)
requires ordered(right, 0, |right|)
ensures ordered(m, 0, |m|)
//ensures same_contents(m, append(left, right))
ensures |m| == |left| + |right|:
    int x = 0
    int y = 0
    int[] merged = []
    while x < |left| && y < |right|
    where ordered(left, 0, |left|)
    where ordered(right, 0, |right|)
    where 0 <= x && x <= |left|
    where 0 <= y && y <= |right|
    where |merged| == x + y
    where 0 < |merged| && x < |left| ==> merged[|merged|-1] <= left[x]
    where 0 < |merged| && y < |right| ==> merged[|merged|-1] <= right[y]
    //where same_contents(merged, append(slice(left, 0, x), slice(right, 0, y)))
    where ordered(merged, 0, |merged|):
        if left[x] < right[y]:
            merged = append(merged, left[x])
            x = x + 1
        else:
            merged = append(merged, right[y])
            y = y + 1
    if x < |left|:
        int p = |merged|
        assume p > 0
        merged = append(merged, slice(left,x,|left|))
        assume ordered(merged, 0, p) && ordered(left, x, |left|) && merged[p-1] <= left[x] ==> ordered(merged, 0, |merged|)
        x = |left|
    if y < |right|:
        int p = |merged|
        assume p > 0
        merged = append(merged, slice(right,y,|right|))
        assume ordered(merged, 0, p) && ordered(right, y, |right|) && merged[p-1] <= right[y] ==> ordered(merged, 0, |merged|)
        y = |right|
    return merged

// merge all segments in `segs' pairwise
function merge_once(int[][] segs) -> (int[][] m)
requires all {k in 0..|segs| | ordered(segs[k], 0, |segs[k]|)}
requires |segs| > 1
ensures all {k in 0..|m| | ordered(m[k], 0, |m[k]|)}
ensures |m| < |segs|:
    int[][] merged = []
    int x = 0
    while x + 1 < |segs|
    where 0 <= x && x <= |segs|
    where all {k in 0..|merged| | ordered(merged[k], 0, |merged[k]|)}
    where 2*|merged| <= x:
        int[] left = segs[x]
        int[] right = segs[x+1]
        int[] n = merge_pair(left, right)
        merged = append(merged, n)
        x = x + 2
    if x < |segs|:
        merged = append(merged, segs[|segs|-1])
    return merged

// sort using GHC's generic method (a kind of patience sorting)
function ghc_sort(int[] a) -> (int[] result)
ensures ordered(result, 0, |result|):
    int[][] segs = monotonic_segments(a)
    while |segs| > 1
    where all {k in 0..|segs| | ordered(segs[k], 0, |segs[k]|)}:
        segs = merge_once(segs)
    int[] merged = []
    if |segs| > 0:
        merged = segs[0]
    return merged