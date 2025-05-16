#define _CRT_SECURE_NO_WARNINGS
#include <string>
#include <string_view>
#include <stack>
#include <utility>
#include <iostream>
#include <vector>
#include <tuple>
#include <algorithm>
#include <random>
#include <cassert>
#include <cstdint>
#include <cstring>
#include <cstdio>
#include <chrono>
#include <thread>

using namespace std;
#define Assert assert
//#define Assert(x) 

constexpr bool SLOW_CHECKS = true;

// ----------------------------------------------------------------------------
// Suffix array and LCP array
// ----------------------------------------------------------------------------

// Builds the suffix array of S in O(n) time using the skew algorithm
// from Kärkkäinen and Sanders, "Simple linear work suffix array construction" (2003).
// https://doi.org/10.1007/3-540-45061-0_73
// and Kärkkäinen, Sanders, Burkhardt, "Linear work suffix array construction" (2006).
// https://doi.org/10.1145/1217856.1217858
// Input: S[0..n-1], consisting of values from the range 1..n.
// Output: SA[0..n-1], containing the values i from 0..n-1
// sorted in lexicographic order of S[i:].
void BuildSuffixArray(vector<int> S, vector<int> &SA)
{
    int nOrig = (int) S.size();
    if constexpr (SLOW_CHECKS) for (int i = 0; i < nOrig; ++i) Assert(1 <= S[i] && S[i] <= nOrig); 
    // If |S| is not a multiple of 3, add additional characters that will be lexicographically
    // smaller than any existing ones but still greater than 0.
    int n = nOrig; while (n % 3 != 0) ++n;
    for (auto &si : S) si += (n - nOrig);
    for (int i = nOrig; i < n; ++i) S.emplace_back(i - nOrig + 1);
    if constexpr (SLOW_CHECKS) for (int i = 0; i < nOrig; ++i) Assert(1 <= S[i] && S[i] <= n); 
    // Append two more '0' values to S as sentinels.  These don't count towards n.
    S.emplace_back(0); S.emplace_back(0);

    // Step 1: sort the suffixes S_i where i mod 3 = 1 or 2.

    const int n23 = (n * 2) / 3, n3 = n / 3;
    vector<int> indices12; indices12.reserve(n23);
    vector<int> hist(n + 1), outIndices12(n23);
    for (int i = 0; i < n; ++i) if (i % 3 != 0) indices12.emplace_back(i);
    // Sort the values i in indices12 in increasing order of S[i:i+3], using radix sort.
    for (int offset = 2; offset >= 0; --offset)
    {
        for (int a = 0; a <= n; ++a) hist[a] = 0;
        for (int i : indices12) ++hist[S[i + offset]];
        for (int next = 0, a = 0; a <= n; ++a) {
            int next2 = next + hist[a]; hist[a] = next; next = next2; }
        // Now hist[a] tells us where the next element with the value a should go in the output vector.
        for (int i : indices12) outIndices12[hist[S[i + offset]]++] = i; 
        swap(outIndices12, indices12);
    }

    if constexpr (SLOW_CHECKS) {
        // Check that we still have the correct set of indices.
        vector<int> v1; for (int i = 0; i < n; ++i) if (i % 3 != 0) v1.emplace_back(i);
        vector<int> v2 = indices12; sort(v2.begin(), v2.end()); Assert(v1 == v2); }

    // Assign a lexicographic name to each index from 'indices12'.
    vector<int> lexNames(n, -1); int nLexNames = 0;
    tuple<int, int, int> tup, prevTup;
    for (int j = 0; j < n23; ++j)
    {
        int i = indices12[j];
        tup = make_tuple(S[i], S[i + 1], S[i + 2]);
        Assert(j == 0 || tup >= prevTup);
        if (j == 0 || tup > prevTup) { ++nLexNames; prevTup = tup; }
        lexNames[i] = nLexNames; // use values 1..2n/3
    }
    // If all the lexical names were different, then 'indices' are already in the order in which we'll
    // have them in the final suffix array.  Otherwise we'll sort them now using a recursive call.
    if (nLexNames < n23)
    {
        vector<int> S12(n23, -1), SA12;
        for (int i = 0; i < n3; ++i) S12[i] = lexNames[3 * i + 1], S12[i + n3] = lexNames[3 * i + 2];
        BuildSuffixArray(S12, SA12); Assert(int(SA12.size()) == n23);
        // SA12 contains indices from the range 0..2n/3 - 1.  Convert them into
        // suitable indices from 'indices12'.
        for (int j = 0; j < n23; ++j) {
            int i12 = SA12[j]; 
            Assert(0 <= i12 && i12 < n23);
            int i = (i12 < n3) ? 3 * i12 + 1 : 3 * (i12 - n3) + 2;
            indices12[j] = i; }
        if constexpr (SLOW_CHECKS) {
            // Check that we still have the correct set of indices.
            vector<int> v1; for (int i = 0; i < n; ++i) if (i % 3 != 0) v1.emplace_back(i);
            vector<int> v2 = indices12; sort(v2.begin(), v2.end()); Assert(v1 == v2); }
    }
    // Prepare a vector which tells us, for each index from 'indices12', at which
    // position in that vector it appears.
    vector<int> inv12 = move(lexNames); // Reuse the old vector to save time.
    Assert(int(inv12.size()) == n);
    for (int i = 0; i < n; ++i) inv12[i] = -1;
    for (int j = 0; j < n23; ++j) inv12[indices12[j]] = j;

    // Step 2: sort the suffixes S_i where i mod 3 = 0.
    vector<int> indices0; indices0.reserve(n3);
    for (int i : indices12) if (i % 3 == 1) indices0.emplace_back(i - 1);
    Assert(int(indices0.size()) == n3);
    // Sort the indices i from 'indices0' stably with regard to S[i],
    // using one pass of radix sort.
    for (int a = 0; a <= n; ++a) hist[a] = 0;
    for (int i : indices0) ++hist[S[i]];
    for (int next = 0, a = 0; a <= n; ++a) {
        int next2 = next + hist[a]; hist[a] = next; next = next2; }
    // Now hist[a] tells us where the next element with the value a should go in the output vector.
    outIndices12.resize(n3);
    for (int i : indices0) outIndices12[hist[S[i]]++] = i; 
    swap(outIndices12, indices0);

    // Step 3: merge both sequences of suffixes into the final suffix array.
    SA.resize(n);
    int src12 = 0, src0 = 0, dest = 0;
    while (src12 < n23 && src0 < n3)
    {
        const int i12 = indices12[src12], i0 = indices0[src0];
        Assert(inv12[i0 + 1] >= 0); 
        bool use12;
        if (i12 % 3 == 1) { Assert(inv12[i12 + 1] >= 0); use12 = make_tuple(S[i12], inv12[i12 + 1]) < make_tuple(S[i0], inv12[i0 + 1]); }
        else { Assert(i12 % 3 == 2); 
            int t12; if (i12 + 2 < n) { t12 = inv12[i12 + 2]; Assert(t12 >= 0); } else t12 = -1;
            int t0 = inv12[i0 + 2]; Assert(t0 >= 0);
            use12 = make_tuple(S[i12], S[i12 + 1], t12) < make_tuple(S[i0], S[i0 + 1], t0); }
        if (use12) { SA[dest++] = i12; ++src12; } else { SA[dest++] = i0; ++src0; }
    }
    while (src12 < n23) SA[dest++] = indices12[src12++];
    while (src0 < n3) SA[dest++] = indices0[src0++];

    // If the length of the original string was not a multiple of 3 and we
    // appended additional characters to it, we should now remove the corresponding
    // suffixes from the start of SA.
    if (n > nOrig) 
    {
        int d = n - nOrig;
        for (int i = 0; i < d; ++i) Assert(SA[i] >= nOrig);
        for (int i = d; i < n; ++i) SA[i - d] = SA[i];
        for (int i = 0; i < d; ++i) SA.pop_back(); 
    }
}

// Calculates the LCP array for the string S, given its suffix array SA.
// Based on Kasai et al., "Linear-time longest-common-prefix computation in suffix arrays
// and its applications" (2001).  http://dx.doi.org/10.1007/3-540-48194-X_17
// Upon return, LCP[i] will be the length of the longest common prefix of 
// S[SA[i - 1]:] and S[SA[i]:].   (LCP[0] will be set to 0.)
void BuildLcpArray(const vector<int> &S, const vector<int> &SA, vector<int> &LCP)
{
    const int n = (int) S.size(); Assert(n == (int) SA.size());
    LCP.resize(n); LCP[0] = 0;
    // Prepare the inverse of the SA table.
    vector<int> rank(n, -1); for (int i = 0; i < n; ++i) {
        Assert(0 <= SA[i] && SA[i] < n); Assert(rank[SA[i]] < 0);
        rank[SA[i]] = i; }
    for (int h = 0, i = 0; i < n; ++i)
    {
        int q = rank[i]; if (q == 0) continue;
        int k = SA[q - 1];
        while (i + h < n && k + h < n && S[i + h] == S[k + h]) ++h; // Note: Kasai et al. mistakenly have 'j + h' instead of 'k + h' in line 8 of Fig. 3
        LCP[q] = h;
        if (h > 0) --h;
    }
}

// Builds both SA and LCP.
void BuildSuffixArray(const vector<int> &S, vector<int> &SA, vector<int> &LCP)
{
    BuildSuffixArray(S, SA);
    BuildLcpArray(S, SA, LCP);
}

// Builds a suffix array for 's'; optionally (if LCP is not null) also builds the LCP array.
void BuildSuffixArray(const string &s, vector<int> &SA, vector<int> *LCP)
{
    bool isLcAlpha = true; int_fast32_t lettersUsed = 0;
    for (char c : s) if (c < 'a' || c > 'z') { isLcAlpha = false; break; } else lettersUsed |= 1 << (c - 'a');
    const int n = (int) s.length(); vector<int> S(n, -1);
    if (isLcAlpha) {
        // A cheaper implementation for the common scenario where 's' consists
        // only of lowercase letters of the English alphabet.
        char letterToInt[26]; for (int i = 0, j = 0; i < 26; ++i) if (lettersUsed & (int_fast32_t(1) << i)) letterToInt[i] = ++j;
        for (int i = 0; i < n; ++i) S[i] = letterToInt[s[i] - 'a']; }
    else {
        vector<int> byteToInt(256, -1);
        for (int i = 0, j = 0; i < n; ++i) {
            int &b = byteToInt[(unsigned char) s[i]];
            if (b < 0) b = ++j;
            S[i] = b; } }
    BuildSuffixArray(S, SA);
    if (LCP) BuildLcpArray(S, SA, *LCP);
}

// Builds both SA and LCP.
void BuildSuffixArray(const string &s, vector<int> &SA, vector<int> &LCP) 
{
    BuildSuffixArray(s, SA, &LCP); 
}

// ----------------------------------------------------------------------------
// Suffix tree and efficient LCP queries 
// ----------------------------------------------------------------------------

// A suffix tree structure with support for constant-time LCP queries.
struct TSuffixTree
{
protected:
    typedef int NodeId;
    struct Node
    {
        bool leaf = false;
        int depth = -1; // in characters
        int level = -1; // in nodes; initialized during InitEulerTour
        NodeId lastChild = -1, prevSib = -1;
        Node() = default;
        Node(bool Leaf, int Depth) : leaf(Leaf), depth(Depth) { }
    };
    vector<Node> nodes;
    NodeId root = -1; 
    int n = -1; // n = the length of the string whose suffix tree this is

    NodeId InsertNode(bool leaf, int depth);
    void AppendChild(NodeId parent, NodeId child);
    // Constructs the suffix tree from the suffix array, based on
    // the algorithm from https://en.wikipedia.org/w/index.php?title=LCP_array&oldid=1228831623#Suffix_tree_construction .
    void InitFromSuffixArray(const vector<int> &SA, const vector<int> &LCP);

    vector<NodeId> eulerTour; // E in [BF00]
    vector<int> eulerTourLevels; // A in [BF00];   eulerTourLevels[r] = nodes[eulerTour[r]].level
    vector<int> firstOcc; // firstOcc[i] = the first occurrence, in 'eulerTour', of the leaf corresponding to S[i:]
    // Constructs the Euler tour of the suffix tree.
    void InitEulerTour();

    int blockSize; // log2(n) / 2
    int eulerTourLen, numBlocks; // eulerTour.size() and ceil(eulerTourLen/blockSize)
    // minToBlkEnd[r] is the index, in 'eulerTourLevels', of the smallest element
    // from r to the end of the block to which r belongs, i.e. blockSize * (r / blockSize + 1) - 1.
    // minFromBlkStart[r] is the same but from the start of the block (i.e. blockSize * (r / blockSize)) to r.
    vector<int> minToBlkEnd, minFromBlkStart;
    // Let 0 <= b < 2^{blockSize - 1} and 0 <= i < j < blockSize.  Then, for the normalized block
    // whose shape is described by 'b' (where bits with a value of 0 represent steps up the tree,
    // where the next element is 1 less than the previous one, and bits with a value of 1 represent
    // steps down the tree, where the next element is 1 greater than the previous one), the index (in the block)
    // of the minimal value on the range i..j is normBlockMin[b * pairsPerBlock + j * (j - 1) / 2 + i].
    vector<int> normBlockMin;
    int pairsPerBlock; // blockSize * (blockSize - 1) / 2
    // blockGroupMin[t][r] is the index, in 'eulerTourLevels', of the smallest element
    // from r * blockSize to (r + 2^t) * blockSize - 1.
    vector<vector<int>> blockGroupMin;
    // normBlock[r] is a (blockSize - 1)-bit number representing the normalized shape
    // of the block consisting of eulerTourLevels[r * blockSize ... (r + 1) * blockSize - 1].
    vector<int> normBlocks; 
    // log2table[i] = floor(log2(i)) for i = 1, ..., numBlocks.
    vector<int> log2table;

public:

    // Initializes, in O(n) time, the data structures needed to be able to answer LCP queries in O(1) time.
    // Based on [BF00] = Bender & Farach-Colton, "The LCA problem revisited" (2000).  https://doi.org/10.1007/10719839_9
    void InitBF00();

    // Constructs the suffix tree based on the given SA array and the corresponding LCP array.
    TSuffixTree(const vector<int> &SA, const vector<int> &LCP, bool doInitBF00 = true);

    // Returns the length of the longest common prefix of S[i:] and S[j:] in constant time,
    // using the algorithm from [BF00].
    int LCP(int i, int j);

    // This function tests if LCP() returns correct results.
    // The string S, of course, must be the one whose suffix array and LCP array
    // were passed to the constructor of this instance of TSuffixTree.
    template<typename String>
    void TestLcp(const String& S, mt19937_64& rnd);
};

TSuffixTree::NodeId TSuffixTree::InsertNode(bool leaf, int depth) 
{ 
    NodeId u = (int) nodes.size(); 
    nodes.emplace_back(leaf, depth); 
    return u; 
}

void TSuffixTree::AppendChild(NodeId parent, NodeId child)
{
    auto &Parent = nodes[parent], &Child = nodes[child];
    Child.prevSib = Parent.lastChild; Parent.lastChild = child;
}

// Constructs the suffix tree from the suffix array, based on
// the algorithm from https://en.wikipedia.org/w/index.php?title=LCP_array&oldid=1228831623#Suffix_tree_construction .
void TSuffixTree::InitFromSuffixArray(const vector<int> &SA, const vector<int> &LCP)
{
    n = (int) SA.size(); Assert(n == (int) LCP.size());
    nodes.clear(); nodes.reserve(2 * n);
    // Create the root node.
    root = InsertNode(false, 0);
    if (n <= 0) return;
    // Create a leaf corresponding to the lexicographically smallest suffix, S[SA[0]:].
    NodeId leaf = InsertNode(true, n - SA[0]);
    AppendChild(root, leaf);
    // 'branch' represents the path from the root to the current leaf.
    vector<int> branch; branch.emplace_back(root); branch.emplace_back(leaf);
    // Add leaves (and internal nodes as needed) corresponding to other suffixes
    // in lexicographically increasing order.
    for (int i = 1; i < n; ++i)
    {
        int depth = n - SA[i], lcp = LCP[i];
        Assert(lcp <= depth); Assert(lcp <= nodes[leaf].depth);
        leaf = InsertNode(true, depth);
        do { branch.pop_back(); } while (nodes[branch.back()].depth > lcp);
        NodeId parent = branch.back();
        // Perhaps a suitable internal node already exists.
        if (lcp == nodes[parent].depth) AppendChild(parent, leaf);
        // Otherwise we'll insert one now.
        else {
            NodeId mid = InsertNode(false, lcp);
            auto &Parent = nodes[parent], &Mid = nodes[mid], &Leaf = nodes[leaf];
            NodeId sib = Parent.lastChild; Assert(sib >= 0); auto &Sib = nodes[sib];
            Mid.prevSib = Sib.prevSib; Sib.prevSib = -1;
            Mid.lastChild = leaf; Leaf.prevSib = sib;
            Parent.lastChild = mid;
            branch.emplace_back(mid); }
        branch.emplace_back(leaf);
    }
}

void TSuffixTree::InitEulerTour()
{
    for (auto &node : nodes) node.level = -1;
    eulerTour.clear(); eulerTour.reserve(2 * nodes.size());
    eulerTour.emplace_back(root); nodes[root].level = 0;
    // 'branch' = the path from the root to the current node.
    vector<NodeId> branch; branch.emplace_back(root);
    while (true)
    {
        NodeId prev = -1, cur = eulerTour.back();
        Assert(branch.back() == cur);
        if (eulerTour.size() > 1) prev = eulerTour[eulerTour.size() - 2];
        const auto &Cur = nodes[cur];
        Assert(Cur.level >= 0);
        // If 'prev' is the parent of 'cur', we have to continue into the last child of 'cur',
        // otherwise 'prev' is a child of 'cur' and we have to continue into the previous sibling of 'prev'.
        NodeId next = (prev >= 0 && nodes[prev].level == Cur.level + 1) ? nodes[prev].prevSib : Cur.lastChild;
        if (next >= 0) { 
            branch.emplace_back(next); eulerTour.emplace_back(next);
            auto &Next = nodes[next]; Assert(Next.level < 0); Next.level = Cur.level + 1; }
        // However, if such a step into a child of 'cur' is not available, we have to return to
        // the parent of 'cur', which we find just above it on 'branch'.
        else {
            branch.pop_back();
            if (branch.empty()) break;
            eulerTour.emplace_back(branch.back()); }
    }
    // Calculate the array of levels of the nodes on the Euler tour (for convenience)
    // and the first occurrence of each leaf (or rather, of each suffix) on the Euler tour.
    // (In fact any occurrence would do for the purposes of LCP queries, not necessarily the first one.)
    firstOcc.clear(); firstOcc.resize(n, -1);
    eulerTourLevels.resize(eulerTour.size());
    for (int j = 0; j < (int) eulerTour.size(); ++j)
    {
        Node &node = nodes[eulerTour[j]];
        eulerTourLevels[j] = node.level;
        if (! node.leaf) continue;
        int i = n - node.depth; Assert(0 <= i); Assert(i < n);
        if (firstOcc[i] < 0) firstOcc[i] = j;
    }
}

// Initializes, in O(n) time, the data structures needed to be able to answer LCP queries in O(1) time.
// Based on [BF00] = Bender & Farach-Colton, "The LCA problem revisited" (2000).  https://doi.org/10.1007/10719839_9
void TSuffixTree::InitBF00()
{
    int log2n = 1; while ((1 << log2n) < n) ++log2n;
    blockSize = (log2n + 1) / 2; Assert(blockSize > 0);
    eulerTourLen = (int) eulerTour.size(); Assert(eulerTourLen == (int) eulerTourLevels.size());
    numBlocks = (eulerTourLen + blockSize - 1) / blockSize;
    // Calculate the log2 table.
    log2table.resize(numBlocks + 1); log2table[0] = -1;
    for (int blockNo = 1, log2 = 0; blockNo <= numBlocks; ++blockNo)
    {
        if (blockNo == (1 << (log2 + 1))) ++log2;
        Assert((blockNo & (1 << log2)) != 0);
        Assert((blockNo >> (log2 + 1)) == 0);
        log2table[blockNo] = log2;
    }
    // Calculate the minimums from the start and end of each block.
    minToBlkEnd.resize(eulerTourLen); minFromBlkStart.resize(eulerTourLen);
    for (int blockNo = 0; blockNo < numBlocks; ++blockNo)
    {
        int r1 = blockNo * blockSize, r2 = (blockNo + 1) * blockSize - 1;
        if (r2 >= eulerTourLen) r2 = eulerTourLen - 1;
        for (int minLevel = -1, minWhere = -1, r = r1; r <= r2; ++r) {
            if (minWhere < 0 || eulerTourLevels[r] < minLevel) minWhere = r, minLevel = eulerTourLevels[r];
            minFromBlkStart[r] = minWhere; }
        for (int minLevel = -1, minWhere = -1, r = r2; r >= r1; --r) {
            if (minWhere < 0 || eulerTourLevels[r] < minLevel) minWhere = r, minLevel = eulerTourLevels[r];
            minToBlkEnd[r] = minWhere; }
    }
    // Calculate the results of all queries on normalized blocks.
    pairsPerBlock = (blockSize * (blockSize - 1)) / 2;
    normBlockMin.clear(); normBlockMin.resize(pairsPerBlock << (blockSize - 1), -1);
    int nNormBlocks = 1 << (blockSize - 1); vector<int> normBlock(blockSize);
    for (int b = 0; b < nNormBlocks; ++b)
    {
        normBlock[0] = 0;
        for (int i = 0; i < (blockSize - 1); ++i) normBlock[i + 1] = normBlock[i] + (((b >> i) & 1) ? 1 : -1);
        for (int i = 0; i < blockSize - 1; ++i)
            for (int minLevel = normBlock[i], minWhere = i, j = i + 1; j < blockSize; ++j) {
                if (normBlock[j] < minLevel) minLevel = normBlock[j], minWhere = j;
                normBlockMin[b * pairsPerBlock + j * (j - 1) / 2 + i] = minWhere; }
    }
    // Calculate the normalized blocks for our Euler tour.
    normBlocks.resize(numBlocks);
    for (int blockNo = 0; blockNo < numBlocks; ++blockNo)
    {
        int b = 0; for (int r = 1; r < blockSize; ++r)
        {
            int pos = blockNo * blockSize + r;
            // If the last block is incomplete, we'll pretend that the missing steps are all
            // downward, which causes them to have no impact on range-minimum queries.
            int delta = (pos < eulerTourLen) ? eulerTourLevels[pos] - eulerTourLevels[pos - 1] : 1;
            Assert(delta == -1 || delta == 1);
            if (delta == 1) b |= (1 << (r - 1));
        }
        normBlocks[blockNo] = b;
    }
    // Calculate the minimums over whole blocks or groups of 2^t blocks.
    int tMax = 0; while (numBlocks >= (1 << (tMax + 1))) ++tMax;
    blockGroupMin.clear(); blockGroupMin.resize(tMax + 1);
    blockGroupMin[0].resize(numBlocks);
    for (int blockNo = 0; blockNo < numBlocks; ++blockNo) blockGroupMin[0][blockNo] = minToBlkEnd[blockNo * blockSize];
    for (int t = 1; t <= tMax; ++t)
    {
        auto &prev = blockGroupMin[t - 1], &cur = blockGroupMin[t];
        int m = numBlocks - (1 << t) + 1; Assert(m > 0);
        cur.resize(m);
        for (int r = 0; r < m; ++r) {
            int cand1 = prev[r], cand2 = prev[r + (1 << (t - 1))];
            cur[r] = (eulerTourLevels[cand1] < eulerTourLevels[cand2]) ? cand1 : cand2; }
    }
    if constexpr (SLOW_CHECKS) for (int t = 0; t <= tMax; ++t) for (int r = 0; r < (int) blockGroupMin[t].size(); ++r)
    {
        int r1 = r * blockSize, r2 = (r + (1 << t)) * blockSize - 1;
        if (r2 >= eulerTourLen) r2 = eulerTourLen - 1;
        Assert(0 <= r1 && r1 <= r2 && r2 < eulerTourLen);
        int minLevel = -1, minWhere = -1;
        for (int rr = r1; rr <= r2; ++rr) if (minWhere < 0 || eulerTourLevels[rr] < minLevel) minWhere = rr, minLevel = eulerTourLevels[rr];
        int minWhere2 = blockGroupMin[t][r]; Assert(minWhere2 >= r1); Assert(minWhere2 <= r2);
        int minLevel2 = eulerTourLevels[minWhere2]; Assert(minLevel2 == minLevel);
    }
}

TSuffixTree::TSuffixTree(const vector<int> &SA, const vector<int> &LCP, bool doInitBF00)
{
    InitFromSuffixArray(SA, LCP);
    InitEulerTour();
    if (doInitBF00) InitBF00();
}

// Returns the length of the longest common prefix of S[i:] and S[j:] in constant time,
// using the algorithm from [BF00].
int TSuffixTree::LCP(int i, int j)
{
    Assert(0 <= i && i < n); Assert(0 <= j && j < n);
    // Treat i == j as a special case.
    if (i == j) return n - i;
    // Convert the LCP query into a range-minimum query.
    i = firstOcc[i]; j = firstOcc[j]; if (j < i) swap(i, j);
    int bi = i / blockSize, bj = j / blockSize; Assert(0 <= bi && bi <= bj && bj < numBlocks);
    // If i and j are in the same block, use the precomputed results for normalized blocks.
    if (bi == bj) 
    {
        int b = normBlocks[bi], ib = i % blockSize, jb = j % blockSize;
        int minWhere = normBlockMin[b * pairsPerBlock + jb * (jb - 1) / 2 + ib];
        minWhere += (bi * blockSize);
        int result = nodes[eulerTour[minWhere]].depth; return result; 
    }
    // Consider the candidates in block 'bi' from 'i' to the end.
    int minWhere = minToBlkEnd[i]; int minLevel = eulerTourLevels[minWhere];
    // Consider the candidates in block 'bj' from the start to 'j'.
    int cand = minFromBlkStart[j]; int candLevel = eulerTourLevels[cand];
    if (candLevel < minLevel) minWhere = cand, minLevel = candLevel;
    // Consider the candidates from intermediate blocks, which the query covers in their entirety.
    if (bj - bi > 1)
    {
        int t = log2table[bj - bi - 1];
        auto &v = blockGroupMin[t];
        // The blocks bi+1..bj-1 can be covered by two groups of 2^t blocks.
        // The first group starts with block bi+1.
        Assert(bi + (1 << t) < bj);
        cand = v[bi + 1]; candLevel = eulerTourLevels[cand];
        if (candLevel < minLevel) minWhere = cand, minLevel = candLevel;
        // The second group ends with block bj-1 and thus starts with block bj - 2^t.
        Assert(bj - (1 << t) > bi);
        cand = v[bj - (1 << t)]; candLevel = eulerTourLevels[cand];
        if (candLevel < minLevel) minWhere = cand, minLevel = candLevel;
    }
    int result = nodes[eulerTour[minWhere]].depth; return result;
}

// ----------------------------------------------------------------------------
// Test code for suffix arrays, suffix trees and LCP queries 
// ----------------------------------------------------------------------------

template<typename String>
void TSuffixTree::TestLcp(const String& S, mt19937_64& rnd)
{
    // If the string is short, we'll try LCP queries for all pairs (i, j),
    // otherwise only for a thousand randomly chosen pairs.
    Assert(n == (int) S.size());
    bool doAll = (n <= 30);
    int i = 0, j = 0;
    for (int testNo = 0; testNo < (doAll ? (n * (n + 1)) / 2 : 1000); ++testNo)
    {
        if (!doAll) { i = uniform_int_distribution<int>(0, n - 1)(rnd); j = uniform_int_distribution<int>(0, n - 1)(rnd); }
        // Calculate the true LCP(S[i:], S[j:]) by comparing character by character.
        int trueLcp = 0;
        while (i + trueLcp < n && j + trueLcp < n && S[i + trueLcp] == S[j + trueLcp]) ++trueLcp;
        // Calculate the LCP with a range-minimum query, very naively implemented.
        // This verifies that our Euler tour and node depths are correct.
        int lcp = -1;
        int rFrom = firstOcc[i], rTo = firstOcc[j]; if (rTo < rFrom) swap(rFrom, rTo);
        for (int r = rFrom; r <= rTo; ++r) 
        {
            Node &node = nodes[eulerTour[r]];
            if (lcp < 0 || node.depth < lcp) lcp = node.depth;
        }
        Assert(lcp == trueLcp);
        // Calculate the LCP with the O(1) algorithm of [BF00].
        int lcp2 = LCP(i, j);
        Assert(lcp2 == trueLcp);
        //
        if (doAll) { if (j == i) ++i, j = 0; else ++j; }
    }
}

// Tests that BuildSuffixArray and BuildLcpArray return correct results
// on the given string S, then constructs a suffix tree with support for
// LCP queries and tests that those queries return correct results too.
template<typename String>
void TestSuffixArrayAndTree(const String &S, mt19937_64 &rnd)
{
    const int n = (int) S.size();
    vector<int> SA, LCP; BuildSuffixArray(S, SA, LCP);
    // Calculate the suffix array of 'SA' by simply sorting all the suffixes.
    vector<int> SA2(n); for (int i = 0; i < n; ++i) SA2[i] = i;
    sort(SA2.begin(), SA2.end(), [&S, n] (int i, int j) { 
        for (int d = 0; i + d < n && j + d < n; ++d) {
            int si = S[i + d], sj = S[j + d]; if (si != sj) return (si < sj); }
        return i > j; });
    // Compare the results with those of BuildSuffixArray.
    Assert(n == (int) SA.size());
    for (int i = 0; i < n; ++i) Assert(SA[i] == SA2[i]);
    // Test the LCP array.
    Assert(n == (int) LCP.size());
    for (int r = 0; r < n; ++r)
    {
        if (r == 0) { Assert(LCP[r] == 0); continue; }
        int i = SA[r - 1], j = SA[r];
        int lcp = 0; while (i + lcp < n && j + lcp < n && S[i + lcp] == S[j + lcp]) ++lcp;
        Assert(LCP[r] == lcp);
    }
    // Build a suffix tree and test LCP queries in it.
    TSuffixTree suffixTree(SA, LCP);
    suffixTree.TestLcp(S, rnd);
}

// Tests the suffix array, suffix tree and LCP queries systematically on
// all short strings and on randomly chosen longer strings.
int TestSuffixArrayAndTree()
{
    mt19937_64 r(123);
    //TestSuffixArrayAndTree(string("lclllllllllllllll"), r);
    string alphabet(26, '.'); for (int i = 0; i < 26; ++i) alphabet[i] = 'a' + i;
    // Systematically test on all strings of length d from a b-letter alphabet,
    // for b = 2..5, where b^d <= 10^6.
    if (true) for (int d = 1; d <= 20; ++d)
    {
        string s(d, '.');
        for (int b = 2; b <= 5; ++b)
        {
            fprintf(stderr, "d = %d, b = %d          \r", d, b); fflush(stderr);
            int bd = 1; for (int i = 0; i < b; ++i) { bd *= b; if (bd > 1'000'000) break; }
            if (bd > 1'000'000) break;
            for (int m = 0; m < bd; ++m)
            {
                if (m % 100 == 0) {
                    mt19937_64 rnd(123 + m * 10 + b);
                    shuffle(alphabet.begin(), alphabet.end(), rnd); }
                for (int i = 0, mm = m; i < d; ++i) s[i] = alphabet[mm % b], mm /= b;
                mt19937_64 rnd(((m * 5) + b) * 20 + d);
                TestSuffixArrayAndTree(s, rnd);
            }
        }
    }
    // Test on randomly constructed longer strings.
    for (int nIter = 0; nIter < 10000'000; ++nIter)
    {
        if (nIter % 1000 == 0) { fprintf(stderr, "%d                  \r", nIter); fflush(stderr); }
        {
            mt19937_64 rnd(123 + 2 * nIter);
            int n = uniform_int_distribution<int>(1, uniform_int_distribution<int>(0, 1)(rnd) == 1 ? 1000 : 50)(rnd);
            shuffle(alphabet.begin(), alphabet.end(), rnd); 
            int a = uniform_int_distribution<int>(1, min(n, 26))(rnd);
            a = uniform_int_distribution<int>(1, min(n, 26))(rnd); // prefer smaller alphabets
            string s(n, '.');
            for (auto &c : s) c = alphabet[uniform_int_distribution<int>(0, a - 1)(rnd)];
            TestSuffixArrayAndTree(s, rnd);
        }
        {
            mt19937_64 rnd(123 + 2 * nIter + 1);
            int n = uniform_int_distribution<int>(1, uniform_int_distribution<int>(0, 1)(rnd) == 1 ? 1000 : 50)(rnd);
            vector<int> alphabet(n); for (int i = 0; i < n; ++i) alphabet[i] = i;
            shuffle(alphabet.begin(), alphabet.end(), rnd); 
            int a = uniform_int_distribution<int>(1, min(n, 26))(rnd);
            a = uniform_int_distribution<int>(1, min(n, 26))(rnd); // prefer smaller alphabets
            vector<int> S(n, -1);
            for (auto &c : S) c = 1 + alphabet[uniform_int_distribution<int>(0, a - 1)(rnd)];
            TestSuffixArrayAndTree(S, rnd);
        }
    }
    return 0;
}

// ----------------------------------------------------------------------------
// Prefix and suffix tables from the Knuth-Morris-Pratt algorithm
// ----------------------------------------------------------------------------
// The functions in this section come in groups: BuildX is the linear-time
// function; BuildX_Naive is a simpler quadratic-time function that should
// return the same results; TestBuildX tests whether they return the same
// results, either on a single string or (the parameterless function) on
// all binary strings up to a certain length.

// Given a string p[0..n-1], this function calculates, for k = 0..n,
// v[k] = the greatest i < k such that p[:i] is a suffix of p[:k].
template<typename String>
void BuildSuffixTable(const String &p, int n, vector<int> &v)
{
    v.resize(n + 1); v[0] = -1; if (n > 0) v[1] = 0;
    for (int k = 2; k <= n; ++k)
    {
        // If p[:i] is a suffix of p[:k], then p[:i-1] must be a suffix of p[:k-1] and p[i-1] must equal p[k-1].
        int j = v[k - 1]; // j is the current candidate for i-1
        while (j > 0 && p[k - 1] != p[j]) 
            // If the candidate j doesn't fit, try the next shorter prefix of p that is also a sufifx of p[:k-1].
            // This algorithm is O(n) because k-j keeps increasing over all the executions of the inner loop.
            j = v[j];
        v[k] = (p[k - 1] == p[j]) ? j + 1 : 0;
    }
}

template<typename String>
void BuildSuffixTable_Naive(const String &p, int n, vector<int> &v)
{
    v.resize(n + 1);
    for (int k = 0; k <= n; ++k)
    {
        int i = k - 1;
        while (i > 0)
        {
            int j = 0; while (j < i && p[j] == p[k - i + j]) ++j;
            if (j >= i) break; else --i;
        }
        v[k] = i;
    }
}

template<typename String>
void TestBuildSuffixTable(const String &p, int n)
{
    vector<int> v1, v2; BuildSuffixTable(p, n, v1);
    BuildSuffixTable_Naive(p, n, v2);
    for (int k = 0; k <= n; ++k) Assert(v1[k] == v2[k]);
}

void TestBuildSuffixTable()
{
    for (int n = 0; n <= 20; ++n)
    {
        printf("%d\n", n); fflush(stdout);
        string s; s.resize(n);
        for (int i = 0; i < (1 << n); ++i)
        {
            for (int j = 0; j < n; ++j) s[j] = 'a' + ((i >> j) & 1);
            TestBuildSuffixTable(s, n);
        }
    }
}

// The following function computes, for the string s[0..sd-1], its suffix table with respect to p[0..pd-1],
// i.e. v[k] = the greatest i < pd (and i <= k) such that p[:i] is a suffix of s[:k].
// pST[k] must be the greatest i < k such that p[:i] is a suffix of p[:k], i.e. the table
// computed by BuildSuffixTable.
template<typename String>
void BuildSuffixTable2(const String &s, int sd, const String &p, int pd, const vector<int> &pST, vector<int> &v)
{
    //if (s == "aa" && p == "aa") printf("!");
    Assert(pd > 0);
    v.resize(sd + 1); v[0] = 0; 
    for (int k = 1; k <= sd; ++k)
    {
        // If p[:i] is a suffix of s[:k], then p[:i-1] must be a suffix of s[:k-1] and p[i-1] must equal s[k-1].
        int j = v[k - 1]; // j is the current candidate for i-1
        while (j > 0 && ! (j < pd - 1 && s[k - 1] == p[j]))
            // If the candidate j doesn't fit, try the next shorter prefix of p that is also a suffix of s[:k-1].
            // This algorithm is O(n) because k-j keeps increasing over all the executions of the inner loop.
            j = pST[j];
        v[k] = (j < pd - 1 && s[k - 1] == p[j]) ? j + 1 : 0;
    }
}

template<typename String>
void BuildSuffixTable2_Naive(const String &s, int sd, const String &p, int pd, vector<int> &v)
{
    //if (s == "aa" && p == "a") printf("!");
    v.resize(sd + 1);
    for (int k = 0; k <= sd; ++k)
    {
        int i = min(k, pd - 1);
        while (i > 0)
        {
            int j = 0; while (j < i && p[j] == s[k - i + j]) ++j;
            if (j >= i) break; else --i;
        }
        v[k] = i;        
    }
}

template<typename String>
void TestBuildSuffixTable2(const String &s, int sd, const String &p, int pd, const vector<int> &pST)
{
    vector<int> v1, v2; BuildSuffixTable2(s, sd, p, pd, pST, v1);
    BuildSuffixTable2_Naive(s, sd, p, pd, v2);
    for (int k = 0; k <= sd; ++k) Assert(v1[k] == v2[k]);
}

void TestBuildSuffixTable2()
{
    string s, p; vector<int> pST;
    for (int n = 0; n <= 12; ++n) for (int m = 1; m <= 6; ++m) 
    {
        printf("%d %d\n", n, m); fflush(stdout);
        s.resize(n); p.resize(m);
        for (int pi = 0; pi < (1 << m); ++pi)
        {
            for (int j = 0; j < m; ++j) p[j] = 'a' + ((pi >> j) & 1);
            BuildSuffixTable(p, m, pST);
            for (int si = 0; si < (1 << n); ++si)
            {
                for (int j = 0; j < n; ++j) s[j] = 'a' + ((si >> j) & 1);
                TestBuildSuffixTable2(s, n, p, m, pST);
            }
        }
    }
}

// For k = 0..sd, returns v[k] = number of occurrences of p in s[:k].
// spST[k] must be the greatest i < min(pd, k) such that p[:i] is a suffix of s[:k].
template<typename String>
void BuildOccCounts(const String &s, int sd, const vector<int> &spST, const String &p, int pd, vector<int> &v)
{
    //if (s == "aa" && p == "a") printf("!");
    v.resize(sd + 1); v[0] = 0;
    const auto pLast = p[pd - 1];
    for (int k = 1; k <= sd; ++k)
        v[k] = v[k - 1] + (spST[k - 1] == pd - 1 && s[k - 1] == pLast ? 1 : 0);
}

template<typename String>
void BuildOccCounts_Naive(const String &s, int sd, const String &p, int pd, vector<int> &v)
{
    v.resize(sd + 1);
    int count = 0;
    for (int k = 0; k <= sd; ++k)
    {
        int i = 0; while (i < k && i < pd && s[k - 1 - i] == p[pd - 1 - i]) ++i;
        if (i == pd) ++count;
        v[k] = count;
    }
}

template<typename String>
void TestBuildOccCounts(const String &s, int sd, const vector<int> &spST, const String &p, int pd)
{
    vector<int> v1, v2; BuildOccCounts(s, sd, spST, p, pd, v1);
    BuildOccCounts_Naive(s, sd, p, pd, v2);
    for (int k = 0; k <= sd; ++k) Assert(v1[k] == v2[k]);
}

void TestBuildOccCounts()
{
    string s, p; vector<int> pST, spST;
    for (int n = 0; n <= 12; ++n) for (int m = 1; m <= 6; ++m) 
    {
        printf("%d %d\n", n, m); fflush(stdout);
        s.resize(n); p.resize(m);
        for (int pi = 0; pi < (1 << m); ++pi)
        {
            for (int j = 0; j < m; ++j) p[j] = 'a' + ((pi >> j) & 1);
            BuildSuffixTable(p, m, pST);
            for (int si = 0; si < (1 << n); ++si)
            {
                for (int j = 0; j < n; ++j) s[j] = 'a' + ((si >> j) & 1);
                BuildSuffixTable2(s, n, p, m, pST, spST);
                TestBuildOccCounts(s, n, spST, p, m);
            }
        }
    }
}

// Returns v[k] = the least i > k such that p[i:] is a prefix of p[k:].
// pRST should be the result of calling BuildSuffixTable(p.rbegin(), pd, pRST); 
void BuildPrefixTable(const vector<int> pRST, vector<int> &v)
{
    const int pd = pRST.size() - 1;
    v = pRST;
    // v[k] = the greatest i < k such that p^R[:i] is a suffix of p^R[:k],
    //                      i.e. such that (p[pd-i:])^R is a suffix of (p[pd-k:])^R,
    //                      i.e. such that p[pd-i:] is a prefix of p[pd-k:].
    reverse(v.begin(), v.end());
    // v[pd - k] = the greatest  i < k such that p[pd-i:] is a prefix of p[pd-k:]
    // i.e. v[k] = the greatest  i < pd - k such that p[pd-i:] is a prefix of p[k:]
    for (auto &x : v) x = pd - x;
    // v[k] = the greatest pd - i < pd - k such that p[i:] is a prefix of p[k:]
    // i.e. v[k] = the least i > k such that p[i:] is a prefix of p[k:]
}

template<typename String>
void BuildPrefixTable_Naive(const String &p, int n, vector<int> &v)
{
    v.resize(n + 1);
    for (int k = 0; k <= n; ++k)
    {
        int i = k + 1;
        while (i < n)
        {
            int j = i; while (j < n && p[j] == p[k - i + j]) ++j;
            if (j >= n) break; else ++i;
        }
        v[k] = i;
    }
}

template<typename String>
void TestBuildPrefixTable(const String &p, int n)
{
    vector<int> pRST; BuildSuffixTable(p.rbegin(), n, pRST); 
    vector<int> v1, v2; BuildPrefixTable(pRST, v1);
    BuildPrefixTable_Naive(p, n, v2);
    for (int k = 0; k <= n; ++k) Assert(v1[k] == v2[k]);
}

void TestBuildPrefixTable()
{
    for (int n = 0; n <= 20; ++n)
    {
        printf("%d\n", n); fflush(stdout);
        string s; s.resize(n);
        for (int i = 0; i < (1 << n); ++i)
        {
            for (int j = 0; j < n; ++j) s[j] = 'a' + ((i >> j) & 1);
            TestBuildPrefixTable(s, n);
        }
    }
}

// Given tpRST[k] = the greatest i < pd (and i <= k) such that p^R[:i] is a suffix of t^R[:k],
// this function calculates v[k] = the least i > 0 such that p[i:] is a prefix of t[k:].
void BuildPrefixTable2(int pd, const vector<int> &tpRST, vector<int> &v)
{
    // tpRST[k] = the greatest i < pd (and i <= k) such that p^R[:i] is a suffix of t^R[:k]
    //                                       i.e. such that (p[pd-i:])^R is a suffix of (t[td-k:])^R
    //                                       i.e. such that p[pd-i:] is a prefix of t[td-k:].
    v = tpRST;
    reverse(v.begin(), v.end());
    // v[k] = the greatest i < pd (and i <= td-k) such that p[pd-i:] is a prefix of t[k:].
    for (auto &x : v) x = pd - x;
    // v[k] = the greatest pd - i < pd (and pd - i <= td-k) such that p[i:] is a prefix of t[k:].
    // i.e. v[k] = the least i > 0 (and pd - i <= td-k) such that p[i:] is a prefix of t[k:].
}

template<typename String>
void BuildPrefixTable2_Naive(const String &t, int td, const String &p, int pd, vector<int> &v)
{
    v.resize(td + 1);
    for (int k = 0; k <= td; ++k)
    {
        int i = 1;
        while (i < pd)
        {
            if (pd - i > td - k) { ++i; continue; }
            int j = i; while (j < pd && t[k + j - i] == p[j]) ++j;
            if (j >= pd) break; else ++i;
        }
        v[k] = i;
    }
}

template<typename String>
void TestBuildPrefixTable2(const String &t, int td, const String &p, int pd, const vector<int> &pRST)
{
    vector<int> tpRST; BuildSuffixTable2(t.rbegin(), td, p.rbegin(), pd, pRST, tpRST);
    vector<int> v1, v2; BuildPrefixTable2(pd, tpRST, v1);
    BuildPrefixTable2_Naive(t, td, p, pd, v2);
    //if (t == "" && p == "a") printf("!");
    for (int k = 0; k <= td; ++k) Assert(v1[k] == v2[k]);
}

void TestBuildPrefixTable2()
{
    string s, p; vector<int> pRST;
    for (int n = 0; n <= 12; ++n) for (int m = 1; m <= 6; ++m) 
    {
        printf("%d %d\n", n, m); fflush(stdout);
        s.resize(n); p.resize(m);
        for (int pi = 0; pi < (1 << m); ++pi)
        {
            for (int j = 0; j < m; ++j) p[j] = 'a' + ((pi >> j) & 1);
            vector<int> pRST; BuildSuffixTable(p.rbegin(), m, pRST); 
            for (int si = 0; si < (1 << n); ++si)
            {
                for (int j = 0; j < n; ++j) s[j] = 'a' + ((si >> j) & 1);
                TestBuildPrefixTable2(s, n, p, m, pRST);
            }
        }
    }
}

// Returns tpPTB[k] = is t[:k] a suffix of p, i.e. does it equal p[pd-k:]?
template<typename String>
void BuildPrefixTable2B(const String &t, int td, const String &p, int pd, const vector<int> &pPT, const vector<int> &tpPT, vector<bool> &tpPTB)
{
    tpPTB.resize(td + 1); for (int k = pd; k <= td; ++k) tpPTB[k] = false;
    // The longest proper suffix of p (i.e. shorter than p itself) that appears at the start of t is p[i:] for i = tpPT[0].
    // After that, the next shorter suffix of p that appears at the start of p[i:] (and thus at the start of t) is given by pPT[i].
    for (int k = tpPT[0]; k < pd; k = pPT[k]) 
        tpPTB[pd - k] = true;
    // Edge cases: t[:0] is an empty string and hence a suffix of p; t[:pd] is a suffix of p if it equals p,
    // which is if t[0] = p[0] and t[1:] starts with p[1:].
    tpPTB[0] = true; if (td >= pd && t[0] == p[0] && tpPT[1] == 1) tpPTB[pd] = true;
}

template<typename String>
void BuildPrefixTable2B_Naive(const String &t, int td, const String &p, int pd, vector<bool> &tpPTB)
{
    tpPTB.resize(td + 1);
    for (int k = 0; k <= td; ++k)
    {
        if (k > pd) { tpPTB[k] = false; continue; }
        int i = 0; while (i < k && t[i] == p[pd - k + i]) ++i;
        tpPTB[k] = (i == k);
    }
}

template<typename String>
void TestBuildPrefixTable2B(const String &t, int td, const String &p, int pd, const vector<int> &pRST, const vector<int> &pPT)
{
    vector<int> temp; BuildSuffixTable(p.rbegin(), pd, temp);  Assert(temp == pRST);
    BuildPrefixTable(pRST, temp); Assert(temp == pPT);
    vector<int> tpRST; BuildSuffixTable2(t.rbegin(), td, p.rbegin(), pd, pRST, tpRST);
    vector<int> tpPT; BuildPrefixTable2(pd, tpRST, tpPT);
    BuildPrefixTable2_Naive(t, td, p, pd, temp); Assert(temp == tpPT);
    vector<bool> v1, v2; BuildPrefixTable2B(t, td, p, pd, pPT, tpPT, v1);
    BuildPrefixTable2B_Naive(t, td, p, pd, v2);
    for (int k = 0; k <= td; ++k) Assert(v1[k] == v2[k]);
}

void TestBuildPrefixTable2B()
{
    string s, p; vector<int> pRST;
    for (int n = 0; n <= 12; ++n) for (int m = 1; m <= 6; ++m) 
    {
        printf("%d %d\n", n, m); fflush(stdout);
        s.resize(n); p.resize(m);
        for (int pi = 0; pi < (1 << m); ++pi)
        {
            for (int j = 0; j < m; ++j) p[j] = 'a' + ((pi >> j) & 1);
            vector<int> pRST; BuildSuffixTable(p.rbegin(), m, pRST); 
            vector<int> pPT; BuildPrefixTable(pRST, pPT);
            for (int si = 0; si < (1 << n); ++si)
            {
                for (int j = 0; j < n; ++j) s[j] = 'a' + ((si >> j) & 1);
                TestBuildPrefixTable2B(s, n, p, m, pRST, pPT);
            }
        }
    }
}

// tpSTB[k] = is t[k:] a prefix of p, i.e. does it equal p[:td-k]?
template<typename String>
void BuildSuffixTable2B(const String &t, int td, const String &p, int pd, const vector<int> &pST, const vector<int> &tpST, vector<bool> &tpSTB)
{
    tpSTB.resize(td + 1); for (int k = 0; k <= td - pd; ++k) tpSTB[k] = false;
    // The longest proper prefix of p (i.e. shorter than p itself) that appears at the end of t is p[:i] for i = tpST[td].
    // After that, the next shorter prefix of p that appears at the end of p[:i] (and thus at the end of t) is given by pST[i].
    for (int k = tpST[td]; k > 0; k = pST[k]) 
        tpSTB[td - k] = true;
    // Edge cases: t[td:] is an empty string and hence a prefix of p; t[td - pd:] is a prefix of p if it equals p,
    // which is if t[td-1] = p[pd-1] and t[:td-1] ends with with p[:pd-1].
    tpSTB[td] = true; if (td >= pd && t[td - 1] == p[pd - 1] && tpST[td - 1] == pd - 1) tpSTB[td - pd] = true;
}

template<typename String>
void BuildSuffixTable2B_Naive(const String &t, int td, const String &p, int pd, vector<bool> &tpSTB)
{
    tpSTB.resize(td + 1);
    for (int k = 0; k <= td; ++k)
    {
        if (td - k > pd) { tpSTB[k] = false; continue; }
        int i = k; while (i < td && t[i] == p[i - k]) ++i;
        tpSTB[k] = (i == td);
    }
}

template<typename String>
void TestBuildSuffixTable2B(const String &t, int td, const String &p, int pd, const vector<int> &pST)
{
    vector<int> tpST; BuildSuffixTable2(t, td, p, pd, pST, tpST);
    vector<bool> v1, v2; BuildSuffixTable2B(t, td, p, pd, pST, tpST, v1);
    BuildSuffixTable2B_Naive(t, td, p, pd, v2);
    for (int k = 0; k <= td; ++k) Assert(v1[k] == v2[k]);
}

void TestBuildSuffixTable2B()
{
    string s, p; vector<int> pRST;
    for (int n = 0; n <= 12; ++n) for (int m = 1; m <= 6; ++m) 
    {
        printf("%d %d\n", n, m); fflush(stdout);
        s.resize(n); p.resize(m);
        for (int pi = 0; pi < (1 << m); ++pi)
        {
            for (int j = 0; j < m; ++j) p[j] = 'a' + ((pi >> j) & 1);
            vector<int> pST; BuildSuffixTable(p, m, pST);
            for (int si = 0; si < (1 << n); ++si)
            {
                for (int j = 0; j < n; ++j) s[j] = 'a' + ((si >> j) & 1);
                TestBuildSuffixTable2B(s, n, p, m, pST);
            }
        }
    }
}

// ----------------------------------------------------------------------------
// The KMP tree
// ----------------------------------------------------------------------------
// In this tree, each node u represents the prefix p[:u], and its parent
// is the node representing the longest suffix of p[:u] that is shorter than u
// and is also a prefix of p.  

struct TKmpTree
{
    // This structure represents a request to calculate f(i, j), defined as
    // the number of those occurrences of p in p[:i] t p[:j] which begin
    // within p[:i] and end within p[:j].  This request arises when counting
    // the occurrences of p in s[:k] t s[k:].  The result, i.e. the value f(i, j),
    // is to be stored in 'result'.  The 'next' field is used when grouping
    // queries based on the nearest marked ancestor of i in the first tree.
    struct TQuery
    {
        int i = -1, j = -1, k = -1, result = -1, next;
    };

    struct TNode
    {
        int parent = -1, firstChild = -1, nextSib = -1;
        int startTime = -1, endTime = -1; // indexes into 'dftOrder'
        int startTime2 = -1, endTime2 = -1; // here the time is not incremented when exiting a node; thus the times to from 0 to nNodes - 1 and 'endTime2' is the maximum of 'startTime2' over all descendants of this node
        int height = -1; // distance from the deepest descendant
        int depth = -1; // distance from the root
        int nDesc = 0; // number of descendants, including this node itself
    };

    vector<TNode> nodes; int root = -1;
    void DepthFirstTraversal()
    {
        stack<pair<int, bool>> toDo; toDo.emplace(root, true);
        int time = 0, time2 = 0; //dftOrder.clear(); dftOrder.reserve(nodes.size());
        while (! toDo.empty())
        {
            auto [u, enter] = toDo.top(); //dftOrder.push_back(toDo.top());
            auto &U = nodes[u];
            TKmpTree::TNode *P = (U.parent >= 0) ? &nodes[U.parent] : nullptr;
            if (! enter) { 
                U.endTime = time++; U.endTime2 = time2 - 1; toDo.pop(); 
                if (P) { P->height = max(P->height, U.height + 1); P->nDesc += U.nDesc; }
                continue; }
            toDo.top().second = false; U.startTime = time++; U.startTime2 = time2++;
            U.depth = (P ? P->depth + 1 : 0);
            U.height = 0; U.nDesc = 1;
            for (int v = U.firstChild; v >= 0; v = nodes[v].nextSib) toDo.emplace(v, true);
        }
        Assert(time2 == (int) nodes.size());
    }
    TKmpTree() = default;
    void Init(const vector<int> &parent) 
    {
        nodes.clear(); nodes.resize(parent.size());
        for (int u = 0, n = parent.size(); u < n; ++u) {
            int p = parent[u]; if (p < 0) { Assert(root < 0); root = u; continue; }
            auto &U = nodes[u], &P = nodes[p];
            U.parent = p; U.nextSib = P.firstChild; P.firstChild = u; }
        DepthFirstTraversal();
    }
    // Returns 'true' if 'anc' is an ancestor of 'desc' (or the asme node).
    bool IsAncestorOf(int anc, int desc) const 
    {
        const auto &D = nodes[desc], &A = nodes[anc];
        return A.startTime <= D.startTime && D.endTime <= A.endTime; 
    }
    // Proceed from the bottom upwards and cut off any subtrees with >= 'maxSubtreeSize' nodes.
    // The roots of such trees are considered to be 'marked', as is the root of the entire tree.
    // The vector 'closestMarkedAncestor[u]' receives the pair (p, d) where p is the closest marked
    // ancestor of u, and d is the distance between p and u.
    int MarkNodes(int maxSubtreeSize, vector<pair<int, int>> &closestMarkedAncestor)
    {
        int n = nodes.size(), nMarked = 0; closestMarkedAncestor.resize(n); for (auto &x : closestMarkedAncestor) x = {-1, -1};
        vector<int> subtreeSize(n, 0), preOrderTraversal;
        stack<pair<int, bool>> toDo; toDo.emplace(root, true);
        while (! toDo.empty())
        {
            auto [u, enter] = toDo.top(); auto &U = nodes[u];
            if (! enter) { 
                if (subtreeSize[u] >= maxSubtreeSize || u == root) closestMarkedAncestor[u] = {u, 0}, ++nMarked;
                else if (int p = U.parent; p >= 0) subtreeSize[p] += subtreeSize[u]; 
                toDo.pop(); continue; }
            preOrderTraversal.emplace_back(u); 
            toDo.top().second = false; subtreeSize[u] = 1;
            for (int v = U.firstChild; v >= 0; v = nodes[v].nextSib) toDo.emplace(v, true);
        }
        for (int u : preOrderTraversal) { auto &C = closestMarkedAncestor[u]; if (C.second >= 0) continue;
            auto &P = closestMarkedAncestor[nodes[u].parent];
            C = {P.first, P.second + 1}; }
        return nMarked;
    }
};

// ----------------------------------------------------------------------------
// Fenwick tree
// ----------------------------------------------------------------------------

// Consider an array a[0..n-1]; let v[t] = sum a[f(t)+1...t], where f(t) is 
// the value obtained by clearing the lowest bit that is set in t.
// This function updates v in a way that corresponds to increasing a[k] by 'delta'.
void FenwickUpdate(vector<int> &v, int k, int delta)
{
    if (k == 0) { v[k] += delta; return; }
    while (k < (int) v.size()) { v[k] += delta; k += (k & ~(k - 1)); }
}

// Returns the sum of a[0..k].
int FenwickQuery(const vector<int> &v, int k)
{
    if (k < 0) return 0;
    int sum = v[0]; while (k > 0) { sum += v[k]; k &= k - 1; }
    return sum;
}

// ----------------------------------------------------------------------------
// TStaticTreeSetUnion
// ----------------------------------------------------------------------------
// A linear-time solution for the union-set problem in the special case
// where the elements are arranged in a tree and the union operation is
// always between the set containing an element and the set containing
// its parent.  Based on:
// [GT85] Harold N. Gabow, Robert Endre Tarjan, "A linear-time algorithm for a special 
//        case of disjoint set union".  _Journal of Computer and System Sciences_, 30(2):209-21 (April 1985).
//        https://doi.org/10.1016/0022-0000(85)90014-5
// [GT83] Harold N. Gabow, Robert Endre Tarjan, "A linear-time algorithm for a special 
//        case of disjoint set union".  _Proc. STOC 1983_, pp. 246-51.  
//        https://doi.org/10.1145/800061.808753

class TStaticTreeSetUnion
{
protected:
    int n; // the number of elements
    int b, ceilLgB; // b - 1 = the maximum number of elements per microset; ceilLgB = ceil(log2(b))
    typedef int TNodeId;
    typedef int TMicrosetId;
    struct TNode 
    {
        TNodeId parent = -1; // the parent of this node in the tree
        TMicrosetId micro = -1; // the microset it belongs to
        int number = -1; // its number in the microset
        TNodeId firstChild = -1, nextSib = -1; // these links are only used temporarily during the construction of microsets
        int desc = -1; // d[v] used during the construction of microsets
        int level = -1; // distance from the root
        // The following members are only used if the present node is the root of a microset.
        // Note that the same node can be the root of several microsets, so we can't
        // store these values in the microsets themselves.  'macroTop' is the element of the 
        // macroset with the lowest 'level' (unique due to the way 'macrounite' is called from 'find').
        int macroSize = -1, macroTop = -1; TNodeId macroParent = -1; // Used to form a disjoint-set forest over the roots.
    };
    struct TMicroset
    {
        vector<TNodeId> nodes; // in preorder
        int mark; // bit i in 'mark' is clear if nodes[i] is marked, i.e. if it is the name of the set it belongs to
        TNodeId root; // The only node which is a parent of some node of this microset but is not itself in this microset.  
            // 'root' can be -1 if the present microset contains the root of the tree.
        // Imagine a vector 'forest' where forest[i] is the number of children, in this microset,
        // of the node this->nodes[i].  Since the microset contains at most b-1 nodes and
        // each node counts towards at most one 'forest[i]', but nodes whose parent is the root of the microset
        // (there must be at least one such node) count towardsnone, it follows that the sum of all
        // forest[i] is at most b-2.  If we represent each element of forest[i] as a sequence of bits
        // consisting of one '1' followed by forest[i] '0' bits, the total length of this representation
        // of the entire 'forest' vector will be at most b-1 ones + b-2 zeros = 2b-3.
        int forest;
    };
    // For i = 0, ..., n-1: microsets[nodes[i].micro].nodes[nodes[i].number] == i.
    vector<TNode> nodes;
    vector<TMicroset> microsets;

    // Returns the name of the macroset containing 'v'.
    TNodeId MacroFind(TNodeId v)
    {
        Assert(0 <= v && v < n); 
        Assert(nodes[v].macroSize > 0); // Make sure that 'v' is the root of a microset and hence the member of a macroset.
        // Find the root of the tree representing the macroset to which 'v' belongs.
        TNodeId u = v; while (true) if (int p = nodes[u].macroParent; p == u) break; else u = p;
        // Flatten the path from 'v' to the root 'u'.
        while (v != u) { 
            auto &V = nodes[v]; int p = V.macroParent;
            V.macroParent = u; v = p; }
        return u;
    }

    // Returns the name of the merged set.
    TNodeId MacroUnite(TNodeId u, TNodeId v)
    {
        u = MacroFind(u); v = MacroFind(v);
        if (u == v) return u; // They are already in the same macroset.
        if (nodes[u].macroSize < nodes[v].macroSize) swap(u, v);
        // Now 'v' is the root of the smaller of the two macrosets; make it the child of 'u'.
        auto &U = nodes[u], &V = nodes[v]; Assert(1 <= V.macroSize && V.macroSize <= U.macroSize);
        V.macroParent = u; U.macroSize += V.macroSize; 
        if (nodes[V.macroTop].level < nodes[U.macroTop].level) U.macroTop = V.macroTop;
        return u;
    }

    // Initializes a new microset from all the descendants of v's children
    // prior to w, and removes these nodes from the tree.  'w' may be < 0, 
    // in which case all of v's children (and their descendants) are used.
    // 'v' may be < 0, in which case 'w' must also be < 0 and all remaining
    // nodes are added to the new microset.
    void AddMicroset(TNodeId v, TNodeId w, TNodeId &treeRoot)
    {
        TMicrosetId ms = (int) microsets.size(); microsets.emplace_back();
        auto &MS = microsets.back();
        if (v < 0) Assert(w < 0);
        if (w >= 0) Assert(nodes[w].parent == v);
        MS.nodes.clear(); MS.nodes.reserve(b - 1);
        MS.forest = 0; MS.mark = 0; MS.root = v;
        vector<int> forest; forest.reserve(b - 1);
        // Visit the nodes of the new microset in preorder, with the aid of an Euler tour.
        TNodeId preOrderPrev = v, preOrderCur = (v >= 0 ? nodes[v].firstChild : treeRoot);
        //vector<int> trace; trace.emplace_back(preOrderPrev);
        while (preOrderCur != w)
        {
            //trace.emplace_back(preOrderCur);
            TNode *Prev = (preOrderPrev < 0) ? nullptr : &nodes[preOrderPrev];
            TNode &Cur = nodes[preOrderCur];
            // If we entered 'Cur' from a child, proceed to its next child.
            if (preOrderPrev >= 0 && preOrderCur == Prev->parent) {
                preOrderPrev = preOrderCur; preOrderCur = Prev->nextSib; 
                // If it has no next child, we'll return to its parent, with the exception
                // that we mustn't move above 'v'.
                if (preOrderCur < 0 && preOrderPrev != v) preOrderCur = Cur.parent;
                continue; }
            // Otherwise we have entered 'Cur' from its parent, and it should now
            // be output to preorder (and, hence, added to the microset).
            Assert(preOrderPrev == Cur.parent);
            Cur.micro = ms; Cur.number = (int) MS.nodes.size();
            MS.nodes.emplace_back(preOrderCur); forest.emplace_back(0);
            // If the parent of 'Cur' is in the same microset, increase its child count in 'forest'.
            if (Cur.parent >= 0 && Cur.parent != v) {
                Assert(Prev->micro == ms); Assert(Prev->number >= 0 && Prev->number < Cur.number);
                ++forest[Prev->number]; }
            // From 'Cur's place in the preorder, we must proceed to its first child.
            preOrderPrev = preOrderCur; preOrderCur = Cur.firstChild;
            // If it has no children, we'll return to its parent, with the exception
            // that we mustn't move above 'v'.
            if (preOrderCur < 0 && preOrderPrev != v) preOrderCur = Cur.parent;
        }
        // Remove, from the list of v's children, those that we have added to the microset.
        (v >= 0 ? nodes[v].firstChild : treeRoot) = w;
        // Convert the 'forest' vector into an integer, storing it in 'MS.forest'.
        int bb = (int) MS.nodes.size(); Assert(bb < b);
        int cSum = 0; for (int i = bb - 1; i >= 0; --i) { int c = forest[i]; MS.forest = ((MS.forest << 1) | 1) << c; cSum += c; }
        Assert(cSum < bb); Assert((MS.forest >> (cSum + bb)) == 0);
    }

    typedef int TAnswerTableRow;
    vector<TAnswerTableRow> answerTable;

    void InitAnswerTable()
    {
        Assert((b - 1) * ceilLgB < 8 * sizeof(answerTable[0])); // make sure all b-1 answers can fit into an int
        answerTable.clear(); answerTable.resize(1 << (3 * b - 4), ~TAnswerTableRow(0));
        vector<int> parent(b - 1), forestV(b - 1), branch; branch.reserve(b - 1);
        for (int forest = 0; forest < (1 << (2 * b - 3)); ++forest)
        {
            // Decode this forest from a bit string into a vector.
            int F = forest; int bb = 0; bool ok = true;
            while (F > 0)
            {
                int fi = 0; while ((F & 1) == 0) { ++fi; F >>= 1; }
                Assert((F & 1) == 1); F >>= 1;
                if (bb >= b - 1) { ok = false; break; } // too many 1's in 'forest'
                forestV[bb++] = fi; 
            }
            if (! ok) continue; // invalid 'forest' bitstring
            // For each node, determine its parent.
            Assert(branch.empty()); 
            for (int u = 0; u < bb; ++u)
            {
                // Remove, from 'branch', and nodes that can't receive any more children.
                while (! branch.empty() && forestV[branch.back()] == 0) branch.pop_back();
                // 'u' becomes the child of the deepest node now on 'branch'.
                int p = branch.empty() ? -1 : branch.back();
                // Decrease the number of children that u's parent can still receive.
                parent[u] = p; if (p >= 0) --forestV[p]; 
                // Add 'u' to the branch.
                branch.push_back(u);
            }
            while (! branch.empty() && forestV[branch.back()] == 0) branch.pop_back();
            if (! branch.empty()) { branch.clear(); continue; } // invalid 'forest' bitstring
            // Convert the 'parent' table back into a forest vector and then into a bitstring
            // and check that it matches the original bitstring.
            if constexpr (SLOW_CHECKS)
            {
                vector<int> forestV2(bb, 0);
                for (int u = 0; u < bb; ++u) if (int v = parent[u]; v >= 0) ++forestV2[v];
                int forest2 = 0; for (int i = bb - 1; i >= 0; --i) { int c = forestV2[i]; forest2 = ((forest2 << 1) | 1) << c; }
                Assert(forest2 == forest);
            }
            // Now we know that 'forest' is a valid bitstring and we have the corresponding 'parent' table.
            // Calculate answers for every possible 'mark' vector.
            const TAnswerTableRow answerMask = (TAnswerTableRow(1) << ceilLgB) - 1;
            for (int mark = 0; mark < (1 << (b - 1)); ++mark)
            {
                TAnswerTableRow answer = 0;
                for (int u = 0; u < bb; ++u)
                {
                    // The answer for u is the nearest marked ancestor of u (including itself), 
                    // or -1 if there is no such node in the microset.
                    // Note that in the 'answer' integer, the answers for all u's are stored not as -1..bb-1, but as 0..bb 
                    // and hence as 0..b-1; thus, ceilLgB bits are allocated for each answer.
                    TAnswerTableRow a;
                    // Thus, if u itself is marked, the answer is u itself.
                    if ((mark & (1 << u)) == 0) a = u + 1;
                    // Otherwise the answer is the same as for u's parent, if it has one.
                    else if (int p = parent[u]; p < 0) a = 0;
                    else a = (answer >> (p * ceilLgB)) & answerMask;
                    answer |= a << (u * ceilLgB);
                }
                answerTable[(forest << (b - 1)) | mark] = answer;
            }
        }
    }

    bool Marked(TNodeId u) const
    {
        Assert(0 <= u && u < n);
        auto &U = nodes[u];
        return (microsets[U.micro].mark & (1 << U.number)) == 0;
    }

    TNodeId MicroFind(TNodeId v) const
    {
        Assert(0 <= v && v < n);
        auto &V = nodes[v];
        auto &MS = microsets[V.micro]; int bb = (int) MS.nodes.size();
        Assert(0 <= V.number && V.number < bb);
        TAnswerTableRow answer = answerTable[(MS.forest << (b - 1)) | MS.mark];
        if constexpr (is_signed_v<TAnswerTableRow>) 
            Assert(answer != ~TAnswerTableRow(0)); // answer == -1 indicates an entry in 'answerTable' that corresponds to an invalid 'forest' bitstring
        answer >>= (V.number * ceilLgB);
        answer &= ((1 << ceilLgB) - 1);
        Assert(0 <= answer && answer <= bb);
        TNodeId answerNode = (answer == 0) ? MS.root : MS.nodes[answer - 1];
        if constexpr (SLOW_CHECKS)
        {
            TNodeId u = v; while (! Marked(u) && nodes[u].micro == V.micro) u = nodes[u].parent;
            Assert(u == answerNode);
        }
        return answerNode;
    }

    void TestMicroFind() { for (TNodeId v = 0; v < n; ++v) MicroFind(v); }

    static inline int FloorLog2(int x) {
        int y = 0; while (x > 1) { x >>= 1; ++y; }
        return y; };
    static inline int CeilLog2(int x) { 
        int y = FloorLog2(x); if (x > (1 << y)) ++y; return y; };

public:

    explicit TStaticTreeSetUnion(const vector<int> &parent) 
    {
        n = (int) parent.size();

        // Determine b, which will limit the microset size (a microset may have at most b-1 nodes).
        // Firstly, b should be >= 2 so that each microset can have at least one node
        b = 2; 
        // Lemma 2 in [GT85] shows that b = Omega(log log n) guarantees linear time-complexity
        // and the remark below states that "much smaller values of b suffice".  It can be
        // shown, for example, that b = Omega((log* n)^2) suffices.
        int logStarN = 0; for (int u = n; u > 1; u = FloorLog2(u)) ++logStarN; 
        b = max(b, min(FloorLog2(FloorLog2(n)), logStarN * logStarN));
        // The answer table will have the size 2^{2b-3} * 2^{b-1} * (b-1), which we should aim to be O(n).
        // Moreover, in the answer table, all the answers for one microset should fit into on element.
        // Admittedly, in our experiments the speedup due to using a larger b (as opposed to skipping
        // the loop below altogerher) was very small (< 5%).
        constexpr int maxAnswerTableRowBits = 8 * sizeof(TAnswerTableRow) - (is_signed_v<TAnswerTableRow> ? 1 : 0);
        while (true)
        {
            int bb = b + 1;
            if ((n >> (3 * bb - 4)) < bb - 1) break;
            int lgBb = CeilLog2(bb);
            if ((bb - 1) * lgBb > maxAnswerTableRowBits) break;
            b = bb;
        }
        microsets.reserve((n + b - 2) / (b - 1));
        ceilLgB = CeilLog2(b);
        Assert((b - 1) * ceilLgB <= maxAnswerTableRowBits); // to make sure that all the answers for one microset fit into a single element of 'answerTable'

        // Initialize the parent/child/sibling links.  Note that the child/sibling links,
        // as well as 'root', will be dissolved during the construction of microsets; 
        // this is also why 'root' is just a local variable here instead of a member of the class.
        TNodeId root = -1; 
        nodes.resize(n);
        for (TNodeId u = 0; u < n; ++u) {
            TNodeId p = parent[u]; Assert(-1 <= p && p < n); Assert(p != u);
            auto &U = nodes[u]; U.parent = p; 
            if (p < 0) { Assert(root < 0); root = u; continue; }
            auto &P = nodes[p];
            U.nextSib = P.firstChild; P.firstChild = u; }
        Assert(root >= 0);

        // Traverse the tree in postorder.  To avoid the need for recursion or for
        // building the postorder explicitly in a vector, we perform a depth-first
        // Euler tour of the tree; a node appears in postorder at the point where 
        // the Euler tour moves into it from its last child, or from its parent if
        // it has no children.
        TNodeId postOrderCur = root;
        TNodeId postOrderPrev = nodes[postOrderCur].parent; Assert(postOrderPrev < 0);
        while (postOrderCur >= 0)
        {
            auto &Cur = nodes[postOrderCur];
            if (postOrderPrev < 0) Assert(postOrderCur == root && Cur.parent == postOrderPrev);
            else Assert(nodes[postOrderPrev].parent == postOrderCur || Cur.parent == postOrderPrev);
            if (postOrderPrev == Cur.parent) 
            {
                if (Cur.level < 0) Cur.level = (postOrderPrev < 0) ? 0 : nodes[postOrderPrev].level + 1;
                else Assert(Cur.level == (postOrderPrev < 0 ? 0 : nodes[postOrderPrev].level + 1)); 
                // We entered 'Cur' from its parent.  Proceed into the first child.
                if (Cur.firstChild >= 0) { postOrderPrev = postOrderCur; postOrderCur = Cur.firstChild; continue; }
                // If 'Cur' has no children, we'll output it to postorder now.
            }
            else
            {
                // We entered 'Cur' from one of its children.  Proceed into the next child.
                auto &Prev = nodes[postOrderPrev]; 
                if (Prev.nextSib >= 0) { postOrderPrev = postOrderCur; postOrderCur = Prev.nextSib; continue; }
                // If 'Cur' has no further children, we'll output it to postorder now.
            }
            // Now we are the 'Cur's place in the postorder, so it's time to process it for
            // the purposes of microset construction.
            TNodeId v = postOrderCur; auto& V = Cur; V.desc = 1;
            while (true)
            {
                TNodeId w = V.firstChild;
                // Gather the subtrees of v's children until we exceed (b+1)/2 nodes.
                while (2 * V.desc < b + 1 && w >= 0) { 
                    auto &W = nodes[w]; V.desc += W.desc; w = W.nextSib; }
                // If we didn't gather enough nodes, move on to the next node in postorder.
                if (2 * V.desc < b + 1) break; 
                // Otherwise construct a microset from the subtrees of v's children up to w,
                // and remove them from the tree.
                AddMicroset(v, w, root);
                Assert(V.firstChild == w); V.desc = 1;
            }
            // From 'Cur's place in the postorder, we must proceed to its parent, because
            // its children by definition appear before it in the postorder.
            postOrderPrev = postOrderCur; postOrderCur = V.parent;
        }
        // The root and any remaining nodes will form the last microset.
        Assert(root >= 0); Assert(nodes[root].micro < 0);
        AddMicroset(-1, -1, root);
        Assert(root < 0);

        // Initialize the answer table used by the microfind operation.
        InitAnswerTable();

        // The root of each microset becomes a singleton macroset.
        // Other nodes do not participate in macrosets.
        for (auto &N : nodes) { N.macroParent = -1; N.macroSize = -1; }
        for (auto &MS : microsets) if (TNodeId u = MS.root; u >= 0) {
            auto &U = nodes[u]; if (U.macroSize > 0) continue;
            U.macroParent = u; U.macroSize = 1; U.macroTop = u; }

        if constexpr (SLOW_CHECKS) TestMicroFind();
    }
    // This can be called to reset the data structure to what it was upon initialization,
    // which can be useful if you want to run another batch of queries on the same tree.
    void Reset()
    {
        // The root of each microset becomes a singleton macroset.
        // Other nodes do not participate in macrosets.
        for (auto &N : nodes) { N.macroParent = -1; N.macroSize = -1; }
        for (auto &MS : microsets) {
            MS.mark = 0; // each node is marked, i.e. is a singleton set
            TNodeId u = MS.root; if (u < 0) continue;
            auto &U = nodes[u]; if (U.macroSize > 0) continue;
            U.macroParent = u; U.macroSize = 1; U.macroTop = u; }
    }
    void Link(int v)
    {
        Assert(0 <= v && v < n);
        auto &V = nodes[v]; auto &MS = microsets[V.micro];
        Assert(0 <= V.number && V.number < (int) MS.nodes.size());
        MS.mark |= 1 << V.number;
    }
    int Find(int v)
    {
        Assert(0 <= v && v < n);
        if constexpr (false) TestMicroFind();
        int x = v; int xMicro = nodes[x].micro;
        int y = MicroFind(x); int yMicro = (y < 0) ? -1 : nodes[y].micro;
        if (xMicro != yMicro) { x = MacroFind(y); xMicro = nodes[x].micro; }
        while (true)
        {
            y = MicroFind(x); yMicro = (y < 0) ? -1 : nodes[y].micro;
            if (xMicro == yMicro) break;
            // Note: in line 7 of 'find', [GT85] (p. 217) has MacroFind, while [GT83] (p. 248) has MicroFind;
            // the latter is correct, while the former can cause an endless loop.
            // Hence we call MacroUnite(y, x) below, and not MacroUnite(MacroFind(x), x).
            if (true) x = MacroUnite(y, x);  // [GT83], correct
            else if (false) x = MacroUnite(MacroFind(x), x); // [GT85], wrong
            else x = MacroUnite(nodes[MacroFind(x)].macroTop, x); // [GB85] with the additional assumption that MacroFind should return the minimum node of the macroset; still wrong
            Assert(x == MacroFind(x));
            x = nodes[x].macroTop; // An important detail mentioned in neither [GT85] nor [GT83]: we need to
            // continue from the highest (i.e. closest to root) member of the macroset, not from any arbitrary
            // member; and yet in general there's no guarantee that MacroFind will return the highest member
            // as the "name" of the macroset (it depends on the implementation of the union-find structure for macrosets).
            xMicro = nodes[x].micro;
        }
        if constexpr (false) TestMicroFind();
        if constexpr (SLOW_CHECKS)
        {
            TNodeId u = v; while (! Marked(u)) u = nodes[u].parent;
            Assert(u == y);
        }
        return y;
    }
};

// Builds a TStaticTreeSetUnion for the tree specified by the 'parent' vector,
// then performs a series of 'find' and 'link' operations and verifies their
// correcntess by comparing their results to those of a naive implementation.
void TestStaticTreeSetUnion(const vector<int>& parent, mt19937_64 &rnd)
{
    TStaticTreeSetUnion tsu { parent };
    const int n = (int) parent.size();
    vector<int> setOf(n), minOfSet(n);
    for (int u = 0; u < n; ++u) setOf[u] = u, minOfSet[u] = u;
    for (int nSets = n; nSets >= 1; --nSets)
    {
        // Test the 'Find' operation on every node, or on a random subset of nodes if n is large.
        int nFinds = min(n, 1000);
        for (int i = 0; i < nFinds; ++i)
        {
            int u = (nFinds == n) ? i : uniform_int_distribution<int>(0, n - 1)(rnd);
            int v = tsu.Find(u);
            int su = setOf[u];
            int vTrue = minOfSet[su];
            Assert(v == vTrue);
        }
        // See which nodes haven't yet been merged with their parents.
        vector<int> cands; 
        for (int u = 0; u < n; ++u) if (int p = parent[u]; p >= 0 && setOf[u] != setOf[p]) cands.emplace_back(u);
        if (cands.empty()) { Assert(nSets == 1); break; }
        // Choose a random node amongst them and merge it with its parent.
        int i = uniform_int_distribution<int>(0, int(cands.size()) - 1)(rnd);
        int u = cands[i]; int p = parent[u];
        int su = setOf[u], sp = setOf[p]; Assert(su != sp);
        for (int v = 0; v < n; ++v) 
            if (auto &sv = setOf[v]; sv == su) sv = sp; 
        Assert(tsu.Find(u) == minOfSet[su]);
        Assert(tsu.Find(p) == minOfSet[sp]);
        minOfSet[sp] = min(minOfSet[su], minOfSet[sp]);
        minOfSet[su] = -1;
        tsu.Link(u);
        Assert(tsu.Find(u) == minOfSet[sp]);
        Assert(tsu.Find(p) == minOfSet[sp]);
    }
}

// Tests the static tree set union data structure on randomly 
// constructed trees, in an endless loop.
void TestStaticTreeSetUnion()
{
    for (int seed = 123, nIter = 0; ; ++seed, ++nIter)
    {
        mt19937_64 rnd(seed);
        int n = uniform_int_distribution<int>(1, 1'000)(rnd);
        if (seed % 100 >= 0) { fprintf(stderr, "%d  n = %d        \r", seed, n); fflush(stderr); }
        // Generate a random tree.
        vector<int> parent(n, -1), xlat(n, -1);
        for (int i = 0; i < n; ++i) 
        {
            int j = uniform_int_distribution<int>(0, i)(rnd);
            xlat[i] = xlat[j]; xlat[j] = i; 
            if (i > 0) parent[i] = uniform_int_distribution<int>(0, i - 1)(rnd);
        }
        // Randomly shuffle the labels of the nodes.
        vector<int> parent2(n, -1);
        for (int i = 0; i < n; ++i) 
        {
            int pi = parent[i];
            parent2[xlat[i]] = (pi < 0) ? -1 : xlat[pi]; 
        }
        TestStaticTreeSetUnion(parent, rnd);
    }
}

// ----------------------------------------------------------------------------
// Batched ancestor queries
// ----------------------------------------------------------------------------
// Consider a tree with nodes 0..pd-1, where (for each u) node u is the 
// child of f[u] and it is always true that u > f[u].
// We want to solve a batch of queries of the form (u_k, b_k) := "what is
// the largest ancestor of u_k whose value is <= b_k?"
// This can be solved using a union-find data structure, and below we
// have two implementations: a nearly-linear one using disjoint-set forests,
// and a genuinely linear one using the static tree set union data structure.

struct TAncestorQuery
{
    int queryIdx; // used to identify the query
    // The purpose of the query is to calculate this loop:
    //   do { u = f[u]; } while (u > upperBound);
    // but we want to do it efficiently for a whole batch of queries.
    // Note that f[u] is assumed to be in the range 0 <= f[u] < u.
    int u, upperBound; 
    int answer = -1; // could share space with 'u' except for testing purposes
    // The following is used internally by BatchAncestorQueries.
    int nextByUb = -1; // next query with the same upper bound
    TAncestorQuery(int QueryIdx, int U, int UpperBound) : queryIdx(QueryIdx), u(U), upperBound(UpperBound) { }
};

// Note that we often have to perform two batches of ancestor queries
// for the same parent vector 'f'.  Thus we can save time by reusing some
// of the data structures instead of initializing new ones each time.
struct TAncestorQueryProcessor
{
    virtual ~TAncestorQueryProcessor() { }
    virtual void Query(vector<TAncestorQuery> &queries) = 0;
};

// The nearly-linear implementation using a disjoint-set forest.
struct TAncestorQueryProcessor_NearlyLinear : public TAncestorQueryProcessor
{
protected:
    int n; const vector<int> &f;
    struct DsfNode { // Represents a node of the disjoint-set forest.
        int parent = -1; // The parent of this node.
        // The following are only valid if the current node is the root of its subtree.
        int size = 1; // number of nodes in the subtree
        int min = -1; // minimum node in the subtree 
    };
    vector<DsfNode> forest;
    // Returns the root of the tree to which 'u' belongs; also flattens the path from u to this root.
    int GetRoot(int u) 
    {
        // Find the root.
        int v = u; while (true) { int p = forest[v].parent; if (p == v) break; else v = p; }
        // Flatten the path.
        while (u != v) { auto &U = forest[u]; int pOld = U.parent; U.parent = v; u = pOld; }
        return u; 
    }
public:
    // The initialization here is trivial; we'll just allocate a vector for the
    // forest, but Query() will have to initialize it anew each time anyway to reset
    // it back to singleton sets.
    TAncestorQueryProcessor_NearlyLinear(const vector<int> &f_) : n(int(f_.size())), f(f_), forest(n) { }

    virtual void Query(vector<TAncestorQuery> &queries) override
    {
        const int nQueries = (int) queries.size();
        // For each value of 'upperBound', prepare a linked list of the queries with that upper bound.
        vector<int> firstByUb(n, -1);
        for (auto &Q : queries) Q.nextByUb = -1;
        for (int q = 0; q < nQueries; ++q) {
            auto &Q = queries[q]; Assert(0 <= Q.upperBound); Assert(Q.upperBound < n);
            Q.nextByUb = firstByUb[Q.upperBound];
            firstByUb[Q.upperBound] = q; }
        // Initialize the DSF tree.
        for (int u = 0; u < n; ++u) { auto &Node = forest[u]; Node.parent = u; Node.min = u; Node.size = 1; }
        // 
        int nQueriesDone = 0;
        for (int v = n - 1; v >= 0; --v)
        {
            // Queries with an upper bound of 'v' can now be answered.
            for (int q = firstByUb[v]; q >= 0; ) 
            {
                auto &Q = queries[q]; Assert(Q.upperBound == v);
                int root = GetRoot(Q.u); 
                auto &answer = Q.answer; answer = forest[root].min; Assert(0 <= answer); Assert(answer <= v);
                ++nQueriesDone; q = Q.nextByUb;
            }
            if (v == 0) break;
            // Merge the node 'v' (and the subset containing it) with w := f[v].
            int w = f[v]; Assert(0 <= w); Assert(w < v);
            int vRoot = GetRoot(v), wRoot = GetRoot(w); Assert(vRoot != wRoot);
            // Let wRoot be the larger of the two, and vRoot the smaller.
            if (forest[vRoot].size > forest[wRoot].size) swap(vRoot, wRoot);
            // Let wRoot become the parent of vRoot.
            auto &VR = forest[vRoot], &WR = forest[wRoot];
            VR.parent = wRoot; WR.size += VR.size; VR.size = -1; 
            WR.min = min(WR.min, VR.min);
        }
        {
            int root = GetRoot(0); auto &R = forest[root];
            Assert(R.size == n); Assert(R.min == 0);
            Assert(nQueriesDone == nQueries);
        }
    }
};

// The linear/time implementation using a the static tree set union data structure.
struct TAncestorQueryProcessor_Linear : public TAncestorQueryProcessor
{
protected:
    int n; const vector<int> &f;
    TStaticTreeSetUnion staticTreeUnion;
    bool needsReset; // Does the staticTreeSetUnion structure need to be reset before the next batch of queries?
public:
    // Note that the initialization of the static tree set union data structure is
    // much more time-consuming than executing the queries themselves.  Thus, if
    // we want to perform more then one batch of queries, it is much cheapter to 
    // reuse the data structure and just reset it before each new batch.
    TAncestorQueryProcessor_Linear(const vector<int> &f_) : n(int(f_.size())), f(f_), staticTreeUnion(f_), needsReset(true) { }

    virtual void Query(vector<TAncestorQuery> &queries) override
    {
        const int nQueries = (int) queries.size();
        // A reset is needed before each batch of queries except the first one.
        if (needsReset) staticTreeUnion.Reset();
        needsReset = true; // We will need a reset after this batch of queries.
        // For each value of 'upperBound', prepare a linked list of the queries with that upper bound.
        vector<int> firstByUb(n, -1);
        for (auto &Q : queries) Q.nextByUb = -1;
        for (int q = 0; q < nQueries; ++q) {
            auto &Q = queries[q]; Assert(0 <= Q.upperBound); Assert(Q.upperBound < n);
            Q.nextByUb = firstByUb[Q.upperBound];
            firstByUb[Q.upperBound] = q; }
        // 
        int nQueriesDone = 0;
        for (int v = n - 1; v >= 0; --v)
        {
            // Queries with an upper bound of 'v' can now be answered.
            for (int q = firstByUb[v]; q >= 0; ) 
            {
                auto &Q = queries[q]; Assert(Q.upperBound == v);
                Q.answer = staticTreeUnion.Find(Q.u); Assert(0 <= Q.answer); Assert(Q.answer <= v);
                ++nQueriesDone; q = Q.nextByUb;
            }
            if (v == 0) break;
            // Merge the node 'v' (and the subset containing it) with w := f[v].
            int w = f[v]; Assert(0 <= w); Assert(w < v);
            staticTreeUnion.Link(v);
        }
        {
            int root = staticTreeUnion.Find(0); Assert(root == 0);
            Assert(nQueriesDone == nQueries);
        }

    }
};

// ----------------------------------------------------------------------------
// Solve
// ----------------------------------------------------------------------------
// This function contains the main part of the solution of our problem.
// Given the strings s, t, p, its job is to calculate, for each position k
// where t may be inserted into s, the number of occurrences of p as a
// substring in the string s[:k] t s[k:].

// Which method is to be used to count those occurrences of p which 
// begin within s[:k] and end within s[k:]?
enum class TMethod { Quadratic, NSqrtN, NLogN, NearlyLinear, Linear };

// For k = 0..s.length(), returns solutions[k] = the number of occurrences of p in s[:k] t s[k:].
void Solve(const string &s, const string &t, const string &p, vector<int> &solutions, const TMethod method = TMethod::Linear)
{
    const int sd = s.length(), td = t.length(), pd = p.length();
    solutions.resize(sd + 1);

    if (true) if (pd > sd + td) {  // If p is longer than s + t, there can never be any occurrences.
        for (auto &sol : solutions) sol = 0; return; }

    // Build the various KMP-related tables.

    // pST[k] = the greatest i < k such that p[:i] is a suffix of p[:k].
    vector<int> pST; BuildSuffixTable(p, pd, pST);
    // spST[k] = the greatest i < pd (and i <= k) such that p[:i] is a suffix of s[:k].
    vector<int> spST; BuildSuffixTable2(s, sd, p, pd, pST, spST);
    // occCountsS[k] = the number of occurrences of p in s[:k]
    vector<int> occCountsS; BuildOccCounts(s, sd, spST, p, pd, occCountsS);
    // pRST[k] = the greatest i < k such that p^R[:i] is a suffix of p^R[:k].
    vector<int> pRST; BuildSuffixTable(p.rbegin(), pd, pRST); 
    // pPT[k] = the least i > k such that p[i:] is a prefix of p[k:].
    vector<int> pPT; BuildPrefixTable(pRST, pPT);
    // tpRST[k] = the greatest i < pd (and i <= k) such that p^R[:i] is a suffix of t^R[:k].
    vector<int> tpRST; BuildSuffixTable2(t.rbegin(), td, p.rbegin(), pd, pRST, tpRST);
    // tpPT[k] = the least i > 0 such that p[i:] is a prefix of t[k:].
    vector<int> tpPT; BuildPrefixTable2(pd, tpRST, tpPT);
    // tpPTB[k] = is t[:k] a suffix of p, i.e. does it equal p[pd-k:]?
    vector<bool> tpPTB; BuildPrefixTable2B(t, td, p, pd, pPT, tpPT, tpPTB);
    // occCountsPT[k] = the number of occurrences of p in p[:k] t which straddle the boundary between p[:k] and t.
    vector<int> occCountsPT(pd + 1, 0); for (int k = 1; k < pd; ++k) occCountsPT[k] = occCountsPT[pST[k]] + (td >= pd - k && tpPTB[pd - k] ? 1 : 0);
    // spRST[k] = te greatest i < pd (and i <= k) such that p^R[:i] is a suffix of s^R[:k].
    vector<int> spRST; BuildSuffixTable2(s.rbegin(), sd, p.rbegin(), pd, pRST, spRST);
    // spPT[k] = the least i > 0 such that p[i:] is a prefix of s[k:].
    vector<int> spPT; BuildPrefixTable2(pd, spRST, spPT);
    // tpST[k] = the greatest i < pd (and i <= k) such that p[:i] is a suffix of t[:k].
    vector<int> tpST; BuildSuffixTable2(t, td, p, pd, pST, tpST);
    // tpSTB[k] = is t[k:] a prefix of p, i.e. does it equal p[:td-k]?
    vector<bool> tpSTB; BuildSuffixTable2B(t, td, p, pd, pST, tpST, tpSTB);
    // occCountsTP[k] = the number of occurrences of p in t p[k:] which straddle the boundary between t and p[k:].
    vector<int> occCountsTP(pd + 1, 0); for (int k = pd - 1; k > 0; --k) occCountsTP[k] = occCountsTP[pPT[k]] + (td >= k && tpSTB[td - k] ? 1 : 0);
    // occCountsT[k] = the number of occurrences of p in t[:k]
    vector<int> occCountsT; BuildOccCounts(t, td, tpST, p, pd, occCountsT);

    // Count those occurrences of p that do not begin within s[:k]
    // and/or do not end in s[k:].  This is the easier part of the problem,
    // which is easy to solve in linear time.
    for (int k = 0; k <= sd; ++k)
    {
        solutions[k] = occCountsT[td]; // occurrences of p that lie wholly in t
        solutions[k] += occCountsS[k]; // occurrences of p in s[:k]
        if (k + pd <= sd) solutions[k] += occCountsS[sd] - occCountsS[k + pd - 1]; // occurrences of p in s[k:]
        // Now let's count the occurrences of p in s[:k] t such that they
        // straddle the boundary between s[:k] and t.  This means that p can be 
        // split into a prefix p[:i] and suffix p[i:], where 0 < i < pd,
        // such that s[:k] ends with p[:i] and t starts with p[:i].
        // We know that the longest p[:i] that appears at the end of s[:k] is given by i = spST[k],
        // so instead of looking at s[:k] t we can look at p[:i] t instead.
        int i = spST[k]; solutions[k] += occCountsPT[i];
        // Similarly we can count the occurrences of p in t s[k:] that straddle
        // the boundary between t and s[k:].  This means that p can be split into
        // a prefix p[:i] and suffix p[i:], where 0 < i < pd,
        // such that t ends with p[:i] and s[k:] starts with p[i:].
        // We know that the longest p[i:] that appears at the start of s[k:] is given by i = spPT[k],
        // so instead of looking at t s[k:] we can look at t p[i:] instead.
        i = spPT[k]; solutions[k] += occCountsTP[i];
    }

    // Now it remains to count those occurrences of p in s[:k] t s[k:] that
    // begin within s[:k] and end within s[k:].

    // If p not at least 2 characters longer than t, there can be no such occurrences.
    if (! (pd >= td + 2)) return;

    // tST[k] = the greatest i < k such that t[:i] is a suffix of t[:k].
    vector<int> tST; BuildSuffixTable(t, td, tST);
    // ptST[k] = the greatest i < td (and i <= k) such that t[:i] is a suffix of p[:k].
    vector<int> ptST; BuildSuffixTable2(p, pd, t, td, tST, ptST);
    // tOccInP[k] = does t occur in p at position k, i.e. is p[k:k+td] = t?
    vector<bool> tOccInP(pd + 1, false); for (int k = 0; k + td <= pd; ++k) tOccInP[k] = (ptST[k + td - 1] == td - 1) && (p[k + td - 1] == t[td - 1]);
    // iNext[i] = the greatest i' < i such that p[:i] ends with p[:i'] and t occurs at position i' in p
    // jNext[j] = the greatest j' < j such that p[pd - j:] starts with p[pd - j':]
    // These two tables, and the KMP trees based on them, are used by the simpler
    // solutions that do not involve the GG algorithm.
    vector<int> iNext, jNext; TKmpTree iTree, jTree;
    if (method == TMethod::Quadratic || method == TMethod::NSqrtN || method == TMethod::NLogN)
    {
        iNext.resize(pd, 0); jNext.resize(pd, 0); iNext[0] = -1; jNext[0] = -1;
        for (int i = 1; i < pd; ++i) if (int ii = pST[i]; ii > 0) iNext[i] = (tOccInP[ii]) ? ii : iNext[ii];
        for (int j = 1; j < pd; ++j) jNext[j] = pd - pPT[pd - j];
        iTree.Init(iNext); jTree.Init(jNext); Assert(iTree.root == 0); Assert(jTree.root == 0);
    }

    // A simple solution based on dynamic programming.  Requires O(s + t + p^2) space and time.
    if (method == TMethod::Quadratic)
    {
        // f[i * pd + j] = the number of occurrences of p in p[:i] t p[pd - j:] which straddle both boundaries.
        vector<int> f(pd * pd, 0);
        for (int i = 1; i < pd; ++i) for (int j = 1; j < pd; ++j) if (i + j + td >= pd)
        {
            // Does p occur at the start of p[:i] t p[pd - j:]?
            int F = 0;
            if (int right = pd - i - td; right > 0 && right <= j && tOccInP[i]) 
                // Now we have to check if p[pd - j:] starts with p[i':] for i' = i + td,
                // which is the same as p[pd - right:].
                if (jTree.IsAncestorOf(right, j)) ++F;
            // Next, count the occurrences of p later in the string.
            if (int ii = iNext[i]; ii > 0) F += f[ii * pd + j];
            if constexpr (SLOW_CHECKS)
            {
                // Alternatively, we can start by checking if p occurs at the end of p[:i] t p[pd - j:].
                int F2 = 0;
                if (int left = pd - j - td; left > 0 && left <= i && tOccInP[left])
                    // Now we have to check if p[:i] ends with p[:left].
                    if (iTree.IsAncestorOf(left, i)) ++F2;
                // Next, count the occurrences of p earlier in the string.
                if (int jj = jNext[j]; jj > 0) F2 += f[i * pd + jj];
                Assert(F2 == F);
            }
            f[i * pd + j] = F;
        }
        // Use the solutions the calculated by the quadratic method.
        for (int k = 1; k < sd; ++k)
        {
            int i = spST[k], j = pd - spPT[k];
            Assert(0 <= i); Assert(i < pd); Assert(0 <= j); Assert(j < pd);
            if (i > 0 && j > 0) solutions[k] += f[i * pd + j];
        }
    }

    // An improvement on the quadratic solution.  Instead of calculating
    // all O(p^2) values f(i, j), we start by marking O(sqrt p) nodes in the
    // KMP tree and calculate f(i, j) for all marked i and for all j. 
    // This takes O(p sqrt p) time and then allows us to calculate
    // additional values f(i, j) in O(sqrt p) time each; since we need to
    // calculate O(s) of them, the total time complexity is O(t + (p + s) sqrt p) time.
    // Moreover, the space complexity can be reduced from quadratic to linear
    // by processing the queries in a suitable order and forgetting results 
    // that will no longer be needed.
    else if (method == TMethod::NSqrtN) // O((p + s) sqrt p) time
    {
        int sqrtP = 1; while (sqrtP * sqrtP < pd) ++sqrtP;
        vector<TKmpTree::TQuery> queries(sd - 1);
        for (int k = 1; k < sd; ++k) { auto &Q = queries[k - 1]; Q.i = spST[k]; Q.j = pd - spPT[k]; Q.k = k; }
        vector<pair<int, int>> closestMarkedAncestor; 
        vector<int> firstQuery(pd, -1); // for each marked u, we have a list of queries (i, j) for which u is the closest marked ancestor of i
        // Mark some nodes so that no node is more than sqrt(p) steps far from the closest marked ancestor.
        int maxSubtreeSize = sqrtP;
        int nMarked = iTree.MarkNodes(maxSubtreeSize, closestMarkedAncestor);
        for (int qi = 0; qi < queries.size(); ++qi) { 
            auto &Q = queries[qi]; auto [anc, dist] = closestMarkedAncestor[Q.i];
            Q.next = firstQuery[anc]; firstQuery[anc] = qi; }
        // Calculate f(i, 0) for all i.
        vector<int> fi0(pd, 0);
        for (int i = 1, j = 0; i < pd; ++i) if (i + j + td >= pd)
        {
            int F = 0; if (int ii = iNext[i]; ii > 0) F += fi0[ii];
            if (int right = pd - i - td; right > 0 && right <= j && tOccInP[i])
                if (jTree.IsAncestorOf(right, j)) ++F;
            fi0[i] = F;
        }
        // Go through all the marked nodes.
        vector<int> fij(pd), ancPath(pd);
        for (int i = 0; i < pd; ++i) if (closestMarkedAncestor[i].first == i)
        {
            // Calculate f(i, j) for all j.
            fij[0] = fi0[i];
            for (int j = 1; j < pd; ++j)
            {
                int F = 0;
                if (i + j + td >= pd)
                {
                    if (int jj = jNext[j]; jj > 0) F += fij[jj];
                    if (int left = pd - j - td; left > 0 && left <= i && tOccInP[left])
                        if (iTree.IsAncestorOf(left, i)) ++F;
                }
                fij[j] = F;
            }
            // Go through all the queries (qi, qj) for which i is the closest marked ancestor of qi.
            for (int q = firstQuery[i]; q >= 0; ) {
                auto &Q = queries[q]; const int qi = Q.i, qj = Q.j;
                Assert(i == closestMarkedAncestor[qi].first);
                int nSteps = 0; for (int anc = qi; anc != i; anc = iNext[anc]) ancPath[nSteps++] = anc;
                Assert(nSteps == closestMarkedAncestor[qi].second);
                int F = fij[qj]; // Now F = f(i, qj).
                for (int step = 0; step < nSteps; ++step)
                {
                    int u = ancPath[nSteps - 1 - step];
                    int uu = iNext[u]; if (step == 0) Assert(uu == i); else Assert(uu == ancPath[nSteps - step]);
                    // Now F = f(uu, qj).
                    if (u + qj + td >= pd) if (int right = pd - u - td; right > 0 && right <= qj && tOccInP[u])
                        if (jTree.IsAncestorOf(right, qj)) ++F;
                    // Now F = f(u, qj).
                }
                // Now F = f(qi, qj).
                Q.result = F;
                q = Q.next; // next query for the current marked ancestor
            }
        }
        // Store the results.
        for (auto &Q : queries) solutions[Q.k] += Q.result;
    }

    // The geometric solution, based on a plane sweep.  O(t + (s + p) log p) time.
    else if (method == TMethod::NLogN) 
    {
        vector<TKmpTree::TQuery> queries(sd - 1);
        for (int k = 1; k < sd; ++k) { auto &Q = queries[k - 1]; Q.i = spST[k]; Q.j = spPT[k]; Q.k = k; Q.result = 0; }
        // Sort the queries by Q.i, in linear time.
        vector<int> firstQuery(pd, -1), nextQuery(queries.size(), -1);
        for (int qi = 0; qi < queries.size(); ++qi) { const auto &Q = queries[qi]; if (Q.i <= 0) continue;
            int x = iTree.nodes[Q.i].startTime2; nextQuery[qi] = firstQuery[x]; firstQuery[x] = qi; }
        // Suppose that t occurs in p at position l, i.e. p[l:l+|t|] = t.  This accounts for one
        // occurrence of p in s[:k] t s[k:] for each k where s[:k] ends in p[:l] and s[k:] starts with p[l+|t|:].
        // This last condition is equivalent to saying that l must be an ancestor of i_k in the first tree,
        // and l+|t| must be an ancestor of j_k in the second tree.  For any given l, its descendants
        // in the first tree constitute a contiguous range in a preorder traversal of the tree,
        // and likewise the descendants of l+|t| in the second tree.  These two ranges can be thought of as
        // defining a rectangle R_l in the 2-dimensional plane, and our condition now becomes equivalent to
        // saying that (i_k, j_k) must lie in R_l.  Thus, for each k we must count the rectangles R_l that contain (i_k, j_k).
        // We will do this with a plane sweep along the x-axis.  The state of the rectangles along a vertical
        // line can be conveniently represented by a Fenwick tree: let a[y] be the difference between the
        // number of rectangles that start at this y-coordinate and the number of rectangles that end there.
        // Then let A[y] be the sum of a[0..y]; this is the number of rectangles that contain the point (x, y)
        // for the current value of y.
        struct Rectangle { int x1, x2, y1, y2; }; // Represents {x1, ..., x2} \times {y1, ..., y2}.
        vector<Rectangle> rects;
        for (int l = 1; l + td < pd; ++l) if (tOccInP[l])
        {
            Rectangle R; const auto &Ni = iTree.nodes[l], &Nj = jTree.nodes[pd - (l + td)]; 
            R.x1 = Ni.startTime2; R.x2 = Ni.endTime2;
            R.y1 = Nj.startTime2; R.y2 = Nj.endTime2;
            rects.push_back(R);
        }
        // For each x, prepare a list of the rectangles whose leftmost column is x 
        // and a list of rectangles whose rightmost column is x.
        vector<int> firstLeft(pd, -1), firstRight(pd, -1), nextLeft(rects.size(), -1), nextRight(rects.size());
        for (int ri = 0; ri < rects.size(); ++ri) { auto &R = rects[ri]; 
            nextLeft[ri] = firstLeft[R.x1]; firstLeft[R.x1] = ri;
            nextRight[ri] = firstRight[R.x2]; firstRight[R.x2] = ri; }
        // Perform the plane sweep.
        vector<int> fenwickTree(pd + 1, 0);
        for (int x = 0; x < pd; ++x)
        {
            // Add the rectangles whose leftmost column is x.
            for (int ri = firstLeft[x]; ri >= 0; ri = nextLeft[ri]) {
                const auto &R = rects[ri]; FenwickUpdate(fenwickTree, R.y1, 1); FenwickUpdate(fenwickTree, R.y2 + 1, -1); }
            // Process the queries for x.
            for (int qi = firstQuery[x]; qi >= 0; qi = nextQuery[qi]) {
                auto &Q = queries[qi]; if (Q.j >= pd) continue;
                int y = jTree.nodes[pd - Q.j].startTime2; Q.result = FenwickQuery(fenwickTree, y); }
            // Remove the rectangles whose rightmost column is x.
            for (int ri = firstRight[x]; ri >= 0; ri = nextRight[ri]) {
                const auto &R = rects[ri]; FenwickUpdate(fenwickTree, R.y1, -1); FenwickUpdate(fenwickTree, R.y2 + 1, 1); }
        }
        for (auto &Q : queries) solutions[Q.k] += Q.result;
    }

    // The really efficient solution based on the GG algorithm.  Its time complexity
    // is linear or nearly linear, depending on which implementation of the
    // union-find data structure is used.
    else if (method == TMethod::NearlyLinear || method == TMethod::Linear) 
    {
        constexpr const bool LotsOfChecks = false;

        // Find the first two occurrences of t in p.  There should be at least one, otherwise 
        // there can't possibly be any occurrences of p in s[:k] t s[k:] which contain the whole t in the middle.
        int tInP = 0; while (tInP < pd && ! tOccInP[tInP]) ++tInP;
        if (tInP >= pd) return;
        if (LotsOfChecks) for (int i = 0; i < td; ++i) Assert(p[tInP + i] == t[i]);
        int tInP2 = tInP + 1; while (tInP2 < pd && ! tOccInP[tInP2]) ++tInP2;
        if (LotsOfChecks) if (tInP2 < pd) for (int i = 0; i < td; ++i) Assert(p[tInP2 + i] == t[i]);

        // tOccInP[k] = the smallest i >= k such that t occurs in p at position i, or pd if there is no such occurrence
        vector<int> tOccInPNext(pd + 1, pd); for (int k = pd - td; k >= 0; --k) tOccInPNext[k] = tOccInP[k] ? k : tOccInPNext[k + 1]; 
        Assert(tInP == tOccInPNext[0]); 
        if (tInP < pd) Assert(tInP2 == tOccInPNext[tInP + 1]); else Assert(tInP2 == pd);

        // [GG22] = Moses Ganardi, Pawel Gawrychowski, "Pattern Matching on
        // Grammar-Compressed Strings in Linear Time", Proc. SODA 2022, pp. 2833-46.
        // https://doi.org/10.1137/1.9781611977073.110
        // Preprint: https://doi.org/10.48550/arXiv.2111.05016 
        // We follow the method described in Theorem 3.2 of this paper, except that the approach
        // from Section 4 of that paper, based on weighted ancestor queries, has been 
        // replaced with a simpler alternative based on a union-find structure over the KMP tree.

        // Build suffix trees of p and p^R.
        vector<int> pSuffArray, pLcpArray, pRSuffArray, pRLcpArray;
        BuildSuffixArray(p, pSuffArray, pLcpArray); 
        string pR = p; reverse(pR.begin(), pR.end()); BuildSuffixArray(pR, pRSuffArray, pRLcpArray); 
        TSuffixTree pSuffixTree(pSuffArray, pLcpArray, false), pRSuffixTree(pRSuffArray, pRLcpArray, false);
        // Returns the length of the longest common prefix of p[i:] and p[j:].
        auto LcpP = [&pSuffixTree, pd] (int i, int j) {
            Assert(0 <= i); Assert(i <= pd); Assert(0 <= j); Assert(j <= pd);
            if (i == j) return pd - i;
            if (i == pd || j == pd) return 0;
            return pSuffixTree.LCP(i, j); 
        };
        // Returns the length of the longest common suffix of p[:pd-i] and p[:pd-j].
        auto LcsP = [&pRSuffixTree, pd] (int i, int j) {
            Assert(0 <= i); Assert(i <= pd); Assert(0 <= j); Assert(j <= pd);
            if (i == j) return pd - i;
            if (i == pd || j == pd) return 0;
            // We want the longest common suffix of p[:pd-i] and p[:pd-j],
            // i.e. the longest common prefix of (p[:pd-i])^R and (p[:pd-j])^R,
            // i.e. the longest common prefix of p^R[i:] and p^R[j:].
            return pRSuffixTree.LCP(i, j); 
        };
        // Preprocess the suffix trees so as to support constant-time LCP queries.
        pSuffixTree.InitBF00(); pRSuffixTree.InitBF00();
        // Test that LcpP works correctly.
        if constexpr (LotsOfChecks) if (pd <= 1000) for (int i = 0; i <= pd; ++i) for (int j = 0; j <= pd; ++j) {
            int r = 0; while (i + r < pd && j + r < pd && p[i + r] == p[j + r]) ++r;
            int rr = LcpP(i, j); Assert(r == rr); }
        // Test that LcsP works correctly.
        if constexpr (LotsOfChecks) if (pd <= 1000) for (int i = 0; i <= pd; ++i) for (int j = 0; j <= pd; ++j) {
            int r = 0; while (i + r < pd && j + r < pd && p[pd - i - 1 - r] == p[pd - j - 1 - r]) ++r;
            int rr = LcsP(i, j); Assert(r == rr); }

        typedef decltype(LcpP) TLcpP;
        typedef decltype(LcsP) TLcsP;

        // This class is used by TFibre to capture local variables from Solve().
        // At first I hoped to simply derive TFibre from a lambda instead, but it turns out that
        // you can't access the variables that a lambda has captured.  https://stackoverflow.com/a/19976680
        struct TCaptureHelper 
        {
            TLcpP &LcpP; TLcsP &LcsP;
            const string &t, &p, &s;
            const int tInP, tInP2, pd, td;
            const vector<int> &spPT, &spST, &pPT, &pST, &tST, &tOccInPNext;
            TCaptureHelper(TLcpP &LcpP_, TLcsP &LcsP_, const string &t_, const string &p_, const string &s_, const int tInP_, const int tInP2_, const vector<int> &spPT_, const vector<int> &spST_, const vector<int> &pPT_, const vector<int> &pST_, const vector<int> &tST_, const vector<int> &tOccInPNext_) : 
                LcpP(LcpP_), LcsP(LcsP_), t(t_), p(p_), s(s_), tInP(tInP_), tInP2(tInP2_), pd((int) p.length()), td((int) t.length()), spPT(spPT_), spST(spST_), pPT(pPT_), pST(pST_), tST(tST_), tOccInPNext(tOccInPNext_) { }
        };
        TCaptureHelper captureHelper { LcpP, LcsP, t, p, s, tInP, tInP2, spPT, spST, pPT, pST, tST, tOccInPNext };

        // QW QW QW rename x into v everywhere!!!!
        // This class counts the occurrences of p in utx (i.e. only such occurrences as begin in u and end in x),
        // where u = p[:k] and x = p[k:].
        // However, it is ready for the fact that at a few steps in the computation, 
        // we'll have to process all k's together as a batch instead of each of them individually.
        struct TFibre : protected TCaptureHelper
        {
            // Our fibre's 'local variables'.
            int k, ud, xd, udOrig, xdOrig, nOccAll = 0;
            // Naive solution, for testing.
            int nOccAll_ = -1, nOccAllEx_ = -1;  // nOccAllEx_ counts all occurrences of p in utx;  nOccAll_ counts only those that begin in u and end in x

            // Finds the longest mm such that p[:mm] = (utx)[h:h + mm].  
            int find_p_in_utx_left(int h) 
            { 
                Assert(0 <= h); Assert(h <= ud);
                int mm = LcpP(0, h); mm = min(mm, ud - h);
                if (mm == ud - h) {
                    // There's no mismatch until the end of u.  Now we're comparing p[mm:] with the beginning of t = p[tInP : tInP + td].
                    int mm2 = LcpP(mm, tInP); mm2 = min(mm2, td);
                    mm += mm2;
                    if (mm2 == td) {
                        // There's no mismatch until the end of t.  Now we're comparing p[mm:] with the beginning of x = p[-xd:].
                        int mm3 = LcpP(mm, pd - xd); mm3 = min(mm3, xd);
                        mm += mm3; } }
                Assert(0 <= mm && mm <= pd);
                if constexpr (LotsOfChecks) for (int i = 0; i <= mm && i < pd && i + h < ud + td + xd; ++i) {
                    int j = h + i; char c = (j < ud) ? p[j] /* = u[j] */ : (j < ud + td) ? t[j - ud] : p[pd - xd + (j - ud - td)] /* = x[j - ud - td] */;
                    char c2 = p[i]; if (i < mm) Assert(c == c2); else if (i == mm) Assert(c != c2); } 
                return mm; 
            }

            // Finds the longest mm such that p[pd - mm:] = (utx)[|utx| - h - mm : |utx| - h].  
            // In other words, we're looking for an occurrence of 'p' that ends 'h' characters
            // before the end of 'utx', and we're interested in the mm such that the rightmost
            // mismatch occurs 'mm' characters before the end of 'p' (if there is actually a match, we'll get mm == |p|).
            int find_p_in_utx_right(int h) 
            { 
                Assert(0 <= h); Assert(h <= xd);
                // First we're comparing p (starting from the right) with the end of x = p[pd - xd:].
                int mm = LcsP(0, h); mm = min(mm, xd - h);
                if (mm == xd - h) {
                    // There's no mismatch (starting from the right) until we reach the left end of x.
                    //  Now we're comparing p[:pd - mm] with the end of t = p[tInP : tInP + td].
                    int mm2 = LcsP(mm, pd - tInP - td); mm2 = min(mm2, td);
                    mm += mm2;
                    if (mm2 == td) {
                        // There's no mismatch until the left end of t.  Now we're comparing p[:pd - mm] with the end of u = p[:ud].
                        int mm3 = LcsP(mm, pd - ud); mm3 = min(mm3, ud);
                        mm += mm3; } }
                Assert(0 <= mm && mm <= pd);
                if constexpr (LotsOfChecks) for (int i = 0; i <= mm && i < pd && i + h < ud + td + xd; ++i) {
                    int j = h + i; char c = (j < xd) ? p[pd - 1 - j] /* = x[xd - 1 - j] */ : (j < xd + td) ? t[td - 1 - (j - xd)] : p[ud - 1 - (j - xd - td)] /* = u[ud - 1 - (j - ud - td)] */;
                    char c2 = p[pd - 1 - i]; if (i < mm) Assert(c == c2); else if (i == mm) Assert(c != c2); } 
                return mm; 
            }

            static inline int Ceil(int a, int b) { Assert(b > 0); return (a < 0) ? -((-a) / b) : (a + b - 1) / b; }
            static inline int Floor(int a, int b) { Assert(b > 0); return (a < 0) ? -((-a + b - 1) / b) : a / b; }

            explicit TFibre(TCaptureHelper &captureHelper_, int k_) : TCaptureHelper(captureHelper_) 
            { 
                // We want to count the occurrences of p in s[:k] t s[k:] which start in s[:k] and end in s[k:].
                // Let u = p[:ud] be the longest prefix of p that is also a suffix of s[:k]
                // and let x = p[-xd:] be the longest suffix of p that is also a preffix of s[k:].
                k = k_; ud = spST[k]; xd = pd - spPT[k];
                if constexpr (false) for (int i = 0; i < ud; ++i) Assert(s[k - ud + i] == p[i]);
                if constexpr (false) for (int i = 0; i < xd; ++i) Assert(s[k + i] == p[pd - xd + i]);
                udOrig = ud, xdOrig = xd; nOccAll = 0;

                // Calculate the solution naively, for testing.
                nOccAllEx_ = -1; nOccAll_ = -1;  // nOccAllEx_ counts all occurrences of p in utx;  nOccAll_ counts only those that begin in u and end in x
                if constexpr (LotsOfChecks) {
                    nOccAllEx_ = 0; nOccAll_ = 0;
                    for (int h = 0; h + pd <= ud + td + xd; ++h) {
                        int mm = (h >= ud) ? -1 : find_p_in_utx_left(h);
                        int h2 = ud + td + xd - (h + pd);
                        int mm2 = (h2 >= xd) ? -1 : find_p_in_utx_right(h2);
                        Assert(mm >= 0 || mm2 >= 0);
                        int found = -1;
                        if (mm < 0) found = (mm2 == pd);
                        else if (mm2 < 0) found = (mm == pd);
                        else {
                            found = (mm == pd);
                            if (found) Assert(mm2 == pd); else Assert(mm2 < pd); }
                        Assert(found >= 0);
                        if (found){
                            ++nOccAllEx_;
                            if (h < ud && h + pd > ud + td) ++nOccAll_; } } }
            }

            // Counts those occurrences of p that begin in the first half of u.
            void CountEarlyOccurrences()
            {
                if (ud <= pd / 4) return;
                int nOcc = -1;
                // First we'll count occurrences of p in utx at positions h <= |u|/2, then shorten u appropriately.
                // Since p itself starts with u, the occurrence of u at the start of utx and the one at the start of p
                // will overlap by at least |u|/2 characters, which means that h is a period of u and therefore
                // a multiple of the minimum period of u.
                const string_view u(p.c_str(), ud), x(p.c_str() + pd - xd, xd);
                const int up = ud - pST[ud]; Assert(0 < up); Assert(up <= ud); // minimum period of u
                if constexpr (LotsOfChecks) for (int i = up; i < ud; ++i) Assert(u[i] == u[i - up]);
                // Compute the maximal K such that p[:K] has the period 'up'.  
                // Since u is a prefix of p and has the period 'up', we will get K >= |u|.
                const int K = LcpP(0, up) + up; Assert(K >= ud); Assert(K <= pd); Assert(K >= up);
                if constexpr (LotsOfChecks) for (int i = up; i < K; ++i) Assert(p[i - up] == p[i]);
                // Since h must be a multiple of 'up', it will be of the form a * up for 0 <= a <= aMax.
                //const int aMax = ud / (2 * up); Assert(aMax >= 0); Assert(aMax * up <= ud / 2); Assert((aMax + 1) * up > ud / 2);
                const int aMax = min(ud / (2 * up), Floor(ud + td + xd - pd, up)); Assert(aMax * up <= ud / 2); Assert(aMax * up + pd <= ud + td + xd);
                //if (aMax * up + pd > ud + td + xd) { fprintf(stderr, "s = \"%s\", t = \"%s\", p = \"%s\"; k = %d; ud = %d, td = %d, xd = %d; up = %d; aMax = %d; aMax up + pd = %d > ud + td + xd = %d\n", s.c_str(), t.c_str(), p.c_str(), k, ud, td, xd, up, aMax, aMax * up + pd, ud + td + xd); fflush(stderr); Assert(false); }
                // But we'll really only be interested in occurrences that extend all the way into x.
                // This means that we want a * up + |p| > |ut|, i.e. a > (|ut| - |p|) / up, i.e. a >= 1 + floor( (|ut| - |p|) / up ).
                int aMin = ud + td - pd; if (aMin < 0) aMin = 0; else aMin = 1 + aMin / up;
                // See if p[:K] occurs in utx at position aMax * up, or find the first mismatch 'mm'.
                // In fact we'll just find the first mismatch between p and utx[aMax * up:], even if it occurs later than in the first K characters.
                const int mm = (aMax < aMin) ? 0 : find_p_in_utx_left(aMax * up);
                if (aMax < aMin) nOcc = 0; 
                // First, consider the case that p[:K] does occur in utx at position aMax * up.
                else if (mm >= K)
                {
                    // If K = |p|, we have found an occurrence of p; and since u is periodic with period 'up',
                    // shifting this occurrence by 'up' characters to the left will still see matching characters everywhere.
                    // Hence there is an occurrence at a * up for all 0 <= a <= aMax.   [But we only care about a >= aMin.]
                    if (K == pd) nOcc = (aMin > aMax) ? 0 : aMax - aMin + 1;
                    // Otherwise no occurrence of p in utx is possible at positions a * up for a < aMax.
                    // However, an occurrence at aMax * up is still possible.  [But we only care about it if aMax >= aMin.]
                    else nOcc = (mm == pd) ? (aMax >= aMin ? 1 : 0) : 0;
                }
                // Otherwise we know that p[:K] does not occur in utx at position aMax * up because only the first mm characers match.
                else
                {
                    // In other words, there is a mismatch between p[mm] and (utx)[aMax * up + mm].
                    // It can be shown that p[:K] also cannot cover that mismatch if we shift it left by a multiple of 'up'.
                    // Thus we have to shift it so far left that p[:K] ends before (utx)[aMax * up + mm].
                    // In other words, we want a * up + K <= aMax * up + mm, hence a <= (aMax * up + mm - K) / up.
                    int aMax2 = aMax * up + mm - K; if (aMax2 < 0) aMax2 = -1; else aMax2 /= up;
                    Assert(aMax2 < aMax);
                    if (aMax2 < 0) nOcc = 0;
                    // If K = |p|, it occurs at every position a * up for 0 <= a <= aMax2.  [But we only care about a >= aMin.]
                    else if (K == pd) { nOcc = (aMin > aMax2) ? 0 : aMax2 - aMin + 1; }
                    // Otherwise the only position where it could occur is at aMax2 * up itself.  We have to check this.   [But we only care about it if aMax2 >= aMin.]
                    else {
                        int mm2 = find_p_in_utx_left(aMax2 * up);
                        nOcc = (mm2 == pd) ? (aMax2 >= aMin ? 1 : 0) : 0; }
                }
                if constexpr (LotsOfChecks) {
                    int nOcc2 = 0; for (int h = 0; h <= ud / 2; ++h) {
                        if (h + pd <= ud + td) continue;
                        int ii = find_p_in_utx_left(h); 
                        if constexpr (true) {
                            int i = 0; for ( ; i < pd && i + h < ud + td + xd; ++i) {
                                int j = i + h; char c = (j < ud) ? u[j] : (j < ud + td) ? t[j - ud] : x[j - ud - td];
                                char c2 = p[i]; if (c != c2) break; }
                            Assert(ii == i); }
                        if (ii == pd) ++nOcc2; }
                    if (nOcc != nOcc2) printf("%d or %d?  u = %s (ud = %d, up = %d), t = %s, x = %s (xd = %d), p = %s (pd = %d); K = %d, mm = %d, aMax = %d\n", nOcc, nOcc2, string(u).c_str(), ud, up, t.c_str(), string(x).c_str(), xd, p.c_str(), pd, K, mm, aMax);
                    Assert(nOcc == nOcc2); }
                if constexpr (false) printf("nOcc = %d; u = %s (ud = %d, up = %d), t = %s, x = %s (xd = %d), p = %s (pd = %d); K = %d, mm = %d, aMax = %d\n", nOcc, string(u).c_str(), ud, up, t.c_str(), string(x).c_str(), xd, p.c_str(), pd, K, mm, aMax);
                Assert(nOcc >= 0); Assert(nOcc <= ud / 2 + 1);
                nOccAll += nOcc;
                /* 
                // Now we should update ud like this:
                int udNext = (ud - 1) / 2;
                do { ud = pST[ud]; } while (ud > udNext);
                // But then the time complexity wouldn't be linear; the caller will have to do this
                // in a batched manner over all the fibres.
                */
            }

            // Counts those occurrences of p that begin in the second half of x.
            void CountLateOccurrences()
            {
                if (xd <= pd / 4) return;
                int nOcc = -1;
                // Now we'll count occurrences of p in utx that end at positions |utx| - h for h <= |x|/2, then shorten x appropriately.
                // Since p itself ends with x, the occurrence of x at the end of utx and the one at the end of p
                // will overlap by at least |x|/2 characters, which means that h is a period of u and therefore
                // a multiple of the minimum period of u.
                const string_view u(p.c_str(), ud), x(p.c_str() + pd - xd, xd);
                const int xp = pPT[pd - xd] - (pd - xd); Assert(0 < xp); Assert(xp <= xd); // minimum period of x
                if constexpr (LotsOfChecks) for (int i = xp; i < xd; ++i) Assert(x[i] == x[i - xp]);
                // Compute the maximal K such that p[pd-K:] has the period 'xp'.  
                // Since x is a suffix of p and has the period 'xp', we will get K >= |x|.
                const int K = LcsP(0, xp) + xp; Assert(K >= xd); Assert(K <= pd); Assert(K >= xp);
                if constexpr (LotsOfChecks) for (int i = xp; i < K; ++i) Assert(p[pd - 1 - (i - xp)] == p[pd - 1 - i]);
                // Since h must be a multiple of 'xp', it will be of the form a * xp for 0 <= a <= aMax.
                //const int aMax = xd / (2 * xp); Assert(aMax >= 0); Assert(aMax * xp <= xd / 2); Assert((aMax + 1) * xp > xd / 2);
                const int aMax = min(xd / (2 * xp), Floor(ud + td + xd - pd, xp)); Assert(aMax * xp <= xd / 2); Assert(aMax * xp + pd <= ud + td + xd);
                // But we'll really only be interested in occurrences whose left end is in u.
                // This means that we want a * xp + |p| > |tx|, i.e. a > (|tx| - |p|) / xp, i.e. a >= 1 + floor( (|tx| - |p|) / xp ).
                int aMin = xd + td - pd; if (aMin < 0) aMin = 0; else aMin = 1 + aMin / xp;
                // See if p[pd-K:] occurs in utx ending at position |utx| - aMax * up, or find the first mismatch 'mm' (counting from the right).
                // In fact we'll just find the rightmost mismatch between p and utx[:|utx| - aMax * up], even if it occurs later than in the rightmost K characters.
                const int mm = (aMax < aMin) ? 0 : find_p_in_utx_right(aMax * xp);
                if (aMax < aMin) nOcc = 0;
                // First, consider the case that p[pd-K:] does occur in utx, ending aMax * xp characters before the right end.
                else if (mm >= K)
                {
                    // If K = |p|, we have found an occurrence of p; and since x is periodic with period 'xp',
                    // shifting this occurrence by 'xp' characters to the right will still see matching characters everywhere.
                    // Hence there is an occurrence at a * xp for all 0 <= a <= aMax.  [But we only case about a >= aMin.]
                    if (K == pd) nOcc = (aMin > aMax) ? 0 : aMax - aMin + 1;
                    // Otherwise no occurrence of p in utx is possible such that it ends a * up characters before the right end for a < aMax.
                    // However, an occurrence at aMax * up is still possible.  [But we only case about it if aMax >= aMin.]
                    else nOcc = (mm == pd) ? (aMax >= aMin ? 1 : 0) : 0;
                }
                // Otherwise we know that p[pd-K:] does not occur in utx s.t. it ends aMax * up characetrs before the right end, because only the first mm characers match.
                else
                {
                    // In other words, there is a mismatch between p[pd-1-mm] and (utx)[|utx| - 1 - (aMax * xp + mm)].
                    // It can be shown that p[pd-K:] also cannot cover that mismatch if we shift it right by a multiple of 'xp'.
                    // Thus we have to shift it so far right that the left end of p[pd-K:] starts to the right of (utx)[|utx| - 1 - (aMax * xp + mm)].
                    // In other words, we want a * xp + K <= aMax * up + mm, hence a <= (aMax * xp + mm - K) / xp.
                    int aMax2 = aMax * xp + mm - K; if (aMax2 < 0) aMax2 = -1; else aMax2 /= xp;
                    Assert(aMax2 < aMax);
                    if (aMax2 < 0) nOcc = 0;
                    // If K = |p|, it occurs at every position a * xp for 0 <= a <= aMax2.  [But we only care about a >= aMin.]
                    else if (K == pd) nOcc = (aMin > aMax2) ? 0 : aMax2 - aMin + 1;
                    // Otherwise the only position where it could occur is at aMax2 * xp itself.  We have to check this.  [And we only care about it if a >= aMin.]
                    else {
                        int mm2 = find_p_in_utx_right(aMax2 * xp);
                        nOcc = (mm2 == pd) ? (aMax2 >= aMin ? 1 : 0) : 0; }
                }
                if constexpr (LotsOfChecks) {
                    int nOcc2 = 0; for (int h = 0; h <= xd / 2; ++h) {
                        if (h + pd <= xd + td) continue;
                        int ii = find_p_in_utx_right(h); 
                        if constexpr (true) {
                            int i = 0; for ( ; i < pd && h + i < ud + td + xd; ++i) {
                                int j = (ud + td + xd) - 1 - (i + h); char c = (j < ud) ? u[j] : (j < ud + td) ? t[j - ud] : x[j - ud - td];
                                char c2 = p[pd - 1 - i]; if (c != c2) break; }
                            Assert(ii == i); }
                        if (ii == pd) ++nOcc2; }
                    if (nOcc != nOcc2) printf("%d or %d?  u = %s (ud = %d), t = %s, x = %s (xd = %d, xp = %d), p = %s (pd = %d); K = %d, mm = %d, aMax = %d\n", nOcc, nOcc2, string(u).c_str(), ud, t.c_str(), string(x).c_str(), xd, xp, p.c_str(), pd, K, mm, aMax);
                    Assert(nOcc == nOcc2); }
                if constexpr (false) printf("nOcc = %d; u = %s (ud = %d), t = %s, x = %s (xd = %d, xp = %d), p = %s (pd = %d); K = %d, mm = %d, aMax = %d\n", nOcc, string(u).c_str(), ud, t.c_str(), string(x).c_str(), xd, xp, p.c_str(), pd, K, mm, aMax);
                Assert(nOcc >= 0); Assert(nOcc <= xd / 2 + 1);
                nOccAll += nOcc;
                /*
                // Now we should update xd like this:
                int xdNext = (xd - 1) / 2;
                do { xd = pd - pPT[pd - xd]; } while (xd > xdNext); 
                // But then the time complexity wouldn't be linear; the caller will have to do this
                // in a batched manner over all the fibres.
                */
            }

            // Counts the occurrences that remain when u and x are short relative to p.
            void CountRemainingOccurrences() 
            {
                // Now u and x are short, <= |p|/4.
                Assert(ud <= pd / 4); Assert(xd <= pd / 4); 
                if (! (ud + td + xd >= pd && ud > 0 && xd > 0)) return;  // ud > 0 and td > 0 are required so that an occurrence of p can begin in u and end in t at all
                Assert(td >= pd / 2);
                const string_view u(p.c_str(), ud), x(p.c_str() + pd - xd, xd);
                int nOcc = -1;
                for (int __ = 0; __ < 1; ++__) 
                {
                    // We're only interested in occurrences of p in u t x that contain the whole t.
                    if (tInP2 >= td) {
                        // There is only one occurrence of t in p, so we can check if p occurs in utx that way.
                        // Also note that we only care about it if it starts in u and extends all the way into x.
                        int h = ud - tInP; if (h < 0 || h >= ud || h + pd <= ud + td) nOcc = 0; 
                        else { int mm = find_p_in_utx_left(h); 
                            nOcc = (mm == pd) ? 1 : 0; } 
                        break; }
                    // At this point we know there are at least two occurrences of t in p, namely at tInP and tInP2.
                    Assert(tInP2 < td);
                    int dtt = tInP2 - tInP;
                    // Now |p| >= dtt + |t|, and thus it can only occur in utx if |utx| >= dtt + |t|,
                    // i.e. dtt <= |u| + |x|.   Note that the right side is <= |p|/2, since we know that |u| and |x| are both <= |p|/4,
                    // so we could check the slightly weaker condition dtt <= |p|/2.
                    if (dtt > xd + ud) { nOcc = 0; break; }
                    Assert(dtt <= pd / 2);
                    // If p does occur in utx, then some occurrence of t in p must match with the explicit occurrence of t in utx.
                    // - If this is the first occurrence of t in p, then the second occurrence can occur at most
                    //   |x| characters later (or it would extend past the right end of utx);
                    //   and since |x| <= |p|/4 and |t| >= |p|/2, it follows that |x| <= |t|/2, 
                    //   so these two occurrences of t in p must overlap by at least |t| - |x| >= |t|/2.
                    // - Similarly, if this is the second or even later occurrence of t in p, then the first occurrence
                    //   can occur at most |u| characters earlier (or it would extend past the left end of utx);
                    //   and since |u| <= |p|/4 <= |p|, it follows that these two occurrences of t in p must overlap by at least |t| - |x| >= |t|/2.
                    // So either way, if p occurs in utx, then p contains two occurrences of t which overlap by at least |t|/2,
                    // and so each of these two overlapping occurrences must constitute a periodic string whose period
                    // is the difference of the offsets in p where they occur, and this, as we already saw, is <= max{|x|, |u|} <= |p|/4.
                    // Since these two overlapping occurrences of t begin with t, it follows that t itself is periodic with this period.
                    const int tp = td - tST[td]; Assert(0 < tp); Assert(tp <= td); // minimum period of t
                    if constexpr (false) for (int i = tp; i < td; ++i) Assert(t[i] == t[i - tp]);
                    if (tp > pd / 4) { nOcc = 0; break; }
                    // We'll take the first occurrence of t in p and see how far left and right we can get
                    // with the same period; thus extending t into p2, we can imagine p being split into p1 p2 p3.
                    int p1d = tInP, p3d = pd - (tInP + td);
                    int p1dShift = LcsP(pd - (tInP + td), pd - (tInP + td - tp)) + tp, p3dShift = LcpP(tInP, tInP + tp) + tp; 
                    Assert(p1dShift >= td); p1dShift -= td;
                    Assert(p3dShift >= td); p3dShift -= td;
                    p1d -= p1dShift; p3d -= p3dShift;
                    int p2d = pd - p1d - p3d;
                    if constexpr (false) printf("t = %s (td = %d, tp = %d) occurs at %d %d in p = %s (pd = %d); p1d = %d, p3d = %d\n", t.c_str(), td, tp, tInP, tInP2, p.c_str(), pd, p1d, p3d);
                    if constexpr (LotsOfChecks) for (int i = p1d + tp - 1; i <= pd - p3d; ++i) if (0 <= i && i < pd) {
                        int j = i - tp; if (j < p1d) Assert(j < 0 || p[i] != p[j]);
                        else if (i >= pd - p3d) Assert(p[i] != p[j]);
                        else Assert(p[i] == p[j]); }
                    // Similarly, we'll take the explicit t in utx and see how far left and right we can get
                    // with the same period; thus extending t into u and x, we can imagine u being split into u1 u2
                    // and x into x1 x2, such that u2 t x1 is periodic with the period 'tp'.
                    int wholePeriods = (td / tp) * tp; Assert(wholePeriods * 2 >= td);
                    // |u| and |x| are <= |p|/4, while wholePeriods >= |t|/2 >= |p|/4,
                    // so we'll reach the end of u or x even with the wholePeriods part.
                    Assert(wholePeriods >= ud); Assert(wholePeriods >= xd); 
                    int u2d = LcsP(pd - ud, pd - (tInP + wholePeriods)); u2d = min(u2d, wholePeriods);
                    if constexpr (false) if (u2d == wholePeriods) {  // Not needed, as we'll reach the end of u even with the wholePeriods part.
                        int mm2 = LcsP(pd - (ud - u2d), pd - (tInP + wholePeriods)); mm2 = min(mm2, wholePeriods);
                        u2d += mm2; }
                    int x1d = LcpP(pd - xd, tInP + td - wholePeriods); x1d = min(x1d, wholePeriods);
                    if constexpr (false) if (x1d == wholePeriods) { // Not needed, as we'll reach the end of x even with the wholePeriods part.
                        int mm2 = LcpP(pd - (xd - x1d), tInP + td - wholePeriods); mm2 = min(mm2, wholePeriods);
                        x1d += mm2; }
                    Assert(u2d <= ud); Assert(u2d <= td); Assert(x1d <= xd); Assert(x1d <= td);
                    int u1d = ud - u2d, x2d = xd - x1d;
                    if constexpr (LotsOfChecks) for (int i = u1d + tp - 1; i <= ud + td + x1d; ++i) if (0 <= i && i < ud + td + xd) {
                        int j = i - tp; if (j < 0) continue;
                        int ci = (i < ud) ? u[i] : (i < ud + td) ? t[i - ud] : x[i - ud - td];
                        int cj = (j < ud) ? u[j] : (j < ud + td) ? t[j - ud] : x[j - ud - td];
                        if (j < u1d || i >= ud + td + x1d) Assert(ci != cj);
                        else Assert(ci == cj); }
                    // If p = p1 p2 p3 occurs in u1 u2 t x1 x2 at position h,
                    // then p2 occurs in u2 t x1 at position h + |p1| - |u1|.  
                    // But where does p2 occur in u2 t x1?  
                    int K = tOccInPNext[p1d]; Assert(K >= p1d); Assert(K + td <= p1d + p2d);
                    K -= p1d; 
                    const string_view p2(p.c_str() + p1d, p2d); 
                    if constexpr (false) printf("p = %s (pd %d), p1d = %d, p2d = %d, p3d = %d; t = %s (td %d), K = %d\n", p.c_str(), pd, p1d, p2d, p3d, t.c_str(), td, K);
                    if constexpr (LotsOfChecks) for (int i = 0; i < td; ++i) Assert(t[i] == p2[K + i]);
                    // Now t occurs at position K in p2; and if p2 occurs in u2 t x1 at position h + |p1| - |u1|,
                    // then the t which occurs at position K in p2 will occur at position h + |p1| - |u1| + K in u2 t x1,
                    // so one way for this to work would be to have h + |p1| - |u1| + K = |u2|,
                    // and thus h = |u| - |p1| - K; other possibilities would have h + a tp for various integers a.
                    int h0 = ud - p1d - K;
                    // We want 0 <= h0 + a tp <= |utx| - |p| so that p lies within utx,
                    int aMin = -h0, aMax = ud + td + xd - pd - h0;
                    // but also 0 <= h0 + a tp + |p1| - |u1| <= |u2 t x1| - |p2| so that p2 lies within u2 t x1.
                    aMin = max(aMin, -h0 - p1d + u1d); 
                    aMax = min(aMax, ud + td + x1d - p1d - p2d - h0);
                    // And we also want h0 + a tp <= |u| - 1 so that p starts within u.
                    aMax = min(aMax, ud - 1 - h0);
                    // And we also want h0 + a tp + |pd| >= |u t| + 1 so that p ends within x.
                    aMin = max(aMin, ud + td + 1 - h0 - pd);
                    aMin = Ceil(aMin, tp); aMax = Floor(aMax, tp);
                    if (aMin > aMax) { nOcc = 0; break; }
                    if constexpr (false) printf("h0 = %d, K = %d, tp = %d, a = %d..%d, p1d = %d, p2d = %d, p3d = %d; u1d = %d, u2d = %d; x1d = %d, x2d = %d\n", h0, K, tp, aMin, aMax, p1d, p2d, p3d, u1d, u2d, x1d, x2d);
                    // We know that p2 occurs in u2 t x1 at positions h0 + a tp for aMin <= a <= aMax.
                    if (p1d == 0 && p3d == 0) 
                        // Since p = p2, we also have the occurrences of p that we were looking for.
                        nOcc = aMax - aMin + 1; 
                    else if (p1d > 0) {
                        // Since p1 is nonempty, it can be shown that only the leftmost candidate can yield an occurrence of p.
                        int mm = find_p_in_utx_left(h0 + aMin * tp);
                        nOcc = (mm == pd) ? 1: 0; }
                    else {
                        Assert(p3d > 0);
                        // Since p3 is nonempty, it can be shown that only the rightmost candidate can yield an occurrence of p.
                        int mm = find_p_in_utx_left(h0 + aMax * tp);
                        nOcc = (mm == pd) ? 1: 0; }
                }

                if constexpr (LotsOfChecks) {
                    // Compare the number of occurrences found by this function with the result obtained by a naive method.
                    int nOcc2 = 0; for (int h = 0; h < ud && h + pd <= ud + td + xd; ++h) {
                        if (h + pd <= ud + td) continue;
                        int m1 = find_p_in_utx_left(h);
                        if constexpr (false) printf(" (%d:%d)", h, m1);
                        int h2 = ud + td + xd - (h + pd);
                        int m2 = find_p_in_utx_right(h2);
                        if (m1 == pd) { Assert(m2 == pd); ++nOcc2; }
                        else Assert(m2 < pd); }
                    if (nOcc != nOcc2) printf("nOcc = %d or %d?  s = %s (sd = %d), k = %d; u = %s (ud = %d), t = %s, x = %s (xd = %d), p = %s (pd = %d)\n", nOcc, nOcc2, s.c_str(), (int) s.length(), k, string(u).c_str(), ud, t.c_str(), string(x).c_str(), xd, p.c_str(), pd);
                    Assert(nOcc == nOcc2);  }
                nOccAll += nOcc;
            }
        }; // TFibre

        // Initialize the fibres.  Each of them will count the occurrences of p in s[:k] t s[k:] for one value of k.
        vector<TFibre> fibres; fibres.reserve(sd);
        for (int k = 1; k < sd; ++k) fibres.emplace_back(captureHelper, k);
        vector<TAncestorQuery> ancQueries; ancQueries.reserve(sd);
        TAncestorQueryProcessor *aqp = nullptr;
        // Count early occurrences.
        for (int nIter = 0; ; ++nIter)
        {
            ancQueries.clear();
            // Let each fibre do its work.
            for (int fi = 0; fi < (int) fibres.size(); ++fi) {
                auto &F = fibres[fi]; F.CountEarlyOccurrences();
                // Set up an ancestor query to calculate the new, shorter length of u.
                if (F.ud > pd / 4) ancQueries.emplace_back(fi, F.ud, (F.ud - 1) / 2); }
            if (ancQueries.empty()) break;
            Assert(nIter < 2);
            // How to do a batch of these O(s) ancestor queries in only O(s + p) time?  
            // [GG22] (lemma 2.2 and sec. 4) achieves this with weighted ancestor queries in the suffix tree, 
            // which is very complicated.  We'll use a much simpler solution using disjoint-set unions
            // in the KMP tree.  
            if (! aqp) { // Initialize the ancestor query procesor (AQP) if needed.
                if (method == TMethod::NearlyLinear) aqp = new TAncestorQueryProcessor_NearlyLinear(pST);
                else aqp = new TAncestorQueryProcessor_Linear(pST); }
            aqp->Query(ancQueries);
            if (nIter == 1) { delete aqp; aqp = nullptr; }
            if constexpr (LotsOfChecks) for (auto &Q : ancQueries)
            {
                int ud = Q.u; int udNext = (ud - 1) / 2; Assert(Q.upperBound == udNext);
                do { ud = pST[ud]; } while (ud > udNext);
                Assert(ud == Q.answer);
            }
            for (auto &Q : ancQueries) fibres[Q.queryIdx].ud = Q.answer;
        }
        if (aqp) { delete aqp; aqp = nullptr; } // Clean up the AQP (later we'll need a new one based on p^R instead of p).
        // Count late occurrences.
        vector<int> fForXdAncQueries(pd + 1); for (int xd = 0; xd <= pd; ++xd) fForXdAncQueries[xd] = pd - pPT[pd - xd];
        for (int nIter = 0; ; ++nIter)
        {
            ancQueries.clear();
            // Let each fibre do its work.
            for (int fi = 0; fi < (int) fibres.size(); ++fi) {
                auto &F = fibres[fi]; F.CountLateOccurrences();
                // Set up an ancestor query to calculate the new, shorter length of x.
                if (F.xd > pd / 4) ancQueries.emplace_back(fi, F.xd, (F.xd - 1) / 2); }
            if (ancQueries.empty()) break;
            Assert(nIter < 2);
            // Do a batch of queries in linear (or near-linear) time, same as above.
            if (!aqp) {
                if (method == TMethod::NearlyLinear) aqp = new TAncestorQueryProcessor_NearlyLinear(fForXdAncQueries);
                else aqp = new TAncestorQueryProcessor_Linear(fForXdAncQueries); }
            aqp->Query(ancQueries);
            if (nIter == 1) { delete aqp; aqp = nullptr; }
            if constexpr (LotsOfChecks) for (auto &Q : ancQueries)
            {
                int xd = Q.u; int xdNext = (xd - 1) / 2; Assert(Q.upperBound == xdNext);
                do { xd = pd - pPT[pd - xd]; } while (xd > xdNext);
                Assert(xd == Q.answer);
            }
            for (auto &Q : ancQueries) fibres[Q.queryIdx].xd = Q.answer;
        }
        if (aqp) { delete aqp; aqp = nullptr; }
        // Count the remaining occurrences and store the solutions.
        for (auto &F : fibres)
        {
            F.CountRemainingOccurrences();
            if (F.nOccAll_ >= 0) Assert(F.nOccAll == F.nOccAll_);
            solutions[F.k] += F.nOccAll;
        }
    }
    else 
        Assert(false); // invalid 'method' parameter
} // Solve

// A very simple cubic-time solution of the same problem.  O(s (s + t) p) time.
void SolveNaive(const string &s, const string &t, const string &p, vector<int> &solutions)
{
    const int sd = s.length(), td = t.length(), pd = p.length();
    const int wd = sd + td; string w; w.resize(wd); 
    solutions.resize(sd + 1);
    for (int k = 0; k <= sd; ++k)
    {
        // Let w := s[:k] t s[k:].
        for (int i = 0; i < k; ++i) w[i] = s[i];
        for (int i = 0; i < td; ++i) w[k + i] = t[i];
        for (int i = k; i < sd; ++i) w[i + td] = s[i];
        // Count the occurrences of p in w.
        int count = 0;
        for (int i = 0; i + pd <= wd; ++i)
        {
            int j = 0; while (j < pd && w[i + j] == p[j]) ++j;
            if (j >= pd) ++count;
        }
        solutions[k] = count;
    }
}

// Tests that the various solutions give the same results on (s, t, p).
void TestSolve(const string &s, const string &t, const string &p)
{
    vector<int> sol1, sol2;
    // Start with the linear method.
    Solve(s, t, p, sol1, TMethod::Linear);
    // If the strings are short enough, compare the results with the naive cubic method. 
    if (s.size() <= 500 && p.size() <= 500 && t.size() <= 500) 
    {
        SolveNaive(s, t, p, sol2);
        for (int k = 0, sd = (int) s.size(); k <= sd; ++k) 
        {
            if (sol1[k] != sol2[k]) { fprintf(stderr, "s = \"%s\", t = \"%s\", p = \"%s\", sol[%d] = %d or %d\n", 
                s.c_str(), t.c_str(), p.c_str(), k, sol1[k], sol2[k]); fflush(stderr); }
            Assert(sol1[k] == sol2[k]);
        }
    }
    // Try the other methods supported by 'Solve'.
    if (true)
    {
        int sd = (int) s.size();
        { vector<int> sol3; Solve(s, t, p, sol3, TMethod::Quadratic); Assert(int(sol3.size()) == sd + 1); for (int k = 0; k <= sd; ++k) Assert(sol1[k] == sol3[k]); }
        { vector<int> sol3; Solve(s, t, p, sol3, TMethod::NSqrtN); Assert(int(sol3.size()) == sd + 1); for (int k = 0; k <= sd; ++k) Assert(sol1[k] == sol3[k]); }
        { vector<int> sol3; Solve(s, t, p, sol3, TMethod::NLogN); Assert(int(sol3.size()) == sd + 1); for (int k = 0; k <= sd; ++k) Assert(sol1[k] == sol3[k]); }
        { vector<int> sol3; Solve(s, t, p, sol3, TMethod::NearlyLinear); Assert(int(sol3.size()) == sd + 1); for (int k = 0; k <= sd; ++k) Assert(sol1[k] == sol3[k]); }
    }
}

// Let M = max(|s|, |t|, |p|) and L = |s| + |t| + |p|.
// This function generates (and tests) all possible test cases where s, t, p are from {'a', 'b'}*
// in increasing order of M and then in increasing order of L.
void TestSolve()
{
    for (int M = 1; ; ++M) // M = max{|s|, |t|, |p|}
    for (int L = 3; L <= 3 * M; ++L) // L = |s| + |t| + |p|
    for (int sd = 1; sd <= M && sd + 2 < L; ++sd) for (int td = 1; td <= M && sd + td < L; ++td) // for (int pd = td; pd <= M; ++pd)
    {
        int pd = L - sd - td; if (pd < td || pd > M) continue;
        if (max(sd, max(td, pd)) < M) continue;
        string s, t, p; s.resize(sd); t.resize(td); p.resize(pd);
        printf("M = %d, L = %d: |s| = %d, |t| = %d, |p| = %d      \n", M, L, sd, td, pd); fflush(stdout);
        for (int sb = 0; sb < (1 << sd); ++sb)
        {
            for (int i = 0; i < sd; ++i) s[i] = 'a' + ((sb >> i) & 1);
            for (int tb = 0; tb < (1 << td); ++tb)
            {
                for (int i = 0; i < td; ++i) t[i] = 'a' + ((tb >> i) & 1);
                for (int pb = 0; pb < (1 << pd); ++pb)
                {
                    for (int i = 0; i < pd; ++i) p[i] = 'a' + ((pb >> i) & 1);
                    TestSolve(s, t, p);
                }
            }
        }
    }
}

// The multi-threaded version of the previous function.
// If nThreads is < 0, the function will use thread::hardware_concurrency() to choose the number of threads.
void TestSolveMt(int nThreads = 10)
{
    if (nThreads < 0) nThreads = thread::hardware_concurrency();
    for (int M = 1; ; ++M)
    for (int L = 3; L <= 3 * M; ++L)
    for (int sd = 1; sd <= M && sd + 2 < L; ++sd) for (int td = 1; td <= M && sd + td < L; ++td) // for (int pd = td; pd <= M; ++pd)
    {
        int pd = L - sd - td; if (pd < td || pd > M) continue;
        if (pd > sd + td) continue;
        if (max(sd, max(td, pd)) < M) continue;
        printf("[%d threads] M = %d, L = %d: |s| = %d, |t| = %d, |p| = %d      \n", nThreads, M, L, sd, td, pd); fflush(stdout);

        auto ThreadFunc = [sd, td, pd] (long long int from, long long int to)
        {
            string s, t, p; s.resize(sd); t.resize(td); p.resize(pd);
            for (long long int x = from; x < to; ++x)
            {
                long long int xx = x;
                for (int i = 0; i < sd; ++i) { s[i] = 'a' + (xx & 1); xx >>= 1; }
                for (int i = 0; i < td; ++i) { t[i] = 'a' + (xx & 1); xx >>= 1; }
                for (int i = 0; i < pd; ++i) { p[i] = 'a' + (xx & 1); xx >>= 1; }
                TestSolve(s, t, p);
            }
        };

        Assert(sd + td + pd == L);
        long long int nCases = 1LL << (sd + td + pd);
        // Divide the 2^L test cases evenly amongst the threads.
        vector<thread> threads;
        for (int i = 0; i < nThreads; ++i) threads.emplace_back(ThreadFunc, (nCases * i) / nThreads, (nCases * (i + 1)) / nThreads);
        // Wait for all the threads to finish running.
        for (auto &thread : threads) thread.join();
    }
}

int PrintExample(const string &s, const string &t, const string &p)
{
    // Print the input strings.
    printf("s = \"%s\"\nt = \"%s\"\np = \"%s\"\n|s| = %d, |t| = %d, |p| = %d\n",
        s.c_str(), t.c_str(), p.c_str(), int(s.length()), int(t.length()), int(p.length()));
    // Calculate the solutions.
    vector<int> solutions; Solve(s, t, p, solutions);
    // Print the solutions.
    printf("solutions = [");
    bool first = true;
    for (int sol : solutions) { printf("%s%d", (first ? "" : ", "), sol); first = false; } 
    printf(" ]\n"); return 0;
}

// Reads s, t and p from the standard input and outputs the solutions
// to the standard output.
int mainStdin()
{
    string s, t, p; cin >> s >> t >> p;
    return PrintExample(s, t, p);
}

int main(int argc, char **argv)
{
    if (false) return PrintExample("aabab", "aba", "aab"); // results: [1, 2, 1, 2, 2, 1]
    if (false) return mainStdin();
    // Most of these test functions run in an infinite loop and will cause
    // an assertion failure if they detect an error.
    if (false) { TestBuildSuffixTable(); return 0; }
    if (false) { TestBuildSuffixTable2(); return 0; }
    if (false) { TestBuildOccCounts(); return 0; }
    if (false) { TestBuildPrefixTable(); return 0; }
    if (false) { TestBuildPrefixTable2(); return 0; }
    if (false) { TestBuildPrefixTable2B(); return 0; }
    if (false) { TestBuildSuffixTable2B(); return 0; }
    if (false) { TestStaticTreeSetUnion(); return 0; }
    if (false) { TestSolve(); return 0; }
    if (true) { TestSolveMt(argc > 1 ? atoi(argv[1]) : 10); return 0; }
    return 0;
}