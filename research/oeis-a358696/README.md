# Boundary-covering cycles in the five-row grid

Let $a(n)$, for $n\ge2$, count the simple undirected cycles in the graph with vertices
$\{0,1,2,3,4\}\times\{1,\ldots,n\}$ and edges between horizontally or vertically adjacent vertices, subject to the cycle visiting every vertex in the first and last rows and the first and last columns. A cycle is counted once as a set of edges in this fixed, labelled graph. Interior vertices may be omitted. This is Seiichi Manyama’s sequence A358696, first published on November 27, 2022, with offset 2. [Original entry](https://oeis.org/A358696) · [Archived source](https://github.com/oeis/oeisdata/blob/571197984aeda7b8b680fe3a1f6a43f9898cd441/seq/A358/A358696.seq)

**Theorem.** For every $n\ge11$,

$$
\begin{aligned}
a(n)={}&6a(n-1)+a(n-2)-20a(n-3)+37a(n-4)+16a(n-5)\\
      &-12a(n-6)-7a(n-7)+5a(n-8)-a(n-9).
\end{aligned}
$$

This proves the full conjecture in A358696. The ordinary generating function follows as a corollary.

## Cut the grid between consecutive columns

Imagine cutting each chosen horizontal edge between columns $j$ and $j+1$ at its midpoint. The half of the cycle in the first $j$ columns consists of disjoint paths. It cannot have a closed component because the required vertices in the last column still lie to the right. The endpoints of each path lie on the cut. Record their two row numbers as a pair. With five possible cut edges, a state is a matching of two or four occupied positions. Planarity rules out interlaced pairs. There are precisely ten one-pair possibilities and two noncrossing matchings for each of the five sets of four positions. These are the 20 states in the table below.

Here is the full rule for adding one column. A subset $V\subseteq\{0,1,2,3\}$ selects its vertical edges, with $i\in V$ joining rows $i$ and $i+1$. A subset $R\subseteq\{0,1,2,3,4\}$ selects the horizontal edges leaving the column. Write $L$ for the union of the incoming pairs. At row $i$ the degree after this choice is

$$
  [i\in L]+[i\in R]+[i-1\in V]+[i\in V].
$$

In an interior column, require degree two in rows 0 and 4 and degree zero or two in the remaining rows. In either end column, require degree two at all five rows. Out-of-range positions never belong to a subset.

The connectivity test uses just five row positions. Take the positions of positive degree as vertices of a temporary graph. Join the positions in each incoming pair and join the positions of each chosen vertical edge. In a nonfinal column, every component must contain exactly two members of $R$. The new state pairs these two members in each component. In the first column start with the empty incoming matching. In the final column require $R=\varnothing$ and exactly one component.

To see why this is sufficient, expand each incoming pair back into the actual path through earlier columns, and attach the new edges. After the degree test each component is either a path with its endpoints at outgoing cut midpoints or a closed cycle. The temporary graph preserves these components even if an incoming path has the same two endpoint rows as a chosen vertical edge. The condition on outgoing positions is therefore exactly the condition that every component stays open until the final column. At the final column, a connected nonempty finite graph in which every used vertex has degree two is one simple cycle. Conversely, every permissible cycle specifies unique sets $V,R$ in every column. The procedure thus counts each admissible edge set exactly once, including a cycle and its reverse as a single object.

## The transfer table

In the following table, `01 24` means the two pairs $(0,1),(2,4)$. An entry in the last column gives a permissible destination index for one interior column. Each listed destination has multiplicity one. The letters label classes used in the next step.

| Index | Pairs | Class | Destinations |
|---:|:---|:---:|:---|
| 0 | 01 | A | 2, 3, 5, 8 |
| 1 | 01 23 | B | 2, 8 |
| 2 | 01 24 | C | 1, 2, 3, 6, 8 |
| 3 | 01 34 | A | 2, 3, 5, 8 |
| 4 | 02 | C | 3, 5, 8, 13, 15 |
| 5 | 02 34 | C | 3, 5, 8, 13, 15 |
| 6 | 03 | D | 8, 9, 15, 18 |
| 7 | 03 12 | E | 9, 18 |
| 8 | 04 | F | 0, 4, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 17, 18, 19 |
| 9 | 04 12 | G | 0, 7, 9, 10, 17, 18, 19 |
| 10 | 04 13 | H | 0, 4, 9, 10, 11, 18, 19 |
| 11 | 04 23 | G | 0, 4, 10, 11, 12, 16, 19 |
| 12 | 12 | B | 5, 8 |
| 13 | 12 34 | B | 5, 8 |
| 14 | 13 | I | 8 |
| 15 | 14 | D | 4, 6, 8, 11 |
| 16 | 14 23 | E | 4, 11 |
| 17 | 23 | B | 2, 8 |
| 18 | 24 | C | 1, 2, 3, 6, 8 |
| 19 | 34 | A | 2, 3, 5, 8 |

For the first column precisely the states 2, 5 and 8 each occur once. Its vertical edges have to partition the five rows into intervals of length at least two, and each interval contributes its two endpoints. For the final column, the three choices for this same interval partition are available by reflection. The unique closing choices occur for incoming states 8, 9 and 11. For example, the sole two-stub closure uses state 8 and the full vertical path. A four-stub closure joins the two incoming paths into one component using the other noncrossing pairing of the same four stubs. These observations also give $a(2)=1$.

The table is a finite enumeration by the degree and connectivity tests above. One reproducible procedure for any row is the following pseudocode. Each repeated outgoing state counts as a separate transition before multiplicities are recorded.

```text
for each of the 16 vertical subsets V:
  for each of the 32 outgoing subsets R (only the empty subset if final):
    compute the five degrees and discard if a required degree fails
    initialize one singleton component for each row of positive degree
    merge the two components incident with each incoming pair and each edge in V
    if final:
      count one closure if there is exactly one component
    else:
      intersect every component with R
      if every intersection has size two, count the matching of these pairs
```

## Why the recurrence has order nine

For each row of the transfer table, count its destinations in each of the classes A through I. Rows in the same class have the same nine counts. The resulting matrix $B$, with row the incoming class and column the outgoing class, is

$$
\begin{pmatrix}
1&0&2&0&0&1&0&0&0\\
0&0&1&0&0&1&0&0&0\\
1&1&1&1&0&1&0&0&0\\
0&0&1&1&0&1&1&0&0\\
0&0&1&0&0&0&1&0&0\\
2&2&2&2&2&1&2&1&1\\
2&1&1&0&1&0&1&1&0\\
2&0&2&0&0&0&2&1&0\\
0&0&0&0&0&1&0&0&0
\end{pmatrix}.
$$

Writing $e_X$ for the corresponding column coordinate vector, the starting row vector is $s=2e_C^{\mathsf T}+e_F^{\mathsf T}$ and the closing column vector is $t=e_F+e_G$. Every state in class G has exactly one closure. By induction, the number of completions with $k$ interior columns remaining is constant on each class and is the corresponding entry of $B^k t$. Consequently

$$
a(n)=sB^{n-2}t\quad(n\ge2).
$$

The characteristic polynomial of $B$ is

$$
P(z)=z^9-6z^8-z^7+20z^6-37z^5-16z^4+12z^3+7z^2-5z+1.
$$

For a short integer certificate, direct multiplication of the displayed matrix gives the traces of its first nine positive powers as

$$
6,\ 38,\ 174,\ 1110,\ 6376,\ 37316,\ 214997,\ 1243174,\ 7179060.
$$

With $d_0=1$, Newton’s identities $j d_j=-\sum_{i=1}^j d_{j-i}\operatorname{tr}(B^i)$ give the coefficients $d_j$ of $z^{9-j}$ in $P$. Cayley–Hamilton now yields $P(B)=0$. For $n\ge11$ multiply this identity on the left by $sB^{n-11}$ and on the right by $t$. The term $B^9$ gives $a(n)$, and the constant term gives $a(n-9)$, proving the claimed recurrence over its entire stated range.

## Initial values and generating function

Directly applying $sB^kt$ for $0\le k\le8$ gives the nine required initial counts, in widths 2 through 10,

$$
1,\ 5,\ 36,\ 191,\ 1123,\ 6410,\ 37165,\ 214515,\ 1240200.
$$

The first recurrence case is $a(11)=7165033$. A one-column grid is a path with no cycle and lies outside the OEIS indexing. Multiplying the power series by the reciprocal characteristic polynomial and using the nine initial values yields

$$
\sum_{n\ge2}a(n)x^n
=\frac{x^2(1-x+5x^2-10x^3+4x^4+2x^6-x^7)}
 {1-6x-x^2+20x^3-37x^4-16x^5+12x^6+7x^7-5x^8+x^9}.
$$

This fraction is in lowest terms, so order nine is also minimal among eventual constant-coefficient recurrences over the rationals. Indeed, the denominator has constant term one. Divide it by the numerator with its factor $x^2$ removed, and continue the Euclidean algorithm modulo 5. The successive nonzero remainders, in increasing order of degree within each polynomial, are $2+3x^2+4x^3+2x^4+2x^5+3x^6$, $2+3x+4x^2+3x^3+3x^4$, and $1$. Both original leading coefficients are units modulo 5, so a common rational factor of positive degree would survive reduction. Any eventual rational-coefficient recurrence supplies a denominator for the same generating function and must therefore have order at least nine.

## Lean verification

Lean 4.33.1 verifies the recurrence for the grid cycles defined in the statement, for every width $n\ge11$. The proof constructs a bijection between admissible edge sets and accepted column sequences. The vertical edges determine the horizontal edges. Tracking which pairs of rows are connected gives the transfer table, and its integer matrix gives the recurrence. The project checker accepted `OMA.solution` with the three audited axioms `propext`, `Classical.choice`, and `Quot.sound`. [Complete Lean proof](https://github.com/taloscoreagent/open-math-agents/blob/8c99f5022baa6499a4a32dbb95badd6c89ee4ff4/proofs/oeis-a358696.lean) · [Graph-theoretic statement](../../statements/oeis-a358696.lean)

To reproduce the audit in a fresh clone of the Talos fork, check out the proof commit and run the project's checker with its pinned toolchain.

```sh
git checkout 8c99f5022baa6499a4a32dbb95badd6c89ee4ff4
tools/oma.sh setup
tools/check.sh proofs/oeis-a358696.lean
```

The transfer calculation and the initial graph lemmas are also available in shorter files. [Transfer.lean](Transfer.lean) · [Grid.lean](Grid.lean)

## Independent checks and related work

A separate depth-first search rooted at the upper-left corner enumerated each cycle by taking its first step right and closing on the other neighbour of the corner. Keeping a visited-vertex set and checking all boundary vertices at closure gives 1, 5, 36, 191, 1123 and 6410 for widths 2 through 7. The transfer also reproduces all 49 values in Manyama’s table for widths 2 through 50. His Python code generates these values by filtering Graphillion cycles for boundary-vertex membership. His PARI/GP file implements the conjectural recurrence directly from the nine seeds. [Manyama’s full table](https://oeis.org/A358696/b358696.txt) · [Manyama’s Python enumeration](https://github.com/manman4/OEIS_03/blob/6f094f9609dc3655425c83170aa62ac61898d33f/358/358696/358696_01.py) · [Manyama’s PARI/GP conjecture](https://github.com/manman4/OEIS_03/blob/6f094f9609dc3655425c83170aa62ac61898d33f/358/358696/358696_01.gp)

The parent array A333758 was published by Manyama in 2020. Its four-row specialization has a fourth-order formula. Its six- and seven-row entries list counts. A particularly close precedent is Yiming Beckmann’s June 2026 proof sketch for Chai Wah Wu’s formula for five-row cycles required to visit the **four corners**. It uses 20 matching states. Permitting the other boundary vertices to be skipped gives seven cycles at width three and an order-eleven recurrence. In the present problem there are five cycles at width three, because all boundary vertices are required. [Manyama’s array](https://oeis.org/A333758) · [Four rows](https://oeis.org/A333760) · [Six rows](https://oeis.org/A358697) · [Seven rows](https://oeis.org/A358698) · [Beckmann’s proof sketch for four corners](https://github.com/oeis/oeisdata/blob/7e846541fdca87dc2be0b6324ea96e3057310a24/seq/A333/A333515.seq#L7)

Tracking connectivity across a cut is a standard method for enumerating lattice polygons. Clisby and Jensen treat square-lattice polygons by perimeter. Guttmann and Jensen study walks and polygons crossing lattice domains. Blanco and Zeilberger implement the transfer method of Stoyan and Strehl for Hamiltonian cycles, which must visit every vertex. These results provide methodological context. The sources reviewed did not supply the specific five-row, all-boundary order-nine identity. [Clisby and Jensen](https://arxiv.org/abs/1111.5877) · [Guttmann and Jensen](https://arxiv.org/abs/2208.06744) · [Blanco and Zeilberger](https://sites.math.rutgers.edu/~zeilberg/mamarim/mamarimhtml/volker.html)
