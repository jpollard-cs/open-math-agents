# Gluing at a binary digit and a second digit

Codex (OpenAI). AI-authored written research on the unique-hole reduction of Erdős #1189.

Two or more branches have disjoint private coordinates and share only a separator with alphabets of sizes $2$ and $q\ge2$. A branch's assignments may be changed independently, including independent permutations of the labels at each separator digit. Rows testing only separator digits are allocated once. At a boundary cell record its number of private continuations truncated to $0,1,2$ (two means at least two). The joint count at a cell is the truncated product; the total is the truncated sum. A local list is rigid when every assignment leaves at least one survivor, some leaves exactly one, and after deleting any row every assignment leaves at least two.

**Exact two-branch criterion.** Each branch assignment gives a multiset of $q$ ordered column types in $\{0,1,2\}^2$. Retain the attainable multisets, repeating after each individual deletion. Test both relative orders of the binary labels. For one pair of multisets in a fixed order let $a_0,a_1,a_2,a_3$ count columns of the first profile with positive-entry masks empty, top alone, bottom alone, both. Define $b_i$ alike for the second profile. A boundary matching giving **zero** joint survivors exists exactly when
$$
 a_3\le b_0,\qquad
 a_3+a_1\le b_0+b_2,\qquad
 a_3+a_2\le b_0+b_1,\qquad
 b_3\le a_0.
$$
A matching giving **exactly one** exists precisely when some available pair of marked column types has ordinary dot product one and the four inequalities hold after subtracting that column from each multiset. These tests decide rigidity with unrestricted reassignment. For the intact lists require zero impossible for every pair and orientation and one attainable for at least one. In each deletion require both zero and one impossible for every resulting pair and orientation. Thus even for unknown interior supports, the boundary comparison cost for each unordered-column profile pair is bounded independently of $q$, counting arithmetic operations on multiplicities.

Indeed a zero matching pairs columns of disjoint positive masks. Apply Hall's theorem: the full mask can go only to mask zero, top to zero or bottom, and bottom to zero or top. The set of all nonempty left masks can go only to the non-full right masks. These four inequalities are necessary. For sufficiency take any subset of left columns. If it includes an empty mask, its neighborhood is all columns. Otherwise bound its size by the inequality for the singleton types present, including the full type in the bound regardless of presence. When both singleton types occur their union has all non-full neighbors. This exhausts Hall's conditions. A total of one has exactly one contributing pair of columns with dot product one and all other pairs have zero. The independent permutations at the two digits allow exactly the tested relative orientations and column bijections.

This is a specialization of Hall's marriage theorem and of bipartite graph packing under part-preserving relabelings. The markers are needed for unique continuations and for deletion tests. [Hall, *On representatives of subsets*](https://doi.org/10.1112/jlms/s1-10.1.26) · [Bipartite graph packing, Definition 3.8](https://www.cs.dartmouth.edu/~ac/Pubs/rsa-randglb.pdf)

For multiple branches, the full nine-type boundary profile composes exactly. For two profiles enumerate nonnegative integer $9\times9$ tables whose row and column sums are the two multiplicity vectors. In one table, a unit in entry $u,v$ gives a column of type $\min(2,u\cdot v)$ where multiplication and truncation here are **coordinatewise**. Sum these multiplicities, try the two orientations, and retain every resulting profile. Every table is realizable by a column bijection. Iterate and perform the same procedure after one deletion. For fixed binary width the number of profiles and transportation tables is polynomial in $q$ (a crude bound for tables is $(q+1)^{81}$). Interior profile generation is a separate task. Treating the $2q$ cells as freely permutable already fails for two full rows versus a row and a full column: the former can be put on opposite sides and the latter always intersect.

## A branch-count obstruction before computing any profiles

Call a branch active if one of its assignments excludes at least one boundary cell (leaves zero continuations there). Let $t$ be the number of active branches and $s$ the number capable of excluding two distinct cells in the same assignment. If **every** global assignment has a survivor, then
$$
                 t+\min(s,q-1)\le 2q-1.
$$
In particular for $t\ge q+1$ one must have $t+s\le2q-1$. In an actual strongly connected digit component, each nontrivial private component after removing the separator is active. Indeed if it could never exclude a boundary cell, all other branches alone admit only the distinguished boundary cell in the singleton witness. A row of this private branch disagreeing there on a tested separator digit would be freely deletable in that witness. Consequently no private-branch row has a nonzero requirement at a separator digit. There is no arrow from the separator into the private component, contrary to strong connectivity. Here a distinguished value at each digit is called zero, as in the [component construction](component-surplus.md). Boundary-only rows can be treated as individual branches.

**Packing lemma.** A pair of distinct cells of the $2\times q$ grid has three possible types under independent relabelings: vertical, horizontal, or diagonal (different rows and columns). For given counts $v,h,d$ of the three types respectively, put $r=q-v$. A disjoint placement exists exactly when
$$
  v\le q,\quad d\le r,\quad h\le 2\lfloor(r-d)/2\rfloor,
  \quad (r,d)\ne(1,1).
$$
Reserve the vertical columns. Every diagonal uses one cell in each row, and each horizontal pair uses two in one row. This gives the necessary inequalities; a single remaining column cannot contain a diagonal. For sufficiency, when $d\ge2$ use the same $d$ columns in each row, shifting their endpoints cyclically. For $d=1$ use different columns, and for $d=0$ use none. There are $r-d$ free cells in each row, which realize the specified horizontal count.

In particular **any $q-1$ or fewer prescribed pair types** can be packed disjointly: $h\le r-d-1$ and the exceptional diagonal case cannot occur. Take $u=\min(s,q-1)$ branches able to exclude two cells. Permute their labels to pack one of their attainable pairs per branch. The other $t-u$ active branches can each exclude any specified single cell by transitivity. If $t+u\ge2q$, together they exclude the entire separator, a contradiction. For $q$ odd, $q$ horizontal pairs cannot tile, although $q-1$ always pack. This shows the boundary-packing threshold is exact. Whether a sharp boundary obstruction can also have unique *private* continuations in an irreducible integer construction is a further question.

[Independent finite verification](two-digit-separator-check.py). The four inequalities are exact for all $q$; the arithmetic component and asymptotic prime-expansion results are separate written arguments.
