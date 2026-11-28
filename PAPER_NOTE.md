# A Three-Vertex Induced-Path Overlap Argument for $K_4$-Free Erdős Problem #151 ($H(n) = 11$, $n \le 52$)

## Theorem (Formalized in Lean 4)

Assuming $R(3,8) \le 28$, every $K_4$-free graph $G$ on $n$ vertices with $H(n) = 11$ (hence $47 \le n \le 52$, using $R(3,11) \ge 47$ and $R(3,12) \ge 53$) satisfies
$$\tau(G) \le n - 11,$$
where $\tau(G)$ is the clique transversal number of $G$.

## Proof Sketch

Let $G$ be a $K_4$-free graph on $n \ge 47$ vertices with $H(n) = 11$ and maximum degree $\Delta(G) \le 10$ (if some vertex $v$ has $\deg(v) \ge 11$, then $N_G(v)$ is triangle-free of size $\ge 11$, giving $\tau(G) \le n - 11$ immediately).

1. **Minimal arrowing subgraph.** If $G$ admits a red/blue edge coloring with no monochromatic triangle, recoloring edges in no triangle red yields a triangle-free red spanning subgraph, which has an independent set of size $H(n) = 11$; that set is triangle-free in $G$ (since every triangle of $G$ has a red edge), so $\tau(G) \le n - 11$.
   Otherwise, let $F \le G$ be a subgraph-minimal $(3,3)$-arrowing subgraph. By Bikov's 7-vertex link-extension lemma (proved in pure kernel Lean 4), every non-isolated vertex $v$ of $F$ has $\deg_F(v) \ge 8$, and every edge $uv \in E(F)$ lies in at least $2$ triangles of $F$.

2. **Three-vertex induced-path anchors.** For each $v$, let $P_v = \{x \in N_G(v) : \exists z,\, G.\text{Adj } v\,z \land G.\text{Adj } x\,z\}$ be the triangle-link of $v$ (which is triangle-free since $G$ is $K_4$-free), and let $s_{uv} = |N_G(u) \cap N_G(v)|$.
   - **Case 1 ($\exists b \in V(F)$ with $\alpha(P_b) \ge 4$).** Pick an independent 4-set $B \subseteq P_b$. Since $|N_F(b)| \ge 8$ and $|P_b| \le 10$, $|B \cap N_F(b)| \ge 2$, giving two distinct non-adjacent $F$-neighbors $a, c \in B \cap N_F(b)$ (so $a - b - c$ is an induced path!). For $v \in \{a, c\}$, if $s_{vb} \ge 4$ take $I_v = \{b\}$ (giving $|I_v| + s_{vb} \ge 5$); if $s_{vb} \le 3$, then $b$ has $\le 3$ neighbors in $P_v$ ($|P_v| \ge 8$), so $b$ has $\ge 4$ non-neighbors in $P_v$, which contain a non-adjacent pair (since $P_v$ is triangle-free), giving an independent 3-set $I_v \subseteq P_v$ containing $b$ with $|I_v| + s_{vb} \ge 3 + 2 = 5$. Thus $|A| + |B| + |C| + s_{ab} + s_{bc} \ge 4 + 5 + 5 = 14$.
   - **Case 2 ($\alpha(P_v) \le 3$ for all $v \in V(F)$).** Since $R(3,4) = 9$, $|P_v| \le 8$, so $|P_v| = 8$ and $N_F(v) = P_v$ for every $v \in V(F)$. Every $y \in P_b$ has $\ge 2$ neighbors in $P_b$ (since every $F$-edge lies in $\ge 2$ $F$-triangles). No 2-regular triangle-free 8-vertex graph has $\alpha \le 3$ (fixing any $x$ and its 5 non-neighbors $W$, every $w \in W$ must have $\ge 2$ neighbors in $W$ else $W$ extends $\{x,w\}$ to an independent 4-set, leaving the 2 neighbors of $x$ isolated from $W$ and each other — contradiction!). Hence some $a \in P_b$ has $s_{ab} \ge 3$. Taking independent 3-sets $B \subseteq P_b$ containing $a$ (and some second vertex $c \in B \setminus \{a\}$), $A \subseteq P_a$ containing $b$, and $C \subseteq P_c$ containing $b$ gives $|A| + |B| + |C| + s_{ab} + s_{bc} \ge 3 + 3 + 3 + 3 + 2 = 14$.

3. **Overlap deletion & extension from 28.** Set $D_a = N_G(a) \setminus A$, $D_b = N_G(b) \setminus B$, $D_c = N_G(c) \setminus C$, and $D = \{a, b, c\} \cup D_a \cup D_b \cup D_c$. Every common neighbor of $a, b$ is adjacent to both $b \in A$ and $a \in B$, so it lies in $D_a \cap D_b$; hence $s_{ab} \le |D_a \cap D_b|$ and similarly $s_{bc} \le |D_b \cap D_c|$. Therefore:
   $$|D| \le 3 + (|N_G(a)| - |A|) + (|N_G(b)| - |B|) + (|N_G(c)| - |C|) - s_{ab} - s_{bc} \le 3 + 30 - 14 = 19.$$
   Hence $|V(G) \setminus D| \ge 47 - 19 = 28$. On any 28-vertex subset $W \subseteq V(G) \setminus D$, either some vertex has degree $\ge 8$ in $G[W]$ (giving 8 triangle-free vertices in its neighborhood) or $G[W]$ is 7-degenerate, hence 2-colorable without monochromatic triangles by Bikov's lemma, and applying $R(3,8) \le 28$ to the red subgraph yields an 8-vertex triangle-free set $T \subseteq W$. Adding $\{a, b, c\}$ back produces an 11-vertex triangle-free set $T \cup \{a, b, c\}$ (any triangle containing an anchor $w \in \{a, b, c\}$ would have two vertices in $N_G(w) \setminus D \subseteq I_w$, impossible since $I_w$ is independent). Thus $\tau(G) \le n - 11$. $\square$

---

# A Four-Anchor Star / Cubic-Link $C_4$ Argument for $H(n) = 12$ ($n \ge 54$, Isolating $n = 53$)

## Theorem (Formalized in Lean 4 — [PR #19010](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/19010))

Assuming $R(3,8) \le 28$, $R(3,12) \ge 53$, Bikov's 7-vertex link-extension lemma, and Seymour's triangle-count bound $T(F) \ge |E(F)|$ for minimal $(3,3)$-arrowing graphs, every $K_4$-free graph $G$ on $n \ge 54$ vertices with $H(n) = 12$ satisfies
$$\tau(G) \le n - 12.$$
In particular, within the entire $H(n) = 12$ band ($53 \le n \le 59$), **order $n = 53$ is the unique remaining case** (and would be eliminated outright by $R(3,12) \ge 54$).

## Proof Sketch

Suppose $\Delta(G) \le 11$, $H(n) = 12$, $n \ge 54$, and take a subgraph-minimal $(3,3)$-arrowing subgraph $F \le G$. Then $\delta(F) \ge 8$, every $F$-edge lies in at least $2$ $F$-triangles, and $T(F) \ge |E(F)|$ by Seymour's theorem. Write $Q_b = G[N_F(b)]$ and $s_{ab} = |N_G(a) \cap N_G(b)|$. For any $a \in N_F(b)$, there is an independent set $I_a \subseteq P_a$ containing $b$ with $|I_a| + s_{ab} \ge 5, 6, 7$ when $d_{Q_b}(a) \ge 2, 3, 4$ respectively.

For any independent $I_b \subseteq Q_b$ containing three leaves $a, c, d$, deleting $D = \{b, a, c, d\} \cup \bigcup_{v \in \{b,a,c,d\}} (N_G(v) \setminus I_v)$ counts all three star-edge overlaps without overcounting, giving
$$|D| \le 48 - \left(|I_b| + \sum_{x \in \{a,c,d\}} (|I_x| + s_{bx})\right).$$

- **Case 1 (Star sum $\ge 22$).** Then $|D| \le 26$, leaving $\ge 54 - 26 = 28$ vertices; $R(3,8) \le 28$ + Bikov $k \le 7$ yields $8$ triangle-free vertices in $G - D$, and adding the $4$ star anchors back gives $12$ triangle-free vertices.
- **Case 2 (Every star sum $< 22$).** Applying the weight table to the neighborhood of each vertex in $Q_b$ shows $d \le 6$ and $2n_4 + 4n_5 + 6n_6 \le 2n_2$, i.e. $2|E(Q_b)| \le 3|V(Q_b)|$. Meanwhile Seymour's bound gives $\sum_b |E(Q_b)| \ge 3T(F) \ge 3|E(F)| = \frac{3}{2}\sum_b |V(Q_b)|$. Equality holds everywhere: every link equals its $F$-link, no degree-2 edge can survive (its triangle neighbor would force two adjacent degree-$\ge 4$ vertices in a link), so **every link is 3-regular on 8 vertices with $\alpha \le 3$**.
  - Any 3-regular triangle-free 8-vertex graph contains an **induced $C_4$ square** $a - b - c - e - a$ (otherwise $1 + 3 + 6 = 10 > 8$).
  - At each square vertex $w$, its two square neighbors extend to an independent triple $I_w \subseteq N_F(w)$ (if their link-neighborhoods were disjoint, one vertex plus the other's 3 neighbors would be an independent 4-set; if they intersect, $\le 5$ vertices are covered, leaving $\ge 1$ of the other 6 vertices).
  - Each of the 4 square edges lies in $3$ $F$-triangles, giving overlap savings $12 - \mu$, where $\mu = |S_a \cap S_b \cap S_c \cap S_e|$ counts common neighbors of all four anchors. We have $\mu \le 2$: if $\mu = 3$, then in $N_F(a)$, $b$ and $e$ share the same $3$ neighbors, and the remaining $3$ vertices of $N_F(a)$ contain a non-adjacent pair forming an independent 4-set with $\{b, e\}$, contradicting $\alpha \le 3$.
  - Hence $|D| \le 4 + 4(11 - 3) - (12 - 2) = 26$, leaving $\ge 28$ vertices and closing all $n \ge 54$. $\square$

---

