# Formalized Progress on $K_4$-Free Erdős Problem #151 ($H(n) \le 12$ for $n \neq 53$)

Pure-kernel Lean 4 + Mathlib formalizations (verified against `google-deepmind/formal-conjectures` commit `9097e2f90e`, Lean `4.33.1`, with `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`, zero `sorry`, zero `axiom`, zero `bv_decide`/`native_decide`) for the $K_4$-free variant of **Erdős Problem #151** (`Erdos151.erdos_151.variants.cliqueFree_four`):

> For every $K_4$-free graph $G$ on $n$ vertices, does the clique transversal number satisfy $\tau(G) \le n - H(n)$, where $H(n)$ is the largest $k$ such that every triangle-free graph on $n$ vertices has an independent set of size $k$?

## Main Mathematical Contributions

We formalize two new computer-free overlap reductions that push the $K_4$-free Erdős Problem #151 frontier from $H(n) \le 10$ ($n \le 46$) all the way through **$H(n) \le 12$ for all $n \neq 53$** (closing all $n \le 52$ and all $54 \le n \le 59$, isolating the single order $n = 53$ and reducing the remaining open problem to $(H(n)=12, n=53)$ or $H(n) \ge 13$, i.e., $n \ge 60$):

### What Is Prior vs. What Is New
- **Prior results (formalized here as pure-kernel Lean proofs/lemmas):**
  - Bikov's 7-vertex triangle-free link-extension lemma ($k \le 7$), giving $\delta(F) \ge 8$ in a subgraph-minimal $(3,3)$-arrowing subgraph $F \le G$.
  - Single-vertex and adjacent-pair neighborhood deletion ($H(n) \le 10$, $n \le 46$).
  - Classical Ramsey bounds: $R(3,6) \le 18$ (**proved here in pure Lean 4 kernel** via bitmask `rfl` certificates!), $R(3,9) \ge 36$ (Kalbfleisch), $R(3,10) \ge 40$ and $R(3,11) \ge 47$ (Exoo's `g310.39` and `g.3.11.46`), and $R(3,8) \le 28$ (McKay & Min 1992).
- **New Step 1 ($H(n) = 11$, $n \le 52$ — [PR #10252](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10252), merged):**
  - In a subgraph-minimal arrowing subgraph $F \le G$ ($\delta(F) \ge 8$, every $F$-edge in $\ge 2$ $F$-triangles, $\Delta(G) \le 10$, $n \ge 47$), we construct a **three-vertex induced path** $a - b - c$ together with independent link-sets $A \subseteq P_a$, $B \subseteq P_b$, $C \subseteq P_c$ ($b \in A$, $a, c \in B$, $b \in C$) satisfying $|A| + |B| + |C| + s_{ab} + s_{bc} \ge 14$.
  - The 3-set overlap bound gives deletion cost $|D| \le 19$, leaving $\ge 47 - 19 = 28$ vertices; $R(3,8) \le 28$ + Bikov $k \le 7$ adds 8 vertices back to $\{a, b, c\}$ for an 11-vertex triangle-free set.
- **New Step 2 ($H(n) = 12$ for all $n \ge 54$, isolating $n = 53$ — [PR #19010](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/19010)):**
  - With $\Delta(G) \le 11$ and $n \ge 54$, we always find **4 free anchors** with deletion cost **at most $26$** (leaving $\ge 54 - 26 = 28$ vertices, so $4 + 8 = 12$):
    - **Case 1 (Star):** Pick an independent set $I_b \subseteq Q_b = G[N_F(b)]$ containing 3 leaves $a, c, d$ forming a $K_{1,3}$ star. Each leaf $x$ guarantees $|I_x| + s_{bx} \ge 5, 6, 7$ for $d_{Q_b}(x) \ge 2, 3, 4$. If any star has $|I_b| + \sum_{x \in \{a,c,d\}} (|I_x| + s_{bx}) \ge 22$, tree overlap gives $|D| \le 48 - 22 = 26$.
    - **Case 2 (Seymour-forced cubic-link $C_4$ square):** If every star has sum $< 22$, discharging incidences between degree-2 and degree-$\ge 4$ vertices in each link gives $2|E(Q_b)| \le 3|V(Q_b)|$, while Seymour's bound $T(F) \ge |E(F)|$ gives $\sum_b |E(Q_b)| \ge \frac{3}{2}\sum_b |V(Q_b)|$. Equality holds everywhere, forcing every link to be **3-regular on 8 vertices** with $\alpha \le 3$. Every 3-regular triangle-free 8-vertex graph has an **induced $C_4$ square**; keeping an independent triple at each square vertex gives 4-set overlap $12 - \mu$ where $\mu \le 2$ (else 3 common neighbors force an independent 4-set in an 8-vertex link), yielding $|D| \le 4 + 4(11 - 3) - (12 - 2) = 26$.
  - Both reductions require **no** extra assumption that every edge of $G$ lies in a triangle and **zero computer search**.

See [PAPER_NOTE.md](PAPER_NOTE.md) for the full human-readable proof sketches.

## Verified Lean 4 Files (`lean/`)

Every file below passed `lake env lean` in Lean `4.33.1` + Mathlib + `formal-conjectures` (`9097e2f90e`), exact upstream `tools/lint.py` (`ok: true`), and `#print axioms` strictly within `{propext, Classical.choice, Quot.sound}`.

| File | Result | Upstream PR |
| :--- | :--- | :--- |
| `Erdos151.erdos_151.variants.cliqueFree_four.R1.H1.R1.H2.lean` | Bikov's 7-vertex link-extension lemma ($k \le 7$, pure-kernel 3-template proof) | [PR #5205](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/5205) (merged) |
| `Erdos151.erdos_151.variants.cliqueFree_four.R1.H1.R1.H1.R1.lean` | $H(n) \le 10$ ($n \le 46$) 2-anchor overlap reduction | [PR #6248](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6248) (merged) |
| `Erdos151.erdos_151.variants.cliqueFree_four.R1.H1.R1.H1.R1.H3.lean` | $R(3,9) \ge 36 \land R(3,10) \ge 40$ (pure-kernel matching-cover trees) | [PR #6595](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6595) (merged) |
| `Erdos151.erdos_151.variants.cliqueFree_four.R1.H1.R1.H1.R1.H4.lean` | Bikov $k \le 7$ for `R1.H1.R1.H1.R1` | [PR #6647](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/6647) (merged) |
| **`Erdos151.erdos_151.variants.cliqueFree_four.R1.H1.R1.H1.R1.H1.R1.lean`** | **NEW: $H(n) = 11$ ($n \le 52$) 3-anchor induced-path overlap reduction** | [PR #10252](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10252) (merged) |
| **`Erdos151.erdos_151.variants.cliqueFree_four.R1.H1.R1.H1.R1.H1.R1.H1.R1.lean`** | **NEW: $H(n) = 12$ ($n \ge 54$) 4-anchor star + Seymour cubic-link $C_4$ square reduction (isolates $n = 53$)** | [PR #19010](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/19010) |
| **`Erdos151.erdos_151.variants.cliqueFree_four.R1.H1.R1.H1.R1.H1.R1.H1.R1.H3.lean`** | **Pure-kernel proof of $R(3,12) \ge 53$ via 52-vertex triangle-free witness (2,891-node matching-cover tree)** | Modal-verified (pending `#19010` merge) |
| **`Erdos151.erdos_151.variants.cliqueFree_four.R1.H1.R1.H1.R1.H1.R1.H1.R1.H4.lean`** | **Pure-kernel proof of Bikov $k \le 7$ + Seymour's theorem $T(F) \ge |E(F)|$ via $\mathbb{Q}$-linear incidence kernel** | Modal-verified (pending `#19010` merge) |
| `Erdos151.erdos_151.variants.cliqueFree_four.R1.H1.R1.H1.R1.H1.R1.H2.R1.lean` | McKay–Min degree reduction for $R(3,8) \le 28$ under $H(n) = 11$ | [PR #11177](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/11177) (merged) |
| `Erdos151.erdos_151.variants.cliqueFree_four.R1.H1.R1.H1.R1.H1.R1.H3.lean` | $R(3,11) \ge 47$ via Exoo's 46-vertex `g.3.11.46` (2,333-node pure-kernel tree) | [PR #10957](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10957) (merged) |
| `Erdos151.erdos_151.variants.cliqueFree_four.R1.H1.R1.H1.R1.H1.R1.H4.lean` | Bikov $k \le 7$ for $H(n) = 11$ reduction | [PR #10981](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10981) (merged) |
| `Erdos151.erdos_151.variants.cliqueFree_four.R2.H2.R2.H1.R1.lean` | Combined $H(n) = 10, 11$ reduction on `R2.H2.R2.H1` | [PR #10215](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10215) (merged) |
| `Erdos151.erdos_151.variants.cliqueFree_four.R2.H2.R2.H1.R1.H1.R1.lean` | McKay–Min degree reduction for $R(3,8) \le 28$ under `R2.H2.R2.H1.R1` | [PR #11175](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/11175) (merged) |
| `Erdos151.erdos_151.variants.cliqueFree_four.R2.H2.R2.H1.R1.H2.lean` | $R(3,10) \ge 40 \land R(3,11) \ge 47$ (pure-kernel matching-cover trees) | [PR #10935](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10935) (merged) |
| `Erdos151.erdos_151.variants.cliqueFree_four.R2.H2.R2.H1.R1.H3.lean` | Bikov $k \le 7$ for `R2.H2.R2.H1.R1` | [PR #11879](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/11879) (merged) |
| `Erdos151.erdos_151.variants.cliqueFree_four.R1.H1.R1.H1.R1.H2.R1.lean` | McKay–Min degree reduction for $R(3,8) \le 28$ (`8 ≤ Erdos151.H 28`) | [PR #10388](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10388) (merged) |
| `Erdos151.erdos_151.variants.cliqueFree_four.R1.H1.R1.H1.R1.H2.R1.H1.R1.lean` | Degree reduction for $R(3,7) \le 23$ (`7 ≤ Erdos151.H 23`) | [PR #11008](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/11008) (merged) |
| **`Erdos151.erdos_151.variants.cliqueFree_four.R1.H1.R1.H1.R1.H2.R1.H1.R1.H1.lean`** | **Pure-kernel proof of $R(3,6) \le 18$ (`6 ≤ Erdos151.H 18`)** | [PR #16943](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/16943) |

*(Also merged earlier in the same chain: [PR #4497](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4497) for `R1.H1.R1`, degeneracy 6 → 7.)*

## Remaining Explicit Premises

The combined $H(n) \le 12$ ($n \neq 53$) reduction chain is conditional ONLY on:
1. $R(3,8) \le 28$ (`8 ≤ Erdos151.H 28`, McKay & Min 1992 — degree reductions merged in `#10388`/`#11008`, pure-kernel $R(3,6) \le 18$ submitted in `#16943`), and
2. The remaining open core: **$(H(n) = 12 \land n = 53)$ or $13 \le H(n)$ ($n \ge 60$)**.

*(All lower bounds $R(3,9) \ge 36$, $R(3,10) \ge 40$, $R(3,11) \ge 47$, $R(3,12) \ge 53$, Bikov's $k \le 7$ lemma, and Seymour's triangle-count bound $T(F) \ge |E(F)|$ are now proved in pure Lean 4 kernel!)*

## Reproducibility

- Formalizations were produced with `ply-math` (`gpt-6.2-sol + gpt-6-lluna`) and direct Lean 4 authoring, verified on Lean `4.33.1` + `formal-conjectures` (`9097e2f90e`).
- `scripts/gen_h3.py` and `scripts/gen_h12_h3.py` reproduce the pure-kernel matching-cover branch-and-bound certificate generators for Ramsey lower bounds ($R(3,9) \ge 36$, $R(3,10) \ge 40$, $R(3,12) \ge 53$).
- `scripts/gen_r36.py` reproduces the pure-kernel bitmask certificate generator for the 5-regular 18-vertex case of $R(3,6) \le 18$.
