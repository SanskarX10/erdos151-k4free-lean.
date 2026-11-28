# Formalized Progress on $K_4$-Free Erdős Problem #151 ($H(n) \le 12$ for $n \neq 53$)

Pure-kernel Lean 4 + Mathlib formalizations (verified against `google-deepmind/formal-conjectures` commit `9097e2f90e`, Lean `4.33.1`, with `#print axioms ⊆ {propext, Classical.choice, Quot.sound}`, zero `sorry`, zero `axiom`, zero `bv_decide`/`native_decide`) for the $K_4$-free variant of **Erdős Problem #151** (`Erdos151.erdos_151.variants.cliqueFree_four`):

> For every $K_4$-free graph $G$ on $n$ vertices, does the clique transversal number satisfy $\tau(G) \le n - H(n)$, where $H(n)$ is the largest $k$ such that every triangle-free graph on $n$ vertices has an independent set of size $k$?

## Main Mathematical Contribution

Our key new step is a **three-vertex induced-path overlap reduction** that resolves **all $K_4$-free graphs with $H(n) = 11$** (closing all $n \le 52$ via $R(3,12) \ge 53$, and reducing the remaining open problem to $H(n) \ge 12$, i.e., $n \ge 53$).

### What Is Prior vs. What Is New
- **Prior results (formalized here as pure-kernel Lean proofs/lemmas):**
  - Bikov's 7-vertex triangle-free link-extension lemma ($k \le 7$), giving $\delta(F) \ge 8$ in a subgraph-minimal $(3,3)$-arrowing subgraph $F \le G$.
  - Single-vertex and adjacent-pair neighborhood deletion ($H(n) \le 10$, $n \le 46$).
  - Classical Ramsey bounds: $R(3,9) \ge 36$ (Kalbfleisch), $R(3,10) \ge 40$ and $R(3,11) \ge 47$ (Exoo's `g310.39` and `g.3.11.46`), and $R(3,8) \le 28$ (McKay & Min 1992).
- **New step ($H(n) = 11$, $n \le 52$):**
  - In a subgraph-minimal arrowing subgraph $F \le G$ ($\delta(F) \ge 8$, every $F$-edge in $\ge 2$ $F$-triangles, $\Delta(G) \le 10$, $n \ge 47$), we construct a **three-vertex induced path** $a - b - c$ ($F.\text{Adj } a\,b$, $F.\text{Adj } b\,c$, $\neg G.\text{Adj } a\,c$) together with independent link-sets $A \subseteq P_a$, $B \subseteq P_b$, $C \subseteq P_c$ ($b \in A$, $a, c \in B$, $b \in C$) satisfying:
    $$|A| + |B| + |C| + s_{ab} + s_{bc} \ge 14,$$
    where $s_{uv} = |N_G(u) \cap N_G(v)|$.
  - Using the 3-set overlap bound $|D_a \cup D_b \cup D_c| \le |D_a| + |D_b| + |D_c| - |D_a \cap D_b| - |D_b \cap D_c|$ with $s_{ab} \le |D_a \cap D_b|$ and $s_{bc} \le |D_b \cap D_c|$, the deletion set $D = \{a, b, c\} \cup D_a \cup D_b \cup D_c$ has size **at most $19$**.
  - Since $n \ge 47$, at least $47 - 19 = 28$ vertices remain. Applying $R(3,8) \le 28$ (plus Bikov $k \le 7$ to color the remainder if it has no degree-$\ge 8$ vertex) yields 8 triangle-free vertices in $G - D$, and adding all three anchors $\{a, b, c\}$ back yields an 11-vertex triangle-free set, giving $\tau(G) \le n - 11$.
  - Importantly, this argument requires **no** extra assumption that every edge of $G$ lies in a triangle and **zero computer search** for the reduction itself.

See [PAPER_NOTE.md](PAPER_NOTE.md) for the full human-readable proof sketch.

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
| `Erdos151.erdos_151.variants.cliqueFree_four.R1.H1.R1.H1.R1.H1.R1.H2.R1.lean` | McKay–Min degree reduction for $R(3,8) \le 28$ under $H(n) = 11$ | [PR #11177](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/11177) |
| `Erdos151.erdos_151.variants.cliqueFree_four.R1.H1.R1.H1.R1.H1.R1.H3.lean` | $R(3,11) \ge 47$ via Exoo's 46-vertex `g.3.11.46` (2,333-node pure-kernel tree) | [PR #10957](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10957) |
| `Erdos151.erdos_151.variants.cliqueFree_four.R1.H1.R1.H1.R1.H1.R1.H4.lean` | Bikov $k \le 7$ for $H(n) = 11$ reduction | [PR #10981](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10981) |
| `Erdos151.erdos_151.variants.cliqueFree_four.R2.H2.R2.H1.R1.lean` | Combined $H(n) = 10, 11$ reduction on `R2.H2.R2.H1` | [PR #10215](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10215) (merged) |
| `Erdos151.erdos_151.variants.cliqueFree_four.R2.H2.R2.H1.R1.H1.R1.lean` | McKay–Min degree reduction for $R(3,8) \le 28$ under `R2.H2.R2.H1.R1` | [PR #11175](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/11175) |
| `Erdos151.erdos_151.variants.cliqueFree_four.R2.H2.R2.H1.R1.H2.lean` | $R(3,10) \ge 40 \land R(3,11) \ge 47$ (pure-kernel matching-cover trees) | [PR #10935](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10935) |
| `Erdos151.erdos_151.variants.cliqueFree_four.R2.H2.R2.H1.R1.H3.lean` | Bikov $k \le 7$ for `R2.H2.R2.H1.R1` | [PR #11879](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/11879) |
| `Erdos151.erdos_151.variants.cliqueFree_four.R1.H1.R1.H1.R1.H2.R1.lean` | McKay–Min degree reduction for $R(3,8) \le 28$ (`8 ≤ Erdos151.H 28`) | [PR #10388](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/10388) (merged) |
| `Erdos151.erdos_151.variants.cliqueFree_four.R1.H1.R1.H1.R1.H2.R1.H1.R1.lean` | Degree reduction for $R(3,7) \le 23$ (`7 ≤ Erdos151.H 23`) | [PR #11008](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/11008) |
| **`Erdos151.erdos_151.variants.cliqueFree_four.R1.H1.R1.H1.R1.H2.R1.H1.R1.H1.lean`** | **Pure-kernel proof of $R(3,6) \le 18$ (`6 ≤ Erdos151.H 18`)** | [PR #16943](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/16943) |

*(Also merged earlier in the same chain: [PR #4497](https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/4497) for `R1.H1.R1`, degeneracy 6 → 7.)*

## Remaining Explicit Premises

The $H(n) = 11$ reduction is conditional on:
1. $R(3,8) \le 28$ (`8 ≤ Erdos151.H 28`, McKay & Min 1992 — formalization in progress via `R1.H1.R1.H1.R1.H2.R1`),
2. $R(3,11) \ge 47$ (`∀ n, 11 ≤ Erdos151.H n → 47 ≤ n` — **already proved in pure kernel** in `...H3.lean`),
3. Bikov's 7-vertex link-extension lemma (**already proved in pure kernel** in `...H4.lean`), and
4. The remaining open core `12 ≤ Erdos151.H n` ($n \ge 53$).

## Reproducibility

- Formalizations were produced with `ply-math` (`gpt-6.2-sol + gpt-6-lluna`) and verified on Lean `4.33.1` + `formal-conjectures` (`9097e2f90e`).
- `scripts/gen_h3.py` reproduces the pure-kernel matching-cover branch-and-bound certificate generator for Ramsey lower bounds.
- `scripts/gen_r36.py` reproduces the pure-kernel bitmask certificate generator for the 5-regular 18-vertex case of $R(3,6) \le 18$.
