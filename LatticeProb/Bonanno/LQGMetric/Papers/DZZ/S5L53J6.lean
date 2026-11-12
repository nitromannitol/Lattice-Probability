/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53J6 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53J5

/-!
# DZZ Lemma 5.3, node 3: desirable cells with high probability (abstract form)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 2510–2514): "using (eq-z-open) and an argument
identical to that of (eq-par) … we obtain that each cell `𝖢_i` is desirable with probability
`1 - e^{-Ω(2^{√log δ⁻¹})}` and thus a union bound verifies that all cells `𝖢_2, …, 𝖢_{d-1}`
are desirable with high probability".

`l53_cell_desirable_prob`: one cell, in abstract form. The `(2N+1)²` boxes of the cell are the
sites of a finite set `Box ⊇ annBox N` (for a cell with `K = 2N + 2` boxes per side,
`Box = [-N, N+1]²` and the boundary depth `tb d` is `N - n` on the sides `B`, `L` and
`N - n + 1` on `T`, `R`); under a measure `μ` (DZZ: `P[· | 𝓕*]`, here any measure, e.g.
`P[· | A₀]` with `l53_cond_biInter`) the bad events `Bad z` have `μ (Bad z) ≤ ε ≤ θ^{(r+1)²}`
and the
product bound for families at pairwise `ℓ^∞`-distance `> r` (for the proxy regions
`(0, s²) × 𝕍_{c_B, 7 s_B}` of S5L53G, disjointness needs `r ≥ 7`); off `Bad z` the box `z` is open
(`hopen`, the form produced by `l53_zopen_dyBox` part 4). The geometric data (`Bd`, `I`,
segments, `Prev`, `Next`, `Λ_{i-1}`, `Λ_i`) are deterministic (DZZ work conditionally on
`𝓕*`, which fixes the cells). Then the `𝖢_i`-clause of `L53ChainDesirable` fails with
probability at most the bound of `l53_perc_cluster`.

`l53_cells_desirable_prob`: the union bound over finitely many cells.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric.DZZ

open LQGMetric

/-- The `𝖢_i`-clause of `L53ChainDesirable` for the boundary pieces `Λprev = Λ_{i-1}`,
`Λnext = Λ_i` (measure `ν`, LGD measure `M`, exponent `T'`). -/
def L53DesClause (ν M : Measure ℂ) (δ T' : ℝ) (Λprev Λnext : Set ℂ) : Prop :=
  ∀ E ⊆ Λnext, 0.1 * ν.real Λnext ≤ ν.real E → ∃ S ⊆ Λprev,
    0.1 * ν.real Λprev ≤ ν.real S ∧ ∀ x ∈ S, ∃ x' ∈ E, lgdLeExp M δ T' x x'

end LQGMetric.DZZ
