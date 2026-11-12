/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53M2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53M1

/-!
# DZZ Lemma 5.3, part 1, node 4: `u` and `v` desirable (P2-DZZ53M)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2516–2522: "Consider
`𝖢₁ = 𝖢_{δ,u}`. Using a similar but simpler argument, we can show that with probability tending
to 1 there exists `Λ_u ⊆ Λ₁` with `𝓛₁(Λ_u) ≥ 0.99 𝓛₁(Λ₁)` such that for `x ∈ Λ_u`,
`log D̃^{𝕍̃_{u,v}}_{δδ̃}(u, x) ≤ E log D̃_{δ̃}(u,v) + (log δ⁻¹)^{0.98}`" (and the same for `v`).

The "simpler argument" is that of (eq-z-open) with one base point instead of two: for the cell
`𝖢 ∋ w` (`w = u` or `v`), a local proxy `ν_𝖢` dominating `μIn` on `𝕍_{c_𝖢, 5s_𝖢}` on the
event that `𝖢` is a cell (the analogue of (eq-M-A-upper-bound-bis)), a per-point far bound
`P((w, x) far for ν_𝖢) ≤ p` for `x ∈ ∂𝖢` (the analogue of the bound after
(eq-scaling-invariance-approximate)), then Markov on `∂𝖢` (`l53_point_markov`) and
(eq-Lambda-i-not-small) (`l53_iface_ge_min`). No conditional independence is needed (no
product of probabilities); the cell `𝖢 ∋ w` is random, which is handled by a union bound over
the deterministic candidates `boxAt n w`, `n ≤ N`.

* `l53WBad νb δ T w Bd a`: the bad event `{μH¹|_{Bd}{x : (w,x) far} ≥ a}`.
* **`l53_wclause_of_not_bad`**: off it, on the domination event, the `w`-clause holds for any
  interface `Λ ⊆ ∂𝖢` with `ε s_𝖢 ≤ μH¹(Λ)`.
* **`l53WBad_le`**: `P(l53WBad … (0.01 ε s_𝖢)) ≤ (400/ε) p`.
* `l53UClause`, `l53VClause`, `l53CellsClause`: the three clauses of `L53ChainDesirable`.
* `l53UVBadR`, `l53CellsBadR`, **`l53BadR_subset`**: `l53BadR ⊆ l53UVBadR ∪ l53CellsBadR`
  (node 4 ∪ node 3).
* **`l53UVBadR_le`**: `P(l53UVBadR) ≤ q + 2(N+1)(400/ε*) p`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

/-- `μH¹(∂𝖢̄) ≤ 4 s_𝖢`. -/
lemma l53_frontier_le (b : DyBox) : μH[1] (frontier b.closedBox) ≤ 4 * ENNReal.ofReal b.side := by
  have hsub : frontier b.closedBox ⊆
      ({z : ℂ | z.re = b.j * b.side ∧ b.k * b.side ≤ z.im ∧ z.im ≤ (b.k + 1) * b.side} ∪
        {z : ℂ | z.re = (b.j + 1) * b.side ∧ b.k * b.side ≤ z.im ∧ z.im ≤ (b.k + 1) * b.side}) ∪
      ({z : ℂ | z.im = b.k * b.side ∧ b.j * b.side ≤ z.re ∧ z.re ≤ (b.j + 1) * b.side} ∪
        {z : ℂ | z.im = (b.k + 1) * b.side ∧ b.j * b.side ≤ z.re ∧ z.re ≤ (b.j + 1) * b.side}) := by
    intro z hz
    obtain ⟨⟨a1, a2, a3, a4⟩, h⟩ := frontier_closedBox_sub hz
    rcases h with h | h | h | h
    · exact Or.inl (Or.inl ⟨h, a3, a4⟩)
    · exact Or.inl (Or.inr ⟨h, a3, a4⟩)
    · exact Or.inr (Or.inl ⟨h, a1, a2⟩)
    · exact Or.inr (Or.inr ⟨h, a1, a2⟩)
  have e : ∀ a : ℝ, ENNReal.ofReal ((a + 1) * b.side - a * b.side) = ENNReal.ofReal b.side :=
    fun a => by congr 1; ring
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  refine (add_le_add (measure_union_le _ _) (measure_union_le _ _)).trans (le_of_eq ?_)
  rw [l53M_vline_eq, l53M_vline_eq, l53M_hline_eq, l53M_hline_eq, e, e]
  ring

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The `u`-clause of `L53ChainDesirable`. -/
def l53UClause (ν : Measure ℂ) (u : ℂ) (δ T : ℝ) (c : List DyBox) : Prop :=
  ∃ A ⊆ l53Iface c 1, MeasurableSet A ∧
    0.99 * (μH[1] : Measure ℂ).real (l53Iface c 1) ≤ (μH[1] : Measure ℂ).real A ∧
    ∀ x ∈ A, lgdLeExp ν δ T u x

/-- The `v`-clause of `L53ChainDesirable`. -/
def l53VClause (ν : Measure ℂ) (v : ℂ) (δ T : ℝ) (c : List DyBox) : Prop :=
  ∃ A ⊆ l53Iface c (c.length - 1),
    0.99 * (μH[1] : Measure ℂ).real (l53Iface c (c.length - 1)) ≤ (μH[1] : Measure ℂ).real A ∧
    ∀ x ∈ A, lgdLeExp ν δ T v x

/-- The `𝖢_i`-clauses of `L53ChainDesirable` (node 3). -/
def l53CellsClause (ν : Measure ℂ) (δ T' : ℝ) (c : List DyBox) : Prop :=
  ∀ i, 2 ≤ i → i ≤ c.length - 1 → ∀ E ⊆ l53Iface c i,
    0.1 * (μH[1] : Measure ℂ).real (l53Iface c i) ≤ (μH[1] : Measure ℂ).real E →
    ∃ S ⊆ l53Iface c (i - 1),
      0.1 * (μH[1] : Measure ℂ).real (l53Iface c (i - 1)) ≤ (μH[1] : Measure ℂ).real S ∧
      ∀ x ∈ S, ∃ x' ∈ E, lgdLeExp ν δ T' x x'

lemma l53ChainDesirable_iff (ν : Measure ℂ) (u v : ℂ) (δ T T' : ℝ) (c : List DyBox) :
    L53ChainDesirable ν u v δ T T' c ↔
      l53UClause ν u δ T c ∧ l53VClause ν v δ T c ∧ l53CellsClause ν δ T' c := Iff.rfl

end DZZ
end LQGMetric
