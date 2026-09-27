import LatticeProb.Prob.KingmanLinear.Defs

/-!
# 1. The sets `A_k`

The set `linSet g C k` of points obeying the linear bound `g n x ≤ C n + k` is measurable, and
for `g` bounded a.e. by some affine function `C n + K`, a.e. point lies in `linSet g C k` for
some natural `k`: this is how the argument reduces to a fixed `k` at a time.
-/

open MeasureTheory Filter Topology Set

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The set `linSet g C k` of points obeying the linear bound `g n x ≤ C n + k` is measurable. -/
theorem measurableSet_linSet {g : ℕ → Ω → ℝ} (hgm : ∀ n, Measurable (g n)) (C : ℝ) (k : ℕ) :
    MeasurableSet (linSet g C k) := by
  simp only [linSet, setOf_forall]
  exact MeasurableSet.iInter fun n => measurableSet_le (hgm n) measurable_const


/-- If `g n x ≤ C n + K` a.e. for some `K`, then a.e. `x` lies in `linSet g C k` for some natural
`k`. -/
theorem ae_exists_mem_linSet_of_linear_bound {μ : Measure Ω} {g : ℕ → Ω → ℝ} {C : ℝ}
    (hlin : ∀ᵐ x ∂μ, ∃ K : ℝ, ∀ n : ℕ, g n x ≤ C * n + K) :
    ∀ᵐ x ∂μ, ∃ k : ℕ, x ∈ linSet g C k := by
  filter_upwards [hlin] with x hx
  obtain ⟨K, hK⟩ := hx
  refine ⟨⌈K⌉₊, ?_⟩
  simp only [linSet, Set.mem_setOf_eq]
  intro n
  linarith [hK n, Nat.le_ceil K]

end LatticeProb
