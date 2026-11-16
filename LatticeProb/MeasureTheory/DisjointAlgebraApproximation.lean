import LatticeProb.MeasureTheory.DisjointificationError

/-! # Disjoint approximations by a measure-dense algebra -/

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal symmDiff BigOperators

namespace LatticeProb

/-- A finite disjoint family of finite-measure measurable sets can be simultaneously
approximated by a disjoint family from a measure-dense set algebra. -/
theorem exists_disjoint_algebra_approximation {α : Type*} [MeasurableSpace α]
    (μ : Measure α) {𝒜 : Set (Set α)} (h𝒜 : IsSetAlgebra 𝒜)
    (hdense : μ.MeasureDense 𝒜) {n : ℕ} (s : Fin n → Set α)
    (hs : Pairwise (Function.onFun Disjoint s))
    (hsm : ∀ i, MeasurableSet (s i)) (hsfinite : ∀ i, μ (s i) ≠ ∞)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : Fin n → Set α, (∀ i, t i ∈ 𝒜) ∧
      Pairwise (Function.onFun Disjoint t) ∧
      ∀ i, μ (s i ∆ t i) < ENNReal.ofReal ε := by
  classical
  let δ : ℝ := ε / (n + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hsmall : (n : ℝ) * δ < ε := by
    dsimp [δ]
    have hn : (0 : ℝ) < n + 1 := by positivity
    rw [← mul_div_assoc, div_lt_iff₀ hn]
    nlinarith
  choose u huA hu using fun i => hdense.approx (s i) (hsm i) (hsfinite i) δ hδ
  refine ⟨disjointed u, fun i => h𝒜.isSetRing.disjointed_mem huA i,
    disjoint_disjointed u, fun i => ?_⟩
  calc
    μ (s i ∆ disjointed u i) ≤ ∑ j, μ (s j ∆ u j) :=
      measure_symmDiff_disjointed_le μ s u hs i
    _ ≤ ∑ _j : Fin n, ENNReal.ofReal δ :=
      Finset.sum_le_sum fun j _ => le_of_lt (hu j)
    _ = ENNReal.ofReal ((n : ℝ) * δ) := by
      simp [ENNReal.ofReal_mul]
    _ < ENNReal.ofReal ε := (ENNReal.ofReal_lt_ofReal_iff hε).2 hsmall

end LatticeProb
