import LatticeProb.MeasureTheory.DisjointAlgebraApproximation
import LatticeProb.MeasureTheory.LabelledPartitionProfileBound

/-! # Approximation by labelled measure-dense partitions -/

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal symmDiff BigOperators

namespace LatticeProb

/-- A finite labelled measurable partition can be approximated using a measure-dense
set algebra, with an arbitrary positive budget for the partition error. -/
theorem exists_simpleFunc_measureDense_partition_bound {α E : Type*}
    [MeasurableSpace α] [PseudoEMetricSpace E]
    (μ : Measure α) {𝒜 : Set (Set α)} (h𝒜 : IsSetAlgebra 𝒜)
    (hdense : μ.MeasureDense 𝒜) {D : Set E} {n : ℕ}
    (s : Fin n → Set α) (hs : Pairwise (Function.onFun Disjoint s))
    (hsm : ∀ i, MeasurableSet (s i)) (hsfinite : ∀ i, μ (s i) ≠ ∞)
    (hcover : ∀ x, ∃ i, x ∈ s i) (v : Fin n → E) (v₀ : E)
    (hv : ∀ i, v i ∈ D) (hv₀ : v₀ ∈ D) (f : α → E) (δ : ℝ≥0∞)
    (hclose : ∀ i x, x ∈ s i → edist (f x) (v i) ≤ δ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : SimpleFunc α E, Set.range g ⊆ D ∧
      (∀ y ∈ Set.range g, g ⁻¹' {y} ∈ 𝒜) ∧
      (∫⁻ x, min 1 (edist (f x) (g x)) ∂μ) ≤ δ * μ univ + ENNReal.ofReal ε := by
  classical
  let η : ℝ := ε / (n + 1)
  have hη : 0 < η := by dsimp [η]; positivity
  have hbudget : (n : ℝ) * η ≤ ε := by
    dsimp [η]
    have hn : (0 : ℝ) < n + 1 := by positivity
    rw [← mul_div_assoc, div_le_iff₀ hn]
    nlinarith
  obtain ⟨t, ht, hdisj, herr⟩ :=
    exists_disjoint_algebra_approximation μ h𝒜 hdense s hs hsm hsfinite hη
  obtain ⟨g, hgD, hgA, hbound⟩ :=
    exists_simpleFunc_labelled_partition_bound μ h𝒜 s t v v₀ hv₀ ht
      (fun i => hdense.measurable (t i) (ht i)) hv hdisj hcover f δ hclose
  refine ⟨g, hgD, hgA, hbound.trans ?_⟩
  gcongr
  calc
    (∑ i, μ (s i ∆ t i)) ≤ ∑ _i : Fin n, ENNReal.ofReal η :=
      Finset.sum_le_sum fun i _ => le_of_lt (herr i)
    _ = ENNReal.ofReal ((n : ℝ) * η) := by simp [ENNReal.ofReal_mul]
    _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hbudget

end LatticeProb
