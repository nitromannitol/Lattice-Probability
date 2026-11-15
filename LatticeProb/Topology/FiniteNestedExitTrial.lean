import LatticeProb.Topology.FlooredNestedExitTrial

/-! # Finite families of conditional exit trials -/

set_option autoImplicit false

open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LatticeProb

/-- Only the trials before `n` need be adapted and satisfy the conditional success bound. -/
theorem measureReal_no_success_le_of_condExp_ge_on_range
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (A : ℕ → Set Ω) (n : ℕ)
    (hA : ∀ k < n, MeasurableSet[ℱ (k + 1)] (A k)) {p : ℝ} (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1)
    (hp : ∀ k < n, ∀ᵐ ω ∂μ, p ≤ μ[(A k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω) :
    μ.real {ω | ∀ k ∈ Finset.range n, ω ∉ A k} ≤
      Real.exp (-(p ^ 2 / 2) * n) := by
  let B : ℕ → Set Ω := fun k => if k < n then A k else univ
  have hB : ∀ k, MeasurableSet[ℱ (k + 1)] (B k) := by
    intro k
    by_cases hk : k < n
    · simpa [B, hk] using hA k hk
    · simp [B, hk]
  have hq : ∀ k, ∀ᵐ ω ∂μ, p ≤ μ[(B k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω := by
    intro k
    by_cases hk : k < n
    · simpa [B, hk] using hp k hk
    · simp only [B, hk, ite_false, Set.indicator_univ, condExp_const (ℱ.le k)]
      exact Filter.Eventually.of_forall (fun _ => hp1)
  have heq : {ω | ∀ k ∈ Finset.range n, ω ∉ B k} =
      {ω | ∀ k ∈ Finset.range n, ω ∉ A k} := by
    ext ω
    simp only [Set.mem_ofPred_eq]
    apply forall_congr' fun k => forall_congr' fun hk => ?_
    simp only [B, Finset.mem_range.mp hk, ite_true]
  rw [← heq]
  exact measureReal_no_success_le_of_condExp_ge ℱ B hB hp0 hp1 hq n

/-- Finite conditional trials suffice to control failure of a nested exit trace. -/
theorem measureReal_firstExitTrace_failure_le_of_condExp_ge_on_range
    {Ω E : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    [PseudoMetricSpace E] (ℱ : Filtration ℕ m) (η : Ω → ℝ → E)
    (t₀ : Ω → ℝ) (z : E) (r : ℕ → ℝ) (R a : ℝ) (n : ℕ)
    (hr : ∀ k < n, r k ≤ R ∧ r (k + 1) ≤ R)
    (hpath : ∀ᵐ ω ∂μ, Continuous (η ω) ∧
      openExitTime (fun s (_ : Unit) => η ω (t₀ ω + (s : ℝ))) (ball z R) () ≠ ⊤)
    (hA : ∀ k < n, MeasurableSet[ℱ (k + 1)] {ω | ∃ w, ball w a ⊆ η ω '' Icc
      (sInf {t : ℝ | t₀ ω ≤ t ∧ η ω t ∉ ball z (r k)})
      (sInf {t : ℝ | t₀ ω ≤ t ∧ η ω t ∉ ball z (r (k + 1))})})
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp : ∀ k < n, ∀ᵐ ω ∂μ, p ≤ μ[({ω | ∃ w, ball w a ⊆ η ω '' Icc
      (sInf {t : ℝ | t₀ ω ≤ t ∧ η ω t ∉ ball z (r k)})
      (sInf {t : ℝ | t₀ ω ≤ t ∧ η ω t ∉ ball z (r (k + 1))})}).indicator
        (fun _ => (1 : ℝ)) | ℱ k] ω) :
    μ.real {ω | ¬ ∃ w, ball w a ⊆ η ω '' Icc (t₀ ω)
      (sInf {t : ℝ | t₀ ω ≤ t ∧ η ω t ∉ ball z R})} ≤
      Real.exp (-(p ^ 2 / 2) * n) := by
  let A : ℕ → Set Ω := fun k => {ω | ∃ w, ball w a ⊆ η ω '' Icc
    (sInf {t : ℝ | t₀ ω ≤ t ∧ η ω t ∉ ball z (r k)})
    (sInf {t : ℝ | t₀ ω ≤ t ∧ η ω t ∉ ball z (r (k + 1))})}
  have hsub : {ω | ¬ ∃ w, ball w a ⊆ η ω '' Icc (t₀ ω)
      (sInf {t : ℝ | t₀ ω ≤ t ∧ η ω t ∉ ball z R})} ≤ᵐ[μ]
      {ω | ∀ k ∈ Finset.range n, ω ∉ A k} := by
    filter_upwards [hpath] with ω hω hfail k hk hsuccess
    exact hfail (exists_ball_subset_nested_firstExitTrace (η ω) (t₀ ω) z
      (hr k (Finset.mem_range.mp hk)).1 (hr k (Finset.mem_range.mp hk)).2
      hω.1 hω.2 hsuccess)
  calc
    _ ≤ μ.real {ω | ∀ k ∈ Finset.range n, ω ∉ A k} :=
      ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub)
    _ ≤ _ := measureReal_no_success_le_of_condExp_ge_on_range ℱ A n hA hp0 hp1 hp

/-- A finite family of nested exit trials yields an inverse-scale exponential bound. -/
theorem measureReal_firstExitTrace_failure_le_floor_inv_on_range
    {Ω E : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    [PseudoMetricSpace E] (ℱ : Filtration ℕ m) (η : Ω → ℝ → E)
    (t₀ : Ω → ℝ) (z : E) (r : ℕ → ℝ) (R a C ε : ℝ)
    (hr : ∀ k < ⌊(C * ε)⁻¹⌋₊ - 1, r k ≤ R ∧ r (k + 1) ≤ R)
    (hpath : ∀ᵐ ω ∂μ, Continuous (η ω) ∧
      openExitTime (fun s (_ : Unit) => η ω (t₀ ω + (s : ℝ))) (ball z R) () ≠ ⊤)
    (hA : ∀ k < ⌊(C * ε)⁻¹⌋₊ - 1, MeasurableSet[ℱ (k + 1)]
      {ω | ∃ w, ball w a ⊆ η ω '' Icc
      (sInf {t : ℝ | t₀ ω ≤ t ∧ η ω t ∉ ball z (r k)})
      (sInf {t : ℝ | t₀ ω ≤ t ∧ η ω t ∉ ball z (r (k + 1))})})
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp : ∀ k < ⌊(C * ε)⁻¹⌋₊ - 1, ∀ᵐ ω ∂μ,
      p ≤ μ[({ω | ∃ w, ball w a ⊆ η ω '' Icc
      (sInf {t : ℝ | t₀ ω ≤ t ∧ η ω t ∉ ball z (r k)})
      (sInf {t : ℝ | t₀ ω ≤ t ∧ η ω t ∉ ball z (r (k + 1))})}).indicator
        (fun _ => (1 : ℝ)) | ℱ k] ω) :
    μ.real {ω | ¬ ∃ w, ball w a ⊆ η ω '' Icc (t₀ ω)
      (sInf {t : ℝ | t₀ ω ≤ t ∧ η ω t ∉ ball z R})} ≤
      Real.exp (p ^ 2) * Real.exp (-(p ^ 2 / 2) * (C * ε)⁻¹) := by
  calc
    _ ≤ Real.exp (-(p ^ 2 / 2) * ((⌊(C * ε)⁻¹⌋₊ - 1 : ℕ) : ℝ)) :=
      measureReal_firstExitTrace_failure_le_of_condExp_ge_on_range ℱ η t₀ z r R a _
        hr hpath hA hp0 hp1 hp
    _ ≤ Real.exp (2 * (p ^ 2 / 2)) * Real.exp (-(p ^ 2 / 2) * (C * ε)⁻¹) :=
      exp_neg_mul_floor_sub_one_le _ _ (by positivity)
    _ = _ := by congr 1; ring

end LatticeProb
