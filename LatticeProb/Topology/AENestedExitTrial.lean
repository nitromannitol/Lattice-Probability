import LatticeProb.Topology.FiniteNestedExitTrial

/-! # Conditional exit trials with adapted representatives -/

set_option autoImplicit false

open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LatticeProb

/-- An almost everywhere adapted finite family satisfies the same conditional trial bound. -/
theorem measureReal_no_success_le_of_condExp_ge_on_range_ae
    {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m) (A B : ℕ → Set Ω) (n : ℕ)
    (hB : ∀ k < n, MeasurableSet[ℱ (k + 1)] (B k))
    (hAB : ∀ k < n, A k =ᵐ[μ] B k) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp : ∀ k < n, ∀ᵐ ω ∂μ, p ≤ μ[(A k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω) :
    μ.real {ω | ∀ k ∈ Finset.range n, ω ∉ A k} ≤
      Real.exp (-(p ^ 2 / 2) * n) := by
  have hcond : ∀ k < n, ∀ᵐ ω ∂μ,
      p ≤ μ[(B k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω := by
    intro k hk
    have hind : (A k).indicator (fun _ => (1 : ℝ)) =ᵐ[μ]
        (B k).indicator (fun _ => (1 : ℝ)) := indicator_ae_eq_of_ae_eq_set (hAB k hk)
    filter_upwards [hp k hk, condExp_congr_ae (m := ℱ k) hind] with ω h1 h2
    simpa only [← h2] using h1
  have heq : {ω | ∀ k ∈ Finset.range n, ω ∉ A k} =ᵐ[μ]
      {ω | ∀ k ∈ Finset.range n, ω ∉ B k} := by
    have hall : ∀ᵐ ω ∂μ, ∀ k, k < n → (ω ∈ A k ↔ ω ∈ B k) := by
      rw [ae_all_iff]
      intro k
      by_cases hk : k < n
      · filter_upwards [hAB k hk] with ω hω _ using Iff.of_eq hω
      · exact Filter.Eventually.of_forall (fun _ h => (hk h).elim)
    filter_upwards [hall] with ω hω
    simp only [Finset.mem_range]
    exact propext (forall_congr' fun k => forall_congr' fun hk => not_congr (hω k hk))
  have hm : μ.real {ω | ∀ k ∈ Finset.range n, ω ∉ A k} =
      μ.real {ω | ∀ k ∈ Finset.range n, ω ∉ B k} := by
    simp only [measureReal_def, measure_congr heq]
  rw [hm]
  exact measureReal_no_success_le_of_condExp_ge_on_range ℱ B n hB hp0 hp1 hcond

/-- Finite nested exit trials may be adapted through almost everywhere representatives. -/
theorem measureReal_firstExitTrace_failure_le_of_condExp_ge_on_range_ae
    {Ω E : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    [PseudoMetricSpace E] (ℱ : Filtration ℕ m) (η : Ω → ℝ → E)
    (t₀ : Ω → ℝ) (z : E) (r : ℕ → ℝ) (R a : ℝ) (n : ℕ)
    (hr : ∀ k < n, r k ≤ R ∧ r (k + 1) ≤ R)
    (hpath : ∀ᵐ ω ∂μ, Continuous (η ω) ∧
      openExitTime (fun s (_ : Unit) => η ω (t₀ ω + (s : ℝ))) (ball z R) () ≠ ⊤)
    (B : ℕ → Set Ω) (hB : ∀ k < n, MeasurableSet[ℱ (k + 1)] (B k))
    (hAB : ∀ k < n, {ω | ∃ w, ball w a ⊆ η ω '' Icc
      (sInf {t : ℝ | t₀ ω ≤ t ∧ η ω t ∉ ball z (r k)})
      (sInf {t : ℝ | t₀ ω ≤ t ∧ η ω t ∉ ball z (r (k + 1))})} =ᵐ[μ] B k)
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
    _ ≤ _ := measureReal_no_success_le_of_condExp_ge_on_range_ae ℱ A B n hB hAB hp0 hp1 hp

end LatticeProb
