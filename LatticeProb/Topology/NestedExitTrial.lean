import LatticeProb.Prob.BallExitRadius
import LatticeProb.Prob.ConditionalTrialFailure
import LatticeProb.Topology.RealFirstExitClock

/-! # Ball containment in nested first-exit traces -/

set_option autoImplicit false

open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LatticeProb

/-- Real first-exit endpoints increase with the radius, provided the outer exit is finite. -/
theorem firstExitEndpoint_le_of_radius_le {E : Type*} [PseudoMetricSpace E]
    (η : ℝ → E) (t₀ : ℝ) (z : E) {r R : ℝ} (hr : r ≤ R)
    (hη : Continuous η)
    (hfin : openExitTime (fun s (_ : Unit) => η (t₀ + (s : ℝ))) (ball z R) () ≠ ⊤) :
    t₀ ≤ sInf {t : ℝ | t₀ ≤ t ∧ η t ∉ ball z r} ∧
    sInf {t : ℝ | t₀ ≤ t ∧ η t ∉ ball z r} ≤
      sInf {t : ℝ | t₀ ≤ t ∧ η t ∉ ball z R} := by
  let B := fun s : ℝ≥0 => fun _ : Unit => η (t₀ + (s : ℝ))
  have hle : openExitTime B (ball z r) () ≤ openExitTime B (ball z R) () :=
    monotone_openExitTime_ball B () z hr
  have hfin' : openExitTime B (ball z r) () ≠ ⊤ := ne_top_of_le_ne_top hfin hle
  have hclock := (ENNReal.toNNReal_le_toNNReal hfin' hfin).2 hle
  rw [sInf_outside_eq_forward_openExitTime η _ t₀ hη isOpen_ball hfin',
    sInf_outside_eq_forward_openExitTime η _ t₀ hη isOpen_ball hfin]
  constructor
  · exact le_add_of_nonneg_right (NNReal.coe_nonneg _)
  · have hreal : ((openExitTime B (ball z r) ()).toNNReal : ℝ) ≤
        ((openExitTime B (ball z R) ()).toNNReal : ℝ) := hclock
    exact add_le_add (le_refl t₀) hreal

/-- Any ball contained between two nested exits is contained in the full exit trace. -/
theorem exists_ball_subset_nested_firstExitTrace {E : Type*} [PseudoMetricSpace E]
    (η : ℝ → E) (t₀ : ℝ) (z : E) {r₁ r₂ R a : ℝ}
    (hr₁ : r₁ ≤ R) (hr₂ : r₂ ≤ R) (hη : Continuous η)
    (hfin : openExitTime (fun s (_ : Unit) => η (t₀ + (s : ℝ))) (ball z R) () ≠ ⊤)
    (hball : ∃ w, ball w a ⊆ η '' Icc
      (sInf {t : ℝ | t₀ ≤ t ∧ η t ∉ ball z r₁})
      (sInf {t : ℝ | t₀ ≤ t ∧ η t ∉ ball z r₂})) :
    ∃ w, ball w a ⊆ η '' Icc t₀ (sInf {t : ℝ | t₀ ≤ t ∧ η t ∉ ball z R}) := by
  obtain ⟨w, hw⟩ := hball
  refine ⟨w, hw.trans (image_mono (Icc_subset_Icc ?_ ?_))⟩
  · exact (firstExitEndpoint_le_of_radius_le η t₀ z hr₁ hη hfin).1
  · exact (firstExitEndpoint_le_of_radius_le η t₀ z hr₂ hη hfin).2

/-- A uniform conditional success estimate for nested exit traces bounds failure of the
whole trace to contain a ball. The adaptedness and conditional estimates are hypotheses. -/
theorem measureReal_firstExitTrace_failure_le_of_condExp_ge
    {Ω E : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    [PseudoMetricSpace E] (ℱ : Filtration ℕ m) (η : Ω → ℝ → E)
    (t₀ : Ω → ℝ) (z : E) (r : ℕ → ℝ) (R a : ℝ) (n : ℕ)
    (hr : ∀ k < n, r k ≤ R ∧ r (k + 1) ≤ R)
    (hpath : ∀ᵐ ω ∂μ, Continuous (η ω) ∧
      openExitTime (fun s (_ : Unit) => η ω (t₀ ω + (s : ℝ))) (ball z R) () ≠ ⊤)
    (hA : ∀ k, MeasurableSet[ℱ (k + 1)] {ω | ∃ w, ball w a ⊆ η ω '' Icc
      (sInf {t : ℝ | t₀ ω ≤ t ∧ η ω t ∉ ball z (r k)})
      (sInf {t : ℝ | t₀ ω ≤ t ∧ η ω t ∉ ball z (r (k + 1))})})
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp : ∀ k, ∀ᵐ ω ∂μ, p ≤ μ[({ω | ∃ w, ball w a ⊆ η ω '' Icc
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
    _ ≤ μ.real {ω | ∀ k ∈ Finset.range n, ω ∉ A k} := by
      exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub)
    _ ≤ _ := measureReal_no_success_le_of_condExp_ge ℱ A hA hp0 hp1 hp n

end LatticeProb
