import LatticeProb.Prob.RealBallExitHistory
import LatticeProb.Topology.AENestedExitTrial

/-! # Finite nested trials at real-time ball exits -/

set_option autoImplicit false

open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LatticeProb

/-- Conditional success at successive stopped ball-exit histories bounds the failure
probability for the full trace up to the outer exit. -/
theorem measureReal_real_ballExitTrace_failure_le
    {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d)}
    (hm : ∀ t, StronglyMeasurable (X t))
    (hc : ∀ ω, Continuous fun t => X t ω)
    (z : EuclideanSpace ℝ (Fin d)) (r : ℕ → ℝ) (hr : Monotone r)
    (R a : ℝ) (n : ℕ) (ha : 0 < a)
    (hrR : ∀ k < n, r k ≤ R ∧ r (k + 1) ≤ R)
    (hfin : ∀ᵐ ω ∂μ, openExitTime X (ball z R) ω ≠ ⊤)
    {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hp : ∀ k < n, ∀ᵐ ω ∂μ,
      p ≤ μ[({ω | ∃ w, ball w a ⊆ (fun t : ℝ => X t.toNNReal ω) '' Icc
        (sInf {t : ℝ | 0 ≤ t ∧ X t.toNNReal ω ∉ ball z (r k)})
        (sInf {t : ℝ | 0 ≤ t ∧ X t.toNNReal ω ∉ ball z (r (k + 1))})}).indicator
          (fun _ => (1 : ℝ)) | ballExitHistory X hm hc z r hr k] ω) :
    μ.real {ω | ¬ ∃ w, ball w a ⊆ (fun t : ℝ => X t.toNNReal ω) '' Icc 0
      (sInf {t : ℝ | 0 ≤ t ∧ X t.toNNReal ω ∉ ball z R})} ≤
      Real.exp (-(p ^ 2 / 2) * n) := by
  classical
  have hex : ∀ k, ∃ s : Set Ω, k < n →
      MeasurableSet[ballExitHistory X hm hc z r hr (k + 1)] s ∧
      {ω | ∃ w, ball w a ⊆ (fun t : ℝ => X t.toNNReal ω) '' Icc
        (sInf {t : ℝ | 0 ≤ t ∧ X t.toNNReal ω ∉ ball z (r k)})
        (sInf {t : ℝ | 0 ≤ t ∧ X t.toNNReal ω ∉ ball z (r (k + 1))})} =ᵐ[μ] s := by
    intro k
    by_cases hk : k < n
    · have hfin' : ∀ᵐ ω ∂μ, openExitTime X (ball z (r (k + 1))) ω ≠ ⊤ := by
        filter_upwards [hfin] with ω hω
        exact ne_top_of_le_ne_top hω (monotone_openExitTime_ball X ω z (hrR k hk).2)
      obtain ⟨s, hs, hrep⟩ :=
        exists_measurableSet_real_ball_subset_exitHistory_segment hm hc z r hr k ha hfin'
      refine ⟨s, fun _ => ⟨hs, ?_⟩⟩
      filter_upwards [hrep] with ω hω
      exact propext hω.symm
    · exact ⟨∅, fun h => (hk h).elim⟩
  choose B hB using hex
  have hpath : ∀ᵐ ω ∂μ, Continuous (fun t : ℝ => X t.toNNReal ω) ∧
      openExitTime (fun s (_ : Unit) => X (0 + (s : ℝ)).toNNReal ω)
        (ball z R) () ≠ ⊤ := by
    filter_upwards [hfin] with ω hω
    refine ⟨(hc ω).comp continuous_real_toNNReal, ?_⟩
    have hf : (fun (s : ℝ≥0) (_ : Unit) => X (0 + (s : ℝ)).toNNReal ω) =
        (fun s (_ : Unit) => X s ω) := by
      funext s u
      simp
    rw [hf]
    exact hω
  exact measureReal_firstExitTrace_failure_le_of_condExp_ge_on_range_ae
    (ballExitHistory X hm hc z r hr) (fun ω t => X t.toNNReal ω) (fun _ => 0)
    z r R a n hrR hpath B (fun k hk => (hB k hk).1) (fun k hk => (hB k hk).2)
    hp0 hp1 hp

end LatticeProb
