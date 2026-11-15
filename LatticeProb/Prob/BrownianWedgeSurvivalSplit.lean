import LatticeProb.Prob.BrownianWedgeSubcriticalExit

/-! # A fixed-time survival bound for Brownian motion in a wedge -/

set_option autoImplicit false

open MeasureTheory Set InnerProductSpace
open scoped NNReal ENNReal Topology

namespace LatticeProb

/-- Wedge survival is bounded by the large-radius exit probability and the
probability of being in the ball at the final time. -/
theorem brownian_wedge_survival_le_exit_add_ball {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {x : Euc 2} {B : ℝ≥0 → Ω → Euc 2}
    (hB : IsBrownianSpace 2 x B P) {θ p r : ℝ} (hθ0 : 0 < θ)
    (hθπ : θ < Real.pi) (hp : 0 < p) (hpθ : p * θ < Real.pi) (hr : 0 < r)
    (t : ℝ≥0) :
    let J : Euc 2 → ℂ := Complex.orthonormalBasisOneI.repr.symm
    let W : Set (Euc 2) := {y | ((J y).re, (J y).im) ∈
      CorrelatedBM.openSymmetricWedge (Real.sin (θ / 2)) (Real.cos (θ / 2))}
    x ∈ closure W →
    Real.cos (p * (θ / 2)) * r ^ p *
      P.real {ω | ∀ s ≤ t, B s ω ∈ W} ≤
      (J x ^ (p : ℂ)).re + Real.cos (p * (θ / 2)) * r ^ p *
        P.real {ω | B t ω ∈ Metric.ball (0 : Euc 2) r} := by
  dsimp only
  intro hx
  have := hB.isProbabilityMeasure
  let J : Euc 2 → ℂ := Complex.orthonormalBasisOneI.repr.symm
  let W : Set (Euc 2) := {y | ((J y).re, (J y).im) ∈
    CorrelatedBM.openSymmetricWedge (Real.sin (θ / 2)) (Real.cos (θ / 2))}
  let U : Set (Euc 2) := Metric.ball 0 r
  let V : Set (Euc 2) := U ∩ W
  let τ : Ω → ℝ≥0∞ := openExitTime B V
  let A : Set Ω := {ω | ∀ s ≤ t, B s ω ∈ W}
  let E : Set Ω := {ω | r ≤ ‖J (B (τ ω).toNNReal ω)‖}
  let F : Set Ω := {ω | B t ω ∈ U}
  have hJ : Continuous J := Complex.orthonormalBasisOneI.repr.symm.continuous
  have hW : IsOpen W := by
    apply (CorrelatedBM.isOpen_openSymmetricWedge _ _).preimage
    exact (Complex.continuous_re.comp hJ).prodMk
      (Complex.continuous_im.comp hJ)
  have hV : IsOpen V := Metric.isOpen_ball.inter hW
  have hVb : Bornology.IsBounded V := Metric.isBounded_ball.subset inter_subset_left
  have hsub : ∀ᵐ ω ∂P, ω ∈ A → ω ∈ E ∪ F := by
    filter_upwards [hB.cont, ae_openExitTime_ne_top (by norm_num) hB hVb] with ω hc hfin hA
    by_cases ht : (t : ℝ≥0∞) < τ ω
    · exact Or.inr (mem_of_lt_openExitTime ht).1
    · left
      have hτ : (τ ω).toNNReal ≤ t := by
        apply ENNReal.coe_le_coe.mp
        rw [ENNReal.coe_toNNReal hfin]
        exact le_of_not_gt ht
      have hw : B (τ ω).toNNReal ω ∈ W := hA _ hτ
      have hout : B (τ ω).toNNReal ω ∉ V := openExitTime_not_mem hV hc hfin
      have hu : B (τ ω).toNNReal ω ∉ U := fun hu => hout ⟨hu, hw⟩
      have hn : r ≤ ‖B (τ ω).toNNReal ω‖ := by
        simpa [U, Metric.mem_ball, dist_zero_right, not_lt] using hu
      simpa only [E, Set.mem_ofPred_eq, J, LinearIsometryEquiv.norm_map] using hn
  have hprob : P.real A ≤ P.real E + P.real F := by
    calc
      P.real A ≤ P.real (E ∪ F) :=
        ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae hsub)
      _ ≤ P.real E + P.real F := measureReal_union_le E F
  have hc : 0 ≤ Real.cos (p * (θ / 2)) * r ^ p := by
    have hc' : 0 < Real.cos (p * (θ / 2)) :=
      Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], by nlinarith⟩
    exact mul_nonneg hc'.le (Real.rpow_nonneg hr.le _)
  have hexit := brownian_wedge_subcritical_exit_bound hB (U := U) Metric.isOpen_ball
    Metric.isBounded_ball hθ0 hθπ hp hpθ hr hx
  change Real.cos (p * (θ / 2)) * r ^ p * P.real A ≤
    (J x ^ (p : ℂ)).re + Real.cos (p * (θ / 2)) * r ^ p * P.real F
  change Real.cos (p * (θ / 2)) * r ^ p * P.real E ≤ (J x ^ (p : ℂ)).re at hexit
  calc
    _ ≤ Real.cos (p * (θ / 2)) * r ^ p * (P.real E + P.real F) :=
      mul_le_mul_of_nonneg_left hprob hc
    _ = Real.cos (p * (θ / 2)) * r ^ p * P.real E +
        Real.cos (p * (θ / 2)) * r ^ p * P.real F := mul_add _ _ _
    _ ≤ _ := add_le_add hexit le_rfl

end LatticeProb
