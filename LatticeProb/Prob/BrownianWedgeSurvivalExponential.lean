import LatticeProb.Prob.BrownianWedgeSubcriticalExit
import LatticeProb.Prob.BrownianStayTail

/-! # Brownian wedge survival with an exponential remainder -/

set_option autoImplicit false

open MeasureTheory Set InnerProductSpace
open scoped NNReal ENNReal Topology

namespace LatticeProb

/-- The survival probability in a wedge is bounded by the subcritical power
profile and an exponential ball-staying remainder. -/
theorem brownian_wedge_survival_exponential :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {x : Euc 2}
      {B : ℝ≥0 → Ω → Euc 2} (_hB : IsBrownianSpace 2 x B P)
      {θ p r : ℝ} (_hθ0 : 0 < θ) (_hθπ : θ < Real.pi)
      (_hp : 0 < p) (_hpθ : p * θ < Real.pi) (_hr : 0 < r)
      (t : ℝ≥0) (_ht : 4 * r ^ 2 ≤ (t : ℝ)) (_hxr : ‖x‖ ≤ r),
      let J : Euc 2 → ℂ := Complex.orthonormalBasisOneI.repr.symm
      let W : Set (Euc 2) := {y | ((J y).re, (J y).im) ∈
        CorrelatedBM.openSymmetricWedge (Real.sin (θ / 2)) (Real.cos (θ / 2))}
      x ∈ closure W →
      Real.cos (p * (θ / 2)) * r ^ p * P.real {ω | ∀ s ≤ t, B s ω ∈ W} ≤
        (J x ^ (p : ℂ)).re + Real.cos (p * (θ / 2)) * r ^ p *
          (C * Real.exp (-(c * ((t : ℝ) / (4 * r ^ 2))))) := by
  obtain ⟨C, c, hC, hc, htail⟩ := exists_brownian_stay_tail 2 (by norm_num)
  refine ⟨C, c, hC, hc, ?_⟩
  intro Ω mΩ P x B hB θ p r hθ0 hθπ hp hpθ hr t ht hxr
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
  let F : Set Ω := {ω | ∀ s : ℝ≥0, (s : ℝ) ≤ (t : ℝ) → ‖B s ω - x‖ < 2 * r}
  have hJ : Continuous J := Complex.orthonormalBasisOneI.repr.symm.continuous
  have hW : IsOpen W := by
    apply (CorrelatedBM.isOpen_openSymmetricWedge _ _).preimage
    exact (Complex.continuous_re.comp hJ).prodMk (Complex.continuous_im.comp hJ)
  have hV : IsOpen V := Metric.isOpen_ball.inter hW
  have hVb : Bornology.IsBounded V := Metric.isBounded_ball.subset inter_subset_left
  have hsub : ∀ᵐ ω ∂P, ω ∈ A → ω ∈ E ∪ F := by
    filter_upwards [hB.cont, ae_openExitTime_ne_top (by norm_num) hB hVb] with ω hc' hfin hA
    by_cases ht' : (t : ℝ≥0∞) < τ ω
    · right
      intro s hs
      have hst : s ≤ t := by exact_mod_cast hs
      have hsτ : (s : ℝ≥0∞) < τ ω := lt_of_le_of_lt (by exact_mod_cast hst) ht'
      have hu : B s ω ∈ U := (mem_of_lt_openExitTime hsτ).1
      have hn : ‖B s ω‖ < r := by simpa [U, Metric.mem_ball, dist_zero_right] using hu
      calc
        ‖B s ω - x‖ ≤ ‖B s ω‖ + ‖x‖ := norm_sub_le _ _
        _ < 2 * r := by linarith
    · left
      have hτ : (τ ω).toNNReal ≤ t := by
        apply ENNReal.coe_le_coe.mp
        rw [ENNReal.coe_toNNReal hfin]
        exact le_of_not_gt ht'
      have hw : B (τ ω).toNNReal ω ∈ W := hA _ hτ
      have hout : B (τ ω).toNNReal ω ∉ V := openExitTime_not_mem hV hc' hfin
      have hu : B (τ ω).toNNReal ω ∉ U := fun hu => hout ⟨hu, hw⟩
      have hn : r ≤ ‖B (τ ω).toNNReal ω‖ := by
        simpa [U, Metric.mem_ball, dist_zero_right, not_lt] using hu
      simpa only [E, Set.mem_ofPred_eq, J, LinearIsometryEquiv.norm_map] using hn
  have hprob : P.real A ≤ P.real E + P.real F := by
    calc
      P.real A ≤ P.real (E ∪ F) :=
        ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae hsub)
      _ ≤ P.real E + P.real F := measureReal_union_le E F
  have hr2 : 0 < 4 * r ^ 2 := by positivity
  have hA1 : 1 ≤ (t : ℝ) / (4 * r ^ 2) := (le_div_iff₀ hr2).2 (by simpa using ht)
  have htime : (t : ℝ) / (4 * r ^ 2) * (2 * r) ^ 2 = (t : ℝ) := by
    field_simp
    ring
  have hF := htail x Ω P (inferInstance) B hB (2 * r) (by positivity)
    ((t : ℝ) / (4 * r ^ 2)) hA1
  rw [htime] at hF
  have hFreal : P.real F ≤ C * Real.exp (-(c * ((t : ℝ) / (4 * r ^ 2)))) := by
    have hnonneg : 0 ≤ C * Real.exp (-(c * ((t : ℝ) / (4 * r ^ 2)))) := by positivity
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hF).trans_eq (ENNReal.toReal_ofReal hnonneg)
  have hcoef : 0 ≤ Real.cos (p * (θ / 2)) * r ^ p := by
    have hc' : 0 < Real.cos (p * (θ / 2)) :=
      Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], by nlinarith⟩
    exact mul_nonneg hc'.le (Real.rpow_nonneg hr.le _)
  have hexit := brownian_wedge_subcritical_exit_bound hB (U := U) Metric.isOpen_ball
    Metric.isBounded_ball hθ0 hθπ hp hpθ hr hx
  change Real.cos (p * (θ / 2)) * r ^ p * P.real E ≤ (J x ^ (p : ℂ)).re at hexit
  change Real.cos (p * (θ / 2)) * r ^ p * P.real A ≤
    (J x ^ (p : ℂ)).re + Real.cos (p * (θ / 2)) * r ^ p *
      (C * Real.exp (-(c * ((t : ℝ) / (4 * r ^ 2)))))
  calc
    _ ≤ Real.cos (p * (θ / 2)) * r ^ p * (P.real E + P.real F) :=
      mul_le_mul_of_nonneg_left hprob hcoef
    _ = Real.cos (p * (θ / 2)) * r ^ p * P.real E +
        Real.cos (p * (θ / 2)) * r ^ p * P.real F := mul_add _ _ _
    _ ≤ _ := add_le_add hexit (mul_le_mul_of_nonneg_left hFreal hcoef)

end LatticeProb
