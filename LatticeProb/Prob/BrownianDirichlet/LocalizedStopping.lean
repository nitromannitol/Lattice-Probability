import LatticeProb.Prob.BrownianDirichlet.OptionalStopping
import LatticeProb.Prob.BrownianDirichlet.Localization
import LatticeProb.Prob.BrownianDirichlet.ScaledExit

/-!
# Localized discounted stopping for classical solutions

A compactly supported extension transfers discounted optional stopping to a classical
solution on a ball, stopped on an inner ball and at a bounded deterministic horizon.
-/

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Topology

noncomputable section

namespace LatticeProb

/-- A classical solution satisfies the discounted identity at a truncated inner-ball exit. -/
theorem localized_stopped_identity {d : ℕ} {μ : Measure (BrownianPath d)}
    (hμ : IsStandardBrownianLaw μ) {c : Euc d} {R a₀ μd : ℝ}
    (hR : 0 < R) (ha : 0 < a₀) (hμd : 0 < μd) {v g : Euc d → ℝ}
    (hv : ContDiffOn ℝ 2 v (Metric.ball c R))
    (hpde : ∀ y ∈ Metric.ball c R,
      μd * v y - a₀ * Laplacian.laplacian v y = g y)
    (k : ℕ) {x : Euc d} (hx : x ∈ Metric.ball c (innerRadius R k)) (N : ℝ≥0) :
    let σ := Real.sqrt (2 * a₀)
    let S := fun ω ↦ (min (scaledExit (Metric.ball c (innerRadius R k)) σ x ω)
      (N : ℝ≥0∞)).toNNReal
    v x = ∫ ω, Real.exp (-μd * (S ω : ℝ)) * v (x + σ • ω (S ω)) +
      (∫ t in (0 : ℝ)..(S ω : ℝ),
        Real.exp (-μd * t) * g (x + σ • ω t.toNNReal)) ∂μ := by
  intro σ S
  let B := Metric.ball c (innerRadius R k)
  let τ := scaledExit B σ x
  have hfin (ω) : min (τ ω) (N : ℝ≥0∞) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (min_le_right _ _)
  have hcoe (ω) : (S ω : ℝ≥0∞) = min (τ ω) (N : ℝ≥0∞) :=
    ENNReal.coe_toNNReal (hfin ω)
  have hstop : IsStoppingTime (brownianNaturalFiltration d)
      (fun ω ↦ (S ω : ℝ≥0∞)) := by
    simp_rw [hcoe]
    exact (isStoppingTime_scaledExit Metric.isOpen_ball σ x).min_const N
  have hbound (ω) : S ω ≤ N := by
    rw [← ENNReal.coe_le_coe, hcoe]
    exact min_le_right _ _
  have hσ : 0 < σ := Real.sqrt_pos.2 (mul_pos (by norm_num) ha)
  have hnorm : σ ^ 2 / 2 = a₀ := by
    dsimp [σ]
    rw [Real.sq_sqrt (by positivity)]
    ring
  obtain ⟨f, W, hW, hBW, hWB, hf, hc, _, heq⟩ := exists_local_extension hR hv k
  have hfx : f x = v x := heq (hBW (subset_closure hx))
  have hbefore (ω) {t : ℝ≥0} (ht : t < S ω) : x + σ • ω t ∈ B := by
    apply mem_of_lt_scaledExit
    have ht' := ENNReal.coe_lt_coe.mpr ht
    rw [hcoe] at ht'
    exact ht'.trans_le (min_le_left _ _)
  have hend (ω : BrownianPath d) (hω : ω 0 = 0) :
      x + σ • ω (S ω) ∈ closure B := by
    have hle : (S ω : ℝ≥0∞) ≤ τ ω := by
      rw [hcoe]
      exact min_le_left _ _
    rcases lt_or_eq_of_le hle with hlt | he
    · exact subset_closure (mem_of_lt_scaledExit hlt)
    · have htfin : τ ω ≠ ⊤ := he ▸ ENNReal.coe_ne_top
      have ht : S ω = (τ ω).toNNReal := by rw [← he, ENNReal.toNNReal_coe]
      rw [ht]
      apply frontier_subset_closure
      apply continuousExitTime_mem_frontier Metric.isOpen_ball _ htfin
      simpa only [scalePath_apply, hω, smul_zero, add_zero] using hx
  have hidentity := integral_discounted_stopped hμ hf hc hσ hμd x hstop N hbound
  rw [hfx] at hidentity
  refine hidentity.symm.trans (integral_congr_ae ?_)
  filter_upwards [standardBrownianLaw_eval_zero_ae hμ] with ω hω
  unfold discountedObservable
  rw [heq (hBW (hend ω hω))]
  congr 1
  apply intervalIntegral.integral_congr_Ioo_of_le (S ω).coe_nonneg
  intro t ht
  have htt : t.toNNReal < S ω := by
    exact (Real.toNNReal_lt_iff_lt_coe ht.1.le).2 ht.2
  have hyW := hBW (subset_closure (hbefore ω htt))
  obtain ⟨hlap, hval⟩ := laplacian_eq_of_eqOn hW heq hyW
  change Real.exp (-μd * t) *
    (μd * f (x + σ • ω t.toNNReal) -
      σ ^ 2 / 2 * Laplacian.laplacian f (x + σ • ω t.toNNReal)) = _
  rw [hnorm, hlap, hval, hpde _ (hWB hyW)]

end LatticeProb
