import Mathlib
import LatticeProb.LQG.LQGDyadicScaling
import LatticeProb.LQG.LQGCircleMoments
import LatticeProb.Gauss.UncorrelatedIndependence
import LatticeProb.LQG.LQGMeasureLocality

/-!
# Scaling and independence for the mass of a small ball under the approximate Liouville measure

Let `r = 2^{-j}`, `z ∈ ℂ`, and let `h'_ε(w) = h_{rε}(r w + z) - h_r(z)` be the dilated and recentred circle
averages.

* **Deterministic scaling** (`lqgApprox_ball_dyadic`): for every `ε ≥ 0` and `ρ`,
  `μ_{rε}(B(z, rρ)) = r^{2+γ²/2} e^{γ h_r(z)} μ'_ε(B(0, ρ))`, where `μ_ε = lqgApprox γ h ε` and
  `μ'_ε = lqgApprox γ h' ε`.
* **Independence** (`IsWholePlaneGFF.indepFun_circle_recentred`): if `‖z‖ + r ≤ 1`, the circle average `h_r(z)` of a
  whole-plane GFF is independent of the family `h'_δ(w)`, `w ∈ K`, whenever `‖w‖ + δ ≤ 1` on `K`; the family
  `h'_δ(w)` is uncorrelated with `h_r(z)` because the circle of radius `rδ` about `r w + z` lies in the disc of
  radius `r` about `z`, where the logarithmic potential of the circle of radius `r` is constant.
-/

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal

namespace LatticeProb.LQG

open LatticeProb.Gauss LQGDyadicScaling

/-- **Scaling of the ball mass of the approximation.** With `r = 2^{-j}`,
`μ_{rε}(B(z, rρ)) = r^{2+γ²/2} e^{γ h_r(z)} μ'_ε(B(0, ρ))`, `μ'` the approximation of the recentred and dilated
circle averages. -/
theorem lqgApprox_ball_dyadic {γ : ℝ} (hγ : γ ≠ 0) (h : ℝ → ℂ → ℝ) (j : ℕ) (z : ℂ) {ε : ℝ}
    (hε : 0 ≤ ε) (ρ : ℝ) :
    lqgApprox γ h (dyadicScale j * ε) (ball z (dyadicScale j * ρ)) =
      dyadicFactor γ j (h (dyadicScale j) z) *
        lqgApprox γ (fun s w => h (dyadicScale j * s) ((dyadicScale j : ℂ) * w + z) -
          h (dyadicScale j) z) ε (ball 0 ρ) := by
  have hr := dyadicScale_pos' j
  have h1 := LQGCoordChangeFixed.lqgApprox_dilate_translate hγ h hr hε z
  have e : (fun (s : ℝ) (u : ℂ) => h (dyadicScale j * s) ((dyadicScale j : ℂ) * u + z) +
      lqgQ γ * Real.log (dyadicScale j)) = fun s w =>
        (h (dyadicScale j * s) ((dyadicScale j : ℂ) * w + z) - h (dyadicScale j) z) +
          (h (dyadicScale j) z + lqgQ γ * Real.log (dyadicScale j)) := by
    funext s u; ring
  rw [e, lqgApprox_add_const] at h1
  have hpre : (fun x : ℂ => (x - z) / (dyadicScale j : ℂ)) ⁻¹' ball 0 ρ =
      ball z (dyadicScale j * ρ) := by
    ext x
    simp only [mem_preimage, Metric.mem_ball, dist_eq_norm, sub_zero, norm_div,
      Complex.norm_real, Real.norm_of_nonneg hr.le]
    rw [div_lt_iff₀ hr, mul_comm]
  have h2 := congrArg (fun m : Measure ℂ => m (ball 0 ρ)) h1
  simp only [Measure.smul_apply, smul_eq_mul] at h2
  rw [Measure.map_apply (by fun_prop) measurableSet_ball, hpre] at h2
  rw [← h2]
  congr 1
  unfold dyadicFactor
  rw [mul_add, Real.exp_add, LQGCoordChangeFixed.exp_mul_lqgQ_log hγ hr,
    rpow_two_add_half_sq hr, mul_comm (Real.exp _)]

end LatticeProb.LQG

namespace LatticeProb.Gauss

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Independence of a circle average from the recentred circle averages inside it.** If `‖z‖ + R ≤ 1` and
`‖w‖ + δ ≤ 1` for `w ∈ K`, then `h_R(z)` is independent of the family
`h_{Rδ}(R w + z) - h_R(z)`, `w ∈ K`. -/
theorem IsWholePlaneGFF.indepFun_circle_recentred (hh : IsWholePlaneGFF P hC hcirc) {R δ : ℝ}
    (hR : 0 < R) (hδ : 0 < δ) {z : ℂ} (hz : ‖z‖ + R ≤ 1) {K : Set ℂ}
    (hK : ∀ w ∈ K, ‖w‖ + δ ≤ 1) :
    IndepFun (fun ω => hcirc ω R z)
      (fun ω (w : K) => hcirc ω (R * δ) ((R : ℂ) * w + z) - hcirc ω R z) P := by
  have hRδ : 0 < R * δ := mul_pos hR hδ
  refine GaussIndep.indepFun_real_of_mem_span_of_covariance_eq_zero hh.isGaussianProcess
    (Submodule.subset_span ⟨⟨.circle R z, hR⟩, rfl⟩)
    (B := fun (w : K) ω => hcirc ω (R * δ) ((R : ℂ) * w + z) - hcirc ω R z)
    (fun w => GaussIndep.fun_sub_mem_span_range
      (fun (o : GFFObservable.Admissible) ω => o.1.eval (hC ω) (hcirc ω))
      ⟨.circle (R * δ) ((R : ℂ) * w + z), hRδ⟩ ⟨.circle R z, hR⟩) (fun w => ?_)
  have hw := hK w.1 w.2
  have hw' : ‖(R : ℂ) * w.1 + z‖ + R * δ ≤ 1 := by
    have h1 : ‖(R : ℂ) * w.1 + z‖ ≤ R * ‖w.1‖ + ‖z‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le]
    nlinarith
  have hP := hh.isProbabilityMeasure
  have hmem : ∀ (r : ℝ) (x : ℂ), 0 < r → MemLp (fun ω => hcirc ω r x) 2 P := fun r x hr =>
    (hh.hasGaussianLaw_circle hr x).memLp_two
  show cov[fun ω => hcirc ω R z, (fun ω => hcirc ω (R * δ) ((R : ℂ) * w.1 + z)) -
    (fun ω => hcirc ω R z); P] = 0
  rw [covariance_sub_right (hmem R z hR) (hmem _ _ hRδ) (hmem R z hR),
    hh.covariance_circle_inside hR hRδ hz hw', hh.covariance_circle_inside hR hR hz hz,
    circlePairPotential_self_center hR.le, max_self,
    circlePairPotential_of_ge hR (s := R * δ)]
  · have : max R ‖z - ((R : ℂ) * w.1 + z)‖ = R := by
      refine max_eq_left ?_
      have : ‖z - ((R : ℂ) * w.1 + z)‖ = R * ‖w.1‖ := by
        rw [show z - ((R : ℂ) * w.1 + z) = -((R : ℂ) * w.1) by ring, norm_neg, norm_mul,
          Complex.norm_real, Real.norm_of_nonneg hR.le]
      rw [this]; nlinarith
    rw [this]; ring
  · intro x hx
    have hx' : ‖x - z‖ = R := (mem_sphere_iff_norm.1 hx).trans (abs_of_pos hR)
    have h1 : ‖(R : ℂ) * w.1‖ = R * ‖w.1‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hR.le]
    have h2 := norm_sub_norm_le (x - z) ((R : ℂ) * w.1)
    have : x - ((R : ℂ) * w.1 + z) = (x - z) - (R : ℂ) * w.1 := by ring
    rw [this]
    nlinarith [norm_nonneg w.1]

end LatticeProb.Gauss

namespace LatticeProb

/-- If `a ↦ u w a` is measurable for every `w` in a second-countable metrizable space `K` and `w ↦ u w a` is
continuous for every `a`, then `a ↦ ∫⁻ w, F (u w a) dν(w)` is measurable (for the same σ-algebra on `α`). -/
theorem measurable_lintegral_of_continuous {α K : Type*} {mα : MeasurableSpace α} [TopologicalSpace K]
    [TopologicalSpace.MetrizableSpace K] [SecondCountableTopology K] [MeasurableSpace K] [OpensMeasurableSpace K]
    (ν : Measure K) [SFinite ν] {u : K → α → ℝ} (hcont : ∀ a, Continuous fun w => u w a)
    (hmeas : ∀ w, Measurable (u w)) {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    Measurable fun a => ∫⁻ w, F (u w a) ∂ν := by
  have hu := measurable_uncurry_of_continuous_of_measurable hcont hmeas
  exact (hF.comp hu).lintegral_prod_left'

end LatticeProb

namespace LatticeProb.LQG

open LatticeProb.Gauss LQGDyadicScaling

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Independence of `h_r(z)` from the ball mass of the recentred approximation.** For `r = 2^{-k}` with
`‖z‖ + r ≤ 1` and `ρ + δ ≤ 1`, the circle average `h_r(z)` is independent of
`μ'_δ(B(0, ρ))`, where `μ'_δ` is the approximation at scale `δ` of the circle averages
`h'_ε(w) = h_{rε}(r w + z) - h_r(z)`. -/
theorem IsWholePlaneGFF.indepFun_circle_lqgApprox_ball (hh : IsWholePlaneGFF P hC hcirc) (γ : ℝ) {k : ℕ}
    {z : ℂ} (hz : ‖z‖ + dyadicScale k ≤ 1) {δ ρ : ℝ} (hδ : 0 < δ) (hρδ : ρ + δ ≤ 1) :
    IndepFun (fun ω => hcirc ω (dyadicScale k) z)
      (fun ω => lqgApprox γ (recentredField hcirc k z ω) δ (ball 0 ρ)) P := by
  classical
  have hR := dyadicScale_pos' k
  obtain ⟨H, hHc, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hRδ : 0 < dyadicScale k * δ := mul_pos hR hδ
  have hK : ∀ w ∈ ball (0 : ℂ) ρ, ‖w‖ + δ ≤ 1 := fun w hw => by
    have := mem_ball_zero_iff.1 hw; linarith
  let Y : Ω → ball (0 : ℂ) ρ → ℝ := fun ω w =>
    H ω (dyadicScale k * δ) ((dyadicScale k : ℂ) * w + z) - H ω (dyadicScale k) z
  have hXY : (fun ω (w : ball (0 : ℂ) ρ) => hcirc ω (dyadicScale k * δ)
      ((dyadicScale k : ℂ) * w + z) - hcirc ω (dyadicScale k) z) =ᵐ[P] Y := by
    filter_upwards [hHae] with ω hω
    funext w
    simp only [Y, hω]
  have hind : IndepFun (fun ω => hcirc ω (dyadicScale k) z) Y P :=
    (hh.indepFun_circle_recentred hR hδ hz hK).congr Filter.EventuallyEq.rfl hXY
  let 𝒢 : MeasurableSpace Ω := MeasurableSpace.comap Y MeasurableSpace.pi
  have hY𝒢 : ∀ w : ball (0 : ℂ) ρ, Measurable[𝒢] (fun ω => Y ω w) := fun w =>
    (measurable_pi_apply w).comp (comap_measurable Y)
  have hcont : ∀ ω, Continuous fun w : ball (0 : ℂ) ρ => Y ω w := fun ω =>
    ((hHc ω _ hRδ).comp (by fun_prop : Continuous fun w : ball (0 : ℂ) ρ =>
      (dyadicScale k : ℂ) * (w : ℂ) + z)).sub continuous_const
  have : IsFiniteMeasure
      (Measure.comap Subtype.val (volume : Measure ℂ) : Measure (ball (0 : ℂ) ρ)) :=
    ⟨by rw [(MeasurableEmbedding.subtype_coe measurableSet_ball).comap_apply,
      Subtype.coe_image_univ]; exact measure_ball_lt_top⟩
  let F : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal (δ ^ (γ ^ 2 / 2) * Real.exp (γ * r))
  have hF : Measurable F := Measurable.ennreal_ofReal (by fun_prop)
  have hT𝒢 : Measurable[𝒢] fun ω => ∫⁻ w : ball (0 : ℂ) ρ, F (Y ω w)
      ∂(Measure.comap Subtype.val (volume : Measure ℂ)) :=
    measurable_lintegral_of_continuous (mα := 𝒢) _ hcont hY𝒢 hF
  have hae : (fun ω => lqgApprox γ (recentredField hcirc k z ω) δ (ball 0 ρ)) =ᵐ[P]
      fun ω => ∫⁻ w : ball (0 : ℂ) ρ, F (Y ω w)
        ∂(Measure.comap Subtype.val (volume : Measure ℂ)) := by
    filter_upwards [hHae] with ω hω
    simp only [lqgApprox]
    rw [withDensity_apply _ measurableSet_ball, ← lintegral_subtype_comap measurableSet_ball]
    refine lintegral_congr fun w => ?_
    simp only [F, Y, recentredField, hω]
  have hfin : IndepFun (fun ω => hcirc ω (dyadicScale k) z) (fun ω => ∫⁻ w : ball (0 : ℂ) ρ,
      F (Y ω w) ∂(Measure.comap Subtype.val (volume : Measure ℂ))) P :=
    indep_of_indep_of_le_right hind (measurable_iff_comap_le.1 hT𝒢)
  exact hfin.congr Filter.EventuallyEq.rfl hae.symm

end LatticeProb.LQG
