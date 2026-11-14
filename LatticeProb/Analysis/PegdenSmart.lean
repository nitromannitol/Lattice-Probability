import Mathlib
import LatticeProb.Analysis.JensenWeak

/-!
# The strict interior maximum of Pegden-Smart, Proposition 2.5

Let `u` be continuous on the closed unit ball of a finite-dimensional real inner product space `E`,
a weak solution of `Δ u = s` in the open ball with `s` essentially bounded, and suppose that the
supremum of `u` over the ball exceeds the supremum over the sphere. Then, assuming that a continuous
weak solution has a second-order Taylor expansion with Peano remainder at almost every point of the
ball (Proposition 2.4 of Pegden-Smart, in the weaker form), the set of points above the boundary
supremum where `u` has a Taylor expansion with negative definite second derivative has positive
measure.

Proof: let `x₀` be a point where `u` is close to its supremum and perturb `u` by `η ‖x - x₀‖²`, which
is again a weak solution of a bounded right-hand side (`pegdenSmart_prop25_of_peano`). For a radius
`r < 1` close to `1`, Jensen's lemma (`jensen_weak`) shows that the points of `closedBall 0 r` that
maximise the perturbed function plus a linear function with small slope form a set of positive measure.
These points lie in the open ball, above the boundary supremum. At such a point where `u` has a Taylor
expansion, the perturbed function has the expansion with second derivative `B + 2 η I`, and the
contact gives `⟪(B + 2 η I) v, v⟫ ≤ 0` (`inner_le_of_contact`).
-/

open MeasureTheory Metric Filter Topology Set Asymptotics
open scoped InnerProductSpace ContDiff
open Laplacian

namespace LatticeProb.PegdenSmart

namespace Prop25

section OneDim

/-- A function on the line with an expansion `a t + b t ^ 2 + o (t ^ 2)` at `0` that is nonpositive near
`0` has `b ≤ 0`. -/
theorem coeff_le_zero_of_expansion {g : ℝ → ℝ} {a b : ℝ}
    (hg : (fun t => g t - (a * t + b * t ^ 2)) =o[𝓝 0] fun t => t ^ 2)
    (hmax : ∀ᶠ t in 𝓝 0, g t ≤ 0) : b ≤ 0 := by
  by_contra hb
  rw [not_le] at hb
  have h1 := hg.def (show 0 < b / 2 by positivity)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (h1.and hmax)
  have hs : 0 < δ / 2 := by positivity
  have hp := hball (y := δ / 2) (by rw [Real.dist_eq, sub_zero, abs_of_pos hs]; linarith)
  have hm := hball (y := -(δ / 2)) (by rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos hs]; linarith)
  obtain ⟨hp1, hp2⟩ := hp
  obtain ⟨hm1, hm2⟩ := hm
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (δ / 2)), abs_le] at hp1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (-(δ / 2))), abs_le] at hm1
  have hpow : 0 < (δ / 2) ^ 2 := by positivity
  nlinarith [hp1.1, hm1.1, mul_pos hb hpow]

end OneDim

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Contact

omit [FiniteDimensional ℝ E] in
/-- At a point of contact where `u` has a Taylor expansion, the quadratic perturbation `η ‖y - x₀‖ ^ 2`
shifts the second derivative form by `2 η ‖v‖ ^ 2`: if `x` is interior to the ball and maximises
`u y + η ‖y - x₀‖ ^ 2 + ⟪p, y⟫` over the ball, then `⟪B v, v⟫ + 2 η ‖v‖ ^ 2 ≤ 0`. -/
theorem inner_le_of_contact {u : E → ℝ} {x x₀ p p₀ : E} {B : E →L[ℝ] E} {η r : ℝ}
    (hx : x ∈ ball (0 : E) r)
    (hpeano : (fun y => u y - u x - ⟪p₀, y - x⟫_ℝ - 1 / 2 * ⟪B (y - x), y - x⟫_ℝ) =o[𝓝 x]
      fun y => ‖y - x‖ ^ 2)
    (hcontact : ∀ y ∈ closedBall (0 : E) r,
      u y + η * ‖y - x₀‖ ^ 2 + ⟪p, y⟫_ℝ ≤ u x + η * ‖x - x₀‖ ^ 2 + ⟪p, x⟫_ℝ) (v : E) :
    ⟪B v, v⟫_ℝ + 2 * η * ‖v‖ ^ 2 ≤ 0 := by
  have hT : Tendsto (fun t : ℝ => x + t • v) (𝓝 0) (𝓝 x) := by
    have hc : Continuous fun t : ℝ => x + t • v := by fun_prop
    simpa using hc.tendsto 0
  have hcomp := hpeano.comp_tendsto hT
  have hbig : (fun t : ℝ => ‖x + t • v - x‖ ^ 2) =O[𝓝 0] fun t : ℝ => t ^ 2 := by
    refine IsBigO.of_bound (‖v‖ ^ 2) (Eventually.of_forall fun t => ?_)
    have e : x + t • v - x = t • v := by abel
    simp only [norm_pow, norm_norm, norm_mul, e, norm_smul]
    exact le_of_eq (by ring)
  have hlo := hcomp.trans_isBigO hbig
  set a : ℝ := ⟪p₀, v⟫_ℝ + 2 * η * ⟪x - x₀, v⟫_ℝ + ⟪p, v⟫_ℝ with ha
  set b : ℝ := 1 / 2 * ⟪B v, v⟫_ℝ + η * ‖v‖ ^ 2 with hb
  set g : ℝ → ℝ := fun t => u (x + t • v) + η * ‖x + t • v - x₀‖ ^ 2 + ⟪p, x + t • v⟫_ℝ -
    (u x + η * ‖x - x₀‖ ^ 2 + ⟪p, x⟫_ℝ) with hg
  have hid : ∀ t : ℝ, g t - (a * t + b * t ^ 2) =
      u (x + t • v) - u x - ⟪p₀, x + t • v - x⟫_ℝ - 1 / 2 * ⟪B (x + t • v - x), x + t • v - x⟫_ℝ := by
    intro t
    have e1 : x + t • v - x = t • v := by abel
    have e2 : x + t • v - x₀ = (x - x₀) + t • v := by abel
    rw [hg, ha, hb]
    simp only [e1, e2, norm_add_sq_real, inner_add_right, inner_smul_right, inner_smul_left,
      map_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, RCLike.conj_to_real]
    ring
  have hlo' : (fun t => g t - (a * t + b * t ^ 2)) =o[𝓝 0] fun t : ℝ => t ^ 2 := by
    refine hlo.congr_left fun t => ?_
    exact (hid t).symm
  have hmax : ∀ᶠ t in 𝓝 0, g t ≤ 0 := by
    filter_upwards [hT.eventually (isOpen_ball.mem_nhds hx)] with t ht
    have := hcontact _ (ball_subset_closedBall ht)
    rw [hg]
    linarith
  have := coeff_le_zero_of_expansion hlo' hmax
  rw [hb] at this
  linarith

end Contact

section Weak

variable [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

theorem integral_mul_fderiv_eq_neg {F ψ : E → ℝ} (hF : ContDiff ℝ ∞ F) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (v : E) :
    ∫ x, F x * fderiv ℝ ψ x v ∂μ = -∫ x, fderiv ℝ F x v * ψ x ∂μ := by
  have hFc : Continuous F := hF.continuous
  have hF'c : Continuous fun x => fderiv ℝ F x v := (contDiff_fderiv_apply hF v).continuous
  have hψ'c : Continuous fun x => fderiv ℝ ψ x v := (contDiff_fderiv_apply hψ v).continuous
  have hψ'cs : HasCompactSupport fun x => fderiv ℝ ψ x v := hc.fderiv_apply ℝ v
  refine integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ?_ ?_ ?_
    (fun x _ => hF.differentiable (by simp) x) (fun x _ => hψ.differentiable (by simp) x)
  · exact (hF'c.mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left
  · exact (hFc.mul hψ'c).integrable_of_hasCompactSupport hψ'cs.mul_left
  · exact (hFc.mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left

theorem integral_mul_fderiv_fderiv_eq {F ψ : E → ℝ} (hF : ContDiff ℝ ∞ F) (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (v : E) :
    ∫ x, F x * fderiv ℝ (fun z => fderiv ℝ ψ z v) x v ∂μ =
      ∫ x, fderiv ℝ (fun z => fderiv ℝ F z v) x v * ψ x ∂μ := by
  have h1 : ∫ x, F x * fderiv ℝ (fun z => fderiv ℝ ψ z v) x v ∂μ =
      -∫ x, fderiv ℝ F x v * fderiv ℝ ψ x v ∂μ :=
    integral_mul_fderiv_eq_neg (ψ := fun z => fderiv ℝ ψ z v) hF (contDiff_fderiv_apply hψ v)
      (hc.fderiv_apply ℝ v) v
  have h2 : ∫ x, fderiv ℝ F x v * fderiv ℝ ψ x v ∂μ =
      -∫ x, fderiv ℝ (fun z => fderiv ℝ F z v) x v * ψ x ∂μ :=
    integral_mul_fderiv_eq_neg (F := fun z => fderiv ℝ F z v) (contDiff_fderiv_apply hF v) hψ hc v
  rw [h1, h2, neg_neg]

end Weak

section Quadratic

omit [FiniteDimensional ℝ E] in
theorem fderiv_quad (x₀ z v : E) :
    fderiv ℝ (fun y : E => ‖y - x₀‖ ^ 2) z v = 2 * ⟪z - x₀, v⟫_ℝ := by
  have h : HasFDerivAt (fun y : E => ‖y - x₀‖ ^ 2)
      (2 • (innerSL ℝ (z - x₀)).comp (ContinuousLinearMap.id ℝ E)) z :=
    ((hasFDerivAt_id z).sub_const x₀).norm_sq
  rw [h.fderiv]
  simp [inner_sub_left]

omit [FiniteDimensional ℝ E] in
theorem fderiv_fderiv_quad (x₀ y v : E) :
    fderiv ℝ (fun z : E => fderiv ℝ (fun w : E => ‖w - x₀‖ ^ 2) z v) y v = 2 * ⟪v, v⟫_ℝ := by
  have h1 : (fun z : E => fderiv ℝ (fun w : E => ‖w - x₀‖ ^ 2) z v) =
      fun z => 2 * ⟪v, z - x₀⟫_ℝ := by
    funext z
    rw [fderiv_quad]
    congr 1
    exact real_inner_comm _ _
  rw [h1]
  have h2 : HasFDerivAt (fun z : E => ⟪v, z - x₀⟫_ℝ)
      ((innerSL ℝ v).comp (ContinuousLinearMap.id ℝ E)) y :=
    (innerSL ℝ v).hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const x₀)
  rw [(h2.const_mul 2).fderiv]
  simp

theorem laplacian_eq_sum_fderiv {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    Δ ψ = fun y => ∑ i, fderiv ℝ (fun y' => fderiv ℝ ψ y' (stdOrthonormalBasis ℝ E i)) y
      (stdOrthonormalBasis ℝ E i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  funext y
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_two_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  have hd : DifferentiableAt ℝ (fderiv ℝ ψ) y :=
    (hψ.fderiv_right (m := ∞) (by simp)).differentiable (by simp) y
  rw [fderiv_clm_apply hd (differentiableAt_const (stdOrthonormalBasis ℝ E i))]
  simp

theorem continuous_laplacian {ψ : E → ℝ} (hψ : ContDiff ℝ ∞ ψ) : Continuous (Δ ψ) := by
  rw [laplacian_eq_sum_fderiv hψ]
  exact continuous_finsetSum _ fun i _ =>
    (contDiff_fderiv_apply (contDiff_fderiv_apply hψ _) _).continuous

theorem laplacian_eq_zero_of_notMem_tsupport {ψ : E → ℝ} {x : E} (hx : x ∉ tsupport ψ) :
    Δ ψ x = 0 := by
  have hev : ψ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := notMem_tsupport_iff_eventuallyEq.1 hx
  rw [(InnerProductSpace.laplacian_congr_nhds hev).eq_of_nhds]
  simp

theorem hasCompactSupport_laplacian {ψ : E → ℝ} (hc : HasCompactSupport ψ) :
    HasCompactSupport (Δ ψ) :=
  HasCompactSupport.intro hc fun _ hx => laplacian_eq_zero_of_notMem_tsupport hx

variable [MeasurableSpace E] [BorelSpace E]

/-- Green's identity for the quadratic `‖x - x₀‖ ^ 2`, whose Laplacian is `2 dim E`. -/
theorem integral_quad_mul_laplacian (μ : Measure E) [μ.IsAddHaarMeasure] {ψ : E → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (x₀ : E) :
    ∫ x, ‖x - x₀‖ ^ 2 * Δ ψ x ∂μ = 2 * (Module.finrank ℝ E : ℝ) * ∫ x, ψ x ∂μ := by
  have hq : ContDiff ℝ ∞ fun x : E => ‖x - x₀‖ ^ 2 :=
    (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)
  set b := stdOrthonormalBasis ℝ E with hb
  have hint : ∀ i, Integrable (fun x => ‖x - x₀‖ ^ 2 *
      fderiv ℝ (fun y => fderiv ℝ ψ y (b i)) x (b i)) μ := fun i =>
    (hq.continuous.mul (contDiff_fderiv_apply (contDiff_fderiv_apply hψ _) _).continuous)
      |>.integrable_of_hasCompactSupport (((hc.fderiv_apply ℝ _).fderiv_apply ℝ _).mul_left)
  rw [laplacian_eq_sum_fderiv hψ]
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ => hint i]
  have hi : ∀ i, ∫ x, ‖x - x₀‖ ^ 2 * fderiv ℝ (fun y => fderiv ℝ ψ y (b i)) x (b i) ∂μ =
      2 * ∫ x, ψ x ∂μ := fun i => by
    rw [integral_mul_fderiv_fderiv_eq hq hψ hc (b i)]
    simp_rw [fderiv_fderiv_quad, real_inner_self_eq_norm_sq, b.orthonormal.1 i]
    simp [integral_const_mul]
  rw [Finset.sum_congr rfl fun i _ => hi i]
  simp
  ring

end Quadratic

theorem exists_ae_abs_le {α : Type*} [MeasurableSpace α] {ν : Measure α} {s : α → ℝ}
    (hs : MemLp s ⊤ ν) : ∃ K : ℝ, 0 ≤ K ∧ ∀ᵐ x ∂ν, |s x| ≤ K := by
  refine ⟨(eLpNormEssSup s ν).toReal, ENNReal.toReal_nonneg, ?_⟩
  have hfin : eLpNormEssSup s ν < ⊤ := by
    have := hs.eLpNorm_lt_top
    rw [eLpNorm_exponent_top] at this
    exact this
    exact hs.aestronglyMeasurable
  filter_upwards [ae_le_eLpNormEssSup (f := s) (μ := ν)] with x hx
  have h := ENNReal.toReal_mono hfin.ne hx
  rwa [toReal_enorm, Real.norm_eq_abs] at h

section Perturb

variable [MeasurableSpace E] [BorelSpace E]

/-- Adding `η ‖x - x₀‖ ^ 2` to a weak solution of `Δ u = s` gives a weak solution of
`Δ w = s + 2 η dim E`. -/
theorem isWeakSolutionLaplace_add_quad (μ : Measure E) [μ.IsAddHaarMeasure] {U : Set E}
    {u s : E → ℝ} {K : ℝ} (hu : ContinuousOn u U) (hsm : AEStronglyMeasurable s (μ.restrict U))
    (hs : ∀ᵐ x ∂μ.restrict U, |s x| ≤ K) (hweak : IsWeakSolutionLaplace μ U u s) (η : ℝ) (x₀ : E) :
    IsWeakSolutionLaplace μ U (fun x => u x + η * ‖x - x₀‖ ^ 2)
      (fun x => s x + 2 * η * (Module.finrank ℝ E : ℝ)) := by
  intro ψ hψ hc hsupp
  have h := hweak ψ hψ hc hsupp
  have hΔc := continuous_laplacian hψ
  have hΔs := hasCompactSupport_laplacian hc
  have hq : Continuous fun x : E => ‖x - x₀‖ ^ 2 := by fun_prop
  have hψi : Integrable ψ μ := hψ.continuous.integrable_of_hasCompactSupport hc
  have hI1 : Integrable (fun x => u x * Δ ψ x) μ := by
    have h1 : IntegrableOn (fun x => u x * Δ ψ x) (tsupport ψ) μ :=
      ((hu.mono hsupp).mul hΔc.continuousOn).integrableOn_compact hc.isCompact
    refine (integrableOn_iff_integrable_of_support_subset ?_).1 h1
    intro x hx
    by_contra hxt
    exact hx (by simp [laplacian_eq_zero_of_notMem_tsupport hxt])
  have hI2 : Integrable (fun x => ‖x - x₀‖ ^ 2 * Δ ψ x) μ :=
    (hq.mul hΔc).integrable_of_hasCompactSupport hΔs.mul_left
  have hI3 : Integrable (fun x => s x * ψ x) μ := by
    have hsup : Function.support (fun x => s x * ψ x) ⊆ U := fun x hx =>
      hsupp (subset_tsupport ψ (right_ne_zero_of_mul hx))
    refine (integrableOn_iff_integrable_of_support_subset hsup).1 ?_
    refine Integrable.mono' (((hψi.abs).const_mul K).integrableOn)
      (hsm.mul hψ.continuous.aestronglyMeasurable) ?_
    filter_upwards [hs] with x hx
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
  have hquad := integral_quad_mul_laplacian μ hψ hc x₀
  calc ∫ x, (u x + η * ‖x - x₀‖ ^ 2) * Δ ψ x ∂μ
      = ∫ x, u x * Δ ψ x ∂μ + η * ∫ x, ‖x - x₀‖ ^ 2 * Δ ψ x ∂μ := by
        simp_rw [add_mul, mul_assoc]
        rw [integral_add hI1 (hI2.const_mul η), integral_const_mul]
    _ = ∫ x, (s x + 2 * η * (Module.finrank ℝ E : ℝ)) * ψ x ∂μ := by
        simp_rw [add_mul]
        rw [integral_add hI3 (hψi.const_mul _), integral_const_mul, h, hquad]
        ring

end Perturb

omit [FiniteDimensional ℝ E] in
/-- A function continuous on the closed unit ball and at most `m` on the unit sphere is less than
`m + θ` on every sphere of radius `r` close enough to `1`. -/
theorem exists_sphere_margin {u : E → ℝ} (hu : ContinuousOn u (closedBall (0 : E) 1))
    [ProperSpace E] {m θ ρ₀ : ℝ} (hθ : 0 < θ) (hm : ∀ y ∈ sphere (0 : E) 1, u y ≤ m)
    (hρ₀ : 0 ≤ ρ₀) (hρ₀1 : ρ₀ < 1) :
    ∃ r, ρ₀ < r ∧ r < 1 ∧ ∀ y ∈ sphere (0 : E) r, u y < m + θ := by
  obtain ⟨ρ, hρ, hunif⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_closedBall (0 : E) 1).uniformContinuousOn_of_continuous hu) θ hθ
  set c : ℝ := max ρ₀ (1 - ρ) with hc
  have hc1 : c < 1 := max_lt hρ₀1 (by linarith)
  have hc0 : 0 ≤ c := le_max_of_le_left hρ₀
  have hρc : ρ₀ ≤ c := le_max_left _ _
  refine ⟨(c + 1) / 2, by linarith, by linarith, fun y hy => ?_⟩
  have hr0 : 0 < (c + 1) / 2 := by linarith
  have hyn : ‖y‖ = (c + 1) / 2 := mem_sphere_zero_iff_norm.1 hy
  have hy' : ((c + 1) / 2)⁻¹ • y ∈ sphere (0 : E) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, hyn, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr0),
      inv_mul_cancel₀ hr0.ne']
  have hdist : dist y (((c + 1) / 2)⁻¹ • y) < ρ := by
    rw [dist_eq_norm]
    have : y - ((c + 1) / 2)⁻¹ • y = (1 - ((c + 1) / 2)⁻¹) • y := by rw [sub_smul, one_smul]
    rw [this, norm_smul, hyn, Real.norm_eq_abs,
      abs_of_nonpos (by rw [sub_nonpos]; exact (one_le_inv₀ hr0).2 (by linarith))]
    have h2 : (-(1 - ((c + 1) / 2)⁻¹)) * ((c + 1) / 2) = 1 - (c + 1) / 2 := by
      field_simp
      ring
    rw [h2]
    have : 1 - ρ ≤ c := le_max_right _ _
    linarith
  have hyc : y ∈ closedBall (0 : E) 1 := by
    rw [mem_closedBall_zero_iff, hyn]; linarith
  have h1 := hunif y hyc _ (sphere_subset_closedBall hy') hdist
  rw [Real.dist_eq] at h1
  have h2 := (abs_lt.1 h1).2
  linarith [hm _ hy']

end Prop25

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Main

variable [MeasurableSpace E] [BorelSpace E]

/-- **Pegden-Smart, Proposition 2.5, from Proposition 2.4.** Let `u` be continuous on the closed unit
ball, a weak solution of `Δ u = s` in the open ball with `s` essentially bounded, and suppose that
`sup_{∂B₁} u < sup_{B₁} u`. If a continuous weak solution of such an equation has a second-order Taylor
expansion with Peano remainder and self-adjoint second derivative at almost every point of the open ball
(the hypothesis `hP`, Proposition 2.4 in its weaker form), then the points of the ball above
`sup_{∂B₁} u` where `u` has such an expansion with negative definite second derivative form a set of
positive (outer) measure. -/
theorem pegdenSmart_prop25_of_peano (μ : Measure E) [μ.IsAddHaarMeasure]
    (hP : ∀ s u : E → ℝ, MemLp s ⊤ (μ.restrict (ball (0 : E) 1)) → ContinuousOn u (ball 0 1) →
      IsWeakSolutionLaplace μ (ball 0 1) u s →
        ∀ᵐ x ∂(μ.restrict (ball (0 : E) 1)), ∃ (p : E) (B : E →L[ℝ] E), IsSelfAdjoint B ∧
          (fun y => u y - u x - ⟪p, y - x⟫_ℝ - 1 / 2 * ⟪B (y - x), y - x⟫_ℝ) =o[𝓝 x]
            fun y => ‖y - x‖ ^ 2) :
    ∀ s u : E → ℝ, MemLp s ⊤ (μ.restrict (ball (0 : E) 1)) → ContinuousOn u (closedBall 0 1) →
      IsWeakSolutionLaplace μ (ball 0 1) u s →
      sSup (u '' sphere 0 1) < sSup (u '' ball 0 1) →
        0 < μ {x | x ∈ ball (0 : E) 1 ∧ sSup (u '' sphere 0 1) < u x ∧
          ∃ (p : E) (B : E →L[ℝ] E), IsSelfAdjoint B ∧
            (fun y => u y - u x - ⟪p, y - x⟫_ℝ - 1 / 2 * ⟪B (y - x), y - x⟫_ℝ) =o[𝓝 x]
              (fun y => ‖y - x‖ ^ 2) ∧
            ∀ v : E, v ≠ 0 → ⟪B v, v⟫_ℝ < 0} := by
  intro s u hs hu hweak hlt
  set m : ℝ := sSup (u '' sphere (0 : E) 1) with hm
  set M : ℝ := sSup (u '' ball (0 : E) 1) with hM
  have hbS : BddAbove (u '' sphere (0 : E) 1) :=
    (isCompact_sphere (0 : E) 1).bddAbove_image (hu.mono sphere_subset_closedBall)
  have hmle : ∀ y ∈ sphere (0 : E) 1, u y ≤ m := fun y hy =>
    le_csSup hbS (mem_image_of_mem u hy)
  have hDpos : 0 < M - m := sub_pos.2 hlt
  set D : ℝ := M - m with hD
  obtain ⟨K, hK0, hK⟩ := Prop25.exists_ae_abs_le hs
  obtain ⟨_, ⟨x₀, hx₀, rfl⟩, hux₀⟩ := exists_lt_of_lt_csSup
    ((nonempty_ball.2 one_pos).image u) (show M - D / 8 < M by linarith)
  have hx₀1 : ‖x₀‖ < 1 := mem_ball_zero_iff.1 hx₀
  set η : ℝ := D / 32 with hη
  set δ : ℝ := D / 32 with hδ
  have hηpos : 0 < η := by positivity
  have hδpos : 0 < δ := by positivity
  obtain ⟨r, hr0, hr1, hrm⟩ := Prop25.exists_sphere_margin hu (θ := D / 8) (by positivity) hmle
    (norm_nonneg x₀) hx₀1
  have hrpos : 0 < r := lt_of_le_of_lt (norm_nonneg _) hr0
  have hx₀r : x₀ ∈ ball (0 : E) r := mem_ball_zero_iff.2 hr0
  have hcbU : closedBall (0 : E) r ⊆ ball 0 1 := closedBall_subset_ball hr1
  set n : ℝ := (Module.finrank ℝ E : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  set w : E → ℝ := fun x => u x + η * ‖x - x₀‖ ^ 2 with hw
  set K' : ℝ := K + 2 * η * n with hK'
  have hK'0 : 0 ≤ K' := by positivity
  have hwcont : ContinuousOn w (ball 0 1) :=
    (hu.mono ball_subset_closedBall).add (by fun_prop)
  have hweak' : IsWeakSolutionLaplace μ (ball 0 1) w (fun x => s x + 2 * η * n) :=
    Prop25.isWeakSolutionLaplace_add_quad μ (hu.mono ball_subset_closedBall) hs.aestronglyMeasurable hK
      hweak η x₀
  have hsm' : AEStronglyMeasurable (fun x => s x + 2 * η * n) (μ.restrict (ball 0 1)) :=
    hs.aestronglyMeasurable.add aestronglyMeasurable_const
  have hs' : ∀ᵐ x ∂μ.restrict (ball (0 : E) 1), |s x + 2 * η * n| ≤ K' := by
    filter_upwards [hK] with x hx
    calc |s x + 2 * η * n| ≤ |s x| + |2 * η * n| := abs_add_le _ _
      _ ≤ K + 2 * η * n := by
        rw [abs_of_nonneg (by positivity : 0 ≤ 2 * η * n)]
        linarith
  have hwx₀ : w x₀ = u x₀ := by simp [hw]
  have hnorm : ∀ y : E, ‖y‖ ≤ r → ‖y - x₀‖ ≤ 2 * r := fun y hy =>
    (norm_sub_le _ _).trans (by linarith)
  have hmargin : ∀ y ∈ sphere (0 : E) r, w y < w x₀ - 2 * δ * r := by
    intro y hy
    have h1 := hrm y hy
    have hy' : ‖y‖ = r := mem_sphere_zero_iff_norm.1 hy
    have h2 := hnorm y hy'.le
    have h3 : ‖y - x₀‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (y - x₀)]
    have h4 : η * ‖y - x₀‖ ^ 2 ≤ η * 4 := mul_le_mul_of_nonneg_left h3 hηpos.le
    rw [hwx₀]
    show u y + η * ‖y - x₀‖ ^ 2 < u x₀ - 2 * δ * r
    nlinarith
  have hJ := jensen_weak μ (ball (0 : E) 1) w (fun x => s x + 2 * η * n) 0 x₀ r K' δ
    isOpen_ball hcbU hrpos hK'0 hδpos hwcont hweak' hsm' hs' hx₀r hmargin
  set Sc : Set E := {x ∈ closedBall (0 : E) r | ∃ p : E, ‖p‖ < δ ∧
    ∀ y ∈ closedBall (0 : E) r, w y + ⟪p, y⟫_ℝ ≤ w x + ⟪p, x⟫_ℝ} with hSc
  have hSc_pos : 0 < μ Sc := by
    by_contra hnot
    have h0 : μ Sc = 0 := le_antisymm (not_lt.1 hnot) zero_le
    rw [h0, mul_zero] at hJ
    exact (Metric.measure_ball_pos μ (0 : E) hδpos).ne' (le_antisymm hJ zero_le)
  have hpts : ∀ x ∈ Sc, x ∈ ball (0 : E) r ∧ m < u x ∧ ∃ p : E, ‖p‖ < δ ∧
      ∀ y ∈ closedBall (0 : E) r, w y + ⟪p, y⟫_ℝ ≤ w x + ⟪p, x⟫_ℝ := by
    rintro x ⟨hxc, p, hp, hmax⟩
    have hxr : ‖x‖ ≤ r := mem_closedBall_zero_iff.1 hxc
    have hxx₀ := hnorm x hxr
    have hineq := hmax x₀ (ball_subset_closedBall hx₀r)
    have hinner : ⟪p, x - x₀⟫_ℝ ≤ ‖p‖ * ‖x - x₀‖ := real_inner_le_norm _ _
    have hpb : ‖p‖ * ‖x - x₀‖ ≤ δ * (2 * r) :=
      mul_le_mul hp.le hxx₀ (norm_nonneg _) hδpos.le
    have hlow : w x₀ - 2 * δ * r ≤ w x := by
      have : ⟪p, x⟫_ℝ - ⟪p, x₀⟫_ℝ = ⟪p, x - x₀⟫_ℝ := (inner_sub_right _ _ _).symm
      nlinarith
    have hxball : x ∈ ball (0 : E) r := by
      by_contra hnot
      have hxs : x ∈ sphere (0 : E) r := by
        rw [mem_sphere_zero_iff_norm]
        have : ¬ ‖x‖ < r := fun h => hnot (mem_ball_zero_iff.2 h)
        linarith
      have := hmargin x hxs
      linarith
    refine ⟨hxball, ?_, p, hp, hmax⟩
    have hxr' : ‖x‖ < r := mem_ball_zero_iff.1 hxball
    have h2 := hnorm x hxr'.le
    have h3 : ‖x - x₀‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (x - x₀)]
    have h4 : η * ‖x - x₀‖ ^ 2 ≤ η * 4 := mul_le_mul_of_nonneg_left h3 hηpos.le
    have hwx : w x = u x + η * ‖x - x₀‖ ^ 2 := rfl
    rw [hwx₀] at hlow
    nlinarith
  have hpeano := hP s u hs (hu.mono ball_subset_closedBall) hweak
  have hae := (ae_restrict_iff' measurableSet_ball).1 hpeano
  refine lt_of_lt_of_le hSc_pos (measure_mono_ae ?_)
  filter_upwards [hae] with x hx hxS
  obtain ⟨hxball, hmx, p, hp, hmax⟩ := hpts x hxS
  obtain ⟨p₀, B, hB, hexp⟩ := hx (hcbU (ball_subset_closedBall hxball))
  refine ⟨hcbU (ball_subset_closedBall hxball), hmx, p₀, B, hB, hexp, fun v hv => ?_⟩
  have hle := Prop25.inner_le_of_contact (u := u) (x₀ := x₀) (p := p) (η := η) hxball hexp
    (fun y hy => hmax y hy) v
  have hv2 : 0 < ‖v‖ ^ 2 := pow_pos (norm_pos_iff.2 hv) 2
  nlinarith [mul_pos hηpos hv2]

end Main

end LatticeProb.PegdenSmart
