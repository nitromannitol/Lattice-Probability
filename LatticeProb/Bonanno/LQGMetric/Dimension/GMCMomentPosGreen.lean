/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Dimension.GMCMomentPosGreen at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Dimension.GMCSqCov
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm18.A1RPick
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.BasicsUnivalent

/-!
# Upper bound for the circle-average covariances of the square GFF (P2-KAHANE2)

For the zero-boundary GFF on `𝕍 = (0,1)²` and circles `∂B(z, r)`, `∂B(w, s)` whose closed discs
lie in `𝕍`:

* `circleCov_le_log` : `Cov(h_r(z), h_s(w)) ≤ log 3 − log max(r, ‖z − w‖)`.

This is the upper half of the covariance comparison `Cov h_ε(x, y) ≤ log(1/max(ε,|x−y|)) + C`
used with Kahane's inequality in the moment bounds of GMC (Berestycki–Powell arXiv:2404.16642,
`GMCproperties.tex` l. 1207 "encadr-cov", and Lemma 3.8 / eq. (roughcov) l. 287–330, where
`K(x,y) = −log|x−y| + g(x,y)` with `g` bounded above).

The bound on the regular part, `hS x y ≤ log 3` (`hS_le_log_three`), is the comparison of Green
functions `G_𝕍(x, y) ≤ G_ℍ(x, y)` for `𝕍 ⊆ ℍ`. We prove it by the Schwarz–Pick lemma in `ℍ`
(Ahlfors, *Complex Analysis*, 3rd ed., §4.3.4, pp. 135–136): the inverse `Φ : ℍ → 𝕍 ⊆ ℍ` of the
conformal map `sqM` contracts the pseudo-hyperbolic distance `|u − a|/|u − ā|`
(`pseudoHyp_le`), and `G_ℍ(u, a) = −log(|u − a|/|u − ā|)`. The Schwarz step follows QZ
`R18.A1R.im_ge_of_mapsTo_H` (A1RPick.lean), which proves it at the base point `i`; a general base
point `a` is reached by the affine automorphism `v ↦ Re a + Im a · v` of `ℍ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric QuantumZipper
open scoped ENNReal ComplexConjugate

namespace LQGMetric

namespace GMCPos

open Complex in
/-- Schwarz's lemma at the base point `i` (QZ `A1R.im_ge_of_mapsTo_H`, first half) -/
lemma schwarz_H_at_I {Ψ : ℂ → ℂ} (hd : DifferentiableOn ℂ Ψ H) (hm : MapsTo Ψ H H) {v : ℂ}
    (hv : v ∈ H) : ‖(Ψ v - Ψ I) / (Ψ v - conj (Ψ I))‖ ≤ ‖(v - I) / (v + I)‖ := by
  have hIH : I ∈ H := by show 0 < I.im; simp
  set p := Ψ I with hp
  have hpH : 0 < p.im := hm hIH
  have hpc : ∀ w ∈ H, w - conj p ≠ 0 := by
    intro w hw h
    have := congrArg Complex.im h
    simp only [sub_im, conj_im, zero_im] at this
    have hw' : 0 < w.im := hw
    linarith
  set G : ℂ → ℂ := fun ζ => (Ψ (R18.A1R.cay ζ) - p) / (Ψ (R18.A1R.cay ζ) - conj p) with hG
  have hGd : DifferentiableOn ℂ G (ball 0 1) := by
    have hc : DifferentiableOn ℂ (fun ζ => Ψ (R18.A1R.cay ζ)) (ball 0 1) :=
      hd.comp R18.A1R.differentiableOn_cay fun ζ hζ => R18.A1R.cay_mem_H hζ
    exact (hc.sub_const _).div (hc.sub_const _) fun ζ hζ => hpc _ (hm (R18.A1R.cay_mem_H hζ))
  have hG0 : G 0 = 0 := by
    show (Ψ (R18.A1R.cay 0) - p) / (Ψ (R18.A1R.cay 0) - conj p) = 0
    rw [show R18.A1R.cay 0 = I by simp [R18.A1R.cay], ← hp, sub_self, zero_div]
  have hGm : MapsTo G (ball 0 1) (closedBall 0 1) := by
    intro ζ hζ
    have hw : 0 < (Ψ (R18.A1R.cay ζ)).im := hm (R18.A1R.cay_mem_H hζ)
    rw [mem_closedBall, dist_zero_right, hG]
    simp only
    rw [norm_div, div_le_one (norm_pos_iff.2 (hpc _ (hm (R18.A1R.cay_mem_H hζ))))]
    exact (R18.A1R.norm_sub_lt_norm_sub_conj hw hpH).le
  have hvI : v + I ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp only [add_im, I_im, zero_im] at this
    have hv' : 0 < v.im := hv
    linarith
  set ζ := (v - I) / (v + I) with hζ
  have hζb : ‖ζ‖ < 1 := by
    have := R18.A1R.norm_sub_lt_norm_sub_conj (w := v) (p := I) hv (by simp)
    rw [hζ, norm_div, div_lt_one (norm_pos_iff.2 hvI)]
    simpa using this
  have hcay : R18.A1R.cay ζ = v := by
    unfold R18.A1R.cay
    rw [hζ]
    have h2 : (1 : ℂ) - (v - I) / (v + I) = 2 * I / (v + I) := by field_simp; ring
    have h3 : (1 : ℂ) + (v - I) / (v + I) = 2 * v / (v + I) := by field_simp; ring
    rw [h2, h3]
    field_simp
  have hS := Complex.norm_le_norm_of_mapsTo_ball hGd hGm hG0 hζb
  have e : G ζ = (Ψ v - p) / (Ψ v - conj p) := by simp only [hG, hcay]
  rwa [e] at hS

open Complex in
/-- **Schwarz–Pick in `ℍ`**: a holomorphic self-map of `ℍ` contracts the pseudo-hyperbolic
distance, `|Φu − Φa| |u − ā| ≤ |u − a| |Φu − \overline{Φa}|`. -/
theorem pseudoHyp_le {Φ : ℂ → ℂ} (hd : DifferentiableOn ℂ Φ H) (hm : MapsTo Φ H H) {a u : ℂ}
    (ha : a ∈ H) (hu : u ∈ H) :
    ‖Φ u - Φ a‖ * ‖u - conj a‖ ≤ ‖u - a‖ * ‖Φ u - conj (Φ a)‖ := by
  have ha' : 0 < a.im := ha
  have hu' : 0 < u.im := hu
  set A : ℂ → ℂ := fun v => (a.re : ℂ) + (a.im : ℂ) * v with hA
  have hAH : MapsTo A H H := fun v (hv : 0 < v.im) => by
    show 0 < (A v).im
    simp only [hA, add_im, ofReal_im, mul_im, ofReal_re, zero_add, zero_mul, add_zero]
    exact mul_pos ha' hv
  have hAd : DifferentiableOn ℂ A H :=
    ((differentiable_const _).add ((differentiable_const _).mul differentiable_id)).differentiableOn
  set v : ℂ := (u - a.re) / a.im with hv
  have hai : (a.im : ℂ) ≠ 0 := ofReal_ne_zero.2 ha'.ne'
  have hAv : A v = u := by simp only [hA, hv]; field_simp; ring
  have hAI : A I = a := by
    simp only [hA]; apply Complex.ext <;> simp
  have hvH : v ∈ H := by
    show 0 < v.im
    rw [hv, div_ofReal_im]
    simp only [sub_im, ofReal_im, sub_zero]
    exact div_pos hu' ha'
  have h := schwarz_H_at_I (Ψ := Φ ∘ A) (hd.comp hAd hAH) (hm.comp hAH) hvH
  simp only [Function.comp_apply, hAv, hAI] at h
  have e1 : u - a = (a.im : ℂ) * (v - I) := by
    rw [← hAv]; apply Complex.ext <;> simp [hA] <;> ring
  have e2 : u - conj a = (a.im : ℂ) * (v + I) := by
    rw [← hAv]; apply Complex.ext <;> simp [hA] <;> ring
  have hvI : v + I ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp only [add_im, I_im, zero_im] at this
    have : 0 < v.im := hvH
    linarith
  have hc : Φ u - conj (Φ a) ≠ 0 := by
    intro h0
    have := congrArg Complex.im h0
    simp only [sub_im, conj_im, zero_im] at this
    have h1 : 0 < (Φ u).im := hm hu
    have h2 : 0 < (Φ a).im := hm ha
    linarith
  have hr : ‖(v - I) / (v + I)‖ = ‖u - a‖ / ‖u - conj a‖ := by
    rw [e1, e2, norm_mul, norm_mul, mul_div_mul_left _ _ (norm_ne_zero_iff.2 hai), norm_div]
  rw [hr, norm_div, div_le_div_iff₀ (norm_pos_iff.2 hc)
    (by rw [e2, norm_mul]; exact mul_pos (norm_pos_iff.2 hai) (norm_pos_iff.2 hvI))] at h
  linarith

/-- the inverse of the conformal map `sqM : 𝕍 → ℍ` -/
def sqInv : ℂ → ℂ :=
  (CA.univalentOPH isOpen_openSquare differentiableOn_sqM sqM_injOn).symm

lemma sqM_image : sqM '' openSquare = H := by
  rw [← isConformalOnto_sqMap.image_eq]
  exact image_congr fun x hx => sqM_eq hx

lemma sqInv_sqM {x : ℂ} (hx : x ∈ openSquare) : sqInv (sqM x) = x :=
  CA.univalentOPH_symm_apply_apply isOpen_openSquare differentiableOn_sqM sqM_injOn hx

lemma differentiableOn_sqInv : DifferentiableOn ℂ sqInv H := by
  have := CA.differentiableOn_univalentOPH_symm isOpen_openSquare differentiableOn_sqM sqM_injOn
  rwa [sqM_image] at this

lemma mapsTo_sqInv : MapsTo sqInv H H := by
  intro u hu
  rw [← sqM_image] at hu
  obtain ⟨x, hx, rfl⟩ := hu
  rw [sqInv_sqM hx]
  exact openSquare_subset_H hx

/-- **Green function comparison** `G_𝕍(x, y) ≤ G_ℍ(x, y)` -/
theorem greenH_sqM_le {x y : ℂ} (hx : x ∈ openSquare) (hy : y ∈ openSquare) (hxy : x ≠ y) :
    greenH (sqM x) (sqM y) ≤ greenH x y := by
  have h := pseudoHyp_le differentiableOn_sqInv mapsTo_sqInv (sqM_mem_H hy) (sqM_mem_H hx)
  rw [sqInv_sqM hx, sqInv_sqM hy] at h
  have hxH : 0 < x.im := openSquare_subset_H hx
  have hyH : 0 < y.im := openSquare_subset_H hy
  have p1 : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  have p2 : 0 < ‖sqM x - sqM y‖ :=
    norm_pos_iff.2 (sub_ne_zero.2 fun e => hxy (sqM_injOn hx hy e))
  have p3 : 0 < ‖sqM x - conj (sqM y)‖ := by
    rw [norm_sub_conj_comm]; exact norm_pos_iff.2 (sub_conj_ne_zero hx hy)
  have p4 : 0 < ‖x - conj y‖ := norm_pos_iff.2 fun h0 => by
    have := congrArg Complex.im h0
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
    linarith
  unfold greenH
  have := Real.log_le_log (by positivity) h
  rw [Real.log_mul p1.ne' p3.ne', Real.log_mul p2.ne' p4.ne'] at this
  linarith

/-- **the regular part of the square Green function is at most `log 3`** -/
theorem hS_le_log_three {x y : ℂ} (hx : x ∈ openSquare) (hy : y ∈ openSquare) :
    hS x y ≤ Real.log 3 := by
  have key : ∀ y ∈ openSquare, x ≠ y → hS x y ≤ Real.log 3 := by
    intro y hy hxy
    have h1 := greenH_sqM hx hy hxy
    have h2 := greenH_sqM_le hx hy hxy
    have hb : ‖x - conj y‖ ≤ 3 := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      simp only [Complex.sub_re, Complex.conj_re, Complex.sub_im, Complex.conj_im,
        sub_neg_eq_add]
      obtain ⟨a1, a2, a3, a4⟩ := hx; obtain ⟨b1, b2, b3, b4⟩ := hy
      have e1 : |x.re - y.re| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
      have e2 : |x.im + y.im| ≤ 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      linarith
    have p4 : 0 < ‖x - conj y‖ := norm_pos_iff.2 fun h0 => by
      have := congrArg Complex.im h0
      simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at this
      have := openSquare_subset_H hx; have := openSquare_subset_H hy
      simp only [H, mem_ofPred_eq] at *
      linarith
    unfold greenH at h1 h2
    have := Real.log_le_log p4 hb
    linarith
  by_cases hxy : x = y
  · subst hxy
    have hc : ContinuousAt (hS x) x :=
      (continuousOn_hS_right hx).continuousAt (isOpen_openSquare.mem_nhds hx)
    have hev : ∀ᶠ y in 𝓝[≠] x, hS x y ≤ Real.log 3 := by
      filter_upwards [nhdsWithin_le_nhds (isOpen_openSquare.mem_nhds hx),
        self_mem_nhdsWithin] with y hy hyx
      exact key y hy (Ne.symm hyx)
    exact le_of_tendsto (hc.tendsto.mono_left nhdsWithin_le_nhds) hev
  · exact key y hy hxy

end GMCPos

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → Measure ℂ → ℝ}

/-- **upper bound for circle-average covariances**:
`Cov(h_r(z), h_s(w)) ≤ log 3 − log max(r, ‖z − w‖)` -/
theorem circleCov_le_log (hX : IsZeroBoundaryGFFOn openSquare X P) {z w : ℂ} {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) (hB₁ : closedBall z r ⊆ openSquare)
    (hB₂ : closedBall w s ⊆ openSquare) :
    cov[fun ω => X ω (foldedCircle z r), fun ω => X ω (foldedCircle w s); P] ≤
      Real.log 3 - Real.log (max r ‖z - w‖) := by
  rw [circleCov_eq_kernel hX hr hs hB₁ hB₂]
  have hw : w ∈ openSquare := hB₂ (mem_closedBall_self hs.le)
  have hcongr : (fun x => ∫ y, greenH (sqM x) (sqM y) ∂circleUnif w s) =ᵐ[circleUnif z r]
      fun x => -Real.log (max s ‖w - x‖) + hS x w := by
    filter_upwards [CoordReg.ae_mem_closedBall_circleUnif z hr.le] with x hx
    rw [integral_greenH_sqM_circle (hB₁ hx) hs hB₂]
  have hat : ∀ᵐ x ∂circleUnif z r, x ≠ w := by
    rw [ae_iff]
    have := noAtoms_of_isAdmissibleH (isAdmissibleH_circleUnif hr hB₁) w
    simpa using this
  have hi1 : Integrable (fun x => -Real.log (max s ‖w - x‖) + hS x w) (circleUnif z r) := by
    refine Integrable.add ?_ ?_
    · refine CoordReg.integrable_circleUnif_of_continuousOn ?_ hr.le ?_
      · exact (Real.measurable_log.comp (measurable_const.max
          (measurable_const.sub measurable_id).norm)).neg
      · refine (Continuous.continuousOn ?_)
        exact ((continuous_const.max (continuous_const.sub continuous_id).norm).log
          fun x => (lt_max_of_lt_left hs).ne').neg
    · simp_rw [hS_symm _ w]; exact integrable_hS_right hw hr.le hB₁
  have hi2 : Integrable (fun x => Real.log 3 - Real.log ‖x - w‖) (circleUnif z r) :=
    (integrable_const _).sub (CircleMV.integrable_log_norm_sub_circleUnif z w r)
  rw [integral_congr_ae hcongr]
  calc ∫ x, -Real.log (max s ‖w - x‖) + hS x w ∂circleUnif z r
      ≤ ∫ x, Real.log 3 - Real.log ‖x - w‖ ∂circleUnif z r := by
        refine integral_mono_ae hi1 hi2 ?_
        filter_upwards [hat, CoordReg.ae_mem_closedBall_circleUnif z hr.le] with x hxw hx
        have h1 := GMCPos.hS_le_log_three (hB₁ hx) hw
        have hp : 0 < ‖w - x‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hxw))
        have h2 := Real.log_le_log hp (le_max_right s ‖w - x‖)
        rw [norm_sub_rev x w]
        linarith
    _ = Real.log 3 - Real.log (max r ‖z - w‖) := by
        rw [integral_sub (integrable_const _) (CircleMV.integrable_log_norm_sub_circleUnif z w r),
          integral_const, integral_log_norm_sub_circleUnif z w hr]
        simp

end LQGMetric
