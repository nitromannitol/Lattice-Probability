/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.MarkovGermVer3D at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.MarkovGermVer3C

/-!
# Germ step for unbounded `V`: the logarithmic Hardy inequality (task P2-MKD3)

`hardy_far`: for `g ∈ C¹_c(ℂ)`, `c ∈ ℝ` and `0 < s₁ < s₂ ≤ a < b`,
`(s₂² − s₁²)/2 ∫_{a<|x|<b} (g − c)²/|x|² ≤
  2 log(b/a) ((s₂² − s₁²)/2 log(b/s₁) ∫ ‖∇g‖² + ∫_{s₁<|x|<s₂} (g − c)²)`.
Proof: along each ray, `(g(ρe^{iθ}) − c)² ≤ 2 log(b/s₁) ∫_{s₁}^b t‖∇g‖² dt + 2 (g(se^{iθ}) − c)²`
(`ray_sq_le`); integrate in `θ`, then against `dρ/ρ` on `[a,b]` and `s ds` on `[s₁,s₂]`, in
polar coordinates (QZ `annulus_polar_integral`). Own elementary proof (the standard proof of
the 2D logarithmic Hardy inequality: FTC along rays + Cauchy–Schwarz).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric QuantumZipper.K3

namespace LQGMetric
namespace MarkovGermVer

set_option maxHeartbeats 1000000 in
theorem hardy_far {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (c : ℝ)
    {s1 s2 a b : ℝ} (h0 : 0 < s1) (h12 : s1 < s2) (h2a : s2 ≤ a) (hab : a < b) :
    (s2 ^ 2 - s1 ^ 2) / 2 *
        ∫ x in {x : ℂ | a < ‖x - 0‖ ∧ ‖x - 0‖ < b}, (g x - c) ^ 2 / ‖x - 0‖ ^ 2 ≤
      2 * Real.log (b / a) * ((s2 ^ 2 - s1 ^ 2) / 2 * Real.log (b / s1) *
        (∫ x, ‖fderiv ℝ g x‖ ^ 2) +
        ∫ x in {x : ℂ | s1 < ‖x - 0‖ ∧ ‖x - 0‖ < s2}, (g x - c) ^ 2) := by
  have ha : 0 < a := by linarith
  have hb : 0 < b := by linarith
  have hπ : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  obtain ⟨Cg, hCg⟩ := hgc.exists_bound_of_continuous hg.continuous
  obtain ⟨Cd, hCd⟩ := (hgc.fderiv ℝ).exists_bound_of_continuous
    (hg.continuous_fderiv one_ne_zero)
  have hcm : Continuous fun q : ℝ × ℝ => circleMap 0 q.1 q.2 := by
    simp only [circleMap]; fun_prop
  have hnorm : ∀ ρ θ : ℝ, 0 ≤ ρ → ‖circleMap 0 ρ θ - 0‖ = ρ := fun ρ θ hρ => by
    rw [sub_zero, norm_circleMap_zero, abs_of_nonneg hρ]
  set G : ℝ → ℝ → ℝ := fun ρ θ => (g (circleMap 0 ρ θ) - c) ^ 2 with hG
  have hGc : Continuous (Function.uncurry G) :=
    ((hg.continuous.comp hcm).sub continuous_const).pow 2
  set Φ : ℝ → ℝ := fun ρ => ∫ θ in (-Real.pi)..Real.pi, G ρ θ with hΦ
  have hΦc : Continuous Φ :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hGc _ _
  set Dn : ℝ → ℝ → ℝ := fun t θ => t * ‖fderiv ℝ g (circleMap 0 t θ)‖ ^ 2 with hDn
  have hDc : Continuous (Function.uncurry Dn) :=
    continuous_fst.mul (((hg.continuous_fderiv one_ne_zero).comp hcm).norm.pow 2)
  set E : ℝ → ℝ := fun θ => ∫ t in s1..b, Dn t θ with hE
  have hEc : Continuous E :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun θ t => Dn t θ) (hDc.comp (continuous_snd.prodMk continuous_fst)) _ _
  set Et := ∫ θ in (-Real.pi)..Real.pi, E θ with hEt
  ---------------------------------------------------------------- (3) `Et ≤ ∫ ‖∇g‖²`
  have hswap : Et = ∫ t in s1..b, ∫ θ in (-Real.pi)..Real.pi, Dn t θ := by
    have hs1b : s1 ≤ b := by linarith
    simp only [hEt, hE, intervalIntegral.integral_of_le hπ, intervalIntegral.integral_of_le hs1b]
    refine integral_integral_swap ?_
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact ((hDc.comp (continuous_snd.prodMk continuous_fst)).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set
        (prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
  have hEtle : Et ≤ ∫ x, ‖fderiv ℝ g x‖ ^ 2 := by
    have hF : Measurable fun x : ℂ => ‖fderiv ℝ g x‖ ^ 2 :=
      ((hg.continuous_fderiv one_ne_zero).norm.pow 2).measurable
    obtain ⟨hpol, -⟩ := annulus_polar_integral hF (0 : ℂ) h0 (by linarith : s1 < b)
      (sq_nonneg Cd) fun x _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hCd x) 2
    rw [hswap]
    have e : (∫ t in s1..b, ∫ θ in (-Real.pi)..Real.pi, Dn t θ) =
        ∫ t in s1..b, t * ∫ θ in (-Real.pi)..Real.pi, ‖fderiv ℝ g (circleMap 0 t θ)‖ ^ 2 := by
      simp only [hDn, intervalIntegral.integral_const_mul]
    rw [e, ← hpol]
    have hint : Integrable fun x : ℂ => ‖fderiv ℝ g x‖ ^ 2 :=
      ((hg.continuous_fderiv one_ne_zero).norm.pow 2).integrable_of_hasCompactSupport
        (hcs_of_vanish (hgc.fderiv ℝ) fun x hx => by simp [hx])
    exact setIntegral_le_integral hint (Eventually.of_forall fun x => sq_nonneg _)
  ---------------------------------------------------------------- (4) the pointwise bound
  have hpt : ∀ ρ ∈ Icc a b, ∀ s ∈ Icc s1 s2,
      Φ ρ ≤ 2 * Real.log (b / s1) * Et + 2 * Φ s := by
    intro ρ hρ s hs
    have hs0 : 0 < s := h0.trans_le hs.1
    have hsρ : s ≤ ρ := hs.2.trans (h2a.trans hρ.1)
    have hL : Real.log (ρ / s) ≤ Real.log (b / s1) :=
      Real.log_le_log (div_pos (hs0.trans_le hsρ) hs0)
        (div_le_div₀ hb.le hρ.2 h0 hs.1)
    have hθ : ∀ θ, G ρ θ ≤ 2 * Real.log (b / s1) * E θ + 2 * G s θ := by
      intro θ
      have h1 := ray_sq_le hg θ hs0 hsρ
      have h2 : (∫ t in s..ρ, Dn t θ) ≤ E θ :=
        intervalIntegral.integral_mono_interval hs.1 hsρ hρ.2
          ((ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun t ht =>
            mul_nonneg (h0.le.trans ht.1.le) (sq_nonneg _)))
          ((hDc.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _)
      have hLn : 0 ≤ Real.log (ρ / s) :=
        Real.log_nonneg (by rw [le_div_iff₀ hs0]; linarith)
      have hE0 : 0 ≤ ∫ t in s..ρ, Dn t θ :=
        intervalIntegral.integral_nonneg hsρ fun t ht =>
          mul_nonneg (hs0.le.trans ht.1) (sq_nonneg _)
      have h3 : Real.log (ρ / s) * (∫ t in s..ρ, Dn t θ) ≤ Real.log (b / s1) * E θ :=
        mul_le_mul hL h2 hE0 (hLn.trans hL)
      simp only [hG]
      nlinarith [sq_nonneg (g (circleMap 0 ρ θ) - g (circleMap 0 s θ) -
        (g (circleMap 0 s θ) - c))]
    have hGθ : ∀ r : ℝ, Continuous fun θ => G r θ := fun r =>
      hGc.comp (continuous_const.prodMk continuous_id)
    calc Φ ρ ≤ ∫ θ in (-Real.pi)..Real.pi, (2 * Real.log (b / s1) * E θ + 2 * G s θ) :=
          intervalIntegral.integral_mono_on hπ ((hGθ ρ).intervalIntegrable _ _)
            (((continuous_const.mul hEc).add (continuous_const.mul (hGθ s))).intervalIntegrable
              _ _)
            fun θ _ => hθ θ
      _ = 2 * Real.log (b / s1) * Et + 2 * Φ s := by
          rw [intervalIntegral.integral_add ((hEc.intervalIntegrable _ _).const_mul _)
            (((hGθ s).intervalIntegrable _ _).const_mul _), intervalIntegral.integral_const_mul,
            intervalIntegral.integral_const_mul]
  ---------------------------------------------------------------- (5), (6) integrate
  have hinvc : ContinuousOn (fun r : ℝ => r⁻¹ * Φ r) (uIcc a b) :=
    (continuousOn_inv₀.mono fun r hr => by
      rw [uIcc_of_le hab.le] at hr; exact (ha.trans_le hr.1).ne').mul hΦc.continuousOn
  set I := ∫ r in a..b, r⁻¹ * Φ r with hI
  have h5 : ∀ s ∈ Icc s1 s2, I ≤ Real.log (b / a) * (2 * Real.log (b / s1) * Et + 2 * Φ s) := by
    intro s hs
    have hinv : IntervalIntegrable (fun r : ℝ => r⁻¹) volume a b :=
      (continuousOn_inv₀.mono fun r hr => by
        rw [uIcc_of_le hab.le] at hr; exact (ha.trans_le hr.1).ne').intervalIntegrable
    calc I ≤ ∫ r in a..b, r⁻¹ * (2 * Real.log (b / s1) * Et + 2 * Φ s) :=
          intervalIntegral.integral_mono_on hab.le hinvc.intervalIntegrable
            (hinv.mul_const _) fun r hr =>
              mul_le_mul_of_nonneg_left (hpt r hr s hs) (inv_nonneg.2 (ha.le.trans hr.1))
      _ = _ := by
          rw [intervalIntegral.integral_mul_const, integral_inv_of_pos ha hb]
  have hs12 : s1 ≤ s2 := h12.le
  have hΦs : Continuous fun s : ℝ => s * Φ s := continuous_id.mul hΦc
  have h6 : (s2 ^ 2 - s1 ^ 2) / 2 * I ≤ Real.log (b / a) *
      (2 * Real.log (b / s1) * Et * ((s2 ^ 2 - s1 ^ 2) / 2) + 2 * ∫ s in s1..s2, s * Φ s) := by
    have hA : Continuous fun s : ℝ => s * I := continuous_id.mul continuous_const
    have hB : Continuous fun s : ℝ =>
        s * (Real.log (b / a) * (2 * Real.log (b / s1) * Et + 2 * Φ s)) :=
      continuous_id.mul (continuous_const.mul (continuous_const.add (continuous_const.mul hΦc)))
    have hm : ∫ s in s1..s2, s * I ≤
        ∫ s in s1..s2, s * (Real.log (b / a) * (2 * Real.log (b / s1) * Et + 2 * Φ s)) :=
      intervalIntegral.integral_mono_on hs12 (hA.intervalIntegrable _ _)
        (hB.intervalIntegrable _ _)
        fun s hs => mul_le_mul_of_nonneg_left (h5 s hs) (h0.le.trans hs.1)
    have e1 : ∫ s in s1..s2, s * I = (s2 ^ 2 - s1 ^ 2) / 2 * I := by
      rw [intervalIntegral.integral_mul_const, integral_id]
    have e2 : ∫ s in s1..s2, s * (Real.log (b / a) * (2 * Real.log (b / s1) * Et + 2 * Φ s)) =
        ∫ s in s1..s2, ((Real.log (b / a) * (2 * Real.log (b / s1) * Et)) * s +
          (2 * Real.log (b / a)) * (s * Φ s)) := by
      congr 1; funext s; ring
    have e3 : ∫ s in s1..s2, ((Real.log (b / a) * (2 * Real.log (b / s1) * Et)) * s +
          (2 * Real.log (b / a)) * (s * Φ s)) = (Real.log (b / a) * (2 * Real.log (b / s1) * Et))
            * ((s2 ^ 2 - s1 ^ 2) / 2) + (2 * Real.log (b / a)) * ∫ s in s1..s2, s * Φ s := by
      have i1 : IntervalIntegrable (fun s : ℝ => (Real.log (b / a) *
          (2 * Real.log (b / s1) * Et)) * s) volume s1 s2 :=
        (continuous_const.mul continuous_id).intervalIntegrable _ _
      have i2 : IntervalIntegrable (fun s : ℝ => (2 * Real.log (b / a)) * (s * Φ s)) volume
          s1 s2 := (continuous_const.mul hΦs).intervalIntegrable _ _
      rw [intervalIntegral.integral_add i1 i2,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      congr 2
      exact integral_id
    rw [e1, e2, e3] at hm
    linarith
  ---------------------------------------------------------------- (7) polar identities
  have hgb : ∀ x, |g x - c| ≤ Cg + |c| := fun x => by
    have := hCg x; rw [Real.norm_eq_abs] at this
    exact (abs_sub _ _).trans (by linarith)
  have hpolA : ∫ x in {x : ℂ | a < ‖x - 0‖ ∧ ‖x - 0‖ < b}, (g x - c) ^ 2 / ‖x - 0‖ ^ 2 = I := by
    have hF : Measurable fun x : ℂ => (g x - c) ^ 2 / ‖x - 0‖ ^ 2 := by
      have : Continuous fun x : ℂ => (g x - c) ^ 2 := (hg.continuous.sub continuous_const).pow 2
      exact this.measurable.div (by fun_prop)
    obtain ⟨hpol, -⟩ := annulus_polar_integral hF (0 : ℂ) ha hab
      (by positivity : (0 : ℝ) ≤ (Cg + |c|) ^ 2 / a ^ 2) fun x hx => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have hx2 : a ^ 2 ≤ ‖x - 0‖ ^ 2 := pow_le_pow_left₀ ha.le hx.le 2
        have hg2 : (g x - c) ^ 2 ≤ (Cg + |c|) ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hgb x) 2
        exact div_le_div₀ (by positivity) hg2 (by positivity) hx2
    rw [hpol, hI]
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [uIcc_of_le hab.le] at hr
    have hr0 : 0 < r := ha.trans_le hr.1
    simp only [hnorm r _ hr0.le, hΦ, hG]
    rw [intervalIntegral.integral_div]
    field_simp
  have hpolS : ∫ x in {x : ℂ | s1 < ‖x - 0‖ ∧ ‖x - 0‖ < s2}, (g x - c) ^ 2 =
      ∫ s in s1..s2, s * Φ s := by
    have hF : Measurable fun x : ℂ => (g x - c) ^ 2 :=
      ((hg.continuous.sub continuous_const).pow 2).measurable
    obtain ⟨hpol, -⟩ := annulus_polar_integral hF (0 : ℂ) h0 h12
      (sq_nonneg (Cg + |c|)) fun x _ => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hgb x) 2
    rw [hpol]
  rw [hpolA, hpolS]
  have hlba : 0 ≤ Real.log (b / a) := Real.log_nonneg (by rw [le_div_iff₀ ha]; linarith)
  have hlbs : 0 ≤ Real.log (b / s1) := Real.log_nonneg (by rw [le_div_iff₀ h0]; linarith)
  have hsq : 0 ≤ (s2 ^ 2 - s1 ^ 2) / 2 := by nlinarith
  have h7 : Real.log (b / s1) * Et * ((s2 ^ 2 - s1 ^ 2) / 2) ≤
      Real.log (b / s1) * (∫ x, ‖fderiv ℝ g x‖ ^ 2) * ((s2 ^ 2 - s1 ^ 2) / 2) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEtle hlbs) hsq
  have h8 := mul_le_mul_of_nonneg_left h7 (by positivity : (0 : ℝ) ≤ 2 * Real.log (b / a))
  nlinarith

end MarkovGermVer
end LQGMetric
