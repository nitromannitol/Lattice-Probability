/-
The lower tail of the centred real Gaussian, and the inversion of the tail that
Step 1 of `lem:dgt4-path-survival` performs at `sandpile.tex:5509-5512`:

  "By \eqref{eq:dgt4-uniform-contact-thresholds} and `ε n_R ≤ n_R - r_x ≤ n_R`, we
   have `P(J(0)>b_x) ≍ R^{-2}` uniformly over `x ∈ Λ`, so inverting the Gaussian
   tail `log P(J(0)>b) = -b^2/(2 Var(J(0))) - log b + O(1)` gives
   `b_x^2/Var(J(0)) = 4 log R - log log R + O_{ε,T}(1)`."

The Chernoff bound of `Support/LinGaussIso.lean` gives the upper half of that
inversion.  The lower half needs a LOWER bound on the tail, which is the Mills
ratio estimate, and that is what is proved here.  The proof is elementary and
avoids the usual antiderivative argument: on the interval `[a, a+v/a]`, of length
`v/a`, the density is at least its value at the right endpoint, and the exponent
there exceeds the exponent at `a` by at most `3/2`, because
`(a + v/a)^2/(2v) = a^2/(2v) + 1 + v/(2a^2)` and `v ≤ a^2`.  The resulting bound
`P(N(0,v) > a) ≥ (√v/a) e^{-a^2/(2v) - 3/2}/√(2π)` for `a ≥ √v` loses only the
universal factor `e^{-3/2}` against the sharp Mills ratio, which is all the
inversion needs: the correction it produces is `log(a/√v) + O(1)`, exactly the
`log b` term of the paper.
-/
import LatticeProb.Gauss.IsonormalSum

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace LatticeProb.GaussTail

/-- The centred Gaussian density is antitone on the nonnegative half line. -/
theorem gaussianPDFReal_le_of_le {v : ℝ≥0} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    gaussianPDFReal 0 v b ≤ gaussianPDFReal 0 v a := by
  rcases eq_or_lt_of_le v.coe_nonneg with hv | hv
  · simp [ProbabilityTheory.gaussianPDFReal, ← hv]
  · simp only [ProbabilityTheory.gaussianPDFReal, sub_zero]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine Real.exp_le_exp.mpr ?_
    have h2v : (0:ℝ) < 2 * (v:ℝ) := by positivity
    apply div_le_div_of_nonneg_right ?_ h2v.le
    nlinarith [sq_nonneg a, sq_nonneg b]

/-- On an interval of the nonnegative half line the integral of the density is at least
the length of the interval times the value of the density at its right endpoint. -/
theorem le_setIntegral_gaussianPDFReal_Ioc {v : ℝ≥0} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (b - a) * gaussianPDFReal 0 v b ≤ ∫ x in Set.Ioc a b, gaussianPDFReal 0 v x := by
  have hg : MeasureTheory.IntegrableOn (gaussianPDFReal 0 v) (Set.Ioc a b) MeasureTheory.volume :=
    (ProbabilityTheory.integrable_gaussianPDFReal 0 v).integrableOn
  have hfin : MeasureTheory.volume (Set.Ioc a b) ≠ ⊤ := by
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  have hf : MeasureTheory.IntegrableOn (fun _ : ℝ => gaussianPDFReal 0 v b) (Set.Ioc a b)
      MeasureTheory.volume := MeasureTheory.integrableOn_const hfin (by finiteness)
  have hmono := MeasureTheory.setIntegral_mono_on hf hg measurableSet_Ioc
    (fun x hx => gaussianPDFReal_le_of_le (le_trans ha hx.1.le) hx.2)
  rw [MeasureTheory.setIntegral_const, MeasureTheory.measureReal_def, Real.volume_Ioc,
    ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ b - a), smul_eq_mul] at hmono
  exact hmono

/-- A lower bound for the integral of the density over an interval is a lower bound for
the Gaussian measure of the half line containing it. -/
theorem gaussianReal_real_Ioi_ge_of_Ioc {v : ℝ≥0} (hv : v ≠ 0) {a b c : ℝ}
    (hB : c ≤ ∫ x in Set.Ioc a b, gaussianPDFReal 0 v x) :
    c ≤ ((gaussianReal 0 v).real (Set.Ioi a)) := by
  have hmeas : ((gaussianReal 0 v).real (Set.Ioi a))
      = ∫ x in Set.Ioi a, gaussianPDFReal 0 v x := by
    rw [MeasureTheory.measureReal_def,
      ProbabilityTheory.gaussianReal_apply_eq_integral 0 hv (Set.Ioi a),
      ENNReal.toReal_ofReal
        (MeasureTheory.integral_nonneg
          (fun x => ProbabilityTheory.gaussianPDFReal_nonneg 0 v x))]
  rw [hmeas]
  refine hB.trans ?_
  refine MeasureTheory.setIntegral_mono_set
    ((ProbabilityTheory.integrable_gaussianPDFReal 0 v).integrableOn)
    (Filter.Eventually.of_forall (fun x => ProbabilityTheory.gaussianPDFReal_nonneg 0 v x))
    (Filter.Eventually.of_forall (fun x hx => Set.Ioc_subset_Ioi_self hx))

/-- **The Mills ratio lower bound.**  For `a ≥ √v`,
`P(N(0,v) > a) ≥ (√v/a) e^{-a²/(2v) - 3/2}/√(2π)`.  This is the companion of the Chernoff
upper bound `gaussianReal_measure_ge_le`, and it is what inverts the Gaussian tail in
Step 1 of `lem:dgt4-path-survival`. -/
theorem gaussianReal_real_Ioi_ge {v : ℝ≥0} (hv : 0 < (v : ℝ)) {a : ℝ}
    (ha : Real.sqrt (v : ℝ) ≤ a) :
    Real.sqrt (v : ℝ) / a * Real.exp (-(a ^ 2 / (2 * (v : ℝ))) - 3 / 2) / Real.sqrt (2 * Real.pi)
      ≤ ((gaussianReal 0 v).real (Set.Ioi a)) := by
  have hvne : v ≠ 0 := by
    intro h; rw [h] at hv; simp at hv
  have hs : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.mpr hv
  have ha0 : 0 < a := lt_of_lt_of_le hs ha
  have hva : (v : ℝ) ≤ a ^ 2 := by
    nlinarith [Real.sq_sqrt hv.le, Real.sqrt_nonneg (v : ℝ)]
  have hb : a ≤ a + (v : ℝ) / a := by
    have : 0 ≤ (v : ℝ) / a := by positivity
    linarith
  refine gaussianReal_real_Ioi_ge_of_Ioc hvne (b := a + (v : ℝ) / a) ?_
  refine le_trans ?_ (le_setIntegral_gaussianPDFReal_Ioc ha0.le hb)
  have hsplit : Real.sqrt (2 * Real.pi * (v : ℝ))
      = Real.sqrt (2 * Real.pi) * Real.sqrt (v : ℝ) :=
    Real.sqrt_mul (by positivity) (v : ℝ)
  have hpi : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  simp only [ProbabilityTheory.gaussianPDFReal, sub_zero, hsplit]
  have hcoef : (a + (v : ℝ) / a - a) * (Real.sqrt (2 * Real.pi) * Real.sqrt (v : ℝ))⁻¹
      = Real.sqrt (v : ℝ) / a / Real.sqrt (2 * Real.pi) := by
    have hvs : Real.sqrt (v : ℝ) * Real.sqrt (v : ℝ) = (v : ℝ) := Real.mul_self_sqrt hv.le
    field_simp
    nlinarith [hvs, hs, hpi, ha0]
  have hexp : -(a ^ 2 / (2 * (v : ℝ))) - 3 / 2
      ≤ -(a + (v : ℝ) / a) ^ 2 / (2 * (v : ℝ)) := by
    rw [neg_div, neg_sub_left, neg_le_neg_iff]
    have hexp2 : (a + (v : ℝ) / a) ^ 2 = a ^ 2 + 2 * (v : ℝ) + (v : ℝ) ^ 2 / a ^ 2 := by
      field_simp; ring
    have hfrac : (v : ℝ) ^ 2 / a ^ 2 ≤ (v : ℝ) := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hva, hv]
    have hkey : (a + (v : ℝ) / a) ^ 2 ≤ 3 * (v : ℝ) + a ^ 2 := by linarith
    calc (a + (v : ℝ) / a) ^ 2 / (2 * (v : ℝ))
        ≤ (3 * (v : ℝ) + a ^ 2) / (2 * (v : ℝ)) := by gcongr
      _ = 3 / 2 + a ^ 2 / (2 * (v : ℝ)) := by field_simp
  calc Real.sqrt (v : ℝ) / a * Real.exp (-(a ^ 2 / (2 * (v : ℝ))) - 3 / 2)
        / Real.sqrt (2 * Real.pi)
      = (Real.sqrt (v : ℝ) / a / Real.sqrt (2 * Real.pi))
          * Real.exp (-(a ^ 2 / (2 * (v : ℝ))) - 3 / 2) := by ring
    _ ≤ (Real.sqrt (v : ℝ) / a / Real.sqrt (2 * Real.pi))
          * Real.exp (-(a + (v : ℝ) / a) ^ 2 / (2 * (v : ℝ))) := by
        have hc : 0 ≤ Real.sqrt (v : ℝ) / a / Real.sqrt (2 * Real.pi) := by positivity
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hc
    _ = (a + (v : ℝ) / a - a) * ((Real.sqrt (2 * Real.pi) * Real.sqrt (v : ℝ))⁻¹
          * Real.exp (-(a + (v : ℝ) / a) ^ 2 / (2 * (v : ℝ)))) := by
        rw [← mul_assoc, hcoef]

/-- **Inverting the Gaussian tail.**  A tail at most `p` at the level `a ≥ √v` forces
`a²/(2v) ≥ log(1/p) - log(a/√v) - 3`.  The `log(a/√v)` term is the paper's `-log b`. -/
theorem log_tail_inversion {v : ℝ} (hv : 0 < v) {a p : ℝ}
    (ha : Real.sqrt v ≤ a)
    (hmills : Real.sqrt v / a * Real.exp (-(a ^ 2 / (2 * v)) - 3 / 2) / Real.sqrt (2 * Real.pi)
      ≤ p) :
    -Real.log p ≤ a ^ 2 / (2 * v) + Real.log (a / Real.sqrt v) + 3 := by
  have hs : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have ha0 : 0 < a := lt_of_lt_of_le hs ha
  have hpi : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hLpos : 0 < Real.sqrt v / a * Real.exp (-(a ^ 2 / (2 * v)) - 3 / 2)
      / Real.sqrt (2 * Real.pi) := by positivity
  have hlog := Real.log_le_log hLpos hmills
  rw [Real.log_div (by positivity) (ne_of_gt hpi),
    Real.log_mul (by positivity) (ne_of_gt (Real.exp_pos _)),
    Real.log_div (ne_of_gt hs) (ne_of_gt ha0), Real.log_exp] at hlog
  have hbound : Real.log (Real.sqrt (2 * Real.pi)) ≤ 1.04 := by
    rw [Real.log_sqrt (by positivity)]
    have h8 : 2 * Real.pi ≤ 8 := by nlinarith [Real.pi_le_four]
    have hl8 : Real.log (2 * Real.pi) ≤ Real.log 8 := Real.log_le_log (by positivity) h8
    have h8e : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]; push_cast; ring
    nlinarith [Real.log_two_lt_d9]
  rw [Real.log_div (ne_of_gt ha0) (ne_of_gt hs)]
  linarith

/-- The form in which Step 1 of `lem:dgt4-path-survival` uses the inversion: the level of a
Gaussian threshold whose upper tail is at most `p` satisfies
`a²/(2v) ≥ log(1/p) - log(a/√v) - 3`. -/
theorem log_le_of_gaussianReal_tail_le {v : ℝ≥0} (hv : 0 < (v : ℝ)) {a p : ℝ}
    (ha : Real.sqrt (v : ℝ) ≤ a) (hp : ((gaussianReal 0 v).real (Set.Ioi a)) ≤ p) :
    -Real.log p ≤ a ^ 2 / (2 * (v : ℝ)) + Real.log (a / Real.sqrt (v : ℝ)) + 3 :=
  log_tail_inversion hv ha ((gaussianReal_real_Ioi_ge hv ha).trans hp)

/-- **The first moment of the centred Gaussian density over a half line**:
`∫_{x > t} x φ_v(x) dx = v φ_v(t)`, by the fundamental theorem of calculus applied to
`F(x) = -v φ_v(x)`, whose derivative is `x φ_v(x)` and which tends to zero at infinity.
This is the identity behind the SHARP Mills ratio, which
`prop:dgt4-contact-asymptotics` needs in case (a) and the crude bound above does not
supply. -/
theorem integral_Ioi_id_mul_gaussianPDFReal {v : ℝ≥0} (hv : 0 < (v : ℝ)) (t : ℝ) :
    ∫ x in Set.Ioi t, x * gaussianPDFReal 0 v x = (v : ℝ) * gaussianPDFReal 0 v t := by
  set C : ℝ := (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ with hC
  have hpdf : ∀ x : ℝ, gaussianPDFReal 0 v x = C * Real.exp (-x ^ 2 / (2 * (v : ℝ))) := by
    intro x
    simp only [ProbabilityTheory.gaussianPDFReal, sub_zero, hC]
  have hbase : Integrable (fun x : ℝ => x * gaussianPDFReal 0 v x) volume := by
    have h : (fun x : ℝ => x * gaussianPDFReal 0 v x)
        = fun x : ℝ => C * (x * Real.exp (-(1 / (2 * (v : ℝ))) * x ^ 2)) := by
      funext x
      rw [hpdf x]; ring_nf
    rw [h]
    exact (integrable_mul_exp_neg_mul_sq (by positivity)).const_mul _
  have hderiv : ∀ x ∈ Set.Ioi t,
      HasDerivAt (fun y : ℝ => -(v : ℝ) * gaussianPDFReal 0 v y)
        (x * gaussianPDFReal 0 v x) x := by
    intro x _
    have hg : HasDerivAt (fun y : ℝ => -y ^ 2 / (2 * (v : ℝ)))
        (-(2 * x) / (2 * (v : ℝ))) x := by
      simpa using ((hasDerivAt_pow 2 x).neg.div_const (2 * (v : ℝ)))
    have he := hg.exp
    have hF := (he.const_mul C).const_mul (-(v : ℝ))
    have hfun : (fun y : ℝ => -(v : ℝ) * (C * Real.exp (-y ^ 2 / (2 * (v : ℝ)))))
        = fun y : ℝ => -(v : ℝ) * gaussianPDFReal 0 v y := by
      funext y; rw [hpdf y]
    rw [hfun] at hF
    have hval : -(v : ℝ) * (C * (Real.exp (-x ^ 2 / (2 * (v : ℝ))) * (-(2 * x) / (2 * (v : ℝ)))))
        = x * gaussianPDFReal 0 v x := by
      rw [hpdf x]
      field_simp
    rw [hval] at hF
    exact hF
  have hcont : ContinuousWithinAt (fun y : ℝ => -(v : ℝ) * gaussianPDFReal 0 v y)
      (Set.Ici t) t := by
    have hc : Continuous fun y : ℝ => -(v : ℝ) * gaussianPDFReal 0 v y := by
      have : (fun y : ℝ => -(v : ℝ) * gaussianPDFReal 0 v y)
          = fun y : ℝ => -(v : ℝ) * (C * Real.exp (-y ^ 2 / (2 * (v : ℝ)))) := by
        funext y; rw [hpdf y]
      rw [this]; fun_prop
    exact hc.continuousWithinAt
  have htend : Tendsto (fun y : ℝ => -(v : ℝ) * gaussianPDFReal 0 v y) atTop (𝓝 0) := by
    have h1 : Tendsto (fun y : ℝ => -y ^ 2 / (2 * (v : ℝ))) atTop atBot := by
      refine Filter.Tendsto.atBot_div_const (by positivity) ?_
      exact tendsto_neg_atBot_iff.mpr (tendsto_pow_atTop (by norm_num))
    have h2 := Real.tendsto_exp_atBot.comp h1
    have h3 := h2.const_mul (-(v : ℝ) * C)
    have hfun : (fun y : ℝ => -(v : ℝ) * C * Real.exp (-y ^ 2 / (2 * (v : ℝ))))
        = fun y : ℝ => -(v : ℝ) * gaussianPDFReal 0 v y := by
      funext y; rw [hpdf y]; ring
    simp only [Function.comp] at h3
    rw [mul_zero] at h3
    have : (fun y : ℝ => -(v : ℝ) * C * Real.exp (-y ^ 2 / (2 * (v : ℝ))))
        = fun y : ℝ => (-(v : ℝ) * C) * Real.exp (-y ^ 2 / (2 * (v : ℝ))) := rfl
    rw [← hfun]
    exact h3
  have hkey := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv
    hbase.integrableOn htend
  rw [hkey]
  ring

/-- The sharp Mills ratio UPPER bound: `P(N(0,v) > t) ≤ (v/t) φ_v(t)` for `t > 0`. -/
theorem gaussianReal_real_Ioi_le {v : ℝ≥0} (hv : 0 < (v : ℝ)) {t : ℝ} (ht : 0 < t) :
    ((gaussianReal 0 v).real (Set.Ioi t)) ≤ (v : ℝ) / t * gaussianPDFReal 0 v t := by
  have hvne : v ≠ 0 := fun h => by rw [h] at hv; simp at hv
  have hmeas : ((gaussianReal 0 v).real (Set.Ioi t))
      = ∫ x in Set.Ioi t, gaussianPDFReal 0 v x := by
    rw [MeasureTheory.measureReal_def,
      ProbabilityTheory.gaussianReal_apply_eq_integral 0 hvne (Set.Ioi t),
      ENNReal.toReal_ofReal
        (MeasureTheory.integral_nonneg
          (fun x => ProbabilityTheory.gaussianPDFReal_nonneg 0 v x))]
  have hbase : Integrable (fun x : ℝ => x * gaussianPDFReal 0 v x) volume := by
    have h : (fun x : ℝ => x * gaussianPDFReal 0 v x)
        = fun x : ℝ => (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
          (x * Real.exp (-(1 / (2 * (v : ℝ))) * x ^ 2)) := by
      funext x
      simp only [ProbabilityTheory.gaussianPDFReal, sub_zero]
      ring_nf
    rw [h]
    exact (integrable_mul_exp_neg_mul_sq (by positivity)).const_mul _
  have hg : IntegrableOn (gaussianPDFReal 0 v) (Set.Ioi t) volume :=
    (integrable_gaussianPDFReal 0 v).integrableOn
  have hxg : IntegrableOn (fun x : ℝ => t⁻¹ * (x * gaussianPDFReal 0 v x))
      (Set.Ioi t) volume := (hbase.const_mul t⁻¹).integrableOn
  have hmono := MeasureTheory.setIntegral_mono_on hg hxg measurableSet_Ioi ?_
  · rw [hmeas]
    refine hmono.trans ?_
    rw [MeasureTheory.integral_const_mul, integral_Ioi_id_mul_gaussianPDFReal hv t]
    rw [inv_mul_eq_div, div_mul_eq_mul_div]
  · intro x hx
    have hxt : t < x := hx
    have hpdfnn := ProbabilityTheory.gaussianPDFReal_nonneg 0 v x
    have h1 : (1 : ℝ) ≤ t⁻¹ * x := by
      rw [le_inv_mul_iff₀ ht]
      linarith
    nlinarith [hpdfnn]

/-- `E(Z - t)_+ = v φ_v(t) - t P(Z > t)` for a centred Gaussian `Z` of variance `v`.  This is
the identity behind `E(-V_∞(0)-t)_+ ∼ (Σ²/t) P(-V_∞(0)>t)` of the contact asymptotics. -/
theorem integral_Ioi_sub_mul_gaussianPDFReal {v : ℝ≥0} (hv : 0 < (v : ℝ)) (t : ℝ) :
    ∫ x in Set.Ioi t, (x - t) * gaussianPDFReal 0 v x
      = (v : ℝ) * gaussianPDFReal 0 v t
        - t * ∫ x in Set.Ioi t, gaussianPDFReal 0 v x := by
  have hbase : Integrable (fun x : ℝ => x * gaussianPDFReal 0 v x) volume := by
    have h : (fun x : ℝ => x * gaussianPDFReal 0 v x)
        = fun x : ℝ => (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
          (x * Real.exp (-(1 / (2 * (v : ℝ))) * x ^ 2)) := by
      funext x
      simp only [ProbabilityTheory.gaussianPDFReal, sub_zero]
      ring_nf
    rw [h]
    exact (integrable_mul_exp_neg_mul_sq (by positivity)).const_mul _
  have h1 : IntegrableOn (fun x : ℝ => x * gaussianPDFReal 0 v x) (Set.Ioi t) volume :=
    hbase.integrableOn
  have h2 : IntegrableOn (fun x : ℝ => t * gaussianPDFReal 0 v x) (Set.Ioi t) volume :=
    ((integrable_gaussianPDFReal 0 v).const_mul t).integrableOn
  have hsplit : ∀ x : ℝ, (x - t) * gaussianPDFReal 0 v x
      = x * gaussianPDFReal 0 v x - t * gaussianPDFReal 0 v x := fun x => by ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hsplit),
    MeasureTheory.integral_sub h1 h2, integral_Ioi_id_mul_gaussianPDFReal hv t,
    MeasureTheory.integral_const_mul]

/-- The derivative of the centred Gaussian density: `φ_v'(x) = -(x/v) φ_v(x)`. -/
theorem hasDerivAt_gaussianPDFReal {v : ℝ≥0} (hv : 0 < (v : ℝ)) (x : ℝ) :
    HasDerivAt (fun y : ℝ => gaussianPDFReal 0 v y)
      (-(x / (v : ℝ)) * gaussianPDFReal 0 v x) x := by
  set C : ℝ := (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ with hC
  have hpdf : ∀ y : ℝ, gaussianPDFReal 0 v y = C * Real.exp (-y ^ 2 / (2 * (v : ℝ))) := by
    intro y
    simp only [ProbabilityTheory.gaussianPDFReal, sub_zero, hC]
  have h1 : HasDerivAt (fun y : ℝ => -y ^ 2 / (2 * (v : ℝ)))
      (-(2 * x) / (2 * (v : ℝ))) x := by
    simpa using ((hasDerivAt_pow 2 x).neg.div_const (2 * (v : ℝ)))
  have h2 := (h1.exp).const_mul C
  have hfun : (fun y : ℝ => C * Real.exp (-y ^ 2 / (2 * (v : ℝ))))
      = fun y : ℝ => gaussianPDFReal 0 v y := by funext y; rw [hpdf y]
  rw [hfun] at h2
  have hval : C * (Real.exp (-x ^ 2 / (2 * (v : ℝ))) * (-(2 * x) / (2 * (v : ℝ))))
      = -(x / (v : ℝ)) * gaussianPDFReal 0 v x := by
    rw [hpdf x]; field_simp
  rwa [hval] at h2

/-- The derivative of the Mills coefficient `v/x - v²/x³`. -/
theorem hasDerivAt_millsCoeff {v : ℝ≥0} (hv : 0 < (v : ℝ)) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => (v : ℝ) / y - (v : ℝ) ^ 2 / y ^ 3)
      (-((v : ℝ) / x ^ 2) + 3 * (v : ℝ) ^ 2 / x ^ 4) x := by
  have h1 : HasDerivAt (fun y : ℝ => (v : ℝ) / y) (-((v : ℝ) / x ^ 2)) x := by
    simpa [div_eq_mul_inv, neg_div] using (hasDerivAt_inv hx).const_mul (v : ℝ)
  have h3 : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
    simpa using hasDerivAt_pow 3 x
  have h2 : HasDerivAt (fun y : ℝ => (v : ℝ) ^ 2 / y ^ 3)
      ((v : ℝ) ^ 2 * (-(3 * x ^ 2) / (x ^ 3) ^ 2)) x := by
    simpa [div_eq_mul_inv] using ((h3.inv (by positivity)).const_mul ((v : ℝ) ^ 2))
  have hsub := h1.sub h2
  have hval : -((v : ℝ) / x ^ 2) - (v : ℝ) ^ 2 * (-(3 * x ^ 2) / (x ^ 3) ^ 2)
      = -((v : ℝ) / x ^ 2) + 3 * (v : ℝ) ^ 2 / x ^ 4 := by
    field_simp; ring
  rw [hval] at hsub
  exact hsub

/-- **The second-order Mills lower bound** `P(N(0,v) > t) ≥ (v/t - v²/t³) φ_v(t)` for
`t > 0`, the companion of `gaussianReal_real_Ioi_le`.  The antiderivative is
`g(x) = (v/x - v²/x³) φ_v(x)`, whose derivative is `φ_v(x)(3v²/x⁴ - 1)`, so that `-g' ≤ φ_v`
pointwise and the fundamental theorem of calculus on the half line gives
`∫_{x>t} φ_v ≥ ∫_{x>t} (-g') = g(t)`.  The second-order lower bound `P(N(0,v) > t) ≥ (v/t - v²/t³) φ_v(t)` for `t > 0`. -/
theorem gaussianReal_real_Ioi_ge_sharp {v : ℝ≥0} (hv : 0 < (v : ℝ)) {t : ℝ} (ht : 0 < t) :
    ((v : ℝ) / t - (v : ℝ) ^ 2 / t ^ 3) * gaussianPDFReal 0 v t
      ≤ ((gaussianReal 0 v).real (Set.Ioi t)) := by
  have hvne : v ≠ 0 := fun h => by rw [h] at hv; simp at hv
  set g : ℝ → ℝ := fun x => ((v : ℝ) / x - (v : ℝ) ^ 2 / x ^ 3) * gaussianPDFReal 0 v x with hg
  set G : ℝ → ℝ := fun x => gaussianPDFReal 0 v x * (3 * (v : ℝ) ^ 2 / x ^ 4 - 1) with hG
  have hgd : ∀ x ∈ Set.Ioi t, HasDerivAt g (G x) x := by
    intro x hx
    have hx0 : 0 < x := lt_trans ht hx
    have hmul := (hasDerivAt_millsCoeff hv (ne_of_gt hx0)).mul (hasDerivAt_gaussianPDFReal hv x)
    have hval : (-((v : ℝ) / x ^ 2) + 3 * (v : ℝ) ^ 2 / x ^ 4) * gaussianPDFReal 0 v x
        + ((v : ℝ) / x - (v : ℝ) ^ 2 / x ^ 3) * (-(x / (v : ℝ)) * gaussianPDFReal 0 v x)
        = G x := by
      rw [hG]
      field_simp
      ring
    rw [hval] at hmul
    exact hmul
  have hle : ∀ x ∈ Set.Ioi t, -G x ≤ gaussianPDFReal 0 v x := by
    intro x hx
    have hx0 : 0 < x := lt_trans ht hx
    have hpdfnn := ProbabilityTheory.gaussianPDFReal_nonneg 0 v x
    have hq : 0 ≤ 3 * (v : ℝ) ^ 2 / x ^ 4 := by positivity
    rw [hG]
    nlinarith [hpdfnn, hq]
  have hGint : IntegrableOn G (Set.Ioi t) volume := by
    have hmeasG : Measurable G := by
      rw [hG]
      exact (ProbabilityTheory.measurable_gaussianPDFReal 0 v).mul
        (((measurable_const.div (measurable_id.pow_const 4)).sub measurable_const))
    refine Integrable.mono' (g := fun x : ℝ => (3 * (v : ℝ) ^ 2 / t ^ 4 + 1) *
        gaussianPDFReal 0 v x)
      (((ProbabilityTheory.integrable_gaussianPDFReal 0 v).const_mul _).integrableOn)
      hmeasG.aestronglyMeasurable ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    have hx0 : 0 < x := lt_trans ht hx
    have hxt : t < x := hx
    have hpdfnn := ProbabilityTheory.gaussianPDFReal_nonneg 0 v x
    have hq : 3 * (v : ℝ) ^ 2 / x ^ 4 ≤ 3 * (v : ℝ) ^ 2 / t ^ 4 := by
      gcongr
    have hq0 : 0 ≤ 3 * (v : ℝ) ^ 2 / x ^ 4 := by positivity
    rw [Real.norm_eq_abs, hG]
    rw [abs_mul, abs_of_nonneg hpdfnn]
    have habs : |3 * (v : ℝ) ^ 2 / x ^ 4 - 1| ≤ 3 * (v : ℝ) ^ 2 / t ^ 4 + 1 := by
      rw [abs_le]
      constructor <;> linarith
    nlinarith [hpdfnn]
  have hcont : ContinuousWithinAt g (Set.Ici t) t := by
    have hd := (hasDerivAt_millsCoeff hv (ne_of_gt ht)).mul (hasDerivAt_gaussianPDFReal hv t)
    exact hd.continuousAt.continuousWithinAt
  have htend : Tendsto g atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => (v : ℝ) / x - (v : ℝ) ^ 2 / x ^ 3) atTop (𝓝 0) := by
      have ha : Tendsto (fun x : ℝ => (v : ℝ) / x) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      have hb : Tendsto (fun x : ℝ => (v : ℝ) ^ 2 / x ^ 3) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))
      simpa using ha.sub hb
    have h2 : Tendsto (fun x : ℝ => gaussianPDFReal 0 v x) atTop (𝓝 0) := by
      have h3 : Tendsto (fun y : ℝ => -y ^ 2 / (2 * (v : ℝ))) atTop atBot := by
        refine Filter.Tendsto.atBot_div_const (by positivity) ?_
        exact tendsto_neg_atBot_iff.mpr (tendsto_pow_atTop (by norm_num))
      have h4 := (Real.tendsto_exp_atBot.comp h3).const_mul
        (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹
      simp only [Function.comp, mul_zero] at h4
      have hfun : (fun y : ℝ => (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
          Real.exp (-y ^ 2 / (2 * (v : ℝ)))) = fun y : ℝ => gaussianPDFReal 0 v y := by
        funext y
        simp only [ProbabilityTheory.gaussianPDFReal, sub_zero]
      rwa [hfun] at h4
    simpa using h1.mul h2
  have hkey := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hgd hGint htend
  have hmeas : ((gaussianReal 0 v).real (Set.Ioi t))
      = ∫ x in Set.Ioi t, gaussianPDFReal 0 v x := by
    rw [MeasureTheory.measureReal_def,
      ProbabilityTheory.gaussianReal_apply_eq_integral 0 hvne (Set.Ioi t),
      ENNReal.toReal_ofReal
        (MeasureTheory.integral_nonneg
          (fun x => ProbabilityTheory.gaussianPDFReal_nonneg 0 v x))]
  have hmono : ∫ x in Set.Ioi t, -G x ≤ ∫ x in Set.Ioi t, gaussianPDFReal 0 v x :=
    MeasureTheory.setIntegral_mono_on hGint.neg
      ((ProbabilityTheory.integrable_gaussianPDFReal 0 v).integrableOn) measurableSet_Ioi hle
  rw [MeasureTheory.integral_neg, hkey] at hmono
  rw [hmeas]
  have hgt : g t = ((v : ℝ) / t - (v : ℝ) ^ 2 / t ^ 3) * gaussianPDFReal 0 v t := rfl
  rw [← hgt]
  linarith

/-- The derivative of the third-order Mills coefficient `v/x - v²/x³ + 3v³/x⁵`. -/
theorem hasDerivAt_millsCoeff3 {v : ℝ≥0} {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => (v : ℝ) / y - (v : ℝ) ^ 2 / y ^ 3 + 3 * (v : ℝ) ^ 3 / y ^ 5)
      (-((v : ℝ) / x ^ 2) + 3 * (v : ℝ) ^ 2 / x ^ 4 - 15 * (v : ℝ) ^ 3 / x ^ 6) x := by
  have h1 : HasDerivAt (fun y : ℝ => (v : ℝ) / y) (-((v : ℝ) / x ^ 2)) x := by
    simpa [div_eq_mul_inv, neg_div] using (hasDerivAt_inv hx).const_mul (v : ℝ)
  have h3 : HasDerivAt (fun y : ℝ => y ^ 3) (3 * x ^ 2) x := by
    simpa using hasDerivAt_pow 3 x
  have h2 : HasDerivAt (fun y : ℝ => (v : ℝ) ^ 2 / y ^ 3)
      ((v : ℝ) ^ 2 * (-(3 * x ^ 2) / (x ^ 3) ^ 2)) x := by
    simpa [div_eq_mul_inv] using ((h3.inv (by positivity)).const_mul ((v : ℝ) ^ 2))
  have h5 : HasDerivAt (fun y : ℝ => y ^ 5) (5 * x ^ 4) x := by
    simpa using hasDerivAt_pow 5 x
  have h4 : HasDerivAt (fun y : ℝ => 3 * (v : ℝ) ^ 3 / y ^ 5)
      (3 * (v : ℝ) ^ 3 * (-(5 * x ^ 4) / (x ^ 5) ^ 2)) x := by
    simpa [div_eq_mul_inv] using ((h5.inv (by positivity)).const_mul (3 * (v : ℝ) ^ 3))
  have hsum := (h1.sub h2).add h4
  have hval : -((v : ℝ) / x ^ 2) - (v : ℝ) ^ 2 * (-(3 * x ^ 2) / (x ^ 3) ^ 2)
      + 3 * (v : ℝ) ^ 3 * (-(5 * x ^ 4) / (x ^ 5) ^ 2)
      = -((v : ℝ) / x ^ 2) + 3 * (v : ℝ) ^ 2 / x ^ 4 - 15 * (v : ℝ) ^ 3 / x ^ 6 := by
    field_simp; ring
  rw [hval] at hsum
  exact hsum

/-- **The third-order Mills upper bound** `P(N(0,v) > t) ≤ (v/t - v²/t³ + 3v³/t⁵) φ_v(t)`.
The antiderivative is `h(x) = (v/x - v²/x³ + 3v³/x⁵) φ_v(x)`, whose derivative is
`-φ_v(x)(1 + 15v³/x⁶)`, so that `φ_v ≤ -h'` pointwise and the fundamental theorem of
calculus on the half line gives `∫_{x>t} φ_v ≤ h(t)`.  The third-order upper bound `P(N(0,v) > t) ≤ (v/t - v²/t³ + 3v³/t⁵) φ_v(t)`. -/
theorem gaussianReal_real_Ioi_le_sharp {v : ℝ≥0} (hv : 0 < (v : ℝ)) {t : ℝ} (ht : 0 < t) :
    ((gaussianReal 0 v).real (Set.Ioi t))
      ≤ ((v : ℝ) / t - (v : ℝ) ^ 2 / t ^ 3 + 3 * (v : ℝ) ^ 3 / t ^ 5)
        * gaussianPDFReal 0 v t := by
  have hvne : v ≠ 0 := fun h => by rw [h] at hv; simp at hv
  set h : ℝ → ℝ := fun x =>
    ((v : ℝ) / x - (v : ℝ) ^ 2 / x ^ 3 + 3 * (v : ℝ) ^ 3 / x ^ 5) * gaussianPDFReal 0 v x with hh
  set H : ℝ → ℝ := fun x => gaussianPDFReal 0 v x * (-(15 * (v : ℝ) ^ 3 / x ^ 6) - 1) with hH
  have hhd : ∀ x ∈ Set.Ioi t, HasDerivAt h (H x) x := by
    intro x hx
    have hx0 : 0 < x := lt_trans ht hx
    have hmul := (hasDerivAt_millsCoeff3 (v := v) (ne_of_gt hx0)).mul
      (hasDerivAt_gaussianPDFReal hv x)
    have hval : (-((v : ℝ) / x ^ 2) + 3 * (v : ℝ) ^ 2 / x ^ 4 - 15 * (v : ℝ) ^ 3 / x ^ 6)
          * gaussianPDFReal 0 v x
        + ((v : ℝ) / x - (v : ℝ) ^ 2 / x ^ 3 + 3 * (v : ℝ) ^ 3 / x ^ 5)
          * (-(x / (v : ℝ)) * gaussianPDFReal 0 v x) = H x := by
      rw [hH]; field_simp; ring
    rw [hval] at hmul
    exact hmul
  have hle : ∀ x ∈ Set.Ioi t, gaussianPDFReal 0 v x ≤ -H x := by
    intro x hx
    have hx0 : 0 < x := lt_trans ht hx
    have hpdfnn := ProbabilityTheory.gaussianPDFReal_nonneg 0 v x
    have hq : 0 ≤ 15 * (v : ℝ) ^ 3 / x ^ 6 := by positivity
    rw [hH]
    nlinarith [hpdfnn, hq]
  have hHint : IntegrableOn H (Set.Ioi t) volume := by
    have hmeasH : Measurable H := by
      rw [hH]
      exact (ProbabilityTheory.measurable_gaussianPDFReal 0 v).mul
        (((measurable_const.div (measurable_id.pow_const 6)).neg).sub measurable_const)
    refine Integrable.mono' (g := fun x : ℝ => (15 * (v : ℝ) ^ 3 / t ^ 6 + 1) *
        gaussianPDFReal 0 v x)
      (((ProbabilityTheory.integrable_gaussianPDFReal 0 v).const_mul _).integrableOn)
      hmeasH.aestronglyMeasurable ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    have hx0 : 0 < x := lt_trans ht hx
    have hxt : t < x := hx
    have hpdfnn := ProbabilityTheory.gaussianPDFReal_nonneg 0 v x
    have hq : 15 * (v : ℝ) ^ 3 / x ^ 6 ≤ 15 * (v : ℝ) ^ 3 / t ^ 6 := by gcongr
    have hq0 : 0 ≤ 15 * (v : ℝ) ^ 3 / x ^ 6 := by positivity
    rw [Real.norm_eq_abs, hH, abs_mul, abs_of_nonneg hpdfnn]
    have habs : |-(15 * (v : ℝ) ^ 3 / x ^ 6) - 1| ≤ 15 * (v : ℝ) ^ 3 / t ^ 6 + 1 := by
      rw [abs_le]; constructor <;> linarith
    nlinarith [hpdfnn]
  have hcont : ContinuousWithinAt h (Set.Ici t) t := by
    have hd := (hasDerivAt_millsCoeff3 (v := v) (ne_of_gt ht)).mul
      (hasDerivAt_gaussianPDFReal hv t)
    exact hd.continuousAt.continuousWithinAt
  have htend : Tendsto h atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ =>
        (v : ℝ) / x - (v : ℝ) ^ 2 / x ^ 3 + 3 * (v : ℝ) ^ 3 / x ^ 5) atTop (𝓝 0) := by
      have ha : Tendsto (fun x : ℝ => (v : ℝ) / x) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_id
      have hb : Tendsto (fun x : ℝ => (v : ℝ) ^ 2 / x ^ 3) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))
      have hc : Tendsto (fun x : ℝ => 3 * (v : ℝ) ^ 3 / x ^ 5) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop (tendsto_pow_atTop (by norm_num))
      simpa using (ha.sub hb).add hc
    have h2 : Tendsto (fun x : ℝ => gaussianPDFReal 0 v x) atTop (𝓝 0) := by
      have h3 : Tendsto (fun y : ℝ => -y ^ 2 / (2 * (v : ℝ))) atTop atBot := by
        refine Filter.Tendsto.atBot_div_const (by positivity) ?_
        exact tendsto_neg_atBot_iff.mpr (tendsto_pow_atTop (by norm_num))
      have h4 := (Real.tendsto_exp_atBot.comp h3).const_mul
        (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹
      simp only [Function.comp, mul_zero] at h4
      have hfun : (fun y : ℝ => (Real.sqrt (2 * Real.pi * (v : ℝ)))⁻¹ *
          Real.exp (-y ^ 2 / (2 * (v : ℝ)))) = fun y : ℝ => gaussianPDFReal 0 v y := by
        funext y
        simp only [ProbabilityTheory.gaussianPDFReal, sub_zero]
      rwa [hfun] at h4
    simpa using h1.mul h2
  have hkey := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hhd hHint htend
  have hmeas : ((gaussianReal 0 v).real (Set.Ioi t))
      = ∫ x in Set.Ioi t, gaussianPDFReal 0 v x := by
    rw [MeasureTheory.measureReal_def,
      ProbabilityTheory.gaussianReal_apply_eq_integral 0 hvne (Set.Ioi t),
      ENNReal.toReal_ofReal
        (MeasureTheory.integral_nonneg
          (fun x => ProbabilityTheory.gaussianPDFReal_nonneg 0 v x))]
  have hmono : ∫ x in Set.Ioi t, gaussianPDFReal 0 v x ≤ ∫ x in Set.Ioi t, -H x :=
    MeasureTheory.setIntegral_mono_on
      ((ProbabilityTheory.integrable_gaussianPDFReal 0 v).integrableOn) hHint.neg
      measurableSet_Ioi hle
  rw [MeasureTheory.integral_neg, hkey] at hmono
  rw [hmeas]
  have hht : h t = ((v : ℝ) / t - (v : ℝ) ^ 2 / t ^ 3 + 3 * (v : ℝ) ^ 3 / t ^ 5)
      * gaussianPDFReal 0 v t := rfl
  rw [← hht]
  linarith

/-- The Gaussian measure of a half line as the integral of the density. -/
theorem gaussianReal_real_Ioi_eq_integral {v : ℝ≥0} (hv : v ≠ 0) (t : ℝ) :
    ((gaussianReal 0 v).real (Set.Ioi t)) = ∫ x in Set.Ioi t, gaussianPDFReal 0 v x := by
  rw [MeasureTheory.measureReal_def,
    ProbabilityTheory.gaussianReal_apply_eq_integral 0 hv (Set.Ioi t),
    ENNReal.toReal_ofReal
      (MeasureTheory.integral_nonneg
        (fun x => ProbabilityTheory.gaussianPDFReal_nonneg 0 v x))]

/-- **The mean overshoot against the tail.**  `|E(Z-t)_+ - (v/t) P(Z>t)| ≤ (2v³/t⁴ + 3v⁴/t⁶)
φ_v(t)` for `t > 0`, which with `(v/t) P(Z>t) ≥ (v²/t² - v³/t⁴) φ_v(t)` is the paper's
`E(-V_∞(0)-t)_+ ∼ (Σ²/t) P(-V_∞(0)>t)`. -/
theorem abs_meanOvershoot_sub_le {v : ℝ≥0} (hv : 0 < (v : ℝ)) {t : ℝ} (ht : 0 < t) :
    |(∫ x in Set.Ioi t, (x - t) * gaussianPDFReal 0 v x)
        - (v : ℝ) / t * ((gaussianReal 0 v).real (Set.Ioi t))|
      ≤ (2 * (v : ℝ) ^ 3 / t ^ 4 + 3 * (v : ℝ) ^ 4 / t ^ 6) * gaussianPDFReal 0 v t := by
  have hvne : v ≠ 0 := fun h => by rw [h] at hv; simp at hv
  have hphi := ProbabilityTheory.gaussianPDFReal_nonneg 0 v t
  have hid := integral_Ioi_sub_mul_gaussianPDFReal hv t
  have hP := gaussianReal_real_Ioi_eq_integral hvne t
  have hlow := gaussianReal_real_Ioi_ge_sharp hv ht
  have hup := gaussianReal_real_Ioi_le_sharp hv ht
  rw [hP] at hlow hup
  set P : ℝ := ∫ x in Set.Ioi t, gaussianPDFReal 0 v x with hPdef
  rw [hP, hid]
  have hkey : ((v : ℝ) * gaussianPDFReal 0 v t - t * P) - (v : ℝ) / t * P
      = (v : ℝ) * gaussianPDFReal 0 v t - (t + (v : ℝ) / t) * P := by ring
  rw [hkey, abs_le]
  have htv : 0 < t + (v : ℝ) / t := by positivity
  constructor
  · have := mul_le_mul_of_nonneg_left hup htv.le
    have hexp : (t + (v : ℝ) / t)
        * (((v : ℝ) / t - (v : ℝ) ^ 2 / t ^ 3 + 3 * (v : ℝ) ^ 3 / t ^ 5)
          * gaussianPDFReal 0 v t)
        = ((v : ℝ) + 2 * (v : ℝ) ^ 3 / t ^ 4 + 3 * (v : ℝ) ^ 4 / t ^ 6)
          * gaussianPDFReal 0 v t := by
      field_simp; ring
    rw [hexp] at this
    nlinarith [this]
  · have := mul_le_mul_of_nonneg_left hlow htv.le
    have hexp : (t + (v : ℝ) / t)
        * (((v : ℝ) / t - (v : ℝ) ^ 2 / t ^ 3) * gaussianPDFReal 0 v t)
        = ((v : ℝ) - (v : ℝ) ^ 3 / t ^ 4) * gaussianPDFReal 0 v t := by
      field_simp; ring
    rw [hexp] at this
    have hpos : 0 ≤ (v : ℝ) ^ 4 / t ^ 6 * gaussianPDFReal 0 v t := by positivity
    have hpos2 : 0 ≤ (v : ℝ) ^ 3 / t ^ 4 * gaussianPDFReal 0 v t := by positivity
    have hgoal : (2 * (v : ℝ) ^ 3 / t ^ 4 + 3 * (v : ℝ) ^ 4 / t ^ 6) * gaussianPDFReal 0 v t
        = 2 * ((v : ℝ) ^ 3 / t ^ 4 * gaussianPDFReal 0 v t)
          + 3 * ((v : ℝ) ^ 4 / t ^ 6 * gaussianPDFReal 0 v t) := by ring
    have hthis : ((v : ℝ) - (v : ℝ) ^ 3 / t ^ 4) * gaussianPDFReal 0 v t
        = (v : ℝ) * gaussianPDFReal 0 v t
          - (v : ℝ) ^ 3 / t ^ 4 * gaussianPDFReal 0 v t := by ring
    rw [hthis] at this
    rw [hgoal]
    linarith [this, hpos, hpos2]

end LatticeProb.GaussTail
