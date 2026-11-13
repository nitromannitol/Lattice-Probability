/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.RandomVarianceTaylor at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.ConditionalGaussianIdentification
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Telescoping with a random bracket: the exponential compensator

`ConditionalCharacteristicProducts` and `ConditionalGaussianIdentification` telescope the
conditional characteristic function of a martingale increment against **deterministic**
factors `1 - u² v_k / 2`; random conditional variances cannot be pulled through the past
conditional expectation, so those files cannot treat a martingale whose bracket is random.

This file telescopes instead with the **past-measurable exponential compensator**
`exp (u² (∑_{k<i} D k) / 2)`, where `D k ≥ 0` are the bracket increments.  With
`Z k` the martingale increments, `E_k = exp (i u Z_k)` and `x_k = u² D_k / 2`, one step is

  `E_k e^{x_k} - 1 = (E_k - 1 + x_k) + E_k (e^{x_k} - 1 - x_k) + (E_k - 1) x_k`,

and, given the conditional identities `P[Z_k | F_k] = 0`, `P[Z_k² | F_k] = P[D_k | F_k]`,

* the conditional expectation of the first term is exactly the remainder of the conditional
  Taylor estimate `MartingaleCharacteristicTaylor.norm_condExp_cexp_sub_quadratic_taylor_le`,
  which already allows a **random** conditional variance (`V = P[D_k | F_k]`);
* the second term is bounded by `e^{u²K/2} x_k²` once `∑ D_k ≤ K`;
* the third is bounded by `|u Z_k| · x_k ≤ (u²/2) (η u² Z_k² / 2 + D_k² / (2η))` for any `η > 0`.

Integrating against a past-measurable factor of modulus `≤ e^{u²K/2}` and summing the steps
gives `norm_integral_test_mul_cexp_mul_exp_sub_le`: the tested compensated Fourier integral
`E[W e^{iu ∑ Z_k} e^{u² ∑ D_k / 2}]` is within `∑_k stepError k` of `E[W]`, and the aggregated
form `norm_integral_test_mul_cexp_mul_exp_sub_le'` shows that the total error is controlled by
the truncation level `δ`, the Lindeberg sum, the free parameter `η`, and the quadratic
oscillation `∑_k E[D_k²]` of the bracket — never by the individual conditional variances.

Nothing about the reflected walk appears here; this is the one-scale input of the
approximate-bracket martingale CLT (`Limit/ApproximateBracketCLT`).
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace ReflectedGMS.ApproximateBracketCLT

open ReflectedGMS.MartingaleLimit

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-! ## Elementary bounds -/

/-- `‖e^{ix} - 1‖ ≤ |x|`. -/
theorem norm_cexp_ofReal_mul_I_sub_one_le (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ ≤ |x| := by
  have h := Real.norm_exp_I_mul_ofReal_sub_one_le (x := x)
  rw [mul_comm] at h
  simpa [Real.norm_eq_abs] using h

/-- Second-order bound for the real exponential on a bounded nonnegative range:
`e^x - 1 - x ≤ e^L x²` for `0 ≤ x ≤ L`. -/
theorem exp_sub_one_sub_self_le {x L : ℝ} (hx0 : 0 ≤ x) (hxL : x ≤ L) :
    Real.exp x - 1 - x ≤ Real.exp L * x ^ 2 := by
  have hL1 : 1 ≤ Real.exp L := Real.one_le_exp (hx0.trans hxL)
  rcases le_or_gt x 1 with hx1 | hx1
  · have h := Real.abs_exp_sub_one_sub_id_le (abs_le.2 ⟨by linarith, hx1⟩)
    have h1 : Real.exp x - 1 - x ≤ x ^ 2 := (le_abs_self _).trans h
    have h2 : x ^ 2 ≤ Real.exp L * x ^ 2 := by
      have := mul_le_mul_of_nonneg_right hL1 (sq_nonneg x)
      linarith
    linarith
  · have h1 : Real.exp x ≤ Real.exp L := Real.exp_le_exp.2 hxL
    have h2 : (1 : ℝ) ≤ x ^ 2 := by nlinarith
    have h3 : Real.exp L ≤ Real.exp L * x ^ 2 := by
      have := mul_le_mul_of_nonneg_left h2 (Real.exp_pos L).le
      linarith
    linarith

/-- The exponential remainder is nonnegative. -/
theorem exp_sub_one_sub_self_nonneg (x : ℝ) : 0 ≤ Real.exp x - 1 - x := by
  have := Real.add_one_le_exp x
  linarith

/-- The elementary inequality `a b ≤ (η/2) a² + (1/(2η)) b²`. -/
theorem mul_le_half_add (a b η : ℝ) (hη : 0 < η) :
    a * b ≤ η / 2 * a ^ 2 + η⁻¹ / 2 * b ^ 2 := by
  have hη' : η ≠ 0 := hη.ne'
  have key : η / 2 * a ^ 2 + η⁻¹ / 2 * b ^ 2 - a * b = (η * a - b) ^ 2 / (2 * η) := by
    field_simp
    ring
  have hnn : 0 ≤ (η * a - b) ^ 2 / (2 * η) := by positivity
  linarith

/-- `|e^{-x} - e^{-y}| ≤ |x - y|` for nonnegative `x, y`. -/
theorem abs_exp_neg_sub_exp_neg_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |Real.exp (-x) - Real.exp (-y)| ≤ |x - y| := by
  have aux : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b →
      0 ≤ Real.exp (-a) - Real.exp (-b) ∧ Real.exp (-a) - Real.exp (-b) ≤ b - a := by
    intro a b ha hab
    have hsplit : Real.exp (-b) = Real.exp (-a) * Real.exp (-(b - a)) := by
      rw [← Real.exp_add]
      ring_nf
    have h1 : -(b - a) + 1 ≤ Real.exp (-(b - a)) := Real.add_one_le_exp _
    have h2 : Real.exp (-a) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have h3 : Real.exp (-(b - a)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have h4 : 0 ≤ Real.exp (-a) := (Real.exp_pos _).le
    have hfac : Real.exp (-a) - Real.exp (-b)
        = Real.exp (-a) * (1 - Real.exp (-(b - a))) := by
      rw [hsplit]
      ring
    rw [hfac]
    constructor
    · exact mul_nonneg h4 (by linarith)
    · calc Real.exp (-a) * (1 - Real.exp (-(b - a)))
          ≤ 1 * (1 - Real.exp (-(b - a))) :=
            mul_le_mul_of_nonneg_right h2 (by linarith)
        _ ≤ b - a := by linarith
  rcases le_total x y with hxy | hxy
  · obtain ⟨h0, h1⟩ := aux hx hxy
    rw [abs_of_nonneg h0, abs_of_nonpos (by linarith)]
    linarith
  · obtain ⟨h0, h1⟩ := aux hy hxy
    rw [abs_sub_comm, abs_of_nonneg h0, abs_of_nonneg (by linarith)]
    linarith

/-! ## Pulling a bounded past-measurable factor out of an integral -/

/-- A bounded `m`-measurable factor can be pulled through the conditional expectation:
`‖∫ G Y‖ ≤ c ∫ ‖P[Y | m]‖`. -/
theorem norm_integral_mul_le_mul_integral_norm_condExp [IsProbabilityMeasure P]
    (m : {q : MeasurableSpace Ω // q ≤ mΩ}) {G Y : Ω → ℂ}
    (hG : StronglyMeasurable[m.1] G) {c : ℝ} (hGc : ∀ᵐ ω ∂P, ‖G ω‖ ≤ c)
    (hY : Integrable Y P) :
    ‖∫ ω, G ω * Y ω ∂P‖ ≤ c * ∫ ω, ‖(P[Y | m.1]) ω‖ ∂P := by
  have hGΩ : StronglyMeasurable G := hG.mono m.2
  have hGY : Integrable (fun ω => G ω * Y ω) P := hY.bdd_mul hGΩ.aestronglyMeasurable hGc
  have hpull : P[fun ω => G ω * Y ω | m.1] =ᵐ[P] fun ω => G ω * (P[Y | m.1]) ω :=
    condExp_bilin_of_stronglyMeasurable_left (.mul ℝ ℂ) hG hGY hY
  have hGc' : Integrable (fun ω => G ω * (P[Y | m.1]) ω) P :=
    integrable_condExp.bdd_mul hGΩ.aestronglyMeasurable hGc
  have h1 : (∫ ω, G ω * Y ω ∂P) = ∫ ω, G ω * (P[Y | m.1]) ω ∂P := by
    calc (∫ ω, G ω * Y ω ∂P) = ∫ ω, (P[fun ω => G ω * Y ω | m.1]) ω ∂P :=
          (integral_condExp m.2).symm
      _ = ∫ ω, G ω * (P[Y | m.1]) ω ∂P := integral_congr_ae hpull
  rw [h1]
  calc ‖∫ ω, G ω * (P[Y | m.1]) ω ∂P‖
      ≤ ∫ ω, ‖G ω * (P[Y | m.1]) ω‖ ∂P := norm_integral_le_integral_norm _
    _ ≤ ∫ ω, c * ‖(P[Y | m.1]) ω‖ ∂P := by
        refine integral_mono_ae hGc'.norm (integrable_condExp.norm.const_mul c) ?_
        filter_upwards [hGc] with ω hω
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right hω (norm_nonneg _)
    _ = c * ∫ ω, ‖(P[Y | m.1]) ω‖ ∂P := integral_const_mul _ _

/-! ## The one-step estimate -/

/-- **One step of the compensated telescoping.**  For an increment `Z` with vanishing
conditional mean and conditional second moment `P[D | m]` (a random bracket increment
`0 ≤ D ≤ K`), the integral of a bounded past-measurable factor `G` against
`e^{iuZ} e^{u²D/2} - 1` is controlled by the Taylor truncation (level `δ`), the Lindeberg
tail of `Z`, the free parameter `η`, and the second moment of `D`. -/
theorem norm_integral_mul_step_le [IsProbabilityMeasure P]
    (m : {q : MeasurableSpace Ω // q ≤ mΩ})
    {G : Ω → ℂ} (hG : StronglyMeasurable[m.1] G) {c : ℝ} (hc0 : 0 ≤ c)
    (hGc : ∀ᵐ ω ∂P, ‖G ω‖ ≤ c)
    {Z D : Ω → ℝ} (hZm : Measurable Z) (hZ1 : Integrable Z P)
    (hZ2 : Integrable (fun ω => Z ω ^ 2) P)
    (hDm : Measurable D) (hD1 : Integrable D P) (hD2 : Integrable (fun ω => D ω ^ 2) P)
    (hD0 : ∀ᵐ ω ∂P, 0 ≤ D ω) {K : ℝ} (hDK : ∀ᵐ ω ∂P, D ω ≤ K)
    (hmean : P[Z | m.1] =ᵐ[P] 0)
    (hvar : P[fun ω => Z ω ^ 2 | m.1] =ᵐ[P] P[D | m.1])
    {u δ η : ℝ} (hδ : 0 ≤ δ) (huδ : |u| * δ ≤ 1) (hη : 0 < η) :
    ‖∫ ω, G ω * (Complex.exp ((u * Z ω : ℝ) * Complex.I)
        * ((Real.exp (u ^ 2 * D ω / 2) : ℝ) : ℂ) - 1) ∂P‖
      ≤ c * (Real.exp (u ^ 2 * K / 2) * (u ^ 4 / 4) * (∫ ω, D ω ^ 2 ∂P)
          + u ^ 2 / 2 * (η / 2 * u ^ 2 * (∫ ω, D ω ∂P) + η⁻¹ / 2 * ∫ ω, D ω ^ 2 ∂P)
          + 2 / 9 * |u| ^ 3 * δ * (∫ ω, D ω ∂P)
          + 4 * u ^ 2 * ∫ ω, Set.indicator {ω | δ < |Z ω|} (fun ω => Z ω ^ 2) ω ∂P) := by
  classical
  set L : ℝ := u ^ 2 * K / 2 with hL
  have hGΩ : StronglyMeasurable G := hG.mono m.2
  -- the pieces
  set x : Ω → ℝ := fun ω => u ^ 2 * D ω / 2 with hx
  set E : Ω → ℂ := fun ω => Complex.exp ((u * Z ω : ℝ) * Complex.I) with hE
  set R : Ω → ℂ := fun ω =>
    E ω * ((Real.exp (x ω) - 1 - x ω : ℝ) : ℂ) + (E ω - 1) * (x ω : ℂ) with hR
  set S : Ω → ℂ := fun ω => E ω - 1 + (x ω : ℂ) with hS
  have hdecomp : ∀ ω, G ω * (Complex.exp ((u * Z ω : ℝ) * Complex.I)
      * ((Real.exp (u ^ 2 * D ω / 2) : ℝ) : ℂ) - 1) = G ω * S ω + G ω * R ω := by
    intro ω
    simp only [hS, hR, hE, hx]
    push_cast
    ring
  -- measurability
  have hxm : Measurable x := (hDm.const_mul _).div_const _
  have hEm : Measurable E := by
    have h1 : Measurable fun ω => ((u * Z ω : ℝ) : ℂ) * Complex.I :=
      (Complex.measurable_ofReal.comp (hZm.const_mul u)).mul_const _
    exact Complex.measurable_exp.comp h1
  have hRm : Measurable R := by
    have h1 : Measurable fun ω => ((Real.exp (x ω) - 1 - x ω : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp ((Real.measurable_exp.comp hxm).sub measurable_const
        |>.sub hxm)
    have h2 : Measurable fun ω => (x ω : ℂ) := Complex.measurable_ofReal.comp hxm
    exact (hEm.mul h1).add ((hEm.sub measurable_const).mul h2)
  have hSm : Measurable S := by
    have h2 : Measurable fun ω => (x ω : ℂ) := Complex.measurable_ofReal.comp hxm
    exact (hEm.sub measurable_const).add h2
  -- elementary pointwise facts
  have hEnorm : ∀ ω, ‖E ω‖ = 1 := fun ω => Complex.norm_exp_ofReal_mul_I _
  have hE1 : ∀ ω, ‖E ω - 1‖ ≤ |u| * |Z ω| := by
    intro ω
    have := norm_cexp_ofReal_mul_I_sub_one_le (u * Z ω)
    rwa [abs_mul] at this
  have hx0 : ∀ᵐ ω ∂P, 0 ≤ x ω := by
    filter_upwards [hD0] with ω hω
    simp only [hx]
    positivity
  have hxL : ∀ᵐ ω ∂P, x ω ≤ L := by
    filter_upwards [hDK] with ω hω
    simp only [hx, hL]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hω (sq_nonneg u)) (by norm_num)
  -- the pointwise bound on `R`
  set bR : Ω → ℝ := fun ω => Real.exp L * (u ^ 4 / 4) * D ω ^ 2
    + u ^ 2 / 2 * (η / 2 * u ^ 2 * Z ω ^ 2 + η⁻¹ / 2 * D ω ^ 2) with hbR
  have hbRint : Integrable bR P :=
    (hD2.const_mul _).add (((hZ2.const_mul _).add (hD2.const_mul _)).const_mul _)
  have hRbound : ∀ᵐ ω ∂P, ‖R ω‖ ≤ bR ω := by
    filter_upwards [hx0, hxL, hD0] with ω hω0 hωL hωD
    have hrem : ‖((Real.exp (x ω) - 1 - x ω : ℝ) : ℂ)‖ ≤ Real.exp L * x ω ^ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (exp_sub_one_sub_self_nonneg _)]
      exact exp_sub_one_sub_self_le hω0 hωL
    have hxabs : ‖(x ω : ℂ)‖ = x ω := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hω0]
    have hxsq : x ω ^ 2 = u ^ 4 / 4 * D ω ^ 2 := by
      simp only [hx]
      ring
    have hcross : ‖E ω - 1‖ * ‖(x ω : ℂ)‖
        ≤ u ^ 2 / 2 * (η / 2 * u ^ 2 * Z ω ^ 2 + η⁻¹ / 2 * D ω ^ 2) := by
      rw [hxabs]
      have h1 : ‖E ω - 1‖ * x ω ≤ (|u| * |Z ω|) * x ω :=
        mul_le_mul_of_nonneg_right (hE1 ω) hω0
      have h2 : (|u| * |Z ω|) * x ω = u ^ 2 / 2 * ((|u| * |Z ω|) * D ω) := by
        simp only [hx]
        ring
      have h3 : (|u| * |Z ω|) * D ω
          ≤ η / 2 * (|u| * |Z ω|) ^ 2 + η⁻¹ / 2 * D ω ^ 2 := mul_le_half_add _ _ η hη
      have h4 : (|u| * |Z ω|) ^ 2 = u ^ 2 * Z ω ^ 2 := by
        rw [mul_pow, sq_abs, sq_abs]
      rw [h4] at h3
      have h5 : u ^ 2 / 2 * ((|u| * |Z ω|) * D ω)
          ≤ u ^ 2 / 2 * (η / 2 * (u ^ 2 * Z ω ^ 2) + η⁻¹ / 2 * D ω ^ 2) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      have h6 : u ^ 2 / 2 * (η / 2 * (u ^ 2 * Z ω ^ 2) + η⁻¹ / 2 * D ω ^ 2)
          = u ^ 2 / 2 * (η / 2 * u ^ 2 * Z ω ^ 2 + η⁻¹ / 2 * D ω ^ 2) := by ring
      linarith [h1, h2, h5, h6]
    calc ‖R ω‖ ≤ ‖E ω * ((Real.exp (x ω) - 1 - x ω : ℝ) : ℂ)‖ + ‖(E ω - 1) * (x ω : ℂ)‖ :=
          norm_add_le _ _
      _ = ‖((Real.exp (x ω) - 1 - x ω : ℝ) : ℂ)‖ + ‖E ω - 1‖ * ‖(x ω : ℂ)‖ := by
          rw [norm_mul, norm_mul, hEnorm, one_mul]
      _ ≤ Real.exp L * x ω ^ 2
          + u ^ 2 / 2 * (η / 2 * u ^ 2 * Z ω ^ 2 + η⁻¹ / 2 * D ω ^ 2) := add_le_add hrem hcross
      _ = bR ω := by
          simp only [hbR, hxsq]
          ring
  -- integrability of the two pieces
  have hGR : Integrable (fun ω => G ω * R ω) P := by
    refine Integrable.mono' (hbRint.const_mul c)
      (hGΩ.aestronglyMeasurable.mul hRm.aestronglyMeasurable) ?_
    filter_upwards [hGc, hRbound] with ω h1 h2
    rw [norm_mul]
    exact mul_le_mul h1 h2 (norm_nonneg _) hc0
  have hSbound : ∀ ω, ‖S ω‖ ≤ 2 + u ^ 2 / 2 * |D ω| := by
    intro ω
    calc ‖S ω‖ ≤ ‖E ω - 1‖ + ‖(x ω : ℂ)‖ := norm_add_le _ _
      _ ≤ (‖E ω‖ + ‖(1 : ℂ)‖) + ‖(x ω : ℂ)‖ := add_le_add (norm_sub_le _ _) le_rfl
      _ = 2 + u ^ 2 / 2 * |D ω| := by
          rw [hEnorm, norm_one, Complex.norm_real, Real.norm_eq_abs]
          simp only [hx]
          rw [show u ^ 2 * D ω / 2 = u ^ 2 / 2 * D ω by ring, abs_mul,
            abs_of_nonneg (by positivity : (0 : ℝ) ≤ u ^ 2 / 2)]
          norm_num
  have hSint : Integrable S P := by
    refine Integrable.mono' ((integrable_const (2 : ℝ)).add (hD1.abs.const_mul _))
      hSm.aestronglyMeasurable (Eventually.of_forall hSbound)
  have hGS : Integrable (fun ω => G ω * S ω) P := hSint.bdd_mul hGΩ.aestronglyMeasurable hGc
  -- splitting the integral
  have hsplit : (∫ ω, G ω * (Complex.exp ((u * Z ω : ℝ) * Complex.I)
      * ((Real.exp (u ^ 2 * D ω / 2) : ℝ) : ℂ) - 1) ∂P)
      = (∫ ω, G ω * S ω ∂P) + ∫ ω, G ω * R ω ∂P := by
    rw [← integral_add hGS hGR]
    exact integral_congr_ae (Eventually.of_forall hdecomp)
  -- the bound on the `R` piece
  have hZ2int : (∫ ω, Z ω ^ 2 ∂P) = ∫ ω, D ω ∂P := by
    calc (∫ ω, Z ω ^ 2 ∂P) = ∫ ω, (P[fun ω => Z ω ^ 2 | m.1]) ω ∂P :=
          (integral_condExp m.2).symm
      _ = ∫ ω, (P[D | m.1]) ω ∂P := integral_congr_ae hvar
      _ = ∫ ω, D ω ∂P := integral_condExp m.2
  have hbRint_eq : (∫ ω, bR ω ∂P) = Real.exp L * (u ^ 4 / 4) * (∫ ω, D ω ^ 2 ∂P)
      + u ^ 2 / 2 * (η / 2 * u ^ 2 * (∫ ω, D ω ∂P) + η⁻¹ / 2 * ∫ ω, D ω ^ 2 ∂P) := by
    have e1 : (∫ ω, bR ω ∂P) = (∫ ω, Real.exp L * (u ^ 4 / 4) * D ω ^ 2 ∂P)
        + ∫ ω, u ^ 2 / 2 * (η / 2 * u ^ 2 * Z ω ^ 2 + η⁻¹ / 2 * D ω ^ 2) ∂P :=
      integral_add (hD2.const_mul _) (((hZ2.const_mul _).add (hD2.const_mul _)).const_mul _)
    have e2 : (∫ ω, u ^ 2 / 2 * (η / 2 * u ^ 2 * Z ω ^ 2 + η⁻¹ / 2 * D ω ^ 2) ∂P)
        = u ^ 2 / 2 * ∫ ω, (η / 2 * u ^ 2 * Z ω ^ 2 + η⁻¹ / 2 * D ω ^ 2) ∂P :=
      integral_const_mul _ _
    have e3 : (∫ ω, (η / 2 * u ^ 2 * Z ω ^ 2 + η⁻¹ / 2 * D ω ^ 2) ∂P)
        = (∫ ω, η / 2 * u ^ 2 * Z ω ^ 2 ∂P) + ∫ ω, η⁻¹ / 2 * D ω ^ 2 ∂P :=
      integral_add (hZ2.const_mul _) (hD2.const_mul _)
    rw [e1, e2, e3, integral_const_mul, integral_const_mul, integral_const_mul, hZ2int]
  have hRint : ‖∫ ω, G ω * R ω ∂P‖
      ≤ c * (Real.exp L * (u ^ 4 / 4) * (∫ ω, D ω ^ 2 ∂P)
          + u ^ 2 / 2 * (η / 2 * u ^ 2 * (∫ ω, D ω ∂P) + η⁻¹ / 2 * ∫ ω, D ω ^ 2 ∂P)) := by
    calc ‖∫ ω, G ω * R ω ∂P‖ ≤ ∫ ω, ‖G ω * R ω‖ ∂P := norm_integral_le_integral_norm _
      _ ≤ ∫ ω, c * bR ω ∂P := by
          refine integral_mono_ae hGR.norm (hbRint.const_mul c) ?_
          filter_upwards [hGc, hRbound] with ω h1 h2
          rw [norm_mul]
          exact mul_le_mul h1 h2 (norm_nonneg _) hc0
      _ = c * ∫ ω, bR ω ∂P := integral_const_mul _ _
      _ = c * (Real.exp L * (u ^ 4 / 4) * (∫ ω, D ω ^ 2 ∂P)
          + u ^ 2 / 2 * (η / 2 * u ^ 2 * (∫ ω, D ω ∂P) + η⁻¹ / 2 * ∫ ω, D ω ^ 2 ∂P)) := by
          rw [hbRint_eq]
  -- the bound on the `S` piece: pull out `G`, then the conditional Taylor estimate
  have hxint : Integrable x P := (hD1.const_mul _).div_const _
  have hcondS : P[S | m.1] =ᵐ[P] fun ω =>
      (P[E | m.1]) ω - 1 + ((u ^ 2 / 2 * (P[D | m.1]) ω : ℝ) : ℂ) := by
    have hEint : Integrable E P :=
      Integrable.of_bound hEm.aestronglyMeasurable 1 (Eventually.of_forall fun ω => (hEnorm ω).le)
    have hcint : Integrable (fun _ : Ω => (-1 : ℂ)) P := integrable_const _
    have hxc : Integrable (Complex.ofRealCLM ∘ x) P := Complex.ofRealCLM.integrable_comp hxint
    have hSeq : S = fun ω => (E ω + (-1 : ℂ)) + (Complex.ofRealCLM ∘ x) ω := by
      funext ω
      simp only [hS, Function.comp_apply, Complex.ofRealCLM_apply]
      ring
    have s1 : P[S | m.1] =ᵐ[P] P[fun ω => E ω + (-1 : ℂ) | m.1] + P[Complex.ofRealCLM ∘ x | m.1] := by
      rw [hSeq]
      exact condExp_add (hEint.add hcint) hxc m.1
    have s2 : P[fun ω => E ω + (-1 : ℂ) | m.1] =ᵐ[P] P[E | m.1] + P[fun _ : Ω => (-1 : ℂ) | m.1] :=
      condExp_add hEint hcint m.1
    have s3 : P[fun _ : Ω => (-1 : ℂ) | m.1] = fun _ => (-1 : ℂ) := condExp_const m.2 _
    have s4 : P[Complex.ofRealCLM ∘ x | m.1] =ᵐ[P] Complex.ofRealCLM ∘ P[x | m.1] :=
      (Complex.ofRealCLM.comp_condExp_comm hxint).symm
    have s5 : P[x | m.1] =ᵐ[P] fun ω => u ^ 2 / 2 * (P[D | m.1]) ω := by
      have hxeq : x = fun ω => u ^ 2 / 2 * D ω := by
        funext ω
        simp only [hx]
        ring
      rw [hxeq]
      exact condExp_smul (μ := P) (m := m.1) (u ^ 2 / 2) D
    filter_upwards [s1, s2, s4, s5] with ω h1 h2 h4 h5
    simp only [Pi.add_apply] at h1 h2
    rw [h1, h2, s3, h4, Function.comp_apply, h5, Complex.ofRealCLM_apply]
    ring
  have htaylor := norm_condExp_cexp_sub_quadratic_taylor_le (P := P) m hZm hZ1 hZ2 hmean hvar
    hδ huδ
  have hSae : ∀ᵐ ω ∂P, ‖(P[S | m.1]) ω‖
      ≤ 2 / 9 * |u| ^ 3 * δ * (P[D | m.1]) ω
        + 4 * u ^ 2 * (P[fun ω => Set.indicator {ω | δ < |Z ω|} (fun ω => Z ω ^ 2) ω | m.1]) ω := by
    filter_upwards [hcondS, htaylor] with ω h1 h2
    rw [h1]
    have heq : (P[E | m.1]) ω - 1 + ((u ^ 2 / 2 * (P[D | m.1]) ω : ℝ) : ℂ)
        = (P[E | m.1]) ω - (1 - ((u ^ 2 / 2 * (P[D | m.1]) ω : ℝ) : ℂ)) := by ring
    rw [heq]
    exact h2
  have hSint' : ‖∫ ω, G ω * S ω ∂P‖
      ≤ c * (2 / 9 * |u| ^ 3 * δ * (∫ ω, D ω ∂P)
          + 4 * u ^ 2 * ∫ ω, Set.indicator {ω | δ < |Z ω|} (fun ω => Z ω ^ 2) ω ∂P) := by
    refine (norm_integral_mul_le_mul_integral_norm_condExp m hG hGc hSint).trans ?_
    refine mul_le_mul_of_nonneg_left ?_ hc0
    have hindmeas : MeasurableSet {ω | δ < |Z ω|} :=
      measurableSet_lt measurable_const (continuous_abs.measurable.comp hZm)
    have hindint : Integrable (fun ω => Set.indicator {ω | δ < |Z ω|} (fun ω => Z ω ^ 2) ω) P :=
      hZ2.indicator hindmeas
    calc (∫ ω, ‖(P[S | m.1]) ω‖ ∂P)
        ≤ ∫ ω, (2 / 9 * |u| ^ 3 * δ * (P[D | m.1]) ω
            + 4 * u ^ 2 * (P[fun ω => Set.indicator {ω | δ < |Z ω|} (fun ω => Z ω ^ 2) ω
              | m.1]) ω) ∂P :=
          integral_mono_ae integrable_condExp.norm
            ((integrable_condExp.const_mul _).add (integrable_condExp.const_mul _)) hSae
      _ = 2 / 9 * |u| ^ 3 * δ * (∫ ω, D ω ∂P)
          + 4 * u ^ 2 * ∫ ω, Set.indicator {ω | δ < |Z ω|} (fun ω => Z ω ^ 2) ω ∂P := by
          rw [integral_add (integrable_condExp.const_mul _) (integrable_condExp.const_mul _),
            integral_const_mul, integral_const_mul, integral_condExp m.2, integral_condExp m.2]
  -- combine
  rw [hsplit]
  calc ‖(∫ ω, G ω * S ω ∂P) + ∫ ω, G ω * R ω ∂P‖
      ≤ ‖∫ ω, G ω * S ω ∂P‖ + ‖∫ ω, G ω * R ω ∂P‖ := norm_add_le _ _
    _ ≤ c * (2 / 9 * |u| ^ 3 * δ * (∫ ω, D ω ∂P)
          + 4 * u ^ 2 * ∫ ω, Set.indicator {ω | δ < |Z ω|} (fun ω => Z ω ^ 2) ω ∂P)
        + c * (Real.exp L * (u ^ 4 / 4) * (∫ ω, D ω ^ 2 ∂P)
          + u ^ 2 / 2 * (η / 2 * u ^ 2 * (∫ ω, D ω ∂P) + η⁻¹ / 2 * ∫ ω, D ω ^ 2 ∂P)) :=
        add_le_add hSint' hRint
    _ = c * (Real.exp (u ^ 2 * K / 2) * (u ^ 4 / 4) * (∫ ω, D ω ^ 2 ∂P)
          + u ^ 2 / 2 * (η / 2 * u ^ 2 * (∫ ω, D ω ∂P) + η⁻¹ / 2 * ∫ ω, D ω ^ 2 ∂P)
          + 2 / 9 * |u| ^ 3 * δ * (∫ ω, D ω ∂P)
          + 4 * u ^ 2 * ∫ ω, Set.indicator {ω | δ < |Z ω|} (fun ω => Z ω ^ 2) ω ∂P) := by
        simp only [hL]
        ring

/-! ## The telescoping -/

/-- The one-step error of the compensated telescoping at bracket level `K`. -/
noncomputable def stepError (P : Measure Ω) (Z D : Ω → ℝ) (u δ η K : ℝ) : ℝ :=
  Real.exp (u ^ 2 * K / 2) * (Real.exp (u ^ 2 * K / 2) * (u ^ 4 / 4) * (∫ ω, D ω ^ 2 ∂P)
    + u ^ 2 / 2 * (η / 2 * u ^ 2 * (∫ ω, D ω ∂P) + η⁻¹ / 2 * ∫ ω, D ω ^ 2 ∂P)
    + 2 / 9 * |u| ^ 3 * δ * (∫ ω, D ω ∂P)
    + 4 * u ^ 2 * ∫ ω, Set.indicator {ω | δ < |Z ω|} (fun ω => Z ω ^ 2) ω ∂P)

/-- **Compensated telescoping with a random bracket.**  Let `Z k` be increments adapted to
`F`, with vanishing conditional means and conditional second moments `P[D k | F k]` for
nonnegative adapted bracket increments `D k` whose sum over `k < N` is at most `K`.  Then
for every `F 0`-measurable test function `W` bounded by one,

  `‖E[W e^{iu ∑_{k<N} Z_k} e^{u² ∑_{k<N} D_k / 2}] - E[W]‖ ≤ ∑_{i<N} stepError i`.

The compensator is the past-measurable exponential of the accumulated bracket; no
conditional variance is ever pulled out of a conditional expectation. -/
theorem norm_integral_test_mul_cexp_mul_exp_sub_le [IsProbabilityMeasure P]
    {F : ℕ → MeasurableSpace Ω} (hFle : ∀ n, F n ≤ mΩ) (hFmono : Monotone F)
    {Z D : ℕ → Ω → ℝ} (hZadapt : ∀ n, Measurable[F (n + 1)] (Z n))
    (hDadapt : ∀ n, Measurable[F (n + 1)] (D n))
    (hZ1 : ∀ n, Integrable (Z n) P) (hZ2 : ∀ n, Integrable (fun ω => Z n ω ^ 2) P)
    (hD1 : ∀ n, Integrable (D n) P) (hD2 : ∀ n, Integrable (fun ω => D n ω ^ 2) P)
    (hD0 : ∀ n, ∀ᵐ ω ∂P, 0 ≤ D n ω)
    (hmean : ∀ n, P[Z n | F n] =ᵐ[P] 0)
    (hvar : ∀ n, P[fun ω => Z n ω ^ 2 | F n] =ᵐ[P] P[D n | F n])
    {W : Ω → ℂ} (hWmeas : StronglyMeasurable[F 0] W) (hWbdd : ∀ ω, ‖W ω‖ ≤ 1)
    {u δ η K : ℝ} (hδ : 0 ≤ δ) (huδ : |u| * δ ≤ 1) (hη : 0 < η)
    (N : ℕ) (hDK : ∀ᵐ ω ∂P, ∑ k ∈ Finset.range N, D k ω ≤ K) :
    ‖(∫ ω, W ω * Complex.exp ((u * ∑ k ∈ Finset.range N, Z k ω : ℝ) * Complex.I)
          * ((Real.exp (u ^ 2 * (∑ k ∈ Finset.range N, D k ω) / 2) : ℝ) : ℂ) ∂P)
        - ∫ ω, W ω ∂P‖
      ≤ ∑ i ∈ Finset.range N, stepError P (Z i) (D i) u δ η K := by
  classical
  have hD0' : ∀ᵐ ω ∂P, ∀ n, 0 ≤ D n ω := ae_all_iff.2 hD0
  -- the compensated process
  set G : ℕ → Ω → ℂ := fun n ω => W ω * Complex.exp ((u * ∑ k ∈ Finset.range n, Z k ω : ℝ)
    * Complex.I) * ((Real.exp (u ^ 2 * (∑ k ∈ Finset.range n, D k ω) / 2) : ℝ) : ℂ) with hGdef
  have hGmeas : ∀ n, StronglyMeasurable[F n] (G n) := by
    intro n
    have hSZ : Measurable[F n] (fun ω => ∑ k ∈ Finset.range n, Z k ω) :=
      measurable_range_sum_of_adapted hFmono hZadapt n
    have hSD : Measurable[F n] (fun ω => ∑ k ∈ Finset.range n, D k ω) :=
      measurable_range_sum_of_adapted hFmono hDadapt n
    have h1 : StronglyMeasurable[F n] (fun ω => Complex.exp
        ((u * ∑ k ∈ Finset.range n, Z k ω : ℝ) * Complex.I)) :=
      Complex.continuous_exp.comp_stronglyMeasurable
        ((Complex.continuous_ofReal.comp_stronglyMeasurable
          (hSZ.const_mul u).stronglyMeasurable).mul_const _)
    have h2 : StronglyMeasurable[F n] (fun ω =>
        ((Real.exp (u ^ 2 * (∑ k ∈ Finset.range n, D k ω) / 2) : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp_stronglyMeasurable
        (Real.continuous_exp.comp_stronglyMeasurable
          ((hSD.const_mul _).div_const _).stronglyMeasurable)
    exact ((hWmeas.mono (hFmono (Nat.zero_le n))).mul h1).mul h2
  have hGbdd : ∀ n, (∀ᵐ ω ∂P, ∑ k ∈ Finset.range n, D k ω ≤ K) →
      ∀ᵐ ω ∂P, ‖G n ω‖ ≤ Real.exp (u ^ 2 * K / 2) := by
    intro n hn
    filter_upwards [hn] with ω hω
    simp only [hGdef]
    rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_eq_abs, Real.abs_exp]
    calc ‖W ω‖ * Real.exp (u ^ 2 * (∑ k ∈ Finset.range n, D k ω) / 2)
        ≤ 1 * Real.exp (u ^ 2 * K / 2) := by
          refine mul_le_mul (hWbdd ω) (Real.exp_le_exp.2 ?_) (Real.exp_pos _).le zero_le_one
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hω (sq_nonneg u))
            (by norm_num)
      _ = Real.exp (u ^ 2 * K / 2) := one_mul _
  have hGint : ∀ n, (∀ᵐ ω ∂P, ∑ k ∈ Finset.range n, D k ω ≤ K) → Integrable (G n) P :=
    fun n hn => Integrable.of_bound ((hGmeas n).mono (hFle n)).aestronglyMeasurable _ (hGbdd n hn)
  have hG0 : G 0 = W := by
    funext ω
    simp [hGdef]
  -- the goal in terms of `G`
  show ‖(∫ ω, G N ω ∂P) - ∫ ω, W ω ∂P‖ ≤ ∑ i ∈ Finset.range N, stepError P (Z i) (D i) u δ η K
  revert hDK
  induction N with
  | zero =>
    intro _
    simp [hG0]
  | succ n ih =>
    intro hDK
    have hDKn : ∀ᵐ ω ∂P, ∑ k ∈ Finset.range n, D k ω ≤ K := by
      filter_upwards [hDK, hD0 n] with ω h1 h2
      rw [Finset.sum_range_succ] at h1
      linarith
    have hDn : ∀ᵐ ω ∂P, D n ω ≤ K := by
      filter_upwards [hDK, hD0'] with ω h1 h2
      have hle : D n ω ≤ ∑ k ∈ Finset.range (n + 1), D k ω :=
        Finset.single_le_sum (fun k _ => h2 k) (Finset.self_mem_range_succ n)
      linarith
    have hih := ih hDKn
    -- one step
    have hstepEq : (∫ ω, G (n + 1) ω ∂P) - ∫ ω, G n ω ∂P
        = ∫ ω, G n ω * (Complex.exp ((u * Z n ω : ℝ) * Complex.I)
            * ((Real.exp (u ^ 2 * D n ω / 2) : ℝ) : ℂ) - 1) ∂P := by
      rw [← integral_sub (hGint (n + 1) hDK) (hGint n hDKn)]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only [hGdef]
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      have e1 : Complex.exp ((u * (∑ k ∈ Finset.range n, Z k ω + Z n ω) : ℝ) * Complex.I)
          = Complex.exp ((u * ∑ k ∈ Finset.range n, Z k ω : ℝ) * Complex.I)
            * Complex.exp ((u * Z n ω : ℝ) * Complex.I) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      have e2 : Real.exp (u ^ 2 * (∑ k ∈ Finset.range n, D k ω + D n ω) / 2)
          = Real.exp (u ^ 2 * (∑ k ∈ Finset.range n, D k ω) / 2) * Real.exp (u ^ 2 * D n ω / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [e1, e2]
      push_cast
      ring
    have hstep := norm_integral_mul_step_le (P := P) ⟨F n, hFle n⟩ (hGmeas n)
      (Real.exp_pos _).le (hGbdd n hDKn)
      ((hZadapt n).mono (hFle (n + 1)) le_rfl) (hZ1 n) (hZ2 n)
      ((hDadapt n).mono (hFle (n + 1)) le_rfl) (hD1 n) (hD2 n) (hD0 n) hDn (hmean n) (hvar n)
      hδ huδ hη
    rw [← hstepEq] at hstep
    rw [Finset.sum_range_succ]
    calc ‖(∫ ω, G (n + 1) ω ∂P) - ∫ ω, W ω ∂P‖
        = ‖((∫ ω, G (n + 1) ω ∂P) - ∫ ω, G n ω ∂P) + ((∫ ω, G n ω ∂P) - ∫ ω, W ω ∂P)‖ := by
          congr 1
          ring
      _ ≤ ‖(∫ ω, G (n + 1) ω ∂P) - ∫ ω, G n ω ∂P‖ + ‖(∫ ω, G n ω ∂P) - ∫ ω, W ω ∂P‖ :=
          norm_add_le _ _
      _ ≤ stepError P (Z n) (D n) u δ η K
          + ∑ i ∈ Finset.range n, stepError P (Z i) (D i) u δ η K := add_le_add hstep hih
      _ = ∑ i ∈ Finset.range n, stepError P (Z i) (D i) u δ η K
          + stepError P (Z n) (D n) u δ η K := add_comm _ _

/-- **Aggregated form of the telescoping bound.**  With `Q = ∑_{i<N} E[D_i²]` the quadratic
oscillation of the bracket and `Lind` the Lindeberg sum at level `δ`, and using
`∑_{i<N} E[D_i] = E[∑ D_i] ≤ K`, the total error is

  `e^{u²K/2} · ( e^{u²K/2} u⁴ Q / 4 + (u²/2)(η u² K / 2 + Q / (2η)) + (2/9)|u|³ δ K + 4 u² Lind )`. -/
theorem norm_integral_test_mul_cexp_mul_exp_sub_le' [IsProbabilityMeasure P]
    {F : ℕ → MeasurableSpace Ω} (hFle : ∀ n, F n ≤ mΩ) (hFmono : Monotone F)
    {Z D : ℕ → Ω → ℝ} (hZadapt : ∀ n, Measurable[F (n + 1)] (Z n))
    (hDadapt : ∀ n, Measurable[F (n + 1)] (D n))
    (hZ1 : ∀ n, Integrable (Z n) P) (hZ2 : ∀ n, Integrable (fun ω => Z n ω ^ 2) P)
    (hD1 : ∀ n, Integrable (D n) P) (hD2 : ∀ n, Integrable (fun ω => D n ω ^ 2) P)
    (hD0 : ∀ n, ∀ᵐ ω ∂P, 0 ≤ D n ω)
    (hmean : ∀ n, P[Z n | F n] =ᵐ[P] 0)
    (hvar : ∀ n, P[fun ω => Z n ω ^ 2 | F n] =ᵐ[P] P[D n | F n])
    {W : Ω → ℂ} (hWmeas : StronglyMeasurable[F 0] W) (hWbdd : ∀ ω, ‖W ω‖ ≤ 1)
    {u δ η K : ℝ} (hδ : 0 ≤ δ) (huδ : |u| * δ ≤ 1) (hη : 0 < η)
    (N : ℕ) (hDK : ∀ᵐ ω ∂P, ∑ k ∈ Finset.range N, D k ω ≤ K) :
    ‖(∫ ω, W ω * Complex.exp ((u * ∑ k ∈ Finset.range N, Z k ω : ℝ) * Complex.I)
          * ((Real.exp (u ^ 2 * (∑ k ∈ Finset.range N, D k ω) / 2) : ℝ) : ℂ) ∂P)
        - ∫ ω, W ω ∂P‖
      ≤ Real.exp (u ^ 2 * K / 2) * (Real.exp (u ^ 2 * K / 2) * (u ^ 4 / 4)
            * (∑ i ∈ Finset.range N, ∫ ω, D i ω ^ 2 ∂P)
          + u ^ 2 / 2 * (η / 2 * u ^ 2 * K
            + η⁻¹ / 2 * ∑ i ∈ Finset.range N, ∫ ω, D i ω ^ 2 ∂P)
          + 2 / 9 * |u| ^ 3 * δ * K
          + 4 * u ^ 2 * ∑ i ∈ Finset.range N,
              ∫ ω, Set.indicator {ω | δ < |Z i ω|} (fun ω => Z i ω ^ 2) ω ∂P) := by
  classical
  refine (norm_integral_test_mul_cexp_mul_exp_sub_le hFle hFmono hZadapt hDadapt hZ1 hZ2 hD1 hD2
    hD0 hmean hvar hWmeas hWbdd hδ huδ hη N hDK).trans ?_
  -- the bracket increments sum to at most `K`
  have hsumD : (∑ i ∈ Finset.range N, ∫ ω, D i ω ∂P) ≤ K := by
    rw [← integral_finsetSum _ fun i _ => hD1 i]
    calc (∫ ω, ∑ i ∈ Finset.range N, D i ω ∂P) ≤ ∫ _ω, K ∂P :=
          integral_mono_ae (integrable_finsetSum _ fun i _ => hD1 i) (integrable_const K) hDK
      _ = K := by simp
  have hexp : (0 : ℝ) ≤ Real.exp (u ^ 2 * K / 2) := (Real.exp_pos _).le
  have hsum : ∑ i ∈ Finset.range N, stepError P (Z i) (D i) u δ η K
      = Real.exp (u ^ 2 * K / 2) * (Real.exp (u ^ 2 * K / 2) * (u ^ 4 / 4)
            * (∑ i ∈ Finset.range N, ∫ ω, D i ω ^ 2 ∂P)
          + u ^ 2 / 2 * (η / 2 * u ^ 2 * (∑ i ∈ Finset.range N, ∫ ω, D i ω ∂P)
            + η⁻¹ / 2 * ∑ i ∈ Finset.range N, ∫ ω, D i ω ^ 2 ∂P)
          + 2 / 9 * |u| ^ 3 * δ * (∑ i ∈ Finset.range N, ∫ ω, D i ω ∂P)
          + 4 * u ^ 2 * ∑ i ∈ Finset.range N,
              ∫ ω, Set.indicator {ω | δ < |Z i ω|} (fun ω => Z i ω ^ 2) ω ∂P) := by
    simp only [stepError, mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  rw [hsum]
  refine mul_le_mul_of_nonneg_left ?_ hexp
  have h1 : u ^ 2 / 2 * (η / 2 * u ^ 2 * (∑ i ∈ Finset.range N, ∫ ω, D i ω ∂P))
      ≤ u ^ 2 / 2 * (η / 2 * u ^ 2 * K) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsumD (by positivity)) (by positivity)
  have h2 : 2 / 9 * |u| ^ 3 * δ * (∑ i ∈ Finset.range N, ∫ ω, D i ω ∂P)
      ≤ 2 / 9 * |u| ^ 3 * δ * K :=
    mul_le_mul_of_nonneg_left hsumD (by positivity)
  linarith [h1, h2]

end ReflectedGMS.ApproximateBracketCLT
