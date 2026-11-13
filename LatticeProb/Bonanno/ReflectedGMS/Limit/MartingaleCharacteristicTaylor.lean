/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.MartingaleCharacteristicTaylor at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen

/-!
# Conditional second-order Taylor estimate for martingale increments

The second-order remainder of the complex exponential is estimated pointwise on
the unit circle, and the estimate is transported through a conditional
expectation.  For an increment `Z` with vanishing conditional mean and
conditional second moment `V`, the conditional characteristic function differs
from `1 - u ^ 2 * V / 2` by at most a small-increment threshold times `V` plus a
conditional Lindeberg tail.

No Gaussianity, independence or fourth moment is assumed: the only probabilistic
inputs are the two conditional moment identities.  This is the one-step input of
the exponential-martingale identity, whose telescoping step is not proved here.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter

namespace ReflectedGMS.MartingaleLimit

/-- Second-order Taylor remainder of `exp (i x)` for a small real argument. -/
theorem norm_cexp_sub_quadratic_taylor_le_cube {x : ℝ} (hx : |x| ≤ 1) :
    ‖Complex.exp ((x : ℂ) * Complex.I) -
        (1 + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2)‖ ≤ 2 / 9 * |x| ^ 3 := by
  have hnx : ‖(x : ℂ) * Complex.I‖ = |x| := by simp
  have hI : ((x : ℂ) * Complex.I) ^ 2 = -(x : ℂ) ^ 2 := by
    rw [mul_pow, Complex.I_sq]
    ring
  have hsum : ∑ m ∈ Finset.range 3, ((x : ℂ) * Complex.I) ^ m / (m.factorial : ℂ)
      = 1 + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, hI]
    norm_num [Nat.factorial]
    try ring
  have h := Complex.exp_bound (x := (x : ℂ) * Complex.I) (by rw [hnx]; exact hx)
    (n := 3) (by norm_num)
  rw [hsum, hnx] at h
  refine h.trans (le_of_eq ?_)
  norm_num [Nat.factorial]
  try ring

/-- A quadratic bound on the same remainder, valid for every real argument. -/
theorem norm_cexp_sub_quadratic_taylor_le_sq (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) -
        (1 + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2)‖ ≤ 4 * x ^ 2 := by
  rcases le_or_gt |x| 1 with hx | hx
  · have h := norm_cexp_sub_quadratic_taylor_le_cube hx
    have h2 : |x| ^ 3 ≤ x ^ 2 := by
      calc |x| ^ 3 = |x| ^ 2 * |x| := by ring
        _ = x ^ 2 * |x| := by rw [sq_abs]
        _ ≤ x ^ 2 * 1 := mul_le_mul_of_nonneg_left hx (sq_nonneg _)
        _ = x ^ 2 := mul_one _
    nlinarith [h, h2, sq_nonneg x]
  · have he : ‖Complex.exp ((x : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I x
    have hb1 : ‖(1 : ℂ) + (x : ℂ) * Complex.I‖ ≤ 1 + |x| := by
      refine (norm_add_le _ _).trans ?_
      simp
    have hb2 : ‖((x : ℂ) ^ 2 / 2 : ℂ)‖ ≤ x ^ 2 / 2 := by
      simp [sq_abs]
    have hb : ‖(1 : ℂ) + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2‖ ≤ 1 + |x| + x ^ 2 / 2 :=
      (norm_sub_le _ _).trans (add_le_add hb1 hb2)
    have htri :
        ‖Complex.exp ((x : ℂ) * Complex.I) -
            (1 + (x : ℂ) * Complex.I - (x : ℂ) ^ 2 / 2)‖ ≤ 1 + (1 + |x| + x ^ 2 / 2) := by
      refine (norm_sub_le _ _).trans ?_
      rw [he]
      linarith [hb]
    have hax : |x| ^ 2 = x ^ 2 := sq_abs x
    have h1 : (1 : ℝ) < x ^ 2 := by nlinarith [hax, hx, abs_nonneg x]
    have h2 : |x| ≤ x ^ 2 := by nlinarith [hax, hx, abs_nonneg x]
    linarith [htri, h1, h2]

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- Conditional second-order Taylor estimate for a martingale increment.  If the
increment `Z` has vanishing conditional mean and conditional second moment `V`
given `G`, then its conditional characteristic function at `u` is `1 - u² V / 2`
up to a remainder controlled by the small-increment threshold `δ` times `V` and
by the conditional Lindeberg tail at level `δ`. -/
theorem norm_condExp_cexp_sub_quadratic_taylor_le
    [IsProbabilityMeasure P] (G : {q : MeasurableSpace Ω // q ≤ mΩ})
    {Z V : Ω → ℝ} (hZm : Measurable Z) (hZ1 : Integrable Z P)
    (hZ2 : Integrable (fun ω => Z ω ^ 2) P)
    (hmean : P[Z | G.1] =ᵐ[P] 0)
    (hvar : P[fun ω => Z ω ^ 2 | G.1] =ᵐ[P] V)
    {u δ : ℝ} (hδ : 0 ≤ δ) (huδ : |u| * δ ≤ 1) :
    ∀ᵐ ω ∂P,
      ‖P[fun ω => Complex.exp ((u * Z ω : ℝ) * Complex.I) | G.1] ω -
          (1 - ((u ^ 2 / 2 * V ω : ℝ) : ℂ))‖ ≤
        2 / 9 * |u| ^ 3 * δ * V ω +
          4 * u ^ 2 *
            P[fun ω => Set.indicator {ω | δ < |Z ω|} (fun ω => Z ω ^ 2) ω | G.1] ω := by
  classical
  set T3 : ℝ →L[ℝ] ℂ :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight (-((u : ℂ) * Complex.I)) with hT3
  set T4 : ℝ →L[ℝ] ℂ :=
    (ContinuousLinearMap.id ℝ ℝ).smulRight (((u ^ 2 / 2 : ℝ) : ℂ)) with hT4
  have hT3apply : ∀ y : ℝ, T3 y = (y : ℂ) * -((u : ℂ) * Complex.I) := by
    intro y
    simp [hT3, Complex.real_smul]
  have hT4apply : ∀ y : ℝ, T4 y = (y : ℂ) * ((u ^ 2 / 2 : ℝ) : ℂ) := by
    intro y
    simp [hT4, Complex.real_smul]
  have hAint : Integrable (fun ω => Complex.exp ((u * Z ω : ℝ) * Complex.I)) P := by
    refine Integrable.of_bound (by fun_prop) 1 (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Complex.norm_exp_ofReal_mul_I, le_refl]
  have hcint : Integrable (fun _ : Ω => (-1 : ℂ)) P := integrable_const _
  have h3int : Integrable (fun ω => T3 (Z ω)) P := T3.integrable_comp hZ1
  have h4int : Integrable (fun ω => T4 (Z ω ^ 2)) P := T4.integrable_comp hZ2
  have hmabs : Measurable fun ω => |Z ω| := by
    first
      | fun_prop
      | measurability
      | exact (Measurable.abs hZm)
  have hindmeas : MeasurableSet {ω | δ < |Z ω|} := measurableSet_lt measurable_const hmabs
  have hindint :
      Integrable (fun ω => Set.indicator {ω | δ < |Z ω|} (fun ω => Z ω ^ 2) ω) P :=
    hZ2.indicator hindmeas
  set fA : Ω → ℂ := fun ω => Complex.exp ((u * Z ω : ℝ) * Complex.I) with hfA
  set fc : Ω → ℂ := fun _ => (-1 : ℂ) with hfc
  set f3 : Ω → ℂ := fun ω => T3 (Z ω) with hf3
  set f4 : Ω → ℂ := fun ω => T4 (Z ω ^ 2) with hf4
  set ind : Ω → ℝ := fun ω => Set.indicator {ω | δ < |Z ω|} (fun ω => Z ω ^ 2) ω with hind
  set R : Ω → ℂ := fA + fc + f3 + f4 with hRdef
  set bd : Ω → ℝ := fun ω => 2 / 9 * |u| ^ 3 * δ * Z ω ^ 2 + 4 * u ^ 2 * ind ω with hbd
  have hRint : Integrable R P := ((hAint.add hcint).add h3int).add h4int
  -- conditional expectation of the linear part
  have hf3cond : P[f3 | G.1] =ᵐ[P] 0 := by
    have hcomp : f3 = T3 ∘ Z := rfl
    have h := T3.comp_condExp_comm (μ := P) (m := G.1) hZ1
    filter_upwards [h, hmean] with ω hω hm
    have h1 : P[f3 | G.1] ω = T3 (P[Z | G.1] ω) := by
      rw [hcomp]
      exact hω.symm
    rw [h1]
    simp only [Pi.zero_apply] at hm ⊢
    rw [hm, map_zero]
  have hf4cond : P[f4 | G.1] =ᵐ[P] fun ω => ((u ^ 2 / 2 * V ω : ℝ) : ℂ) := by
    have hcomp : f4 = T4 ∘ (fun ω => Z ω ^ 2) := rfl
    have h := T4.comp_condExp_comm (μ := P) (m := G.1) hZ2
    filter_upwards [h, hvar] with ω hω hv
    have h1 : P[f4 | G.1] ω = T4 (P[fun ω => Z ω ^ 2 | G.1] ω) := by
      rw [hcomp]
      exact hω.symm
    rw [h1, hv, hT4apply]
    push_cast
    ring
  have hRcond : P[R | G.1] =ᵐ[P] fun ω =>
      P[fA | G.1] ω - 1 + ((u ^ 2 / 2 * V ω : ℝ) : ℂ) := by
    have s1 : P[R | G.1] =ᵐ[P] P[fA + fc + f3 | G.1] + P[f4 | G.1] :=
      condExp_add ((hAint.add hcint).add h3int) h4int G.1
    have s2 : P[fA + fc + f3 | G.1] =ᵐ[P] P[fA + fc | G.1] + P[f3 | G.1] :=
      condExp_add (hAint.add hcint) h3int G.1
    have s3 : P[fA + fc | G.1] =ᵐ[P] P[fA | G.1] + P[fc | G.1] := condExp_add hAint hcint G.1
    have s4 : P[fc | G.1] = fun _ => (-1 : ℂ) := by
      rw [hfc]
      exact condExp_const G.2 _
    filter_upwards [s1, s2, s3, hf3cond, hf4cond] with ω t1 t2 t3 t4 t5
    simp only [Pi.add_apply] at t1 t2 t3
    rw [t1, t2, t3, t4, t5, s4]
    simp only [Pi.zero_apply]
    ring
  -- pointwise remainder bound
  have hbound : ∀ ω, ‖R ω‖ ≤ bd ω := by
    intro ω
    have hRω : R ω = Complex.exp (((u * Z ω : ℝ) : ℂ) * Complex.I) -
        (1 + ((u * Z ω : ℝ) : ℂ) * Complex.I - ((u * Z ω : ℝ) : ℂ) ^ 2 / 2) := by
      simp only [hRdef, hfA, hfc, hf3, hf4, Pi.add_apply, hT3apply, hT4apply]
      push_cast
      ring
    rw [hRω]
    rcases le_or_gt |Z ω| δ with hsmall | hlarge
    · have hx : |u * Z ω| ≤ 1 := by
        rw [abs_mul]
        calc |u| * |Z ω| ≤ |u| * δ := mul_le_mul_of_nonneg_left hsmall (abs_nonneg u)
          _ ≤ 1 := huδ
      have hcube := norm_cexp_sub_quadratic_taylor_le_cube hx
      have hindnn : 0 ≤ ind ω := by
        simp only [hind]
        exact Set.indicator_nonneg (fun a _ => sq_nonneg (Z a)) ω
      have hind0 : 0 ≤ 4 * u ^ 2 * ind ω := mul_nonneg (by positivity) hindnn
      have h3 : |u * Z ω| ^ 3 = |u| ^ 3 * |Z ω| ^ 3 := by rw [abs_mul, mul_pow]
      have h4 : |Z ω| ^ 3 ≤ δ * Z ω ^ 2 := by
        calc |Z ω| ^ 3 = |Z ω| ^ 2 * |Z ω| := by ring
          _ = Z ω ^ 2 * |Z ω| := by rw [sq_abs]
          _ ≤ Z ω ^ 2 * δ := mul_le_mul_of_nonneg_left hsmall (sq_nonneg _)
          _ = δ * Z ω ^ 2 := mul_comm _ _
      have h5 : 2 / 9 * |u * Z ω| ^ 3 ≤ 2 / 9 * |u| ^ 3 * δ * Z ω ^ 2 := by
        rw [h3]
        nlinarith [h4, pow_nonneg (abs_nonneg u) 3]
      simp only [hbd]
      linarith [hcube, h5, hind0]
    · have hmem : ω ∈ {ω | δ < |Z ω|} := hlarge
      have hindeq : ind ω = Z ω ^ 2 := by
        simp only [hind]
        exact Set.indicator_of_mem hmem (fun a => Z a ^ 2)
      have hsq := norm_cexp_sub_quadratic_taylor_le_sq (u * Z ω)
      have h1 : 4 * (u * Z ω) ^ 2 = 4 * u ^ 2 * Z ω ^ 2 := by ring
      have hu3 : (0 : ℝ) ≤ 2 / 9 * |u| ^ 3 := by positivity
      have h0 : 0 ≤ 2 / 9 * |u| ^ 3 * δ * Z ω ^ 2 :=
        mul_nonneg (mul_nonneg hu3 hδ) (sq_nonneg _)
      simp only [hbd, hindeq]
      linarith [hsq, h0, h1]
  -- conditional expectation of the bound
  have hbdint : Integrable bd P := (hZ2.const_mul _).add (hindint.const_mul _)
  have hbdcond : P[bd | G.1] =ᵐ[P] fun ω =>
      2 / 9 * |u| ^ 3 * δ * V ω + 4 * u ^ 2 * P[ind | G.1] ω := by
    have e1 : P[bd | G.1] =ᵐ[P]
        P[fun ω => 2 / 9 * |u| ^ 3 * δ * Z ω ^ 2 | G.1] + P[fun ω => 4 * u ^ 2 * ind ω | G.1] :=
      condExp_add (hZ2.const_mul _) (hindint.const_mul _) G.1
    have e2 : P[fun ω => 2 / 9 * |u| ^ 3 * δ * Z ω ^ 2 | G.1] =ᵐ[P]
        fun ω => 2 / 9 * |u| ^ 3 * δ * P[fun ω => Z ω ^ 2 | G.1] ω :=
      condExp_smul (μ := P) (m := G.1) (2 / 9 * |u| ^ 3 * δ) (fun ω => Z ω ^ 2)
    have e3 : P[fun ω => 4 * u ^ 2 * ind ω | G.1] =ᵐ[P]
        fun ω => 4 * u ^ 2 * P[ind | G.1] ω :=
      condExp_smul (μ := P) (m := G.1) (4 * u ^ 2) ind
    filter_upwards [e1, e2, e3, hvar] with ω h1 h2 h3 hv
    simp only [Pi.add_apply] at h1
    rw [h1, h2, h3, hv]
  have hjensen := norm_condExp_le (μ := P) (m := G.1) R
  have hmono : P[fun ω => ‖R ω‖ | G.1] ≤ᵐ[P] P[bd | G.1] :=
    condExp_mono hRint.norm hbdint (Filter.Eventually.of_forall hbound)
  filter_upwards [hjensen, hmono, hbdcond, hRcond] with ω j1 j2 j3 j4
  have hstep : P[fA | G.1] ω - (1 - ((u ^ 2 / 2 * V ω : ℝ) : ℂ)) = P[R | G.1] ω := by
    rw [j4]
    ring
  rw [hstep]
  calc ‖P[R | G.1] ω‖ ≤ P[fun ω => ‖R ω‖ | G.1] ω := j1
    _ ≤ P[bd | G.1] ω := j2
    _ = 2 / 9 * |u| ^ 3 * δ * V ω + 4 * u ^ 2 * P[ind | G.1] ω := j3

end ReflectedGMS.MartingaleLimit
