/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.ParameterizedResolventMarkov at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.ParameterizedResolvent
import LatticeProb.Bonanno.ReflectedGMS.Forms.ResolventMarkov

/-!
# Markov preservation by every positive parameterized resolvent

The checked algebraic `h`-resolvent minimizes the quadratic objective with
energy coefficient `h > 0`.  Completing the square against its exact weak
identity lets the existing normal-contraction argument apply verbatim at every
positive parameter.
-/

set_option autoImplicit false

open scoped InnerProductSpace ENNReal

namespace ReflectedGMS.FullNetworkForm

variable {V : Type*} {C : ℝ → ℝ}

/-- The quadratic full-form objective with positive energy coefficient `h`. -/
noncomputable def parameterizedResolventObjective
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) (h : ℝ)
    (f : ValueSpace V) (u : hilbertDomain G m) : ℝ :=
  ‖valueInclusion G m u - f‖ ^ 2 + h * ‖gradientInclusion G m u‖ ^ 2

theorem parameterizedResolventFunction_hasSpeedL2
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (h : ℝ) (f : ValueSpace V) :
    HasSpeedL2 m (parameterizedResolventFunction G m h f) :=
  hasSpeedL2_unweight m hm (parameterizedResolvent G m h f)

private noncomputable def parameterizedResolventLift
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (h : ℝ) (f : ValueSpace V) : hilbertDomain G m :=
  inHilbertDomain G m hm (parameterizedResolventFunction G m h f)
    (parameterizedResolventFunction_hasSpeedL2 G m hm h f)
    (parameterizedResolventFunction_hasFiniteEnergy G m h f)

private theorem parameterizedResolventLift_weak
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    {h : ℝ} (hh : 0 < h) (f : ValueSpace V) (v : hilbertDomain G m) :
    ⟪valueInclusion G m (parameterizedResolventLift G m hm h f),
        valueInclusion G m v⟫_ℝ +
      h * ⟪gradientInclusion G m (parameterizedResolventLift G m hm h f),
        gradientInclusion G m v⟫_ℝ =
      ⟪f, valueInclusion G m v⟫_ℝ := by
  let g := unweight m (valueInclusion G m v)
  have hgL2 : HasSpeedL2 m g := hasSpeedL2_unweight m hm (valueInclusion G m v)
  have hgE : G.HasFiniteEnergy g := hilbertDomain_hasFiniteEnergy G m v
  have hw := parameterizedResolventFunction_weak G m hm hh f g hgL2 hgE
  dsimp [parameterizedResolventLift]
  rw [gradientInclusion_eq, weightedGradient_inner]
  have hwu := weightedValue_unweight m hm (parameterizedResolvent G m h f)
  change weightedValue m (parameterizedResolventFunction G m h f) _ =
    parameterizedResolvent G m h f at hwu
  rw [hwu]
  have hgv := weightedValue_unweight m hm (valueInclusion G m v)
  change weightedValue m g hgL2 = valueInclusion G m v at hgv
  rw [hgv] at hw
  exact hw

/-- Exact completing-square identity for the positive-parameter objective. -/
theorem parameterizedResolventObjective_eq_min_add_squares
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    {h : ℝ} (hh : 0 < h) (f : ValueSpace V) (v : hilbertDomain G m) :
    parameterizedResolventObjective G m h f v =
      parameterizedResolventObjective G m h f
        (parameterizedResolventLift G m hm h f) +
      ‖valueInclusion G m (v - parameterizedResolventLift G m hm h f)‖ ^ 2 +
      h * ‖gradientInclusion G m
        (v - parameterizedResolventLift G m hm h f)‖ ^ 2 := by
  let u := parameterizedResolventLift G m hm h f
  let d := v - u
  have hv : v = u + d := by dsimp [d]; abel
  have hweak := parameterizedResolventLift_weak G m hm hh f d
  have hcross :
      ⟪valueInclusion G m u - f, valueInclusion G m d⟫_ℝ +
        h * ⟪gradientInclusion G m u, gradientInclusion G m d⟫_ℝ = 0 := by
    rw [inner_sub_left]
    linarith
  rw [hv]
  change
    ‖valueInclusion G m u + valueInclusion G m d - f‖ ^ 2 +
        h * ‖gradientInclusion G m u + gradientInclusion G m d‖ ^ 2 =
      (‖valueInclusion G m u - f‖ ^ 2 +
        h * ‖gradientInclusion G m u‖ ^ 2) +
      ‖valueInclusion G m (u + d - u)‖ ^ 2 +
        h * ‖gradientInclusion G m (u + d - u)‖ ^ 2
  rw [show valueInclusion G m u + valueInclusion G m d - f =
      (valueInclusion G m u - f) + valueInclusion G m d by abel]
  rw [norm_add_sq_real, norm_add_sq_real, add_sub_cancel_left]
  linarith

/-- On an actual full-domain function, the parameterized objective is weighted
`L²` error plus `h` times the checked network energy. -/
theorem parameterizedResolventObjective_inHilbertDomain
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (h : ℝ) (f : ValueSpace V) (g : V → ℝ) (hL2 : HasSpeedL2 m g)
    (hE : G.HasFiniteEnergy g) :
    parameterizedResolventObjective G m h f
        (inHilbertDomain G m hm g hL2 hE) =
      ‖weightedValue m g hL2 - f‖ ^ 2 + h * G.Energy g := by
  rw [parameterizedResolventObjective, valueInclusion_inHilbertDomain,
    gradientInclusion_inHilbertDomain, weightedGradient_norm_sq]

/-- A normal contraction fixing every decoded forcing value also fixes the
decoded `h`-resolvent for every `h > 0`. -/
theorem parameterizedResolventFunction_contraction_fixed
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    {h : ℝ} (hh : 0 < h) (f : ValueSpace V)
    (hC : LipschitzWith 1 C) (hzero : C 0 = 0)
    (hfix : ∀ v, C (unweight m f v) = unweight m f v) :
    C ∘ parameterizedResolventFunction G m h f =
      parameterizedResolventFunction G m h f := by
  let u := parameterizedResolventFunction G m h f
  have huL2 : HasSpeedL2 m u := parameterizedResolventFunction_hasSpeedL2 G m hm h f
  have huE : G.HasFiniteEnergy u := parameterizedResolventFunction_hasFiniteEnergy G m h f
  have hc := normalContraction G m u hC hzero huL2 huE
  let w := inHilbertDomain G m hm (C ∘ u) hc.1 hc.2.1
  let q := parameterizedResolventLift G m hm h f
  have hdist :
      ‖weightedValue m (C ∘ u) hc.1 - f‖ ≤ ‖weightedValue m u huL2 - f‖ := by
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro v
    have hfv : f v = Real.sqrt (m v) * unweight m f v := by
      simpa only [weightedValue_apply] using congrArg (fun z : ValueSpace V => z v)
        (weightedValue_unweight m hm f).symm
    have hcontract := hC.dist_le_mul (u v) (unweight m f v)
    rw [NNReal.coe_one, one_mul, Real.dist_eq, Real.dist_eq, hfix v] at hcontract
    change ‖Real.sqrt (m v) * C (u v) - f v‖ ≤
      ‖Real.sqrt (m v) * u v - f v‖
    rw [hfv, ← mul_sub, ← mul_sub, norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left hcontract (norm_nonneg _)
  have hobj : parameterizedResolventObjective G m h f w ≤
      parameterizedResolventObjective G m h f q := by
    dsimp [w, q, parameterizedResolventLift]
    rw [parameterizedResolventObjective_inHilbertDomain,
      parameterizedResolventObjective_inHilbertDomain]
    exact add_le_add
      ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hdist)
      (mul_le_mul_of_nonneg_left hc.2.2 hh.le)
  have hsquare := parameterizedResolventObjective_eq_min_add_squares
    G m hm hh f w
  change parameterizedResolventObjective G m h f w =
      parameterizedResolventObjective G m h f q +
        ‖valueInclusion G m (w - q)‖ ^ 2 +
          h * ‖gradientInclusion G m (w - q)‖ ^ 2 at hsquare
  have hvalue : ‖valueInclusion G m (w - q)‖ = 0 := by
    have hgrad : 0 ≤ h * ‖gradientInclusion G m (w - q)‖ ^ 2 :=
      mul_nonneg hh.le (sq_nonneg _)
    nlinarith [sq_nonneg ‖valueInclusion G m (w - q)‖]
  have hvq : valueInclusion G m w = valueInclusion G m q := by
    have := norm_eq_zero.mp hvalue
    rw [map_sub, sub_eq_zero] at this
    exact this
  change weightedValue m (C ∘ u) _ =
      weightedValue m u huL2 at hvq
  have hdecoded := congrArg (unweight m) hvq
  rw [unweight_weightedValue m hm, unweight_weightedValue m hm] at hdecoded
  simpa [u] using hdecoded

/-- If the decoded forcing lies in `[0,1]`, so does its positive-parameter
resolvent. -/
theorem parameterizedResolventFunction_mem_Icc
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    {h : ℝ} (hh : 0 < h) (f : ValueSpace V)
    (hf : ∀ v, unweight m f v ∈ Set.Icc (0 : ℝ) 1) (v : V) :
    parameterizedResolventFunction G m h f v ∈ Set.Icc (0 : ℝ) 1 := by
  have hfix : ∀ v, unitIntervalProjection (unweight m f v) = unweight m f v := by
    intro w
    simp [unitIntervalProjection, Set.coe_projIcc, min_eq_right (hf w).2,
      max_eq_right (hf w).1]
  have hinv := parameterizedResolventFunction_contraction_fixed G m hm hh f
    unitIntervalProjection_lipschitz unitIntervalProjection_zero hfix
  have hmem := unitIntervalProjection_mem (parameterizedResolventFunction G m h f v)
  rw [show unitIntervalProjection (parameterizedResolventFunction G m h f v) =
      parameterizedResolventFunction G m h f v by
    simpa only [Function.comp_apply] using congrFun hinv v] at hmem
  exact hmem

end ReflectedGMS.FullNetworkForm
