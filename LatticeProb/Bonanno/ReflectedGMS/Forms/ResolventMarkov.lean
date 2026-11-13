/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.ResolventMarkov at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.DomainDensity
import LatticeProb.Bonanno.ReflectedGMS.Forms.NormalContraction
import LatticeProb.Bonanno.ReflectedGMS.Forms.Resolvent

/-!
# Markov preservation by the resolvent

Normal contractions that fix the decoded forcing also fix the decoded full-form
resolvent.  The proof compares the contracted candidate in the exact variational
objective and uses uniqueness of the minimizer.

This is a pointwise statement for the real resolvent.  No operator-order or
semigroup Markov assertion is made.
-/

-- Merged from `ReflectedGMS/Forms/ResolventMinimizer.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_ResolventMinimizer

/-!
# Variational minimum for the full resolvent

The full-domain `1`-resolvent lift minimizes its actual quadratic graph-form
objective.  The proof is the Hilbert-space completing-square identity, with the
cross term cancelled by the checked weak resolvent equation.

No positivity, Markov, or semigroup property is asserted here.
-/

set_option autoImplicit false

open scoped InnerProductSpace

namespace ReflectedGMS.FullNetworkForm

variable {V : Type*} (G : ReflectedWalk.ConductanceGraph V)

/-- The quadratic objective for the full form at forcing vector `f`. -/
noncomputable def resolventObjective (m : V → ℝ) (f : ValueSpace V)
    (u : hilbertDomain G m) : ℝ :=
  ‖valueInclusion G m u - f‖ ^ 2 + ‖gradientInclusion G m u‖ ^ 2

private theorem hilbertDomain_norm_sq_eq (m : V → ℝ)
    (u : hilbertDomain G m) :
    ‖u‖ ^ 2 = ‖valueInclusion G m u‖ ^ 2 + ‖gradientInclusion G m u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, hilbertDomain_inner,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

/-- Exact completing-square identity for the full-domain resolvent objective. -/
theorem resolventObjective_eq_min_add_norm_sq (m : V → ℝ) (f : ValueSpace V)
    (v : hilbertDomain G m) :
    resolventObjective G m f v =
      resolventObjective G m f (oneResolventLift G m f) +
        ‖v - oneResolventLift G m f‖ ^ 2 := by
  let u := oneResolventLift G m f
  let d := v - u
  have hv : v = u + d := by dsimp [d]; abel
  have hweak := oneResolventLift_weak G m f d
  have hcross :
      ⟪valueInclusion G m u - f, valueInclusion G m d⟫_ℝ +
        ⟪gradientInclusion G m u, gradientInclusion G m d⟫_ℝ = 0 := by
    dsimp [u]
    rw [inner_sub_left]
    linarith
  rw [hv]
  change
    ‖valueInclusion G m u + valueInclusion G m d - f‖ ^ 2 +
        ‖gradientInclusion G m u + gradientInclusion G m d‖ ^ 2 =
      (‖valueInclusion G m u - f‖ ^ 2 + ‖gradientInclusion G m u‖ ^ 2) +
        ‖u + d - u‖ ^ 2
  rw [show valueInclusion G m u + valueInclusion G m d - f =
      (valueInclusion G m u - f) + valueInclusion G m d by abel]
  rw [norm_add_sq_real, norm_add_sq_real, add_sub_cancel_left,
    hilbertDomain_norm_sq_eq G m d]
  linarith

/-- On an actual finite-energy, speed-`L²` function, the abstract objective is
exactly weighted `L²` error plus the checked full network energy. -/
theorem resolventObjective_inHilbertDomain (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (f : ValueSpace V) (g : V → ℝ) (hL2 : HasSpeedL2 m g)
    (hE : G.HasFiniteEnergy g) :
    resolventObjective G m f (inHilbertDomain G m hm g hL2 hE) =
      ‖weightedValue m g hL2 - f‖ ^ 2 + G.Energy g := by
  rw [resolventObjective, valueInclusion_inHilbertDomain,
    gradientInclusion_inHilbertDomain, weightedGradient_norm_sq]

end ReflectedGMS.FullNetworkForm

end Merged_ResolventMinimizer

set_option autoImplicit false

open scoped ENNReal

namespace ReflectedGMS.FullNetworkForm

variable {V : Type*} {C : ℝ → ℝ}

/-- Decoded values determine the entire full-domain vector. -/
theorem valueInclusion_injective
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) :
    Function.Injective (valueInclusion G m) := by
  intro u v huv
  have hgrad : gradientInclusion G m u = gradientInclusion G m v := by
    rw [gradientInclusion_eq, gradientInclusion_eq]
    apply lp.ext
    funext p
    simp only [weightedGradient_apply]
    rw [huv]
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  have hinner := hilbertDomain_inner G m (u - v) (u - v)
  rw [map_sub, huv, sub_self, map_sub, hgrad, sub_self,
    inner_zero_left, inner_zero_left, add_zero] at hinner
  rw [real_inner_self_eq_norm_sq] at hinner
  exact sq_eq_zero_iff.mp hinner

private theorem inHilbertDomain_oneResolventFunction
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (f : ValueSpace V) :
    inHilbertDomain G m hm (oneResolventFunction G m f)
        (oneResolventFunction_hasSpeedL2 G m hm f)
        (oneResolventFunction_hasFiniteEnergy G m f) =
      oneResolventLift G m f := by
  apply valueInclusion_injective G m
  rw [valueInclusion_inHilbertDomain]
  change weightedValue m (unweight m (oneResolvent G m f)) _ = oneResolvent G m f
  exact weightedValue_unweight m hm (oneResolvent G m f)

/-- A normal contraction fixing every decoded forcing value also fixes the
decoded full-form resolvent. -/
theorem oneResolventFunction_contraction_fixed
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (f : ValueSpace V) (hC : LipschitzWith 1 C) (hzero : C 0 = 0)
    (hfix : ∀ v, C (unweight m f v) = unweight m f v) :
    C ∘ oneResolventFunction G m f = oneResolventFunction G m f := by
  let u := oneResolventFunction G m f
  have huL2 : HasSpeedL2 m u := oneResolventFunction_hasSpeedL2 G m hm f
  have huE : G.HasFiniteEnergy u := oneResolventFunction_hasFiniteEnergy G m f
  have hc := normalContraction G m u hC hzero huL2 huE
  let w := inHilbertDomain G m hm (C ∘ u) hc.1 hc.2.1
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
  have hobj : resolventObjective G m f w ≤
      resolventObjective G m f (oneResolventLift G m f) := by
    rw [← inHilbertDomain_oneResolventFunction G m hm f]
    rw [resolventObjective_inHilbertDomain, resolventObjective_inHilbertDomain]
    exact add_le_add
      ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hdist) hc.2.2
  have hsquare := resolventObjective_eq_min_add_norm_sq G m f w
  have hnorm : ‖w - oneResolventLift G m f‖ = 0 := by
    nlinarith [norm_nonneg (w - oneResolventLift G m f)]
  have hw : w = oneResolventLift G m f := sub_eq_zero.mp (norm_eq_zero.mp hnorm)
  have hvalue := congrArg (valueInclusion G m) hw
  change weightedValue m (C ∘ u) _ = oneResolvent G m f at hvalue
  have hdecoded := congrArg (unweight m) hvalue
  rw [unweight_weightedValue m hm] at hdecoded
  simpa [u, oneResolventFunction] using hdecoded

end ReflectedGMS.FullNetworkForm
