/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.SemigroupMarkov at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.EulerResolvent
import LatticeProb.Bonanno.ReflectedGMS.Forms.ParameterizedResolventMarkov

/-!
# Markov preservation by the full-form semigroup

Dyadic powers of the positive parameterized resolvents preserve every pointwise
fixed set of a normal contraction.  Operator-norm convergence of those powers,
followed by continuous evaluation and decoding, transfers the same statement to
the actual full-form semigroup.  This gives both the unit-interval property and
positivity, including for unbounded nonnegative data in weighted `L²`.
-/

set_option autoImplicit false

open Filter
open scoped Topology NNReal

namespace ReflectedGMS.FullNetworkForm

variable {V : Type*} {C : ℝ → ℝ}

/-- Every power of a positive parameterized resolvent preserves the pointwise
fixed set of a normal contraction. -/
private theorem parameterizedResolvent_pow_contraction_fixed
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    {h : ℝ} (hh : 0 < h) (f : ValueSpace V)
    (hC : LipschitzWith 1 C) (hzero : C 0 = 0)
    (hfix : ∀ v, C (unweight m f v) = unweight m f v) (n : ℕ) :
    C ∘ unweight m (((parameterizedResolvent G m h) ^ n) f) =
      unweight m (((parameterizedResolvent G m h) ^ n) f) := by
  induction n with
  | zero =>
      funext v
      simpa only [pow_zero, one_apply_eq_self, Function.comp_apply] using hfix v
  | succ n ih =>
      have hstep := parameterizedResolventFunction_contraction_fixed
        G m hm hh (((parameterizedResolvent G m h) ^ n) f) hC hzero
        (fun v ↦ congrFun ih v)
      simpa only [parameterizedResolventFunction, pow_succ',
        ContinuousLinearMap.mul_apply] using hstep

/-- The actual full-form semigroup preserves every pointwise fixed set of a
normal contraction on decoded weighted `L²` data. -/
theorem fullFormSemigroup_contraction_fixed
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (t : ℝ≥0) (f : ValueSpace V)
    (hC : LipschitzWith 1 C) (hzero : C 0 = 0)
    (hfix : ∀ v, C (unweight m f v) = unweight m f v) :
    C ∘ unweight m (fullFormSemigroup G m t f) =
      unweight m (fullFormSemigroup G m t f) := by
  rcases eq_zero_or_pos t with rfl | ht
  · rw [fullFormSemigroup_zero]
    funext v
    simpa only [one_apply_eq_self, Function.comp_apply] using hfix v
  · funext v
    let evalDecoded : (ValueSpace V →L[ℝ] ValueSpace V) → ℝ :=
      fun T ↦ unweight m (T f) v
    have heval : Continuous evalDecoded := by
      exact (((lp.evalCLM ℝ (fun _ : V ↦ ℝ) 2 v).continuous.comp
        (ContinuousLinearMap.apply ℝ (ValueSpace V) f).continuous).div_const _)
    have hlim : Tendsto
        (fun n ↦ unweight m
          ((parameterizedResolvent G m ((t : ℝ) / (2 : ℝ) ^ n) ^ (2 ^ n : ℕ)) f) v)
        atTop (nhds (unweight m (fullFormSemigroup G m t f) v)) := by
      exact heval.continuousAt.tendsto.comp
        (dyadic_parameterizedResolvent_pow_tendsto G m ht)
    have hClim := hC.continuous.continuousAt.tendsto.comp hlim
    have hfixed (n : ℕ) :
        C (unweight m
          ((parameterizedResolvent G m ((t : ℝ) / (2 : ℝ) ^ n) ^ (2 ^ n : ℕ)) f) v) =
        unweight m
          ((parameterizedResolvent G m ((t : ℝ) / (2 : ℝ) ^ n) ^ (2 ^ n : ℕ)) f) v := by
      exact congrFun (parameterizedResolvent_pow_contraction_fixed G m hm
        (div_pos (show 0 < (t : ℝ) from ht) (pow_pos (by norm_num) n))
        f hC hzero hfix (2 ^ n)) v
    have hClim' : Tendsto
        (fun n ↦ unweight m
          ((parameterizedResolvent G m ((t : ℝ) / (2 : ℝ) ^ n) ^ (2 ^ n : ℕ)) f) v)
        atTop (nhds (C (unweight m (fullFormSemigroup G m t f) v))) := by
      exact hClim.congr' (Filter.Eventually.of_forall fun n ↦ hfixed n)
    simpa only [Function.comp_apply] using tendsto_nhds_unique hClim' hlim

/-- If decoded weighted `L²` data lie in `[0,1]`, then so does the full-form
semigroup at every nonnegative time. -/
theorem fullFormSemigroup_mem_Icc
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (t : ℝ≥0) (f : ValueSpace V)
    (hf : ∀ v, unweight m f v ∈ Set.Icc (0 : ℝ) 1) (v : V) :
    unweight m (fullFormSemigroup G m t f) v ∈ Set.Icc (0 : ℝ) 1 := by
  have hfix : ∀ v, unitIntervalProjection (unweight m f v) = unweight m f v := by
    intro w
    simp [unitIntervalProjection, Set.coe_projIcc, min_eq_right (hf w).2,
      max_eq_right (hf w).1]
  have hinv := fullFormSemigroup_contraction_fixed G m hm t f
    unitIntervalProjection_lipschitz unitIntervalProjection_zero hfix
  have hmem := unitIntervalProjection_mem (unweight m (fullFormSemigroup G m t f) v)
  rw [show unitIntervalProjection (unweight m (fullFormSemigroup G m t f) v) =
      unweight m (fullFormSemigroup G m t f) v by
    simpa only [Function.comp_apply] using congrFun hinv v] at hmem
  exact hmem

/-- The full-form semigroup preserves nonnegativity for arbitrary nonnegative
decoded weighted `L²` data; no bounded clipping hypothesis is needed. -/
theorem fullFormSemigroup_nonneg
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (t : ℝ≥0) (f : ValueSpace V) (hf : ∀ v, 0 ≤ unweight m f v) (v : V) :
    0 ≤ unweight m (fullFormSemigroup G m t f) v := by
  let Cplus : ℝ → ℝ := fun x ↦ max 0 x
  have hfix : ∀ v, Cplus (unweight m f v) = unweight m f v := by
    intro w
    exact max_eq_right (hf w)
  have hCplus : LipschitzWith 1 Cplus := by
    simpa [Cplus] using (LipschitzWith.id.const_max 0)
  have hinv := fullFormSemigroup_contraction_fixed G m hm t f
    hCplus (by simp [Cplus]) hfix
  have hv : max 0 (unweight m (fullFormSemigroup G m t f) v) =
      unweight m (fullFormSemigroup G m t f) v := by
    simpa only [Cplus, Function.comp_apply] using congrFun hinv v
  rw [max_eq_right_iff] at hv
  exact hv

end ReflectedGMS.FullNetworkForm
