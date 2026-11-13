/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.VertexResolventExcessive at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.SemigroupProbabilityKernel
import LatticeProb.Bonanno.ReflectedGMS.Forms.SemigroupKernelLaplace
import Mathlib.MeasureTheory.Group.LIntegral

/-!
# Excessivity of the vertex occupation resolvent

The positive-discount potential of one vertex is excessive for the actual
analytic semigroup kernel. The proof is Tonelli plus Chapman--Kolmogorov.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal

namespace ReflectedGMS.FullNetworkForm

variable {V : Type*}

/-- The nonnegative extended-real positive-discount occupation potential. -/
noncomputable def vertexOccupationPotentialENN
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (alpha : ℝ) (x y : V) : ℝ≥0∞ :=
  ∫⁻ t : ℝ in Ioi 0, ENNReal.ofReal
    (Real.exp (-alpha * t) * semigroupKernel G m (Real.toNNReal t) x y)

/-- The ordinary real positive-discount occupation potential. -/
noncomputable def vertexOccupationPotential
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (alpha : ℝ) (x y : V) : ℝ :=
  ∫ t : ℝ in Ioi 0,
    Real.exp (-alpha * t) * semigroupKernel G m (Real.toNNReal t) x y

private theorem measurable_discountedKernel
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (alpha : ℝ) (x y : V) :
    Measurable (fun t : ℝ => ENNReal.ofReal
      (Real.exp (-alpha * t) * semigroupKernel G m (Real.toNNReal t) x y)) := by
  apply ENNReal.continuous_ofReal.measurable.comp
  exact ((by fun_prop : Continuous fun t : ℝ => Real.exp (-alpha * t)).mul
    ((continuous_semigroupKernel G m hm x y).comp continuous_real_toNNReal)).measurable

private theorem lintegral_comp_add_Ioi_le
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) {s : ℝ} (hs : 0 ≤ s) :
    (∫⁻ t : ℝ in Ioi 0, f (t + s)) ≤ ∫⁻ t : ℝ in Ioi 0, f t := by
  rw [← lintegral_indicator measurableSet_Ioi,
    ← lintegral_indicator measurableSet_Ioi]
  have hind : (Ioi 0).indicator (fun t : ℝ => f (t + s)) =
      fun t => (Ioi s).indicator f (t + s) := by
    funext t
    by_cases ht : t ∈ Ioi (0 : ℝ)
    · have htt : 0 < t := ht
      have hts : t + s ∈ Ioi s := by
        change s < t + s
        linarith
      simp [ht, hts]
    · have hts : t + s ∉ Ioi s := by
        change ¬ s < t + s
        have htt : ¬ 0 < t := ht
        linarith
      simp [ht, hts]
  rw [hind]
  calc
    (∫⁻ t : ℝ, (Ioi s).indicator f (t + s)) =
        ∫⁻ t : ℝ, (Ioi s).indicator f t := by
      calc
        _ = ∫⁻ t : ℝ, (Ioi s).indicator f t ∂Measure.map (fun t => t + s) volume := by
          symm
          exact MeasureTheory.lintegral_map
            (hf.indicator measurableSet_Ioi) (measurable_id.add_const s)
        _ = _ := by rw [map_add_right_eq_self]
    _ ≤ ∫⁻ t : ℝ, (Ioi 0).indicator f t := by
      apply lintegral_mono
      intro t
      by_cases ht : t ∈ Ioi s
      · have ht0 : t ∈ Ioi (0 : ℝ) := by
          have hst : s < t := ht
          change 0 < t
          linarith
        simp [ht, ht0]
      · simp [ht]

/-- Positive-discount vertex potentials are excessive, in ENNReal form. -/
theorem vertexOccupationPotentialENN_excessive [DecidableEq V] [Countable V]
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (_hmsum : Summable m)
    {alpha : ℝ} (_ha : 0 < alpha) (s : ℝ≥0) (x y : V) :
    ENNReal.ofReal (Real.exp (-alpha * (s : ℝ))) *
        ∑' z, ENNReal.ofReal (semigroupKernel G m s x z) *
          vertexOccupationPotentialENN G m alpha z y ≤
      vertexOccupationPotentialENN G m alpha x y := by
  let f : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal
    (Real.exp (-alpha * t) * semigroupKernel G m (Real.toNNReal t) x y)
  have hf : Measurable f := measurable_discountedKernel G m hm alpha x y
  have hpull (z : V) :
      (ENNReal.ofReal (Real.exp (-alpha * (s : ℝ))) *
          ENNReal.ofReal (semigroupKernel G m s x z)) *
          vertexOccupationPotentialENN G m alpha z y =
        ∫⁻ t : ℝ in Ioi 0,
          (ENNReal.ofReal (Real.exp (-alpha * (s : ℝ))) *
            ENNReal.ofReal (semigroupKernel G m s x z)) *
          ENNReal.ofReal (Real.exp (-alpha * t) *
            semigroupKernel G m (Real.toNNReal t) z y) := by
    rw [vertexOccupationPotentialENN,
      lintegral_const_mul _ (measurable_discountedKernel G m hm alpha z y)]
  calc
    ENNReal.ofReal (Real.exp (-alpha * (s : ℝ))) *
          ∑' z, ENNReal.ofReal (semigroupKernel G m s x z) *
            vertexOccupationPotentialENN G m alpha z y =
        ∫⁻ t : ℝ in Ioi 0, f (t + s) := by
      rw [← ENNReal.tsum_mul_left]
      simp_rw [← mul_assoc, hpull]
      rw [← MeasureTheory.lintegral_tsum]
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only [f]
      simp_rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← ENNReal.ofReal_mul
        (mul_nonneg (Real.exp_nonneg _)
          (semigroupKernel_nonneg G m hm s x _))]
      rw [← ENNReal.ofReal_tsum_of_nonneg]
      · congr 1
        calc
          ∑' z, Real.exp (-alpha * (s : ℝ)) * semigroupKernel G m s x z *
              (Real.exp (-alpha * t) *
                semigroupKernel G m (Real.toNNReal t) z y) =
              (Real.exp (-alpha * (s : ℝ)) * Real.exp (-alpha * t)) *
                ∑' z, semigroupKernel G m s x z *
                  semigroupKernel G m (Real.toNNReal t) z y := by
            rw [← tsum_mul_left]
            apply tsum_congr
            intro z
            ring
          _ = (Real.exp (-alpha * (s : ℝ)) * Real.exp (-alpha * t)) *
                semigroupKernel G m (s + Real.toNNReal t) x y := by
            rw [tsum_semigroupKernel_mul_eq_semigroupKernel_add G m hm]
          _ = Real.exp (-alpha * (t + (s : ℝ))) *
                semigroupKernel G m (Real.toNNReal (t + (s : ℝ))) x y := by
            have ht0 : 0 ≤ t := ht.le
            have htime : Real.toNNReal (t + (s : ℝ)) = s + Real.toNNReal t := by
              rw [Real.toNNReal_add ht0 s.coe_nonneg, Real.toNNReal_coe]
              exact add_comm _ _
            rw [htime]
            congr 1
            rw [← Real.exp_add]
            congr 1
            ring
      · intro z
        exact mul_nonneg
          (mul_nonneg (Real.exp_nonneg _)
            (semigroupKernel_nonneg G m hm s x z))
          (mul_nonneg (Real.exp_nonneg _)
            (semigroupKernel_nonneg G m hm (Real.toNNReal t) z y))
      · refine (summable_semigroupKernel_mul G m hm s (Real.toNNReal t) x y).mul_left
          (Real.exp (-alpha * (s : ℝ)) * Real.exp (-alpha * t)) |>.congr ?_
        intro z
        ring
      · intro z
        exact ((measurable_discountedKernel G m hm alpha z y).const_mul _).aemeasurable
    _ ≤ ∫⁻ t : ℝ in Ioi 0, f t :=
      lintegral_comp_add_Ioi_le f hf s.coe_nonneg
    _ = vertexOccupationPotentialENN G m alpha x y := rfl

/-- The ENNReal potential is the lift of the integrable real kernel potential. -/
theorem vertexOccupationPotentialENN_eq_ofReal
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) {alpha : ℝ} (ha : 0 < alpha) (x y : V) :
    vertexOccupationPotentialENN G m alpha x y =
      ENNReal.ofReal (vertexOccupationPotential G m alpha x y) := by
  symm
  exact ofReal_integral_eq_lintegral_ofReal
    (integrableOn_exp_neg_alpha_mul_semigroupKernel G m ha x y)
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t _ =>
      mul_nonneg (Real.exp_nonneg _)
        (semigroupKernel_nonneg G m hm (Real.toNNReal t) x y))

/-- Identification of the scalar potential with the checked full resolvent. -/
theorem vertexOccupationPotential_eq_resolvent
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    {alpha : ℝ} (ha : 0 < alpha) (x y : V) :
    vertexOccupationPotential G m alpha x y =
      (1 / alpha) * unweight m
        (parameterizedResolvent G m (1 / alpha)
          (weightedValue m (G.indic y) (VertexTest.indic_hasSpeedL2 G m y))) x :=
  integral_exp_neg_alpha_mul_semigroupKernel G m ha x y

end ReflectedGMS.FullNetworkForm
