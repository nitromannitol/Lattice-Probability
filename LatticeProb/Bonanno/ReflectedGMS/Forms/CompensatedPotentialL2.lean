/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.CompensatedPotentialL2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.VertexPotentialSupermartingale
import LatticeProb.Bonanno.ReflectedGMS.Forms.ProcessOccupationLaplace
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Integral.Prod
import LatticeProb.Bonanno.ReflectedGMS.Forms.ReflectedTrajectoryConditional
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Square integrability of the compensated vertex potential

The terminal discounted occupation is bounded between `0` and `1 / alpha`.
Conditional expectation preserves these bounds and contracts `L²`, so the
concrete compensated process is square integrable at every deterministic time.
The martingale projection identity then gives orthogonal deterministic-time
increments and the exact second-moment increment formula.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

namespace ReflectedGMS

open ReflectedWalk ReflectedWalk.Theorem16 FullNetworkForm

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V]

/-- Deterministic increments of a real square-integrable martingale are
orthogonal to its past value. -/
theorem martingale_integral_mul_increment_eq_zero
    {Ω ι : Type*} {mΩ : MeasurableSpace Ω} [Preorder ι]
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ι mΩ}
    {M : ι → Ω → ℝ} (hM : Martingale M F P)
    (h2 : ∀ r, MemLp (M r) 2 P) {s t : ι} (hst : s ≤ t) :
    (∫ ω, M s ω * (M t ω - M s ω) ∂P) = 0 := by
  have hs2 := h2 s
  have ht2 := h2 t
  have hst2 : MemLp (M t - M s) 2 P := ht2.sub hs2
  have hprod : Integrable (M s * (M t - M s)) P := hs2.integrable_mul hst2
  have hincr : Integrable (M t - M s) P := hst2.integrable one_le_two
  have hsmeas : AEStronglyMeasurable[F s] (M s) P :=
    (hM.stronglyMeasurable s).aestronglyMeasurable
  have hce : P[M t - M s | F s] =ᵐ[P] 0 := by
    have hsub := condExp_sub (hM.integrable t) (hM.integrable s) (F s)
    have hself : P[M s | F s] =ᵐ[P] M s := hM.condExp_ae_eq le_rfl
    filter_upwards [hsub, hM.condExp_ae_eq hst, hself] with ω hsubω htω hsω
    change P[M t - M s | F s] ω =
      P[M t | F s] ω - P[M s | F s] ω at hsubω
    rw [hsubω, htω, hsω]
    simp
  calc
    (∫ ω, M s ω * (M t ω - M s ω) ∂P) =
        ∫ ω, P[M s * (M t - M s) | F s] ω ∂P :=
      (integral_condExp (F.le s)).symm
    _ = ∫ ω, M s ω * P[M t - M s | F s] ω ∂P :=
      integral_congr_ae
        (condExp_mul_of_aestronglyMeasurable_left hsmeas hprod hincr)
    _ = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hce] with ω hω
      simp [hω]

/-- Exact deterministic-time `L²` increment identity for a real
square-integrable martingale. -/
theorem martingale_sq_increment_integral
    {Ω ι : Type*} {mΩ : MeasurableSpace Ω} [Preorder ι]
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ι mΩ}
    {M : ι → Ω → ℝ} (hM : Martingale M F P)
    (h2 : ∀ r, MemLp (M r) 2 P) {s t : ι} (hst : s ≤ t) :
    (∫ ω, (M t ω - M s ω) ^ 2 ∂P) =
      (∫ ω, (M t ω) ^ 2 ∂P) - ∫ ω, (M s ω) ^ 2 ∂P := by
  have hs2 := h2 s
  have ht2 := h2 t
  have hcross := martingale_integral_mul_increment_eq_zero hM h2 hst
  have htti : Integrable (M t * M t) P := ht2.integrable_mul ht2
  have hssi : Integrable (M s * M s) P := hs2.integrable_mul hs2
  have htsi : Integrable (M s * (M t - M s)) P :=
    hs2.integrable_mul (ht2.sub hs2)
  calc
    (∫ ω, (M t ω - M s ω) ^ 2 ∂P) =
        ∫ ω, (M t ω * M t ω - M s ω * M s ω) -
          2 * (M s ω * (M t ω - M s ω)) ∂P := by
      apply integral_congr_ae
      filter_upwards with ω
      ring
    _ = (∫ ω, M t ω * M t ω - M s ω * M s ω ∂P) -
        ∫ ω, 2 * (M s ω * (M t ω - M s ω)) ∂P :=
      integral_sub (htti.sub hssi) (htsi.const_mul 2)
    _ = ((∫ ω, M t ω * M t ω ∂P) -
        ∫ ω, M s ω * M s ω ∂P) -
        2 * ∫ ω, M s ω * (M t ω - M s ω) ∂P := by
      have hdiff : (∫ ω, M t ω * M t ω - M s ω * M s ω ∂P) =
          (∫ ω, M t ω * M t ω ∂P) -
            ∫ ω, M s ω * M s ω ∂P := integral_sub htti hssi
      rw [hdiff, integral_const_mul]
    _ = (∫ ω, (M t ω) ^ 2 ∂P) - ∫ ω, (M s ω) ^ 2 ∂P := by
      rw [hcross]
      simp only [mul_zero, sub_zero, pow_two]

end ReflectedGMS
