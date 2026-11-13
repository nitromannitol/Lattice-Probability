/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.VertexDynkinEnergy at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.VertexDynkinSquareCompensation
import LatticeProb.Bonanno.ReflectedGMS.Forms.CompensatedPotentialL2
import LatticeProb.Bonanno.ReflectedGMS.Forms.AdaptedJumpOccupationMoments
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

/-! Exact stationary energy and fixed-start bounds for the actual ordinary
vertex Dynkin martingale, using its proved square compensator. -/

-- Merged from `ReflectedGMS/Forms/SquareCompensatorEnergy.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_SquareCompensatorEnergy

/-! The mean increment of an integrable square compensator equals the
second moment of the martingale increment. This reuses martingale orthogonality. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace ReflectedGMS

theorem martingale_sq_increment_integral_eq_compensator
    {Ω ι : Type*} {mΩ : MeasurableSpace Ω} [Preorder ι]
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ι mΩ}
    {M A : ι → Ω → ℝ} (hM : Martingale M F P)
    (h2 : ∀ r, MemLp (M r) 2 P)
    (hN : Martingale (fun r ω ↦ (M r ω) ^ 2 - A r ω) F P)
    {s t : ι} (hst : s ≤ t) :
    (∫ ω, (M t ω - M s ω) ^ 2 ∂P) =
      ∫ ω, A t ω - A s ω ∂P := by
  have hsq (r : ι) : Integrable (fun ω ↦ (M r ω) ^ 2) P := by
    have hp : Integrable (M r * M r) P := (h2 r).integrable_mul (h2 r)
    apply hp.congr
    filter_upwards [] with ω
    exact (pow_two (M r ω)).symm
  have hA (r : ι) : Integrable (A r) P := by
    apply ((hsq r).sub (hN.integrable r)).congr
    filter_upwards [] with ω
    change (M r ω) ^ 2 - ((M r ω) ^ 2 - A r ω) = A r ω
    ring
  have hmean := hN.setIntegral_eq hst MeasurableSet.univ
  simp only [Measure.restrict_univ] at hmean
  rw [integral_sub (hsq s) (hA s), integral_sub (hsq t) (hA t)] at hmean
  rw [martingale_sq_increment_integral hM h2 hst, integral_sub (hA t) (hA s)]
  linarith

end ReflectedGMS

end Merged_SquareCompensatorEnergy

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ReflectedGMS
open ReflectedWalk FullNetworkForm

variable {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

theorem integral_reflectedSpeedLaw
    (PF : ProcessFamily V) (m : V → ℝ) (hmsum : Summable m)
    {f : PF.Ω → ℝ} (hf : Integrable f (reflectedSpeedLaw PF m)) :
    (∫ ω, f ω ∂reflectedSpeedLaw PF m) =
      ∫ z, (∫ ω, f ω ∂PF.P z) ∂vertexSpeedMeasure m := by
  letI := vertexSpeedMeasure_isFinite m hmsum
  change Integrable f (reflectedStartKernel PF ∘ₘ vertexSpeedMeasure m) at hf
  rw [Measure.comp_eq_comp_const_apply] at hf
  change (∫ ω, f ω ∂(reflectedStartKernel PF ∘ₘ vertexSpeedMeasure m)) = _
  rw [Measure.comp_eq_comp_const_apply, Kernel.integral_comp hf]
  rfl

variable {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}
  (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
  (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
  (hmsum : Summable m) {alpha : ℝ} (ha : 0 < alpha) (y : V)

include h hG hm hmsum ha

theorem vertexDynkinMartingale_memLp_two
    (ν : Measure PF.Ω) [IsFiniteMeasure ν] (t : ℝ≥0) :
    MemLp (vertexDynkinMartingale PF G m alpha y t) 2 ν := by
  apply MemLp.of_bound
    (((vertexDynkinMartingale_isMartingale h hG hm hmsum ha y y).stronglyMeasurable t).mono
      (PF.naturalFiltration.le t)).aestronglyMeasurable
    (1 / alpha + (t : ℝ) * 2)
  exact Filter.Eventually.of_forall
    (norm_vertexDynkinMartingale_le PF G m hm ha y (le_refl t))

end ReflectedGMS
