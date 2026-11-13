/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.ResolventCoreEnergy at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.ResolventCoreSquareCompensation
import LatticeProb.Bonanno.ReflectedGMS.Forms.ResolventCoreLinearity
import LatticeProb.Bonanno.ReflectedGMS.Forms.VertexDynkinEnergy
import LatticeProb.Bonanno.ReflectedGMS.Forms.RightContinuousMartingaleMaximal

/-! The generic compensated-square energy identity, specialized to the
existing rational resolvent core. The speed law remains unnormalized. -/

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ReflectedGMS
open ReflectedWalk FullNetworkForm

variable {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]
  {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
  {PF : ProcessFamily V}
  (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
  (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
  (hmsum : Summable m) (q : CountableResolventCoreIndex V)

include h hG hm hmsum

theorem rawResolventCoreMartingale_sq_increment_eq_jumpOccupation
    (z : V) {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ ω, (rawResolventCoreMartingale PF G m q t ω -
        rawResolventCoreMartingale PF G m q s ω) ^ 2 ∂PF.P z) =
      ∫ ω, adaptedJumpOccupation PF G m (countableResolventCoreFeature G m q) t ω -
        adaptedJumpOccupation PF G m (countableResolventCoreFeature G m q) s ω ∂PF.P z :=
  martingale_sq_increment_integral_eq_compensator
    (rawResolventCoreMartingale_isMartingale h hG hm hmsum q z)
    (rawResolventCoreMartingale_memLp_two h hG hm hmsum q (PF.P z))
    (rawResolventCoreSquareCompensation_isMartingale h hG hm hmsum q z) hst

theorem mul_rawResolventCoreMartingale_sq_increment_integral_le
    (z : V) {s t : ℝ≥0} (hst : s ≤ t) :
    m z * (∫ ω, (rawResolventCoreMartingale PF G m q t ω -
        rawResolventCoreMartingale PF G m q s ω) ^ 2 ∂PF.P z) ≤
      (t : ℝ) * (2 * G.Energy (countableResolventCoreFeature G m q)) := by
  have hu := countableResolventCoreFeature_hasFiniteEnergy G m q
  rw [rawResolventCoreMartingale_sq_increment_eq_jumpOccupation h hG hm hmsum q z hst,
    integral_sub (integrable_adaptedJumpOccupation h hG hm hmsum hu t z)
      (integrable_adaptedJumpOccupation h hG hm hmsum hu s z)]
  have hn : 0 ≤ ∫ ω, adaptedJumpOccupation PF G m
      (countableResolventCoreFeature G m q) s ω ∂PF.P z :=
    integral_nonneg (fun _ ↦ ENNReal.toReal_nonneg)
  have hb := mul_integral_adaptedJumpOccupation_le h hG hm hmsum hu t z
  nlinarith [hm z]

theorem rawResolventCoreMartingale_stationary_increment_energy
    {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ ω, (rawResolventCoreMartingale PF G m q t ω -
        rawResolventCoreMartingale PF G m q s ω) ^ 2 ∂reflectedSpeedLaw PF m) =
      ((t : ℝ) - (s : ℝ)) * (2 * G.Energy (countableResolventCoreFeature G m q)) := by
  letI := reflectedSpeedLaw_isFinite PF m hmsum
  have hu := countableResolventCoreFeature_hasFiniteEnergy G m q
  have h2 := (rawResolventCoreMartingale_memLp_two h hG hm hmsum q
    (reflectedSpeedLaw PF m) t).sub
      (rawResolventCoreMartingale_memLp_two h hG hm hmsum q (reflectedSpeedLaw PF m) s)
  have hsq : Integrable (fun ω ↦ (rawResolventCoreMartingale PF G m q t ω -
      rawResolventCoreMartingale PF G m q s ω) ^ 2) (reflectedSpeedLaw PF m) := by
    apply (h2.integrable_mul h2).congr
    filter_upwards [] with ω
    exact (pow_two _).symm
  have hA := (integrable_adaptedJumpOccupation_reflectedSpeedLaw h hG hm hmsum hu t).sub
    (integrable_adaptedJumpOccupation_reflectedSpeedLaw h hG hm hmsum hu s)
  have heq : (∫ ω, (rawResolventCoreMartingale PF G m q t ω -
      rawResolventCoreMartingale PF G m q s ω) ^ 2 ∂reflectedSpeedLaw PF m) =
      ∫ ω, adaptedJumpOccupation PF G m (countableResolventCoreFeature G m q) t ω -
        adaptedJumpOccupation PF G m (countableResolventCoreFeature G m q) s ω
        ∂reflectedSpeedLaw PF m := by
    have hAformula := integral_reflectedSpeedLaw PF m hmsum hA
    simp only [Pi.sub_apply] at hAformula
    rw [integral_reflectedSpeedLaw PF m hmsum hsq, hAformula]
    apply integral_congr_ae
    filter_upwards [] with z
    exact rawResolventCoreMartingale_sq_increment_eq_jumpOccupation h hG hm hmsum q z hst
  rw [heq, integral_sub
    (integrable_adaptedJumpOccupation_reflectedSpeedLaw h hG hm hmsum hu t)
    (integrable_adaptedJumpOccupation_reflectedSpeedLaw h hG hm hmsum hu s),
    integral_adaptedJumpOccupation_reflectedSpeedLaw h hG hm hmsum hu t,
    integral_adaptedJumpOccupation_reflectedSpeedLaw h hG hm hmsum hu s]
  ring

end ReflectedGMS
