/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.AdaptedJumpOccupationMoments at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.AdaptedJumpOccupation

/-! Exact first moment of the adapted ordinary jump occupation under the
unnormalized stationary speed law. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace ReflectedGMS
open ReflectedWalk

variable {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

theorem adaptedJumpOccupation_ae_eq_stationary_reflectedSpeedLaw
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {u : V → ℝ} (hu : G.HasFiniteEnergy u) :
    ∀ᵐ ω ∂reflectedSpeedLaw PF m, ∀ t : ℝ≥0,
      adaptedJumpOccupation PF G m u t ω =
        (stationaryJumpOccupation PF G m u t ω).toReal :=
  (ae_reflectedSpeedLaw_iff PF m hm _).mpr
    (fun z ↦ adaptedJumpOccupation_ae_eq_stationary h hG hm hmsum hu z)

theorem integrable_adaptedJumpOccupation_reflectedSpeedLaw
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {u : V → ℝ} (hu : G.HasFiniteEnergy u)
    (t : ℝ≥0) :
    Integrable (adaptedJumpOccupation PF G m u t) (reflectedSpeedLaw PF m) := by
  have hfinite : (∫⁻ ω, stationaryJumpOccupation PF G m u t ω
      ∂reflectedSpeedLaw PF m) ≠ ∞ := by
    rw [lintegral_stationaryJumpOccupation_reflectedSpeedLaw h hG hm hmsum hu t]
    exact ENNReal.ofReal_ne_top
  have hi := integrable_toReal_of_lintegral_ne_top
    (measurable_stationaryJumpOccupation PF G m u t).aemeasurable hfinite
  apply hi.congr
  filter_upwards [adaptedJumpOccupation_ae_eq_stationary_reflectedSpeedLaw
    h hG hm hmsum hu] with ω hω
  exact (hω t).symm

theorem integral_adaptedJumpOccupation_reflectedSpeedLaw
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {u : V → ℝ} (hu : G.HasFiniteEnergy u)
    (t : ℝ≥0) :
    (∫ ω, adaptedJumpOccupation PF G m u t ω ∂reflectedSpeedLaw PF m) =
      (t : ℝ) * (2 * G.Energy u) := by
  have hmean := lintegral_stationaryJumpOccupation_reflectedSpeedLaw
    h hG hm hmsum hu t
  have hfinite : (∫⁻ ω, stationaryJumpOccupation PF G m u t ω
      ∂reflectedSpeedLaw PF m) ≠ ∞ := by
    rw [hmean]
    exact ENNReal.ofReal_ne_top
  calc
    (∫ ω, adaptedJumpOccupation PF G m u t ω ∂reflectedSpeedLaw PF m) =
        ∫ ω, (stationaryJumpOccupation PF G m u t ω).toReal
          ∂reflectedSpeedLaw PF m := by
      apply integral_congr_ae
      filter_upwards [adaptedJumpOccupation_ae_eq_stationary_reflectedSpeedLaw
        h hG hm hmsum hu] with ω hω
      exact hω t
    _ = (∫⁻ ω, stationaryJumpOccupation PF G m u t ω
        ∂reflectedSpeedLaw PF m).toReal :=
      integral_toReal (measurable_stationaryJumpOccupation PF G m u t).aemeasurable
        (ae_lt_top (measurable_stationaryJumpOccupation PF G m u t) hfinite)
    _ = (t : ℝ) * (2 * G.Energy u) := by
      rw [hmean, ENNReal.toReal_ofReal]
      exact mul_nonneg t.coe_nonneg (mul_nonneg (by norm_num) (G.Energy_nonneg u))

/-- Every fixed starting vertex inherits the full-energy occupation bound
from its positive atom in the stationary speed mixture. -/
theorem mul_integral_adaptedJumpOccupation_le
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {u : V → ℝ} (hu : G.HasFiniteEnergy u)
    (t : ℝ≥0) (z : V) :
    m z * (∫ ω, adaptedJumpOccupation PF G m u t ω ∂PF.P z) ≤
      (t : ℝ) * (2 * G.Energy u) := by
  have hn : 0 ≤ᵐ[reflectedSpeedLaw PF m] adaptedJumpOccupation PF G m u t := by
    filter_upwards [] with ω
    exact ENNReal.toReal_nonneg
  have hb := integral_mono_measure (smul_start_le_reflectedSpeedLaw PF m z) hn
    (integrable_adaptedJumpOccupation_reflectedSpeedLaw h hG hm hmsum hu t)
  simpa only [integral_smul_measure, ENNReal.toReal_ofReal (hm z).le, smul_eq_mul,
    integral_adaptedJumpOccupation_reflectedSpeedLaw h hG hm hmsum hu t] using hb

end ReflectedGMS
