/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.JumpOccupationIntegrability at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.StationaryJumpOccupation

/-! Positive speed mass upgrades the stationary jump-occupation estimate to
finite expectation under each starting law, not just almost-sure finiteness. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace ReflectedGMS
open ReflectedWalk

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

theorem smul_start_le_reflectedSpeedLaw (PF : ProcessFamily V) (m : V → ℝ) (z : V) :
    ENNReal.ofReal (m z) • PF.P z ≤ reflectedSpeedLaw PF m := by
  unfold reflectedSpeedLaw
  rw [Measure.comp_eq_sum_of_countable]
  simp only [vertexSpeedMeasure_singleton]
  exact Measure.le_sum (fun x => ENNReal.ofReal (m x) • PF.P x) z

theorem mul_lintegral_stationaryJumpOccupation_le
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v => G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {u : V → ℝ} (hu : G.HasFiniteEnergy u)
    (t : ℝ≥0) (z : V) :
    ENNReal.ofReal (m z) *
      (∫⁻ ω, stationaryJumpOccupation PF G m u t ω ∂PF.P z) ≤
        ENNReal.ofReal ((t : ℝ) * (2 * G.Energy u)) := by
  have hb := lintegral_mono' (smul_start_le_reflectedSpeedLaw PF m z)
    (le_refl (stationaryJumpOccupation PF G m u t))
  simpa only [lintegral_smul_measure, smul_eq_mul,
    lintegral_stationaryJumpOccupation_reflectedSpeedLaw h hG hm hmsum hu t] using hb

theorem lintegral_stationaryJumpOccupation_lt_top
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v => G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {u : V → ℝ} (hu : G.HasFiniteEnergy u)
    (t : ℝ≥0) (z : V) :
    (∫⁻ ω, stationaryJumpOccupation PF G m u t ω ∂PF.P z) < ∞ := by
  have hb := (mul_lintegral_stationaryJumpOccupation_le h hG hm hmsum hu t z).trans_lt
    ENNReal.ofReal_lt_top
  by_contra hn
  have ht : (∫⁻ ω, stationaryJumpOccupation PF G m u t ω ∂PF.P z) = ∞ :=
    top_le_iff.mp (not_lt.mp hn)
  rw [ht, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (hm z)).ne'] at hb
  exact (lt_irrefl _ hb)

theorem integrable_stationaryJumpOccupation_toReal
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v => G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {u : V → ℝ} (hu : G.HasFiniteEnergy u)
    (t : ℝ≥0) (z : V) :
    Integrable (fun ω => (stationaryJumpOccupation PF G m u t ω).toReal) (PF.P z) :=
  integrable_toReal_of_lintegral_ne_top
    (measurable_stationaryJumpOccupation PF G m u t).aemeasurable
    (lintegral_stationaryJumpOccupation_lt_top h hG hm hmsum hu t z).ne

end ReflectedGMS
