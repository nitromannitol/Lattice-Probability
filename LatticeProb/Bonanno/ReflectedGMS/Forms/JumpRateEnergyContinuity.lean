/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.JumpRateEnergyContinuity at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Analysis.WeightedGradient
import LatticeProb.Bonanno.ReflectedGMS.Forms.StationaryJumpOccupation

/-!
# Full-energy continuity of the ordinary-edge jump rate

The canonical real square-increment rate is continuous from the full finite-energy
domain to `L¹(vertexSpeedMeasure m)`.  The estimate is the edge polarization
identity followed by Cauchy–Schwarz in the normalized weighted-gradient space.

With the repository normalization `Energy = (1 / 2) * ∑_(x,y) gradSq`, the
constant is `2`.  This file is analytic only: it makes no process-limit or
stochastic-bracket assertion.
-/

set_option autoImplicit false

open scoped BigOperators ENNReal
open MeasureTheory

namespace ReflectedGMS

open ReflectedWalk

universe u_1
variable {V : Type u_1} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [DecidableEq V]

private theorem weightedGradient_norm_eq_sqrt_energy
    (G : ConductanceGraph V) {f : V → ℝ} (hf : G.HasFiniteEnergy f) :
    ‖weightedGradient G f hf‖ = Real.sqrt (G.Energy f) := by
  apply (Real.sqrt_sq (norm_nonneg _)).symm.trans
  rw [weightedGradient_norm_sq G f hf]

private theorem summable_abs_gradSq_sub
    (G : ConductanceGraph V) {u v : V → ℝ}
    (hu : G.HasFiniteEnergy u) (hv : G.HasFiniteEnergy v) :
    Summable (fun p : V × V ↦ |G.gradSq u p - G.gradSq v p|) := by
  apply Summable.of_nonneg_of_le (fun _ ↦ abs_nonneg _)
    (fun p ↦ by
      calc
        |G.gradSq u p - G.gradSq v p| ≤
            |G.gradSq u p| + |G.gradSq v p| := abs_sub _ _
        _ = G.gradSq u p + G.gradSq v p := by
          rw [abs_of_nonneg (G.gradSq_nonneg u p),
            abs_of_nonneg (G.gradSq_nonneg v p)])
    (Summable.add hu hv)

private theorem tsum_abs_gradSq_sub_le
    (G : ConductanceGraph V) {u v : V → ℝ}
    (hu : G.HasFiniteEnergy u) (hv : G.HasFiniteEnergy v) :
    (∑' p : V × V, |G.gradSq u p - G.gradSq v p|) ≤
      2 * Real.sqrt (G.Energy (u - v)) * Real.sqrt (G.Energy (u + v)) := by
  let hsub : G.HasFiniteEnergy (u - v) := hu.sub hv
  let hadd : G.HasFiniteEnergy (u + v) := hu.add hv
  have hholder := lp.tsum_mul_le_mul_norm'
    (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
    (by simpa using Real.HolderConjugate.two_two)
    (weightedGradient G (u - v) hsub) (weightedGradient G (u + v) hadd)
  have hedge : ∀ p : V × V,
      |G.gradSq u p - G.gradSq v p| =
        2 * ‖weightedGradient G (u - v) hsub p‖ *
          ‖weightedGradient G (u + v) hadd p‖ := by
    intro p
    have hc : 0 ≤ G.c p.1 p.2 / 2 := div_nonneg (G.c_nonneg _ _) (by norm_num)
    have hs : Real.sqrt (G.c p.1 p.2 / 2) * Real.sqrt (G.c p.1 p.2 / 2) =
        G.c p.1 p.2 / 2 := by
      rw [← pow_two, Real.sq_sqrt hc]
    have hraw : G.gradSq u p - G.gradSq v p =
        2 * weightedGradientCoord G (u - v) p *
          weightedGradientCoord G (u + v) p := by
      unfold weightedGradientCoord ConductanceGraph.gradSq
      simp only [Pi.sub_apply, Pi.add_apply]
      calc
        G.c p.1 p.2 * (u p.2 - u p.1) ^ 2 -
            G.c p.1 p.2 * (v p.2 - v p.1) ^ 2 =
            G.c p.1 p.2 *
              ((u p.2 - v p.2) - (u p.1 - v p.1)) *
              ((u p.2 + v p.2) - (u p.1 + v p.1)) := by ring
        _ = 2 * (Real.sqrt (G.c p.1 p.2 / 2) *
              Real.sqrt (G.c p.1 p.2 / 2)) *
              (((u p.2 - v p.2) - (u p.1 - v p.1)) *
                ((u p.2 + v p.2) - (u p.1 + v p.1))) := by
            rw [hs]
            ring
        _ = 2 * (Real.sqrt (G.c p.1 p.2 / 2) *
              ((u p.2 - v p.2) - (u p.1 - v p.1))) *
              (Real.sqrt (G.c p.1 p.2 / 2) *
                ((u p.2 + v p.2) - (u p.1 + v p.1))) := by ring
    rw [hraw]
    change |2 * weightedGradientCoord G (u - v) p *
        weightedGradientCoord G (u + v) p| =
      2 * |weightedGradientCoord G (u - v) p| *
        |weightedGradientCoord G (u + v) p|
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    (∑' p : V × V, |G.gradSq u p - G.gradSq v p|) =
        ∑' p : V × V, 2 * ‖weightedGradient G (u - v) hsub p‖ *
          ‖weightedGradient G (u + v) hadd p‖ := tsum_congr hedge
    _ = 2 * (∑' p : V × V, ‖weightedGradient G (u - v) hsub p‖ *
          ‖weightedGradient G (u + v) hadd p‖) := by
      simp_rw [mul_assoc]
      rw [tsum_mul_left]
    _ ≤ 2 * (‖weightedGradient G (u - v) hsub‖ *
          ‖weightedGradient G (u + v) hadd‖) :=
      mul_le_mul_of_nonneg_left hholder (by positivity)
    _ = 2 * Real.sqrt (G.Energy (u - v)) *
          Real.sqrt (G.Energy (u + v)) := by
      rw [weightedGradient_norm_eq_sqrt_energy G hsub,
        weightedGradient_norm_eq_sqrt_energy G hadd]
      ring

private theorem summable_speed_mul_abs_vertexCarreDuChamp_sub
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ x, 0 < m x)
    {u v : V → ℝ} (hu : G.HasFiniteEnergy u) (hv : G.HasFiniteEnergy v) :
    Summable (fun x ↦ m x * |vertexCarreDuChamp G m u x -
      vertexCarreDuChamp G m v x|) := by
  have h := (summable_speed_mul_vertexCarreDuChamp G m hm hu).sub
    (summable_speed_mul_vertexCarreDuChamp G m hm hv)
  apply h.abs.congr
  intro x
  rw [← mul_sub, abs_mul, abs_of_pos (hm x)]

private theorem tsum_speed_mul_abs_vertexCarreDuChamp_sub_le
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ x, 0 < m x)
    {u v : V → ℝ} (hu : G.HasFiniteEnergy u) (hv : G.HasFiniteEnergy v) :
    (∑' x : V, m x * |vertexCarreDuChamp G m u x -
      vertexCarreDuChamp G m v x|) ≤
      2 * Real.sqrt (G.Energy (u - v)) * Real.sqrt (G.Energy (u + v)) := by
  have hedge := summable_abs_gradSq_sub G hu hv
  have hrow : ∀ x : V,
      m x * |vertexCarreDuChamp G m u x - vertexCarreDuChamp G m v x| ≤
        ∑' y : V, |G.gradSq u (x, y) - G.gradSq v (x, y)| := by
    intro x
    rw [show m x * |vertexCarreDuChamp G m u x - vertexCarreDuChamp G m v x| =
        |m x * vertexCarreDuChamp G m u x -
          m x * vertexCarreDuChamp G m v x| by
      rw [← mul_sub, abs_mul, abs_of_pos (hm x)]]
    rw [
      speed_mul_vertexCarreDuChamp G m hm hu x,
      speed_mul_vertexCarreDuChamp G m hm hv x]
    rw [← (hu.prod_factor x).tsum_sub (hv.prod_factor x)]
    simpa only [Real.norm_eq_abs, abs_abs] using
      norm_tsum_le_tsum_norm (((hu.prod_factor x).sub (hv.prod_factor x)).norm)
  calc
    (∑' x : V, m x * |vertexCarreDuChamp G m u x -
        vertexCarreDuChamp G m v x|) ≤
        ∑' x : V, ∑' y : V, |G.gradSq u (x, y) - G.gradSq v (x, y)| := by
      have hrows : Summable (fun x : V ↦
          ∑' y : V, |G.gradSq u (x, y) - G.gradSq v (x, y)|) :=
        (summable_prod_of_nonneg
          (fun p : V × V ↦ abs_nonneg (G.gradSq u p - G.gradSq v p))).mp hedge |>.2
      exact (summable_speed_mul_abs_vertexCarreDuChamp_sub G m hm hu hv).tsum_le_tsum
        hrow hrows
    _ = ∑' p : V × V, |G.gradSq u p - G.gradSq v p| := hedge.tsum_prod.symm
    _ ≤ 2 * Real.sqrt (G.Energy (u - v)) * Real.sqrt (G.Energy (u + v)) :=
      tsum_abs_gradSq_sub_le G hu hv

/-- The difference of two canonical real ordinary-edge rates is speed-`L¹`
integrable on the full finite-energy domain. -/
theorem integrable_stateVertexCarreDuChamp_toReal_sub
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ x, 0 < m x)
    {u v : V → ℝ} (hu : G.HasFiniteEnergy u) (hv : G.HasFiniteEnergy v) :
    Integrable (fun x : V ↦
      (stateVertexCarreDuChamp G m u (some x)).toReal -
      (stateVertexCarreDuChamp G m v (some x)).toReal)
      (vertexSpeedMeasure m) := by
  simp only [stateVertexCarreDuChamp,
    ENNReal.toReal_ofReal (vertexCarreDuChamp_nonneg G m hm _ _)]
  change Integrable (fun x : V ↦
    vertexCarreDuChamp G m u x - vertexCarreDuChamp G m v x)
    (vertexSpeedMeasure m)
  change Integrable _
    (Measure.sum (fun x ↦ ENNReal.ofReal (m x) • Measure.dirac x))
  apply integrable_sum_dirac (fun x ↦ ENNReal.ofReal_ne_top)
  simpa only [ENNReal.toReal_ofReal (hm _).le, norm_mul,
    Real.norm_of_nonneg (hm _).le, Real.norm_eq_abs] using
      summable_speed_mul_abs_vertexCarreDuChamp_sub G m hm hu hv

/-- Full-domain `L¹(vertexSpeedMeasure m)` continuity of the canonical real
ordinary-edge square-increment rate.  The factor `2` reflects the half
ordered-edge normalization of `Energy`. -/
theorem integral_norm_stateVertexCarreDuChamp_toReal_sub_le
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ x, 0 < m x)
    {u v : V → ℝ} (hu : G.HasFiniteEnergy u) (hv : G.HasFiniteEnergy v) :
    (∫ x : V, ‖(stateVertexCarreDuChamp G m u (some x)).toReal -
        (stateVertexCarreDuChamp G m v (some x)).toReal‖
      ∂vertexSpeedMeasure m) ≤
      2 * Real.sqrt (G.Energy (u - v)) * Real.sqrt (G.Energy (u + v)) := by
  have hi := (integrable_stateVertexCarreDuChamp_toReal_sub G m hm hu hv).norm
  rw [integral_countable hi]
  simp only [measureReal_def, vertexSpeedMeasure_singleton,
    ENNReal.toReal_ofReal (hm _).le, smul_eq_mul, stateVertexCarreDuChamp,
    ENNReal.toReal_ofReal (vertexCarreDuChamp_nonneg G m hm _ _),
    Real.norm_eq_abs]
  exact tsum_speed_mul_abs_vertexCarreDuChamp_sub_le G m hm hu hv

end ReflectedGMS
