/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.ResolventCoreInput at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.ResolventCoreMartingale
import LatticeProb.Bonanno.ReflectedGMS.Forms.BoundedResolventSquareMartingale

/-!
# Countable resolvent-core coordinates as bounded resolvent inputs

A finite rational vertex coordinate is a bounded function on the vertex set.
This module identifies its existing finite weighted-indicator sum with the
canonical weighted value of that function, and then specializes the checked
bounded-input square martingale to every countable resolvent-core coordinate.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace ReflectedGMS

open ReflectedWalk ReflectedWalk.Theorem16 FullNetworkForm

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

/-- Every coefficient of a finite rational vertex coordinate is bounded by
the sum of the absolute values of all its coefficients. -/
theorem countableResolventCoreIndex_abs_le
    (q : CountableResolventCoreIndex V) (x : V) :
    |(q x : ℝ)| ≤ countableResolventCoreBound q := by
  classical
  unfold countableResolventCoreBound Finsupp.sum
  by_cases hx : x ∈ q.support
  · exact Finset.single_le_sum
      (fun y hy ↦ abs_nonneg ((q y : ℚ) : ℝ)) hx
  · rw [Finsupp.notMem_support_iff.mp hx]
    simp only [Rat.cast_zero, abs_zero]
    exact Finset.sum_nonneg fun y hy ↦ abs_nonneg ((q y : ℚ) : ℝ)

/-- A finite rational vertex coordinate is in speed `L²` under summable
positive speed. -/
theorem countableResolventCoreIndex_hasSpeedL2
    {m : V → ℝ} (hm : ∀ v, 0 < m v) (hmsum : Summable m)
    (q : CountableResolventCoreIndex V) :
    HasSpeedL2 m (fun x ↦ (q x : ℝ)) :=
  hasSpeedL2_of_abs_le hm hmsum (countableResolventCoreIndex_abs_le q)

/-- The original finite sum of weighted vertex indicators is exactly the
weighted value of the corresponding bounded rational coordinate function. -/
theorem countableResolventCoreInput_eq_weightedValue
    (G : ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (hmsum : Summable m)
    (q : CountableResolventCoreIndex V) :
    countableResolventCoreInput G m q =
      weightedValue m (fun x ↦ (q x : ℝ))
        (countableResolventCoreIndex_hasSpeedL2 hm hmsum q) := by
  classical
  apply lp.ext
  funext x
  unfold countableResolventCoreInput Finsupp.sum
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul,
    Pi.smul_apply, smul_eq_mul, weightedValue_apply]
  by_cases hx : x ∈ q.support
  · rw [Finset.sum_eq_single x]
    · simp [ConductanceGraph.indic, mul_comm]
    · intro y hy hyx
      simp [ConductanceGraph.indic, Ne.symm hyx]
    · exact fun h ↦ (h hx).elim
  · have hqx : q x = 0 := Finsupp.notMem_support_iff.mp hx
    rw [Finset.sum_eq_zero]
    · simp [hqx]
    · intro y hy
      have hyx : y ≠ x := by
        intro h
        subst y
        exact hx hy
      simp [ConductanceGraph.indic, Ne.symm hyx]

/-- Consequently the existing countable-core feature is the checked
one-resolvent of its bounded rational coordinate input. -/
theorem countableResolventCoreFeature_eq_oneResolventFunction
    (G : ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (hmsum : Summable m)
    (q : CountableResolventCoreIndex V) :
    countableResolventCoreFeature G m q =
      oneResolventFunction G m
        (weightedValue m (fun x ↦ (q x : ℝ))
          (countableResolventCoreIndex_hasSpeedL2 hm hmsum q)) := by
  unfold countableResolventCoreFeature
  rw [countableResolventCoreInput_eq_weightedValue G m hm hmsum q]

/-- On a countable-core input, the bounded-resolvent drift is exactly
`2 u_q (u_q - q)`, with `u_q` the existing countable-core feature. -/
theorem boundedResolventSquareDrift_eq_countableResolventCore
    (G : ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (hmsum : Summable m)
    (q : CountableResolventCoreIndex V) (x : V) :
    boundedResolventSquareDrift G m (fun y ↦ (q y : ℝ))
        (countableResolventCoreIndex_hasSpeedL2 hm hmsum q) (some x) =
      2 * countableResolventCoreFeature G m q x *
        (countableResolventCoreFeature G m q x - (q x : ℝ)) := by
  unfold boundedResolventSquareDrift
  simp only [Option.elim_some]
  rw [countableResolventCoreFeature_eq_oneResolventFunction G m hm hmsum q]

/-- The bounded-resolvent square martingale specialized to every finite
rational coordinate in the countable full-form core. -/
theorem countableResolventCoreSquareMartingale_isMartingale
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (q : CountableResolventCoreIndex V) (z : V) :
    Martingale
      (boundedResolventSquareMartingale PF G m (fun x ↦ (q x : ℝ))
        (countableResolventCoreIndex_hasSpeedL2 hm hmsum q))
      PF.naturalFiltration (PF.P z) := by
  simpa only using boundedResolventSquareMartingale_isMartingale
    h hG hm hmsum (fun x ↦ (q x : ℝ))
      (countableResolventCoreIndex_abs_le q) z

end ReflectedGMS
