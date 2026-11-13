/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.VertexCarreDuChamp at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.CompactVertexSpace
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Sum
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import LatticeProb.Bonanno.ReflectedGMS.Forms.FullNetworkForm
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import LatticeProb.Bonanno.ReflectedGMS.Analysis.ExtendedEnergy
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The ordinary-edge carré du champ on vertices

For a positive speed measure `m`, this file records the square-increment rate
of the already defined conductance jump kernel at an original vertex.  Its
weighted total is twice `ConductanceGraph.Energy`, since that energy is half
the sum over ordered pairs.

These are analytic identities on the full finite-energy domain.  No stochastic
bracket identification or assertion about compactification-boundary jumps is
made here.
-/

set_option autoImplicit false

open scoped BigOperators

namespace ReflectedGMS

variable {V : Type*}

/-- The ordinary-edge square-increment rate at a vertex.  The summand is the
singleton jump rate `c(x,y) / m(x)` from `CompactVertexSpace.jumpRateKernel`.
-/
noncomputable def vertexCarreDuChamp
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ) (u : V → ℝ) (x : V) : ℝ :=
  ∑' y : V, (G.c x y / m x) * (u y - u x) ^ 2

/-- Finite full energy implies summability of every square-increment-rate row.
No finite-support or core approximation is used. -/
theorem summable_vertexCarreDuChamp_row
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    {u : V → ℝ} (hu : G.HasFiniteEnergy u) (x : V) :
    Summable (fun y : V ↦ (G.c x y / m x) * (u y - u x) ^ 2) := by
  have hrow : Summable (fun y : V ↦ G.gradSq u (x, y)) := hu.prod_factor x
  apply (hrow.div_const (m x)).congr
  intro y
  simp only [ReflectedWalk.ConductanceGraph.gradSq]
  ring

/-- The square-increment rate is nonnegative for positive speed. -/
theorem vertexCarreDuChamp_nonneg
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ x, 0 < m x) (u : V → ℝ) (x : V) :
    0 ≤ vertexCarreDuChamp G m u x := by
  apply tsum_nonneg
  intro y
  exact mul_nonneg (div_nonneg (G.c_nonneg x y) (hm x).le) (sq_nonneg _)

/-- Multiplying a row rate by its speed recovers the ordered energy row. -/
theorem speed_mul_vertexCarreDuChamp
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ x, 0 < m x) {u : V → ℝ} (hu : G.HasFiniteEnergy u) (x : V) :
    m x * vertexCarreDuChamp G m u x =
      ∑' y : V, G.gradSq u (x, y) := by
  rw [vertexCarreDuChamp,
    ← (summable_vertexCarreDuChamp_row G m hu x).tsum_mul_left (m x)]
  apply tsum_congr
  intro y
  simp only [ReflectedWalk.ConductanceGraph.gradSq]
  field_simp [(hm x).ne']

/-- The speed-weighted vertex rates are summable on the full finite-energy
domain; this is derived from `HasFiniteEnergy`. -/
theorem summable_speed_mul_vertexCarreDuChamp
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ x, 0 < m x) {u : V → ℝ} (hu : G.HasFiniteEnergy u) :
    Summable (fun x : V ↦ m x * vertexCarreDuChamp G m u x) := by
  have hrows : Summable (fun x : V ↦ ∑' y : V, G.gradSq u (x, y)) :=
    (summable_prod_of_nonneg (fun p ↦ G.gradSq_nonneg u p)).mp hu |>.2
  exact hrows.congr (fun x ↦ (speed_mul_vertexCarreDuChamp G m hm hu x).symm)

/-- Exact global normalization: `Energy` is half the ordered-pair sum, so the
speed-weighted total square-increment rate is `2 * Energy`. -/
theorem tsum_speed_mul_vertexCarreDuChamp
    (G : ReflectedWalk.ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ x, 0 < m x) {u : V → ℝ} (hu : G.HasFiniteEnergy u) :
    (∑' x : V, m x * vertexCarreDuChamp G m u x) = 2 * G.Energy u := by
  calc
    (∑' x : V, m x * vertexCarreDuChamp G m u x) =
        ∑' x : V, ∑' y : V, G.gradSq u (x, y) := by
      apply tsum_congr
      exact speed_mul_vertexCarreDuChamp G m hm hu
    _ = ∑' p : V × V, G.gradSq u p := hu.tsum_prod.symm
    _ = 2 * G.Energy u := G.tsum_gradSq_eq u

end ReflectedGMS
