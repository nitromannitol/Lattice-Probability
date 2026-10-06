/-
# The one-dimensional Berry--Esseen theorem in random-variable form

`BerryEsseenOneDim.lean` states `berryEsseen_oneDim` for a family of probability **laws**
`ν : ι → Measure ℝ`, through the law `sumLaw ν` of a sum of independent variables.  The route
`scratch/pk/mvbe-route.md`, step A4, states the same theorem for independent real **random
variables** `Y : ι → Ω → ℝ` on a probability space `(Ω, P)`, as
`P {ω | ∑ i, Y i ω ≤ x}`.  This file assembles that form from the law form:

* `iIndepFun.map_fun_eq_pi_map` (`Probability/Independence/Basic.lean`) gives the joint law
  `P.map (fun ω i => Y i ω) = Measure.pi (fun i => P.map (Y i))` of independent variables;
* `Measure.map_map` then turns it into the law of the sum, which is exactly `sumLaw`;
* `Measure.map_apply_of_aemeasurable` converts `P {ω | ∑ i, Y i ω ≤ x}` into a value of that
  law;
* `variance_id_map`, `integral_map` and `integrable_map_measure` transport the variance, the third
  absolute moment and its integrability across the pushforward `P.map (Y i)`.

The conclusion is the route's A4 statement with the explicit constant `100`.
-/
import Mathlib
import LatticeProb.Prob.BerryEsseenOneDim

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace LatticeProb

/-- **Berry--Esseen, one dimension, random-variable form.**  For independent, centred real random
variables `Y i` on a probability space `(Ω, P)` with finite third absolute moments and positive
total variance `V = ∑ Var(Y i)`, the distribution function of the sum differs from that of the
centred Gaussian of variance `V` by at most `100 ∑ E|Y i|³ / V ^ (3/2)`. -/
theorem berryEsseen_oneDim_indep {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ι → Ω → ℝ)
    (hmeas : ∀ i, Measurable (Y i)) (hY : iIndepFun Y P)
    (hmean : ∀ i, ∫ ω, Y i ω ∂P = 0)
    (h3 : ∀ i, Integrable (fun ω => |Y i ω| ^ 3) P)
    (hV : 0 < ∑ i, variance (Y i) P) (x : ℝ) :
    |(P {ω | ∑ i, Y i ω ≤ x}).toReal -
        (gaussianReal 0 (∑ i, variance (Y i) P).toNNReal (Set.Iic x)).toReal|
      ≤ 100 * (∑ i, ∫ ω, |Y i ω| ^ 3 ∂P) /
          (∑ i, variance (Y i) P) ^ ((3 : ℝ) / 2) := by
  haveI hprob : ∀ i, IsProbabilityMeasure (P.map (Y i)) := fun i =>
    Measure.isProbabilityMeasure_map (hmeas i).aemeasurable
  have hf : Measurable fun ω => fun i => Y i ω := measurable_pi_iff.mpr hmeas
  have hg : Measurable fun y : ι → ℝ => ∑ i, y i :=
    Finset.measurable_sum _ fun i _ => measurable_pi_apply i
  have hlaw : P.map (fun ω => ∑ i, Y i ω) = sumLaw (fun i => P.map (Y i)) := by
    rw [show (fun ω => ∑ i, Y i ω)
        = (fun y : ι → ℝ => ∑ i, y i) ∘ (fun ω i => Y i ω) from by funext ω; rfl,
      ← Measure.map_map hg hf, hY.map_fun_eq_pi_map (fun i => (hmeas i).aemeasurable)]
    rfl
  have hvar : ∑ i, variance id (P.map (Y i)) = ∑ i, variance (Y i) P :=
    Finset.sum_congr rfl fun i _ => variance_id_map (hmeas i).aemeasurable
  have hint : ∑ i, ∫ z, |z| ^ 3 ∂(P.map (Y i)) = ∑ i, ∫ ω, |Y i ω| ^ 3 ∂P :=
    Finset.sum_congr rfl fun i _ => integral_map (hmeas i).aemeasurable
      (by fun_prop : AEStronglyMeasurable (fun z : ℝ => |z| ^ 3) (P.map (Y i)))
  have hmean' : ∀ i, ∫ z, z ∂(P.map (Y i)) = 0 := fun i => by
    rw [integral_map (hmeas i).aemeasurable
      (by fun_prop : AEStronglyMeasurable (fun z : ℝ => z) (P.map (Y i))), hmean i]
  have h3' : ∀ i, Integrable (fun z : ℝ => |z| ^ 3) (P.map (Y i)) := fun i =>
    (integrable_map_measure (by fun_prop : AEStronglyMeasurable (fun z : ℝ => |z| ^ 3)
      (P.map (Y i))) (hmeas i).aemeasurable).mpr (h3 i)
  have hV' : 0 < ∑ i, variance id (P.map (Y i)) := by rw [hvar]; exact hV
  have hone : P {ω | ∑ i, Y i ω ≤ x} = (P.map (fun ω => ∑ i, Y i ω)) (Set.Iic x) := by
    have h := Measure.map_apply_of_aemeasurable (μ := P) (f := fun ω => ∑ i, Y i ω)
      (Finset.measurable_sum (Finset.univ) fun i _ => hmeas i).aemeasurable
      (s := Set.Iic x) measurableSet_Iic
    exact h.symm
  rw [hone, hlaw, ← hvar, ← hint]
  exact berryEsseen_oneDim_of_pos (fun i => P.map (Y i)) hmean' h3' hV' x

end LatticeProb
