/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cM.BundleSec4Link at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cM.Bundle
import LatticeProb.Bonanno.MatedCRTHarmonic.BundleSec4.Lemma43M

/-!
# the `Lemma43MeasurableM` and the mated-CRT map conclusion from the H4 alone

Source: [18], Lemma 4.3.

The bundle construction (`BundleSec4/Lemma43M.lean`) restricted the named input `GMS4FO.Lemma43Measurable` to the admissible test data
The Proposition 4.10 argument actually uses (`BundleSec4.Lemma43MeasurableM`) and re-ran the chain from it. This file produces it:

* **`lemma43MeasurableM_holds`**: `BundleSec4.Lemma43MeasurableM D` for every frozen coupling with `γ ∈ (0, 2)`
  (from `lemma43MeasurableGuarded_holds`: open sets are Borel, a test continuous on an open domain is
  a.e.-measurable there);
* `H4ForAllBundles` (the first conjunct of the `TwoInputsMForAllBundles`: the H4 at the H1, owner
  the second-moment estimate), `twoInputsMForAllBundles_of_H4`;
* **the companion map conclusion**, `exists_cellModel_of_matingOfTrees_of_H4`: both conditional v3
  conclusions of the mated-CRT map conclusion from `H4ForAllBundles` alone.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology TopologicalSpace
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMS4cM

open MatedCRTHarmonic LQGMetric MatedCRTHarmonic.MatedCRT

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- **the restricted Lemma 4.3 measurability holds on every frozen coupling.** -/
theorem lemma43MeasurableM_holds
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) (hγ : γ ∈ Ioo (0 : ℝ) 2) :
    BundleSec4.Lemma43MeasurableM D :=
  fun V hV1 ε Dm g A tol R r hε hDo hgc _ _ _ hRo hDR hr hRV =>
    lemma43MeasurableGuarded_holds D hγ V hV1 ε Dm g A tol R r hε hr hDR hRV hDo.measurableSet
      hRo.measurableSet (hgc.aemeasurable hDo.measurableSet)

end Coupling

end MatedCRTHarmonic.GMS4cM
