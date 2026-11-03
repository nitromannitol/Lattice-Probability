/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.MarkovFinal at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.MarkovAsm
import LatticeProb.Bonanno.LQGMetric.Blueprint.LMResults
import LatticeProb.Bonanno.LQGMetric.Field.MarkovGermVer3F

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# LM Lemma 2.1 (`Blueprint.LMLem2_1`), final assembly

After decision D61 the harmonic clause of `Blueprint.LMLem2_1` is almost sure, so
`Blueprint.LMLem2_1` is definitionally `MarkovAsm.LMLem2_1AE` (LM = arXiv:1905.00380,
Lemma 2.1, l. 425–429; proven in GMSh = arXiv:1807.07511, Lemma 2.2).

* `lmLem2_1_of_germ` : `Blueprint.LMLem2_1` from the germ step for unbounded `V`
  (`mem_range_cmIso_of_orth_unbdd`);
* `lmLem2_1` : `Blueprint.LMLem2_1`, unconditional (germ step `mem_range_cmIso_of_orth_unbdd`,
  `Field/MarkovGermVer3F.lean`);
* `lmLem2_1_bdd` : the bounded-`V` case, unconditional.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric TopologicalSpace InnerProductSpace
open scoped RealInnerProductSpace

namespace LQGMetric
namespace MarkovFinal

open MarkovZB MarkovExt MarkovVer2 MarkovGermVer MarkovAsm Blueprint QuantumZipper QuantumZipper.K3

/-- **LM Lemma 2.1** from the germ step for unbounded `V`. -/
theorem lmLem2_1_of_germ
    (hD : ∀ {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
      {h : Ω → DistC} (hh : IsNormalizedWPGFF h P) {V : Opens ℂ},
      Disjoint (V : Set ℂ) (sphere 0 1) → ∀ {ε : ℝ}, 0 < ε →
      ∀ v : gradClosure ((⊤ : Opens ℂ) : Set ℂ) (zeroSpace ((⊤ : Opens ℂ) : Set ℂ)),
      (∀ u ∈ germSpan hh.1 (Blueprint.nbhdO ε (V : Set ℂ)ᶜ), ⟪u, cmIso hh.1 ⊤ v⟫ = 0) →
        cmIso hh.1 ⊤ v ∈ Set.range (cmIso hh.1 V)) :
    Blueprint.LMLem2_1 :=
  lmLem2_1AE_of_germ hD

/-- **LM Lemma 2.1** (LM Lemma 2.1; GMSh Lemma 2.2), unconditional. -/
theorem lmLem2_1 : Blueprint.LMLem2_1 :=
  lmLem2_1_of_germ (by
    intro Ω _ P _ h hh V hV ε hε v hv
    exact MarkovGermVer.mem_range_cmIso_of_orth_unbdd hh hV hε v hv)

end MarkovFinal
end LQGMetric
