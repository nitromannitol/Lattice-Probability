/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.BundleSec4.MesoModelFinal at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.BundleSec4.MesoModelH4
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4O.Prop48OTripleH4Proof

/-!
# The mated-CRT map conclusions from the coupling assumptions

The last named fact of the chain, the triple-centred good-event second moment, is proved for arbitrary
H1, H2: `GMS4O.p48o_goodEventSecondMomentTriple_holds D hγ hq hζ H1 H2` (`GMS4O/Prop48OTripleH4Proof.lean`).
Instantiated at admissible parameters (`bundle_exists_admissible_qζ`), at the first-moment input (`bundle_H1`, [18] Lemma 4.9)
and at the second local input (`GMS4cQ.thickGMCReaders`), it gives `BundleSec4.H4TripleForAllBundles`, hence the two conclusions below:

* **`exists_cellModel_of_matingOfTrees_holds`** — the frozen v3 type of `exists_cellModel_of_matingOfTrees`;
* The companion map conclusion for the mated-CRT graph.

Chain: the second-moment input → `GMS4.Canonical.prop48ZeroConeLintegral_of_tripleH4` ([18] Prop 4.8 on the 0-cone,
lower-integral form) → `BundleSec4.zeroConeCase0At_of_lintegral` (with the unconditional 0-cone Prop 4.5) →
`GMS4cM.lemma43MeasurableM_holds`, `BundleSec4.prop410At_of_inputsM` (the per-root chain through Cases 1–4) → `BundleSec4.Prop410AtForAllBundles` ([18] Prop 4.10 at `(3/4, 100)`) → `BundleSec4.prop210At_of_prop410At` ([18] Prop 2.10
via (4.20)) → `hAnnulus38`, `hREC` → `MesoModel.FinalAssembly` → the frozen anchors.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.BundleSec4

open MatedCRTHarmonic

/-- **The last named fact holds**: the triple-centred H4 at the first-moment input, for every frozen coupling. -/
theorem h4TripleForAllBundles_holds : H4TripleForAllBundles := by
  intro γ hγ Ω mΩ hstd P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm D
  obtain ⟨q, ζ, hq, hζ⟩ := bundle_exists_admissible_qζ hγ
  exact ⟨q, ζ, hq, hζ, GMS4O.p48o_goodEventSecondMomentTriple_holds D hγ hq hζ (bundle_H1 D hγ hζ)
    (GMS4cQ.thickGMCReaders D hγ)⟩

end MatedCRTHarmonic.BundleSec4
