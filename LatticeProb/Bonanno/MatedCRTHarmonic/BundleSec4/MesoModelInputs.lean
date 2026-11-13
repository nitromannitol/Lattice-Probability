/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.BundleSec4.MesoModelInputs at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.BundleSec4.ZeroConeCase0
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48CanonicalLintegral
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cO.Lemma49Canonical
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cS.Lemma49Complete
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cQ.ThickReaders

/-!
# The mated-CRT map conclusion from the remaining named facts of [18] §4 (final composition)

The chain starts with `GMS4.Canonical.prop48ZeroConeLintegral_of_H1_H4`, the lower-integral form of [18] Proposition 4.8 for the 0-cone curve `η₀`. Its inputs are H1, H2, and H4; H3 follows from H2 by reconstruction. This gives
`BundleSec4.zeroConeCase0At_of_lintegral` (the `ZeroConeCase0At D (13/16)`, windows from the unconditional 0-cone
Proposition 4.5) then `prop410At_of_inputs` (with `Lemma43Measurable D`) then `BundleSec4.Prop410AtForAllBundles`, and finally both
frozen v3 conclusions.

* `H1H4ForAllBundles` — for every frozen coupling on a standard Borel space: the first-moment input, H2, H4 at some admissible
  `q, ζ`, and the `Lemma43Measurable D`; the companion map conclusion,
  `exists_cellModel_of_matingOfTrees_of_H1H4`;
* `bundle_H1_of_locality` — the first-moment input from the locality argument's two `ZeroConeRescaledLocality` instances;
  `bundle_H1` — the first-moment input unconditionally, at the `GMS4cS.lemma49_zeroConeRescaledLocality_pair`;
* **`ThreeInputsForAllBundles`** — the three remaining named facts, for every frozen coupling: H2
  `ThickGMCReaders D`, H4 `Prop48GoodEventSecondMomentInput D hγ q ζ (bundle_H1 D hγ hζ)`, `GMS4FO.Lemma43Measurable D`;
  the companion map conclusion, `exists_cellModel_of_matingOfTrees_of_threeInputs`;
* **`TwoInputsForAllBundles`** — H2 plugged in (`GMS4cQ.thickGMCReaders D hγ`): the two remaining named
  facts, H4 at `H1 := GMS4cS.lemma49ConditionalMoments` and `GMS4FO.Lemma43Measurable D`;
  **the companion map conclusion**, `exists_cellModel_of_matingOfTrees_of_twoInputs`.

The input types are referenced by name and parameter list only, so restatements that keep these lists need only a
rebuild.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.BundleSec4

open MatedCRTHarmonic

/-! ### H1, H2, H4 + `Lemma43Measurable` -/

/-! ### H1 from Lemma 4.9 -/

section Bundle

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {T : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- the range `ζ ∈ (0, q/100)` gives the locality argument's `4ζ < q`. -/
theorem bundle_four_zeta_lt {q ζ : ℝ} (hζ : ζ ∈ Ioo (0 : ℝ) (q / 100)) : 4 * ζ < q := by
  linarith [hζ.1, hζ.2]

/-- **the first-moment input, unconditionally**: the `GMS4cS.lemma49ConditionalMoments` (the locality argument's
`lemma49ConditionalMoments_of_locality` at `GMS4cS.lemma49_zeroConeRescaledLocality_pair`, d8cc183f5). -/
def bundle_H1
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' T ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) {q ζ : ℝ} (hζ : ζ ∈ Ioo (0 : ℝ) (q / 100)) :
    ∀ ρ : ℝ, ρ ∈ Ioo (0 : ℝ) 1 → GMS4.Canonical.Lemma49ConditionalMoments D hγ q ζ ρ :=
  fun _ hρ => GMS4cS.lemma49ConditionalMoments D hγ hρ hζ.1 (bundle_four_zeta_lt hζ)

end Bundle

/-! ### The three remaining named facts -/

/-! ### H2 plugged in: the two remaining named facts -/

end MatedCRTHarmonic.BundleSec4
