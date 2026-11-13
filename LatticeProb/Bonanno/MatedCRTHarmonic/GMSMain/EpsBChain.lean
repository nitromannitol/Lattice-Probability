/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.EpsBChain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSMain.T15AModel

/-!
# The annulus-disconnection / Lemma 3.8 / Lemma 3.11 assembly for a random cell family

`T15A.cellFamilyCompl_at` establishes the annulus-disconnection estimate (`ScaledGridControl`) on the dyadic
mesh family of a coupling. Every producer it calls is stated for an arbitrary `CellFamily.RandomCellFamily`; only the
inputs (Lemma 2.7 in two forms, the Peanosphere/G0 witness, Proposition 2.10, connectivity, looplessness) were taken
from the dyadic family. `cellFamily_of_inputs` is that assembly with the inputs as hypotheses, so that the same argument applies
on the band family (`EpsBFamily`) whose `k`-th member has a real mesh `θₖ ∈ (2⁻ᵏ⁻¹, 2⁻ᵏ]`:

* [18] Lemma 3.8 (`CellFamily.Lemma38AnnulusHitBad F ρ₂`): the one-scale bound from the five Proposition 2.10 tests
  (`Lemma38Source.annulus38OneScaleBadBound_of_L27_G4`) and the grid of representative scales;
* the polar-template itinerary (`CellFamily.itineraryEstimateBad_of_lemma38Bad_fixed2`, WSMP's waypoint input);
* Route M separation from the Peanosphere/G0 witness;
* The annulus-disconnection estimate (`CellFamily.cellFamily_compl_of_interfaces_bad`, lattice count `finiteGridCount_holds`);
* [18] Lemma 3.11 (`T15A.lemma311Bad_of_cellFamily`, grid annuli to every annulus).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSMain.EpsB

open MatedCRTHarmonic

/-- **The Lemma 3.8 / annulus-disconnection assembly for any random cell family** (T15A's `cellFamilyCompl_at` with its inputs
as hypotheses): Lemma 2.7 at `ρ₂` (bad-event form) and at `ρ'` (G3's `CellDiamBound`), the Peanosphere/G0 witness,
[18] Proposition 2.10 at `(ρ', 100)`, connectivity and looplessness give [18] Lemma 3.8 at `ρ₂` and the annulus-disconnection estimate
(`ScaledGridControl`) at `ρ₂`, both at the nominal scales `2⁻ᵏ`. -/
theorem cellFamily_of_inputs (F : CellFamily.RandomCellFamily) {γ q ρ₂ ρ' α27 C27 : ℝ} (hγ : γ ∈ Ioo 0 2)
    (hq : 0 < q ∧ q < 2 / (2 + γ) ^ 2) (hq1 : q < 1) (hρ₂ : 0 < ρ₂) (hρ₂ρ' : ρ₂ < ρ') (hρ' : ρ' < 1)
    (hconn : CellFamily.GraphConnected F) (hloop : CellFamily.GraphLoopless F) (hpeano : CellFamily.PeanosphereG0 F)
    (h27 : CellFamily.Lemma27CellDiamBad F q ρ₂) (hα27 : 0 < α27) (hC27 : 0 ≤ C27)
    (h27' : ∀ k, F.P {ω | GMS3.CellDiamBound (F.H k ω) ρ' (CellFamily.mesh k ^ q)}ᶜ ≤
      ENNReal.ofReal (C27 * CellFamily.mesh k ^ α27))
    (h210 : BundleSec4.Prop210At F ρ' 100) :
    CellFamily.Lemma38AnnulusHitBad F ρ₂ ∧
      ∃ χ β α p C : ℝ, 0 < χ ∧ 0 < β ∧ β < min χ q ∧ 0 < α ∧ 0 < p ∧
        ∀ k, F.P {ω | (F.H k ω).ScaledGridControl 1 (CellFamily.mesh k) χ β q ρ₂ p}ᶜ ≤
          ENNReal.ofReal (C * CellFamily.mesh k ^ α) := by
  obtain ⟨betaG4, A, α210, Cfail, hbetaG4, hα210, hA, hCfail, h210'⟩ := h210
  have hAnnulus38 : MesoModel.Annulus38OneScaleBadBound F ρ₂ :=
    Lemma38Source.annulus38OneScaleBadBound_of_L27_G4 F hρ₂ hρ₂ρ' hρ' hq.1 hq1 hbetaG4 hα210 hα27 hA hC27 hCfail
      hpeano h27' h210'
  have h38 : CellFamily.Lemma38AnnulusHitBad F ρ₂ := MesoModel.lemma38AnnulusHitBad_of_oneScaleBadBound F ρ₂ hAnnulus38
  have hSeparation := CellFamily.templateSeparation_of_peanosphereG0 F hpeano
  have hItinerary := CellFamily.itineraryEstimateBad_of_lemma38Bad_fixed2 F q ρ₂ h27 h38 hconn hloop hq.1
    (CellFamily.waypointStrongMarkovInputFixed2_holds F q ρ₂)
  exact ⟨h38, CellFamily.cellFamily_compl_of_interfaces_bad F γ ρ₂ q hγ ⟨hρ₂, hρ₂ρ'.trans hρ'⟩ hq h27 hItinerary
    (CellFamily.finiteGridCount_holds ρ₂) hconn hSeparation⟩

/-- **[18] Lemma 3.11 for any random cell family** at every `ρ < ρ₂`, from the same inputs (`cellFamily_of_inputs` and
T15A's grid-to-annulus step `T15A.lemma311Bad_of_cellFamily`). -/
theorem lemma311Bad_of_inputs (F : CellFamily.RandomCellFamily) {γ q ρ ρ₂ ρ' α27 C27 : ℝ} (hγ : γ ∈ Ioo 0 2)
    (hq : 0 < q ∧ q < 2 / (2 + γ) ^ 2) (hq1 : q < 1) (hρρ₂ : ρ < ρ₂) (hρ₂ : 0 < ρ₂) (hρ₂ρ' : ρ₂ < ρ')
    (hρ' : ρ' < 1) (hconn : CellFamily.GraphConnected F) (hloop : CellFamily.GraphLoopless F)
    (hpeano : CellFamily.PeanosphereG0 F) (h27 : CellFamily.Lemma27CellDiamBad F q ρ₂) (hα27 : 0 < α27) (hC27 : 0 ≤ C27)
    (h27' : ∀ k, F.P {ω | GMS3.CellDiamBound (F.H k ω) ρ' (CellFamily.mesh k ^ q)}ᶜ ≤
      ENNReal.ofReal (C27 * CellFamily.mesh k ^ α27))
    (h210 : BundleSec4.Prop210At F ρ' 100) :
    T15A.Lemma311Bad F ρ := by
  obtain ⟨-, χ, β, α, p, C, hχ, hβ, hβmin, hα, hp, h26⟩ :=
    cellFamily_of_inputs F hγ hq hq1 hρ₂ hρ₂ρ' hρ' hconn hloop hpeano h27 hα27 hC27 h27' h210
  exact T15A.lemma311Bad_of_cellFamily F hconn hβ (lt_of_lt_of_le hβmin (min_le_left _ _))
    (lt_of_lt_of_le hβmin (min_le_right _ _)) hα hp hρρ₂ h26

end MatedCRTHarmonic.GMSMain.EpsB
