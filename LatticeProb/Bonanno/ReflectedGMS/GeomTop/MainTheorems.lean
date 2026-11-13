/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.GeomTop.MainTheorems at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.GeomTop.HypothesisTransfer
import LatticeProb.Bonanno.ReflectedGMS.GeomTop.UniqueCellCovariance
import LatticeProb.Bonanno.ReflectedGMS.GeneralMainTheorems
import Mathlib.Util.AssertNoSorry

/-!
# Theorems 1.2 and 1.3 of the geometric-topology revision, from the upstream coding facts

Statements: `GeomTop.GeomHarmonicCoordinateMainTheorem`, `GeomTop.GeomReflectedInvarianceMainTheorem`
(`GeomTop/Statement.lean`).  Each is a short application of the proved general-cell theorem
(`GeneralMainTheorems.generalHarmonicCoordinateMainTheorem`,
`GeneralMainTheorems.generalReflectedInvarianceMainTheorem`) to the coordinate law
`P := μ.map coords`, with the hypotheses transferred by `GeomTop/HypothesisTransfer.lean`, and
`ν := validLaw P hV`, whose coordinate pushforward is `P` (`EnvironmentLaws.map_validLaw`).  The
end-image clause of Theorem 1.3 is taken verbatim from the general theorem.  The harmonic coordinate
of the general theorem is renormalized so that (1.10) holds wherever `H_u` is uniquely defined
(`GeomTop/UniqueCellCovariance.lean`), and almost every environment's coordinates are general valid
because the coordinate law is carried by general environments (`ae_validGeneral_coords`).

The properties of the coding `coords` proved in other packets enter as explicit hypotheses
(`hmeas`, `hvalidB`, `hvalid`, `hinv`, `hsim`, `hFEle`; see `HypothesisTransfer`).
-/

set_option autoImplicit false

open MeasureTheory

namespace ReflectedGMS.GeomTop

open Code GeneralLaws

/-- **Theorem 1.2** of the geometric-topology revision, from the properties of the coding. -/
theorem geomHarmonicCoordinateMainTheorem_of (hmeas : Measurable coords)
    (hvalidB : MeasurableSet {r : RawCode | ValidGeneral r})
    (hvalid : ∀ H : SingSpace, (∃ w : GeomTop.SingularWitness H.1, LineConnectedOff H.1 w.sing) →
      ValidGeneral (coords H))
    (hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : SingSpace), IsSimilar s u hs H H' →
      (ValidGeneral (coords H) ↔ ValidGeneral (coords H')))
    (hsim : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : SingSpace) (h : ValidGeneral (coords H))
      (h' : ValidGeneral (coords H')), IsSimilar s u hs H H' →
        GeneralLaws.IsSimilarity s u hs ⟨coords H, h⟩ ⟨coords H', h'⟩)
    (hFEle : ∀ (H : SingSpace) (h : ValidGeneral (coords H)),
      GeneralLaws.rootedFiniteEnergyDensity (config ⟨coords H, h⟩) 0 ≤ rootedFEDensity H.1) :
    GeomHarmonicCoordinateMainTheorem := by
  intro μ _ hLCS hMT hFE
  have hP := supportedOnValidGeneral_coords hmeas hvalidB hvalid hLCS
  obtain ⟨hV, hconc⟩ := GeneralMainTheorems.generalHarmonicCoordinateMainTheorem (μ.map coords) hP
    (massTransport_generalLaw_geom hmeas hvalidB hinv hsim hP hMT)
    (finiteEnergyMoment_generalLaw_geom hmeas hvalidB hFEle hP hFE)
  exact ⟨hmeas, ae_of_ae_map (p := Valid) hmeas.aemeasurable hV,
    EnvironmentLaws.validLaw (μ.map coords) hV, inferInstance,
    EnvironmentLaws.map_validLaw (μ.map coords) hV,
    geomHarmonicCoordinateConclusions_of_harmonicCoordinateConclusions hconc⟩

/-- **Theorem 1.3** of the geometric-topology revision, from the properties of the coding. -/
theorem geomReflectedInvarianceMainTheorem_of (hmeas : Measurable coords)
    (hvalidB : MeasurableSet {r : RawCode | ValidGeneral r})
    (hvalid : ∀ H : SingSpace, (∃ w : GeomTop.SingularWitness H.1, LineConnectedOff H.1 w.sing) →
      ValidGeneral (coords H))
    (hinv : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : SingSpace), IsSimilar s u hs H H' →
      (ValidGeneral (coords H) ↔ ValidGeneral (coords H')))
    (hsim : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : SingSpace) (h : ValidGeneral (coords H))
      (h' : ValidGeneral (coords H')), IsSimilar s u hs H H' →
        GeneralLaws.IsSimilarity s u hs ⟨coords H, h⟩ ⟨coords H', h'⟩)
    (hFEle : ∀ (H : SingSpace) (h : ValidGeneral (coords H)),
      GeneralLaws.rootedFiniteEnergyDensity (config ⟨coords H, h⟩) 0 ≤ rootedFEDensity H.1) :
    GeomReflectedInvarianceMainTheorem := by
  intro μ _ hLCS hMT hFE hErg
  have hP := supportedOnValidGeneral_coords hmeas hvalidB hvalid hLCS
  obtain ⟨hV, hconc, hends⟩ :=
    GeneralMainTheorems.generalReflectedInvarianceMainTheorem (μ.map coords) hP
      (massTransport_generalLaw_geom hmeas hvalidB hinv hsim hP hMT)
      (finiteEnergyMoment_generalLaw_geom hmeas hvalidB hFEle hP hFE)
      (environmentErgodic_generalLaw_geom hmeas hvalidB hinv hsim hP hErg)
  exact ⟨hmeas, ae_of_ae_map (p := Valid) hmeas.aemeasurable hV,
    ae_validGeneral_coords hmeas hvalidB hP,
    EnvironmentLaws.validLaw (μ.map coords) hV, inferInstance,
    EnvironmentLaws.map_validLaw (μ.map coords) hV,
    geomReflectedInvarianceConclusions_of_reflectedInvarianceConclusions hconc, hends⟩

end ReflectedGMS.GeomTop

assert_no_sorry ReflectedGMS.GeomTop.geomHarmonicCoordinateMainTheorem_of
assert_no_sorry ReflectedGMS.GeomTop.geomReflectedInvarianceMainTheorem_of

#print axioms ReflectedGMS.GeomTop.geomHarmonicCoordinateMainTheorem_of
#print axioms ReflectedGMS.GeomTop.geomReflectedInvarianceMainTheorem_of
