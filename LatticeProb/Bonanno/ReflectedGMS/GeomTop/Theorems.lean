/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.GeomTop.Theorems at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.GeomTop.MainTheorems
import LatticeProb.Bonanno.ReflectedGMS.GeomTop.CoordsMeasurable
import LatticeProb.Bonanno.ReflectedGMS.GeomTop.CodingSing
import LatticeProb.Bonanno.ReflectedGMS.GeomTop.ValidGeneralBorel
import Mathlib.Util.AssertNoSorry

/-!
# Theorems 1.2 and 1.3 of the geometric-topology revision — proved

`geomHarmonicCoordinateMainTheorem : GeomHarmonicCoordinateMainTheorem` and
`geomReflectedInvarianceMainTheorem : GeomReflectedInvarianceMainTheorem`
(statements: `GeomTop/Statement.lean`).

The assembly `GeomTop/MainTheorems.lean` reduces both theorems to the proved general-cell theorems
plus six facts about the auxiliary rational-label coordinates `coords`; they are supplied here:

* `measurable_coords` (`GeomTop/CoordsMeasurable.lean`): `coords` is `B_sing`-measurable;
* `measurableSet_validGeneral` (`GeomTop/ValidGeneralBorel*.lean`): the valid codes of the
  general-cell manuscript form a Borel set (via the canonical minimal singular set);
* `validGeneral_code_of_witness`, `validGeneral_code_iff_similarity`,
  `generalLaws_isSimilarity_sing`, `rootedFiniteEnergyDensity_config_sing`
  (`GeomTop/CodingSing.lean`): Definition 1.1 + (LCS) makes the coordinates a valid code, validity
  and the similarity relation are carried by similarities, and the (FE) integrands agree.
-/

set_option autoImplicit false

open MeasureTheory

namespace ReflectedGMS.GeomTop

open Code GeneralLaws GMS

theorem hvalid_coords (H : SingSpace)
    (h : ∃ w : SingularWitness H.1, LineConnectedOff H.1 w.sing) : ValidGeneral (coords H) := by
  obtain ⟨w, hL⟩ := h
  exact validGeneral_code_of_witness H.2 w hL

theorem hinv_coords (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : SingSpace) (h : IsSimilar s u hs H H') :
    ValidGeneral (coords H) ↔ ValidGeneral (coords H') := by
  have hc : coords H' = (H.1.similarity s u hs).code := by
    show H'.1.code = _
    rw [h]
  rw [hc]
  exact validGeneral_code_iff_similarity s u hs H.2

theorem hsim_coords (s : ℝ) (u : Plane) (hs : 0 < s) (H H' : SingSpace)
    (h : ValidGeneral (coords H)) (h' : ValidGeneral (coords H')) (hHH : IsSimilar s u hs H H') :
    GeneralLaws.IsSimilarity s u hs ⟨coords H, h⟩ ⟨coords H', h'⟩ := by
  have hc : coords H' = (H.1.similarity s u hs).code := by
    show H'.1.code = _
    rw [hHH]
  exact generalLaws_isSimilarity_sing s u hs H.2 (e := ⟨coords H, h⟩) (e' := ⟨coords H', h'⟩)
    rfl hc

theorem hFEle_coords (H : SingSpace) (h : ValidGeneral (coords H)) :
    GeneralLaws.rootedFiniteEnergyDensity (config ⟨coords H, h⟩) 0 ≤ rootedFEDensity H.1 :=
  (rootedFiniteEnergyDensity_config_sing H.2 (e := ⟨coords H, h⟩) rfl).le

/-- **Theorem 1.2** of the geometric-topology revision (harmonic coordinates). -/
theorem geomHarmonicCoordinateMainTheorem : GeomHarmonicCoordinateMainTheorem :=
  geomHarmonicCoordinateMainTheorem_of measurable_coords measurableSet_validGeneral hvalid_coords
    hinv_coords hsim_coords hFEle_coords

/-- **Theorem 1.3** of the geometric-topology revision (reflected invariance principle). -/
theorem geomReflectedInvarianceMainTheorem : GeomReflectedInvarianceMainTheorem :=
  geomReflectedInvarianceMainTheorem_of measurable_coords measurableSet_validGeneral hvalid_coords
    hinv_coords hsim_coords hFEle_coords

end ReflectedGMS.GeomTop

assert_no_sorry ReflectedGMS.GeomTop.geomHarmonicCoordinateMainTheorem
assert_no_sorry ReflectedGMS.GeomTop.geomReflectedInvarianceMainTheorem
#print axioms ReflectedGMS.GeomTop.geomHarmonicCoordinateMainTheorem
#print axioms ReflectedGMS.GeomTop.geomReflectedInvarianceMainTheorem
