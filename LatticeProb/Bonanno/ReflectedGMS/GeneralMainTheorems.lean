/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.GeneralMainTheorems at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.GeneralMainStatements
import LatticeProb.Bonanno.ReflectedGMS.Geometry.EndSpatialImageGeneral
import LatticeProb.Bonanno.ReflectedGMS.MainTheorems
import LatticeProb.Bonanno.ReflectedGMS.Environment.GeneralLawTransfer
import LatticeProb.Bonanno.ReflectedGMS.Spatial.GeneralGraphLocalFiniteness
import Mathlib.Util.AssertNoSorry

/-!
# Theorems 1.2 and 1.3 of the general-cell singular-set manuscript, proved

The conclusions of Theorems 1.2 and 1.3 are those of the harmonic-coordinate and reflected-invariance
theorems already proved (`MainTheorems.harmonicCoordinateMainTheorem`,
`MainTheorems.reflectedInvarianceMainTheorem`), plus the end-image sentence of 1.3(b).  The proof is
therefore an environment-class inclusion, not a second proof of the stochastic results:

* **Lemma 2.1 and Proposition 2.3** (`Code.valid_of_validGeneral`, `Environment/CodeGeneralValid.lean`):
  an environment satisfying Definition 1.1 and (LCS) whose graph is locally finite is valid in the
  earlier sense — null boundaries, disjoint interiors, `H¹`-null uncovered set, connected graph and
  generic line connectivity are all *derived*, the last two from (LCS) alone, with no face rule.
* **Proposition 2.6** (`endSpatialImageConclusions_of_geometry`, `Geometry/EndSpatialImageGeneral.lean`):
  spatial images of graph ends, for every slim singular witness.

* **Lemma 2.5** (`GeneralLaws.ae_finiteRows`, `Spatial/GeneralGraphLocalFiniteness.lean`): under
  (1.4) and (FE) with extended sums, almost every environment has a locally finite graph — so the
  paper-faithful theorems below carry **no** local-finiteness hypothesis.
* **Law transfer** (`Environment/GeneralLawTransfer.lean`): (1.4), (FE) and ergodicity on the general
  environment space imply the corresponding hypotheses of the earlier theorems on `validLaw`.

The file proves both the paper-faithful Theorems 1.2 and 1.3 and the intermediate forms in which
graph local finiteness is an explicit hypothesis.
-/

set_option autoImplicit false

namespace ReflectedGMS.GeneralMainTheorems

open GeneralMainStatements

/-- **Theorem 1.2 with graph local finiteness assumed.** -/
theorem generalHarmonicCoordinateMainTheoremOfLocallyFinite :
    GeneralHarmonicCoordinateMainTheoremOfLocallyFinite :=
  fun P _ hP hLF hmt hFE =>
    MainTheorems.harmonicCoordinateMainTheorem P (supportedOnValid_of_general hP hLF) hmt hFE

/-- **Theorem 1.3 with graph local finiteness assumed.**  Clauses (a)–(e) come from the earlier
theorem through the class inclusion; the end-image sentence is Proposition 2.6, which holds
deterministically for every valid environment. -/
theorem generalReflectedInvarianceMainTheoremOfLocallyFinite :
    GeneralReflectedInvarianceMainTheoremOfLocallyFinite :=
  fun P _ hP hLF hmt hFE herg =>
    ⟨MainTheorems.reflectedInvarianceMainTheorem P (supportedOnValid_of_general hP hLF)
      hmt hFE herg,
     fun e _ => endSpatialImageConclusions_of_geometry (Code.decode_geometry e)⟩

/-- **Theorem 1.2** (harmonic coordinates), with exactly the manuscript's hypotheses: Definition 1.1,
(LCS), (1.4) and (FE).  Graph local finiteness is derived (Lemma 2.5). -/
theorem generalHarmonicCoordinateMainTheorem : GeneralHarmonicCoordinateMainTheorem := by
  intro P _ hP hmt hFE
  have hfin := GeneralLaws.ae_finiteRows (GeneralLaws.generalLaw P hP) hmt hFE
  have hV := GeneralLaws.supportedOnValid_of_generalLaw P hP hfin
  exact ⟨hV, MainTheorems.harmonicCoordinateMainTheorem P hV
    (GeneralLaws.ambientMassTransport_of_generalLaw P hP hfin hV hmt)
    (GeneralLaws.finiteEnergyMoment_validLaw_of_generalLaw P hP hfin hV hFE)⟩

/-- **Theorem 1.3** (reflected invariance principle), with exactly the manuscript's hypotheses:
Definition 1.1, (LCS), (1.4), (FE) and ergodicity modulo scaling.  Graph local finiteness is derived
(Lemma 2.5); the end-image sentence of (b) is Proposition 2.6. -/
theorem generalReflectedInvarianceMainTheorem : GeneralReflectedInvarianceMainTheorem := by
  intro P _ hP hmt hFE herg
  have hfin := GeneralLaws.ae_finiteRows (GeneralLaws.generalLaw P hP) hmt hFE
  have hV := GeneralLaws.supportedOnValid_of_generalLaw P hP hfin
  exact ⟨hV, MainTheorems.reflectedInvarianceMainTheorem P hV
      (GeneralLaws.ambientMassTransport_of_generalLaw P hP hfin hV hmt)
      (GeneralLaws.finiteEnergyMoment_validLaw_of_generalLaw P hP hfin hV hFE)
      (GeneralLaws.ambientEnvironmentErgodic_of_generalLaw P hP hfin hV herg),
    fun e _ => endSpatialImageConclusions_of_geometry (Code.decode_geometry e)⟩

end ReflectedGMS.GeneralMainTheorems

assert_no_sorry ReflectedGMS.GeneralMainTheorems.generalHarmonicCoordinateMainTheorem
assert_no_sorry ReflectedGMS.GeneralMainTheorems.generalReflectedInvarianceMainTheorem

assert_no_sorry ReflectedGMS.GeneralMainTheorems.generalHarmonicCoordinateMainTheoremOfLocallyFinite
assert_no_sorry ReflectedGMS.GeneralMainTheorems.generalReflectedInvarianceMainTheoremOfLocallyFinite

#print axioms ReflectedGMS.GeneralMainTheorems.generalHarmonicCoordinateMainTheoremOfLocallyFinite
#print axioms ReflectedGMS.GeneralMainTheorems.generalReflectedInvarianceMainTheoremOfLocallyFinite
#print axioms ReflectedGMS.GeneralMainTheorems.generalHarmonicCoordinateMainTheorem
#print axioms ReflectedGMS.GeneralMainTheorems.generalReflectedInvarianceMainTheorem
