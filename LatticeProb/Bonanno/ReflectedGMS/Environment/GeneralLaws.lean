/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Environment.GeneralLaws at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Environment.GeneralGeometry
import LatticeProb.Bonanno.ReflectedGMS.Environment.RootDensities
import LatticeProb.Bonanno.ReflectedGMS.Environment.Laws

/-!
# Codes, environments and random-environment hypotheses for the general-cell manuscript

The hypotheses of Theorems 1.2 and 1.3 are stated for environments satisfying Definition 1.1 and
(LCS) — `GeneralGeometry` — **without** graph local finiteness.  The existing environment type
`Code.Env` cannot carry them, since `Code.AdmissibleConductance` contains the finite-row clause
`finiteRow`.  This file therefore introduces

* `Code.RawAdmissible` — `AdmissibleConductance` without `finiteRow`;
* `Code.ValidGeneral` / `Code.EnvGeneral` — Definition 1.1 + (LCS) + canonical labels;
* `GeneralLaws.MassTransport` — (1.4)/(1.5) on `EnvGeneral`, verbatim the kernel condition of
  `EnvironmentLaws.MassTransport` with the environment space enlarged;
* `GeneralLaws.FiniteEnergyMoment` — (FE) with the conductance sums read as **extended nonnegative
  sums**, exactly as the manuscript prescribes before Lemma 2.5 (manuscript lines 123–126), so that
  an infinite-degree root cell makes the moment infinite rather than silently zero;
* `GeneralLaws.EnvironmentErgodic` — ergodicity modulo scaling on `EnvGeneral`.

The rooted density is zero at uncovered and boundary roots, the manuscript's convention (line 104);
it reuses `RootDensities.rootAt`, which reads only the cells.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace ReflectedGMS

namespace Code

/-- Conductance admissibility **without** finite rows: symmetric, nonnegative, loop-free, and
supported on active labels. -/
structure RawAdmissible (r : RawCode) : Prop where
  symm : ∀ n m, r.2 n m = r.2 m n
  nonneg : ∀ n m, 0 ≤ r.2 n m
  self : ∀ n, r.2 n n = 0
  absent : ∀ n m, r.1 n = none ∨ r.1 m = none → r.2 n m = 0

/-- Every row of conductances has finite support (graph local finiteness at the code level). -/
def FiniteRows (r : RawCode) : Prop := ∀ n, (Function.support (r.2 n)).Finite

theorem admissibleConductance_iff (r : RawCode) :
    AdmissibleConductance r ↔ RawAdmissible r ∧ FiniteRows r :=
  ⟨fun h => ⟨⟨h.symm, h.nonneg, h.self, h.absent⟩, h.finiteRow⟩,
    fun h => ⟨h.1.symm, h.1.nonneg, h.1.self, h.1.absent, h.2⟩⟩

/-- The cell configuration carried by a code, with no summability requirement. -/
def rawConfig (r : RawCode) (h : RawAdmissible r) : CellConfiguration (Vertex r) where
  cell := cell r
  c := fun v w => r.2 v.val w.val
  c_symm := fun v w => h.symm v.val w.val
  c_nonneg := fun v w => h.nonneg v.val w.val
  c_self := fun v => h.self v.val

/-- **Pathwise validity for the general manuscript**: Definition 1.1, (LCS), and least rational
interior labels.  Neither graph local finiteness nor graph connectedness is assumed. -/
def ValidGeneral (r : RawCode) : Prop :=
  ∃ h : RawAdmissible r, GeneralGeometry (rawConfig r h) ∧ CanonicalLabels r

/-- Environments of the general manuscript, with the trace σ-algebra of `RawCode`. -/
abbrev EnvGeneral := {r : RawCode // ValidGeneral r}

/-- The configuration of a general environment. -/
noncomputable def config (e : EnvGeneral) : CellConfiguration (Vertex e.val) :=
  rawConfig e.val e.property.choose

theorem config_generalGeometry (e : EnvGeneral) : GeneralGeometry (config e) :=
  e.property.choose_spec.1

theorem config_canonicalLabels (e : EnvGeneral) : CanonicalLabels e.val :=
  e.property.choose_spec.2

/-- `rawConfig` does not depend on the admissibility proof. -/
theorem rawConfig_congr (r : RawCode) (h h' : RawAdmissible r) : rawConfig r h = rawConfig r h' :=
  rfl

/-- On a valid (finite-row) environment the decoded network has the raw configuration. -/
theorem toCellConfiguration_decode (e : Env) (h : RawAdmissible e.val) :
    (decode e).toCellConfiguration = rawConfig e.val h := rfl

end Code

namespace GeneralLaws

open Code

/-- A physical similarity between general environments after relabelling the active vertices:
cells are transformed by `z ↦ s(z − u)` and conductances are unchanged.  Verbatim
`EnvironmentLaws.IsSimilarityRelabel`, on `EnvGeneral`. -/
def IsSimilarityRelabel (s : ℝ) (u : Plane) (hs : 0 < s) (e e' : EnvGeneral)
    (relabel : Vertex e.val ≃ Vertex e'.val) : Prop :=
  (∀ v, (config e').cell (relabel v) = transformCell s u hs ((config e).cell v)) ∧
    (∀ v w, (config e').c (relabel v) (relabel w) = (config e).c v w)

/-- The physical similarity relation on general environments. -/
def IsSimilarity (s : ℝ) (u : Plane) (hs : 0 < s) (e e' : EnvGeneral) : Prop :=
  ∃ relabel : Vertex e.val ≃ Vertex e'.val, IsSimilarityRelabel s u hs e e' relabel

/-- Nonnegative measurable transport kernels of scaling degree `−2`, (1.5). -/
structure MassTransportKernel where
  toFun : EnvGeneral × Plane × Plane → ℝ≥0∞
  measurable_toFun : Measurable toFun
  covariant : ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (e e' : EnvGeneral),
    IsSimilarity s u hs e e' → ∀ w z : Plane,
      toFun (e', positiveSimilarity s u w, positiveSimilarity s u z) =
        ENNReal.ofReal ((s ^ 2)⁻¹) * toFun (e, w, z)

/-- **Mass transport modulo scaling**, (1.4), for a law on general environments. -/
def MassTransport (ν : Measure EnvGeneral) : Prop :=
  ∀ T : MassTransportKernel,
    (∫⁻ e, ∫⁻ z : Plane, T.toFun (e, 0, z) ∂volume ∂ν) =
      ∫⁻ e, ∫⁻ z : Plane, T.toFun (e, z, 0) ∂volume ∂ν

/-- Events invariant under translations and positive dilations. -/
def SimilarityInvariant (A : Set EnvGeneral) : Prop :=
  ∀ (s : ℝ) (u : Plane) (hs : 0 < s) (e e' : EnvGeneral),
    IsSimilarity s u hs e e' → (e ∈ A ↔ e' ∈ A)

/-- **Ergodicity modulo scaling**: every measurable similarity-invariant event has law `0` or `1`. -/
def EnvironmentErgodic (ν : Measure EnvGeneral) : Prop :=
  ∀ A : Set EnvGeneral, MeasurableSet A → SimilarityInvariant A → ν A = 0 ∨ ν A = 1

/-- The (FE) integrand `d_H² / a_H · (π(H) + π*(H))`, with `π(H) = Σ_{H'∼H} c(H,H')` and
`π*(H) = Σ_{H'∼H} c(H,H')⁻¹` read as **extended nonnegative sums** (manuscript lines 123–126).
Non-neighbours contribute `0` to both sums (`c = 0` and `0⁻¹ = 0`). -/
noncomputable def finiteEnergyDensity {V : Type*} (C : CellConfiguration V) (v : V) : ℝ≥0∞ :=
  ENNReal.ofReal (Metric.diam (C.cell v : Set Plane) ^ 2) /
      ENNReal.ofReal (StatementIngredients.cellArea C.cellsOnly v) *
    ((∑' w, ENNReal.ofReal (C.c v w)) + ∑' w, ENNReal.ofReal (C.c v w)⁻¹)

/-- The (FE) integrand at the cell containing `z`; zero at uncovered or boundary points. -/
noncomputable def rootedFiniteEnergyDensity {V : Type*} (C : CellConfiguration V) (z : Plane) :
    ℝ≥0∞ :=
  (RootDensities.rootAt C.cellsOnly z).elim 0 (finiteEnergyDensity C)

/-- **(FE)**: `E[d²_{H₀}/a_{H₀} (π(H₀) + π*(H₀))] < ∞`, with extended sums. -/
def FiniteEnergyMoment (ν : Measure EnvGeneral) : Prop :=
  (∫⁻ e, rootedFiniteEnergyDensity (config e) 0 ∂ν) < ∞

/-- The raw environment law is carried by general environments. -/
def SupportedOnValidGeneral (P : Measure RawCode) : Prop := ∀ᵐ r ∂P, ValidGeneral r

/-- The lift of the raw law to the trace-measurable subtype of general environments. -/
noncomputable def generalLaw (P : Measure RawCode) [IsProbabilityMeasure P]
    (hP : SupportedOnValidGeneral P) : Measure EnvGeneral :=
  supportedLaw P {r | ValidGeneral r} hP

instance generalLaw_isProbability (P : Measure RawCode) [IsProbabilityMeasure P]
    (hP : SupportedOnValidGeneral P) : IsProbabilityMeasure (generalLaw P hP) :=
  supportedLaw_isProbability P {r | ValidGeneral r} hP

theorem map_generalLaw (P : Measure RawCode) [IsProbabilityMeasure P]
    (hP : SupportedOnValidGeneral P) : (generalLaw P hP).map Subtype.val = P :=
  map_supportedLaw P {r | ValidGeneral r} hP

end GeneralLaws

end ReflectedGMS
