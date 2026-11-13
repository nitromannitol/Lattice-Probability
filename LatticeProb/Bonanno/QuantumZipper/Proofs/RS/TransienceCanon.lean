/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.RS.TransienceCanon at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.RS.TraceMeas
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.PathLaw

/-!
# EXT-RS node TRANS, tool: the canonical space of continuous paths

Blueprint `blueprint/EXT_RS_BLUEPRINT.md` §4, node **TRANS** (scaling and Markov steps).

`CPath` is the space of continuous paths `ℝ≥0 → ℝ` with the subspace σ-algebra of the product
σ-algebra, and `canonBM t f = f t` its coordinate process. Every path of `canonBM` is continuous,
so the measurable-trace machinery (TR6) applies to it directly.

* `isBrownianReal_canonBM`: the push-forward of a pre-Brownian motion with measurable
  coordinates and continuous paths makes `canonBM` a Brownian motion;
* `map_toCPath_eq`: two such pre-Brownian motions (on possibly different spaces) have the same
  law on `CPath` (Kolmogorov uniqueness, `Williams.map_eq_of_forall_finset`, and the fact that the
  σ-algebra of a subtype is the comap of the inclusion, `Williams.map_subtype_val_injective`);
* `exists_good_version0`: a Brownian motion has a version with measurable coordinates, all paths
  continuous and started at `0`; it has the same SLE trace almost surely.

Own elementary bookkeeping (measure theory only); no literature statement is involved.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace RS

/-- Continuous real paths on `ℝ≥0`, with the subspace σ-algebra of the product σ-algebra. -/
abbrev CPath : Type := {f : ℝ≥0 → ℝ // Continuous f}

/-- The coordinate process on `CPath`. -/
def canonBM : ℝ≥0 → CPath → ℝ := fun t f => f.1 t

theorem measurable_canonBM (t : ℝ≥0) : Measurable (canonBM t) :=
  (measurable_pi_apply t).comp measurable_subtype_coe

theorem continuous_canonBM (f : CPath) : Continuous (canonBM · f) := f.2

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The path of a process with continuous paths, as an element of `CPath`. -/
def toCPath (B : ℝ≥0 → Ω → ℝ) (hc : ∀ ω, Continuous (B · ω)) (ω : Ω) : CPath :=
  ⟨(B · ω), hc ω⟩

theorem measurable_toCPath {B : ℝ≥0 → Ω → ℝ} (hBm : ∀ t, Measurable (B t))
    (hc : ∀ ω, Continuous (B · ω)) : Measurable (toCPath B hc) :=
  Measurable.subtype_mk (measurable_pi_iff.2 hBm)

omit [MeasurableSpace Ω] in
@[simp] theorem canonBM_toCPath (B : ℝ≥0 → Ω → ℝ) (hc : ∀ ω, Continuous (B · ω)) (t : ℝ≥0)
    (ω : Ω) : canonBM t (toCPath B hc ω) = B t ω := rfl

omit [MeasurableSpace Ω] in
theorem sleTrace_toCPath (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (hc : ∀ ω, Continuous (B · ω)) (ω : Ω) :
    sleTrace κ canonBM (toCPath B hc ω) = sleTrace κ B ω := rfl

/-- The coordinate process is a Brownian motion under the law of a pre-Brownian motion with
continuous paths. -/
theorem isBrownianReal_canonBM {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous (B · ω)) :
    IsBrownianReal canonBM (P.map (toCPath B hc)) where
  hasLaw I := by
    have hm := measurable_toCPath hBm hc
    have hI : Measurable fun f : CPath => I.restrict (canonBM · f) :=
      measurable_pi_iff.2 fun i => measurable_canonBM _
    refine ⟨hI.aemeasurable, ?_⟩
    rw [Measure.map_map hI hm]
    exact (hB.hasLaw I).map_eq
  cont := ae_of_all _ continuous_canonBM

omit [MeasurableSpace Ω] in
/-- Measures on a subtype are determined by their push-forwards along the inclusion (as
`Williams.map_subtype_val_injective`). -/
theorem map_val_injective_rs {α : Type*} [MeasurableSpace α] {p : α → Prop}
    {μ ν : Measure (Subtype p)} (h : μ.map Subtype.val = ν.map Subtype.val) : μ = ν := by
  ext S hS
  obtain ⟨T, hT, hTS⟩ := MeasurableSpace.measurableSet_comap.mp hS
  rw [← hTS, ← Measure.map_apply measurable_subtype_coe hT,
    ← Measure.map_apply measurable_subtype_coe hT, h]

/-- Two pre-Brownian motions with measurable coordinates and continuous paths have the same law
on `CPath`. -/
theorem map_toCPath_eq {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {B : ℝ≥0 → Ω → ℝ} {B' : ℝ≥0 → Ω' → ℝ} (hB : IsPreBrownianReal B P)
    (hB' : IsPreBrownianReal B' P') (hBm : ∀ t, Measurable (B t))
    (hBm' : ∀ t, Measurable (B' t)) (hc : ∀ ω, Continuous (B · ω))
    (hc' : ∀ ω, Continuous (B' · ω)) :
    P.map (toCPath B hc) = P'.map (toCPath B' hc') := by
  have hm := measurable_toCPath hBm hc
  have hm' := measurable_toCPath hBm' hc'
  refine map_val_injective_rs ?_
  rw [Measure.map_map measurable_subtype_coe hm, Measure.map_map measurable_subtype_coe hm']
  refine Williams.map_eq_of_forall_finset (measurable_pi_iff.2 hBm).aemeasurable
    (measurable_pi_iff.2 hBm').aemeasurable fun I => ?_
  exact (hB.hasLaw I).map_eq.trans (hB'.hasLaw I).map_eq.symm

/-- A version of a Brownian motion with measurable coordinates, all paths continuous and
started at `0`. -/
theorem exists_good_version0 {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∃ B'' : ℝ≥0 → Ω → ℝ, (∀ t, Measurable (B'' t)) ∧ (∀ ω, Continuous (B'' · ω)) ∧
      (∀ ω, B'' 0 ω = 0) ∧ IsBrownianReal B'' P ∧ ∀ᵐ ω ∂P, ∀ t, B'' t ω = B t ω := by
  obtain ⟨B', hB'm, hB'c, hB'eq⟩ := CharFun.exists_good_version hB
  have hae : ∀ᵐ ω ∂P, ∀ t, B' t ω - B' 0 ω = B t ω := by
    filter_upwards [hB'eq, hB.eval_zero_ae_eq_zero] with ω h h0 t
    simp [h, h0]
  refine ⟨fun t ω => B' t ω - B' 0 ω, fun t => (hB'm t).sub (hB'm 0),
    fun ω => (hB'c ω).sub continuous_const, fun ω => sub_self _, ?_, hae⟩
  exact ⟨hB.toIsPreBrownianReal.congr fun t => hae.mono fun ω h => (h t).symm,
    ae_of_all _ fun ω => (hB'c ω).sub continuous_const⟩

omit [MeasurableSpace Ω] in
theorem sleTrace_congr_of_eq {B B' : ℝ≥0 → Ω → ℝ} {ω : Ω} (h : ∀ t, B' t ω = B t ω) (κ : ℝ) :
    sleTrace κ B' ω = sleTrace κ B ω := by
  have : drive κ B' ω = drive κ B ω := funext fun t => by simp [drive, h]
  simp only [sleTrace, this]

end RS
end QuantumZipper
