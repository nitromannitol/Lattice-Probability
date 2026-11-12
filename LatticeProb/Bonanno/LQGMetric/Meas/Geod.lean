/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Meas.Geod at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Meas.UM
import LatticeProb.Bonanno.LQGMetric.Field.StandardBorelMetric
import LatticeProb.Bonanno.LQGMetric.Field.StandardBorelRange
import LatticeProb.Bonanno.LQGMetric.Prob.PolishContinuousMap
import Mathlib.Topology.UnitInterval
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Geodesics as measurable objects (decision D31 = D-C2, nodes F.GEO-MEAS, F.GEO-SEL, CR3)

`decisions/DEC-C.md`, OD-2 rules 1–3 and OD-1 item 6 (CR3); signatures verbatim from its last
section.

* `ContMetric.IsGeod01 D z w η`: `η : C([0,1], ℂ)` is a constant-speed `D`-geodesic from `z`
  to `w`. `isClosed_setOf_isGeod01`: the relation is closed in `ContMetric × C([0,1], ℂ)`;
  `measurableSet_geodRel`: for a measurable metric map `D` on a field space, the relation
  `{(g, η) | η is a D_g-geodesic}` is Borel.
* CR3 events: "some geodesic", "at most one geodesic" (`GeodUnique`), "exactly one geodesic" and
  "∃/∀ geodesic with a Borel property" are universally measurable (Lusin, `UMeasurableSet`).
* `exists_measurable_geodSel` (Lusin–Souslin selector): if `μ`-a.s. the geodesic is unique, a
  measurable `Γ` picks it a.s. The proof restricts the geodesic relation to a Borel set of full
  measure on which it is a partial graph and applies Lusin–Souslin (Kechris, *Classical Descriptive
  Set Theory*, Thm 15.1: injective Borel images are Borel), as in QuantumZipper
  `QuantumZipper.Thm14Determination.exists_measurable_of_partialGraph`
  (QZ/Proofs/Thm14/Determination.lean:49), whose 15-line proof is copied here
  (`exists_measurable_of_partialGraph'`) to avoid importing QZ's Theorem 13/14 chain.
-/

open MeasureTheory Set Filter Topology

namespace LQGMetric

/-- `η` is a `D`-geodesic from `z` to `w`, parametrized on `[0,1]` at constant speed -/
def ContMetric.IsGeod01 (D : ContMetric) (z w : ℂ) (η : C(unitInterval, ℂ)) : Prop :=
  η 0 = z ∧ η 1 = w ∧ ∀ s t : unitInterval, D.1 (η s, η t) = |(t : ℝ) - s| * D.1 (z, w)

/-- at most one geodesic -/
def ContMetric.GeodUnique (D : ContMetric) (z w : ℂ) : Prop :=
  ∀ η η' : C(unitInterval, ℂ), D.IsGeod01 z w η → D.IsGeod01 z w η' → η = η'

/-- `ContMetric` (subspace of the Polish space `C(ℂ × ℂ, ℝ)`) is second countable -/
instance secondCountableTopology_contMetricGeo : SecondCountableTopology ContMetric :=
  TopologicalSpace.Subtype.secondCountableTopology _

/-- the Borel σ-algebra of `ContMetric` is the subspace σ-algebra -/
instance borelSpace_contMetricGeo : BorelSpace ContMetric := Subtype.borelSpace _

theorem continuous_contMetric_apply :
    Continuous fun p : ContMetric × (ℂ × ℂ) => p.1.1 p.2 :=
  continuous_eval.comp (continuous_subtype_val.prodMap continuous_id)

/-- the geodesic relation is closed in `ContMetric × C([0,1], ℂ)` -/
theorem isClosed_setOf_isGeod01 (z w : ℂ) :
    IsClosed {p : ContMetric × C(unitInterval, ℂ) | p.1.IsGeod01 z w p.2} := by
  have he : ∀ s : unitInterval, Continuous fun p : ContMetric × C(unitInterval, ℂ) => p.2 s :=
    fun s => (continuous_eval_const s).comp continuous_snd
  simp only [ContMetric.IsGeod01, ofPred_and, ofPred_forall]
  refine (isClosed_eq (he 0) continuous_const).inter ((isClosed_eq (he 1) continuous_const).inter
    (isClosed_iInter fun s => isClosed_iInter fun t => isClosed_eq ?_ ?_))
  · exact continuous_contMetric_apply.comp (continuous_fst.prodMk ((he s).prodMk (he t)))
  · exact continuous_const.mul (continuous_contMetric_apply.comp
      (continuous_fst.prodMk continuous_const))

theorem measurableSet_setOf_isGeod01 (z w : ℂ) :
    MeasurableSet {p : ContMetric × C(unitInterval, ℂ) | p.1.IsGeod01 z w p.2} :=
  (isClosed_setOf_isGeod01 z w).measurableSet

/-- the geodesic relation of a measurable metric map, on any field space -/
theorem measurableSet_geodRel_of {S : Type*} [MeasurableSpace S] (D : S → ContMetric)
    (hD : Measurable D) (z w : ℂ) :
    MeasurableSet {p : S × C(unitInterval, ℂ) | (D p.1).IsGeod01 z w p.2} :=
  measurableSet_setOf_isGeod01 z w |>.preimage
    ((hD.comp measurable_fst).prodMk measurable_snd)

/-- **F.GEO-MEAS.** The geodesic relation of a metric map is Borel. -/
theorem measurableSet_geodRel (D : DistC → ContMetric) (hD : Measurable D) (z w : ℂ) :
    MeasurableSet {p : DistC × C(unitInterval, ℂ) | (D p.1).IsGeod01 z w p.2} :=
  measurableSet_geodRel_of D hD z w

/-! ### CR3: events quantified over geodesics are universally measurable -/

section CR3

variable {S : Type*} [MeasurableSpace S] [StandardBorelSpace S] (D : S → ContMetric)
  (hD : Measurable D) (z w : ℂ)
include hD

/-- "there is a geodesic with the Borel property `Q`" -/
theorem uMeasurableSet_exists_geod {Q : Set (S × C(unitInterval, ℂ))} (hQ : MeasurableSet Q) :
    UMeasurableSet {g | ∃ η, (D g).IsGeod01 z w η ∧ (g, η) ∈ Q} :=
  UMeasurableSet.setOf_exists (S := {p | (D p.1).IsGeod01 z w p.2} ∩ Q)
    ((measurableSet_geodRel_of D hD z w).inter hQ)

end CR3

/-! ### The Lusin–Souslin selector (F.GEO-SEL) -/

/-- **Lusin–Souslin selection** (Kechris Thm 15.1; proof copied from QuantumZipper
`QuantumZipper.Thm14Determination.exists_measurable_of_partialGraph`): a Borel partial graph in a
product of standard Borel spaces is contained in the graph of a measurable map. -/
theorem exists_measurable_of_partialGraph' {S E : Type*} [MeasurableSpace S]
    [StandardBorelSpace S] [MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]
    {G : Set (S × E)} (hGm : MeasurableSet G)
    (hG : ∀ ⦃y : S⦄ ⦃z z' : E⦄, (y, z) ∈ G → (y, z') ∈ G → z = z') :
    ∃ F : S → E, Measurable F ∧ ∀ p ∈ G, F p.1 = p.2 := by
  have := hGm.standardBorel
  have emb : MeasurableEmbedding (fun p : G => (p : S × E).1) :=
    Measurable.measurableEmbedding (measurable_fst.comp measurable_subtype_coe)
      (fun a b hab => by
        have hb : ((a : S × E).1, (b : S × E).2) ∈ G := by
          have h2 := b.2
          rw [show (a : S × E).1 = (b : S × E).1 from hab]
          exact h2
        exact Subtype.ext (Prod.ext hab (hG a.2 hb)))
  obtain ⟨F, hF, hcomp⟩ := emb.exists_measurable_extend
    (g := fun p : G => (p : S × E).2) (measurable_snd.comp measurable_subtype_coe)
    (fun _ => inferInstance)
  exact ⟨F, hF, fun p hp => congrFun hcomp ⟨p, hp⟩⟩

/-- the selector on any standard Borel field space: if `μ`-a.s. there is exactly one geodesic,
some measurable `Γ` is a.s. that geodesic -/
theorem exists_measurable_geodSel_of {S : Type*} [MeasurableSpace S] [StandardBorelSpace S]
    (D : S → ContMetric) (hD : Measurable D) (z w : ℂ) (μ : Measure S)
    (h : ∀ᵐ g ∂μ, ∃! η, (D g).IsGeod01 z w η) :
    ∃ Γ : S → C(unitInterval, ℂ), Measurable Γ ∧ ∀ᵐ g ∂μ, (D g).IsGeod01 z w (Γ g) := by
  set N := toMeasurable μ {g | ¬ ∃! η, (D g).IsGeod01 z w η}
  have hN0 : μ N = 0 := by rw [measure_toMeasurable]; exact ae_iff.1 h
  have hB : ∀ g, g ∉ N → ∃! η, (D g).IsGeod01 z w η := fun g hg => by
    by_contra hc; exact hg (subset_toMeasurable _ _ hc)
  set G := {p : S × C(unitInterval, ℂ) | p.1 ∈ Nᶜ ∧ (D p.1).IsGeod01 z w p.2}
  have hGm : MeasurableSet G :=
    ((measurableSet_toMeasurable _ _).compl.preimage measurable_fst).inter
      (measurableSet_geodRel_of D hD z w)
  obtain ⟨F, hF, hFG⟩ := exists_measurable_of_partialGraph' hGm fun g η η' h₁ h₂ =>
    (hB g h₁.1).unique h₁.2 h₂.2
  refine ⟨F, hF, ?_⟩
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN0] with g hg
  obtain ⟨η, hη, -⟩ := hB g hg
  rw [hFG (g, η) ⟨hg, hη⟩]
  exact hη

/-- **F.GEO-SEL** (D31 rule 3; DEC-C signature). Lusin–Souslin selector of the a.s.-unique
geodesic. -/
theorem exists_measurable_geodSel (D : DistC → ContMetric) (hD : Measurable D) (z w : ℂ)
    (μ : Measure DistC) (h : ∀ᵐ g ∂μ, ∃! η, (D g).IsGeod01 z w η) :
    ∃ Γ : DistC → C(unitInterval, ℂ), Measurable Γ ∧ ∀ᵐ g ∂μ, (D g).IsGeod01 z w (Γ g) :=
  exists_measurable_geodSel_of D hD z w μ h

end LQGMetric
