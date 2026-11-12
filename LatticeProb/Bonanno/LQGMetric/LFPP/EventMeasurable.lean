/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.LFPP.EventMeasurable at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.LFPP.Measurable
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_10ProofScale
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.Median

/-!
# The events of `TendstoInProbLU` are measurable up to null sets

`TendstoInProbLU` (Statement/Metric.lean) asks that `P {ω | δ ≤ sup_{B̄_R(0)²} |X_i ω − Y ω|}`
tend to `0`, where `P` is applied to an arbitrary set, i.e. as an outer measure. For the processes
of Theorems 1.1 and 1.2 these events are null-measurable, so the outer probability is their
probability (for the completion of `P`), and `TendstoInProbLU` is convergence in probability in
the usual sense (GM l. 230).

* `nullMeasurableSet_supEdist_ge`: for a.s. continuous `X ω`, `Y ω` whose evaluations are
  a.e.-measurable, `{ω | c ≤ ⨆ p ∈ S, edist (X ω p) (Y ω p)}` is null-measurable (the supremum
  over `S` equals the supremum over a countable dense subset of `S`).
* `IsGFFPlusBddCont.nullMeasurableSet_lfpp_event`: the events of Theorem 1.1 and of the existence
  part of Theorem 1.2, `X ω = 𝔞_ε⁻¹ D^ε_{h(ω)}` (any scalar) with `ε > 0`, for every a.e.-measurable
  `Y : Ω → C(ℂ × ℂ, ℝ)`, in particular for `Y` a.s. determined by `h`
  (`AEDeterminedBy.aemeasurable`) and for `Y ω = D_{h(ω)}` with `D` measurable.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- the supremum of a continuous `ℝ≥0∞`-valued function over a set equals its supremum over any
subset whose closure contains the set -/
theorem biSup_eq_of_subset_closure {α : Type*} [TopologicalSpace α] {g : α → ℝ≥0∞}
    (hg : Continuous g) {S C : Set α} (hCS : C ⊆ S) (hSC : S ⊆ closure C) :
    ⨆ p ∈ S, g p = ⨆ p ∈ C, g p := by
  refine le_antisymm (iSup₂_le fun p hp => ?_) (biSup_mono hCS)
  have hcl : closure C ⊆ g ⁻¹' Iic (⨆ c ∈ C, g c) :=
    closure_minimal (fun c hc => le_biSup g hc) (isClosed_Iic.preimage hg)
  exact hcl (hSC hp)

/-- **The event `{c ≤ sup_S edist (X ω) (Y ω)}` is null-measurable** when `X ω`, `Y ω` are a.s.
continuous and every evaluation is a.e.-measurable (`S ⊆ ℂ × ℂ` arbitrary). -/
theorem nullMeasurableSet_supEdist_ge {X Y : Ω → ℂ × ℂ → ℝ}
    (hXc : ∀ᵐ ω ∂P, Continuous (X ω)) (hYc : ∀ᵐ ω ∂P, Continuous (Y ω))
    (hXm : ∀ p, AEMeasurable (fun ω => X ω p) P) (hYm : ∀ p, AEMeasurable (fun ω => Y ω p) P)
    (S : Set (ℂ × ℂ)) (c : ℝ≥0∞) :
    NullMeasurableSet {ω | c ≤ ⨆ p ∈ S, edist (X ω p) (Y ω p)} P := by
  obtain ⟨C, hCS, hCc, hSC⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace S).exists_countable_dense_subset
  have hF : AEMeasurable (fun ω => ⨆ p ∈ C, edist (X ω p) (Y ω p)) P :=
    AEMeasurable.biSup C hCc fun p _ => (hXm p).edist (hYm p)
  have heq : (fun ω => ⨆ p ∈ C, edist (X ω p) (Y ω p)) =ᵐ[P]
      fun ω => ⨆ p ∈ S, edist (X ω p) (Y ω p) := by
    filter_upwards [hXc, hYc] with ω hx hy
    exact (biSup_eq_of_subset_closure (hx.edist hy) hCS hSC).symm
  exact (hF.congr heq).nullMeasurable measurableSet_Ici

/-- a random continuous function a.s. determined by a measurable `h` is a.e.-measurable -/
theorem AEDeterminedBy.aemeasurable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {Y : Ω → β} {X : Ω → α} (hY : AEDeterminedBy Y X P) (hX : Measurable X) :
    AEMeasurable Y P := by
  obtain ⟨F, hF, he⟩ := hY
  exact ⟨F ∘ X, hF.comp hX, he⟩

/-- **The events of Theorems 1.1 and 1.2 are null-measurable.** For a whole-plane GFF plus a
bounded continuous function, `ε > 0`, any scalar `a` (in the theorems `a = 𝔞_ε⁻¹`) and any
a.e.-measurable `Y : Ω → C(ℂ × ℂ, ℝ)`, the event
`{ω | c ≤ sup_{p ∈ S} |a D^ε_{h(ω)}(p) − Y ω p|}` is null-measurable. -/
theorem IsGFFPlusBddCont.nullMeasurableSet_lfpp_event {h : Ω → DistC}
    (hh : IsGFFPlusBddCont h P) {ξ ε : ℝ} (hε : 0 < ε) (a : ℝ) {Y : Ω → C(ℂ × ℂ, ℝ)}
    (hY : AEMeasurable Y P) (S : Set (ℂ × ℂ)) (c : ℝ≥0∞) :
    NullMeasurableSet {ω | c ≤ ⨆ p ∈ S, edist ((a • lfppDist ξ ε (h ω)) p) (Y ω p)} P := by
  refine nullMeasurableSet_supEdist_ge (X := fun ω => a • lfppDist ξ ε (h ω))
    (Y := fun ω => ⇑(Y ω)) ?_ (Eventually.of_forall fun ω => (Y ω).continuous) ?_ ?_ S c
  · filter_upwards [hh.ae_tendstoLocallyUniformly_heatMollify ε hε.ne'] with ω hω
    have hcont : Continuous (lfppDist ξ ε (h ω)) :=
      ENNReal.continuousOn_toReal.comp_continuous (DFGPS.continuous_lfppDistE_uncurry hω.2)
        fun p => GM.lfppDistE_ne_top hω.2 p.1 p.2
    exact continuous_const.smul hcont
  · intro p
    exact ((LFPP.IsGFFPlusBddCont.aemeasurable_lfppDistE hh hε.ne' p.1 p.2).ennreal_toReal).const_smul a
  · intro p
    exact (continuous_eval_const p).measurable.comp_aemeasurable hY

end LQGMetric
