/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Meas.LocalEvent at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Meas.UM
import LatticeProb.Bonanno.LQGMetric.Blueprint.M2Defs
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-!
# Events of a local random object are local events (task P2-LOCMEAS, decision D51)

The shared measurability step behind GM Lemma 3.7 ("`𝖤_r(z)` is determined by
`h|_{𝔸_{r/2,2r}(z)}`", GM arXiv:1905.00383v3 l. 1345–1360), GM Lemma 4.6 and DFGPS Lemma 3.2.
Axiom II (locality) only says that the internal metric `D_h(·,·;U)` is a.s. a measurable function
of `h|_U`, coordinatewise. Events quantifying over all points and paths become `σ(h|_U)`-events
as follows (the argument of P2-E3a's `GM.gm_ae_preimage_eq_of_saturated`, extended to
universally measurable events):

* `Y : Ω → β` (the field, `β` standard Borel), `R : β → γ'` Borel (the internal metric at the
  pairs of a countable dense set, read off `Y`), `W ⊆ β` Borel carrying the law of `Y` on which
  `R` determines the event `B` (`B` saturated: continuity of internal metrics, LM Lemma 1.1).
* `ae_preimage_eq_of_saturated`: if `W ∩ B` is Borel, the images `R(W ∩ B)` and `R(W ∖ B)` are
  disjoint analytic sets, separated by a Borel `S` (Lusin separation, mathlib
  `AnalyticSet.measurablySeparable`; Kechris, *Classical Descriptive Set Theory*, Thm 14.7);
  then `{Y ∈ B} = {R(Y) ∈ S}` a.s. Proof copied from P2-E3a's
  `GM.gm_ae_preimage_eq_of_saturated` (`Papers/GM/S4/L46Meas.lean`), to keep `Meas/` free of
  paper imports.
* `ae_preimage_eq_of_saturated_null`: the same when `B` is only null-measurable for the law of
  `Y` (e.g. universally measurable: analytic/coanalytic events over paths, decision D30):
  shrink `W` by the null Borel set `B₂ ∖ B₁` between a Borel kernel and hull of `B`.
* `aeEventIn_of_saturated`: if moreover `V = R(Y)` a.s. with `V` measurable for a σ-algebra `m`
  (locality: `V` is the internal metric computed from `h|_U`), then `{Y ∈ B}` is a.s. an event of
  `m` (`Blueprint.AEEventIn`).

Standard descriptive set theory (no paper proof to follow; own short arguments around mathlib's
separation theorem).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter

namespace LQGMetric.LocalEvent

/-- **Lusin separation step** (copied from P2-E3a's `GM.gm_ae_preimage_eq_of_saturated`): an
event `{Y ∈ B}` whose indicator is, on a Borel set `W` carrying `Y`, a function of `R(Y)`, is
a.s. equal to `{R(Y) ∈ S}` with `S` Borel. -/
theorem ae_preimage_eq_of_saturated {Ω β γ' : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [MeasurableSpace β] [StandardBorelSpace β] [TopologicalSpace γ'] [T2Space γ']
    [MeasurableSpace γ'] [OpensMeasurableSpace γ'] [SecondCountableTopology γ']
    {Y : Ω → β} {R : β → γ'} (hR : Measurable R) {B W : Set β} (hW : MeasurableSet W)
    (hWB : MeasurableSet (W ∩ B)) (hYW : ∀ᵐ ω ∂P, Y ω ∈ W)
    (hsat : ∀ g₁ ∈ W, ∀ g₂ ∈ W, R g₁ = R g₂ → g₁ ∈ B → g₂ ∈ B) :
    ∃ S : Set γ', MeasurableSet S ∧ Y ⁻¹' B =ᵐ[P] Y ⁻¹' (R ⁻¹' S) := by
  have hs : AnalyticSet (R '' (W ∩ B)) := hWB.analyticSet_image hR
  have ht : AnalyticSet (R '' (W \ (W ∩ B))) := (hW.diff hWB).analyticSet_image hR
  have hdisj : Disjoint (R '' (W ∩ B)) (R '' (W \ (W ∩ B))) := by
    rw [Set.disjoint_left]
    rintro _ ⟨g₁, ⟨hg₁W, hg₁B⟩, rfl⟩ ⟨g₂, ⟨hg₂W, hg₂B⟩, he⟩
    exact hg₂B ⟨hg₂W, hsat g₁ hg₁W g₂ hg₂W he.symm hg₁B⟩
  obtain ⟨u, hsu, htu, hu⟩ := hs.measurablySeparable ht hdisj
  refine ⟨u, hu, ?_⟩
  filter_upwards [hYW] with ω hω
  refine propext ⟨fun hB => hsu ⟨Y ω, ⟨hω, hB⟩, rfl⟩, fun hu' => ?_⟩
  by_contra hB
  exact Set.disjoint_left.1 htu ⟨Y ω, ⟨hω, fun h => hB h.2⟩, rfl⟩ hu'

/-- **Lusin separation for null-measurable events**: as `ae_preimage_eq_of_saturated`, with `B`
only null-measurable for the law of `Y` (e.g. universally measurable). -/
theorem ae_preimage_eq_of_saturated_null {Ω β γ' : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [MeasurableSpace β] [StandardBorelSpace β] [TopologicalSpace γ'] [T2Space γ']
    [MeasurableSpace γ'] [OpensMeasurableSpace γ'] [SecondCountableTopology γ']
    {Y : Ω → β} (hY : Measurable Y) {R : β → γ'} (hR : Measurable R) {B W : Set β}
    (hW : MeasurableSet W) (hB : NullMeasurableSet B (P.map Y)) (hYW : ∀ᵐ ω ∂P, Y ω ∈ W)
    (hsat : ∀ g₁ ∈ W, ∀ g₂ ∈ W, R g₁ = R g₂ → g₁ ∈ B → g₂ ∈ B) :
    ∃ S : Set γ', MeasurableSet S ∧ Y ⁻¹' B =ᵐ[P] Y ⁻¹' (R ⁻¹' S) := by
  obtain ⟨B₁, hB₁s, hB₁m, hB₁e⟩ := hB.exists_measurable_subset_ae_eq
  set B₂ := toMeasurable (P.map Y) B
  have hB₂e : B₂ =ᵐ[P.map Y] B := hB.toMeasurable_ae_eq
  have hnull : (P.map Y) (B₂ \ B₁) = 0 := by
    rw [← ae_eq_empty]
    exact (hB₂e.diff hB₁e).trans (by rw [sdiff_self])
  set W' := W ∩ (B₂ \ B₁)ᶜ
  have hW' : MeasurableSet W' :=
    hW.inter ((measurableSet_toMeasurable _ _).diff hB₁m).compl
  have hYW' : ∀ᵐ ω ∂P, Y ω ∈ W' := by
    have h1 : ∀ᵐ y ∂(P.map Y), y ∉ B₂ \ B₁ := ae_iff.2 (by simpa only [not_not, ofPred_mem_eq] using hnull)
    filter_upwards [hYW, ae_of_ae_map hY.aemeasurable h1] with ω hω h2
    exact ⟨hω, h2⟩
  have hWB : W' ∩ B = W' ∩ B₁ := by
    ext x
    refine ⟨fun ⟨hxW, hxB⟩ => ⟨hxW, ?_⟩, fun ⟨hxW, hx1⟩ => ⟨hxW, hB₁s hx1⟩⟩
    by_contra hx1
    exact hxW.2 ⟨subset_toMeasurable _ _ hxB, hx1⟩
  refine ae_preimage_eq_of_saturated hR hW' (hWB ▸ hW'.inter hB₁m) hYW' ?_
  exact fun g₁ h₁ g₂ h₂ he hB₁ => hsat g₁ h₁.1 g₂ h₂.1 he hB₁

/-- **Local events**: an event `{Y ∈ B}` with `B` null-measurable for the law of `Y` and
determined, on a Borel set `W` carrying the law, by `R(Y)`, is a.s. an event of any σ-algebra `m`
for which some `V` with `V = R(Y)` a.s. is measurable. -/
theorem aeEventIn_of_saturated {Ω : Type} {m : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω}
    {β γ' : Type*} [MeasurableSpace β] [StandardBorelSpace β] [TopologicalSpace γ'] [T2Space γ']
    [MeasurableSpace γ'] [OpensMeasurableSpace γ'] [SecondCountableTopology γ']
    {Y : Ω → β} (hY : Measurable Y) {R : β → γ'} (hR : Measurable R)
    {V : Ω → γ'} (hV : Measurable[m] V) (hVR : ∀ᵐ ω ∂P, V ω = R (Y ω)) {B W : Set β}
    (hW : MeasurableSet W) (hB : NullMeasurableSet B (P.map Y)) (hYW : ∀ᵐ ω ∂P, Y ω ∈ W)
    (hsat : ∀ g₁ ∈ W, ∀ g₂ ∈ W, R g₁ = R g₂ → g₁ ∈ B → g₂ ∈ B) :
    Blueprint.AEEventIn P m (Y ⁻¹' B) := by
  obtain ⟨S, hS, hE⟩ := ae_preimage_eq_of_saturated_null hY hR hW hB hYW hsat
  refine ⟨V ⁻¹' S, hV hS, hE.trans ?_⟩
  filter_upwards [hVR] with ω hω
  show (R (Y ω) ∈ S) = (V ω ∈ S)
  rw [hω]

end LQGMetric.LocalEvent
