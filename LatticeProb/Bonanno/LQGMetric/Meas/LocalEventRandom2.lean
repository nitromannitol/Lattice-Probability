/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Meas.LocalEventRandom2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Meas.LocalEventRandom
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.GoodAnnulusMeas4

/-!
# Local events of a random local set: Lusin separation on each hull piece (task P2-E2R)

The random-set version of `LocalEvent.aeEventIn_of_saturated` (handoff/P2-LOCMEAS.md,
"Random-set case"): let `𝒜 : DistC → Set ℂ` give a random closed set `A = 𝒜(h)` which is a.s.
bounded, and let `B ⊆ DistC` be an event which, on each piece `{A^{(n)} = S}` (`S` a finite union
of level-`n` dyadic squares), is determined by the internal metric `D_h(·,·; int S)`
(saturation) and null-measurable for the law of `h`. Then `{h ∈ B}` is a.s. an event of
`σ(A, h|_A)` (`localSigma`, D32): on each piece apply Lusin separation with Axiom II on `int S`
(as in `GM.gm_L3_7meas`), and glue by `LocalEvent.aeEventIn_localSigma_of_pieces`.

`measurableSet_localSigma_prod_of_code` packages countably many such events into a
`σ(A, h|_A) ⊗ Borel`-measurable set (joint measurability in a Borel parameter `x`).

Own arguments around mathlib's separation theorem and Axiom II (DEVIATIONS entry proposed in
handoff/P2-E2R.md).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.LocalEvent

/-- **Random-set Lusin step** (one hull piece): with `U = int S` nonempty, a saturated
null-measurable event agrees on `{A^{(n)} = S}` with a `σ(h|_U)`-event. -/
theorem exists_fieldSigma_piece {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hgp : IsGFFPlusCont h P)
    (hlen : ∀ᵐ ω ∂P, D (h ω) ∈ lenSet) {U : Set ℂ} (hUo : IsOpen U) {Bs : Set DistC}
    (hnull : NullMeasurableSet Bs (P.map h))
    (hsat : ∀ g₁ g₂, D g₁ ∈ lenSet → D g₂ ∈ lenSet → (D g₁).internal U = (D g₂).internal U →
      g₁ ∈ Bs → g₂ ∈ Bs) :
    ∃ F, MeasurableSet[fieldSigma h (toOpens U hUo)] F ∧ h ⁻¹' Bs =ᵐ[P] F := by
  classical
  have hhm : Measurable h := hgp.1
  by_cases hU : U.Nonempty
  · obtain ⟨Φ, hΦ, hΦae⟩ := hD.locality P h hgp (toOpens U hUo)
    have : Nonempty U := hU.to_subtype
    set q : ℕ → ℂ := fun n => (TopologicalSpace.denseSeq U n : ℂ) with hq
    have hqU : ∀ n, q n ∈ U := fun n => (TopologicalSpace.denseSeq U n).2
    have hqd : U ⊆ closure (range q) := by
      intro x hx
      rw [_root_.mem_closure_iff]
      intro o ho hxo
      obtain ⟨n, hn⟩ := (TopologicalSpace.denseRange_denseSeq U).exists_mem_open
        (ho.preimage continuous_subtype_val) ⟨⟨x, hx⟩, hxo⟩
      exact ⟨q n, hn, n, rfl⟩
    let R : DistC → (ℕ × ℕ → ℝ≥0∞) := fun g p => (D g).chainInf U (q p.1) (q p.2)
    let G : DistOn (toOpens U hUo) → (ℕ × ℕ → ℝ≥0∞) := fun x p => Φ x (q p.1) (q p.2)
    have hR : Measurable R := measurable_pi_iff.2 fun p =>
      GM.measurable_chainInf_comp hD.measurable measurable_const measurable_const _
    have hG : Measurable G := measurable_pi_iff.2 fun p =>
      (measurable_pi_apply _).comp ((measurable_pi_apply _).comp hΦ)
    have hV : Measurable[fieldSigma h (toOpens U hUo)] fun ω => G (restrictTo _ (h ω)) :=
      hG.comp (Measurable.of_comap_le le_rfl)
    have hVR : ∀ᵐ ω ∂P, G (restrictTo (toOpens U hUo) (h ω)) = R (h ω) := by
      filter_upwards [hΦae, hlen] with ω h1 h3
      funext p
      show Φ _ (q p.1) (q p.2) = (D (h ω)).chainInf U (q p.1) (q p.2)
      rw [← h1 _ (hqU _) _ (hqU _)]
      exact (D (h ω)).internal_eq_chainInf (isLength_of_mem_lenSet h3) hUo _ _
    have hW : MeasurableSet (D ⁻¹' lenSet) := measurableSet_lenSet.preimage hD.measurable
    have hs : ∀ g₁ ∈ D ⁻¹' lenSet, ∀ g₂ ∈ D ⁻¹' lenSet, R g₁ = R g₂ → g₁ ∈ Bs → g₂ ∈ Bs := by
      intro g₁ h1 g₂ h2 he hB
      have l1 := isLength_of_mem_lenSet h1
      have l2 := isLength_of_mem_lenSet h2
      refine hsat g₁ g₂ h1 h2 ?_ hB
      refine GM.internal_eq_of_dense l1 l2 hUo hqU hqd fun i j => ?_
      rw [(D g₁).internal_eq_chainInf l1 hUo, (D g₂).internal_eq_chainInf l2 hUo]
      exact congrFun he (i, j)
    exact aeEventIn_of_saturated hhm hR hV hVR hW hnull hlen hs
  · -- `U = ∅`: all internal metrics on `U` coincide
    rw [not_nonempty_iff_eq_empty] at hU
    subst hU
    have hint : ∀ g₁ g₂ : DistC, (D g₁).internal ∅ = (D g₂).internal ∅ := fun g₁ g₂ => by
      funext x y
      rw [GM.internal_eq_top_of_notMem _ (notMem_empty x),
        GM.internal_eq_top_of_notMem _ (notMem_empty x)]
    by_cases hex : ∃ g₁, D g₁ ∈ lenSet ∧ g₁ ∈ Bs
    · obtain ⟨g₁, hg₁, hB₁⟩ := hex
      refine ⟨univ, @MeasurableSet.univ Ω (fieldSigma h _), ?_⟩
      filter_upwards [hlen] with ω hω
      exact propext ⟨fun _ => trivial, fun _ => hsat g₁ (h ω) hg₁ hω (hint _ _) hB₁⟩
    · refine ⟨∅, @MeasurableSet.empty Ω (fieldSigma h _), ?_⟩
      filter_upwards [hlen] with ω hω
      exact propext ⟨fun hB => hex ⟨h ω, hω, hB⟩, fun h => h.elim⟩

/-- **Random-set version of `aeEventIn_of_saturated`**: for a random closed set `𝒜(h)` which is
a.s. bounded, an event `{h ∈ B}` which on each hull piece `{𝒜(h)^{(n)} = S}` is determined by
the internal metric of `D_h` on `int S` (and null-measurable) is a.s. a `σ(𝒜(h), h|_{𝒜(h)})`-event. -/
theorem aeEventIn_localSigma_of_saturated {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hgp : IsGFFPlusCont h P)
    (hlen : ∀ᵐ ω ∂P, D (h ω) ∈ lenSet) (𝒜 : DistC → Set ℂ) (hA : ∀ g, IsClosed (𝒜 g))
    (hb : ∀ᵐ ω ∂P, Bornology.IsBounded (𝒜 (h ω))) {B : Set DistC}
    (hnull : ∀ n s, NullMeasurableSet (B ∩ {g | dyadicHull n (𝒜 g) = hullFin n s}) (P.map h))
    (hsat : ∀ n s g₁ g₂, D g₁ ∈ lenSet → D g₂ ∈ lenSet →
      (D g₁).internal (interior (hullFin n s)) = (D g₂).internal (interior (hullFin n s)) →
      dyadicHull n (𝒜 g₁) = hullFin n s → g₁ ∈ B →
        dyadicHull n (𝒜 g₂) = hullFin n s ∧ g₂ ∈ B) :
    AEEventIn P (localSigma h (fun ω => 𝒜 (h ω))) (h ⁻¹' B) := by
  refine aeEventIn_localSigma_of_pieces h (fun ω => hA (h ω)) hb fun n s => ?_
  obtain ⟨F, hF, hEF⟩ := exists_fieldSigma_piece hD P h hgp hlen isOpen_interior (hnull n s)
    (fun g₁ g₂ h1 h2 he hB => (hsat n s g₁ g₂ h1 h2 he hB.2 hB.1).symm)
  refine ⟨F, hF, ?_⟩
  filter_upwards [hEF] with ω hω hS
  have := Iff.of_eq hω
  simp only [mem_preimage, mem_inter_iff, mem_ofPred_eq, hS, and_true] at this
  exact this

/-- countably many a.s.-`m`-events form an `m`-measurable code -/
theorem exists_measurable_code {Ω : Type} {m : MeasurableSpace Ω} [MeasurableSpace Ω] {P : Measure Ω}
    {ι : Type*} [Countable ι] {E : ι → Set Ω} (hE : ∀ i, AEEventIn P m (E i)) :
    ∃ Z : Ω → ι → Bool, Measurable[m] Z ∧ ∀ᵐ ω ∂P, ∀ i, (Z ω i = true ↔ ω ∈ E i) := by
  classical
  choose F hFm hEF using hE
  refine ⟨fun ω i => decide (ω ∈ F i), ?_, ?_⟩
  · have hi : ∀ i, Measurable[m] (fun ω => decide (ω ∈ F i)) := fun i => by
      refine @measurable_to_bool Ω m _ ?_
      convert hFm i using 1
      ext ω
      simp
    exact @Measurable.of_eval Ω ι (fun _ => Bool) m _ _ hi
  · rw [ae_all_iff]
    intro i
    filter_upwards [hEF i] with ω hω
    simp only [decide_eq_true_eq]
    exact (Iff.of_eq hω).symm

end LQGMetric.LocalEvent
