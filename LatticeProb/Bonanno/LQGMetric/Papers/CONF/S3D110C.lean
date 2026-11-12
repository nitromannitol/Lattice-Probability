/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D110C at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D110A

/-!
# D110 P5: the trace lemma and CONF Lemma 3.6 on the event `{supp ψ₀ ⊆ int 𝓑^•_τ}`

Source: CONF = Gwynne–Miller, arXiv:1905.00381, `confluence-final.tex`, Lemma 3.6
(C:1308–1320), the field "viewed modulo additive constant" (C:347, 1154, 1187); decision
`decisions/DEC-110.md` §3 (packet P5).

For a field `h` normalized at a mass-one test function `ψ₀` (`h(ψ₀) = 0` surely) and a random
closed set `A`, on the event `E = {supp ψ₀ ⊆ int A}`:

* `confD110_setSigma_supp_subset_interior`: `E ∈ σ(A)` (Effros: `K ⊆ int A` iff a thickening
  of `K` lies in `A`, iff the points of a countable dense subset of the thickening lie in `A`);
* `confD110_localSigma_inter`: **trace lemma**, `F ∈ σ(A, h|_A) ⇒ F ∩ E ∈ σ(A, h|_A mod
  constants)` (generator argument at each hull level with `gm_fieldSigma_eq_fieldSigma0On`);
* `confD110_condExp_eq_on`: `P[X | localSigma h A] = P[X | localSigma0 h A]` a.s. on `E`
  (mathlib's `condExp_ae_eq_restrict_of_measurableSpace_eq_on`);
* `CONFLem3_6AtAENE` (def) and `confLem3_6AtAENE_of_AE0 : CONFLem3_6AtAE0 → CONFLem3_6AtAENE`.

Deviation from the text of DEC-110 §3 (proposed DEVIATIONS entry): `CONFLem3_6AtAENE` takes the
local-set hypothesis in D108's mod-constant form `IsLocalSetDet0` (as `CONFLem3_6AtAE0` does;
the raw `IsLocalSetDet` does not imply it off the event `E`) and the hypothesis
`localSigma h 𝓑^•_τ ≤ 𝓕` (needed for a raw conditional expectation to be non-junk).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter TopologicalSpace Topology
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint GM

section Trace
variable {Ω : Type}

/-- `{K ⊆ int A} ∈ σ(A)` for a random closed set `A` and compact `K` (Effros) -/
theorem confD110_setSigma_supp_subset_interior {A : Ω → Set ℂ} (hA : ∀ ω, IsClosed (A ω))
    {K : Set ℂ} (hK : IsCompact K) : MeasurableSet[setSigma A] {ω | K ⊆ interior (A ω)} := by
  obtain ⟨D₀, hD₀c, hD₀d⟩ := TopologicalSpace.exists_countable_dense ℂ
  have e : {ω | K ⊆ interior (A ω)} = ⋃ m : ℕ, ⋂ q ∈ D₀ ∩ thickening (1 / ((m : ℝ) + 1)) K,
      {ω | (A ω ∩ {q}).Nonempty} := by
    ext ω
    simp only [mem_ofPred_eq, mem_iUnion, mem_iInter, inter_singleton_nonempty]
    constructor
    · intro hKA
      obtain ⟨δ, hδ, hδK⟩ := hK.exists_thickening_subset_open isOpen_interior hKA
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt hδ
      exact ⟨m, fun q hq => interior_subset
        (hδK (thickening_mono hm.le K hq.2))⟩
    · rintro ⟨m, hm⟩
      have hsub : thickening (1 / ((m : ℝ) + 1)) K ⊆ A ω := by
        refine (hD₀d.open_subset_closure_inter isOpen_thickening).trans ?_
        exact (hA ω).closure_subset_iff.2 fun q hq => hm q ⟨hq.2, hq.1⟩
      exact (self_subset_thickening (by positivity) K).trans
        (interior_maximal hsub isOpen_thickening)
  rw [e]
  refine MeasurableSet.iUnion fun m => MeasurableSet.biInter
    (hD₀c.mono inter_subset_left) fun q _ => ?_
  exact gm_setSigma_hit_closed (F := {q}) hA isClosed_singleton

/-- the σ-algebra of the sets whose trace on `E` lies in `m` -/
@[instance_reducible]
def confD110TraceSpace (m : MeasurableSpace Ω) {E : Set Ω} (hE : MeasurableSet[m] E) :
    MeasurableSpace Ω where
  MeasurableSet' F := MeasurableSet[m] (F ∩ E)
  measurableSet_empty := by simp only [empty_inter]; exact @MeasurableSet.empty Ω m
  measurableSet_compl F hF := by
    have e : Fᶜ ∩ E = E \ (F ∩ E) := by
      ext; simp only [mem_inter_iff, mem_compl_iff, Set.mem_sdiff]; tauto
    rw [e]; exact hE.diff hF
  measurableSet_iUnion f hf := by
    rw [iUnion_inter]; exact MeasurableSet.iUnion hf

/-- **trace lemma at one hull level** (DEC-110 §3) -/
theorem confD110_hullSigma_inter (h : Ω → DistC) {ψ₀ : TestC} (hψ₀ : ∫ x, ψ₀ x = 1)
    (h0 : ∀ ω, h ω ψ₀ = 0) {A : Ω → Set ℂ}
    (hE : MeasurableSet[setSigma A] {ω | tsupport (ψ₀ : ℂ → ℝ) ⊆ interior (A ω)}) (n : ℕ)
    {F : Set Ω} (hF : MeasurableSet[hullSigma h A n] F) :
    MeasurableSet[hullSigma0 h A n] (F ∩ {ω | tsupport (ψ₀ : ℂ → ℝ) ⊆ interior (A ω)}) := by
  set E := {ω | tsupport (ψ₀ : ℂ → ℝ) ⊆ interior (A ω)} with hEdef
  have hS0 : setSigma A ≤ hullSigma0 h A n := le_sup_left
  have hE0 : MeasurableSet[hullSigma0 h A n] E := hS0 _ hE
  suffices hle : hullSigma h A n ≤ confD110TraceSpace (hullSigma0 h A n) hE0 from hle _ hF
  refine sup_le (fun G hG => (hS0 _ hG).inter hE0) (MeasurableSpace.generateFrom_le ?_)
  rintro G ⟨S, F', hF', rfl⟩
  show MeasurableSet[hullSigma0 h A n] (({ω | dyadicHull n (A ω) = S} ∩ F') ∩ E)
  by_cases hs : tsupport (ψ₀ : ℂ → ℝ) ⊆ interior S
  · rw [gm_fieldSigma_eq_fieldSigma0On hψ₀ h0
      (V := toOpens (interior S) isOpen_interior) hs] at hF'
    refine MeasurableSet.inter ?_ hE0
    exact (le_sup_right : MeasurableSpace.generateFrom _ ≤ hullSigma0 h A n) _
      (MeasurableSpace.measurableSet_generateFrom ⟨S, F', hF', rfl⟩)
  · have e : ({ω | dyadicHull n (A ω) = S} ∩ F') ∩ E = ∅ := by
      ext ω
      simp only [hEdef, mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨⟨hS, -⟩, hω⟩
      exact hs (hω.trans (interior_subset.trans
        (hS ▸ LocalEvent.subset_interior_dyadicHull n (A ω))))
    rw [e]; exact @MeasurableSet.empty Ω (hullSigma0 h A n)

/-- `σ(A) ≤ σ(A, h|_A mod constants)` -/
theorem confD110_setSigma_le_localSigma0 (h : Ω → DistC) (A : Ω → Set ℂ) :
    setSigma A ≤ localSigma0 h A :=
  le_iInf fun _ => le_sup_left

/-- **trace lemma** (DEC-110 §3): for `h` normalized at `ψ₀`, the raw σ-algebra
`σ(A, h|_A)` and the mod-constant one have the same trace on `{supp ψ₀ ⊆ int A}` -/
theorem confD110_localSigma_inter (h : Ω → DistC) {ψ₀ : TestC} (hψ₀ : ∫ x, ψ₀ x = 1)
    (h0 : ∀ ω, h ω ψ₀ = 0) {A : Ω → Set ℂ}
    (hE : MeasurableSet[setSigma A] {ω | tsupport (ψ₀ : ℂ → ℝ) ⊆ interior (A ω)})
    {F : Set Ω} (hF : MeasurableSet[localSigma h A] F) :
    MeasurableSet[localSigma0 h A] (F ∩ {ω | tsupport (ψ₀ : ℂ → ℝ) ⊆ interior (A ω)}) := by
  unfold localSigma at hF
  unfold localSigma0
  rw [MeasurableSpace.measurableSet_iInf] at hF ⊢
  exact fun n => confD110_hullSigma_inter h hψ₀ h0 hE n (hF n)

/-- **raw and mod-constant conditional expectations agree on `{supp ψ₀ ⊆ int A}`** for `h`
normalized at `ψ₀` and `A` closed -/
theorem confD110_condExp_eq_on [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    (h : Ω → DistC) {ψ₀ : TestC} (hψ₀ : ∫ x, ψ₀ x = 1) (h0 : ∀ ω, h ω ψ₀ = 0)
    {A : Ω → Set ℂ} (hA : ∀ ω, IsClosed (A ω)) (hm : localSigma h A ≤ ‹MeasurableSpace Ω›)
    (f : Ω → ℝ) :
    ∀ᵐ ω ∂P, tsupport (ψ₀ : ℂ → ℝ) ⊆ interior (A ω) →
      P[f | localSigma h A] ω = P[f | localSigma0 h A] ω := by
  set E := {ω | tsupport (ψ₀ : ℂ → ℝ) ⊆ interior (A ω)} with hEdef
  have hEs : MeasurableSet[setSigma A] E :=
    confD110_setSigma_supp_subset_interior hA ψ₀.hasCompactSupport.isCompact
  have hE0 : MeasurableSet[localSigma0 h A] E := confD110_setSigma_le_localSigma0 h A _ hEs
  have hle0 := localSigma0_le_localSigma h A
  have hE : MeasurableSet[localSigma h A] E := hle0 _ hE0
  have key : P[f | localSigma h A] =ᵐ[P.restrict E] P[f | localSigma0 h A] := by
    refine condExp_ae_eq_restrict_of_measurableSpace_eq_on hm (hle0.trans hm) hE fun t => ?_
    constructor
    · intro ht
      have := confD110_localSigma_inter h hψ₀ h0 hEs ht
      rwa [inter_right_comm, inter_self] at this
    · exact fun ht => hle0 _ ht
  exact (ae_restrict_iff' (hm _ hE)).1 key

end Trace

/-! ## CONF Lemma 3.6 on the event `{supp ψ₀ ⊆ int 𝓑^•_τ}` -/

/-- **CONF Lemma 3.6, raw σ-algebras, for a field normalized at `ψ₀`, on the event
`{supp ψ₀ ⊆ int 𝓑^•_τ}`** (DEC-110 §3, packet P5): `CONFLem3_6AtAEN` without the sure
hypothesis `supp ψ₀ ⊆ int 𝓑^•_τ`; the centres and the radii are measurable for the mod-constant
σ-algebra, `𝓑^•_τ` is a local set modulo constants (`IsLocalSetDet0`, CONF Lemma 2.1 read at
C:1154), `σ(𝓑^•_τ, h|_{𝓑^•_τ})` is a sub-σ-algebra, and the conditional lower bound is asserted
on the event `{supp ψ₀ ⊆ int 𝓑^•_τ}`. -/
def CONFLem3_6AtAENE (γ : ℝ) (D : DistC → ContMetric) (c : ℝ → ℝ) (p : CONFParams) : Prop :=
  ∃ α C₀ : ℝ, 0 < α ∧ 1 < C₀ ∧
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ (z₀ : ℂ) (R : ℝ), 0 < R → ∀ τ : Ω → ℝ,
      IsFilledBallStoppingTime D h z₀ τ →
      ∀ ψ₀ : TestC, (∫ x, ψ₀ x = 1) → (∀ ω, h ω ψ₀ = 0) →
      IsLocalSetDet0 P h (fun ω => filledBall (D (h ω)) z₀ (τ ω)) →
      localSigma h (fun ω => filledBall (D (h ω)) z₀ (τ ω)) ≤ ‹MeasurableSpace Ω› →
      ∀ (x : Ω → ℂ) (ε : Ω → ℝ),
      @Measurable Ω ℂ (localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (τ ω))) _ x →
      @Measurable Ω ℝ (localSigma0 h (fun ω => filledBall (D (h ω)) z₀ (τ ω))) _ ε →
      (∀ᵐ ω ∂P, x ω ∈ frontier (filledBall (D (h ω)) z₀ (τ ω))) → (∀ ω, ε ω ∈ Ioo 0 1) →
      (Set.range ε).Countable →
      ∃ G : Set Ω,
        AEEventIn P (filledBallSigmaAt D h z₀
          (fun ω => confSigma (xiGamma γ) c D P h p z₀ R (ε ω) (τ ω) ω)) G ∧
        (∀ ω ∈ G, x ω ∈ frontier (filledBall (D (h ω)) z₀ (τ ω)) →
          confRK (xiGamma γ) c D P h p R (ε ω) (filledBall (D (h ω)) z₀ (τ ω)) ω ≤
            Metric.ediam (filledBall (D (h ω)) z₀ (τ ω)) →
          ∀ (y : ℂ) (Q : ℝ → ℂ) (L : ℝ),
            y ∉ enbhd (confRK (xiGamma γ) c D P h p R (ε ω) (filledBall (D (h ω)) z₀ (τ ω)) ω)
              (filledBall (D (h ω)) z₀ (τ ω)) →
            IsGeodesicL (D (h ω)) Q L z₀ y → ∀ u ∈ Icc 0 L,
              Q u ∉ Metric.ball (x ω) (ε ω * R) \ filledBall (D (h ω)) z₀ (τ ω)) ∧
        ∀ᵐ ω ∂P, tsupport (ψ₀ : ℂ → ℝ) ⊆ interior (filledBall (D (h ω)) z₀ (τ ω)) →
          1 - C₀ * ε ω ^ α ≤
          (P[G.indicator (fun _ => (1 : ℝ)) |
            localSigma h (fun ω => filledBall (D (h ω)) z₀ (τ ω))]) ω

/-- **the on-event raw form is an instance of the mod-constant form** (DEC-110 §3):
`CONFLem3_6AtAE0 → CONFLem3_6AtAENE`, by the trace lemma `confD110_condExp_eq_on` -/
theorem confLem3_6AtAENE_of_AE0 {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ} {p : CONFParams}
    (H0 : CONFLem3_6AtAE0 γ D c p) : CONFLem3_6AtAENE γ D c p := by
  obtain ⟨α, C₀, hα, hC₀, H⟩ := H0
  refine ⟨α, C₀, hα, hC₀, ?_⟩
  intro Ω _ P _ h hh z₀ R hR τ hτ ψ₀ hψ₀ h0 hdet hm x ε hx hε hxf hε01 hεc
  obtain ⟨G, ⟨F, hFm, hFe⟩, hGA, hGc⟩ := H P h hh z₀ R hR τ (hτ.ae P) hdet
    ((localSigma0_le_localSigma h _).trans hm) x ε hx hε hxf hε01 hεc
  refine ⟨G, ⟨F, filledBallSigmaAt0_le D h z₀ _ F hFm, hFe⟩, hGA, ?_⟩
  filter_upwards [hGc, confD110_condExp_eq_on (P := P) h hψ₀ h0
    (fun ω => gm_filledBall_isClosed _ _ _) hm (G.indicator fun _ => (1 : ℝ))] with ω h1 h2 hω
  rw [h2 hω]
  exact h1

end LQGMetric.CONF
