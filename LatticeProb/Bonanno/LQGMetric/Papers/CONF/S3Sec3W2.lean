/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3Sec3W2 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108M10
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108M4
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108Q3

/-!
# CONF L2.10 at `confU` threaded through the L3.3 Step 3 chain (DEC-127 packet J, P2-CONFW)

DEC-127 (final): CONF Lemma 2.10 (C:712) is proved only at `U = confU r δ z T`, the only domains
CONF uses (C:1236–1243). `CONFLem2_10At U` is `CONFLem2_10` at one `U`; the hypothesis of the
chain is `CONFLem2_10AtConfU := ∀ r δ z T, CONFLem2_10At (toOpens (confU r δ z T) _)`.

The declarations below are copies (only the `hL` hypothesis changed, and its use) of:
`fkg_sets_zb_of_lem2_10`, `confProp2_8_frozen` (S3D108K1), `confProp2_8_chain_ne` (S3D108M3),
`zbDiamSet_fkg_frozen` (S3D108M4), `confFKGFrozenEUc_of` (S3D108M6),
`confFKGFrozenEUc_of_outside` (M8), `confFKGFrozenEUc_of_link` (M9),
`confFKGFrozenEUc_of_link'` (M10). The `U` of each use is `toOpens (confU r p.δ z T)`
(M6, `hZB`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology TopologicalSpace
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

/-- **CONF Lemma 2.10 at one domain `U`** (C:712–742): for the zero-boundary GFF `X` on `U`
(extended by `0`) and `Φ, Ψ` as in `IsFKGFunZB`, `Cov(Φ(X), Ψ(X)) ≥ 0`. `CONFLem2_10` is
`∀ U, CONFLem2_10At U`. -/
def CONFLem2_10At (U : TopologicalSpace.Opens ℂ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → DistC),
    IsZBExtField U X P → ∀ Φ Ψ : DistC → ℝ, IsFKGFunZB P X Φ → IsFKGFunZB P X Ψ →
      0 ≤ cov[fun ω => Φ (X ω), fun ω => Ψ (X ω); P]

/-- **CONF Lemma 2.10 at the domains `confU r δ z T`** (DEC-127) -/
def CONFLem2_10AtConfU : Prop :=
  ∀ (r δ : ℝ) (z : ℂ) (T : Finset (ℤ × ℤ)), CONFLem2_10At (toOpens (confU r δ z T) (isOpen_confU r δ z T))

/-- `CONFLem2_10At U` from a white-noise model of the coarse/fine splitting on `U` -/
lemma confLem2_10At_of_model {U : TopologicalSpace.Opens ℂ} (H : CONFZBCoarseModel U) :
    CONFLem2_10At U :=
  fun P _ X hX Φ Ψ hΦ hΨ => confLem2_10_at_of_model H P X hX Φ Ψ hΦ hΨ

section FKGSets

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {U : TopologicalSpace.Opens ℂ}

/-- **FKG for decreasing events of the zero-boundary GFF** (from CONF Lemma 2.10): two events
of `X` that are a.s. non-increasing and a.s. continuous along continuous perturbations are
positively correlated. -/
theorem fkg_sets_zb_at (hL : CONFLem2_10At U) {X : Ω → DistC}
    (hX : IsZBExtField U X P) {A B : Set DistC} (hA : MeasurableSet A)
    (hB : MeasurableSet B)
    (hAm : ∀ᵐ ω ∂P, ∀ f g : C(ℂ, ℝ), f ≤ g → addFun (X ω) g ∈ A → addFun (X ω) f ∈ A)
    (hAc : ∀ᵐ ω ∂P, ∀ fn : ℕ → C(ℂ, ℝ), Tendsto fn atTop (𝓝 0) →
      ∀ᶠ n in atTop, (addFun (X ω) (fn n) ∈ A ↔ X ω ∈ A))
    (hBm : ∀ᵐ ω ∂P, ∀ f g : C(ℂ, ℝ), f ≤ g → addFun (X ω) g ∈ B → addFun (X ω) f ∈ B)
    (hBc : ∀ᵐ ω ∂P, ∀ fn : ℕ → C(ℂ, ℝ), Tendsto fn atTop (𝓝 0) →
      ∀ᶠ n in atTop, (addFun (X ω) (fn n) ∈ B ↔ X ω ∈ B)) :
    P.map X A * P.map X B ≤ P.map X (A ∩ B) := by
  have h := hL P X hX _ _ (isFKGFunZB_neg_indicator hA hAm hAc)
    (isFKGFunZB_neg_indicator hB hBm hBc)
  have e : ∀ S : Set DistC, (fun ω => -S.indicator (1 : DistC → ℝ) (X ω)) =
      -(fun ω => S.indicator (1 : DistC → ℝ) (X ω)) := fun _ => rfl
  rw [e, e, covariance_neg_left, covariance_neg_right, neg_neg] at h
  exact prob_mul_le_of_cov_nonneg hX.measurable hA hB h

/-- **CONF Proposition 2.8 in the frozen form of Lemma 3.3, Step 3** (C:1236–1243), the
hypothesis `hfkg` of `condFKG_freeze2`: `X` a zero-boundary GFF on `U` extended by `0`; `SG, SF ⊆ β × 𝒟'(ℂ)`
measurable; for a.e. frozen outside datum `w` (law of `W`) and a.e. `x` (law of `X`), the sections
`SG_w`, `SF_w` are non-increasing and continuous along continuous perturbations of `x`. Then for
a.e. `w`, `P_X(SG_w) P_X(SF_w) ≤ P_X(SG_w ∩ SF_w)`. -/
theorem confProp2_8_frozen_at (hL : CONFLem2_10At U) {β : Type} [MeasurableSpace β] {W : Ω → β}
    {X : Ω → DistC} (hX : IsZBExtField U X P) {SG SF : Set (β × DistC)}
    (hSG : MeasurableSet SG) (hSF : MeasurableSet SF)
    (hGm : ∀ᵐ w ∂(P.map W), ∀ᵐ x ∂(P.map X), ∀ f g : C(ℂ, ℝ), f ≤ g →
      (w, addFun x g) ∈ SG → (w, addFun x f) ∈ SG)
    (hGc : ∀ᵐ w ∂(P.map W), ∀ᵐ x ∂(P.map X), ∀ fn : ℕ → C(ℂ, ℝ), Tendsto fn atTop (𝓝 0) →
      ∀ᶠ n in atTop, ((w, addFun x (fn n)) ∈ SG ↔ (w, x) ∈ SG))
    (hFm : ∀ᵐ w ∂(P.map W), ∀ᵐ x ∂(P.map X), ∀ f g : C(ℂ, ℝ), f ≤ g →
      (w, addFun x g) ∈ SF → (w, addFun x f) ∈ SF)
    (hFc : ∀ᵐ w ∂(P.map W), ∀ᵐ x ∂(P.map X), ∀ fn : ℕ → C(ℂ, ℝ), Tendsto fn atTop (𝓝 0) →
      ∀ᶠ n in atTop, ((w, addFun x (fn n)) ∈ SF ↔ (w, x) ∈ SF)) :
    ∀ᵐ w ∂(P.map W), P.map X (Prod.mk w ⁻¹' SG) * P.map X (Prod.mk w ⁻¹' SF) ≤
      P.map X (Prod.mk w ⁻¹' SG ∩ Prod.mk w ⁻¹' SF) := by
  have hXa := hX.measurable.aemeasurable (μ := P)
  filter_upwards [hGm, hGc, hFm, hFc] with w h1 h2 h3 h4
  exact fkg_sets_zb_at hL hX (measurable_prodMk_left hSG) (measurable_prodMk_left hSF)
    (ae_of_ae_map hXa h1) (ae_of_ae_map hXa h2) (ae_of_ae_map hXa h3) (ae_of_ae_map hXa h4)

end FKGSets

section Chain

variable {Ω β : Type} [MeasurableSpace Ω] [MeasurableSpace β] {P : Measure Ω}
  [IsProbabilityMeasure P]

/-- **CONF Proposition 2.8, frozen form, for chain-formula diameter events on two frozen fields,
with S-cont-law as hypotheses** (C:656–669, C:748–752): the inputs on the frozen fields are Axiom
III and the a.s. non-attainment of the thresholds on the frozen law. -/
theorem confProp2_8_chain_ne_at {U : TopologicalSpace.Opens ℂ} (hL : CONFLem2_10At U) {γ : ℝ}
    (hγ : 0 < γ) {D : DistC → ContMetric} (hDm : Measurable D) {W : Ω → β}
    {X : Ω → DistC} (hX : IsZBExtField U X P) {G₁ G₂ : β → DistC} (hG₁ : Measurable G₁)
    (hG₂ : Measurable G₂)
    (hwe₁ : ∀ᵐ w ∂(P.map W), ∀ᵐ x ∂(P.map X), WeylAt (xiGamma γ) D (G₁ w + x))
    (hwe₂ : ∀ᵐ w ∂(P.map W), ∀ᵐ x ∂(P.map X), WeylAt (xiGamma γ) D (G₂ w + x))
    {FzG FzF : β → Prop} (hFzG : MeasurableSet {w | FzG w}) (hFzF : MeasurableSet {w | FzF w})
    {ι ι' : Type} {I : Set ι} {I' : Set ι'} (hI : I.Finite)
    (hI' : I'.Finite) {A V : ι → Set ℂ} {A' V' : ι' → Set ℂ} (hA : ∀ i ∈ I, (A i).Countable)
    (hA' : ∀ i ∈ I', (A' i).Countable) (hV : ∀ i, IsOpen (V i))
    (hVb : ∀ i, Bornology.IsBounded (V i)) (hV' : ∀ i, IsOpen (V' i))
    (hVb' : ∀ i, Bornology.IsBounded (V' i)) {T : β → ι → ℝ≥0∞} {T' : β → ι' → ℝ≥0∞}
    (hTm : ∀ i ∈ I, Measurable fun w => T w i) (hTm' : ∀ i ∈ I', Measurable fun w => T' w i)
    (hneG : ∀ᵐ w ∂(P.map W), ∀ᵐ x ∂(P.map X),
      ∀ i ∈ I, internalDiam (D (G₁ w + x)) (A i) (V i) ≠ T w i)
    (hneF : ∀ᵐ w ∂(P.map W), ∀ᵐ x ∂(P.map X),
      ∀ i ∈ I', internalDiam (D (G₂ w + x)) (A' i) (V' i) ≠ T' w i) :
    ∀ᵐ w ∂(P.map W),
      P.map X (Prod.mk w ⁻¹' frozenChainEv D G₁ FzG I A V T) *
          P.map X (Prod.mk w ⁻¹' frozenChainEv D G₂ FzF I' A' V' T') ≤
        P.map X (Prod.mk w ⁻¹' frozenChainEv D G₁ FzG I A V T ∩
          Prod.mk w ⁻¹' frozenChainEv D G₂ FzF I' A' V' T') := by
  have hSG := measurableSet_frozenChainEv hDm hG₁ hFzG hI.countable hA hTm (V := V)
  have hSF := measurableSet_frozenChainEv hDm hG₂ hFzF hI'.countable hA' hTm' (V := V')
  have hG' := chainEv_mono_cont (Fz := FzG) hγ hwe₁ hI hV hVb hneG
  have hF'' := chainEv_mono_cont (Fz := FzF) hγ hwe₂ hI' hV' hVb' hneF
  refine confProp2_8_frozen_at hL hX hSG hSF ?_ ?_ ?_ ?_
  · filter_upwards [hG'] with w hw; filter_upwards [hw] with x hx; exact hx.1
  · filter_upwards [hG'] with w hw; filter_upwards [hw] with x hx; exact hx.2
  · filter_upwards [hF''] with w hw; filter_upwards [hw] with x hx; exact hx.1
  · filter_upwards [hF''] with w hw; filter_upwards [hw] with x hx; exact hx.2

end Chain

section Bridge

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The FKG part of `CONFFKGFrozenEU`** (CONF Prop 2.8 at C:1236–1243, for countable `A i`):
for a.e. frozen outside datum `v`, the zero-boundary diameter event `G^U = zbDiamSet V Fm A t`
and the section of any measurable chain-formula event on the field `G v + x = recField`
(S-cont-law for it as a hypothesis) are positively correlated under the law of `X`. -/
theorem zbDiamSet_fkg_frozen_at {U : Set ℂ} {hU : IsOpen U} (hL : CONFLem2_10At (toOpens U hU))
    {γ : ℝ} (hγ : 0 < γ) {D : DistC → ContMetric}
    {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) {h : Ω → DistC} (hh : IsWholePlaneGFF h P)
    {ρ : ℝ} {w : ℂ} (hUb : Bornology.IsBounded U) {X G : Ω → DistC}
    (hX : IsL33ZBPart P h ρ w U hU X) (hGm : Measurable[recSigma h ρ w Uᶜ] G)
    (hXG : ∀ ω, X ω = recField h ρ w ω - G ω) (hZB : IsZBExtField (toOpens U hU) X P)
    {ι : Type} [Finite ι] (V : ι → Opens ℂ) (hVU : ∀ i, closure (V i : Set ℂ) ⊆ U)
    (Fm : ∀ i, DistOn (V i) → ℂ → ℂ → ℝ≥0∞) (hFm : ∀ i, Measurable (Fm i))
    (hFmid : ∀ i, ∀ᵐ ω ∂P, ∀ 𝔥 : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd 𝔥 U →
      (∀ φ : TestOn (toOpens U hU),
        restrictTo (toOpens U hU) (recField h ρ w ω - X ω) φ = ∫ x, 𝔥 x * φ x) →
      ∀ f : C(ℂ, ℝ), tsupport ⇑f ⊆ U → EqOn ⇑f 𝔥 (V i : Set ℂ) →
      ∀ u ∈ V i, ∀ v ∈ V i,
        (D (addFun (recField h ρ w ω) (-f))).internal (V i) u v =
          Fm i (restrictTo (V i) (X ω)) u v)
    (A : ι → Set ℂ) (hAV : ∀ i, A i ⊆ V i) (hAc : ∀ i, (A i).Countable) {t : ℝ} (ht : 0 < t)
    {FzF : SigOmega Ω (recSigma h ρ w Uᶜ) → Prop} (hFzF : MeasurableSet {v | FzF v})
    {ι' : Type} {I' : Set ι'} (hI' : I'.Finite) {A' V' : ι' → Set ℂ}
    (hA' : ∀ i ∈ I', (A' i).Countable) (hV' : ∀ i, IsOpen (V' i))
    (hVb' : ∀ i, Bornology.IsBounded (V' i))
    {T' : SigOmega Ω (recSigma h ρ w Uᶜ) → ι' → ℝ≥0∞}
    (hTm' : ∀ i ∈ I', Measurable fun v => T' v i)
    (hneF : ∀ᵐ v ∂(P.map (toSig (recSigma h ρ w Uᶜ))), ∀ᵐ x ∂(P.map X),
      ∀ i ∈ I', internalDiam (D (G v.val + x)) (A' i) (V' i) ≠ T' v i) :
    ∀ᵐ v ∂(P.map (toSig (recSigma h ρ w Uᶜ))),
      P.map X (zbDiamSet V Fm A t) *
          P.map X (Prod.mk v ⁻¹' frozenChainEv D (fun v => G v.val) FzF I' A' V' T') ≤
        P.map X (zbDiamSet V Fm A t ∩
          Prod.mk v ⁻¹' frozenChainEv D (fun v => G v.val) FzF I' A' V' T') := by
  have hle : recSigma h ρ w Uᶜ ≤ mΩ := recSigma_le hh ρ w Uᶜ
  have hXm : Measurable X := hX.1
  have hind := hX.2.1
  have hWm : Measurable (toSig (recSigma h ρ w Uᶜ)) := measurable_toSig hle
  have hval : @Measurable (SigOmega Ω (recSigma h ρ w Uᶜ)) Ω _ (recSigma h ρ w Uᶜ)
      SigOmega.val := comap_measurable _
  have hG₂m : Measurable fun v : SigOmega Ω (recSigma h ρ w Uᶜ) => G v.val := hGm.comp hval
  -- the cut-off of the harmonic part on `⋃ V i`
  have hcl : closure (⋃ i, (V i : Set ℂ)) ⊆ U := by
    rw [closure_iUnion_of_finite]; exact iUnion_subset hVU
  have hVc : IsCompact (closure (⋃ i, (V i : Set ℂ))) :=
    (hUb.subset (subset_closure.trans hcl)).isCompact_closure
  obtain ⟨φ, δ', hδ', hcut0⟩ := exists_cutoff33G hU hVc hcl
  have hcut : ∀ (T : DistC) (𝔥 : ℂ → ℝ), InnerProductSpace.HarmonicOnNhd 𝔥 U →
      (∀ ψ : TestOn (toOpens U hU), restrictTo (toOpens U hU) T ψ = ∫ y, 𝔥 y * ψ y) →
      tsupport ⇑(DFGPS.L217.harmFn φ δ' hδ' T) ⊆ U ∧
        ∀ i, EqOn ⇑(DFGPS.L217.harmFn φ δ' hδ' T) 𝔥 (V i : Set ℂ) := fun T 𝔥 h1 h2 =>
    ⟨(hcut0 T 𝔥 h1 h2).1, fun i => (hcut0 T 𝔥 h1 h2).2.mono (subset_iUnion (fun j => (V j : Set ℂ)) i)⟩
  have hsec := ae_ae_zbDiamSet_eq hD hh hU hX hGm hXG V Fm hFm hFmid A hAV hAc t hcut
  -- bumps for the `V i`
  have hbump : ∀ i, ∃ F : TestC, (∀ x ∈ (V i : Set ℂ), F x = 1) ∧ tsupport (F : ℂ → ℝ) ⊆ U :=
    fun i => exists_testC_bump hU (hUb.subset (subset_closure.trans (hVU i))) (hVU i)
  choose F hF hFU using hbump
  -- Axiom III on the frozen law for both fields
  have hrec : IsWholePlaneGFF (fun ω => G (toSig (recSigma h ρ w Uᶜ) ω).val + X ω) P := by
    have e : (fun ω => G (toSig (recSigma h ρ w Uᶜ) ω).val + X ω) = recField h ρ w :=
      funext fun ω => by simp only [toSig, hXG ω, add_sub_cancel]
    rw [e]; exact isWholePlaneGFF_recField hh ρ w
  have hg : Measurable fun v : SigOmega Ω (recSigma h ρ w Uᶜ) =>
      -DFGPS.L217.harmFn φ δ' hδ' (G v.val) :=
    continuous_neg.measurable.comp ((DFGPS.L217.measurable_harmFn φ δ' hδ').comp hG₂m)
  have hG₁m : Measurable fun v : SigOmega Ω (recSigma h ρ w Uᶜ) =>
      addFun (G v.val) (-DFGPS.L217.harmFn φ δ' hδ' (G v.val)) :=
    measurable_addFun.comp (hG₂m.prodMk hg)
  have hwe₁ := ae_ae_weylAt_addFun hD hWm hXm hind hG₂m hrec hg
  have hwe₂ := ae_ae_weylAt hD hWm hXm hind hG₂m hrec
  have hT0 : ENNReal.ofReal t ≠ 0 := (ENNReal.ofReal_pos.2 ht).ne'
  have hneG := ae_ae_diam_ne_family_of_weyl hγ hD.measurable (U := toOpens U hU) hUb hZB hwe₁
    (I := univ) finite_univ (A := A) (fun i _ => hAc i) (fun i => (V i).isOpen) F
    (fun i _ => hF i) (fun i _ => hFU i) (T := fun _ _ => ENNReal.ofReal t) (fun _ _ => hT0)
    (fun _ _ => ENNReal.ofReal_ne_top)
  have main := confProp2_8_chain_ne_at hL hγ hD.measurable hZB hG₁m hG₂m
    hwe₁ hwe₂ (FzG := fun _ => True) (by simp) hFzF (I := univ) finite_univ hI' (A := A)
    (fun i _ => hAc i) hA' (fun i => (V i).isOpen)
    (fun i => hUb.subset (subset_closure.trans (hVU i))) hV' hVb'
    (fun _ _ => measurable_const) hTm' hneG hneF
  exact frozen_fkg_congr_ae hsec (ae_of_all _ fun _ => EventuallyEq.rfl) main

end Bridge

/-- **CONF Proposition 2.8 in the frozen form of Lemma 3.3, Step 3** (C:656–669, C:1236–1243):
`CONFFKGFrozenEU` for countable `A i`, from CONF Lemma 2.10 and the two one-sentence claims
`CONFEUOutside13`, `CONFEUSContLaw`. -/
theorem confFKGFrozenEUc_of_at (hL : CONFLem2_10AtConfU) {γ : ℝ} (hγ : 0 < γ) {D : DistC → ContMetric}
    {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) {p : CONFParams} (hδ : 0 < p.δ)
    (hO : CONFEUOutside13 γ D c p) (hS : CONFEUSContLaw γ D c p) :
    CONFFKGFrozenEUc γ D c p := by
  intro Ω _ P _ h hh z r hr T hT ρ w hρ hUw X G hX hGm hXG hZB
  have hU := isOpen_confU r p.δ z T
  have hUb := isBounded_confU r p.δ z T
  have hle := recSigma_le hh ρ w (confU r p.δ z T)ᶜ
  have hval : @Measurable (SigOmega Ω (recSigma h ρ w (confU r p.δ z T)ᶜ)) Ω _
      (recSigma h ρ w (confU r p.δ z T)ᶜ) SigOmega.val := comap_measurable _
  have hG₂m : Measurable fun v : SigOmega Ω (recSigma h ρ w (confU r p.δ z T)ᶜ) => G v.val :=
    hGm.comp hval
  obtain ⟨B, hBm, hB13⟩ := hO P h hh z r hr T hT ρ w hρ hUw
  obtain ⟨A₀, hA₀c, hA₀, hEU⟩ := confEU_ae_eq_chain hD hh p hr z T ρ w hXG hB13
  have hSfin : (confSqIdx (p.δ * r) z (annulus z (3 * r) (4 * r))).Finite :=
    finite_confSqIdx_annulus (mul_pos hδ hr) z _ _
  have hFz : MeasurableSet {v : SigOmega Ω (recSigma h ρ w (confU r p.δ z T)ᶜ) | v.val ∈ B} :=
    measurableSet_val_preimage hBm
  have hca : Measurable[recSigma h ρ w (confU r p.δ z T)ᶜ]
      fun ω => circleAvg (recField h ρ w ω) r z :=
    GM.measurable_circleAvg_fieldSigmaClosed (recField h ρ w) r z
      (sphere_subset_compl_confU hr p.δ z T)
  have hTm : Measurable fun v : SigOmega Ω (recSigma h ρ w (confU r p.δ z T)ᶜ) =>
      euThr (xiGamma γ) c p h ρ w r z v.val :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul
      (Real.measurable_exp.comp (measurable_const.mul (hca.comp hval))))
  have hannO : ∀ _ : ℤ × ℤ, IsOpen (annulus z (2 * r) (5 * r) : Set ℂ) :=
    fun _ => (annulus z (2 * r) (5 * r)).isOpen
  refine ⟨_, measurableSet_frozenChainEv hD.measurable hG₂m hFz hSfin.countable
    (fun k _ => hA₀c k) (fun _ _ => hTm), hEU, ?_⟩
  intro ι _ V hVU Fm hFm hFmid A hAV hAc t ht
  -- S-cont-law on the countable subsets
  have hwe₂ := ae_ae_weylAt hD (measurable_toSig hle) hX.1 hX.2.1 hG₂m (by
    have e : (fun ω => G (toSig (recSigma h ρ w (confU r p.δ z T)ᶜ) ω).val + X ω) =
        recField h ρ w := funext fun ω => by simp only [toSig, hXG ω, add_sub_cancel]
    rw [e]; exact isWholePlaneGFF_recField hh ρ w)
  have hS' := hS P h hh z r hr T hT ρ w hρ hUw X G hX hGm hXG hZB
  have hneF : ∀ᵐ v ∂(P.map (toSig (recSigma h ρ w (confU r p.δ z T)ᶜ))), ∀ᵐ x ∂(P.map X),
      ∀ k ∈ confSqIdx (p.δ * r) z (annulus z (3 * r) (4 * r)),
        internalDiam (D (G v.val + x)) (A₀ k) (annulus z (2 * r) (5 * r)) ≠
          euThr (xiGamma γ) c p h ρ w r z v.val := by
    have hS'' : ∀ᵐ v ∂(P.map (toSig (recSigma h ρ w (confU r p.δ z T)ᶜ))), ∀ᵐ x ∂(P.map X),
        ∀ k ∈ confSqIdx (p.δ * r) z (annulus z (3 * r) (4 * r)),
          internalDiam (D (G v.val + x)) (confSq (p.δ * r) z k) (annulus z (2 * r) (5 * r)) ≠
            euThr (xiGamma γ) c p h ρ w r z v.val := by
      filter_upwards [(eventually_all_finite hSfin).2 hS'] with v hv
      exact (eventually_all_finite hSfin).2 hv
    filter_upwards [hS'', hwe₂] with v h1 h2
    filter_upwards [h1, h2] with x hx1 hx2 k hk
    rw [← hA₀ k _ (isLength_of_weylAt0 hx2)]; exact hx1 k hk
  exact zbDiamSet_fkg_frozen_at (hL r p.δ z T) hγ hD hh hUb hX hGm hXG hZB V hVU Fm hFm hFmid A hAV hAc ht
    hFz hSfin (fun k _ => hA₀c k) hannO (fun _ => isBounded_annulus_m6 z _ _)
    (fun _ _ => hTm) hneF

/-- copy of `confFKGFrozenEUc_of_outside` (S3D108M8) with `CONFLem2_10AtConfU` -/
theorem confFKGFrozenEUc_of_outside_at (hL : CONFLem2_10AtConfU) {γ : ℝ} (hγ : 0 < γ)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) {p : CONFParams}
    (hδ : 0 < p.δ) (hpc : 0 < p.c) (hO : CONFEUOutside13 γ D c p) :
    CONFFKGFrozenEUc γ D c p :=
  confFKGFrozenEUc_of_at hL hγ hD hδ hO (confEUSContLaw_of hγ hD hpc)

/-- **`CONFFKGFrozenEUc` from CONF L2.10 at `confU` and the link of the harmonic parts** (copy of
`confFKGFrozenEUc_of_link'`, S3D108M10, through `confFKGFrozenEUc_of_link`, M9) -/
theorem confFKGFrozenEUc_of_link_at (hL : CONFLem2_10AtConfU) {γ : ℝ} (hγ : 0 < γ)
    {D : DistC → ContMetric} {c : ℝ → ℝ} (hD : IsWeakLQGMetric γ D c) {p : CONFParams}
    (hδ : 0 < p.δ) (hpc : 0 < p.c) (HL : CONFHarmPartLink) : CONFFKGFrozenEUc γ D c p :=
  confFKGFrozenEUc_of_outside_at hL hγ hD hδ hpc (confEUOutside13_of hδ HL (confEUOutside1_of hD))

end LQGMetric.CONF
