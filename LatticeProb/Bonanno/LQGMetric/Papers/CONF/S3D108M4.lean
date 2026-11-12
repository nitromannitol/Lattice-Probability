/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D108M4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D108M3
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D112L3

/-!
# CONF Lemma 3.3, Step 3: the zero-boundary diameter event `G^U` as a frozen chain event

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`, Lemma 3.3, Step 3 (C:1236–1243), bridging step
(a) of `handoff/P2-CONFFKG.md` §"For the consumer" and `handoff/P2-CONF33G.md` §"How to discharge 4".

Setting of `CONFFKGFrozenEU` (S3D112L3): `X = (h − h_ρ(w)) − G` with `G` outside-measurable
(`𝒢 = recSigma h ρ w Uᶜ`), `IsZBExtField U X`, the frozen datum `v = toSig 𝒢 ω`. The event
`G^U = zbDiamSet V Fm A t` is defined through the zero-boundary metrics `Fm i` of CONF Remark 1.2.
With the cut-off `φ𝔥 = harmFn φ δ' (G ω)` of the harmonic part (`exists_cutoff33G`) and the
frozen field `G₁ v = G v − φ𝔥(v)`, the hypothesis on `Fm` says that a.s.
`Fm i (X|_{V i}) = D_{G₁ v + X}(·,·; V i)` on `V i`. For countable `A i` this is a measurable
condition on `(v, X)` once `internal` is replaced by `chainInf` (`D_{G₁ v + X}` is a length metric
by Axiom III), so it transfers to the product law `law(v) ⊗ law(X)` (independence), and
`zbDiamSet` agrees a.e. with the sections of the measurable event
`frozenChainEv D G₁ ⊤ univ A V t`.

* `exists_testC_bump`: a test function `= 1` on `V`, supported in `U` (`closure V ⊆ U` compact);
* **`ae_ae_zbDiamSet_eq`**: the a.e. equality of the sections;
* **`zbDiamSet_fkg_frozen`**: the FKG part of `CONFFKGFrozenEU` for countable `A i`, with the
  `E^U`-side event any measurable chain event on the frozen field `G v + x = recField`.

What is left for `CONFFKGFrozenEU`: writing `E^U` as such a chain event (conditions 1 and 3 as
`𝒢`-measurable events, condition 2's squares by countable dense subsets) and the countability of
`A i` (see `handoff/P2-CONFFKGB.md`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology TopologicalSpace
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

/-- a test function `= 1` on `V` and supported in the open `U ⊇ closure V`, `V` bounded
(mathlib's smooth Urysohn lemma, as `GM.l510_exists_bump`) -/
lemma exists_testC_bump {U V : Set ℂ} (hU : IsOpen U) (hVb : Bornology.IsBounded V)
    (hVU : closure V ⊆ U) : ∃ F : TestC, (∀ x ∈ V, F x = 1) ∧ tsupport (F : ℂ → ℝ) ⊆ U := by
  obtain ⟨d, hd, hdU⟩ := hVb.isCompact_closure.exists_cthickening_subset_open hU hVU
  have hs : IsClosed (thickening (d / 2) V)ᶜ := isOpen_thickening.isClosed_compl
  have hdisj : Disjoint (thickening (d / 2) V)ᶜ (closure V) :=
    Set.disjoint_left.2 fun x hx hx' => hx (closure_subset_thickening (by linarith) V hx')
  obtain ⟨f, hf, -, h0, h1⟩ := exists_contDiff_zero_iff_one_iff_of_isClosed
    (n := (⊤ : ℕ∞)) hs isClosed_closure hdisj
  have hsupp : Function.support f ⊆ thickening (d / 2) V := fun x hx => by
    by_contra h; exact hx ((h0 x).1 h)
  have hts : tsupport f ⊆ U := by
    refine (closure_mono hsupp).trans ((closure_thickening_subset_cthickening _ _).trans ?_)
    exact (cthickening_mono (by linarith) V).trans
      ((cthickening_subset_of_subset d subset_closure).trans hdU)
  have hcs : HasCompactSupport f :=
    IsCompact.of_isClosed_subset (hVb.thickening.isCompact_closure) isClosed_closure
      (closure_mono hsupp)
  exact ⟨⟨f, hf, hcs, subset_univ _⟩, fun z hz => (h1 z).1 (subset_closure hz), hts⟩

section Bridge

variable {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **`G^U` is a.e. a frozen chain event** (bridging step (a)): for countable `A i`, the event
`zbDiamSet V Fm A t` agrees `law(X)`-a.e., for a.e. frozen datum `v`, with the section of
`frozenChainEv D G₁ ⊤ univ A V t`, `G₁ v = G v − φ𝔥(G v)`. -/
theorem ae_ae_zbDiamSet_eq {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {ρ : ℝ} {w : ℂ}
    {U : Set ℂ} (hU : IsOpen U) {X G : Ω → DistC} (hX : IsL33ZBPart P h ρ w U hU X)
    (hGm : Measurable[recSigma h ρ w Uᶜ] G) (hXG : ∀ ω, X ω = recField h ρ w ω - G ω)
    {ι : Type} [Finite ι] (V : ι → Opens ℂ) (Fm : ∀ i, DistOn (V i) → ℂ → ℂ → ℝ≥0∞)
    (hFm : ∀ i, Measurable (Fm i))
    (hFmid : ∀ i, ∀ᵐ ω ∂P, ∀ 𝔥 : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd 𝔥 U →
      (∀ φ : TestOn (toOpens U hU),
        restrictTo (toOpens U hU) (recField h ρ w ω - X ω) φ = ∫ x, 𝔥 x * φ x) →
      ∀ f : C(ℂ, ℝ), tsupport ⇑f ⊆ U → EqOn ⇑f 𝔥 (V i : Set ℂ) →
      ∀ u ∈ V i, ∀ v ∈ V i,
        (D (addFun (recField h ρ w ω) (-f))).internal (V i) u v =
          Fm i (restrictTo (V i) (X ω)) u v)
    (A : ι → Set ℂ) (hAV : ∀ i, A i ⊆ V i) (hAc : ∀ i, (A i).Countable) (t : ℝ)
    {φ : C(ℂ, ℝ)} {δ' : ℝ} {hδ' : 0 < δ'}
    (hcut : ∀ (T : DistC) (𝔥 : ℂ → ℝ), InnerProductSpace.HarmonicOnNhd 𝔥 U →
      (∀ ψ : TestOn (toOpens U hU), restrictTo (toOpens U hU) T ψ = ∫ y, 𝔥 y * ψ y) →
      tsupport ⇑(DFGPS.L217.harmFn φ δ' hδ' T) ⊆ U ∧
        ∀ i, EqOn ⇑(DFGPS.L217.harmFn φ δ' hδ' T) 𝔥 (V i : Set ℂ)) :
    ∀ᵐ v ∂(P.map (toSig (recSigma h ρ w Uᶜ))),
      Prod.mk v ⁻¹' (Prod.snd ⁻¹' zbDiamSet V Fm A t) =ᵐ[P.map X]
        Prod.mk v ⁻¹' frozenChainEv D
          (fun v : SigOmega Ω (recSigma h ρ w Uᶜ) =>
            addFun (G v.val) (-DFGPS.L217.harmFn φ δ' hδ' (G v.val)))
          (fun _ => True) univ A (fun i => (V i : Set ℂ)) (fun _ _ => ENNReal.ofReal t) := by
  have hle : (recSigma h ρ w Uᶜ) ≤ mΩ := recSigma_le hh ρ w Uᶜ
  obtain ⟨hXm, hind, hh₀, hz, hdec, hXz, hhg, -, -⟩ := hX
  have hWm : Measurable (toSig (recSigma h ρ w Uᶜ)) := measurable_toSig hle
  have hval : @Measurable (SigOmega Ω (recSigma h ρ w Uᶜ)) Ω _ (recSigma h ρ w Uᶜ) SigOmega.val := comap_measurable _
  set G₁ : SigOmega Ω (recSigma h ρ w Uᶜ) → DistC := fun v =>
    addFun (G v.val) (-DFGPS.L217.harmFn φ δ' hδ' (G v.val)) with hG₁
  have hG₁m : Measurable G₁ := by
    have hg : Measurable fun v : SigOmega Ω (recSigma h ρ w Uᶜ) => G v.val := hGm.comp hval
    exact measurable_addFun.comp (hg.prodMk
      (continuous_neg.measurable.comp ((DFGPS.L217.measurable_harmFn φ δ' hδ').comp hg)))
  have hDG : Measurable fun p : SigOmega Ω (recSigma h ρ w Uᶜ) × DistC => D (G₁ p.1 + p.2) :=
    hD.measurable.comp (measurable_add_frozen hG₁m)
  -- the measurable identification event
  set Qs : Set (SigOmega Ω (recSigma h ρ w Uᶜ) × DistC) := {p | ∀ i, ∀ u ∈ A i, ∀ u' ∈ A i,
    Fm i (restrictTo (V i) p.2) u u' = (D (G₁ p.1 + p.2)).chainInf (V i) u u'} with hQs
  have hQm : MeasurableSet Qs := by
    have e : Qs = ⋂ i, ⋂ u ∈ A i, ⋂ u' ∈ A i, {p : SigOmega Ω (recSigma h ρ w Uᶜ) × DistC |
        Fm i (restrictTo (V i) p.2) u u' = (D (G₁ p.1 + p.2)).chainInf (V i) u u'} := by
      ext p; simp [hQs]
    rw [e]
    refine MeasurableSet.iInter fun i => MeasurableSet.biInter (hAc i) fun u _ =>
      MeasurableSet.biInter (hAc i) fun u' _ => measurableSet_eq_fun ?_ ?_
    · exact (measurable_pi_apply u').comp ((measurable_pi_apply u).comp
        ((hFm i).comp ((measurable_restrictTo _).comp measurable_snd)))
    · exact (ContMetric.measurable_chainInf (V i)).comp
        (hDG.prodMk (measurable_const (a := ((u, u') : ℂ × ℂ))))
  -- `Qs` at the sample
  have hrec := isWholePlaneGFF_recField hh ρ w
  have hwe : ∀ᵐ ω ∂P, WeylAt (xiGamma γ) D (recField h ρ w ω) :=
    hD.weyl P _ (GM.isGFFPlusCont_of_isWholePlaneGFF hrec)
  have hQω : ∀ᵐ ω ∂P, (toSig (recSigma h ρ w Uᶜ) ω, X ω) ∈ Qs := by
    filter_upwards [ae_all_iff.2 hFmid, hwe, hhg, hXz] with ω hFω hwω hg hXω
    obtain ⟨g, hgH, hgT⟩ := hg
    have eG : recField h ρ w ω - X ω = G ω := by rw [hXG ω, sub_sub_cancel]
    have hpair : ∀ ψ : TestOn (toOpens U hU),
        restrictTo (toOpens U hU) (recField h ρ w ω - X ω) ψ = ∫ x, g x * ψ x := by
      have e : recField h ρ w ω - X ω = hh₀ ω := by rw [hdec ω, hXω, add_sub_cancel_right]
      rw [e]; exact hgT
    have hpairG : ∀ ψ : TestOn (toOpens U hU),
        restrictTo (toOpens U hU) (G ω) ψ = ∫ y, g y * ψ y := by rw [← eG]; exact hpair
    obtain ⟨hts, heq⟩ := hcut (G ω) g hgH hpairG
    set f := DFGPS.L217.harmFn φ δ' hδ' (G ω)
    have eF : G₁ (toSig (recSigma h ρ w Uᶜ) ω) + X ω = addFun (recField h ρ w ω) (-f) := by
      simp only [hG₁, toSig, addFun, hXG ω]; abel
    intro i u hu u' hu'
    rw [← hFω i g hgH hpair f hts (heq i) u (hAV i hu) u' (hAV i hu'), eF,
      (D _).internal_eq_chainInf (isLength_of_weylAt hwω _) (V i).isOpen]
  have hmap : P.map (fun ω => (toSig (recSigma h ρ w Uᶜ) ω, X ω)) = (P.map (toSig (recSigma h ρ w Uᶜ))).prod (P.map X) :=
    (indepFun_iff_map_prod_eq_prod_map_map hWm.aemeasurable hXm.aemeasurable).1 hind
  have hQp : ∀ᵐ p ∂((P.map (toSig (recSigma h ρ w Uᶜ))).prod (P.map X)), p ∈ Qs := by
    rw [← hmap]
    exact (ae_map_iff (hWm.prodMk hXm).aemeasurable hQm).2 hQω
  filter_upwards [Measure.ae_ae_of_ae_prod hQp] with v hv
  refine eventuallyEqSet_iff.2 ?_
  filter_upwards [hv] with x hx
  simp only [mem_preimage, zbDiamSet, frozenChainEv, mem_ofPred_eq, mem_univ, true_and,
    forall_const, chainDiam, iSup_le_iff]
  refine forall_congr' fun i => forall₂_congr fun u hu => forall₂_congr fun u' hu' => ?_
  rw [hx i u hu u' hu']

end Bridge

end LQGMetric.CONF
