/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_17Core3G at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17Core3F
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17Step4

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.17, core case: one stage of Step 4 on the law of `(h, D_h)` (R3)

Source: DFGPS = arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Lemma 2.17,
Step 3–4 (T:1260–1278) with decision D80 (`h|_{cl V}` on the left of (eqn-limit-metric-ind)).

* `condIndepEv_comap_of_map` — conditional independence on the law pulls back to the sample
  space (converse of `condIndepEv_map`);
* `condIndepEv_stage` — for one stage (finite families `𝒲, 𝒲'` of dyadic domains), in the limit
  coupling `ρ` of `indep_stage_limit`: (eqn-limit-metric-ind) with `D₁(·,·;W)` on the left
  (`indep_stage_intFn`) and the Weyl/"measurable function" step of T:1270–1273
  (`comap_intFn_le_aeClosure_coupling`) give, on the law of `(x, D₁)`,
  `⋁_{W ∈ 𝒲} D₁(·,·;W) ⟂ σ(ℋ) ∨ ⋁_{W' ∈ 𝒲'} D₁(·,·;W') | σ(𝒢)` (with `Fb` `𝒢`-measurable).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace
open scoped ENNReal BoundedContinuousFunction

namespace LQGMetric.DFGPS.L217

open Blueprint GM.Bilip

/-- conditional independence on the law pulls back along the random element -/
theorem condIndepEv_comap_of_map {Ω T : Type*} {G A B : MeasurableSpace T}
    [mΩ : MeasurableSpace Ω] [mT : MeasurableSpace T] {P : Measure Ω} [IsProbabilityMeasure P]
    {Ψ : Ω → T} (hΨ : Measurable Ψ) (hG : G ≤ mT) (hA : A ≤ mT) (hB : B ≤ mT)
    (h : CondIndepEv G A B (P.map Ψ)) :
    CondIndepEv (G.comap Ψ) (A.comap Ψ) (B.comap Ψ) P := by
  have : IsProbabilityMeasure (P.map Ψ) :=
    (Measure.isProbabilityMeasure_map_iff hΨ.aemeasurable).2 inferInstance
  rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
  have ha' := hA a ha
  have hb' := hB b hb
  have ind : ∀ s : Set T, (s.indicator fun _ => (1 : ℝ)) ∘ Ψ =
      (Ψ ⁻¹' s).indicator fun _ => (1 : ℝ) := fun s => by
    funext x; simp only [Function.comp, Set.indicator, Set.mem_preimage]; rfl
  have e : ∀ s : Set T, MeasurableSet s → P⟦Ψ ⁻¹' s | G.comap Ψ⟧ =ᵐ[P]
      (P.map Ψ)⟦s | G⟧ ∘ Ψ := fun s hs => by
    rw [← ind s]
    exact condExp_comp_map hΨ hG (integrable_indOne hs)
  have H := ae_of_ae_map hΨ.aemeasurable (h a b ha hb)
  filter_upwards [H, e _ (ha'.inter hb'), e _ ha', e _ hb'] with x hx e1 e2 e3
  simp only [Function.comp, Pi.mul_apply, Set.preimage_inter] at hx e1 e2 e3 ⊢
  rw [e1, e2, e3, hx]

/-- **One stage of Step 4 on the law of `(x, D₁)`** (T:1260–1278, D80) -/
theorem condIndepEv_stage (h28 : Lem2_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {S : Type} [TopologicalSpace S] [mS : MeasurableSpace S] [BorelSpace S] [PolishSpace S]
    {μ : Measure S} [IsProbabilityMeasure μ] {N : S → DistC} (hN : IsGFFPlusBddCont N μ)
    {Fb : S → C(ℂ, ℝ)} (hFb : Measurable Fb) {K : Set ℂ} (hK : IsCompact K)
    (hFK : ∀ x, ∀ z ∉ K, Fb x z = 0)
    (hN₂ : IsGFFPlusBddCont (fun x => N x - ofCont (Fb x)) μ)
    {εs : ℕ → ℝ} (hεs : ∀ n, 0 < εs n) (hεs0 : Tendsto εs atTop (𝓝 0))
    {ρ : ProbabilityMeasure (S × (DyProd × DyProd))}
    (hconv : ∀ f : S × (DyProd × DyProd) →ᵇ ℝ, Tendsto (fun n => ∫ x, f (x,
        (lfppJoint (xiGamma γ) (εs n) (N x), lfppJoint (xiGamma γ) (εs n) (N x - ofCont (Fb x))))
          ∂μ) atTop (𝓝 (∫ p, f p ∂(ρ : Measure (S × (DyProd × DyProd))))))
    (hmarg : (ρ : Measure (S × (DyProd × DyProd))).map Prod.fst = μ)
    (hdy : ∀ᵐ p ∂(ρ : Measure (S × (DyProd × DyProd))), IsDyadicLimit p.2.1)
    (𝒲 𝒲' : Finset dyadicDomainsC) (𝒢 ℋ : {m : MeasurableSpace S // m ≤ mS})
    (hFb𝒢 : Measurable[𝒢.1] Fb)
    (hind : Indep (𝒢.1.comap Prod.fst ⊔ MeasurableSpace.comap
          (fun p : S × (DyProd × DyProd) => famProj 𝒲 p.2.1.2) inferInstance)
        (ℋ.1.comap Prod.fst ⊔ MeasurableSpace.comap
          (fun p : S × (DyProd × DyProd) => famProj 𝒲' p.2.2.2) inferInstance)
        (ρ : Measure (S × (DyProd × DyProd)))) :
    CondIndepEv (𝒢.1.comap Prod.fst)
      (⨆ W ∈ 𝒲, MeasurableSpace.comap (fun q : S × C(ℂ × ℂ, ℝ) => intFn W q.2) inferInstance)
      (ℋ.1.comap Prod.fst ⊔
        ⨆ W ∈ 𝒲', MeasurableSpace.comap (fun q : S × C(ℂ × ℂ, ℝ) => intFn W q.2) inferInstance)
      ((ρ : Measure (S × (DyProd × DyProd))).map fun p => (p.1, p.2.1.1)) := by
  set ρm := (ρ : Measure (S × (DyProd × DyProd)))
  set π : S × (DyProd × DyProd) → S × C(ℂ × ℂ, ℝ) := fun p => (p.1, p.2.1.1)
  have hπ : Measurable π := measurable_fst.prodMk
    (continuous_dyProd_fst.measurable.comp (measurable_fst.comp measurable_snd))
  have H1 := indep_stage_intFn hdy 𝒲 𝒲' 𝒢 ℋ hind
  have hGm : 𝒢.1.comap (Prod.fst : S × (DyProd × DyProd) → S) ≤
      (inferInstance : MeasurableSpace (S × (DyProd × DyProd))) :=
    (MeasurableSpace.comap_mono 𝒢.2).trans measurable_fst.comap_le
  have hHm : ℋ.1.comap (Prod.fst : S × (DyProd × DyProd) → S) ⊔ MeasurableSpace.comap
      (fun p : S × (DyProd × DyProd) => famProj 𝒲' p.2.2.2) inferInstance ≤
      (inferInstance : MeasurableSpace (S × (DyProd × DyProd))) :=
    sup_le ((MeasurableSpace.comap_mono ℋ.2).trans measurable_fst.comap_le)
      (show Measurable (fun p : S × (DyProd × DyProd) => famProj 𝒲' p.2.2.2) from
        ((measurable_pi_iff.2 fun W => (continuous_dyProd_snd W).measurable :
          Measurable fun x : DyProd => famProj 𝒲' x.2).comp
            (measurable_snd.comp measurable_snd))).comap_le
  have hint : ∀ W, MeasurableSpace.comap (fun p : S × (DyProd × DyProd) => intFn W p.2.1.1)
      inferInstance ≤ (inferInstance : MeasurableSpace (S × (DyProd × DyProd))) := fun W =>
    ((measurable_intFn W).comp
      (continuous_dyProd_fst.measurable.comp (measurable_fst.comp measurable_snd))).comap_le
  have hAm : (⨆ W ∈ 𝒲, MeasurableSpace.comap
      (fun p : S × (DyProd × DyProd) => intFn W p.2.1.1) inferInstance) ≤
      (inferInstance : MeasurableSpace (S × (DyProd × DyProd))) := iSup₂_le fun W _ => hint W
  -- the `h̊` side: `D₁(·,·;W')` is a.s. a function of `Fb` and `d₂_{W'}`
  have hB : ℋ.1.comap (Prod.fst : S × (DyProd × DyProd) → S) ⊔ ⨆ W ∈ 𝒲', MeasurableSpace.comap
      (fun p : S × (DyProd × DyProd) => intFn W p.2.1.1) inferInstance ≤
      aeClosure ρm ((ℋ.1.comap (Prod.fst : S × (DyProd × DyProd) → S) ⊔ MeasurableSpace.comap
        (fun p : S × (DyProd × DyProd) => famProj 𝒲' p.2.2.2) inferInstance) ⊔
        𝒢.1.comap (Prod.fst : S × (DyProd × DyProd) → S)) := by
    refine sup_le ((le_sup_left.trans le_sup_left).trans (le_aeClosure _))
      (iSup₂_le fun W hW => ?_)
    refine (comap_intFn_le_aeClosure_coupling h28 hγ hγ2 hN hFb hK hFK hN₂ hεs hεs0 hconv
      hmarg W).trans (aeClosure_mono ?_)
    refine (MeasurableSpace.comap_prodMk (fun p : S × (DyProd × DyProd) => Fb p.1)
      (fun p : S × (DyProd × DyProd) => p.2.2.2 W)).le.trans (sup_le ?_ ?_)
    · refine le_sup_of_le_right ?_
      rw [show (fun p : S × (DyProd × DyProd) => Fb p.1) = Fb ∘ Prod.fst from rfl,
        ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono hFb𝒢.comap_le
    · refine le_sup_of_le_left (le_sup_of_le_right ?_)
      have e : (fun p : S × (DyProd × DyProd) => p.2.2.2 W) =
          (fun f : FamT 𝒲' => f ⟨W, hW⟩) ∘ fun p : S × (DyProd × DyProd) => famProj 𝒲' p.2.2.2 :=
        rfl
      rw [e, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono (measurable_iff_comap_le.1 (measurable_pi_apply _))
  have H2 := condIndepEv_of_indep_of_le hGm hAm hHm (by rw [sup_comm]; exact H1)
    (le_sup_left.trans (le_aeClosure _)) hB
  -- push to the law of `π`
  refine condIndepEv_map hπ ((MeasurableSpace.comap_mono 𝒢.2).trans measurable_fst.comap_le)
    (iSup₂_le fun W _ => ((measurable_intFn W).comp measurable_snd).comap_le)
    (sup_le ((MeasurableSpace.comap_mono ℋ.2).trans measurable_fst.comap_le)
      (iSup₂_le fun W _ => ((measurable_intFn W).comp measurable_snd).comap_le)) ?_
  simp only [MeasurableSpace.comap_iSup, MeasurableSpace.comap_sup, MeasurableSpace.comap_comp]
  exact H2

end L217

end LQGMetric.DFGPS
