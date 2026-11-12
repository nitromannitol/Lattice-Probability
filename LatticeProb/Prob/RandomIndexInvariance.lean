import Mathlib
import LatticeProb.Prob.AeLimitLaw

/-!
# Random indices independent of the process, and almost sure limits with an extra coordinate

Two elementary facts about laws, used to replace a deterministic index of an invariance by a random one.

* `LatticeProb.map_pair_randomIndex_of_indepFun`: let `X ⟂ Y`, let `k` be a measurable map of the value of `X`
  into a countable index set `ι`, and let `T i` be measurable maps with `(T i)_* law(Y) = ν` for all `i`.
  Then `(X, T_{k(X)} Y)` has the law `law(X) ⊗ ν`: the random index may depend on `X`, the invariance under every
  fixed index survives, and the transformed sample is independent of `X`.
* `LatticeProb.map_pair_eq_of_tendsto_ae`: if `V n → Vlim` almost surely in a pseudometric space and all the pairs
  `(X, V n)` have the same law `μ`, then `(X, Vlim)` has the law `μ`. The first coordinate is only a measurable
  space; this is the form of `map_eq_of_tendsto_ae` needed when the limit is taken jointly with an auxiliary
  random element.

Together they give the invariance for a random index with values in a continuum by dyadic discretisation of the
index: apply the first fact to the discretisations and pass to the limit with the second.
-/

noncomputable section

namespace LatticeProb

open MeasureTheory ProbabilityTheory Filter Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- **A random index (a measurable function of `X`, with countably many values) does not destroy the invariance
of `Y`.** -/
theorem map_pair_randomIndex_of_indepFun {α β γ ι : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] [MeasurableSpace ι] [MeasurableSingletonClass ι] [Countable ι]
    [IsProbabilityMeasure P] {X : Ω → α} {Y : Ω → β} (hX : AEMeasurable X P) (hY : AEMeasurable Y P)
    (hind : IndepFun X Y P) {k : α → ι} (hk : Measurable k) {T : ι → β → γ} (hT : ∀ i, Measurable (T i))
    {ν : Measure γ} [SFinite ν] (hinv : ∀ i, (P.map Y).map (T i) = ν) :
    P.map (fun ω => (X ω, T (k (X ω)) (Y ω))) = (P.map X).prod ν := by
  have hT2 : Measurable (fun q : ι × β => T q.1 q.2) :=
    measurable_from_prod_countable_right (fun i => hT i)
  have hΦ : Measurable (fun p : α × β => (p.1, T (k p.1) p.2)) :=
    measurable_fst.prodMk (hT2.comp ((hk.comp measurable_fst).prodMk measurable_snd))
  have hpair : P.map (fun ω => (X ω, Y ω)) = (P.map X).prod (P.map Y) :=
    (indepFun_iff_map_prod_eq_prod_map_map hX hY).1 hind
  have hcomp : (fun ω => (X ω, T (k (X ω)) (Y ω))) =
      (fun p : α × β => (p.1, T (k p.1) p.2)) ∘ (fun ω => (X ω, Y ω)) := rfl
  rw [hcomp, ← AEMeasurable.map_map_of_aemeasurable hΦ.aemeasurable (hX.prodMk hY), hpair]
  refine Measure.ext fun A hA => ?_
  rw [Measure.map_apply hΦ hA, Measure.prod_apply (hΦ hA), Measure.prod_apply hA]
  refine lintegral_congr fun x => ?_
  have hAx : MeasurableSet (Prod.mk x ⁻¹' A) := measurable_prodMk_left hA
  rw [← hinv (k x), Measure.map_apply (hT _) hAx]
  rfl

/-- **An almost sure limit of random elements whose pairs with `X` have a common law has that law, jointly with
`X`.** -/
theorem map_pair_eq_of_tendsto_ae {α E : Type*} [MeasurableSpace α] [PseudoMetricSpace E]
    [MeasurableSpace E] [BorelSpace E] [IsProbabilityMeasure P] {X : Ω → α} (hX : Measurable X)
    {V : ℕ → Ω → E} {Vlim : Ω → E} {μ : Measure (α × E)} (hVm : ∀ n, AEMeasurable (V n) P)
    (hV : ∀ n, P.map (fun ω => (X ω, V n ω)) = μ)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => V n ω) atTop (𝓝 (Vlim ω))) :
    P.map (fun ω => (X ω, Vlim ω)) = μ := by
  have hVlim : AEMeasurable Vlim P := aemeasurable_of_tendsto_metrizable_ae atTop hVm hlim
  have : IsFiniteMeasure μ := by
    rw [← hV 0]
    infer_instance
  have hrect : ∀ (A : Set α) (B : Set E), MeasurableSet A → MeasurableSet B →
      P.map (fun ω => (X ω, Vlim ω)) (A ×ˢ B) = μ (A ×ˢ B) := by
    intro A B hA hB
    have hAB : ∀ W : Ω → E, AEMeasurable W P →
        P.map (fun ω => (X ω, W ω)) (A ×ˢ B) = P (X ⁻¹' A ∩ W ⁻¹' B) := by
      intro W hW
      rw [Measure.map_apply_of_aemeasurable (hX.aemeasurable.prodMk hW) (hA.prod hB)]
      rfl
    rw [hAB _ hVlim, ← hV 0, hAB _ (hVm 0)]
    by_cases hz : P (X ⁻¹' A) = 0
    · have h1 : P (X ⁻¹' A ∩ Vlim ⁻¹' B) = 0 := measure_mono_null Set.inter_subset_left hz
      have h2 : P (X ⁻¹' A ∩ V 0 ⁻¹' B) = 0 := measure_mono_null Set.inter_subset_left hz
      rw [h1, h2]
    · have hfin : P (X ⁻¹' A) ≠ ⊤ := measure_ne_top _ _
      have : IsProbabilityMeasure (ProbabilityTheory.cond P (X ⁻¹' A)) :=
        ProbabilityTheory.cond_isProbabilityMeasure hz
      have hs : MeasurableSet (X ⁻¹' A) := hX hA
      set P' := ProbabilityTheory.cond P (X ⁻¹' A) with hP'
      have hac : P' ≪ P := ProbabilityTheory.cond_absolutelyContinuous
      have hVm' : ∀ n, AEMeasurable (V n) P' := fun n => (hVm n).mono_ac hac
      have hval : ∀ (n : ℕ) (hn : P.map (fun ω => (X ω, V n ω)) = μ), P'.map (V n) B =
          (P (X ⁻¹' A))⁻¹ * μ (A ×ˢ B) := by
        intro n hn
        rw [Measure.map_apply_of_aemeasurable (hVm' n) hB, hP', ProbabilityTheory.cond_apply hs]
        congr 1
        rw [← hn, hAB _ (hVm n)]
      have hcommon : ∀ n, P'.map (V n) = P'.map (V 0) := by
        intro n
        refine Measure.ext fun C hC => ?_
        have hn := hV n
        have h0 := hV 0
        rw [Measure.map_apply_of_aemeasurable (hVm' n) hC, Measure.map_apply_of_aemeasurable (hVm' 0) hC,
          hP', ProbabilityTheory.cond_apply hs, ProbabilityTheory.cond_apply hs]
        congr 1
        have e1 : P (X ⁻¹' A ∩ V n ⁻¹' C) = P.map (fun ω => (X ω, V n ω)) (A ×ˢ C) := by
          rw [Measure.map_apply_of_aemeasurable (hX.aemeasurable.prodMk (hVm n)) (hA.prod hC)]; rfl
        have e0 : P (X ⁻¹' A ∩ V 0 ⁻¹' C) = P.map (fun ω => (X ω, V 0 ω)) (A ×ˢ C) := by
          rw [Measure.map_apply_of_aemeasurable (hX.aemeasurable.prodMk (hVm 0)) (hA.prod hC)]; rfl
        rw [e1, e0, hn, h0]
      have hlim' : ∀ᵐ ω ∂P', Tendsto (fun n => V n ω) atTop (𝓝 (Vlim ω)) := hac.ae_le hlim
      have hmap := map_eq_of_tendsto_ae hVm' (fun n => hcommon n) hlim'
      have h1 : P'.map Vlim B = (P (X ⁻¹' A))⁻¹ * P (X ⁻¹' A ∩ Vlim ⁻¹' B) := by
        rw [Measure.map_apply_of_aemeasurable (hVlim.mono_ac hac) hB, hP', ProbabilityTheory.cond_apply hs]
      have h2 := hval 0 (hV 0)
      rw [hmap, h2] at h1
      have hne0 : (P (X ⁻¹' A))⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hfin
      have hnetop : (P (X ⁻¹' A))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hz
      have e0 : μ (A ×ˢ B) = P (X ⁻¹' A ∩ V 0 ⁻¹' B) := by rw [← hV 0, hAB _ (hVm 0)]
      exact ((ENNReal.mul_right_inj hne0 hnetop).1 h1).symm.trans e0
  refine ext_of_generate_finite _ generateFrom_prod.symm isPiSystem_prod ?_ ?_
  · rintro _ ⟨A, hA, B, hB, rfl⟩
    exact hrect A B hA hB
  · have := hrect Set.univ Set.univ MeasurableSet.univ MeasurableSet.univ
    simpa using this

end LatticeProb
