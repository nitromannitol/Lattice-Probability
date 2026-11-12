/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.T1_7V8 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7E3

/-!
# LM Theorem 1.7, packet P-VAR (d): slices of the conditional law given `(θ, Y_θ)`

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), proof of Theorem 1.7 (l. 1011–1026) conditions on `(h, θ)` and on the
square metrics `Y_θ = {D(·,·;S) : S ∈ 𝒮^ε_θ}`, with `θ` independent of `(h, D)`. In the kernel
form (per field `g`, `ν = κ_g`) one needs a conditional law of `D` given `Y_θ` that is *jointly*
measurable in `θ` (for Tonelli over `θ`, D107 §1.3). `t17v_slice`: if `K` is a conditional law of
`D` given `(θ, Y(θ, D))` under `Λ ⊗ ν`, then for `Λ`-a.e. `θ` its slice `K(θ, ·)` is a conditional
law of `D` given `Y(θ, D)` under `ν` (disintegration identity), hence equal to
`condDistrib id Y_θ ν` a.e. (`condDistrib_ae_eq_of_measure_eq_compProd`).

Own standard argument (no source needed): both sides are finite measures agreeing on a countable
π-system of rectangles, and each rectangle identity holds for a.e. `θ` because its integrals over
every measurable `A ⊆ Θ` agree by the global identity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric.LM

variable {Θ β γ : Type*} [MeasurableSpace Θ] [MeasurableSpace β] [MeasurableSpace γ]

/-- one rectangle -/
lemma t17v_slice_rect (Λ : Measure Θ) [IsProbabilityMeasure Λ] (ν : Measure β)
    [IsProbabilityMeasure ν] {Y : Θ × β → γ} (hY : Measurable Y) (K : Kernel (Θ × γ) β)
    [IsMarkovKernel K]
    (hK : (Λ.prod ν).map (fun p => ((p.1, Y p), p.2)) = ((Λ.prod ν).map fun p => (p.1, Y p)) ⊗ₘ K)
    {B : Set γ} (hB : MeasurableSet B) {C : Set β} (hC : MeasurableSet C) :
    ∀ᵐ θ ∂Λ, ν {d | Y (θ, d) ∈ B ∧ d ∈ C} =
      ∫⁻ d, {p : Θ × β | Y p ∈ B}.indicator (fun p => K (p.1, Y p) C) (θ, d) ∂ν := by
  have hS : MeasurableSet {p : Θ × β | Y p ∈ B ∧ p.2 ∈ C} := (hY hB).inter (measurable_snd hC)
  have hYB : MeasurableSet {p : Θ × β | Y p ∈ B} := hY hB
  have hKm : Measurable fun p : Θ × β => K (p.1, Y p) C :=
    (K.measurable_coe hC).comp (measurable_fst.prodMk hY)
  have hgm : Measurable fun p : Θ × β => {p : Θ × β | Y p ∈ B}.indicator
      (fun p => K (p.1, Y p) C) p := hKm.indicator hYB
  have hf : Measurable fun θ => ν {d | Y (θ, d) ∈ B ∧ d ∈ C} :=
    measurable_measure_prodMk_left hS
  have hg : Measurable fun θ => ∫⁻ d, {p : Θ × β | Y p ∈ B}.indicator
      (fun p => K (p.1, Y p) C) (θ, d) ∂ν := hgm.lintegral_prod_right'
  refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite hf hg fun A hA _ => ?_
  have hŶ : Measurable fun p : Θ × β => (p.1, Y p) := measurable_fst.prodMk hY
  have hm : Measurable fun p : Θ × β => ((p.1, Y p), p.2) := hŶ.prodMk measurable_snd
  have hABC : MeasurableSet ((A ×ˢ B) ×ˢ C) := (hA.prod hB).prod hC
  have h := congrArg (fun μ : Measure ((Θ × γ) × β) => μ ((A ×ˢ B) ×ˢ C)) hK
  rw [Measure.map_apply hm hABC, Measure.compProd_apply_prod (hA.prod hB) hC,
    Measure.prod_apply (hm hABC), ← lintegral_indicator (hA.prod hB),
    lintegral_map ((K.measurable_coe hC).indicator (hA.prod hB)) hŶ,
    lintegral_prod (fun a : Θ × β => (A ×ˢ B).indicator (fun q => K q C) (a.1, Y a))
      (((K.measurable_coe hC).indicator (hA.prod hB)).comp hŶ).aemeasurable] at h
  rw [← lintegral_indicator hA, ← lintegral_indicator hA]
  refine (lintegral_congr fun θ => ?_).trans (h.trans (lintegral_congr fun θ => ?_))
  · by_cases hθ : θ ∈ A
    · rw [indicator_of_mem hθ]
      congr 1
      ext d; simp [hθ]
    · rw [indicator_of_notMem hθ]
      symm
      convert measure_empty (μ := ν)
      ext d; simp [hθ]
  · by_cases hθ : θ ∈ A
    · rw [indicator_of_mem hθ]
      refine lintegral_congr fun d => ?_
      by_cases hd : Y (θ, d) ∈ B
      · simp [indicator, hθ, hd]
      · simp [indicator, hθ, hd]
    · rw [indicator_of_notMem hθ]
      refine lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall fun d => ?_)
      simp [indicator, hθ]

/-- **the slices of a joint conditional law are conditional laws** -/
theorem t17v_slice [MeasurableSpace.CountablyGenerated β] [MeasurableSpace.CountablyGenerated γ]
    (Λ : Measure Θ) [IsProbabilityMeasure Λ] (ν : Measure β) [IsProbabilityMeasure ν]
    {Y : Θ × β → γ} (hY : Measurable Y) (K : Kernel (Θ × γ) β) [IsMarkovKernel K]
    (hK : (Λ.prod ν).map (fun p => ((p.1, Y p), p.2)) = ((Λ.prod ν).map fun p => (p.1, Y p)) ⊗ₘ K) :
    ∀ᵐ θ ∂Λ, (ν.map fun d => Y (θ, d)) ⊗ₘ
        (K.comap (fun y => (θ, y)) (measurable_const.prodMk measurable_id)) =
      ν.map fun d => (Y (θ, d), d) := by
  set Cγ := t17eFinInter (MeasurableSpace.countableGeneratingSet γ)
  set Cβ := t17eFinInter (MeasurableSpace.countableGeneratingSet β)
  have hCγm : ∀ s ∈ Cγ, MeasurableSet s := fun s hs => measurableSet_of_mem_t17eFinInter
    (fun u hu => MeasurableSpace.measurableSet_countableGeneratingSet hu) hs
  have hCβm : ∀ s ∈ Cβ, MeasurableSet s := fun s hs => measurableSet_of_mem_t17eFinInter
    (fun u hu => MeasurableSpace.measurableSet_countableGeneratingSet hu) hs
  set C := image2 (· ×ˢ ·) Cγ Cβ with hCdef
  have hCc : C.Countable := (t17eFinInter_countable
    MeasurableSpace.countable_countableGeneratingSet).image2
    (t17eFinInter_countable MeasurableSpace.countable_countableGeneratingSet) _
  have hsγ : IsCountablySpanning Cγ := ⟨fun _ => univ, fun _ => univ_mem_t17eFinInter _, iUnion_const _⟩
  have hsβ : IsCountablySpanning Cβ := ⟨fun _ => univ, fun _ => univ_mem_t17eFinInter _, iUnion_const _⟩
  have hgen : (inferInstance : MeasurableSpace (γ × β)) = MeasurableSpace.generateFrom C :=
    (generateFrom_eq_prod (C := Cγ) (D := Cβ) generateFrom_t17eFinInter generateFrom_t17eFinInter
      hsγ hsβ).symm
  have hpi : IsPiSystem C := (t17eFinInter_isPiSystem _).prod (t17eFinInter_isPiSystem _)
  have hrect : ∀ S ∈ C, ∀ᵐ θ ∂Λ, ((ν.map fun d => Y (θ, d)) ⊗ₘ
      (K.comap (fun y => (θ, y)) (measurable_const.prodMk measurable_id))) S =
        (ν.map fun d => (Y (θ, d), d)) S := by
    rintro _ ⟨B, hB, C', hC', rfl⟩
    filter_upwards [t17v_slice_rect Λ ν hY K hK (hCγm B hB) (hCβm C' hC')] with θ hθ
    have hYθ : Measurable fun d => Y (θ, d) := hY.comp (measurable_const.prodMk measurable_id)
    rw [Measure.compProd_apply_prod (hCγm B hB) (hCβm C' hC'),
      Measure.map_apply (hYθ.prodMk measurable_id : Measurable fun d => (Y (θ, d), d))
        ((hCγm B hB).prod (hCβm C' hC')),
      ← lintegral_indicator (hCγm B hB),
      lintegral_map (((K.comap (fun y => (θ, y)) (measurable_const.prodMk measurable_id)).measurable_coe
        (hCβm C' hC')).indicator (hCγm B hB)) hYθ]
    have e1 : (fun d => (Y (θ, d), d)) ⁻¹' (B ×ˢ C') = {d | Y (θ, d) ∈ B ∧ d ∈ C'} := rfl
    rw [e1, hθ]
    refine lintegral_congr fun d => ?_
    by_cases hd : Y (θ, d) ∈ B
    · simp [indicator, hd, Kernel.comap_apply]
    · simp [indicator, hd]
  filter_upwards [(ae_ball_iff hCc).2 hrect] with θ hθ
  have : IsProbabilityMeasure (ν.map fun d => (Y (θ, d), d)) :=
    (Measure.isProbabilityMeasure_map_iff ((hY.comp (measurable_const.prodMk measurable_id)).prodMk
      measurable_id).aemeasurable).2 inferInstance
  have : IsProbabilityMeasure (ν.map fun d => Y (θ, d)) :=
    (Measure.isProbabilityMeasure_map_iff
      (hY.comp (measurable_const.prodMk measurable_id)).aemeasurable).2 inferInstance
  exact ext_of_generate_finite C hgen hpi (fun S hS => hθ S hS) (by simp [measure_univ])

end LQGMetric.LM
