/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.L3_1InFrz at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_1Filt
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepAsm5

/-!
# LM (3.8): the frozen conditional-probability bounds (abstract part)

Source: LM = Gwynne–Miller, *Local metrics of the Gaussian free field*, arXiv:1905.00379,
`literature/src/1905.00379/local-metrics-final.tex`, Lemma 3.3 (l. 623–643) and (3.8)
(l. 725–730); MQ = Miller–Qian arXiv:1812.03913 Lemma 4.1 and Remark 4.2 (l. 549–610);
GM arXiv:1905.00383 l. 989–998 (the same argument for disjoint balls, formalized in
`LQGMetric.Papers.GM.S2.SpatialIndepCore`).

By the Markov property, given `𝓕_{r}` the field on `B_r(0)` is the frozen harmonic part `W`
(`𝓕_r`-measurable) plus an independent zero-boundary GFF `Y`. Hence
`P[(W, Y) ∈ T | 𝓕] = φ(W)` with `φ(w) = P[(w, Y) ∈ T]` (`condExp_frozen`, the freezing lemma;
own elementary proof), and the RN bounds of MQ Lemma 4.1 (compared with the zero-boundary law,
as in MQ Remark 4.2 and GM l. 996–998) give, on the good set, the two bounds used in LM's proof
of Lemma 3.1: `(1 − φ)⁴ ≤ 2c³(1 − P[E])` (`frozen_upper`) and `φ ≥ (p/4)⁴/c³` when
`P[E] ≥ p` (`GM.lowerBound_of_rn`), as long as the good set has probability `≥ 1 − p/4`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace LQGMetric.LM

variable {Ω : Type} {m0 : MeasurableSpace Ω}

/-- independence passes to the null augmentation -/
theorem indep_augSigma {P : @Measure Ω m0} [IsProbabilityMeasure P] {m F : MeasurableSpace Ω}
    (hind : Indep m F P) : Indep m (augSigma P F) P := by
  rw [Indep_iff] at hind ⊢
  rintro s t hs ⟨-, t', ht', htt'⟩
  have h1 : P (s ∩ t) = P (s ∩ t') := measure_congr (EventuallyEqSet.inter (ae_eq_refl s) htt')
  rw [h1, hind s t' hs ht', measure_congr htt']

/-- **freezing lemma**: `W` `m`-measurable, `Y` independent of `m` ⇒
`P[(W, Y) ∈ T | m] = P[(w, Y) ∈ T]|_{w = W}` a.s. (own elementary proof). -/
theorem condExp_frozen {m mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (hm : m ≤ mΩ) {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {W : Ω → α} {Y : Ω → β} (hW : Measurable[m] W) (hY : Measurable Y)
    (hind : Indep m (MeasurableSpace.comap Y inferInstance) P) {T : Set (α × β)}
    (hT : MeasurableSet T) :
    (fun ω => ((P.map Y) (Prod.mk (W ω) ⁻¹' T)).toReal) =ᵐ[P]
      P[{ω | (W ω, Y ω) ∈ T}.indicator (fun _ => (1 : ℝ)) | m] := by
  have hW0 : Measurable W := hW.mono hm le_rfl
  have hE : MeasurableSet {ω | (W ω, Y ω) ∈ T} := (hW0.prodMk hY) hT
  have hf : Measurable fun w : α => (P.map Y) (Prod.mk w ⁻¹' T) :=
    measurable_measure_prodMk_left hT
  refine ae_eq_condExp_of_forall_setIntegral_eq hm ((integrable_const (1 : ℝ)).indicator hE)
    (fun s _ _ => ?_) (fun s hs _ => ?_) ?_
  · refine Integrable.integrableOn ?_
    refine (integrable_const (1 : ℝ)).mono' (hf.comp hW0).ennreal_toReal.aestronglyMeasurable
      (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by rw [ENNReal.ofReal_one]; exact prob_le_one)
  · -- `∫_s φ(W) = P(s ∩ E)`
    have hs0 : MeasurableSet s := hm s hs
    set W' : Ω → α × ℝ := fun ω => (W ω, s.indicator (fun _ => (1 : ℝ)) ω)
    have hW' : Measurable[m] W' := hW.prodMk (measurable_const.indicator hs)
    have hW'0 : Measurable W' := hW'.mono hm le_rfl
    set T' : Set ((α × ℝ) × β) := {q | q.1.2 = 1 ∧ (q.1.1, q.2) ∈ T}
    have hT' : MeasurableSet T' :=
      (measurableSet_eq_fun (measurable_snd.comp measurable_fst) measurable_const).inter
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd hT)
    have hindW' : IndepFun W' Y P := by
      rw [IndepFun_iff_Indep]
      exact indep_of_indep_of_le_left hind hW'.comap_le
    have hsec := GM.prob_eq_lintegral_section P hW'0 hY hindW' hT'
    have hf' : Measurable fun w' : α × ℝ => (P.map Y) {b | (w', b) ∈ T'} :=
      measurable_measure_prodMk_left hT'
    rw [lintegral_map hf' hW'0] at hsec
    have hsecω : ∀ ω, (P.map Y) {b | (W' ω, b) ∈ T'} =
        s.indicator (fun ω => (P.map Y) (Prod.mk (W ω) ⁻¹' T)) ω := by
      intro ω
      by_cases hω : ω ∈ s
      · simp [W', T', hω, indicator_of_mem]; rfl
      · simp [W', T', hω, indicator_of_notMem]
    simp_rw [hsecω] at hsec
    rw [lintegral_indicator hs0] at hsec
    have hset : {ω | (W' ω, Y ω) ∈ T'} = s ∩ {ω | (W ω, Y ω) ∈ T} := by
      ext ω
      by_cases hω : ω ∈ s <;> simp [W', T', hω]
    rw [hset] at hsec
    rw [setIntegral_indicator hE, setIntegral_const, smul_eq_mul, mul_one]
    have hint := integral_toReal (μ := P.restrict s)
      (f := fun x => (P.map Y) (Prod.mk (W x) ⁻¹' T)) (hf.comp hW0).aemeasurable
      (ae_of_all _ fun _ => measure_lt_top _ _)
    rw [hint, ← hsec, Measure.real]
  · exact ((hf.comp hW).ennreal_toReal).aestronglyMeasurable

/-- **upper bound on the conditional failure probability** (MQ Remark 4.2 twice, for the
complementary event): if on the good set (of mass `≥ 1/2`) `φ² ≤ c a` and `a² ≤ c φ`, then
`φ⁴ ≤ 2 c³ ∫ φ`. Own elementary computation. -/
theorem frozen_upper {α : Type*} [MeasurableSpace α] {μW : Measure α} {φ : α → ℝ≥0∞}
    (hφm : Measurable φ) {Good : Set α} (hG : MeasurableSet Good) {c a : ℝ≥0∞}
    (hhalf : 1 / 2 ≤ μW Good)
    (hrn : ∀ᵐ w ∂μW, w ∈ Good → φ w ^ 2 ≤ c * a ∧ a ^ 2 ≤ c * φ w) :
    ∀ᵐ w ∂μW, w ∈ Good → φ w ^ 4 ≤ 2 * c ^ 3 * ∫⁻ w, φ w ∂μW := by
  have h1 : a ^ 2 * μW Good ≤ c * ∫⁻ w, φ w ∂μW := by
    calc a ^ 2 * μW Good = ∫⁻ _ in Good, a ^ 2 ∂μW := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ w in Good, c * φ w ∂μW := by
          refine setLIntegral_mono_ae' hG ?_
          filter_upwards [hrn] with w hw hwG using (hw hwG).2
      _ ≤ ∫⁻ w, c * φ w ∂μW := setLIntegral_le_lintegral _ _
      _ = c * ∫⁻ w, φ w ∂μW := lintegral_const_mul c hφm
  have h2 : a ^ 2 ≤ 2 * c * ∫⁻ w, φ w ∂μW := by
    have h12 : (1 : ℝ≥0∞) ≤ 2 * μW Good := by
      calc (1 : ℝ≥0∞) = 2 * (1 / 2) := by rw [one_div, ENNReal.mul_inv_cancel] <;> norm_num
        _ ≤ 2 * μW Good := by gcongr
    calc a ^ 2 = a ^ 2 * 1 := (mul_one _).symm
      _ ≤ a ^ 2 * (2 * μW Good) := by gcongr
      _ = 2 * (a ^ 2 * μW Good) := by ring
      _ ≤ 2 * (c * ∫⁻ w, φ w ∂μW) := by gcongr
      _ = 2 * c * ∫⁻ w, φ w ∂μW := by ring
  filter_upwards [hrn] with w hw hwG
  calc φ w ^ 4 = (φ w ^ 2) ^ 2 := by ring
    _ ≤ (c * a) ^ 2 := by gcongr; exact (hw hwG).1
    _ = c ^ 2 * a ^ 2 := by ring
    _ ≤ c ^ 2 * (2 * c * ∫⁻ w, φ w ∂μW) := by gcongr
    _ = 2 * c ^ 3 * ∫⁻ w, φ w ∂μW := by ring

end LQGMetric.LM
