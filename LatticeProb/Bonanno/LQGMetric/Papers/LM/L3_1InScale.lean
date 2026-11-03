/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.L3_1InScale at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_1InRep

/-!
# LM (3.8) at one scale (MQ Lemma 4.1 + Remark 4.2 form)

Source: LM arXiv:1905.00379 (`literature/src/1905.00379/local-metrics-final.tex`) Lemma 3.3
(l. 623–643) and (3.8) (l. 725–730); MQ arXiv:1812.03913 Lemma 4.1 and Remark 4.2
(l. 549–610); GM arXiv:1905.00383 l. 989–998 (`GM.rn_bounds_of_rep`, `GM.lowerBound_of_rn`).

At scale `r`, with the decomposition `IsLMRep` of `lmScaled h r` on `B_1(0)`, an event of the
annulus σ-algebra is `{(W, Y) ∈ T}` a.s., with `W` the centred harmonic part
(`𝓕_r`-measurable) and `Y = h̊|_{B_{s₂}}` independent of `𝓕_r`. The freezing lemma
`condExp_frozen` and the RN bounds of MQ Lemma 4.1 (radii `ρ₁ = s₂ < ρ₂ = (1+s₂)/2 < 1`) on the
good event give `lm38_scale`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric TopologicalSpace InnerProductSpace
open scoped ENNReal

namespace LQGMetric.LM

open Blueprint

/-- `GM.rn_bounds_of_rep` with the inner ball `B(x, ρ₁R)` of any radius -/
theorem rn_bounds_gen {ρ₁ ρ₂ M c : ℝ} (hc : GM.MQSpec ρ₁ ρ₂ M c) {x : ℂ} {R : ℝ} (hR : 0 < R)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ht hz : Ω → DistC} (htm : Measurable ht) (hthz : ∀ᵐ ω ∂P, ht ω = hz ω)
    (hzb : IsZeroBoundaryGFF (ballO x R) (fun ω => restrictTo (ballO x R) (hz ω)) P)
    {g : ℂ → ℝ} (hg : HarmonicOnNhd g (ball x R)) {a0 : ℝ}
    (hb : ∀ w ∈ ball x (ρ₂ * R), |g w - a0| ≤ M) {T : DistC}
    (hT : ∀ φ : TestOn (ballO x R), restrictTo (ballO x R) T φ = ∫ y, (g y - a0) * φ y)
    {S : Set (DistOn (ballO x (ρ₁ * R)))} (hS : MeasurableSet S) :
    (P.map fun ω => restrictTo (ballO x (ρ₁ * R)) (hz ω))
        {b | b + restrictTo (ballO x (ρ₁ * R)) T ∈ S} ^ 2 ≤
        ENNReal.ofReal c * (P.map fun ω => restrictTo (ballO x (ρ₁ * R)) (hz ω)) S ∧
      (P.map fun ω => restrictTo (ballO x (ρ₁ * R)) (hz ω)) S ^ 2 ≤
        ENNReal.ofReal c * (P.map fun ω => restrictTo (ballO x (ρ₁ * R)) (hz ω))
          {b | b + restrictTo (ballO x (ρ₁ * R)) T ∈ S} := by
  have hzb' : IsZeroBoundaryGFF (ballO x R) (fun ω => restrictTo (ballO x R) (ht ω)) P :=
    GM.isZeroBoundaryGFF_of_ae_eq hzb (by filter_upwards [hthz] with ω hω; rw [hω])
      ((measurable_restrictTo _).comp htm)
  have H := hc x R hR P ht htm hzb' g hg a0 hb T hT
  dsimp only at H
  obtain ⟨h1, h2, h3, h4⟩ := H
  have hP := GM.rn_pair_bounds h1 h2 h3 h4 hS
  have e0 : (P.map fun ω => restrictTo (ballO x (ρ₁ * R)) (ht ω)) =
      P.map fun ω => restrictTo (ballO x (ρ₁ * R)) (hz ω) :=
    Measure.map_congr (by filter_upwards [hthz] with ω hω; rw [hω])
  have hadd : Measurable fun b : DistOn (ballO x (ρ₁ * R)) =>
      b + restrictTo (ballO x (ρ₁ * R)) T :=
    measurable_distOn_iff.2 fun φ => by
      show Measurable fun b : DistOn (ballO x (ρ₁ * R)) =>
        b φ + restrictTo (ballO x (ρ₁ * R)) T φ
      exact (measurable_distOn_apply φ).add_const _
  have eg : (P.map fun ω => restrictTo (ballO x (ρ₁ * R)) (ht ω + T)) S =
      (P.map fun ω => restrictTo (ballO x (ρ₁ * R)) (hz ω))
        {b | b + restrictTo (ballO x (ρ₁ * R)) T ∈ S} := by
    have : (fun ω => restrictTo (ballO x (ρ₁ * R)) (ht ω + T)) =
        (fun b => b + restrictTo (ballO x (ρ₁ * R)) T) ∘
          fun ω => restrictTo (ballO x (ρ₁ * R)) (ht ω) := by
      funext ω; simp only [Function.comp, GM.restrictTo_add_gm]
    have hm : Measurable fun ω => restrictTo (ballO x (ρ₁ * R)) (ht ω) :=
      (measurable_restrictTo _).comp htm
    rw [this, ← Measure.map_map hadd hm, e0, Measure.map_apply hadd hS]
    rfl
  rw [eg, e0] at hP
  exact hP

lemma addConst_zero' (T : DistC) : addConst T 0 = T := by
  refine DFunLike.ext _ _ fun φ => ?_
  rw [GFFInv.addConst_apply]; ring

lemma measurableSet_shiftSet1 (V : Opens ℂ) {S : Set (DistOn V)} (hS : MeasurableSet S) :
    MeasurableSet {q : DistC × DistOn V | q.2 + restrictTo V q.1 ∈ S} := by
  have hm : Measurable fun q : DistC × DistOn V => q.2 + restrictTo V q.1 :=
    measurable_distOn_iff.2 fun φ => by
      show Measurable fun q : DistC × DistOn V => q.2 φ + restrictTo V q.1 φ
      exact ((measurable_distOn_apply φ).comp measurable_snd).add
        ((measurable_distOn_apply φ).comp ((measurable_restrictTo V).comp measurable_fst))
  exact hm hS

variable {Ω : Type} [mΩ : MeasurableSpace Ω]

omit mΩ in
lemma measurable_lmW (h G : Ω → DistC) (r : ℝ)
    (hG : Measurable[fieldSigmaClosed (lmScaled h r) (ball (0 : ℂ) 1)ᶜ] G) :
    Measurable[fieldSigmaClosed (lmScaled h r) (ball (0 : ℂ) 1)ᶜ]
      fun ω => addConst (G ω) (-circleAvg (lmScaled h r ω) 1 0) := by
  have hc : Measurable[fieldSigmaClosed (lmScaled h r) (ball (0 : ℂ) 1)ᶜ]
      fun ω => -circleAvg (lmScaled h r ω) 1 0 :=
    (GM.measurable_circleAvg_fieldSigmaClosed _ 1 0 (fun y hy => by
      simp only [abs_one, mem_sphere_iff_norm, sub_zero] at hy
      simp [mem_ball, hy])).neg
  have hW := @GM.measurable_addConst_pi Ω (fieldSigmaClosed (lmScaled h r) (ball (0 : ℂ) 1)ᶜ)
    Unit G (fun _ ω => -circleAvg (lmScaled h r ω) 1 0) hG (fun _ => hc)
  exact (measurable_pi_apply ()).comp hW

/-- **LM (3.8) at one scale**, in the form given by MQ Lemma 4.1 + Remark 4.2 (zero-boundary
comparison), on the good event `{𝔐 ≤ M}` of probability `≥ 1 − p/4`. -/
theorem lm38_scale {s₂ : ℝ} {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) {r : ℝ} (hr : 0 < r) {hh0 hz G : Ω → DistC}
    (hrep : IsLMRep P h r hh0 hz G) {δ : ℝ} (hδ : 0 < δ) (hρδ : (1 + s₂) / 2 * 1 + δ < 1)
    {Sd : Set ℂ} (hSdc : Sd.Countable) (hSdd : Dense Sd) {M c : ℝ} (hc : GM.MQSpec s₂ ((1 + s₂) / 2) M c)
    (hc0 : 0 < c) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hbad : P (lmGood δ hδ.le Sd ((1 + s₂) / 2) M h G r)ᶜ ≤ ENNReal.ofReal (p / 4))
    {s₁ : ℝ} {A : Set Ω} (hA : MeasurableSet[annSigma h s₁ s₂ r] A) :
    ∀ᵐ ω ∂P, ω ∈ lmGood δ hδ.le Sd ((1 + s₂) / 2) M h G r →
      (1 - P[A.indicator (fun _ => (1 : ℝ)) | augSigma P (lmF h r)] ω) ^ 4 ≤
        2 * c ^ 3 * (1 - P.real A) ∧
      (p ≤ P.real A →
        (p / 4) ^ 4 / c ^ 3 ≤ P[A.indicator (fun _ => (1 : ℝ)) | augSigma P (lmF h r)] ω) := by
  obtain ⟨hdec, hhG, hGF, hharm, hzb, hind⟩ := hrep
  set g := lmScaled h r with hgdef
  have hg : IsWholePlaneGFF g P := isWholePlaneGFF_lmScaled hh hr
  have hm : augSigma P (lmF h r) ≤ mΩ := augSigma_le P _
  have hlmF : lmF h r ≤ mΩ :=
    GM.fieldSigmaClosed_le_gm (measurable_recentre hh.measurable r) _
  have hFm : fieldSigmaClosed g (ball (0 : ℂ) 1)ᶜ ≤ augSigma P (lmF h r) :=
    (fieldSigmaClosed_lmScaled_le h hr).trans (le_augSigma P hlmF)
  set W : Ω → DistC := fun ω => addConst (G ω) (-circleAvg (g ω) 1 0) with hWdef
  have hWm : Measurable[augSigma P (lmF h r)] W := (measurable_lmW h G r hGF).mono hFm le_rfl
  have hW0 : Measurable W := hWm.mono hm le_rfl
  set V : Opens ℂ := ballO 0 (s₂ * 1)
  set Y : Ω → DistOn V := fun ω => restrictTo V (hz ω) with hYdef
  have hs₂1 : s₂ < 1 := by linarith
  have hVB : V ≤ ballO 0 1 := fun y hy => by
    have : ‖y‖ < s₂ * 1 := by simpa [V, ballO] using hy
    show y ∈ ball (0 : ℂ) 1; simp only [mem_ball, dist_zero_right]; linarith
  have hYeq : Y = GM.distRes V (ballO 0 1) ∘ fun ω => restrictTo (ballO 0 1) (hz ω) := by
    funext ω; exact (GM.distRes_restrictTo hVB (hz ω)).symm
  have hY : Measurable Y := by rw [hYeq]; exact (GM.measurable_distRes _ _).comp hzb.measurable
  have hindY : Indep (augSigma P (lmF h r)) (MeasurableSpace.comap Y inferInstance) P := by
    have h1 : Indep (MeasurableSpace.comap hz inferInstance) (augSigma P (lmF h r)) P :=
      indep_augSigma (indep_of_indep_of_le_right hind (lmF_le_fieldSigmaClosed_lmScaled h hr))
    refine indep_of_indep_of_le_right h1.symm ?_
    show MeasurableSpace.comap ((fun T => restrictTo V T) ∘ hz) _ ≤ _
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_restrictTo V).comap_le
  have hWY : IndepFun W Y P := by
    rw [IndepFun_iff_Indep]; exact indep_of_indep_of_le_left hindY hWm.comap_le
  -- the event
  have hA' := annSigma_le_lmScaled h hr A hA
  rw [show ballO (0 : ℂ) s₂ = V by simp only [V, mul_one]] at hA'
  obtain ⟨S, hS, rfl⟩ := hA'
  set T : Set (DistC × DistOn V) := {q | q.2 + restrictTo V q.1 ∈ S}
  have hT : MeasurableSet T := measurableSet_shiftSet1 V hS
  have hAeq : (fun ω => restrictTo V (g ω)) ⁻¹' S =ᵐ[P] {ω | (W ω, Y ω) ∈ T} := by
    refine eventuallyEqSet_iff.2 ?_
    filter_upwards [hhG, ae_circleAvg_lmScaled hh hr] with ω hω hc0
    show restrictTo V (g ω) ∈ S ↔ Y ω + restrictTo V (W ω) ∈ S
    have hWω : W ω = G ω := by
      show addConst (G ω) (-circleAvg (g ω) 1 0) = G ω
      rw [hc0, neg_zero, addConst_zero']
    have : g ω = hz ω + W ω := by rw [hWω, hdec ω, hω, add_comm]
    rw [this, GM.restrictTo_add_gm]
  set E : Set Ω := (fun ω => restrictTo V (g ω)) ⁻¹' S
  have hE0 : MeasurableSet E := ((measurable_restrictTo _).comp hg.measurable) hS
  have hET : MeasurableSet {ω | (W ω, Y ω) ∈ T} := (hW0.prodMk hY) hT
  -- the conditional probability is frozen
  set φ : DistC → ℝ≥0∞ := fun w => (P.map Y) (Prod.mk w ⁻¹' T)
  set φc : DistC → ℝ≥0∞ := fun w => (P.map Y) (Prod.mk w ⁻¹' Tᶜ)
  have hφm : Measurable φ := measurable_measure_prodMk_left hT
  have hφcm : Measurable φc := measurable_measure_prodMk_left hT.compl
  have hφφc : ∀ w, φc w = 1 - φ w := fun w => by
    show (P.map Y) (Prod.mk w ⁻¹' Tᶜ) = 1 - (P.map Y) (Prod.mk w ⁻¹' T)
    rw [preimage_compl, prob_compl_eq_one_sub (measurable_prodMk_left hT)]
  have hce : P[E.indicator (fun _ => (1 : ℝ)) | augSigma P (lmF h r)] =ᵐ[P] fun ω => (φ (W ω)).toReal := by
    have h1 : E.indicator (fun _ => (1 : ℝ)) =ᵐ[P]
        {ω | (W ω, Y ω) ∈ T}.indicator (fun _ => (1 : ℝ)) := indicator_ae_eq_of_ae_eq_set hAeq
    exact (condExp_congr_ae h1).trans (condExp_frozen hm hWm hY hindY hT).symm
  -- the laws
  set μW := P.map W
  set GoodS : Set DistC := {T' | GM.goodD δ hδ.le Sd 0 ((1 + s₂) / 2 * 1) M T'}
  have hGoodS : MeasurableSet GoodS := GM.measurableSet_goodD hδ.le hSdc 0 _ M
  -- MQ Lemma 4.1 + Remark 4.2 on the good set
  have hGm : Measurable G := hGF.mono (GM.fieldSigmaClosed_le_gm hg.measurable _) le_rfl
  set ht : Ω → DistC := fun ω => g ω - G ω with htdef
  have htm : Measurable ht := measurable_distOn_iff.2 fun φ => by
    show Measurable fun ω => g ω φ - G ω φ
    exact ((measurable_distOn_apply φ).comp hg.measurable).sub
      ((measurable_distOn_apply φ).comp hGm)
  have hthz : ∀ᵐ ω ∂P, ht ω = hz ω := by
    filter_upwards [hhG] with ω hω
    simp only [htdef]; rw [hdec ω, hω, add_sub_cancel_left]
  have hgood_ae : ∀ S' : Set (DistOn V), MeasurableSet S' → ∀ᵐ ω ∂P, W ω ∈ GoodS →
      (P.map Y) {b | b + restrictTo V (W ω) ∈ S'} ^ 2 ≤ ENNReal.ofReal c * (P.map Y) S' ∧
      (P.map Y) S' ^ 2 ≤ ENNReal.ofReal c * (P.map Y) {b | b + restrictTo V (W ω) ∈ S'} := by
    intro S' hS'
    filter_upwards [hhG, hharm] with ω hω hωh hgood
    obtain ⟨gf, hgf, hrepf⟩ := hωh
    rw [hω] at hrepf
    obtain ⟨hrepW, hbd⟩ := GM.pointwise_good (U := ballO 0 1) hgf hrepf hδ (fun y hy => hy)
      hρδ hSdd hgood
    exact rn_bounds_gen hc (x := 0) one_pos htm hthz hzb hgf hbd hrepW hS'
  have hmeasA : ∀ ψ : DistC → ℝ≥0∞, Measurable ψ → ∀ a : ℝ≥0∞,
      MeasurableSet {w : DistC | w ∈ GoodS → ψ w ^ 2 ≤ ENNReal.ofReal c * a ∧
        a ^ 2 ≤ ENNReal.ofReal c * ψ w} := fun ψ hψ a =>
    MeasurableSet.imp hGoodS ((measurableSet_le (hψ.pow_const 2) measurable_const).inter
      (measurableSet_le measurable_const (hψ.const_mul _)))
  have hrnA : ∀ᵐ w ∂μW, w ∈ GoodS →
      φ w ^ 2 ≤ ENNReal.ofReal c * (P.map Y) S ∧ (P.map Y) S ^ 2 ≤ ENNReal.ofReal c * φ w :=
    (ae_map_iff hW0.aemeasurable (hmeasA φ hφm _)).2 (hgood_ae S hS)
  have hrnAc : ∀ᵐ w ∂μW, w ∈ GoodS →
      φc w ^ 2 ≤ ENNReal.ofReal c * (P.map Y) Sᶜ ∧ (P.map Y) Sᶜ ^ 2 ≤ ENNReal.ofReal c * φc w :=
    (ae_map_iff hW0.aemeasurable (hmeasA φc hφcm _)).2 (hgood_ae Sᶜ hS.compl)
  -- probabilities through the frozen sections
  have hPE : P E = ∫⁻ w, φ w ∂μW :=
    (measure_congr hAeq).trans (GM.prob_eq_lintegral_section P hW0 hY hWY hT)
  have hPEc : P Eᶜ = ∫⁻ w, φc w ∂μW := by
    refine (measure_congr hAeq.compl).trans ?_
    exact GM.prob_eq_lintegral_section P hW0 hY hWY hT.compl
  have hbadW : μW GoodSᶜ ≤ ENNReal.ofReal (p / 4) := by
    rw [Measure.map_apply hW0 hGoodS.compl]; exact hbad
  have hhalf : 1 / 2 ≤ μW GoodS := by
    calc (1 : ℝ≥0∞) / 2 = ENNReal.ofReal (1 / 2) := by
          rw [ENNReal.ofReal_div_of_pos two_pos]; simp
      _ ≤ ENNReal.ofReal (1 - p / 4) := ENNReal.ofReal_le_ofReal (by linarith)
      _ = ENNReal.ofReal 1 - ENNReal.ofReal (p / 4) := ENNReal.ofReal_sub _ (by positivity)
      _ = 1 - ENNReal.ofReal (p / 4) := by rw [ENNReal.ofReal_one]
      _ ≤ 1 - μW GoodSᶜ := tsub_le_tsub_left hbadW 1
      _ = μW GoodS := by rw [← prob_compl_eq_one_sub hGoodS.compl, compl_compl]
  have hup := frozen_upper hφcm hGoodS hhalf hrnAc
  rw [← hPEc] at hup
  have hup' := ae_of_ae_map hW0.aemeasurable hup
  have hPEc' : (P Eᶜ).toReal = 1 - P.real E := by
    rw [prob_compl_eq_one_sub hE0, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top]
    rfl
  -- the lower bound (only used when `P[E] ≥ p`)
  have hlow : p ≤ P.real E → ∀ᵐ ω ∂P, W ω ∈ GoodS →
      (ENNReal.ofReal p / 4) ^ 4 / ENNReal.ofReal c ^ 3 ≤ φ (W ω) := by
    intro hpE
    refine ae_of_ae_map hW0.aemeasurable (GM.lowerBound_of_rn (fun w => prob_le_one) hGoodS
      (by simp [hp]) ENNReal.ofReal_ne_top ?_ ?_ hrnA)
    · rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_div_of_pos (by norm_num)]; exact hbadW
    · rw [← hPE]; exact ENNReal.ofReal_le_of_le_toReal hpE
  have key : ∀ ω, P[E.indicator (fun _ => (1 : ℝ)) | augSigma P (lmF h r)] ω =
      (φ (W ω)).toReal → (W ω ∈ GoodS → φc (W ω) ^ 4 ≤ 2 * ENNReal.ofReal c ^ 3 * P Eᶜ) →
      W ω ∈ GoodS →
      (1 - P[E.indicator (fun _ => (1 : ℝ)) | augSigma P (lmF h r)] ω) ^ 4 ≤
        2 * c ^ 3 * (1 - P.real E) := by
    intro ω hcp hupω hω
    have hφ1 : φ (W ω) ≤ 1 := prob_le_one
    have h1c : 1 - (φ (W ω)).toReal = (φc (W ω)).toReal := by
      rw [hφφc, ENNReal.toReal_sub_of_le hφ1 ENNReal.one_ne_top, ENNReal.toReal_one]
    rw [hcp, h1c]
    have := ENNReal.toReal_mono (by
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num)
        (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)) (measure_ne_top _ _)) (hupω hω)
    rw [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hc0.le, hPEc'] at this
    simpa using this
  by_cases hpE : p ≤ P.real E
  · filter_upwards [hce, hup', hlow hpE] with ω hceω hupω hlowω hω
    refine ⟨key ω hceω hupω hω, fun _ => ?_⟩
    rw [hceω]
    have := ENNReal.toReal_mono (measure_ne_top _ _) (hlowω hω)
    rw [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_pow, ENNReal.toReal_div,
      ENNReal.toReal_ofReal hp.le, ENNReal.toReal_ofReal hc0.le] at this
    simpa using this
  · filter_upwards [hce, hup'] with ω hceω hupω hω
    exact ⟨key ω hceω hupω hω, fun h => absurd h hpE⟩

end LQGMetric.LM
