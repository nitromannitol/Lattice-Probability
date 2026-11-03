/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.L3_1InAsm at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_1InScale
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_1InQ
import LatticeProb.Bonanno.LQGMetric.Papers.MQ.Lem41

/-!
# LM Lemma 3.1 inputs: assembly of (3.8) at all scales; (3.10) as the remaining leaf

Source: LM arXiv:1905.00379 (`literature/src/1905.00379/local-metrics-final.tex`), proof of
Lemma 3.1 (l. 723–764), Lemma 3.3 (l. 623–643), Lemma 3.4 (l. 696–706); GM arXiv:1905.00383
l. 984–988 (`GM.exists_good_const`: `P[𝔐 > A] ≤ ε` uniformly, here at the fixed scale `1`
after scaling, hence uniformly in `r_k`).

* `prob_lmGood_compl_le` — the bad event at scale `r` has probability `≤ 3ε` for `M ≥ A(ε)`.
* `LMGoodScaleLeaf` — LM Lemma 3.4 / (3.10) for the good events `lmGood` built from any Markov
  decompositions at the scales `r_k` (exact remaining statement; MQ Prop 4.3 redone for general
  `(r_k)`).
* `lmAnnulusIterInputQ_of` — `LMAnnulusIterInputQ` from MQ Lemma 4.1 and the leaf;
  `lmLem3_1a_of_leaf`, `lmLem3_1b_of_leaf` — LM Lemma 3.1 from the leaf.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric TopologicalSpace InnerProductSpace
open scoped ENNReal

namespace LQGMetric.LM

open Blueprint

/-- the countable dense set of centres used to read off `𝔐` -/
def lmSd : Set ℂ := Classical.choose (TopologicalSpace.exists_countable_dense ℂ)

lemma lmSd_countable : lmSd.Countable :=
  (Classical.choose_spec (TopologicalSpace.exists_countable_dense ℂ)).1

lemma lmSd_dense : Dense lmSd :=
  (Classical.choose_spec (TopologicalSpace.exists_countable_dense ℂ)).2

/-- the bump radius `δ = (1 − s₂)/8` -/
def lmδ (s₂ : ℝ) : ℝ := |1 - s₂| / 8

lemma lmδ_nonneg (s₂ : ℝ) : 0 ≤ lmδ s₂ := by unfold lmδ; positivity

/-- **GM l. 984–988 at scale `1`**: the bad event has probability `≤ 3ε` uniformly. -/
theorem prob_lmGood_compl_le {s₂ : ℝ} (hs₂0 : 0 < s₂) (hs₂ : s₂ < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ A : ℝ, 0 < A ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P → ∀ r : ℝ, 0 < r → ∀ hh0 hz G : Ω → DistC,
      IsLMRep P h r hh0 hz G →
      P (lmGood (lmδ s₂) (lmδ_nonneg s₂) lmSd ((1 + s₂) / 2) A h G r)ᶜ ≤
        ENNReal.ofReal (3 * ε) := by
  have hδe : lmδ s₂ = (1 - s₂) / 8 := by unfold lmδ; rw [abs_of_pos (by linarith)]
  have hδ : 0 < lmδ s₂ := by rw [hδe]; linarith
  have hδ1 : lmδ s₂ < 1 := by rw [hδe]; linarith
  have hρ₂1 : (1 + s₂) / 2 < 1 := by linarith
  have hρδ : (1 + s₂) / 2 * 1 + lmδ s₂ < 1 := by rw [hδe]; linarith
  obtain ⟨A, hA, hosc, hoff, hzv⟩ := GM.exists_good_const hδ hδ1 hρ₂1 one_pos hε
  refine ⟨A, hA, fun {Ω} _ P _ h hh r hr hh0 hz G hrep => ?_⟩
  obtain ⟨hdec, hhG, hGF, hharm, hzb, hind⟩ := hrep
  have hg := isWholePlaneGFF_lmScaled hh hr
  have hGm : Measurable G := hGF.mono (GM.fieldSigmaClosed_le_gm hg.measurable _) le_rfl
  have hindG : Indep (MeasurableSpace.comap hz inferInstance)
      (MeasurableSpace.comap G inferInstance) P :=
    indep_of_indep_of_le_right hind hGF.comap_le
  have hdecG : ∀ᵐ ω ∂P, lmScaled h r ω = G ω + hz ω := by
    filter_upwards [hhG] with ω hω; rw [hdec, hω]
  have hρ : 0 ≤ (1 + s₂) / 2 * 1 := by positivity
  have h0 := GM.prob_not_goodD_le (P := P) (h' := lmScaled h r) (G := G) (U := ballO 0 1)
    hdec hhG hharm (A := A) hδ (x := 0) (R := 1) (fun y hy => hy) hρδ hρ lmSd
  have h1 := GM.prob_oscEv_le hg hzb hindG hdecG hGm (z := 0) one_pos (by positivity) hρ₂1
    (fun y hy => hy) (half_pos hA)
  have h2 := hoff P (lmScaled h r) hg 0
  have hI := GM.integral_radProf_pos hδ
  have h3 := GM.prob_zbPair_ge_le hδ hδ1 hzb (t := A * (∫ y, GM.radProf (lmδ s₂) y) / 4)
    (by positivity)
  calc P (lmGood (lmδ s₂) (lmδ_nonneg s₂) lmSd ((1 + s₂) / 2) A h G r)ᶜ ≤ _ :=
        (measure_mono fun ω hω => hω).trans h0
    _ ≤ ENNReal.ofReal ε + ENNReal.ofReal ε + ENNReal.ofReal ε :=
        add_le_add (add_le_add (h1.trans (hosc 0)) h2) (h3.trans (ENNReal.ofReal_le_ofReal hzv))
    _ = ENNReal.ofReal (3 * ε) := by
        rw [← ENNReal.ofReal_add hε.le hε.le, ← ENNReal.ofReal_add (by positivity) hε.le]
        congr 1; ring

/-- **LM Lemma 3.4** (l. 696–706) in the form used at l. 736–740 ((3.10)), for the good events
`{𝔐^{r_k}_{s'r_k} ≤ M}` read off any Markov decompositions at the scales `r_k`
(`s' = (1+s₂)/2`). Remaining leaf (MQ Prop 4.3, l. 613–733 of arXiv:1812.03913, redone for
general `(r_k)` with `r_{k+1}/r_k ≤ s₁`). -/
def LMGoodScaleLeaf (s₁ s₂ : ℝ) : Prop :=
  ∃ M₀ c₀ : ℝ → ℝ → ℝ, (∀ a b, 0 < c₀ a b) ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsNormalizedWPGFF h P → ∀ r : ℕ → ℝ, (∀ k, 0 < r k) → Antitone r →
      (∀ k, r (k + 1) / r k ≤ s₁) → ∀ hh0 hz G : ℕ → Ω → DistC,
      (∀ k, IsLMRep P h (r k) (hh0 k) (hz k) (G k)) →
      ∀ a, 0 < a → ∀ b, 0 < b → b < 1 → ∀ K : ℕ,
        P.real {ω | (countOcc (fun k => lmGood (lmδ s₂) (lmδ_nonneg s₂) lmSd ((1 + s₂) / 2)
          (M₀ a b) h (G k) (r k)) K ω : ℝ) < b * K} ≤ c₀ a b * Real.exp (-a * K)

/-- `LMAnnulusIterInputQ` from MQ Lemma 4.1 (general radii) and the leaf (3.10). -/
theorem lmAnnulusIterInputQ_of (hMQ : MQLem4_1Gen) {s₁ s₂ : ℝ} (hs₂0 : 0 < s₂) (hs₂ : s₂ < 1)
    (hL : LMGoodScaleLeaf s₁ s₂) : LMAnnulusIterInputQ s₁ s₂ := by
  classical
  obtain ⟨M₀, c₀, hc₀, HL⟩ := hL
  have hρ₁₂ : s₂ < (1 + s₂) / 2 := by linarith
  have hρ₂1 : (1 + s₂) / 2 < 1 := by linarith
  have hδe : lmδ s₂ = (1 - s₂) / 8 := by unfold lmδ; rw [abs_of_pos (by linarith)]
  have hδ : 0 < lmδ s₂ := by rw [hδe]; linarith
  have hρδ : (1 + s₂) / 2 * 1 + lmδ s₂ < 1 := by rw [hδe]; linarith
  let cM : ℝ → ℝ := fun M => if hM : 0 < M then
    Classical.choose (GM.exists_MQSpec hMQ hs₂0 hρ₁₂ hρ₂1 hM) else 1
  have hcM : ∀ M, 0 < M → 0 < cM M ∧ GM.MQSpec s₂ ((1 + s₂) / 2) M (cM M) := fun M hM => by
    simp only [cM, dif_pos hM]
    exact Classical.choose_spec (GM.exists_MQSpec hMQ hs₂0 hρ₁₂ hρ₂1 hM)
  have hcM0 : ∀ M, 0 < cM M := fun M => by
    by_cases hM : 0 < M
    · exact (hcM M hM).1
    · simp only [cM, dif_neg hM]; exact one_pos
  let M₁ : ℝ → ℝ := fun p => if hp : 0 < p then
    Classical.choose (prob_lmGood_compl_le hs₂0 hs₂ (ε := p / 12) (by positivity)) else 1
  have hM₁ : ∀ p, 0 < p → 0 < M₁ p ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistC), IsWholePlaneGFF h P → ∀ r : ℝ, 0 < r →
      ∀ hh0 hz G : Ω → DistC, IsLMRep P h r hh0 hz G →
      P (lmGood (lmδ s₂) (lmδ_nonneg s₂) lmSd ((1 + s₂) / 2) (M₁ p) h G r)ᶜ ≤
        ENNReal.ofReal (3 * (p / 12)) := fun p hp => by
    simp only [M₁, dif_pos hp]
    exact Classical.choose_spec (prob_lmGood_compl_le hs₂0 hs₂ (ε := p / 12) (by positivity))
  refine ⟨fun M => 2 * cM M ^ 3, M₁, M₀, c₀, fun M => by have := hcM0 M; positivity, hc₀, ?_⟩
  intro Ω _ P _ h hh r hr0 hrA hrs
  choose hh0 hz G hrep using fun k => exists_lmRep hh.1 (hr0 k)
  have hlmF : ∀ k, lmF h (r k) ≤ ‹MeasurableSpace Ω› := fun k =>
    GM.fieldSigmaClosed_le_gm (measurable_recentre hh.1.measurable (r k)) _
  refine ⟨fun M k => lmGood (lmδ s₂) (lmδ_nonneg s₂) lmSd ((1 + s₂) / 2) M h (G k) (r k),
    fun M k => le_augSigma P (hlmF k) _ (measurableSet_lmGood (lmδ_nonneg s₂) lmSd_countable
      _ M h (G k) (hr0 k) (hrep k).2.2.1),
    fun M M' k hMM => lmGood_mono hδ hMM h (G k) (r k), ?_,
    HL P h hh r hr0 hrA hrs hh0 hz G hrep⟩
  intro p hp hp1 M hM k A hA
  obtain ⟨hM₁0, hM₁b⟩ := hM₁ p hp
  have hM0 : 0 < M := hM₁0.trans_le hM
  obtain ⟨hc0, hc⟩ := hcM M hM0
  have hbad : P (lmGood (lmδ s₂) hδ.le lmSd ((1 + s₂) / 2) M h (G k) (r k))ᶜ ≤
      ENNReal.ofReal (p / 4) := by
    refine (measure_mono (compl_subset_compl.2 (lmGood_mono hδ hM h (G k) (r k)))).trans ?_
    refine (hM₁b P h hh.1 (r k) (hr0 k) (hh0 k) (hz k) (G k) (hrep k)).trans (le_of_eq ?_)
    congr 1; ring
  have H := lm38_scale hh.1 (hr0 k) (hrep k) hδ hρδ lmSd_countable lmSd_dense hc hc0 hp hp1
    hbad (s₁ := s₁) hA
  filter_upwards [H] with ω hω hG
  obtain ⟨h1, h2⟩ := hω hG
  refine ⟨h1, fun hpA => (div_le_div_of_nonneg_left (by positivity) (by positivity)
    (by nlinarith [pow_pos hc0 3])).trans (h2 hpA)⟩

/-- **LM Lemma 3.1 (1)** (`N = 0`) from (3.10) (`LMGoodScaleLeaf`). -/
theorem lmLem3_1a_of_leaf (hL : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ → s₂ < 1 → LMGoodScaleLeaf s₁ s₂) :
    LMLem3_1a :=
  lmLem3_1a_of_inputQ fun s₁ s₂ h1 h2 h3 =>
    lmAnnulusIterInputQ_of MQ.mqLem4_1Gen (h1.trans h2) h3 (hL s₁ s₂ h1 h2 h3)

end LQGMetric.LM
