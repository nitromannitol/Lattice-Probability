/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.L3_1InQ at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_1Filt

/-!
# LM Lemma 3.1 (`N = 0`) from (3.8) in Miller–Qian form and (3.10)

Source: LM = Gwynne–Miller, *Local metrics of the Gaussian free field*, arXiv:1905.00379,
`literature/src/1905.00379/local-metrics-final.tex`, proof of Lemma 3.1 (l. 723–764).

LM l. 725–730 derive (3.8) from LM Lemma 3.3 (RN derivative of the conditional law of the field
on `B_{sr}` given `𝓕_r` w.r.t. its *marginal* law). LM's proof of Lemma 3.3 cites MQ Lemma 4.1,
which compares with the *zero-boundary* law (`Blueprint.MQLem4_1Gen`). From the zero-boundary
comparison one gets (as in MQ Remark 4.2 and GM l. 996–998) the two bounds of
`LMAnnulusIterInputQ`, valid once the good event has probability `≥ 1 − p/4` (i.e. for
`M ≥ M₁(p)`), which is all LM's proof uses: `p_M → 1` as `p → 1` (l. 727) and `p_M > 0`
(l. 755). The good events are increasing in `M`, so (3.10) at `M₀` gives it at every `M ≥ M₀`.
The constant choices follow `lmLem3_1a_of_input`, `lmLem3_1b_of_input` (P2-LM31).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory

namespace LQGMetric.LM

open Blueprint

/-- (3.8) in the form obtained from MQ Lemma 4.1 (zero-boundary comparison) and (3.10). -/
def LMAnnulusIterInputQ (s₁ s₂ : ℝ) : Prop :=
  ∃ (C M₁ : ℝ → ℝ) (M₀ c₀ : ℝ → ℝ → ℝ), (∀ M, 0 < C M) ∧ (∀ a b, 0 < c₀ a b) ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
      (hh : IsNormalizedWPGFF h P) (r : ℕ → ℝ) (hr0 : ∀ k, 0 < r k) (hrA : Antitone r),
      (∀ k, r (k + 1) / r k ≤ s₁) →
      ∃ Good : ℝ → ℕ → Set Ω,
        (∀ M k, MeasurableSet[lmFiltration P hh.1 hr0 hrA k] (Good M k)) ∧
        (∀ M M' k, M ≤ M' → Good M k ⊆ Good M' k) ∧
        (∀ p, 0 < p → p ≤ 1 → ∀ M, M₁ p ≤ M → ∀ k (A : Set Ω),
          MeasurableSet[annSigma h s₁ s₂ (r k)] A →
          ∀ᵐ ω ∂P, ω ∈ Good M k →
            (1 - P[A.indicator (fun _ => (1 : ℝ)) | lmFiltration P hh.1 hr0 hrA k] ω) ^ 4 ≤
              C M * (1 - P.real A) ∧
            (p ≤ P.real A → (p / 4) ^ 4 / C M ≤
              P[A.indicator (fun _ => (1 : ℝ)) | lmFiltration P hh.1 hr0 hrA k] ω)) ∧
        (∀ a, 0 < a → ∀ b, 0 < b → b < 1 → ∀ K : ℕ,
          P.real {ω | (countOcc (Good (M₀ a b)) K ω : ℝ) < b * K} ≤ c₀ a b * Real.exp (-a * K))

lemma countOcc_mono {Ω : Type} {G G' : ℕ → Set Ω} (hGG : ∀ k, G k ⊆ G' k) (K : ℕ) (ω : Ω) :
    countOcc G K ω ≤ countOcc G' K ω := by
  classical
  unfold countOcc
  exact Finset.card_le_card fun k hk => by
    simp only [Finset.mem_filter] at hk ⊢; exact ⟨hk.1, hGG k hk.2⟩

lemma prob_countOcc_mono {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {G G' : ℕ → Set Ω} (hGG : ∀ k, G k ⊆ G' k) (b : ℝ) (K : ℕ) :
    P.real {ω | (countOcc G' K ω : ℝ) < b * K} ≤ P.real {ω | (countOcc G K ω : ℝ) < b * K} :=
  measureReal_mono fun ω hω => by
    have h1 : (countOcc G K ω : ℝ) ≤ countOcc G' K ω := by exact_mod_cast countOcc_mono hGG K ω
    exact lt_of_le_of_lt h1 hω

/-- **LM Lemma 3.1 (1)** (`N = 0`) from `LMAnnulusIterInputQ` (LM l. 723–757). -/
theorem lmLem3_1a_of_inputQ (hIn : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ → s₂ < 1 →
    LMAnnulusIterInputQ s₁ s₂) : LMLem3_1a := by
  intro s₁ s₂ hs₁ hs₁₂ hs₂ a ha b hb0 hb1
  obtain ⟨C, M₁, M₀, c₀, hC, hc₀, H⟩ := hIn s₁ s₂ hs₁ hs₁₂ hs₂
  set β := Real.sqrt b with hβdef
  have hβ0 : 0 < β := Real.sqrt_pos.2 hb0
  have hβ1 : β < 1 := by rw [hβdef, Real.sqrt_lt' one_pos]; linarith
  have hββ : β * β = b := Real.mul_self_sqrt hb0.le
  set M := max (M₀ a β) (M₁ 1)
  set CM := C M
  have hCM : 0 < CM := hC M
  set γ := a / β with hγdef
  have hγ : 0 < γ := div_pos ha hβ0
  set l := (γ + Real.log 2) / (1 - β) with hldef
  have hl : 0 ≤ l := div_nonneg (by have := Real.log_pos one_lt_two; linarith) (by linarith)
  set δ := Real.exp (-γ) * Real.exp (-(l * β)) / 2 with hδdef
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ ≤ 1 / 2 := by
    have h1 : Real.exp (-γ) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have h2 : Real.exp (-(l * β)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    rw [hδdef]; nlinarith [Real.exp_pos (-γ), Real.exp_pos (-(l * β))]
  have hδ4 : δ ^ 4 < 1 := by
    calc δ ^ 4 ≤ (1 / 2) ^ 4 := by gcongr
      _ < 1 := by norm_num
  set p := 1 - δ ^ 4 / (CM + 1) with hpdef
  have hd4 : δ ^ 4 / (CM + 1) < 1 := by
    rw [div_lt_one (by linarith)]; nlinarith
  have hd40 : 0 < δ ^ 4 / (CM + 1) := by positivity
  refine ⟨p, c₀ a β + 1, by rw [hpdef]; linarith, by rw [hpdef]; linarith,
    by linarith [hc₀ a β], ?_⟩
  intro Ω _ P _ h hh r E hE hpE K
  obtain ⟨hr0, hrA, hrs, hEm⟩ := hE
  obtain ⟨Good, hGood, hmono, h38, h310⟩ := H P h hh r hr0 hrA hrs
  have hq : ∀ k, ∀ᵐ ω ∂P, ω ∈ Good M k →
      1 - δ ≤ P[(E k).indicator (fun _ => (1 : ℝ)) | lmFiltration P hh.1 hr0 hrA k] ω := by
    intro k
    filter_upwards [h38 1 one_pos le_rfl M (le_max_right _ _) k (E k) (hEm k)] with ω hω hG
    have h1 := (hω hG).1
    have hPE : p ≤ P.real (E k) := real_ge_of_ofReal_le (hpE k)
    have h2 : CM * (1 - P.real (E k)) ≤ δ ^ 4 := by
      calc CM * (1 - P.real (E k)) ≤ CM * (δ ^ 4 / (CM + 1)) := by
            gcongr; rw [hpdef] at hPE; linarith
        _ ≤ (CM + 1) * (δ ^ 4 / (CM + 1)) := by gcongr; linarith
        _ = δ ^ 4 := by field_simp
    by_contra hlt
    push Not at hlt
    have h3 : δ < 1 - P[(E k).indicator (fun _ => (1 : ℝ)) | lmFiltration P hh.1 hr0 hrA k] ω := by
      linarith
    have := pow_lt_pow_left₀ h3 hδ0.le (by norm_num : (4 : ℕ) ≠ 0)
    linarith
  have hρ : Real.exp (l * β) * (1 - (1 - δ) + (1 - δ) * Real.exp (-l)) ≤ Real.exp (-γ) := by
    have he1 : Real.exp (l * β) * δ = Real.exp (-γ) / 2 := by
      rw [hδdef, mul_div_assoc', ← mul_assoc, mul_comm (Real.exp (l * β)), mul_assoc,
        ← Real.exp_add]
      simp
    have he2 : Real.exp (l * β) * Real.exp (-l) = Real.exp (-γ) / 2 := by
      rw [← Real.exp_add]
      have h1β : (1 - β) ≠ 0 := by linarith
      have hl1 : l * (1 - β) = γ + Real.log 2 := by rw [hldef]; field_simp
      have : l * β + -l = -γ - Real.log 2 := by linear_combination -hl1
      rw [this, Real.exp_sub, Real.exp_log two_pos]
    have hel : 0 ≤ Real.exp (l * β) * Real.exp (-l) := by positivity
    nlinarith [Real.exp_pos (l * β)]
  have hmain := prob_countOcc_lt_le (lmFiltration P hh.1 hr0 hrA) (G := Good M) (E := E)
    (hGood M) (fun k => annSigma_le_lmFiltration hh.1 hr0 hrA (by linarith) hrs k _ (hEm k))
    (q := 1 - δ) (by linarith) (by linarith) hl hβ0.le (by rw [hββ]) hγ.le hρ hq K
  have hγβ : γ * β = a := by rw [hγdef]; field_simp
  rw [hγβ] at hmain
  have h4 := (prob_countOcc_mono (P := P) (G := Good (M₀ a β)) (G' := Good M)
    (fun k => hmono _ _ k (le_max_left _ _)) β K).trans
    (h310 a ha β hβ0 hβ1 K)
  apply measure_le_ofReal_of_real
  calc P.real {ω | (countOcc E K ω : ℝ) < b * K}
      ≤ c₀ a β * Real.exp (-a * K) + Real.exp (-a * K) := by
        have : -(a) * (K : ℝ) = -a * K := rfl
        linarith
    _ = (c₀ a β + 1) * Real.exp (-a * K) := by ring

end LQGMetric.LM
