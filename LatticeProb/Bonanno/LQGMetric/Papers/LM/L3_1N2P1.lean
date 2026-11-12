/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.L3_1N2P1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_1N2
import LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_1InQ

/-!
# LM Lemma 3.1 (1) with `N = 2`: the counting step from a per-scale input (task P2-LM31N2)

Source: Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), proof of Lemma 3.1, l. 723–757.

LM l. 725–730 obtain (3.8) for events `E_{r_k}` of the `(N+1)`-tuple (3.1) from LM Lemma 3.3,
whose proof (l. 631–637) first removes the metrics by locality ("the metrics … are conditionally
independent from `𝓕_r` given `(h − h_r(0))|_{B_{sr}(0)}`") and then uses the field bound. Here
this is split as follows.

* `LMN2ScaleInput s₁ s₂` (the locality part): a filtration `ℱ` containing the field filtration
  `lmFiltration` (null-augmented `𝓕_{r_k}`, `N = 0`), versions `E'_k` of the events with
  `E'_k ∈ ℱ_{k+1}` ((3.9)), and for every `η ∈ (0,1)` an event `a` of the annulus field
  σ-algebra with `P[aᶜ] η ≤ P[E'_kᶜ]`, `P[a | ℱ_k] = P[a | 𝓕_{r_k}]` and
  `(1 − η) P[a | ℱ_k] ≤ P[E'_k | ℱ_k]` (take `a = {P[E_k | (h − h_{r_k}(0))|_{A_k}] ≥ 1 − η}`).
* `lmLem3_1aN2_of_scale`: from it and the `N = 0` field input `LMAnnulusIterInputQ`
  ((3.8) for field events and (3.10)), the constant choices of LM l. 725–757, exactly as in
  `lmLem3_1a_of_inputQ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory

namespace LQGMetric.LM

open Blueprint

/-- The locality input of LM Lemma 3.1 with `N = 2` at every scale (LM l. 631–637, 731–734). -/
def LMN2ScaleInput (s₁ s₂ : ℝ) : Prop :=
  ∀ (ξ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (D₁ D₂ : Ω → ContMetric) (hh : IsNormalizedWPGFF h P),
    IsXiAdditive2 ξ P h D₁ D₂ → ∀ (r : ℕ → ℝ) (E : ℕ → Set Ω) (hr0 : ∀ k, 0 < r k)
    (hrA : Antitone r), AnnulusIterHypN2 ξ h D₁ D₂ s₁ s₂ r E →
    ∃ (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (E' : ℕ → Set Ω),
      (∀ k, lmFiltration P hh.1 hr0 hrA k ≤ ℱ k) ∧ (∀ k, E k =ᵐ[P] E' k) ∧
      (∀ k, MeasurableSet[ℱ (k + 1)] (E' k)) ∧
      ∀ k (η : ℝ), 0 < η → η < 1 → ∃ a : Set Ω, MeasurableSet[annSigma h s₁ s₂ (r k)] a ∧
        (1 - P.real a) * η ≤ 1 - P.real (E' k) ∧
        P[a.indicator (fun _ => (1 : ℝ)) | ℱ k] =ᵐ[P]
          P[a.indicator (fun _ => (1 : ℝ)) | lmFiltration P hh.1 hr0 hrA k] ∧
        ∀ᵐ ω ∂P, (1 - η) * P[a.indicator (fun _ => (1 : ℝ)) | ℱ k] ω ≤
          P[(E' k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω

lemma countOcc_congr {Ω : Type} {E E' : ℕ → Set Ω} {ω : Ω} (hω : ∀ k, (ω ∈ E k ↔ ω ∈ E' k))
    (K : ℕ) : countOcc E K ω = countOcc E' K ω := by
  classical
  unfold countOcc
  congr 1
  exact Finset.filter_congr fun k _ => hω k

lemma prob_countOcc_congr {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {E E' : ℕ → Set Ω}
    (hEE : ∀ k, E k =ᵐ[P] E' k) (b : ℝ) (K : ℕ) :
    P {ω | (countOcc E K ω : ℝ) < b * K} = P {ω | (countOcc E' K ω : ℝ) < b * K} := by
  refine measure_congr ?_
  have hall : ∀ᵐ ω ∂P, ∀ k, (ω ∈ E k ↔ ω ∈ E' k) := by
    rw [ae_all_iff]; intro k
    filter_upwards [hEE k] with ω hω
    exact Iff.of_eq hω
  filter_upwards [hall] with ω hω
  show ((countOcc E K ω : ℝ) < b * K) = ((countOcc E' K ω : ℝ) < b * K)
  rw [countOcc_congr hω K]

/-- **LM Lemma 3.1 (1)** with `N = 2` from the locality input and the `N = 0` field input
(LM l. 723–757). -/
theorem lmLem3_1aN2_of_scale (hIn : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ → s₂ < 1 →
    LMAnnulusIterInputQ s₁ s₂)
    (hS : ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ → s₂ < 1 → LMN2ScaleInput s₁ s₂) : LMLem3_1aN2 := by
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
  set η := δ / 2 with hηdef
  have hη0 : 0 < η := by positivity
  have hη1 : η < 1 := by linarith
  have hη4 : η ^ 4 < 1 := by
    calc η ^ 4 ≤ (1 / 4) ^ 4 := by gcongr; linarith
      _ < 1 := by norm_num
  set ε := η * (η ^ 4 / (CM + 1)) with hεdef
  have hd40 : 0 < η ^ 4 / (CM + 1) := by positivity
  have hd4 : η ^ 4 / (CM + 1) < 1 := by rw [div_lt_one (by linarith)]; nlinarith
  have hε0 : 0 < ε := by positivity
  have hε1 : ε < 1 := by
    calc ε ≤ 1 * (η ^ 4 / (CM + 1)) := by rw [hεdef]; gcongr
      _ < 1 := by linarith
  set p := 1 - ε with hpdef
  refine ⟨p, c₀ a β + 1, by rw [hpdef]; linarith, by rw [hpdef]; linarith,
    by linarith [hc₀ a β], ?_⟩
  intro ξ Ω _ P _ h D₁ D₂ hh hX r E hE hpE K
  obtain ⟨hr0, hrA, hrs, hEm⟩ := hE
  obtain ⟨Good, hGood, hmono, h38, h310⟩ := H P h hh r hr0 hrA hrs
  obtain ⟨ℱ, E', hLF, hEE, hE'm, hsc⟩ :=
    hS s₁ s₂ hs₁ hs₁₂ hs₂ ξ P h D₁ D₂ hh hX r E hr0 hrA ⟨hr0, hrA, hrs, hEm⟩
  have hq : ∀ k, ∀ᵐ ω ∂P, ω ∈ Good M k →
      1 - δ ≤ P[(E' k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω := by
    intro k
    obtain ⟨A, hA, hPA, hAL, hAE⟩ := hsc k η hη0 hη1
    have hPE : p ≤ P.real (E' k) := by
      rw [← measureReal_congr (hEE k)]; exact real_ge_of_ofReal_le (hpE k)
    have hPA' : 1 - P.real A ≤ η ^ 4 / (CM + 1) := by
      have : (1 - P.real A) * η ≤ η * (η ^ 4 / (CM + 1)) := by
        rw [hpdef] at hPE; linarith
      nlinarith
    filter_upwards [h38 1 one_pos le_rfl M (le_max_right _ _) k A hA, hAL, hAE] with
      ω hω hωL hωE hG
    have h1 := (hω hG).1
    have h2 : CM * (1 - P.real A) < η ^ 4 := by
      calc CM * (1 - P.real A) ≤ CM * (η ^ 4 / (CM + 1)) := by gcongr
        _ < (CM + 1) * (η ^ 4 / (CM + 1)) := by
            gcongr; linarith
        _ = η ^ 4 := by field_simp
    have h3 : 1 - η < P[A.indicator (fun _ => (1 : ℝ)) |
        lmFiltration P hh.1 hr0 hrA k] ω := by
      by_contra hlt
      push Not at hlt
      have h4 : η ≤ 1 - P[A.indicator (fun _ => (1 : ℝ)) | lmFiltration P hh.1 hr0 hrA k] ω := by
        linarith
      have := pow_le_pow_left₀ hη0.le h4 4
      linarith
    rw [← hωL] at h3
    have h5 : (1 - η) * (1 - η) ≤ (1 - η) * P[A.indicator (fun _ => (1 : ℝ)) | ℱ k] ω :=
      mul_le_mul_of_nonneg_left h3.le (by linarith)
    nlinarith
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
  have hmain := prob_countOcc_lt_le ℱ (G := Good M) (E := E')
    (fun k => hLF k _ (hGood M k)) hE'm
    (q := 1 - δ) (by linarith) (by linarith) hl hβ0.le (by rw [hββ]) hγ.le hρ hq K
  have hγβ : γ * β = a := by rw [hγdef]; field_simp
  rw [hγβ] at hmain
  have h4 := (prob_countOcc_mono (P := P) (G := Good (M₀ a β)) (G' := Good M)
    (fun k => hmono _ _ k (le_max_left _ _)) β K).trans
    (h310 a ha β hβ0 hβ1 K)
  rw [prob_countOcc_congr hEE b K]
  apply measure_le_ofReal_of_real
  calc P.real {ω | (countOcc E' K ω : ℝ) < b * K}
      ≤ c₀ a β * Real.exp (-a * K) + Real.exp (-a * K) := by
        have : -(a) * (K : ℝ) = -a * K := rfl
        linarith
    _ = (c₀ a β + 1) * Real.exp (-a * K) := by ring

end LQGMetric.LM
