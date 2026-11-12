/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39Tail at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39Engine
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39Count

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Lemma 3.11: the abstract tail bound

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`
C:1600–1716 (Lemmas 3.10 and 3.11, steps 2–3). Abstract setting: a filtration `𝓕_k`
(CONF: `σ(𝓑^•_{s_k}, h|_{𝓑^•_{s_k}})`), adapted non-increasing counts `n_k = #𝓘_k`, bad events
`Bad_k ∈ 𝓕_{k+1}` (CONF: `#𝓘_k^{**} > ¼ #(𝓘_k ∖ 𝓘_k^*)`) with
`P[A ∩ Bad_k] ≤ C₁ b^{−a} P[A]` for `A ∈ 𝓕_k`, `A ⊆ {n_k ≥ b}` (CONF (3.25) with
`ε_k ≤ 2 n_k^{−1/4}`, `a = α/4`), and on `E` (CONF: `𝓔_𝕣(a)`) every alive step
(`k ≤ K_{N₀} − 1`) at count `≥ N₀` that is not bad halves the count ((3.27)).

`t39_tail`: the probability that `E` occurs and the alive steps with `n_k ≥ N` have
`∑ n_k^{−θ} > M (N/2)^{−θ}/(1 − 2^{−θ})` is at most `∑_j (C₁ 2^{−a(⌊log₂ N⌋ + j)})^M`
(CONF (3.29)–(3.31), with the dyadic-level bookkeeping DV-CONF-T39a).
-/

namespace LQGMetric
namespace CONF

open MeasureTheory Set Finset
open scoped ENNReal

variable {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω)

/-- **CONF Lemma 3.11, abstract form** (C:1690–1716) -/
theorem t39_tail (𝓕 : ℕ → MeasurableSpace Ω) (hmono : Monotone 𝓕) (h𝓕 : ∀ k, 𝓕 k ≤ m0)
    [IsProbabilityMeasure P] (n : ℕ → Ω → ℕ) (hn : ∀ k, Measurable[𝓕 k] (n k))
    (hnmono : ∀ ω k, n (k + 1) ω ≤ n k ω)
    (Bad : ℕ → Set Ω) (hBad : ∀ k, MeasurableSet[𝓕 (k + 1)] (Bad k)) (C₁ a : ℝ)
    (hstep : ∀ k (b : ℕ) (A : Set Ω), 1 ≤ b → MeasurableSet[𝓕 k] A → A ⊆ {ω | b ≤ n k ω} →
      P (A ∩ Bad k) ≤ ENNReal.ofReal (C₁ * (b : ℝ) ^ (-a)) * P A)
    (E : Set Ω) (Alive : ℕ → Ω → Prop) (N₀ : ℕ)
    (hdet : ∀ ω ∈ E, ∀ k, Alive k ω → N₀ ≤ n k ω → ω ∉ Bad k → 2 * n (k + 1) ω ≤ n k ω)
    {θ : ℝ} (hθ : 0 < θ) (N M : ℕ) (hN : 1 ≤ N) (hN₀ : N₀ ≤ N) :
    P {ω | ω ∈ E ∧ ∃ K : ℕ, (∀ k < K, Alive k ω ∧ N ≤ n k ω) ∧
        (M : ℝ) * ((N : ℝ) / 2) ^ (-θ) / (1 - (2 : ℝ) ^ (-θ)) <
          ∑ k ∈ range K, ((n k ω : ℝ) ^ (-θ))} ≤
      ∑' j : ℕ, ENNReal.ofReal (C₁ * ((2 : ℕ) ^ (Nat.log 2 N + j) : ℕ) ^ (-a)) ^ M := by
  classical
  set ℓ₀ := Nat.log 2 N
  have hsub : {ω | ω ∈ E ∧ ∃ K : ℕ, (∀ k < K, Alive k ω ∧ N ≤ n k ω) ∧
        (M : ℝ) * ((N : ℝ) / 2) ^ (-θ) / (1 - (2 : ℝ) ^ (-θ)) <
          ∑ k ∈ range K, ((n k ω : ℝ) ^ (-θ))} ⊆
      ⋃ j : ℕ, t39LevelEvent n Bad (2 ^ (ℓ₀ + j)) M := by
    rintro ω ⟨hE, K, hK, hlt⟩
    by_contra hno
    refine (not_le.2 hlt) (t39_sum_le (fun k => n k ω) K N M hθ hN (fun k hk => (hK k hk).2)
      fun ℓ => ?_)
    rcases lt_or_ge ℓ ℓ₀ with hℓ | hℓ
    · -- below the level of `N` there is no index
      refine (Finset.card_eq_zero.2 ?_).le.trans (Nat.zero_le M)
      refine Finset.filter_eq_empty_iff.2 fun k hk ⟨_, h2⟩ => ?_
      have h1 : 2 * 2 ^ ℓ ≤ 2 ^ ℓ₀ := by
        rw [← pow_succ']; exact Nat.pow_le_pow_right (by norm_num) hℓ
      have h3 : 2 ^ ℓ₀ ≤ N := Nat.pow_log_le_self 2 (show N ≠ 0 by omega)
      have := (hK k (Finset.mem_range.1 hk)).2
      omega
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hℓ
      refine t39_level_card_le (fun k => n k ω) (fun k => ω ∈ Bad k) K _ M (hnmono ω)
        (fun k hk hb => hdet ω hE k (hK k hk).1 (hN₀.trans (hK k hk).2) hb) ?_
      rintro ⟨k₀, h₀, hbad⟩
      refine hno (Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨k₀, ?_⟩⟩)
      exact (mem_t39PeelSet _ _ _ _ _ M).2 ⟨h₀, hbad⟩
  calc _ ≤ P (⋃ j : ℕ, t39LevelEvent n Bad (2 ^ (ℓ₀ + j)) M) := measure_mono hsub
    _ ≤ ∑' j : ℕ, P (t39LevelEvent n Bad (2 ^ (ℓ₀ + j)) M) := measure_iUnion_le _
    _ ≤ _ := by
      gcongr with j
      exact t39_level P 𝓕 hmono h𝓕 n hn Bad hBad _ _
        (fun k A hA hAs => hstep k _ A (Nat.one_le_two_pow) hA hAs) M

end CONF
end LQGMetric
