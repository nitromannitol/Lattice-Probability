/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39G4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39G1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Lemma 3.11 with a uniform constant `b₀`

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`
C:1506 ("a constant `b₀ > 0` depending only on `a`"), C:1716–1722. `t39_tail_exp`
(S3T39Exp) chooses `b₀` after the probability space; Theorem 3.9 (`CONFThm3_9At`) needs `b₀`
before `Ω, P, h, 𝕣, τ`. The proof of `t39_tail_exp` gives `b₀` depending only on
`C₁, a, θ, N₀`; `t39g_tail_exp_unif` is that proof (copied from `t39_tail_exp`) with the
quantifiers in this order, and `t39g_lem311_unif` the uniform form of `t39g_lem311`.
-/

namespace LQGMetric
namespace CONF

open MeasureTheory Set Finset Real
open scoped ENNReal

/-- `t39_tail_exp` with `b₀` depending only on `C₁, a, θ, N₀` -/
theorem t39g_tail_exp_unif {C₁ a θ : ℝ} (hC₁ : 0 ≤ C₁) (ha : 0 < a) (hθ : 0 < θ) (N₀ : ℕ) :
    ∃ b₀ : ℝ, 0 < b₀ ∧ ∀ {Ω : Type} {m0 : MeasurableSpace Ω} (P : Measure Ω)
    (𝓕 : ℕ → MeasurableSpace Ω), Monotone 𝓕 → (∀ k, 𝓕 k ≤ m0) → ∀ [IsProbabilityMeasure P]
    (n : ℕ → Ω → ℕ), (∀ k, Measurable[𝓕 k] (n k)) → (∀ ω k, n (k + 1) ω ≤ n k ω) →
    ∀ (Bad : ℕ → Set Ω), (∀ k, MeasurableSet[𝓕 (k + 1)] (Bad k)) →
    (∀ k (b : ℕ) (A : Set Ω), 1 ≤ b → MeasurableSet[𝓕 k] A → A ⊆ {ω | b ≤ n k ω} →
      P (A ∩ Bad k) ≤ ENNReal.ofReal (C₁ * (b : ℝ) ^ (-a)) * P A) →
    ∀ (E : Set Ω) (Alive : ℕ → Ω → Prop),
    (∀ ω ∈ E, ∀ k, Alive k ω → N₀ ≤ n k ω → ω ∉ Bad k → 2 * n (k + 1) ω ≤ n k ω) →
    ∀ N : ℕ, 1 ≤ N →
      P {ω | ω ∈ E ∧ ∃ K : ℕ, (∀ k < K, Alive k ω ∧ N ≤ n k ω) ∧
        (2 : ℝ) ^ (θ + 1) / (1 - (2 : ℝ) ^ (-θ)) * (N : ℝ) ^ (-(θ / 2)) <
          ∑ k ∈ range K, ((n k ω : ℝ) ^ (-θ))} ≤
        ENNReal.ofReal (b₀ * exp (-(N : ℝ) ^ (θ / 2))) := by
  have htend : Filter.Tendsto (fun N : ℕ => C₁ * ((N : ℝ) / 2) ^ (-a)) Filter.atTop (nhds 0) := by
    have h1 := (tendsto_rpow_neg_atTop ha).comp
      ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_div_const (by norm_num : (0 : ℝ) < 2))
    simpa using h1.const_mul C₁
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1
    (htend.eventually (ge_mem_nhds (Real.exp_pos (-1))))
  set N₂ := max N₁ (max N₀ 1)
  have hra : 0 < 1 - (2 : ℝ) ^ (-a) := by
    have := Real.rpow_lt_one_of_one_lt_of_neg (x := 2) (by norm_num) (by linarith : -a < 0)
    linarith
  set b₀ := max (exp ((N₂ : ℝ) ^ (θ / 2))) (1 / (1 - (2 : ℝ) ^ (-a)))
  refine ⟨b₀, lt_max_of_lt_left (Real.exp_pos _), ?_⟩
  intro Ω m0 P 𝓕 hmono h𝓕 _ n hn hnmono Bad hBad hstep E Alive hdet N hN
  rcases lt_or_ge N N₂ with hlt | hge
  · refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have hle : (N : ℝ) ^ (θ / 2) ≤ (N₂ : ℝ) ^ (θ / 2) :=
      Real.rpow_le_rpow (by positivity) (by exact_mod_cast hlt.le) (by linarith)
    calc (1 : ℝ) = exp ((N₂ : ℝ) ^ (θ / 2)) * exp (-(N₂ : ℝ) ^ (θ / 2)) := by
          rw [← Real.exp_add]; simp
      _ ≤ b₀ * exp (-(N : ℝ) ^ (θ / 2)) := by
          gcongr
          · exact le_max_left _ _
  · set M := ⌈(N : ℝ) ^ (θ / 2)⌉₊
    have hN₁N : N₁ ≤ N := (le_max_left _ _).trans hge
    have hN₀N : N₀ ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hge
    have hpow1 : 1 ≤ (N : ℝ) ^ (θ / 2) :=
      Real.one_le_rpow (by exact_mod_cast hN) (by linarith)
    have hM1 : 1 ≤ M := Nat.one_le_iff_ne_zero.2 (by
      intro h0; have := Nat.ceil_eq_zero.1 h0; linarith)
    have hMge : (N : ℝ) ^ (θ / 2) ≤ M := Nat.le_ceil _
    calc _ ≤ P {ω | ω ∈ E ∧ ∃ K : ℕ, (∀ k < K, Alive k ω ∧ N ≤ n k ω) ∧
          (M : ℝ) * ((N : ℝ) / 2) ^ (-θ) / (1 - (2 : ℝ) ^ (-θ)) <
            ∑ k ∈ range K, ((n k ω : ℝ) ^ (-θ))} := by
          refine measure_mono fun ω ⟨hE, K, hK, hlt⟩ => ⟨hE, K, hK, ?_⟩
          exact (t39_threshold_le hθ N hN).trans_lt hlt
      _ ≤ ∑' j : ℕ, ENNReal.ofReal (C₁ * ((2 : ℕ) ^ (Nat.log 2 N + j) : ℕ) ^ (-a)) ^ M :=
          t39_tail P 𝓕 hmono h𝓕 n hn hnmono Bad hBad C₁ a hstep E Alive N₀ hdet hθ N M hN hN₀N
      _ ≤ ENNReal.ofReal (exp (-(M : ℝ)) / (1 - (2 : ℝ) ^ (-a))) :=
          t39_levels_tsum_le hC₁ ha N M hN hM1 (hN₁ N hN₁N)
      _ ≤ ENNReal.ofReal (b₀ * exp (-(N : ℝ) ^ (θ / 2))) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [div_eq_mul_inv, mul_comm]
          gcongr
          · rw [← one_div]; exact le_max_right _ _

/-- **CONF Lemma 3.11 + first step of the proof of Theorem 3.9, uniform `b₀`** (C:1660–1736):
`b₀` depends only on `C₁, a, θ, N₀` -/
theorem t39g_lem311_unif {C₁ a θ : ℝ} (hC₁ : 0 ≤ C₁) (ha : 0 < a) (hθ : 0 < θ) (N₀ : ℕ) :
    ∃ b₀ : ℝ, 0 < b₀ ∧ ∀ {Ω : Type} {m0 : MeasurableSpace Ω} (P : Measure Ω)
    (𝓕 : ℕ → MeasurableSpace Ω), Monotone 𝓕 → (∀ k, 𝓕 k ≤ m0) → ∀ [IsProbabilityMeasure P]
    (n : ℕ → Ω → ℕ), (∀ k, Measurable[𝓕 k] (n k)) → (∀ ω k, n (k + 1) ω ≤ n k ω) →
    ∀ (Bad : ℕ → Set Ω), (∀ k, MeasurableSet[𝓕 (k + 1)] (Bad k)) →
    (∀ k (b : ℕ) (A : Set Ω), 1 ≤ b → MeasurableSet[𝓕 k] A → A ⊆ {ω | b ≤ n k ω} →
      P (A ∩ Bad k) ≤ ENNReal.ofReal (C₁ * (b : ℝ) ^ (-a)) * P A) →
    ∀ (E : Set Ω) (Alive : ℕ → Ω → Prop),
    (∀ ω ∈ E, ∀ k, Alive k ω → N₀ ≤ n k ω → ω ∉ Bad k → 2 * n (k + 1) ω ≤ n k ω) →
    ∀ (s : ℕ → Ω → ℝ) (τ S : Ω → ℝ), (∀ ω, s 0 ω = τ ω) → ∀ {C : ℝ}, 0 ≤ C →
    (∀ ω ∈ E, 0 ≤ S ω) →
    (∀ ω ∈ E, ∀ k, Alive k ω → N₀ ≤ n k ω →
      s (k + 1) ω ≤ s k ω + C * (n k ω : ℝ) ^ (-θ) * S ω) →
    ∀ N : ℕ, 1 ≤ N → N₀ ≤ N →
      P {ω | ω ∈ E ∧ ¬ ∃ K : ℕ, s K ω ≤ τ ω + C * ((2 : ℝ) ^ (θ + 1) / (1 - (2 : ℝ) ^ (-θ))) *
          (N : ℝ) ^ (-(θ / 2)) * S ω ∧ (¬ Alive K ω ∨ n K ω < N)} ≤
        ENNReal.ofReal (b₀ * exp (-(N : ℝ) ^ (θ / 2))) := by
  obtain ⟨b₀, hb₀, hT⟩ := t39g_tail_exp_unif hC₁ ha hθ N₀
  refine ⟨b₀, hb₀, ?_⟩
  intro Ω m0 P 𝓕 hmono h𝓕 _ n hn hnmono Bad hBad hstep E Alive hdet s τ S hs0 C hC hS hstep1
    N hN hN₀
  exact (measure_mono (t39g_lem311_subset n hnmono E Alive N₀ hθ s τ S hs0 hC hS hstep1 N hN
    hN₀)).trans (hT P 𝓕 hmono h𝓕 n hn hnmono Bad hBad hstep E Alive hdet N hN)

end CONF
end LQGMetric
