/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39G1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39Exp
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3T39Markov

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Lemmas 3.10–3.11, the abstract layer between the engine and the geometry

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`.

* `t39g_inter_compl_le_local`: CONF (3.24) used on an `𝓕`-event `A` on which the random bound
  `1 − C₀ε_k^α` is at least `1 − e` (C:1625–1628; here `ε_k` is random, `𝓕_k`-measurable).
* `t39g_hstep`: the `hstep` input of `t39_tail_exp` from the per-arc bound (3.24) with
  `ε_k ≤ 2n_k^{−1/4}` ((3.19), C:1563): on `A ⊆ {n_k ≥ b}`,
  `P[A ∩ {#Act < 4#(Act ∖ G)}] ≤ 4C₀2^α b^{−α/4} P[A]` (proof of Lemma 3.10, C:1625–1632,
  conditional Markov (3.25) via `t39_condMarkov`).
* `t39g_count_half`: (3.23) + (3.29): if `#𝓘_k^* ≤ n_k/4`, the killed arcs `I ∈ Act ∩ G_I` and the
  dead arcs stay dead, and `#𝓘_k^{**} ≤ #Act/4`, then `n_{k+1} ≤ n_k/2` (C:1640–1645).
* `t39g_lem311`: CONF Lemma 3.11 together with the first lines of the proof of Theorem 3.9
  (C:1660–1736): with the Step 1 bound `s_{k+1} ≤ s_k + C n_k^{−θ} S` (C:1676–1689, (3.32)),
  outside an event of probability `≤ b₀e^{−N^{θ/2}}`, some `K` (CONF's `K_N`, (3.20)) has
  `s_K ≤ τ + C c_θ N^{−θ/2} S` and (`K` not alive or `n_K < N`).
-/

namespace LQGMetric
namespace CONF

open MeasureTheory Set Finset Real
open scoped ENNReal

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- a conditional lower bound `P[G | 𝓕] ≥ 1 − e` on an `𝓕`-event `A` gives `P[A ∩ Gᶜ] ≤ e P[A]` -/
theorem t39g_inter_compl_le_local {μ : Measure Ω} [IsProbabilityMeasure μ]
    {F : MeasurableSpace Ω} (hF : F ≤ m0) {G : Set Ω} (hGm : MeasurableSet[m0] G) {e : ℝ}
    {A : Set Ω} (hA : MeasurableSet[F] A)
    (h : ∀ᵐ x ∂μ, x ∈ A → 1 - e ≤ μ[G.indicator (fun _ => (1 : ℝ)) | F] x) :
    μ (A ∩ Gᶜ) ≤ ENNReal.ofReal e * μ A := by
  have hAm : MeasurableSet[m0] A := hF _ hA
  have hint : Integrable (G.indicator fun _ => (1 : ℝ)) μ := (integrable_const 1).indicator hGm
  have h1 : ∫ x in A, (μ[G.indicator (fun _ => (1 : ℝ)) | F]) x ∂μ = μ.real (A ∩ G) := by
    rw [setIntegral_condExp hF hint hA, setIntegral_indicator hGm, setIntegral_const,
      smul_eq_mul, mul_one]
  have h2 : (1 - e) * μ.real A ≤ ∫ x in A, (μ[G.indicator (fun _ => (1 : ℝ)) | F]) x ∂μ := by
    calc (1 - e) * μ.real A = ∫ _ in A, (1 - e) ∂μ := by rw [setIntegral_const, smul_eq_mul,
          mul_comm]
      _ ≤ _ := setIntegral_mono_ae_restrict integrableOn_const integrable_condExp.integrableOn
          ((ae_restrict_iff' hAm).2 h)
  have h3 := measureReal_sdiff_add_inter (μ := μ) (s := A) hGm
  have h4 : μ.real (A \ G) ≤ e * μ.real A := by linarith
  rw [← Set.sdiff_eq, ← ofReal_measureReal (μ := μ) (s := A \ G),
    ← ofReal_measureReal (μ := μ) (s := A)]
  rcases le_or_gt 0 e with he0 | he0
  · rw [← ENNReal.ofReal_mul he0]; exact ENNReal.ofReal_le_ofReal h4
  · have : μ.real (A \ G) ≤ 0 :=
      h4.trans (mul_nonpos_of_nonpos_of_nonneg he0.le measureReal_nonneg)
    rw [ENNReal.ofReal_of_nonpos this]; exact zero_le

/-- `ε ≤ 2n^{−1/4}`, `n ≥ b ≥ 1` give `C₀ε^α ≤ C₀2^α b^{−α/4}` -/
theorem t39g_eps_pow_le {C₀ α ε : ℝ} (hC₀ : 0 ≤ C₀) (hα : 0 < α) (hε0 : 0 ≤ ε) {n b : ℕ}
    (hb : 1 ≤ b) (hbn : b ≤ n) (hεn : ε ≤ 2 * (n : ℝ) ^ (-(1 / 4 : ℝ))) :
    C₀ * ε ^ α ≤ C₀ * 2 ^ α * (b : ℝ) ^ (-(α / 4)) := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have hnb : (n : ℝ) ^ (-(1 / 4 : ℝ)) ≤ (b : ℝ) ^ (-(1 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hb0 (by exact_mod_cast hbn) (by norm_num)
  have h1 : ε ^ α ≤ (2 * (b : ℝ) ^ (-(1 / 4 : ℝ))) ^ α :=
    Real.rpow_le_rpow hε0 (hεn.trans (by linarith)) hα.le
  have h2 : (2 * (b : ℝ) ^ (-(1 / 4 : ℝ))) ^ α = 2 ^ α * (b : ℝ) ^ (-(α / 4)) := by
    rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hb0.le]
    congr 2; ring
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (h1.trans h2.le) hC₀

/-- **CONF (3.25) with a random `ε_k`** (proof of Lemma 3.10, C:1625–1632): the `hstep` input of
`t39_tail_exp`, with `C₁ = 4C₀2^α` and kill exponent `α/4` -/
theorem t39g_hstep (P : Measure Ω) [IsProbabilityMeasure P] (F : MeasurableSpace Ω) (hF : F ≤ m0)
    {ι : Type*} (s : Finset ι) (Act G : ι → Set Ω) (hAct : ∀ i, MeasurableSet[F] (Act i))
    (hG : ∀ i, MeasurableSet[m0] (G i)) (nk : Ω → ℕ) (ε : Ω → ℝ) {C₀ α : ℝ} (hC₀ : 0 ≤ C₀)
    (hα : 0 < α) (hε0 : ∀ ω, 0 ≤ ε ω)
    (hεn : ∀ ω, 1 ≤ nk ω → ε ω ≤ 2 * (nk ω : ℝ) ^ (-(1 / 4 : ℝ)))
    (hcond : ∀ i, ∀ᵐ ω ∂P, ω ∈ Act i →
      1 - C₀ * ε ω ^ α ≤ P[(G i).indicator (fun _ => (1 : ℝ)) | F] ω)
    (b : ℕ) (hb : 1 ≤ b) (A : Set Ω) (hA : MeasurableSet[F] A) (hAb : A ⊆ {ω | b ≤ nk ω}) :
    P (A ∩ {ω | t39Count s Act ω < 4 * t39Count s (fun i => Act i ∩ (G i)ᶜ) ω}) ≤
      ENNReal.ofReal (4 * C₀ * 2 ^ α * (b : ℝ) ^ (-(α / 4))) * P A := by
  set e := C₀ * 2 ^ α * (b : ℝ) ^ (-(α / 4))
  set Act' : ι → Set Ω := fun i => A ∩ Act i
  have hAct' : ∀ i, MeasurableSet[F] (Act' i) := fun i => hA.inter (hAct i)
  have hq : ∀ i (A' : Set Ω), MeasurableSet[F] A' →
      P (A' ∩ Act' i ∩ (G i)ᶜ) ≤ ENNReal.ofReal e * P (A' ∩ Act' i) := by
    intro i A' hA'
    refine t39g_inter_compl_le_local hF (hG i) (hA'.inter (hAct' i)) ?_
    filter_upwards [hcond i] with ω hω hωA
    have hωA2 : ω ∈ A := hωA.2.1
    have := t39g_eps_pow_le hC₀ hα (hε0 ω) hb (hAb hωA2) (hεn ω (hb.trans (hAb hωA2)))
    linarith [hω hωA.2.2]
  have hM := t39_condMarkov P F hF s Act' G hAct' hG (ENNReal.ofReal e) hq A hA
  have hsub : A ∩ {ω | t39Count s Act ω < 4 * t39Count s (fun i => Act i ∩ (G i)ᶜ) ω} ⊆
      A ∩ {ω | t39Count s Act' ω < 4 * t39Count s (fun i => Act' i ∩ (G i)ᶜ) ω} := by
    rintro ω ⟨hωA, hω⟩
    refine ⟨hωA, ?_⟩
    have e1 : t39Count s Act' ω = t39Count s Act ω := by
      unfold t39Count
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : ω ∈ Act i <;> by_cases hg : ω ∈ G i <;> simp [Act', Set.indicator, hωA, hi, hg]
    have e2 : t39Count s (fun i => Act' i ∩ (G i)ᶜ) ω =
        t39Count s (fun i => Act i ∩ (G i)ᶜ) ω := by
      unfold t39Count
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : ω ∈ Act i <;> by_cases hg : ω ∈ G i <;> simp [Act', Set.indicator, hωA, hi, hg]
    show t39Count s Act' ω < 4 * t39Count s (fun i => Act' i ∩ (G i)ᶜ) ω
    rw [e1, e2]; exact hω
  refine (measure_mono hsub).trans (hM.trans (le_of_eq ?_))
  rw [show 4 * C₀ * 2 ^ α * (b : ℝ) ^ (-(α / 4)) = 4 * e by simp only [e]; ring]
  conv_rhs => rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_ofNat]

open Classical in
/-- **(3.23) + (3.29)** (C:1640–1645), counting at one `ω`: the arcs alive at step `k+1` are
alive at step `k` and not killed (`Act ∩ G`), `Act` ⊆ alive, `4#(alive ∖ Act) ≤ n_k` ((3.21′)),
and the step is not bad; then `2n_{k+1} ≤ n_k`. -/
theorem t39g_count_half {ι : Type*} [DecidableEq ι] (s : Finset ι) (Al Al' Act G : ι → Set Ω)
    (ω : Ω) (hAct : ∀ i ∈ s, ω ∈ Act i → ω ∈ Al i)
    (hnext : ∀ i ∈ s, ω ∈ Al' i → ω ∈ Al i ∧ ¬ (ω ∈ Act i ∧ ω ∈ G i))
    (hstar : 4 * (s.filter fun i => ω ∈ Al i ∧ ω ∉ Act i).card ≤
      (s.filter fun i => ω ∈ Al i).card)
    (hnb : ¬ (t39Count s Act ω < 4 * t39Count s (fun i => Act i ∩ (G i)ᶜ) ω)) :
    2 * (s.filter fun i => ω ∈ Al' i).card ≤ (s.filter fun i => ω ∈ Al i).card := by
  classical
  rw [not_lt, t39Count_eq_card, t39Count_eq_card] at hnb
  have hnb' : 4 * (s.filter fun i => ω ∈ Act i ∩ (G i)ᶜ).card ≤
      (s.filter fun i => ω ∈ Act i).card := by exact_mod_cast hnb
  have hA : (s.filter fun i => ω ∈ Act i).card ≤ (s.filter fun i => ω ∈ Al i).card :=
    Finset.card_le_card fun i hi => by
      rw [Finset.mem_filter] at hi ⊢; exact ⟨hi.1, hAct i hi.1 hi.2⟩
  have hU : (s.filter fun i => ω ∈ Al' i) ⊆ (s.filter fun i => ω ∈ Al i ∧ ω ∉ Act i) ∪
      (s.filter fun i => ω ∈ Act i ∩ (G i)ᶜ) := by
    intro i hi
    rw [Finset.mem_filter] at hi
    obtain ⟨hal, hk⟩ := hnext i hi.1 hi.2
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_cases ha : ω ∈ Act i
    · exact Or.inr ⟨hi.1, ha, fun hg => hk ⟨ha, hg⟩⟩
    · exact Or.inl ⟨hi.1, hal, ha⟩
  have := (Finset.card_le_card hU).trans (Finset.card_union_le _ _)
  omega

/-- telescoping of the Step 1 bound (C:1689–1692, (3.32)) -/
theorem t39g_telescope (s : ℕ → ℝ) (f : ℕ → ℝ) (K : ℕ) (h : ∀ k < K, s (k + 1) ≤ s k + f k) :
    s K ≤ s 0 + ∑ k ∈ range K, f k := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ]
    have := ih fun k hk => h k (Nat.lt_succ_of_lt hk)
    linarith [h K (Nat.lt_succ_self K)]

/-- **CONF Lemma 3.11 + first step of the proof of Theorem 3.9** (C:1660–1736), abstract form: in
the setting of `t39_tail_exp`, with radii `s_k` (`s_0 = τ`) obeying the Step 1 bound
`s_{k+1} ≤ s_k + C n_k^{−θ} S` on `E` at alive steps with `n_k ≥ N₀` (C:1676–1689), outside an
event of probability `≤ b₀e^{−N^{θ/2}}` there is a step `K` (CONF's `K_N`, (3.20)) with
`s_K ≤ τ + C c_θ N^{−θ/2} S` at which the iteration has stopped (not alive, or `n_K < N`). -/
theorem t39g_lem311_subset (n : ℕ → Ω → ℕ) (hnmono : ∀ ω k, n (k + 1) ω ≤ n k ω)
    (E : Set Ω) (Alive : ℕ → Ω → Prop) (N₀ : ℕ)
    {θ : ℝ} (hθ : 0 < θ) (s : ℕ → Ω → ℝ) (τ S : Ω → ℝ) (hs0 : ∀ ω, s 0 ω = τ ω) {C : ℝ}
    (hC : 0 ≤ C) (hS : ∀ ω ∈ E, 0 ≤ S ω)
    (hstep1 : ∀ ω ∈ E, ∀ k, Alive k ω → N₀ ≤ n k ω →
      s (k + 1) ω ≤ s k ω + C * (n k ω : ℝ) ^ (-θ) * S ω) (N : ℕ) (hN : 1 ≤ N) (hN₀ : N₀ ≤ N) :
    {ω | ω ∈ E ∧ ¬ ∃ K : ℕ, s K ω ≤ τ ω + C * ((2 : ℝ) ^ (θ + 1) / (1 - (2 : ℝ) ^ (-θ))) *
          (N : ℝ) ^ (-(θ / 2)) * S ω ∧ (¬ Alive K ω ∨ n K ω < N)} ⊆
      {ω | ω ∈ E ∧ ∃ K : ℕ, (∀ k < K, Alive k ω ∧ N ≤ n k ω) ∧
        (2 : ℝ) ^ (θ + 1) / (1 - (2 : ℝ) ^ (-θ)) * (N : ℝ) ^ (-(θ / 2)) <
          ∑ k ∈ range K, ((n k ω : ℝ) ^ (-θ))} := by
  classical
  set cθ := (2 : ℝ) ^ (θ + 1) / (1 - (2 : ℝ) ^ (-θ))
  rintro ω ⟨hE, hno⟩
  refine ⟨hE, ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  by_cases hex : ∃ K, ¬ Alive K ω ∨ n K ω < N
  · set K := Nat.find hex
    have hmin : ∀ k < K, Alive k ω ∧ N ≤ n k ω := fun k hk => by
      have := Nat.find_min hex hk
      push Not at this; exact this
    refine ⟨K, hmin, ?_⟩
    by_contra hle
    push Not at hle
    apply hno
    refine ⟨K, ?_, Nat.find_spec hex⟩
    have htel := t39g_telescope (fun k => s k ω) (fun k => C * (n k ω : ℝ) ^ (-θ) * S ω) K
      fun k hk => hstep1 ω hE k (hmin k hk).1 (hN₀.trans (hmin k hk).2)
    simp only [hs0] at htel
    have hsum : ∑ k ∈ range K, C * (n k ω : ℝ) ^ (-θ) * S ω =
        C * (∑ k ∈ range K, (n k ω : ℝ) ^ (-θ)) * S ω := by
      rw [Finset.mul_sum, Finset.sum_mul]
    rw [hsum] at htel
    have hCS : 0 ≤ C * S ω := mul_nonneg hC (hS ω hE)
    have := mul_le_mul_of_nonneg_left hle hCS
    nlinarith
  · push Not at hex
    have hn00 : N ≤ n 0 ω := (hex 0).2
    have hpos : (0 : ℝ) < (n 0 ω : ℝ) ^ (-θ) :=
      Real.rpow_pos_of_pos (by exact_mod_cast (hN.trans hn00)) _
    obtain ⟨K, hK⟩ := exists_nat_gt (cθ * (N : ℝ) ^ (-(θ / 2)) / (n 0 ω : ℝ) ^ (-θ))
    refine ⟨K, fun k _ => hex k, ?_⟩
    have hlow : ∀ k ∈ range K, (n 0 ω : ℝ) ^ (-θ) ≤ (n k ω : ℝ) ^ (-θ) := fun k _ =>
      Real.rpow_le_rpow_of_nonpos (by exact_mod_cast (hN.trans (hex k).2))
        (by exact_mod_cast (antitone_nat_of_succ_le (f := fun j => n j ω)
          (fun j => hnmono ω j)) (Nat.zero_le k))
        (by linarith)
    have h1 := Finset.sum_le_sum hlow
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
    rw [div_lt_iff₀ hpos] at hK
    linarith

end CONF
end LQGMetric
