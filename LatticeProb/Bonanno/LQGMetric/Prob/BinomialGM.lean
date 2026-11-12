/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Prob.BinomialGM at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Prob.BinomialDomination

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# GM Lemma 4.18 and Step 4 of GM Lemma 4.15 (binomial domination + Hoeffding)

Gwynne–Miller, *Existence and uniqueness of the LQG metric*, arXiv:1905.00383,
`uniqueness-final.tex`:

* **Lemma 4.18** (`lem-uncond-to-cond`, lines 2284–2318). The paper's proof: the stopping times
  `τ_j` (the `j`-th `k` with `P[E_k | 𝓕_k] < α`), stochastic domination of
  `Σ_j 1_{E^c_{τ_j}}` by `Bin(m+1, 1-α)`, and Hoeffding's inequality. We follow it through
  `measureReal_binomDom_hoeffding` (iterated conditioning, which replaces the coupling; selection
  events `G k = {P[E_k | 𝓕_k] < α}`, events `A k = E_kᶜ`).

  **The statement as printed is false** for some admissible parameters: with `K = 1`, `m = 1`,
  `α = 0.99`, `δ = 0.98`, trivial `𝓕_k` and independent `E_0, E_1` of probability `0.98`, the
  event of (4.36) is `E_0 ∩ E_1`, of probability `0.9604 > e^{-2·0.98²} ≈ 0.147`. The proof
  loses one index: `{Σ_{k=0}^K 1_{E_k} ≥ K - (1-α-δ)m}` allows `1 + (1-α-δ)m` failures, not
  `< (1-α-δ)m`. We prove two corrected versions:
  `gm_uncond_to_cond` — the paper's bound `e^{-2δ²m}` when the two thresholds use the number
  `n = K+1` of indices instead of `K`; and `gm_uncond_to_cond_K` — the paper's thresholds
  with the bound `exp(-2 (δm - α)² / (m+1))` (for `α ≤ δ m`) which the paper's argument gives
  with `m+1` trials.
* **Step 4 of Lemma 4.15** (lines 2189–2194): `gm_count_lower_tail`, conditional probabilities
  `≥ 1 - s` at every index give `P[#{k < n : A_k} < (1-t) n] ≤ exp(-2 (t-s)² n)` for `s ≤ t`.

The filtration is indexed by `ℕ`; `E_k ∈ 𝓕_{k+1}` is required for every `k < n` (the paper
needs `𝓕_{K+1}` for `E_K` implicitly; take `𝓕_{K+1}` to be the ambient σ-algebra).
-/

open MeasureTheory ProbabilityTheory Real Finset

namespace LQGMetric

variable {Ω : Type*} {m0 : MeasurableSpace Ω} (ℱ : Filtration ℕ m0)

lemma condExp_indicator_compl_ae {μ : Measure Ω} [IsProbabilityMeasure μ] {E : Set Ω}
    (hE : MeasurableSet E) (k : ℕ) :
    μ[Eᶜ.indicator (fun _ => (1 : ℝ)) | ℱ k] =ᵐ[μ]
      fun ω => 1 - μ[E.indicator (fun _ => (1 : ℝ)) | ℱ k] ω := by
  have h : Eᶜ.indicator (fun _ => (1 : ℝ)) = (fun _ => (1 : ℝ)) - E.indicator (fun _ => 1) :=
    Set.indicator_compl E _
  rw [h]
  filter_upwards [condExp_sub (m := ℱ k) (integrable_const (1 : ℝ))
    ((integrable_const (1 : ℝ)).indicator hE)] with ω hω
  rw [hω, Pi.sub_apply, condExp_const (ℱ.le k)]

/-- Core of GM Lemma 4.18: at least `j` of the indices `k < n` have `P[E_k | 𝓕_k] < α` and at
most `(1-α-δ) j` of the `E_k` fail, with probability `≤ e^{-2δ²j}`. -/
theorem gm_uncond_to_cond_core {μ : Measure Ω} [IsProbabilityMeasure μ] (E : ℕ → Set Ω)
    (hE : ∀ k, MeasurableSet[ℱ (k + 1)] (E k)) {α δ : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hδ : 0 ≤ δ) (n j : ℕ) :
    μ.real {ω | (j : ℝ) ≤ n - ∑ k ∈ range n,
          {ω | α ≤ μ[(E k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω}.indicator 1 ω ∧
        (n : ℝ) - ∑ k ∈ range n, (E k).indicator 1 ω ≤ (1 - α - δ) * j} ≤
      Real.exp (-2 * δ ^ 2 * j) := by
  set c : ℕ → Ω → ℝ := fun k => μ[(E k).indicator (fun _ => (1 : ℝ)) | ℱ k]
  set G : ℕ → Set Ω := fun k => {ω | c k ω < α}
  set A : ℕ → Set Ω := fun k => (E k)ᶜ
  have hG : ∀ k, MeasurableSet[ℱ k] (G k) := fun k =>
    measurableSet_lt (stronglyMeasurable_condExp (m := ℱ k)).measurable measurable_const
  have hA : ∀ k, MeasurableSet[ℱ (k + 1)] (A k) := fun k => (hE k).compl
  have hq : ∀ k, ∀ᵐ ω ∂μ, ω ∈ G k → 1 - α ≤ μ[(A k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω := by
    intro k
    filter_upwards [condExp_indicator_compl_ae ℱ (ℱ.le (k + 1) _ (hE k)) (μ := μ) k] with ω hω hG'
    rw [hω]
    have : c k ω < α := hG'
    simp only [c] at this; linarith
  have hmain := measureReal_binomDom_hoeffding ℱ hG hA (by linarith) (by linarith) hδ hq n j
  refine le_trans (measureReal_mono ?_) hmain
  intro ω ⟨h1, h2⟩
  refine ⟨?_, ?_⟩
  · have : binomDomCount G n ω = n - ∑ k ∈ range n,
        {ω | α ≤ μ[(E k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω}.indicator 1 ω := by
      unfold binomDomCount
      rw [eq_sub_iff_add_eq, ← sum_add_distrib]
      rw [show (n : ℝ) = ∑ k ∈ range n, (1 : ℝ) by simp]
      refine sum_congr rfl fun k _ => ?_
      by_cases h : c k ω < α
      · have h' : ¬ α ≤ c k ω := not_le.2 h
        simp [G, Set.indicator, h, h', c] at *
      · have h' : α ≤ c k ω := not_lt.1 h
        simp only [G, Set.indicator, Set.mem_ofPred_eq, h, ite_false, Pi.one_apply]
        simp only [c] at h'; simp [h']
    rw [this]; exact h1
  · have hle : binomDomHits G A n ω ≤ n - ∑ k ∈ range n, (E k).indicator 1 ω := by
      unfold binomDomHits
      rw [le_sub_iff_add_le, ← sum_add_distrib]
      rw [show (n : ℝ) = ∑ k ∈ range n, (1 : ℝ) by simp]
      refine sum_le_sum fun k _ => ?_
      by_cases hk : ω ∈ E k
      · simp [A, Set.indicator, hk]
      · by_cases hg : ω ∈ G k <;> simp [A, Set.indicator, hk, hg]
    linarith

/-- **GM Lemma 4.18, corrected thresholds** (`uniqueness-final.tex` 2284–2290, with `K` replaced
by the number `n = K + 1` of indices in both thresholds): for `α ∈ (0,1)`, `δ ∈ (0,α)`, `m ∈ ℕ`,
`P[Σ_{k<n} 1{P[E_k | 𝓕_k] ≥ α} ≤ n - m, Σ_{k<n} 1_{E_k} ≥ n - (1-α-δ) m] ≤ e^{-2δ²m}`. -/
theorem gm_uncond_to_cond {μ : Measure Ω} [IsProbabilityMeasure μ] (E : ℕ → Set Ω)
    (hE : ∀ k, MeasurableSet[ℱ (k + 1)] (E k)) {α δ : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hδ0 : 0 < δ) (_hδα : δ < α) (n m : ℕ) :
    μ.real {ω | ∑ k ∈ range n,
          {ω | α ≤ μ[(E k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω}.indicator 1 ω ≤ (n : ℝ) - m ∧
        (n : ℝ) - (1 - α - δ) * m ≤ ∑ k ∈ range n, (E k).indicator 1 ω} ≤
      Real.exp (-2 * δ ^ 2 * m) := by
  refine le_trans (measureReal_mono ?_)
    (gm_uncond_to_cond_core ℱ (μ := μ) E hE hα0 hα1 hδ0.le n m)
  intro ω ⟨h1, h2⟩
  exact ⟨by linarith, by linarith⟩

/-- **GM Step 4 of Lemma 4.15** (`uniqueness-final.tex` 2189–2194): if `A_k ∈ 𝓕_{k+1}` and
`P[A_k | 𝓕_k] ≥ 1 - s` a.s. for every `k`, then for `0 ≤ s ≤ t ≤ 1`,
`P[#{k < n : A_k} < (1 - t) n] ≤ exp(-2 (t - s)² n)` (the paper: `s = ε^ω`, `t = ε^θ`, `n = K`). -/
theorem gm_count_lower_tail {μ : Measure Ω} [IsProbabilityMeasure μ] (A : ℕ → Set Ω)
    (hA : ∀ k, MeasurableSet[ℱ (k + 1)] (A k)) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (ht : t ≤ 1)
    (hq : ∀ k, ∀ᵐ ω ∂μ, 1 - s ≤ μ[(A k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω) (n : ℕ) :
    μ.real {ω | ∑ k ∈ range n, (A k).indicator 1 ω < (1 - t) * n} ≤
      Real.exp (-2 * (t - s) ^ 2 * n) := by
  have h := measureReal_binomDom_hoeffding ℱ (G := fun _ => Set.univ) (fun _ => MeasurableSet.univ)
    hA (by linarith) (by linarith) (by linarith : 0 ≤ t - s)
    (fun k => (hq k).mono fun ω h _ => h) n n
  refine le_trans (measureReal_mono ?_) h
  intro ω hω
  simp only [Set.mem_ofPred_eq] at hω
  refine ⟨by simp [binomDomCount], ?_⟩
  have : binomDomHits (fun _ => Set.univ) A n ω = ∑ k ∈ range n, (A k).indicator 1 ω := by
    simp [binomDomHits]
  rw [this]
  have : 1 - s - (t - s) = 1 - t := by ring
  rw [this]; exact hω.le

end LQGMetric
