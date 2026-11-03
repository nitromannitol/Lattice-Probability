/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.L3_1Core at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Prob.BinomialDomination
import LatticeProb.Bonanno.LQGMetric.Blueprint.LMResults

/-!
# LM Lemma 3.1: the counting argument (abstract core)

Source: LM = Gwynne–Miller, *Local metrics of the Gaussian free field*, arXiv:1905.00379,
`literature/src/1905.00379/local-metrics-final.tex`, proof of Lemma 3.1 (`lem-annulus-iterate`),
l. 723–764.

Setting (abstract): a filtration `ℱ` (in LM, `ℱ k = 𝓕_{r_k}`, eq. (3.4)), "good" events
`G k ∈ ℱ k` (LM: `{𝔐^{r_k}_{s' r_k} ≤ M}`) and events `E k ∈ ℱ (k+1)` (LM (3.9)) with
`P[E k | ℱ k] ≥ q` a.s. on `G k` (LM (3.8)). LM l. 744–749 deduce that `𝒩(k_j)` stochastically
dominates `Bin(j, q)` and conclude with the binomial tail (LM Lemma 3.5) and the bound on the
number of good scales (LM Lemma 3.4, (3.10)), l. 757–763:
`P[𝒩(K) < bK] ≤ P[#good ≤ … ] + P[𝒩(k_j) < … ]`.

As in `LQGMetric.Prob.BinomialDomination` (LM S3.1a in `blueprint/LocalMetrics.md`) we do not
build the coupling / the stopping times `k_j`; the exponential-Markov bound for the hits among the
good indices (`measureReal_binomDom_le`) gives the same estimate directly
(`prob_countOcc_lt_le`). The choice of the exponential parameter `λ` replaces the explicit
binomial rate of LM Lemma 3.5 (own elementary bookkeeping, see `DEVIATIONS.md`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Finset

namespace LQGMetric.LM

open Blueprint

variable {Ω : Type} {m0 : MeasurableSpace Ω}

/-- `ℱ` shifted by one: `k ↦ ℱ (k+1)`. -/
def shiftFiltration (ℱ : Filtration ℕ m0) : Filtration ℕ m0 where
  seq i := ℱ (i + 1)
  mono' i j hij := ℱ.mono (by omega)
  le' i := ℱ.le _

/-- `𝒩(K) = #{k ∈ [1,K] : ω ∈ S k}` as a sum over `range K` of the shifted indicators. -/
lemma countOcc_eq_sum (S : ℕ → Set Ω) (K : ℕ) (ω : Ω) :
    (Blueprint.countOcc S K ω : ℝ) = ∑ i ∈ range K, (S (i + 1)).indicator 1 ω := by
  classical
  unfold Blueprint.countOcc
  rw [Finset.natCast_card_filter]
  have hI : Finset.Icc 1 K = Finset.Ico 1 (K + 1) := rfl
  rw [hI, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Set.indicator_apply, add_comm]

lemma binomDomCount_shift_eq (S : ℕ → Set Ω) (K : ℕ) (ω : Ω) :
    binomDomCount (fun i => S (i + 1)) K ω = Blueprint.countOcc S K ω := by
  rw [countOcc_eq_sum]; rfl

lemma binomDomHits_shift_le (G E : ℕ → Set Ω) (K : ℕ) (ω : Ω) :
    binomDomHits (fun i => G (i + 1)) (fun i => E (i + 1)) K ω ≤ Blueprint.countOcc E K ω := by
  rw [countOcc_eq_sum]
  unfold binomDomHits
  refine Finset.sum_le_sum fun i _ => ?_
  exact Set.indicator_le_indicator_of_subset Set.inter_subset_right (fun _ => zero_le_one) ω

/-- `ρ ≤ e^{-γ}`, `βK ≤ j` ⇒ `ρ^j ≤ e^{-γβK}`. -/
lemma pow_le_exp_of_le {ρ γ β : ℝ} (hρ0 : 0 ≤ ρ) (hγ : 0 ≤ γ) (hρ : ρ ≤ Real.exp (-γ))
    {K j : ℕ} (hj : β * K ≤ j) : ρ ^ j ≤ Real.exp (-(γ * β) * K) := by
  calc ρ ^ j ≤ Real.exp (-γ) ^ j := pow_le_pow_left₀ hρ0 hρ j
    _ = Real.exp (-γ * j) := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ Real.exp (-(γ * β) * K) := by
        apply Real.exp_le_exp.2; nlinarith

/-- **Core of LM Lemma 3.1** (l. 744–763). If `G k ∈ ℱ k`, `E k ∈ ℱ (k+1)`, and
`P[E k | ℱ k] ≥ q` a.s. on `G k`, then for `b ≤ αβ` and any `λ ≥ 0` with
`e^{λα}(1 - q + q e^{-λ}) ≤ e^{-γ}`,
`P[𝒩(K) < bK] ≤ P[#{k ∈ [1,K] : G k} < βK] + e^{-γβK}`. -/
theorem prob_countOcc_lt_le {μ : Measure Ω} [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    {G E : ℕ → Set Ω} (hG : ∀ k, MeasurableSet[ℱ k] (G k))
    (hE : ∀ k, MeasurableSet[ℱ (k + 1)] (E k)) {q l α β b γ : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hl : 0 ≤ l) (hα : 0 ≤ α) (hb : b ≤ α * β) (hγ : 0 ≤ γ)
    (hρ : Real.exp (l * α) * (1 - q + q * Real.exp (-l)) ≤ Real.exp (-γ))
    (hq : ∀ k, ∀ᵐ ω ∂μ, ω ∈ G k → q ≤ μ[(E k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω)
    (K : ℕ) :
    μ.real {ω | (Blueprint.countOcc E K ω : ℝ) < b * K} ≤
      μ.real {ω | (Blueprint.countOcc G K ω : ℝ) < β * K} + Real.exp (-(γ * β) * K) := by
  set ℱ' := shiftFiltration ℱ
  set G' : ℕ → Set Ω := fun i => G (i + 1)
  set E' : ℕ → Set Ω := fun i => E (i + 1)
  have hG' : ∀ k, MeasurableSet[ℱ' k] (G' k) := fun k => hG (k + 1)
  have hE' : ∀ k, MeasurableSet[ℱ' (k + 1)] (E' k) := fun k => hE (k + 1)
  have hq' : ∀ k, ∀ᵐ ω ∂μ, ω ∈ G' k →
      q ≤ μ[(E' k).indicator (fun _ => (1 : ℝ)) | ℱ' k] ω := fun k => hq (k + 1)
  set j := ⌈β * K⌉₊
  have hj : β * K ≤ j := Nat.le_ceil _
  have hmain := measureReal_binomDom_le ℱ' hG' hE' hq0 hq1 hl hq' K j (α * j)
  have hsub : {ω | (Blueprint.countOcc E K ω : ℝ) < b * K} ⊆
      {ω | (Blueprint.countOcc G K ω : ℝ) < β * K} ∪
      {ω | (j : ℝ) ≤ binomDomCount G' K ω ∧ binomDomHits G' E' K ω ≤ α * j} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
    by_cases hc : (Blueprint.countOcc G K ω : ℝ) < β * K
    · exact Or.inl hc
    · right
      push_neg at hc
      have hcnt : binomDomCount G' K ω = Blueprint.countOcc G K ω := binomDomCount_shift_eq G K ω
      refine ⟨?_, ?_⟩
      · rw [hcnt]; exact_mod_cast Nat.ceil_le.2 (by exact_mod_cast hc)
      · have h1 := binomDomHits_shift_le G E K ω
        have h2 : b * K ≤ α * j := by
          calc b * K ≤ α * β * K := by gcongr
            _ = α * (β * K) := by ring
            _ ≤ α * j := by gcongr
        linarith
  refine (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans ?_)
  gcongr
  refine hmain.trans ?_
  have hφ0 : 0 ≤ 1 - q + q * Real.exp (-l) := by
    have := Real.exp_pos (-l); nlinarith
  calc Real.exp (l * (α * j)) * (1 - q + q * Real.exp (-l)) ^ j
      = (Real.exp (l * α) * (1 - q + q * Real.exp (-l))) ^ j := by
        rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
    _ ≤ Real.exp (-(γ * β) * K) :=
        pow_le_exp_of_le (mul_nonneg (Real.exp_pos _).le hφ0) hγ hρ hj

end LQGMetric.LM
