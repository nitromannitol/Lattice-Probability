/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.IterateCount at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Prob.BinomialGM

/-!
# GM Lemma 4.21 and Proposition 4.17: the probabilistic core

Source: GM = Gwynne–Miller, *Existence and uniqueness of the LQG metric*, arXiv:1905.00383,
`literature/src/1905.00383/uniqueness-final.tex`, §4.5:

* **Lemma 4.21** (`lem-nomax-cond`, l. 2361–2398): Lemma 4.18 with `E_k = {𝒵^E_k ≠ ∅} ∩ F_k`,
  `α = 1/2`, `δ = 1/4`, combined with Proposition 4.12 (`#{k : 𝒵^E_k ≠ ∅}` large on `ℰ_𝕣`), the
  inclusion `ℰ_𝕣 ⊆ ⋂_k F_k` (Lemma 4.19) and Lemma 4.7 (`P[𝒵^𝔈_k ≠ ∅ | 𝓕_k] ≥
  κ P[𝒵^E_k ≠ ∅ | 𝓕_k] − e` with `κ = ε^{2ν+o(1)}`, `e = o^∞_ε(ε)`).
* **Proposition 4.17** (`prop-nomax-quant`, proof l. 2404–2433): Lemma 4.18 with
  `E'_k = {𝒵^𝔈_k = ∅} ∩ F_k`, and again `ℰ_𝕣 ⊆ ⋂_k F_k`.

`gm_P4_17_core` is the combination of these two proofs for abstract events: `F k` (GM's `F_k`),
`ZE k` (`{𝒵^E_k ≠ ∅}`), `ZF k` (`{𝒵^𝔈_k ≠ ∅}`), `Reg` (`ℰ_𝕣`), a filtration `ℱ` (GM (4.9)) and
`n = K + 1` indices. The hypotheses are exactly the inputs the paper uses: the measurability of
Lemma 4.20 (and `F_k ∈ 𝓕_{k+1}` from Lemma 4.19), `ℰ_𝕣 ⊆ F_k` (Lemma 4.19), the count bound of
Prop. 4.12, and Lemma 4.7 at each `k`.

Deviations from the paper's arithmetic (proposed DEVIATIONS entry DV-M2K-1): Lemma 4.18 is used in
its corrected form `gm_uncond_to_cond` (D29: thresholds with `n = K+1`); in the second application
we take `α = 1 − p/2`, `δ = p/4` with `p = κ/2 − e` (GM: `α = 1 − ε^{2ν+ζ/2}`,
`δ = ε^{2ν+ζ/2}/2`), so that `P[E'_k | 𝓕_k] ≤ 1 − p < α` is strict as Lemma 4.18 requires, and
`m = n − m₁` in place of `⌊(1 − 4ε^θ)K⌋`. The conclusion is
`#{k : 𝒵^𝔈_k ≠ ∅} > (p/4)(n − m₁)` on `ℰ_𝕣` outside an event of probability
`δ₁ + e^{−m₁/8} + n δ₂ + e^{−p²(n−m₁)/8}`; the rate lemma turns this into GM's `ε^{2ν+ζ}K`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Finset

namespace LQGMetric.GM

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

open scoped Classical in
/-- the indicator sum is the number of indices -/
theorem gm_sum_indicator_eq_card (A : ℕ → Set Ω) (n : ℕ) (ω : Ω) :
    ∑ k ∈ range n, (A k).indicator (1 : Ω → ℝ) ω =
      (((range n).filter (fun k => ω ∈ A k)).card : ℝ) := by
  rw [Finset.card_filter]; push_cast
  refine sum_congr rfl fun k _ => ?_
  by_cases h : ω ∈ A k <;> simp [Set.indicator_apply, h]

/-- the indicator sum is at most the number of indices -/
theorem gm_sum_indicator_le (A : ℕ → Set Ω) (n : ℕ) (ω : Ω) :
    ∑ k ∈ range n, (A k).indicator (1 : Ω → ℝ) ω ≤ n := by
  calc ∑ k ∈ range n, (A k).indicator (1 : Ω → ℝ) ω ≤ ∑ _k ∈ range n, (1 : ℝ) :=
        sum_le_sum fun k _ => by
          by_cases h : ω ∈ A k <;> simp [Set.indicator_apply, h]
    _ = n := by simp

/-- **GM Lemma 4.21 + Proposition 4.17, probabilistic core** (l. 2361–2433). -/
theorem gm_P4_17_core (ℱ : Filtration ℕ m0) {μ : Measure Ω} [IsProbabilityMeasure μ]
    (n m₁ : ℕ) (Reg : Set Ω) (F ZE ZF : ℕ → Set Ω)
    (hF : ∀ k, MeasurableSet[ℱ (k + 1)] (F k))
    (hZE : ∀ k, MeasurableSet[ℱ (k + 1)] (ZE k ∩ F k))
    (hZF : ∀ k, MeasurableSet[ℱ (k + 1)] (ZF k ∩ F k))
    (hZEm : ∀ k, MeasurableSet (ZE k)) (hZFm : ∀ k, MeasurableSet (ZF k))
    (hReg : ∀ k < n, Reg ⊆ F k)
    {δ₁ δ₂ κ e : ℝ} (hκ : 0 ≤ κ) (hp : 0 < κ / 2 - e) (hp1 : κ / 2 - e ≤ 1)
    (h412 : μ.real (Reg ∩ {ω | ∑ k ∈ range n, (ZE k).indicator 1 ω < (n : ℝ) - m₁ / 4}) ≤ δ₁)
    (h47 : ∀ k < n, μ.real {ω | ω ∈ Reg ∧ μ[(ZF k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω <
        κ * μ[(ZE k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω - e} ≤ δ₂) :
    μ.real (Reg ∩ {ω | ∑ k ∈ range n, (ZF k).indicator 1 ω ≤
        (κ / 2 - e) / 4 * ((n - m₁ : ℕ) : ℝ)}) ≤
      δ₁ + Real.exp (-2 * (1 / 4) ^ 2 * m₁) + n * δ₂ +
        Real.exp (-2 * ((κ / 2 - e) / 4) ^ 2 * ((n - m₁ : ℕ) : ℝ)) := by
  set p := κ / 2 - e with hpdef
  set E : ℕ → Set Ω := fun k => ZE k ∩ F k
  set E' : ℕ → Set Ω := fun k => (ZF k)ᶜ ∩ F k
  set j : ℕ := n - m₁
  have hE' : ∀ k, MeasurableSet[ℱ (k + 1)] (E' k) := by
    intro k
    have : E' k = F k \ (ZF k ∩ F k) := by
      ext ω; simp only [E', Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_diff]; tauto
    rw [this]; exact (hF k).diff (hZF k)
  -- the four exceptional events and the null set
  set A1 := Reg ∩ {ω | ∑ k ∈ range n, (ZE k).indicator 1 ω < (n : ℝ) - m₁ / 4}
  set A2 := {ω | ∑ k ∈ range n,
          {ω | (1 / 2 : ℝ) ≤ μ[(E k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω}.indicator 1 ω ≤
            (n : ℝ) - m₁ ∧
        (n : ℝ) - (1 - 1 / 2 - 1 / 4) * m₁ ≤ ∑ k ∈ range n, (E k).indicator 1 ω}
  set B := ⋃ k ∈ range n, {ω | ω ∈ Reg ∧ μ[(ZF k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω <
        κ * μ[(ZE k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω - e}
  set C := {ω | (j : ℝ) ≤ n - ∑ k ∈ range n,
          {ω | 1 - p / 2 ≤ μ[(E' k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω}.indicator 1 ω ∧
        (n : ℝ) - ∑ k ∈ range n, (E' k).indicator 1 ω ≤ (1 - (1 - p / 2) - p / 4) * j}
  have hgood : ∀ᵐ ω ∂μ, ∀ k,
      μ[(E k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω ≤
        μ[(ZE k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω ∧
      μ[(E' k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω ≤
        1 - μ[(ZF k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω := by
    rw [ae_all_iff]; intro k
    have hEm : MeasurableSet (E k) := ℱ.le (k + 1) _ (hZE k)
    have hE'm : MeasurableSet (E' k) := ℱ.le (k + 1) _ (hE' k)
    have h1 := condExp_mono (m := ℱ k) (μ := μ) ((integrable_const (1 : ℝ)).indicator hEm)
      ((integrable_const (1 : ℝ)).indicator (hZEm k))
      (Filter.Eventually.of_forall (Set.indicator_le_indicator_of_subset
        Set.inter_subset_left (fun _ => zero_le_one)))
    have h2 := condExp_mono (m := ℱ k) (μ := μ) ((integrable_const (1 : ℝ)).indicator hE'm)
      ((integrable_const (1 : ℝ)).indicator (hZFm k).compl)
      (Filter.Eventually.of_forall (Set.indicator_le_indicator_of_subset
        Set.inter_subset_left (fun _ => zero_le_one)))
    have h3 := condExp_indicator_compl_ae ℱ (μ := μ) (hZFm k) k
    filter_upwards [h1, h2, h3] with ω h1 h2 h3
    exact ⟨h1, h2.trans_eq h3⟩
  set N := {ω | ¬ ∀ k,
      μ[(E k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω ≤
        μ[(ZE k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω ∧
      μ[(E' k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω ≤
        1 - μ[(ZF k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω}
  have hN : μ.real N = 0 := by
    simp only [Measure.real, N]
    rw [ae_iff.1 hgood]; rfl
  -- the inclusion
  have hsub : Reg ∩ {ω | ∑ k ∈ range n, (ZF k).indicator 1 ω ≤ p / 4 * (j : ℝ)} ⊆
      A1 ∪ A2 ∪ B ∪ C ∪ N := by
    intro ω ⟨hR, hle⟩
    by_contra hcon
    simp only [Set.mem_union, not_or] at hcon
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hcon
    simp only [N, Set.mem_ofPred_eq, not_not] at h5
    -- step A (Lemma 4.21, first half)
    have hEZ : ∑ k ∈ range n, (E k).indicator (1 : Ω → ℝ) ω =
        ∑ k ∈ range n, (ZE k).indicator 1 ω := by
      refine sum_congr rfl fun k hk => ?_
      have hFk : ω ∈ F k := hReg k (mem_range.1 hk) hR
      by_cases h : ω ∈ ZE k <;> simp [E, h, hFk]
    have hA1 : (n : ℝ) - m₁ / 4 ≤ ∑ k ∈ range n, (ZE k).indicator 1 ω := by
      by_contra h; exact h1 ⟨hR, lt_of_not_ge h⟩
    have hA2 : (n : ℝ) - m₁ < ∑ k ∈ range n,
        {ω | (1 / 2 : ℝ) ≤ μ[(E k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω}.indicator 1 ω := by
      by_contra h
      exact h2 ⟨le_of_not_gt h, by rw [hEZ]; linarith⟩
    -- step B (Lemma 4.7) and the comparison of the two counts
    have hcount : ∑ k ∈ range n,
        {ω | 1 - p / 2 ≤ μ[(E' k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω}.indicator (1 : Ω → ℝ) ω
          ≤ n - ∑ k ∈ range n,
        {ω | (1 / 2 : ℝ) ≤ μ[(E k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω}.indicator 1 ω := by
      rw [le_sub_iff_add_le, ← sum_add_distrib]
      calc _ ≤ ∑ _k ∈ range n, (1 : ℝ) := sum_le_sum fun k hk => ?_
        _ = n := by simp
      by_cases hc : (1 / 2 : ℝ) ≤ μ[(E k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω
      · have hB : ¬ (ω ∈ Reg ∧ μ[(ZF k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω <
            κ * μ[(ZE k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω - e) := by
          intro hb; exact h3 (Set.mem_biUnion hk hb)
        have hZFk : κ * μ[(ZE k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω - e ≤
            μ[(ZF k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω := by
          by_contra h; exact hB ⟨hR, lt_of_not_ge h⟩
        have hZE' : 1 / 2 ≤ μ[(ZE k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω :=
          hc.trans (h5 k).1
        have hpk : p ≤ μ[(ZF k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω := by
          have := mul_le_mul_of_nonneg_left hZE' hκ
          simp only [hpdef]; linarith
        have hlt : μ[(E' k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω < 1 - p / 2 := by
          have := (h5 k).2; linarith
        have hn : ¬ (1 - p / 2 ≤ μ[(E' k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω) :=
          not_le.2 hlt
        simp only [Set.indicator_apply, Set.mem_ofPred_eq, hn, hc, if_true, if_false,
          Pi.one_apply]
        norm_num
      · by_cases hc' : 1 - p / 2 ≤ μ[(E' k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω <;>
          simp only [Set.indicator_apply, Set.mem_ofPred_eq, hc, hc', if_true, if_false,
            Pi.one_apply] <;> norm_num
    have hj : (j : ℝ) ≤ n - ∑ k ∈ range n,
        {ω | 1 - p / 2 ≤ μ[(E' k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω}.indicator
          (1 : Ω → ℝ) ω := by
      have hle' := gm_sum_indicator_le
        (fun k => {ω | (1 / 2 : ℝ) ≤ μ[(E k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω}) n ω
      have hle'' := gm_sum_indicator_le
        (fun k => {ω | 1 - p / 2 ≤ μ[(E' k).indicator (fun _ => (1 : ℝ)) | ℱ k] ω}) n ω
      rcases le_total m₁ n with hm | hm
      · have : (j : ℝ) = n - m₁ := by simp only [j]; push_cast [hm]; ring
        rw [this]; linarith
      · have : j = 0 := Nat.sub_eq_zero_of_le hm
        rw [this, Nat.cast_zero]; linarith
    -- step C (Proposition 4.17)
    have hC : (1 - (1 - p / 2) - p / 4) * j < (n : ℝ) - ∑ k ∈ range n, (E' k).indicator 1 ω := by
      by_contra h; exact h4 ⟨hj, le_of_not_gt h⟩
    have hE'Z : (n : ℝ) - ∑ k ∈ range n, (E' k).indicator (1 : Ω → ℝ) ω =
        ∑ k ∈ range n, (ZF k).indicator 1 ω := by
      rw [sub_eq_iff_eq_add, ← sum_add_distrib]
      rw [show (n : ℝ) = ∑ _k ∈ range n, (1 : ℝ) by simp]
      refine sum_congr rfl fun k hk => ?_
      have hFk : ω ∈ F k := hReg k (mem_range.1 hk) hR
      by_cases h : ω ∈ ZF k <;> simp [E', h, hFk]
    rw [hE'Z] at hC
    have : (1 - (1 - p / 2) - p / 4) = p / 4 := by ring
    rw [this] at hC
    simp only [Set.mem_ofPred_eq] at hle
    linarith
  -- the measure bound
  have hA2 : μ.real A2 ≤ Real.exp (-2 * (1 / 4) ^ 2 * m₁) :=
    gm_uncond_to_cond ℱ (μ := μ) E hZE (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      n m₁
  have hB : μ.real B ≤ n * δ₂ := by
    refine (measureReal_biUnion_finset_le _ _).trans ?_
    calc _ ≤ ∑ _k ∈ range n, δ₂ := sum_le_sum fun k hk => h47 k (mem_range.1 hk)
      _ = n * δ₂ := by simp
  have hC : μ.real C ≤ Real.exp (-2 * (p / 4) ^ 2 * j) :=
    gm_uncond_to_cond_core ℱ (μ := μ) E' hE' (by linarith) (by linarith) (by linarith) n j
  calc _ ≤ μ.real (A1 ∪ A2 ∪ B ∪ C ∪ N) := measureReal_mono hsub
    _ ≤ μ.real A1 + μ.real A2 + μ.real B + μ.real C + μ.real N := by
        have u1 := measureReal_union_le (μ := μ) A1 A2
        have u2 := measureReal_union_le (μ := μ) (A1 ∪ A2) B
        have u3 := measureReal_union_le (μ := μ) (A1 ∪ A2 ∪ B) C
        have u4 := measureReal_union_le (μ := μ) (A1 ∪ A2 ∪ B ∪ C) N
        linarith
    _ ≤ _ := by rw [hN]; linarith

end LQGMetric.GM
