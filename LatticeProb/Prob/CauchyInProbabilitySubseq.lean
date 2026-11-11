import Mathlib

/-!
# Borel–Cantelli extraction of an almost surely controlled subsequence

Three facts that pass from convergence in probability to an almost sure, eventually controlled
subsequence on an arbitrary measure space `(X, μ)`:

* `LatticeProb.exists_seq_prob_le_of_cauchy`: if the distances `d s t` tend to `0` in `μ`-measure
  as `(s, t) → (0, 0)` in `(0, ∞)²`, there is a strictly decreasing null sequence `ε` whose
  consecutive pairs satisfy the geometric bounds `μ {2^{-k} < d (ε k) (ε (k+1))} ≤ 2^{-k}`.
* `LatticeProb.ae_eventually_le_of_prob_le`: if nonnegative extended-real functions `D k` satisfy
  `μ {2^{-k} < D k} ≤ 2^{-k}` for all `k`, then `μ`-almost every `x` satisfies `D k x ≤ 2^{-k}` for
  all large `k` (the first Borel–Cantelli lemma, `MeasureTheory.ae_eventually_notMem`).
* `LatticeProb.exists_strictMono_prob_le_of_cauchy`: the sequence version of the first fact, with
  a strictly increasing index sequence `n : ℕ → ℕ` in place of the null sequence `ε`.

In the first fact, each level `k` has a radius `δ k` such that every pair with both entries in
`(0, δ k)` is good at level `k`. The sequence `ε` is `halvingSeq δ`, which satisfies
`ε k < δ k` and `ε (k+1) < δ k`, so the consecutive pair at level `k` is good.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

/-- The auxiliary radius sequence `e 0 = δ 0 / 2` and `e (k+1) = min (e k / 2) (δ (k+1) / 2)`.
It is positive, strictly decreasing and tends to `0`, and `e k < δ k`, `e (k+1) < δ k`. -/
def halvingSeq (δ : ℕ → ℝ) : ℕ → ℝ
  | 0 => δ 0 / 2
  | k + 1 => min (halvingSeq δ k / 2) (δ (k + 1) / 2)

lemma halvingSeq_zero (δ : ℕ → ℝ) : halvingSeq δ 0 = δ 0 / 2 := rfl

lemma halvingSeq_succ (δ : ℕ → ℝ) (k : ℕ) :
    halvingSeq δ (k + 1) = min (halvingSeq δ k / 2) (δ (k + 1) / 2) := rfl

lemma halvingSeq_pos {δ : ℕ → ℝ} (hδ : ∀ k, 0 < δ k) (k : ℕ) : 0 < halvingSeq δ k := by
  induction k with
  | zero => rw [halvingSeq_zero]; exact half_pos (hδ 0)
  | succ k ih => rw [halvingSeq_succ]; exact lt_min (half_pos ih) (half_pos (hδ (k + 1)))

lemma halvingSeq_succ_le (δ : ℕ → ℝ) (k : ℕ) : halvingSeq δ (k + 1) ≤ halvingSeq δ k / 2 := by
  rw [halvingSeq_succ]; exact min_le_left _ _

lemma halvingSeq_lt {δ : ℕ → ℝ} (hδ : ∀ k, 0 < δ k) (k : ℕ) : halvingSeq δ k < δ k := by
  cases k with
  | zero => rw [halvingSeq_zero]; linarith [hδ 0]
  | succ k =>
    rw [halvingSeq_succ]
    exact lt_of_le_of_lt (min_le_right _ _) (by linarith [hδ (k + 1)])

lemma halvingSeq_succ_lt {δ : ℕ → ℝ} (hδ : ∀ k, 0 < δ k) (k : ℕ) :
    halvingSeq δ (k + 1) < δ k := by
  have h1 := halvingSeq_pos hδ k
  have h2 := halvingSeq_lt hδ k
  exact lt_of_le_of_lt (halvingSeq_succ_le δ k) (by linarith)

lemma halvingSeq_strictAnti {δ : ℕ → ℝ} (hδ : ∀ k, 0 < δ k) : StrictAnti (halvingSeq δ) :=
  strictAnti_nat_of_succ_lt fun k =>
    lt_of_le_of_lt (halvingSeq_succ_le δ k) (by linarith [halvingSeq_pos hδ k])

lemma halvingSeq_le_geom (δ : ℕ → ℝ) (k : ℕ) :
    halvingSeq δ k ≤ halvingSeq δ 0 * (1 / 2 : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc halvingSeq δ (k + 1) ≤ halvingSeq δ k / 2 := halvingSeq_succ_le δ k
      _ ≤ halvingSeq δ 0 * (1 / 2 : ℝ) ^ k / 2 := by linarith
      _ = halvingSeq δ 0 * (1 / 2 : ℝ) ^ (k + 1) := by ring

lemma tendsto_halvingSeq {δ : ℕ → ℝ} (hδ : ∀ k, 0 < δ k) :
    Tendsto (halvingSeq δ) atTop (𝓝 0) := by
  have hg : Tendsto (fun k : ℕ => halvingSeq δ 0 * (1 / 2 : ℝ) ^ k) atTop (𝓝 0) := by
    have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (halvingSeq δ 0)
    simpa using h
  exact squeeze_zero (fun k => (halvingSeq_pos hδ k).le) (halvingSeq_le_geom δ) hg

/-- **Borel–Cantelli subsequence for convergence in probability.** Suppose that for every `η > 0`
the `μ`-measure of `{d s t > η}` tends to `0` as `(s, t) → (0, 0)` in `(0, ∞)²`. Then there is a
strictly decreasing sequence `ε` tending to `0` such that, for every `k`, the pair
`(ε k, ε (k+1))` satisfies `μ {d (ε k) (ε (k+1)) > 2^{-k}} ≤ 2^{-k}`. The same `ε` serves every
measure on the same space for which the bounds have been transferred. -/
theorem exists_seq_prob_le_of_cauchy {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (d : ℝ → ℝ → X → ℝ≥0∞)
    (h : ∀ η : ℝ, 0 < η → Tendsto (fun p : ℝ × ℝ => μ {x | ENNReal.ofReal η < d p.1 p.2 x})
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 0)) :
    ∃ ε : ℕ → ℝ, (∀ k, 0 < ε k) ∧ StrictAnti ε ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ k, μ {x | ENNReal.ofReal ((1 / 2) ^ k) < d (ε k) (ε (k + 1)) x} ≤
        ENNReal.ofReal ((1 / 2) ^ k) := by
  -- Level `k`: a radius `δ k` such that every pair in `(0, δ k)²` is good at level `k`.
  have hscale : ∀ k : ℕ, ∃ δ : ℝ, 0 < δ ∧ ∀ s t : ℝ, 0 < s → s < δ → 0 < t → t < δ →
      μ {x | ENNReal.ofReal ((1 / 2) ^ k) < d s t x} ≤ ENNReal.ofReal ((1 / 2) ^ k) := by
    intro k
    have hη : (0 : ℝ) < (1 / 2) ^ k := by positivity
    have hev := (h _ hη).eventually (Iio_mem_nhds (ENNReal.ofReal_pos.2 hη))
    obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := Filter.mem_prod_iff.1 (Filter.eventually_iff.1 hev)
    obtain ⟨u₁, hu₁, hsu₁⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 ht₁
    obtain ⟨u₂, hu₂, hsu₂⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 ht₂
    refine ⟨min u₁ u₂, lt_min hu₁ hu₂, fun s t hs hsδ ht htδ => ?_⟩
    have hs' : s ∈ Ioo 0 u₁ := ⟨hs, lt_of_lt_of_le hsδ (min_le_left _ _)⟩
    have ht' : t ∈ Ioo 0 u₂ := ⟨ht, lt_of_lt_of_le htδ (min_le_right _ _)⟩
    have hmem := hsub (mk_mem_prod (hsu₁ hs') (hsu₂ ht'))
    exact le_of_lt (Set.mem_Iio.1 hmem)
  choose δ hδpos hδgood using hscale
  refine ⟨halvingSeq δ, halvingSeq_pos hδpos, halvingSeq_strictAnti hδpos,
    tendsto_halvingSeq hδpos, fun k => ?_⟩
  exact hδgood k _ _ (halvingSeq_pos hδpos k) (halvingSeq_lt hδpos k)
    (halvingSeq_pos hδpos (k + 1)) (halvingSeq_succ_lt hδpos k)

/-- **Sequence form of the Borel–Cantelli extraction.** If `d a b` tends to `0` in `μ`-measure as
`(a, b) → (∞, ∞)` in `ℕ × ℕ`, then for every `n₀` there is a strictly increasing sequence `n` with
`n₀ ≤ n 0` whose consecutive pairs satisfy the geometric bounds
`μ {2^{-k} < d (n k) (n (k + 1))} ≤ 2^{-k}` for all `k`. The proof takes, for each level `k`, a
threshold `N k` beyond which the level-`k` bound holds on the whole quadrant, and spaces the indices
so that `n k ≥ N k` and `n (k + 1) ≥ N k`. Literature locator: standard measure theory (extraction of
an almost surely controlled subsequence from convergence in measure, via the first Borel–Cantelli
lemma); the continuous-parameter version is `exists_seq_prob_le_of_cauchy`. -/
theorem exists_strictMono_prob_le_of_cauchy {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (d : ℕ → ℕ → X → ℝ≥0∞)
    (h : ∀ η : ℝ, 0 < η → Tendsto (fun p : ℕ × ℕ => μ {x | ENNReal.ofReal η < d p.1 p.2 x})
      atTop (𝓝 0))
    (n₀ : ℕ) :
    ∃ n : ℕ → ℕ, StrictMono n ∧ n₀ ≤ n 0 ∧
      ∀ k, μ {x | ENNReal.ofReal ((1 / 2) ^ k) < d (n k) (n (k + 1)) x} ≤
        ENNReal.ofReal ((1 / 2) ^ k) := by
  -- Level `k`: a threshold `N k` such that every pair in `[N k, ∞)²` is good at level `k`.
  have hscale : ∀ k : ℕ, ∃ N : ℕ, ∀ a b : ℕ, N ≤ a → N ≤ b →
      μ {x | ENNReal.ofReal ((1 / 2) ^ k) < d a b x} ≤ ENNReal.ofReal ((1 / 2) ^ k) := by
    intro k
    have hη : (0 : ℝ) < (1 / 2) ^ k := by positivity
    have hev := (h _ hη).eventually (Iio_mem_nhds (ENNReal.ofReal_pos.2 hη))
    obtain ⟨N, hN⟩ := Filter.eventually_atTop_prod_self'.1 hev
    exact ⟨N, fun a b ha hb => le_of_lt (Set.mem_Iio.1 (hN a ha b hb))⟩
  choose N hN using hscale
  refine ⟨fun k => n₀ + k + ∑ j ∈ Finset.range (k + 1), N j, ?_, ?_, fun k => ?_⟩
  · refine strictMono_nat_of_lt_succ fun k => ?_
    simp only [Finset.sum_range_succ]
    omega
  · simp only [Finset.sum_range_succ, Finset.sum_range_zero]
    omega
  · dsimp only
    refine hN k _ _ ?_ ?_ <;> simp only [Finset.sum_range_succ] <;> omega

/-- **First Borel–Cantelli lemma for geometric thresholds.** If `μ {2^{-k} < D k} ≤ 2^{-k}` for all
`k`, then for `μ`-almost every `x` the inequality `D k x ≤ 2^{-k}` holds for all sufficiently large
`k`. The proof sums the bounds: `∑ 2^{-k} < ∞`, so `μ`-almost every `x` lies in only finitely
many of the sets `{2^{-k} < D k}`. -/
theorem ae_eventually_le_of_prob_le {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (D : ℕ → X → ℝ≥0∞)
    (hD : ∀ k, μ {x | ENNReal.ofReal ((1 / 2) ^ k) < D k x} ≤ ENNReal.ofReal ((1 / 2) ^ k)) :
    ∀ᵐ x ∂μ, ∀ᶠ k in atTop, D k x ≤ ENNReal.ofReal ((1 / 2) ^ k) := by
  have hgeom : ∑' k : ℕ, ENNReal.ofReal ((1 / 2 : ℝ) ^ k) ≠ ∞ := by
    have hr : ENNReal.ofReal (1 / 2) < 1 := by
      rw [ENNReal.ofReal_lt_one]; norm_num
    simp_rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [ENNReal.tsum_geometric]
    exact ENNReal.inv_ne_top.2 (tsub_pos_of_lt hr).ne'
  have hsum : ∑' k : ℕ, μ {x | ENNReal.ofReal ((1 / 2) ^ k) < D k x} ≠ ∞ :=
    ne_top_of_le_ne_top hgeom (ENNReal.tsum_le_tsum hD)
  filter_upwards [ae_eventually_notMem hsum] with x hx
  exact hx.mono fun k hk => not_lt.1 hk

end LatticeProb
