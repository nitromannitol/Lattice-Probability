/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39Engine at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Theorem 3.9: the probabilistic iteration engine (Lemmas 3.10, 3.11)

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), §3.3,
`confluence-final.tex` C:1570–1730. In the proof of Theorem 3.9 the arc counts `n_k = #𝓘_k`
(C:1563) are adapted to the filtration `𝓕_k = σ(𝓑^•_{s_k}, h|_{𝓑^•_{s_k}})`, non-increasing, and on
`𝓔_𝕣(a)`, for `k ≤ K_{N₀} − 1`, either the "bad" event `#𝓘_k^{**} > ¼ #(𝓘_k ∖ 𝓘_k^*)` occurs
(conditional probability `≤ 4C₀ε_k^α ≤ C n_k^{−α/4}`, (3.25)) or `n_{k+1} ≤ ½ n_k` ((3.27)).

This file proves the abstract consequence of these facts used in C:1640–1730:

* `t39_peel`: the iteration of (3.25) over `M` consecutive steps (C:1633–1640, (3.26)),
  decomposed on the first entry time (the rigorous form of "conditioning on `𝓕_{k_j}`");
* `t39_level`: the number of steps spent with `n_k ∈ [b, 2b)` exceeds `M` only with
  probability `≤ q_b^M` (Lemma 3.10);
* `t39_sum_le`: off these events, `∑_{k<K} n_k^{−θ} ≤ M (N/2)^{−θ}/(1 − 2^{−θ})` (Lemma 3.11,
  steps 2–3).

Bookkeeping deviation (DV-CONF-T39a): CONF groups the steps into the halving epochs `[k_j, k_{j+1})`
(Lemma 3.10); we group them by the dyadic level `⌊log₂ n_k⌋`. Both use the same estimate (3.26)
(`M` consecutive bad steps at counts `≥ b` have probability `≤ (C b^{−α/4})^M`) and the same
geometric summation (3.29)–(3.31).
-/

namespace LQGMetric
namespace CONF

open MeasureTheory Set
open scoped ENNReal

section Engine

variable {Ω : Type*} {m0 : MeasurableSpace Ω} (P : Measure Ω)

/-- the events `A ∩ ⋂_{i<M} (L_{k+i} ∩ Bad_{k+i})` -/
def t39PeelSet (L Bad : ℕ → Set Ω) (A : Set Ω) (k : ℕ) : ℕ → Set Ω
  | 0 => A
  | M + 1 => t39PeelSet L Bad A k M ∩ L (k + M) ∩ Bad (k + M)

theorem mem_t39PeelSet (L Bad : ℕ → Set Ω) (A : Set Ω) (k : ℕ) (ω : Ω) :
    ∀ M, ω ∈ t39PeelSet L Bad A k M ↔ ω ∈ A ∧ ∀ i < M, ω ∈ L (k + i) ∧ ω ∈ Bad (k + i)
  | 0 => by simp [t39PeelSet]
  | M + 1 => by
    rw [t39PeelSet, mem_inter_iff, mem_inter_iff, mem_t39PeelSet L Bad A k ω M]
    constructor
    · rintro ⟨⟨⟨hA, h⟩, hL⟩, hB⟩
      refine ⟨hA, fun i hi => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact h i hi
      · exact ⟨hL, hB⟩
    · rintro ⟨hA, h⟩
      exact ⟨⟨⟨hA, fun i hi => h i (by omega)⟩, (h M (by omega)).1⟩, (h M (by omega)).2⟩

/-- **CONF (3.26)** (C:1633–1640), iterated form of (3.25): if `Bad_k ∈ 𝓕_{k+1}`, `L_k ∈ 𝓕_k`
and `P[A ∩ Bad_k] ≤ q P[A]` for `A ∈ 𝓕_k`, `A ⊆ L_k`, then for `A ∈ 𝓕_k`,
`P[A ∩ ⋂_{i<M}(L_{k+i} ∩ Bad_{k+i})] ≤ q^M P[A]`. -/
theorem t39_peel (𝓕 : ℕ → MeasurableSpace Ω) (hmono : Monotone 𝓕) (L Bad : ℕ → Set Ω)
    (q : ℝ≥0∞) (hBad : ∀ k, MeasurableSet[𝓕 (k + 1)] (Bad k))
    (hL : ∀ k, MeasurableSet[𝓕 k] (L k))
    (hstep : ∀ k (A : Set Ω), MeasurableSet[𝓕 k] A → A ⊆ L k → P (A ∩ Bad k) ≤ q * P A)
    (k : ℕ) (A : Set Ω) (hA : MeasurableSet[𝓕 k] A) :
    ∀ M, MeasurableSet[𝓕 (k + M)] (t39PeelSet L Bad A k M) ∧
      P (t39PeelSet L Bad A k M) ≤ q ^ M * P A
  | 0 => by simpa [t39PeelSet] using hA
  | M + 1 => by
    obtain ⟨hm, hle⟩ := t39_peel 𝓕 hmono L Bad q hBad hL hstep k A hA M
    have hmL : MeasurableSet[𝓕 (k + M)] (t39PeelSet L Bad A k M ∩ L (k + M)) :=
      hm.inter (hL _)
    refine ⟨?_, ?_⟩
    · exact (hmono (Nat.le_succ (k + M)) _ hmL).inter (hBad _)
    · calc P (t39PeelSet L Bad A k (M + 1))
          = P ((t39PeelSet L Bad A k M ∩ L (k + M)) ∩ Bad (k + M)) := rfl
        _ ≤ q * P (t39PeelSet L Bad A k M ∩ L (k + M)) :=
          hstep _ _ hmL inter_subset_right
        _ ≤ q * P (t39PeelSet L Bad A k M) := by gcongr; exact inter_subset_left
        _ ≤ q * (q ^ M * P A) := by gcongr
        _ = q ^ (M + 1) * P A := by ring

/-- the event that, after the first time `k₀` with `n_{k₀} < 2b`, the next `M` steps are bad
steps at counts `≥ b` -/
def t39LevelEvent (n : ℕ → Ω → ℕ) (Bad : ℕ → Set Ω) (b M : ℕ) : Set Ω :=
  ⋃ k₀ : ℕ, t39PeelSet (fun k => {ω | b ≤ n k ω}) Bad
    {ω | n k₀ ω < 2 * b ∧ ∀ j < k₀, 2 * b ≤ n j ω} k₀ M

/-- **CONF Lemma 3.10** (C:1600–1647), level form: the event that `M` consecutive bad steps
occur at counts in `[b, 2b)` (starting at the entry into `[0, 2b)`) has probability `≤ q^M`. -/
theorem t39_level (𝓕 : ℕ → MeasurableSpace Ω) (hmono : Monotone 𝓕) (h𝓕 : ∀ k, 𝓕 k ≤ m0)
    [IsProbabilityMeasure P] (n : ℕ → Ω → ℕ) (hn : ∀ k, Measurable[𝓕 k] (n k))
    (Bad : ℕ → Set Ω) (hBad : ∀ k, MeasurableSet[𝓕 (k + 1)] (Bad k)) (b : ℕ) (q : ℝ≥0∞)
    (hstep : ∀ k (A : Set Ω), MeasurableSet[𝓕 k] A → A ⊆ {ω | b ≤ n k ω} →
      P (A ∩ Bad k) ≤ q * P A) (M : ℕ) :
    P (t39LevelEvent n Bad b M) ≤ q ^ M := by
  set E : ℕ → Set Ω := fun k₀ => {ω | n k₀ ω < 2 * b ∧ ∀ j < k₀, 2 * b ≤ n j ω}
  have hE : ∀ k₀, MeasurableSet[𝓕 k₀] (E k₀) := by
    intro k₀
    have h1 : MeasurableSet[𝓕 k₀] {ω | n k₀ ω < 2 * b} :=
      hn k₀ (Set.to_countable (Iio (2 * b))).measurableSet
    have h2 : MeasurableSet[𝓕 k₀] {ω | ∀ j < k₀, 2 * b ≤ n j ω} := by
      have : {ω | ∀ j < k₀, 2 * b ≤ n j ω} = ⋂ j ∈ Finset.range k₀, {ω | 2 * b ≤ n j ω} := by
        ext ω; simp
      rw [this]
      refine Finset.measurableSet_biInter _ fun j hj => ?_
      exact hmono (Finset.mem_range.1 hj).le _ (hn j (Set.to_countable (Ici (2 * b))).measurableSet)
    exact h1.inter h2
  have hL : ∀ k, MeasurableSet[𝓕 k] {ω | b ≤ n k ω} :=
    fun k => hn k (Set.to_countable (Ici b)).measurableSet
  have hdisj : Pairwise (Function.onFun Disjoint E) := by
    intro i j hij
    refine Set.disjoint_left.2 fun ω hi hj => ?_
    rcases lt_or_gt_of_ne hij with h | h
    · exact absurd (hj.2 i h) (not_le.2 hi.1)
    · exact absurd (hi.2 j h) (not_le.2 hj.1)
  calc P (t39LevelEvent n Bad b M)
      ≤ ∑' k₀, P (t39PeelSet (fun k => {ω | b ≤ n k ω}) Bad (E k₀) k₀ M) :=
        measure_iUnion_le _
    _ ≤ ∑' k₀, q ^ M * P (E k₀) := by
        gcongr with k₀
        exact (t39_peel P 𝓕 hmono _ Bad q hBad hL hstep k₀ (E k₀) (hE k₀) M).2
    _ = q ^ M * P (⋃ k₀, E k₀) := by
        rw [ENNReal.tsum_mul_left, measure_iUnion hdisj fun k₀ => h𝓕 k₀ _ (hE k₀)]
    _ ≤ q ^ M := by
        calc q ^ M * P (⋃ k₀, E k₀) ≤ q ^ M * 1 := by gcongr; exact prob_le_one
          _ = q ^ M := mul_one _

end Engine

end CONF
end LQGMetric
