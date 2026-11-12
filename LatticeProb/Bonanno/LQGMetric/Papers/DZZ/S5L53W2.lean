/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53W2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53W1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53M2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53J6
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L13Meas

/-!
# The wiring of `hbadB`: per selected chain, per cell, union (P2-DZZ53W, D131 P-131W)

Ding–Zeitouni–Zhang, arXiv:1807.00422 (`LBM_LGDarXiv.tex`, DZZ l.), proof of Lemma 5.3:
the chain `𝒞` of `𝓔*` (l. 2363–2378) is `𝓕*`-measurable, and DZZ bound the probability that `𝒞`
is not desirable (l. 2504–2522) *conditionally on `𝓕*`*, i.e. on each event `{𝒞 = c₀}`, by the
union over the cells `𝖢_i`, `2 ≤ i ≤ d − 1` (node 3, l. 2510–2514) and the two clauses for `u`
and `v` (node 4, l. 2516–2522); the event `𝓔₄` (l. 2440–2443) is removed first (DEC-131 §2).

* `l53FibreBad c₀`, **`l53BadB_subset`**: `l53BadB ⊆ ⋃ c₀, {𝒞 = c₀} ∩ (𝒟₁ᴮ ∩ l53FibreBad c₀)` (`l53BadB`,
  `l53Chain`: S5L53P2, S5L53L5).
* **`measure_iUnion_inter_le_cond`**: for a countable measurable partition `A c` and an event `E`,
  `P(⋃ c, A c ∩ B c) ≤ P(Eᶜ) + ε` as soon as `P[E ∩ B c | A c] ≤ ε` for every `c`.
* **`l53FibreBad_cond_le`**: on one fibre, the conditional probability splits into the `u`-clause,
  the `v`-clause and one term per interior cell (the `L53DesClause` of node 3, S5L53J6).
* **`l53BadB_le_split`**: `P(l53BadB) ≤ P(𝒟₁ᴮ ∩ Eᶜ) + ε_u + ε_v + e^{T₁} β`, the three
  conditional bounds being on `E ∩ 𝒟₁ᴮ` (`E = 𝓔₄` of P-131R).

Own elementary bookkeeping (the union over chains and cells of DZZ l. 2513–2522).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Union over a countable measurable partition with conditional bounds** (DZZ's conditioning
on `𝓕*`): `P(⋃ c, A c ∩ B c) ≤ P(Eᶜ) + ε` if `P[E ∩ B c | A c] ≤ ε` for every `c`. -/
theorem measure_iUnion_inter_le_cond {ι : Type*} [Countable ι] (P : Measure Ω)
    [IsProbabilityMeasure P] (A B : ι → Set Ω) (hA : ∀ c, MeasurableSet (A c))
    (hdis : Pairwise (Function.onFun Disjoint A)) (E : Set Ω) (ε : ℝ≥0∞)
    (h : ∀ c, P[E ∩ B c | A c] ≤ ε) :
    P (⋃ c, A c ∩ B c) ≤ P Eᶜ + ε := by
  have hsub : (⋃ c, A c ∩ B c) ⊆ Eᶜ ∪ ⋃ c, A c ∩ (E ∩ B c) := by
    intro ω hω
    obtain ⟨c, hc1, hc2⟩ := mem_iUnion.1 hω
    by_cases hE : ω ∈ E
    · exact Or.inr (mem_iUnion.2 ⟨c, hc1, hE, hc2⟩)
    · exact Or.inl hE
  have hterm : ∀ c, P (A c ∩ (E ∩ B c)) ≤ ε * P (A c) := fun c => by
    rw [← cond_mul_eq_inter (hA c) _ P]
    gcongr
    exact h c
  calc P (⋃ c, A c ∩ B c) ≤ P Eᶜ + P (⋃ c, A c ∩ (E ∩ B c)) :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ ≤ P Eᶜ + ∑' c, ε * P (A c) := by
        gcongr
        exact (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum hterm)
    _ = P Eᶜ + ε * P (⋃ c, A c) := by
        rw [ENNReal.tsum_mul_left, measure_iUnion hdis hA]
    _ ≤ P Eᶜ + ε := by
        exact add_le_add_right ((mul_le_mul_of_nonneg_left (prob_le_one (μ := P) (s := ⋃ c, A c)) zero_le).trans_eq
          (mul_one ε)) _

/-- The `𝖢_i`-clauses of `L53ChainDesirable` are the clauses `L53DesClause` of node 3 (S5L53J6)
for the cells `2 ≤ i ≤ d − 1`. -/
lemma l53CellsClause_iff (ν : Measure ℂ) (δ T' : ℝ) (c : List DyBox) :
    l53CellsClause ν δ T' c ↔ ∀ i ∈ Finset.Icc 2 (c.length - 1),
      L53DesClause (μH[1] : Measure ℂ) ν δ T' (l53Iface c (i - 1)) (l53Iface c i) := by
  simp only [Finset.mem_Icc, l53CellsClause, L53DesClause, and_imp]

end DZZ
end LQGMetric
