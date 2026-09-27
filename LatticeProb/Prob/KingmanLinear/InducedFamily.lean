import LatticeProb.Prob.KingmanLinear.Defs
import LatticeProb.Prob.KingmanLinear.Restated
import LatticeProb.Prob.KingmanLinear.LinearSets
import LatticeProb.Prob.Kingman

/-!
# 2. The induced family

On `A = linSet g C k` with first-return map `inducedMap T A` and return time `retTime T A`, the
induced family `indG g T A` is subadditive along `inducedMap T A`, measurable, and integrable at
`j = 1` (Kac's lemma). The library's Kingman theorem (`LatticeProb.ae_tendsto_div`) then gives
a.e. convergence of `indG g T A j x / j`, and the library's Birkhoff theorem
(`LatticeProb.ae_tendsto_bAvg`) gives a.e. convergence of `retSum T A j x / j`.
-/

open MeasureTheory Filter Topology Set

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- The induced family `indG g T A` is subadditive along `inducedMap T A`, inherited from the
subadditivity of `g` along `T`. -/
private theorem subadditiveAlong_indG {g : ℕ → Ω → ℝ} {T : Ω → Ω}
    (hsub : ∀ m n x, g (m+n) x ≤ g m x + g n (T^[m] x)) (A : Set Ω) :
    SubadditiveAlong (inducedMap T A) (indG g T A) := by
  intro m n x
  simp only [indG, retSum]
  rw [birkhoffSum_add (inducedMap T A) (retTime T A) m n x]
  have h := hsub (birkhoffSum (inducedMap T A) (retTime T A) m x)
      (birkhoffSum (inducedMap T A) (retTime T A) n ((inducedMap T A)^[m] x)) x
  rw [← iterate_inducedMap_eq_iterate_birkhoffSum T A m x] at h
  exact h


/-- The return-time Birkhoff sum `retSum T A j` is measurable. -/
private theorem measurable_retSum {T : Ω → Ω} (hT : Measurable T) {A : Set Ω} (hA : MeasurableSet A)
    (j : ℕ) :
    Measurable (retSum T A j) := by
  unfold retSum birkhoffSum
  exact Finset.measurable_sum _
    (fun k _ => (retTime_measurable hT hA).comp
      (Measurable.iterate (inducedMap_measurable hT hA) k))


/-- The induced family `indG g T A j` is measurable. -/
private theorem measurable_indG {g : ℕ → Ω → ℝ} (hgm : ∀ n, Measurable (g n)) {T : Ω → Ω}
    (hT : Measurable T) {A : Set Ω} (hA : MeasurableSet A) (j : ℕ) :
    Measurable (indG g T A j) := by
  have hF : Measurable (fun p : Ω × ℕ => g p.2 p.1) :=
    measurable_from_prod_countable_left (fun n => (hgm n).comp measurable_id)
  exact hF.comp (measurable_id.prodMk (measurable_retSum hT hA j))


omit [MeasurableSpace Ω] in
/-- On `linSet g C k`, the first induced value `indG g T (linSet g C k) 1` is bounded by `|C| *
retTime + k`. -/
private theorem norm_indG_one_le_of_mem_linSet {g : ℕ → Ω → ℝ} (hg : ∀ n x, 0 ≤ g n x) (T : Ω → Ω)
    (C : ℝ) (k : ℕ) {x : Ω} (hx : x ∈ linSet g C k) :
    ‖indG g T (linSet g C k) 1 x‖ ≤ |C| * (retTime T (linSet g C k) x : ℝ) + k := by
  simp only [linSet, Set.mem_setOf_eq] at hx
  rw [show indG g T (linSet g C k) 1 x = g (retTime T (linSet g C k) x) x from
      by simp [indG, retSum, birkhoffSum_one],
    Real.norm_of_nonneg (hg _ _)]
  exact le_trans (hx _)
    (add_le_add (mul_le_mul_of_nonneg_right (le_abs_self C) (Nat.cast_nonneg _)) le_rfl)


/-- The first induced value `indG g T (linSet g C k) 1` is integrable on
`μ.restrict (linSet g C k)`. -/
private theorem integrable_indG_one_restrict_linSet {μ : Measure Ω} [IsProbabilityMeasure μ]
    {T : Ω → Ω} (hT : MeasurePreserving T μ μ) {g : ℕ → Ω → ℝ} (hg : ∀ n x, 0 ≤ g n x)
    (hgm : ∀ n, Measurable (g n)) (C : ℝ) (k : ℕ) :
    Integrable (indG g T (linSet g C k) 1) (μ.restrict (linSet g C k)) := by
  have hA : MeasurableSet (linSet g C k) := measurableSet_linSet hgm C k
  have hInt : Integrable (fun x => |C| * (retTime T (linSet g C k) x : ℝ) + k)
      (μ.restrict (linSet g C k)) :=
    ((integrable_retTime_restrict μ T hT hA).const_mul |C|).add (integrable_const (k : ℝ))
  refine hInt.mono' ?_ ?_
  · exact ((measurable_indG hgm hT.measurable hA 1).aestronglyMeasurable).restrict
  · filter_upwards [ae_restrict_mem hA] with x hx
    exact norm_indG_one_le_of_mem_linSet hg T C k hx


/-- Kingman's theorem for the induced family (the library's `ae_tendsto_div` with `c = 0`): a.e.
on `linSet g C k`, `indG g T (linSet g C k) j x / j` converges. -/
theorem ae_exists_tendsto_indG_div {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {g : ℕ → Ω → ℝ}
    (hsub : ∀ m n x, g (m+n) x ≤ g m x + g n (T^[m] x)) (hg : ∀ n x, 0 ≤ g n x)
    (hgm : ∀ n, Measurable (g n)) (C : ℝ) (k : ℕ) :
    ∀ᵐ x ∂(μ.restrict (linSet g C k)), ∃ L : ℝ,
      Tendsto (fun j : ℕ => indG g T (linSet g C k) j x / (j : ℝ)) atTop (𝓝 L) :=
  ae_tendsto_div (inducedMap_measurePreserving hT (measurableSet_linSet hgm C k))
    (subadditiveAlong_indG hsub _)
    (measurable_indG hgm hT.measurable (measurableSet_linSet hgm C k))
    (integrable_indG_one_restrict_linSet hT hg hgm C k) (c := 0)
    (fun n y _ => by rw [zero_mul]; exact hg _ _)

omit [MeasurableSpace Ω] in
/-- The real cast of `retSum T A j x` equals the Birkhoff sum of the real-valued return time. -/
private theorem retSum_cast_eq_birkhoffSum (T : Ω → Ω) (A : Set Ω) (j : ℕ) (x : Ω) :
    (retSum T A j x : ℝ) = birkhoffSum (inducedMap T A) (fun y => (retTime T A y : ℝ)) j x := by
  simp only [retSum, birkhoffSum]
  exact Nat.cast_sum _ _


/-- For `μ`-a.e. `x ∈ A`, `retSum T A j x / j` converges, by the library's Birkhoff theorem applied
to the return time. -/
theorem ae_exists_tendsto_retSum_div {μ : Measure Ω} [IsProbabilityMeasure μ] {T : Ω → Ω}
    (hT : MeasurePreserving T μ μ) {A : Set Ω} (hA : MeasurableSet A) :
    ∀ᵐ x ∂(μ.restrict A), ∃ ρ : ℝ,
      Tendsto (fun j : ℕ => (retSum T A j x : ℝ) / (j : ℝ)) atTop (𝓝 ρ) := by
  have hmeasr : Measurable (fun y => (retTime T A y : ℝ)) :=
    measurable_from_nat.comp (retTime_measurable hT.measurable hA)
  have h := ae_tendsto_bAvg (inducedMap_measurePreserving hT hA) hmeasr
    (integrable_retTime_restrict μ T hT hA)
  filter_upwards [h] with x hx
  obtain ⟨L, hL⟩ := hx
  exact ⟨L, by simpa [bAvg, retSum_cast_eq_birkhoffSum] using hL⟩

end LatticeProb
