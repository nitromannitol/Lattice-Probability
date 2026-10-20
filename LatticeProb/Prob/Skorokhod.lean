/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Prob/Skorokhod.lean.
-/
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Analysis.SpecificLimits.Basic
import LatticeProb.Prob.SkorokhodLaw

/-!
# Almost sure convergence in the Skorokhod construction

This file continues `LatticeProb.Skorokhod.SkorokhodLaw`. On the probability space `SkΩ S` with
the measure `SkData.prob` it introduces two events:

* `SkData.good`: each coordinate `Y_{ni}` lies in its cell `B^{m}_i`, for `m = D.reg n`, whenever
  `Ps n` charges that cell; and the coordinate `X` avoids every cell of level `m` that `P` does
  not charge;
* `SkData.bad`: infinitely many levels `m` have `X ∈ B^m_0` or `ξ > 1 - ε_m`.

The file proves that `good` has probability one (`SkData.prob_good_compl`), that `bad` has
probability zero by the Borel–Cantelli lemma (`SkData.prob_bad`), and that `X'_n ω → X ω` for
every `ω ∈ good ∩ badᶜ` (`SkData.tendsto_X'`). Since `good ∩ badᶜ` has full measure, `X'_n`
converges to `X` almost surely. The file proves this as the pathwise statement on `good ∩ badᶜ`
together with the two null-set facts. It does not combine them into a single almost-sure
declaration, and it does not modify `X'_n` on a null set.

The construction follows Billingsley, *Convergence of Probability Measures*, 2nd ed. (1999),
proof of Theorem 6.7 (pp. 70–71).
-/

open MeasureTheory ProbabilityTheory Set Filter Topology Function
open scoped ENNReal unitInterval

namespace LatticeProb.Skorokhod

variable {S : Type*} [MeasurableSpace S] [PseudoMetricSpace S]
variable {P : Measure S} {Ps : ℕ → Measure S} (D : SkData P Ps)
variable [IsProbabilityMeasure P] [∀ n, IsProbabilityMeasure (Ps n)]

namespace SkData

/-- The good event. Each coordinate `Y_{ni}` lies in its cell `B^{D.reg n}_i` whenever `Ps n`
charges that cell, and the coordinate `X` avoids every cell of each level `m` that `P` does not
charge. -/
def good : Set (SkΩ S) :=
  {ω | ∀ n i, Ps n (D.B (D.reg n) i) ≠ 0 → ω.1 (some (Sum.inl (n, i))) ∈ D.B (D.reg n) i} ∩
    {ω | ∀ m i, P (D.B m i) = 0 → ω.1 none ∉ D.B m i}

/-- The bad event: infinitely many levels `m` have `X ∈ B^m_0` or `ξ > 1 - ε_m`. -/
def bad : Set (SkΩ S) := {ω | ∃ᶠ m in atTop, ω.1 none ∈ D.B m 0 ∨ ¬ ω.2 ≤ thr m}

/-- The good event has probability one. -/
lemma prob_good_compl : D.prob (D.good)ᶜ = 0 := by
  have h1 : ∀ n i, D.prob {ω : SkΩ S | Ps n (D.B (D.reg n) i) ≠ 0 ∧
      ω.1 (some (Sum.inl (n, i))) ∈ (D.B (D.reg n) i)ᶜ} = 0 := by
    intro n i
    by_cases h : Ps n (D.B (D.reg n) i) = 0
    · simp [h]
    · refine measure_mono_null (t := {ω : SkΩ S | ω.1 (some (Sum.inl (n, i))) ∈
        (D.B (D.reg n) i)ᶜ}) (fun ω hω => hω.2) ?_
      rw [D.prob_coord _ ((D.part _).meas i).compl]
      exact skCond_compl _ ((D.part _).meas i) h
  have h2 : ∀ m i, D.prob {ω : SkΩ S | P (D.B m i) = 0 ∧ ω.1 none ∈ D.B m i} = 0 := by
    intro m i
    by_cases h : P (D.B m i) = 0
    · refine measure_mono_null (t := {ω : SkΩ S | ω.1 none ∈ D.B m i}) (fun ω hω => hω.2) ?_
      rw [D.prob_coord _ ((D.part _).meas i)]
      exact h
    · simp [h]
  refine measure_mono_null (t := (⋃ n, ⋃ i, {ω : SkΩ S | Ps n (D.B (D.reg n) i) ≠ 0 ∧
      ω.1 (some (Sum.inl (n, i))) ∈ (D.B (D.reg n) i)ᶜ}) ∪
      ⋃ m, ⋃ i, {ω : SkΩ S | P (D.B m i) = 0 ∧ ω.1 none ∈ D.B m i}) ?_ ?_
  · intro ω hω
    simp only [good, mem_compl_iff, mem_inter_iff, Set.mem_setOf_eq, not_and_or, not_forall,
      not_not] at hω
    rcases hω with ⟨n, i, hne, hmem⟩ | ⟨m, i, h0, hmem⟩
    · exact Or.inl (mem_iUnion₂.2 ⟨n, i, hne, hmem⟩)
    · exact Or.inr (mem_iUnion₂.2 ⟨m, i, h0, hmem⟩)
  · exact measure_union_null (measure_iUnion_null fun n => measure_iUnion_null fun i => h1 n i)
      (measure_iUnion_null fun m => measure_iUnion_null fun i => h2 m i)

/-- The bad event has probability zero, by the Borel–Cantelli lemma. -/
lemma prob_bad : D.prob D.bad = 0 := by
  refine measure_setOf_frequently_eq_zero ?_
  have hle : ∀ m, D.prob {ω : SkΩ S | ω.1 none ∈ D.B m 0 ∨ ¬ ω.2 ≤ thr m} ≤
      ENNReal.ofReal (skEps m) + ENNReal.ofReal (skEps m) := by
    intro m
    refine (measure_union_le {ω : SkΩ S | ω.1 none ∈ D.B m 0} {ω : SkΩ S | ¬ ω.2 ≤ thr m}).trans
      (add_le_add ?_ (le_of_eq ?_))
    · rw [D.prob_coord _ ((D.part m).meas 0)]; exact D.small m
    · have := D.prob_one none MeasurableSet.univ (thr m)
      simp only [mem_univ, and_true, measure_univ, one_mul] at this
      rw [this, show ((thr m : I) : ℝ) = 1 - skEps m from rfl, sub_sub_cancel]
  have hsum : Summable skEps := by
    unfold skEps
    exact (summable_nat_add_iff 1).2 (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
  rw [ENNReal.tsum_add, ← ENNReal.ofReal_tsum_of_nonneg (fun m => (skEps_pos m).le) hsum]
  exact ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩

omit [IsProbabilityMeasure P] [∀ n, IsProbabilityMeasure (Ps n)] in
/-- Pathwise convergence: on `good ∩ badᶜ`, `X'_n ω → X ω = ω.1 none` as `n → ∞`. Billingsley's
step: `X_n` and `X` lie in the same cell `B^m_i` for all large `n`. -/
lemma tendsto_X' {ω : SkΩ S} (hg : ω ∈ D.good) (hb : ω ∉ D.bad) :
    Tendsto (fun n => D.X' n ω) atTop (𝓝 (ω.1 none)) := by
  have hgood : ∀ᶠ m in atTop, ω.1 none ∉ D.B m 0 ∧ ω.2 ≤ thr m := by
    have hb' : ¬ ∃ᶠ m in atTop, ω.1 none ∈ D.B m 0 ∨ ¬ ω.2 ≤ thr m := hb
    rw [not_frequently] at hb'
    filter_upwards [hb'] with m hm
    push Not at hm
    exact hm
  have hdist : ∀ᶠ n in atTop, dist (D.X' n ω) (ω.1 none) ≤ skEps (D.reg n) := by
    filter_upwards [D.tendsto_reg.eventually hgood, eventually_ge_atTop (D.φ 0)] with n hn hn0
    set m := D.reg n
    set i := D.idx m (ω.1 none)
    have hx : ω.1 none ∈ D.B m i := D.mem_idx m _
    have hi0 : i ≠ 0 := fun h => hn.1 (h ▸ hx)
    have hP : P (D.B m i) ≠ 0 := fun h => hg.2 m i h hx
    have hPn : Ps n (D.B m i) ≠ 0 := by
      refine (lt_of_lt_of_le ?_ (D.lower m n (D.reg_spec hn0) i)).ne'
      refine ENNReal.mul_pos (by
        rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith [skEps_le_half m]) hP
    have hy := hg.1 n i hPn
    have hX : D.X' n ω = ω.1 (some (Sum.inl (n, i))) := by simp [X', hn0, hn.2, m, i]
    rw [hX]
    exact (D.diam m i hi0 _ hy _ hx).le
  rw [tendsto_iff_dist_tendsto_zero]
  exact squeeze_zero' (Eventually.of_forall fun n => dist_nonneg) hdist
    (tendsto_skEps.comp D.tendsto_reg)

end SkData

end LatticeProb.Skorokhod
