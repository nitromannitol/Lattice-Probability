import Mathlib

/-!
# Measurability of proportionality for random continuous functions

Let `X` be a separable topological space and let `m M : T → C(X, ℝ)` be measurable maps, where
`C(X, ℝ)` carries the Borel σ-algebra of the compact-open topology. Write `f⁺` for the positive
part `ENNReal.ofReal ∘ f`. The set of parameters `o` for which `(m o)⁺` is a positive multiple of
`(M o)⁺` need not be presented as a measurable set (it is a projection over the scalar). This
module exhibits a measurable set `G` with the two properties needed to transfer proportionality
along a change of law:

* on `G`, `(m o)⁺ = b • (M o)⁺` for some `b > 0`;
* `G` contains every `o` for which `(m o)⁺` and `(M o)⁺` are positive multiples of one common
  `[0, ∞]`-valued function on `X`.

The set `G` is described through a countable dense subset `S ⊆ X` only: either both functions are
nonpositive on `S`, or there is a point `q ∈ S` where both are positive and the cross products
`(m o x)⁺ (M o q) = (m o q) (M o x)⁺` agree for `x ∈ S`. Continuity and density extend these
relations to all of `X`.
-/

namespace LatticeProb

open MeasureTheory Set
open scoped ENNReal

/-- `ENNReal.ofReal` only sees the positive part. -/
theorem ofReal_max_zero (y : ℝ) : ENNReal.ofReal (max y 0) = ENNReal.ofReal y := by
  rcases le_total y 0 with h | h
  · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]
  · rw [max_eq_left h]

/-- **Measurable proportionality set.** For measurable maps `m M : T → C(X, ℝ)` on a separable
space `X` there is a measurable set `G` such that on `G` the positive part of `m o` is a positive
multiple of the positive part of `M o`, and `G` contains every `o` for which both positive parts
are positive multiples of one common function `I : X → [0, ∞]`. -/
theorem exists_measurableSet_ofReal_proportional {X T : Type*} [TopologicalSpace X]
    [TopologicalSpace.SeparableSpace X] [MeasurableSpace T] {m M : T → C(X, ℝ)}
    (hm : Measurable m) (hM : Measurable M) :
    ∃ G : Set T, MeasurableSet G ∧
      (∀ o ∈ G, ∃ b : ℝ, 0 < b ∧ ∀ x : X,
        ENNReal.ofReal (m o x) = ENNReal.ofReal b * ENNReal.ofReal (M o x)) ∧
      (∀ o : T, (∃ (b₁ b₂ : ℝ) (I : X → ℝ≥0∞), 0 < b₁ ∧ 0 < b₂ ∧ ∀ x : X,
          ENNReal.ofReal (m o x) = ENNReal.ofReal b₁ * I x ∧
            ENNReal.ofReal (M o x) = ENNReal.ofReal b₂ * I x) → o ∈ G) := by
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense X
  have hev : ∀ x : X, Measurable fun o => m o x :=
    fun x => (ContinuousMap.measurable_eval x).comp hm
  have hEv : ∀ x : X, Measurable fun o => M o x :=
    fun x => (ContinuousMap.measurable_eval x).comp hM
  let G₁ : Set T := ⋂ x ∈ S, {o | m o x ≤ 0} ∩ {o | M o x ≤ 0}
  let G₂ : Set T := ⋃ q ∈ S, ({o | 0 < m o q} ∩ {o | 0 < M o q}) ∩
    ⋂ x ∈ S, {o | max (m o x) 0 * M o q = m o q * max (M o x) 0}
  refine ⟨G₁ ∪ G₂, ?_, ?_, ?_⟩
  · refine MeasurableSet.union ?_ ?_
    · refine MeasurableSet.biInter hSc fun x _ => ?_
      exact (measurableSet_le (hev x) measurable_const).inter
        (measurableSet_le (hEv x) measurable_const)
    · refine MeasurableSet.biUnion hSc fun q _ => ?_
      refine ((measurableSet_lt measurable_const (hev q)).inter
        (measurableSet_lt measurable_const (hEv q))).inter ?_
      refine MeasurableSet.biInter hSc fun x _ => ?_
      exact measurableSet_eq_fun (((hev x).max measurable_const).mul (hEv q))
        ((hev q).mul ((hEv x).max measurable_const))
  · intro o ho
    rcases ho with ho | ho
    · simp only [G₁, mem_iInter, mem_inter_iff, mem_ofPred_eq] at ho
      have hcl : ∀ (f : C(X, ℝ)), (∀ x ∈ S, f x ≤ 0) → ∀ x, f x ≤ 0 := by
        intro f hf x
        have hsub : closure S ⊆ {y | f y ≤ 0} :=
          (isClosed_le f.continuous continuous_const).closure_subset_iff.mpr hf
        exact hsub (hSd.closure_eq ▸ mem_univ x)
      have h1 := hcl (m o) fun x hx => (ho x hx).1
      have h2 := hcl (M o) fun x hx => (ho x hx).2
      refine ⟨1, one_pos, fun x => ?_⟩
      rw [ENNReal.ofReal_of_nonpos (h1 x), ENNReal.ofReal_of_nonpos (h2 x), mul_zero]
    · simp only [G₂, mem_iUnion, mem_inter_iff, mem_iInter, mem_ofPred_eq] at ho
      obtain ⟨q, -, ⟨hmq, hMq⟩, hx⟩ := ho
      have hext : (fun x => max (m o x) 0 * M o q) = fun x => m o q * max (M o x) 0 :=
        Continuous.ext_on hSd (((m o).continuous.max continuous_const).mul continuous_const)
          (continuous_const.mul ((M o).continuous.max continuous_const)) fun x hxS => hx x hxS
      refine ⟨m o q / M o q, div_pos hmq hMq, fun x => ?_⟩
      have h := congrFun hext x
      have hx' : max (m o x) 0 = m o q / M o q * max (M o x) 0 := by
        field_simp
        linarith
      rw [← ofReal_max_zero (m o x), hx', ENNReal.ofReal_mul (div_pos hmq hMq).le,
        ofReal_max_zero]
  · rintro o ⟨b₁, b₂, I, hb₁, hb₂, hI⟩
    by_cases hpos : ∃ q ∈ S, 0 < m o q
    · obtain ⟨q, hqS, hmq⟩ := hpos
      have hmq' : ENNReal.ofReal (m o q) ≠ 0 := (ENNReal.ofReal_pos.mpr hmq).ne'
      have hIq : I q ≠ 0 := by
        intro h; apply hmq'; rw [(hI q).1, h, mul_zero]
      have hMq : 0 < M o q := by
        have : ENNReal.ofReal (M o q) ≠ 0 := by
          rw [(hI q).2]
          exact mul_ne_zero (ENNReal.ofReal_pos.mpr hb₂).ne' hIq
        exact ENNReal.ofReal_pos.mp (pos_iff_ne_zero.mpr this)
      refine Or.inr ?_
      simp only [G₂, mem_iUnion, mem_inter_iff, mem_iInter, mem_ofPred_eq]
      refine ⟨q, hqS, ⟨hmq, hMq⟩, fun x _ => ?_⟩
      have hE : ENNReal.ofReal (m o x) * ENNReal.ofReal (M o q) =
          ENNReal.ofReal (m o q) * ENNReal.ofReal (M o x) := by
        rw [(hI x).1, (hI q).2, (hI q).1, (hI x).2]; ring
      rw [← ofReal_max_zero (m o x), ← ofReal_max_zero (M o x),
        ← ENNReal.ofReal_mul (le_max_right _ _), ← ENNReal.ofReal_mul hmq.le] at hE
      exact (ENNReal.ofReal_eq_ofReal_iff (mul_nonneg (le_max_right _ _) hMq.le)
        (mul_nonneg hmq.le (le_max_right _ _))).mp hE
    · push Not at hpos
      refine Or.inl ?_
      simp only [G₁, mem_iInter, mem_inter_iff, mem_ofPred_eq]
      intro x hxS
      refine ⟨hpos x hxS, ?_⟩
      by_contra hMx
      rw [not_le] at hMx
      have hm0 : ENNReal.ofReal (m o x) = 0 := ENNReal.ofReal_of_nonpos (hpos x hxS)
      have hIx : I x = 0 := by
        rw [(hI x).1] at hm0
        exact (mul_eq_zero.mp hm0).resolve_left
          (ENNReal.ofReal_pos.mpr hb₁).ne'
      have : ENNReal.ofReal (M o x) = 0 := by rw [(hI x).2, hIx, mul_zero]
      rw [ENNReal.ofReal_eq_zero] at this
      linarith

end LatticeProb
