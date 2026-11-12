import Mathlib
import LatticeProb.LQG.InternalMetricCrossings
import LatticeProb.Bonanno.LQGMetric.Topo.RectCross

/-!
# Trimming a path in a strip to a crossing of a rectangle

A path `P` that stays in a horizontal strip `{y₀ ≤ Im z ≤ y₁}` and goes from `{Re z ≤ x₀}` to
`{x₁ ≤ Re z}` contains a subpath that is a left-right crossing of the closed rectangle
`[x₀, x₁] × [y₀, y₁]`: take the first time `t₁` at which `Re P = x₁`, and the last time `t₀ ≤ t₁` at
which `Re P = x₀`. The subpath is no longer than `P` for any function `D`.  The same holds for a path in
a vertical strip going from `{y₁ ≤ Im z}` to `{Im z ≤ y₀}`, with top-bottom crossings.

* `restrictPath`: the restriction `P|[s, t]` of a path, parametrized affinely on `[0, 1]`;
* `pathLength_restrictPath_le`: its `D`-length is at most the `D`-length of `P` on `[s, t]`;
* `exists_leftRightCrossing_pathLength_le`: the trimming lemma for left-right crossings;
* `exists_topBottomCrossing_pathLength_le`: the trimming lemma for top-bottom crossings.
-/

open Set
open scoped ENNReal unitInterval

namespace LatticeProb.LQG

/-- The restriction `P|[s, t]` of a path `P`, reparametrized affinely onto `[0, 1]`. -/
noncomputable def restrictPath {a b : ℂ} (P : Path a b) (s t : ℝ) : Path (P.extend s) (P.extend t) where
  toFun u := P.extend (s + (u : ℝ) * (t - s))
  continuous_toFun := P.continuous_extend.comp (by fun_prop)
  source' := by simp
  target' := by simp

theorem restrictPath_apply {a b : ℂ} (P : Path a b) (s t : ℝ) (u : I) :
    restrictPath P s t u = P.extend (s + (u : ℝ) * (t - s)) := rfl

/-- The `D`-length of `P|[s, t]` is at most the `D`-length of `P` on `[s, t]`. -/
theorem pathLength_restrictPath_le (D : ℂ → ℂ → ℝ) {a b : ℂ} (P : Path a b) {s t : ℝ} (hst : s ≤ t) :
    pathLength D (restrictPath P s t) ≤ curveLength D P.extend s t := by
  unfold pathLength curveLength
  refine iSup_le fun q => ?_
  have hmem : ∀ i, s + q.2.1 i * (t - s) ∈ Icc s t := fun i => by
    have h := q.2.2.2 i
    exact ⟨by nlinarith [h.1, sub_nonneg.2 hst], by nlinarith [h.2, sub_nonneg.2 hst]⟩
  refine le_iSup_of_le (⟨q.1, fun i => s + q.2.1 i * (t - s), fun i j hij => ?_, hmem⟩ :
    ℕ × { u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc s t }) ?_
  · have := q.2.2.1 hij
    nlinarith [sub_nonneg.2 hst]
  · refine le_of_eq (Finset.sum_congr rfl fun i _ => ?_)
    have h1 : (restrictPath P s t).extend (q.2.1 (i + 1)) = P.extend (s + q.2.1 (i + 1) * (t - s)) := by
      rw [Path.extend_apply _ (q.2.2.2 (i + 1))]; rfl
    have h0 : (restrictPath P s t).extend (q.2.1 i) = P.extend (s + q.2.1 i * (t - s)) := by
      rw [Path.extend_apply _ (q.2.2.2 i)]; rfl
    rw [h1, h0]

/-- **Trimming to a left-right crossing.** A path `P` in the horizontal strip `y₀ ≤ Im z ≤ y₁` from `{Re z ≤ x₀}`
to `{x₁ ≤ Re z}` contains a subpath that is a left-right crossing of the closed rectangle `[x₀, x₁] × [y₀, y₁]`
and that has `D`-length at most the `D`-length of `P`. -/
theorem exists_leftRightCrossing_pathLength_le (D : ℂ → ℂ → ℝ) {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) {a b : ℂ}
    (P : Path a b) (hP : ∀ t, (P t).im ∈ Icc y₀ y₁) (ha : a.re ≤ x₀) (hb : x₁ ≤ b.re) :
    ∃ (u v : ℂ) (Q : Path u v), IsLeftRightCrossing x₀ x₁ y₀ y₁ Q ∧ pathLength D Q ≤ pathLength D P := by
  obtain ⟨s, t, hs, hst, ht, hfs, hft, hrange⟩ := LQGMetric.RectCross.exists_sub_crossing
    (f := fun u => (P.extend u).re) (α := 0) (β := 1) zero_le_one
    (Complex.continuous_re.comp P.continuous_extend).continuousOn hx (by simpa using ha) (by simpa using hb)
  refine ⟨_, _, restrictPath P s t, ⟨fun u => ?_, hfs, hft⟩, ?_⟩
  · have hv : s + (u : ℝ) * (t - s) ∈ Icc s t :=
      ⟨by nlinarith [u.2.1, sub_nonneg.2 hst], by nlinarith [u.2.2, sub_nonneg.2 hst]⟩
    have h01 : s + (u : ℝ) * (t - s) ∈ Icc (0 : ℝ) 1 := ⟨hs.trans hv.1, hv.2.trans ht⟩
    rw [restrictPath_apply]
    refine Complex.mem_reProdIm.2 ⟨hrange _ hv, ?_⟩
    rw [Path.extend_apply _ h01]
    exact hP _
  · exact (pathLength_restrictPath_le D P hst).trans (curveLength_mono_Icc D P.extend hs ht)

/-- **Trimming to a top-bottom crossing.** A path `P` in the vertical strip `x₀ ≤ Re z ≤ x₁` from `{y₁ ≤ Im z}` to
`{Im z ≤ y₀}` contains a subpath that is a top-bottom crossing of the closed rectangle `[x₀, x₁] × [y₀, y₁]` and
that has `D`-length at most the `D`-length of `P`. -/
theorem exists_topBottomCrossing_pathLength_le (D : ℂ → ℂ → ℝ) {x₀ x₁ y₀ y₁ : ℝ} (hy : y₀ ≤ y₁) {a b : ℂ}
    (P : Path a b) (hP : ∀ t, (P t).re ∈ Icc x₀ x₁) (ha : y₁ ≤ a.im) (hb : b.im ≤ y₀) :
    ∃ (u v : ℂ) (Q : Path u v), IsTopBottomCrossing x₀ x₁ y₀ y₁ Q ∧ pathLength D Q ≤ pathLength D P := by
  obtain ⟨s, t, hs, hst, ht, hfs, hft, hrange⟩ := LQGMetric.RectCross.exists_sub_crossing'
    (f := fun u => (P.extend u).im) (α := 0) (β := 1) zero_le_one
    (Complex.continuous_im.comp P.continuous_extend).continuousOn hy (by simpa using ha) (by simpa using hb)
  refine ⟨_, _, restrictPath P s t, ⟨fun u => ?_, hfs, hft⟩, ?_⟩
  · have hv : s + (u : ℝ) * (t - s) ∈ Icc s t :=
      ⟨by nlinarith [u.2.1, sub_nonneg.2 hst], by nlinarith [u.2.2, sub_nonneg.2 hst]⟩
    have h01 : s + (u : ℝ) * (t - s) ∈ Icc (0 : ℝ) 1 := ⟨hs.trans hv.1, hv.2.trans ht⟩
    rw [restrictPath_apply]
    refine Complex.mem_reProdIm.2 ⟨?_, hrange _ hv⟩
    rw [Path.extend_apply _ h01]
    exact hP _
  · exact (pathLength_restrictPath_le D P hst).trans (curveLength_mono_Icc D P.extend hs ht)

end LatticeProb.LQG
