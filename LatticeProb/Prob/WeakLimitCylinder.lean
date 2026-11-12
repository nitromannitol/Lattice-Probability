/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib

/-!
# Bounded Lipschitz cylinder functions on spaces of continuous functions

For a topological space `X`, a function `f : C(X, ℝ) → ℝ` is a *bounded Lipschitz cylinder function*
if it is bounded and there are a finite set `I ⊆ X` and a constant `K` with
`|f w - f w'| ≤ K r` whenever `|w t - w' t| ≤ r` for all `t ∈ I`.  Such a function depends only on
the values of `w` on `I`, is Lipschitz for the supremum distance of these values, and is continuous
for the compact-open topology.

The bounded Lipschitz cylinder functions form a star subalgebra of `C(X, ℝ) →ᵇ ℝ` which separates
points.  Together with a tightness statement this is what determines a weak limit of probability
measures on `C(X, ℝ)`.

* `LatticeProb.IsLipCylinder`: the predicate.
* `LatticeProb.lipCylinderSubalgebra`: the star subalgebra of `C(X, ℝ) →ᵇ ℝ`.
* `LatticeProb.separatesPoints_lipCylinderSubalgebra`: the subalgebra separates points.
-/

open Filter Topology BoundedContinuousFunction

namespace LatticeProb

section Cylinder

variable {X : Type*} [TopologicalSpace X]

/-- A bounded Lipschitz cylinder function on `C(X, ℝ)`: bounded by `M`, and `K`-Lipschitz for the
supremum distance of the values on a finite set `I`. -/
def IsLipCylinder (f : C(X, ℝ) → ℝ) : Prop :=
  ∃ (I : Finset X) (K M : ℝ), 0 ≤ K ∧ (∀ w, |f w| ≤ M) ∧
    ∀ (w w' : C(X, ℝ)) (r : ℝ), 0 ≤ r → (∀ t ∈ I, |w t - w' t| ≤ r) → |f w - f w'| ≤ K * r

theorem IsLipCylinder.continuous {f : C(X, ℝ) → ℝ} (hf : IsLipCylinder f) : Continuous f := by
  obtain ⟨I, K, M, hK, -, hlip⟩ := hf
  refine continuous_iff_continuousAt.2 fun w0 => ?_
  have hcont : Continuous fun w : C(X, ℝ) => K * ∑ t ∈ I, |w t - w0 t| := by
    fun_prop
  have h0 : (fun w : C(X, ℝ) => K * ∑ t ∈ I, |w t - w0 t|) w0 = 0 := by simp
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) (fun w => ?_)
    (by simpa [h0] using hcont.tendsto w0))
  rw [Real.dist_eq]
  exact hlip w w0 _ (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    fun t ht => Finset.single_le_sum (f := fun t => |w t - w0 t|) (fun _ _ => abs_nonneg _) ht

theorem isLipCylinder_const (c : ℝ) : IsLipCylinder (fun _ : C(X, ℝ) => c) :=
  ⟨∅, 0, |c|, le_rfl, fun _ => le_rfl, fun w w' r _ _ => by simp⟩

theorem IsLipCylinder.add {f g : C(X, ℝ) → ℝ} (hf : IsLipCylinder f) (hg : IsLipCylinder g) :
    IsLipCylinder (f + g) := by
  classical
  obtain ⟨I, K, M, hK, hM, hlip⟩ := hf
  obtain ⟨J, L, N, hL, hN, hlip'⟩ := hg
  refine ⟨I ∪ J, K + L, M + N, add_nonneg hK hL, fun w => ?_, fun w w' r hr h => ?_⟩
  · exact (abs_add_le _ _).trans (add_le_add (hM w) (hN w))
  · have h1 := hlip w w' r hr fun t ht => h t (Finset.mem_union_left _ ht)
    have h2 := hlip' w w' r hr fun t ht => h t (Finset.mem_union_right _ ht)
    calc |(f + g) w - (f + g) w'| = |(f w - f w') + (g w - g w')| := by
          simp only [Pi.add_apply]; ring_nf
      _ ≤ |f w - f w'| + |g w - g w'| := abs_add_le _ _
      _ ≤ (K + L) * r := by linarith

theorem IsLipCylinder.mul {f g : C(X, ℝ) → ℝ} (hf : IsLipCylinder f) (hg : IsLipCylinder g) :
    IsLipCylinder (f * g) := by
  classical
  obtain ⟨I, K, M, hK, hM, hlip⟩ := hf
  obtain ⟨J, L, N, hL, hN, hlip'⟩ := hg
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hN0 : 0 ≤ N := (abs_nonneg _).trans (hN 0)
  refine ⟨I ∪ J, M * L + N * K, M * N, by positivity, fun w => ?_, fun w w' r hr h => ?_⟩
  · simp only [Pi.mul_apply, abs_mul]
    exact mul_le_mul (hM w) (hN w) (abs_nonneg _) hM0
  · have h1 := hlip w w' r hr fun t ht => h t (Finset.mem_union_left _ ht)
    have h2 := hlip' w w' r hr fun t ht => h t (Finset.mem_union_right _ ht)
    have e : (f * g) w - (f * g) w' = f w * (g w - g w') + g w' * (f w - f w') := by
      simp only [Pi.mul_apply]; ring
    rw [e]
    calc |f w * (g w - g w') + g w' * (f w - f w')|
        ≤ |f w * (g w - g w')| + |g w' * (f w - f w')| := abs_add_le _ _
      _ = |f w| * |g w - g w'| + |g w'| * |f w - f w'| := by rw [abs_mul, abs_mul]
      _ ≤ M * (L * r) + N * (K * r) := by
          gcongr
          · exact hM w
          · exact hN w'
      _ = (M * L + N * K) * r := by ring

/-- The bounded Lipschitz cylinder functions form a star subalgebra of `C(X, ℝ) →ᵇ ℝ`. -/
def lipCylinderSubalgebra (X : Type*) [TopologicalSpace X] :
    StarSubalgebra ℝ (C(X, ℝ) →ᵇ ℝ) where
  carrier := {f | IsLipCylinder (f : C(X, ℝ) → ℝ)}
  zero_mem' := isLipCylinder_const 0
  add_mem' := fun {f g} hf hg => hf.add hg
  one_mem' := isLipCylinder_const 1
  mul_mem' := fun {f g} hf hg => hf.mul hg
  algebraMap_mem' := fun r => by
    have : ((algebraMap ℝ (C(X, ℝ) →ᵇ ℝ) r : C(X, ℝ) →ᵇ ℝ) : C(X, ℝ) → ℝ) = fun _ => r := by
      funext w; simp [BoundedContinuousFunction.algebraMap_apply]
    show IsLipCylinder _
    rw [this]; exact isLipCylinder_const r
  star_mem' := fun {f} hf => by simpa using hf

/-- A bounded Lipschitz function of one evaluation is a cylinder function. -/
theorem isLipCylinder_comp_eval (t : X) {φ : ℝ → ℝ} {K : NNReal} (hφ : LipschitzWith K φ) {M : ℝ}
    (hM : ∀ x, |φ x| ≤ M) : IsLipCylinder (fun w : C(X, ℝ) => φ (w t)) := by
  refine ⟨{t}, K, M, K.2, fun w => hM _, fun w w' r hr h => ?_⟩
  have := hφ.dist_le_mul (w t) (w' t)
  rw [Real.dist_eq, Real.dist_eq] at this
  calc |φ (w t) - φ (w' t)| ≤ K * |w t - w' t| := this
    _ ≤ K * r := mul_le_mul_of_nonneg_left (h t (Finset.mem_singleton_self t)) K.2

/-- The subalgebra of bounded Lipschitz cylinder functions separates points of `C(X, ℝ)`. -/
theorem separatesPoints_lipCylinderSubalgebra (X : Type*) [TopologicalSpace X] :
    ((lipCylinderSubalgebra X).map (toContinuousMapStarₐ ℝ)).SeparatesPoints := by
  intro w w' hne
  obtain ⟨t, ht⟩ : ∃ t, w t ≠ w' t := by
    by_contra h
    push Not at h
    exact hne (ContinuousMap.ext h)
  set N : ℝ := max |w t| |w' t| + 1 with hN
  let φ : ℝ → ℝ := fun x => max (min x N) (-N)
  have hφ : LipschitzWith 1 φ := (LipschitzWith.id.min_const N).max_const (-N)
  have hN0 : 0 ≤ N := by positivity
  have hb : ∀ x, |φ x| ≤ N := fun x => by
    rw [abs_le]
    refine ⟨le_max_right _ _, max_le (min_le_right _ _) (by linarith)⟩
  have hcyl : IsLipCylinder (fun v : C(X, ℝ) => φ (v t)) := isLipCylinder_comp_eval t hφ hb
  let F : C(X, ℝ) →ᵇ ℝ := BoundedContinuousFunction.mkOfBound
    ⟨fun v : C(X, ℝ) => φ (v t), hcyl.continuous⟩ (2 * N) (fun v v' => by
      have h1 := hb (v t)
      have h2 := hb (v' t)
      rw [Real.dist_eq]
      have := abs_sub_le (φ (v t)) 0 (φ (v' t))
      simp only [sub_zero, zero_sub, abs_neg] at this
      show |φ (v t) - φ (v' t)| ≤ 2 * N
      linarith)
  have hF : F ∈ lipCylinderSubalgebra X := hcyl
  refine ⟨F, ⟨(F : C(C(X, ℝ), ℝ)), ⟨F, hF, rfl⟩, rfl⟩, ?_⟩
  have h1 : φ (w t) = w t := by
    have a1 := le_abs_self (w t)
    have a2 := neg_abs_le (w t)
    have a3 := le_max_left |w t| |w' t|
    show max (min (w t) N) (-N) = w t
    rw [min_eq_left (by linarith), max_eq_left (by linarith)]
  have h2 : φ (w' t) = w' t := by
    have a1 := le_abs_self (w' t)
    have a2 := neg_abs_le (w' t)
    have a3 := le_max_right |w t| |w' t|
    show max (min (w' t) N) (-N) = w' t
    rw [min_eq_left (by linarith), max_eq_left (by linarith)]
  show φ (w t) ≠ φ (w' t)
  rw [h1, h2]; exact ht

end Cylinder

end LatticeProb
