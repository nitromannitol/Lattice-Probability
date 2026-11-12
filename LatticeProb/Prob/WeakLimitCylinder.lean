/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib

/-!
# Bounded Lipschitz cylinder functions on spaces of continuous functions

For a topological space `X`, a *bounded Lipschitz cylinder functional* is a measurable function
`Φ : (X → ℝ) → ℝ` which is bounded and for which there are a finite set `I ⊆ X` and a constant `K`
with `|Φ g - Φ g'| ≤ K r` whenever `|g t - g' t| ≤ r` for all `t ∈ I`.  Such a functional depends
only on the values of `g` on `I`, is Lipschitz for the supremum distance of these values, and its
restriction to `C(X, ℝ)` is continuous for the compact-open topology.

The bounded Lipschitz cylinder functions form a star subalgebra of `C(X, ℝ) →ᵇ ℝ` which separates
points.  Together with a tightness statement this is what determines a weak limit of probability
measures on `C(X, ℝ)`.

* `LatticeProb.IsLipCylinder`: the predicate on functionals `Φ : (X → ℝ) → ℝ`.
* `LatticeProb.lipCylinderSubalgebra`: the star subalgebra of `C(X, ℝ) →ᵇ ℝ`.
* `LatticeProb.separatesPoints_lipCylinderSubalgebra`: the subalgebra separates points.
-/

open Filter Topology BoundedContinuousFunction

namespace LatticeProb

section Cylinder

variable {X : Type*}

/-- A bounded Lipschitz cylinder functional on `X → ℝ`: measurable, bounded by `M`, and
`K`-Lipschitz for the supremum distance of the values on a finite set `I`. -/
def IsLipCylinder (Φ : (X → ℝ) → ℝ) : Prop :=
  Measurable Φ ∧ ∃ (I : Finset X) (K M : ℝ), 0 ≤ K ∧ (∀ g, |Φ g| ≤ M) ∧
    ∀ (g g' : X → ℝ) (r : ℝ), 0 ≤ r → (∀ t ∈ I, |g t - g' t| ≤ r) → |Φ g - Φ g'| ≤ K * r

theorem IsLipCylinder.continuous [TopologicalSpace X] {Φ : (X → ℝ) → ℝ} (hΦ : IsLipCylinder Φ) :
    Continuous fun w : C(X, ℝ) => Φ w := by
  obtain ⟨-, I, K, M, hK, -, hlip⟩ := hΦ
  refine continuous_iff_continuousAt.2 fun w0 => ?_
  have hcont : Continuous fun w : C(X, ℝ) => K * ∑ t ∈ I, |w t - w0 t| := by
    fun_prop
  have h0 : (fun w : C(X, ℝ) => K * ∑ t ∈ I, |w t - w0 t|) w0 = 0 := by simp
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) (fun w => ?_)
    (by simpa [h0] using hcont.tendsto w0))
  rw [Real.dist_eq]
  exact hlip w w0 _ (Finset.sum_nonneg fun _ _ => abs_nonneg _)
    fun t ht => Finset.single_le_sum (f := fun t => |w t - w0 t|) (fun _ _ => abs_nonneg _) ht

theorem isLipCylinder_const (c : ℝ) : IsLipCylinder (fun _ : X → ℝ => c) :=
  ⟨measurable_const, ∅, 0, |c|, le_rfl, fun _ => le_rfl, fun g g' r _ _ => by simp⟩

theorem IsLipCylinder.add {Φ Ψ : (X → ℝ) → ℝ} (hΦ : IsLipCylinder Φ) (hΨ : IsLipCylinder Ψ) :
    IsLipCylinder (Φ + Ψ) := by
  classical
  obtain ⟨hmΦ, I, K, M, hK, hM, hlip⟩ := hΦ
  obtain ⟨hmΨ, J, L, N, hL, hN, hlip'⟩ := hΨ
  refine ⟨hmΦ.add hmΨ, I ∪ J, K + L, M + N, add_nonneg hK hL, fun g => ?_, fun g g' r hr h => ?_⟩
  · exact (abs_add_le _ _).trans (add_le_add (hM g) (hN g))
  · have h1 := hlip g g' r hr fun t ht => h t (Finset.mem_union_left _ ht)
    have h2 := hlip' g g' r hr fun t ht => h t (Finset.mem_union_right _ ht)
    calc |(Φ + Ψ) g - (Φ + Ψ) g'| = |(Φ g - Φ g') + (Ψ g - Ψ g')| := by
          simp only [Pi.add_apply]; ring_nf
      _ ≤ |Φ g - Φ g'| + |Ψ g - Ψ g'| := abs_add_le _ _
      _ ≤ (K + L) * r := by linarith

theorem IsLipCylinder.mul {Φ Ψ : (X → ℝ) → ℝ} (hΦ : IsLipCylinder Φ) (hΨ : IsLipCylinder Ψ) :
    IsLipCylinder (Φ * Ψ) := by
  classical
  obtain ⟨hmΦ, I, K, M, hK, hM, hlip⟩ := hΦ
  obtain ⟨hmΨ, J, L, N, hL, hN, hlip'⟩ := hΨ
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have hN0 : 0 ≤ N := (abs_nonneg _).trans (hN 0)
  refine ⟨hmΦ.mul hmΨ, I ∪ J, M * L + N * K, M * N, by positivity, fun g => ?_,
    fun g g' r hr h => ?_⟩
  · simp only [Pi.mul_apply, abs_mul]
    exact mul_le_mul (hM g) (hN g) (abs_nonneg _) hM0
  · have h1 := hlip g g' r hr fun t ht => h t (Finset.mem_union_left _ ht)
    have h2 := hlip' g g' r hr fun t ht => h t (Finset.mem_union_right _ ht)
    have e : (Φ * Ψ) g - (Φ * Ψ) g' = Φ g * (Ψ g - Ψ g') + Ψ g' * (Φ g - Φ g') := by
      simp only [Pi.mul_apply]; ring
    rw [e]
    calc |Φ g * (Ψ g - Ψ g') + Ψ g' * (Φ g - Φ g')|
        ≤ |Φ g * (Ψ g - Ψ g')| + |Ψ g' * (Φ g - Φ g')| := abs_add_le _ _
      _ = |Φ g| * |Ψ g - Ψ g'| + |Ψ g'| * |Φ g - Φ g'| := by rw [abs_mul, abs_mul]
      _ ≤ M * (L * r) + N * (K * r) := by
          gcongr
          · exact hM g
          · exact hN g'
      _ = (M * L + N * K) * r := by ring

/-- The bounded Lipschitz cylinder functions form a star subalgebra of `C(X, ℝ) →ᵇ ℝ`: those
bounded continuous functions that are the restriction of a bounded Lipschitz cylinder functional. -/
def lipCylinderSubalgebra (X : Type*) [TopologicalSpace X] :
    StarSubalgebra ℝ (C(X, ℝ) →ᵇ ℝ) where
  carrier := {f | ∃ Φ : (X → ℝ) → ℝ, IsLipCylinder Φ ∧ ∀ w : C(X, ℝ), f w = Φ w}
  zero_mem' := ⟨fun _ => 0, isLipCylinder_const 0, fun _ => rfl⟩
  add_mem' := fun {f g} hf hg => by
    obtain ⟨Φ, hΦ, hf⟩ := hf
    obtain ⟨Ψ, hΨ, hg⟩ := hg
    exact ⟨Φ + Ψ, hΦ.add hΨ, fun w => by simp [hf w, hg w]⟩
  one_mem' := ⟨fun _ => 1, isLipCylinder_const 1, fun _ => rfl⟩
  mul_mem' := fun {f g} hf hg => by
    obtain ⟨Φ, hΦ, hf⟩ := hf
    obtain ⟨Ψ, hΨ, hg⟩ := hg
    exact ⟨Φ * Ψ, hΦ.mul hΨ, fun w => by simp [hf w, hg w]⟩
  algebraMap_mem' := fun r =>
    ⟨fun _ => r, isLipCylinder_const r, fun w => by simp [BoundedContinuousFunction.algebraMap_apply]⟩
  star_mem' := fun {f} hf => by
    obtain ⟨Φ, hΦ, hf⟩ := hf
    exact ⟨Φ, hΦ, fun w => by simpa using hf w⟩

/-- A bounded Lipschitz function of one evaluation is a cylinder functional. -/
theorem isLipCylinder_comp_eval (t : X) {φ : ℝ → ℝ} {K : NNReal} (hφ : LipschitzWith K φ) {M : ℝ}
    (hM : ∀ x, |φ x| ≤ M) : IsLipCylinder (fun g : X → ℝ => φ (g t)) := by
  refine ⟨hφ.continuous.measurable.comp (measurable_pi_apply t), {t}, K, M, K.2, fun g => hM _,
    fun g g' r hr h => ?_⟩
  have := hφ.dist_le_mul (g t) (g' t)
  rw [Real.dist_eq, Real.dist_eq] at this
  calc |φ (g t) - φ (g' t)| ≤ K * |g t - g' t| := this
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
  have hcyl : IsLipCylinder (fun g : X → ℝ => φ (g t)) := isLipCylinder_comp_eval t hφ hb
  let F : C(X, ℝ) →ᵇ ℝ := BoundedContinuousFunction.mkOfBound
    ⟨fun v : C(X, ℝ) => φ (v t), hcyl.continuous⟩ (2 * N) (fun v v' => by
      have h1 := hb (v t)
      have h2 := hb (v' t)
      rw [Real.dist_eq]
      have := abs_sub_le (φ (v t)) 0 (φ (v' t))
      simp only [sub_zero, zero_sub, abs_neg] at this
      show |φ (v t) - φ (v' t)| ≤ 2 * N
      linarith)
  have hF : F ∈ lipCylinderSubalgebra X := ⟨fun g => φ (g t), hcyl, fun _ => rfl⟩
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
