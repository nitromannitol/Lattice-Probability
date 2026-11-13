import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Subgradients of convex functions

For a function `f : E → ℝ` on a real inner product space `E`, a vector `g` is a *subgradient* of `f`
at `x` when the affine function `y ↦ f x + ⟪g, y - x⟫` lies below `f` everywhere. This file develops
the basic facts about subgradients that are needed to run the resolvent argument for convex functions
on a finite-dimensional space.

## Main results

* `LatticeProb.ConvexAnalysis.IsSubgradientAt`: the definition.
* `LatticeProb.ConvexAnalysis.exists_isSubgradientAt`: a convex function on a finite-dimensional
  space has a subgradient at every point (separation of the strict epigraph from a boundary point).
* `LatticeProb.ConvexAnalysis.IsSubgradientAt.inner_sub_nonneg`: monotonicity of subgradients.
* `LatticeProb.ConvexAnalysis.exists_bound_isSubgradientAt`: subgradients are locally bounded.
* `LatticeProb.ConvexAnalysis.IsSubgradientAt.eq_of_hasGradientAt`: at a point of differentiability
  the only subgradient is the gradient.
* `LatticeProb.ConvexAnalysis.tendsto_isSubgradientAt`: subgradients at points near a point of
  differentiability are close to the gradient there.
-/

open Set Topology Metric
open scoped InnerProductSpace

namespace LatticeProb.ConvexAnalysis

section Basic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {f : E → ℝ} {x z g p : E}

/-- `g` is a subgradient of `f` at `x`: the affine function `y ↦ f x + ⟪g, y - x⟫` lies below `f`. -/
def IsSubgradientAt (f : E → ℝ) (x g : E) : Prop :=
  ∀ y, f x + ⟪g, y - x⟫_ℝ ≤ f y

/-- Subgradients are monotone: `⟪g - g', x - x'⟫ ≥ 0` for subgradients `g` at `x` and `g'` at `x'`. -/
theorem IsSubgradientAt.inner_sub_nonneg {x' g' : E} (h : IsSubgradientAt f x g)
    (h' : IsSubgradientAt f x' g') : 0 ≤ ⟪g - g', x - x'⟫_ℝ := by
  have h1 := h x'
  have h2 := h' x
  have e1 : ⟪g, x' - x⟫_ℝ = -⟪g, x - x'⟫_ℝ := by rw [← inner_neg_right, neg_sub]
  have e2 : ⟪g', x - x'⟫_ℝ = -⟪g', x' - x⟫_ℝ := by rw [← inner_neg_right, neg_sub]
  rw [inner_sub_left]
  linarith

/-- If `g` is a subgradient of `f` at `z` and `g ≠ p`, then a step of length `t` in the unit direction
`(g - p) / ‖g - p‖` shows `t * ‖g - p‖ ≤ f (z + t • w) - f z - t * ⟪p, w⟫`. -/
theorem IsSubgradientAt.exists_unit_mul_norm_le (h : IsSubgradientAt f z g) (hne : g ≠ p) {t : ℝ} :
    ∃ w : E, ‖w‖ = 1 ∧ t * ‖g - p‖ ≤ f (z + t • w) - f z - t * ⟪p, w⟫_ℝ := by
  have hn : 0 < ‖g - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  set w : E := ‖g - p‖⁻¹ • (g - p) with hw
  have hw1 : ‖w‖ = 1 := by
    rw [hw, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
  have e : ⟪g - p, w⟫_ℝ = ‖g - p‖ := by
    rw [hw, real_inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  have e2 : ⟪g, w⟫_ℝ = ‖g - p‖ + ⟪p, w⟫_ℝ := by
    rw [← e, ← inner_add_left, sub_add_cancel]
  refine ⟨w, hw1, ?_⟩
  have h1 := h (z + t • w)
  rw [add_sub_cancel_left, real_inner_smul_right, e2] at h1
  linarith

variable [CompleteSpace E]

/-- Quantitative form of differentiability at `x` with gradient `p`. -/
theorem exists_forall_abs_le_of_hasGradientAt (hp : HasGradientAt f p x) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ρ > 0, ∀ y, ‖y - x‖ ≤ ρ → |f y - f x - ⟪p, y - x⟫_ℝ| ≤ δ * ‖y - x‖ := by
  have h := (hasGradientAt_iff_hasFDerivAt.mp hp).isLittleO.def hδ
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp h
  refine ⟨ε / 2, by positivity, fun y hy => ?_⟩
  have := hball (y := y) (by rw [dist_eq_norm]; linarith)
  simpa [InnerProductSpace.toDual_apply_apply] using this

/-- At a point where `f` has gradient `p`, the only subgradient is `p`. -/
theorem IsSubgradientAt.eq_of_hasGradientAt (h : IsSubgradientAt f x g) (hp : HasGradientAt f p x) :
    g = p := by
  by_contra hne
  have hn : 0 < ‖g - p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  obtain ⟨ρ, hρ, hR⟩ := exists_forall_abs_le_of_hasGradientAt hp (half_pos hn)
  obtain ⟨w, hw, hle⟩ := h.exists_unit_mul_norm_le hne (t := ρ)
  have hy : x + ρ • w - x = ρ • w := add_sub_cancel_left x _
  have hnorm : ‖ρ • w‖ = ρ := by rw [norm_smul, hw, Real.norm_eq_abs, abs_of_pos hρ, mul_one]
  have hb := hR (x + ρ • w) (by rw [hy, hnorm])
  rw [hy, hnorm, real_inner_smul_right] at hb
  have := (abs_le.mp hb).2
  nlinarith [mul_pos hρ hn]

/-- Subgradients at points near a point `x` of differentiability are close to the gradient at `x`.
No convexity is needed. -/
theorem exists_norm_sub_lt_of_hasGradientAt (hp : HasGradientAt f p x) {ε : ℝ} (hε : 0 < ε) :
    ∃ r > 0, ∀ z g, dist z x < r → IsSubgradientAt f z g → ‖g - p‖ < ε := by
  obtain ⟨ρ, hρ, hR⟩ := exists_forall_abs_le_of_hasGradientAt hp (show 0 < ε / 4 by positivity)
  refine ⟨ρ / 2, by positivity, fun z g hz hg => ?_⟩
  by_cases hgp : g = p
  · rw [hgp, sub_self, norm_zero]
    exact hε
  have hz' : ‖z - x‖ < ρ / 2 := by rwa [dist_eq_norm] at hz
  obtain ⟨w, hw, hle⟩ := hg.exists_unit_mul_norm_le hgp (t := ρ / 2)
  have hsplit : z + (ρ / 2) • w - x = (z - x) + (ρ / 2) • w := by abel
  have hnorm : ‖(ρ / 2) • w‖ = ρ / 2 := by
    rw [norm_smul, hw, Real.norm_eq_abs, abs_of_pos (by positivity), mul_one]
  have hstep : ‖z + (ρ / 2) • w - x‖ ≤ ‖z - x‖ + ρ / 2 := by
    rw [hsplit]
    exact (norm_add_le _ _).trans (by rw [hnorm])
  have hA := hR (z + (ρ / 2) • w) (by linarith)
  have hB := hR z (by linarith)
  have hinner : ⟪p, z + (ρ / 2) • w - x⟫_ℝ = ⟪p, z - x⟫_ℝ + ρ / 2 * ⟪p, w⟫_ℝ := by
    rw [hsplit, inner_add_right, real_inner_smul_right]
  rw [hinner] at hA
  have hA' := (abs_le.mp hA).2
  have hB' := (abs_le.mp hB).1
  have hδ : (0 : ℝ) ≤ ε / 4 := by positivity
  have h1 : ε / 4 * ‖z + (ρ / 2) • w - x‖ ≤ ε / 4 * (‖z - x‖ + ρ / 2) :=
    mul_le_mul_of_nonneg_left hstep hδ
  have h2 : ε / 4 * ‖z - x‖ ≤ ε / 4 * (ρ / 2) :=
    mul_le_mul_of_nonneg_left hz'.le hδ
  have h3 : ε / 4 * (‖z - x‖ + ρ / 2) ≤ ε / 4 * ρ :=
    mul_le_mul_of_nonneg_left (by linarith) hδ
  by_contra hnot
  have hnot := not_lt.mp hnot
  nlinarith [mul_pos hρ (show 0 < ‖g - p‖ from lt_of_lt_of_le hε hnot)]

/-- Subgradients at points near a point `x` of differentiability of a convex function are close to the
gradient at `x`. The convexity hypothesis is not used by the proof: see
`exists_norm_sub_lt_of_hasGradientAt`. -/
theorem tendsto_isSubgradientAt (_hf : ConvexOn ℝ Set.univ f) (hp : HasGradientAt f p x) :
    ∀ ε > 0, ∃ r > 0, ∀ z, dist z x < r → ∀ g, IsSubgradientAt f z g → ‖g - p‖ < ε := by
  intro ε hε
  obtain ⟨r, hr, h⟩ := exists_norm_sub_lt_of_hasGradientAt hp hε
  exact ⟨r, hr, fun z hz g hg => h z g hz hg⟩

end Basic

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {f : E → ℝ}

/-- A convex function on a finite-dimensional space is continuous. -/
theorem continuous_of_convexOn_univ (hf : ConvexOn ℝ Set.univ f) : Continuous f :=
  continuousOn_univ.mp (hf.continuousOn isOpen_univ)

/-- A convex function on a finite-dimensional inner product space has a subgradient at every point. -/
theorem exists_isSubgradientAt (hf : ConvexOn ℝ Set.univ f) (x : E) :
    ∃ g, IsSubgradientAt f x g := by
  have hcont : Continuous f := continuous_of_convexOn_univ hf
  set S : Set (E × ℝ) := {q | f q.1 < q.2} with hS
  have hSconv : Convex ℝ S := by
    rw [convex_iff_forall_pos]
    rintro ⟨x₁, t₁⟩ h₁ ⟨x₂, t₂⟩ h₂ a b ha hb hab
    have h₁' : f x₁ < t₁ := h₁
    have h₂' : f x₂ < t₂ := h₂
    show f (a • x₁ + b • x₂) < a • t₁ + b • t₂
    calc f (a • x₁ + b • x₂) ≤ a • f x₁ + b • f x₂ :=
          hf.2 (Set.mem_univ x₁) (Set.mem_univ x₂) ha.le hb.le hab
      _ < a • t₁ + b • t₂ := by
          simp only [smul_eq_mul]
          exact add_lt_add (mul_lt_mul_of_pos_left h₁' ha) (mul_lt_mul_of_pos_left h₂' hb)
  have hSopen : IsOpen S := isOpen_lt (hcont.comp continuous_fst) continuous_snd
  have hx : (x, f x) ∉ S := fun h => lt_irrefl (f x) h
  obtain ⟨φ, hφ⟩ := geometric_hahn_banach_open_point hSconv hSopen hx
  set α : StrongDual ℝ E := φ.comp (ContinuousLinearMap.inl ℝ E ℝ) with hα
  set c : ℝ := φ (0, 1) with hc
  have hφ_eq : ∀ y t, φ (y, t) = α y + t * c := by
    intro y t
    have : (y, t) = (y, (0 : ℝ)) + t • ((0 : E), (1 : ℝ)) := by ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
    simp [hα, hc]
  have hcneg : c < 0 := by
    have h := hφ (x, f x + 1) (by simp [hS])
    rw [hφ_eq, hφ_eq] at h
    linarith
  have hk : 0 < -c := neg_pos.mpr hcneg
  have key : ∀ y, α y - α x ≤ -c * (f y - f x) := by
    intro y
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    obtain ⟨s, hs, hsε⟩ : ∃ s : ℝ, 0 < s ∧ -c * s = ε :=
      ⟨ε / -c, div_pos hε hk, by field_simp [hcneg.ne]⟩
    have h := hφ (y, f y + s) (by simp [hS, hs])
    rw [hφ_eq, hφ_eq] at h
    nlinarith
  refine ⟨(InnerProductSpace.toDual ℝ E).symm ((-c)⁻¹ • α), fun y => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply]
  have h1 := mul_le_mul_of_nonneg_left (key y) (inv_nonneg.mpr hk.le)
  rw [← mul_assoc, inv_mul_cancel₀ hk.ne', one_mul] at h1
  simp only [smul_apply, smul_eq_mul, map_sub]
  linarith

/-- Subgradients of a convex function are locally bounded. -/
theorem exists_bound_isSubgradientAt (hf : ConvexOn ℝ Set.univ f) (x : E) :
    ∃ r > 0, ∃ C, ∀ z, dist z x < r → ∀ g, IsSubgradientAt f z g → ‖g‖ ≤ C := by
  have hcont := continuous_of_convexOn_univ hf
  obtain ⟨M, hM⟩ := (isCompact_closedBall x 2).exists_bound_of_continuousOn hcont.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM x (mem_closedBall_self (by norm_num)))
  refine ⟨1, one_pos, 2 * M, fun z hz g hg => ?_⟩
  by_cases hg0 : g = 0
  · rw [hg0, norm_zero]
    linarith
  · obtain ⟨w, hw, hle⟩ := hg.exists_unit_mul_norm_le hg0 (p := 0) (t := 1)
    have hz' : z ∈ closedBall x 2 := by
      rw [mem_closedBall]
      linarith
    have hzw : z + (1 : ℝ) • w ∈ closedBall x 2 := by
      rw [mem_closedBall, dist_eq_norm]
      have : z + (1 : ℝ) • w - x = (z - x) + w := by rw [one_smul]; abel
      rw [this]
      have h3 : ‖z - x‖ < 1 := by rwa [dist_eq_norm] at hz
      calc ‖(z - x) + w‖ ≤ ‖z - x‖ + ‖w‖ := norm_add_le _ _
        _ ≤ 2 := by rw [hw]; linarith
    have h1 := abs_le.mp (by simpa [Real.norm_eq_abs] using hM z hz')
    have h2 := abs_le.mp (by simpa [Real.norm_eq_abs] using hM _ hzw)
    simp only [sub_zero, one_mul, one_smul, inner_zero_left, mul_zero] at hle
    linarith [h1.1, h1.2, h2.1, h2.2]

end FiniteDimensional

end LatticeProb.ConvexAnalysis
