import LatticeProb.Prob.Percolation.OpenComponentTranslationIso
import LatticeProb.Prob.Percolation.CorrectedPlaneGrowth

/-!
# Translation of corrected planes

Inverse composition preserves the prescribed slope on every actual component. Euclidean
ball enlargement and the constant slope displacement control the full real-radius tail.
The harmonic-and-tail characterization recovers the entire source A₁ requirement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb.Percolation

open scoped BigOperators

noncomputable section

variable {d : ℕ} {ω : Configuration d}

private theorem embedding_add (x z : Vertex d) :
    latticeEuclideanEmbedding (x + z) =
      latticeEuclideanEmbedding x + latticeEuclideanEmbedding z := by
  ext i
  exact Int.cast_add _ _

private theorem embedding_zero : latticeEuclideanEmbedding (0 : Vertex d) = 0 := by
  ext i
  exact Int.cast_zero

private theorem slope_translation {ω' : Configuration d} (C : OpenComponent ω)
    (D : OpenComponent ω') (e : C ≃ D) (z : Vertex d)
    (he : ∀ x, (e x).val = x.val + z) (q : Fin d → ℝ) (x : C) :
    componentSlope D q (e x) = componentSlope C q x + ∑ i, q i * (z i : ℝ) := by
  simp only [componentSlope, he, Pi.add_apply, Int.cast_add, mul_add, Finset.sum_add_distrib]

private theorem slope_asymptotics_transport {ω' : Configuration d} (C : OpenComponent ω)
    (D : OpenComponent ω') (e : C ≃ D) (z : Vertex d)
    (he : ∀ x, (e x).val = x.val + z) (q : Fin d → ℝ) (u : C → ℝ)
    (hu : componentSlopeAsymptotics C q u) :
    componentSlopeAsymptotics D q (fun y => u (e.symm y)) := by
  intro ε hε
  obtain ⟨R₀, _, htail⟩ := hu (ε / 4) (by positivity)
  let a := ‖latticeEuclideanEmbedding z‖
  let b := |∑ i, q i * (z i : ℝ)|
  refine ⟨max 1 (max R₀ (max a (2 * b / ε))),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro R hR y hy
  have hR₀ : R₀ ≤ R := (le_max_left _ _).trans ((le_max_right _ _).trans hR)
  have ha : a ≤ R := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hR))
  have hb : 2 * b / ε ≤ R := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hR))
  have hb' : 2 * b ≤ ε * R := by
    have := (div_le_iff₀ hε).mp hb
    linarith
  have hRp : 0 < R := zero_lt_one.trans_le ((le_max_left _ _).trans hR)
  have hrad : (e.symm y) ∈ componentEuclideanBall C 0 (R + a) := by
    rw [mem_componentEuclideanBall, embedding_zero, dist_zero_right]
    have hy' := (mem_componentEuclideanBall D 0 R y).mp hy
    rw [embedding_zero, dist_zero_right] at hy'
    have hv := he (e.symm y)
    rw [e.apply_symm_apply] at hv
    have hn := norm_sub_le (latticeEuclideanEmbedding y.val) (latticeEuclideanEmbedding z)
    have hid : latticeEuclideanEmbedding (e.symm y).val =
        latticeEuclideanEmbedding y.val - latticeEuclideanEmbedding z := by
      rw [hv, embedding_add, add_sub_cancel_right]
    rw [hid]
    dsimp only [a]
    linarith
  have hs := htail (R + a) (hR₀.trans (le_add_of_nonneg_right (norm_nonneg _)))
    (e.symm y) hrad
  have hshift := slope_translation C D e z he q (e.symm y)
  rw [e.apply_symm_apply] at hshift
  calc
    |u (e.symm y) - componentSlope D q y| =
        |(u (e.symm y) - componentSlope C q (e.symm y)) -
          ∑ i, q i * (z i : ℝ)| := by rw [hshift]; congr 1; ring
    _ ≤ |u (e.symm y) - componentSlope C q (e.symm y)| + b := abs_sub _ _
    _ ≤ (ε / 4) * (R + a) + b := add_le_add hs (le_refl b)
    _ ≤ ε * R := by nlinarith

/-- The full uniform slope tail is invariant under literal inverse vertex composition. -/
theorem componentSlopeAsymptotics_translation_iff (z : Vertex d) (C : OpenComponent ω)
    (q : Fin d → ℝ) (u : C → ℝ) :
    componentSlopeAsymptotics (openComponentTranslation z ω C) q
      (fun y => u ((openComponentTranslationIso z C).symm y)) ↔
    componentSlopeAsymptotics C q u := by
  let D := openComponentTranslation z ω C
  let e := (openComponentTranslationIso z C).toEquiv
  constructor
  · intro h
    have he (y : D) : (e.symm y).val = y.val + -z := by
      exact sub_eq_add_neg _ _
    have ht := slope_asymptotics_transport D C e.symm (-z) he q
      (fun y => u (e.symm y)) h
    simpa only [Equiv.symm_symm, e.symm_apply_apply] using ht
  · exact slope_asymptotics_transport C D e z (fun _ => rfl) q u

/-- The entire source corrected-plane predicate, including A₁, is translation invariant. -/
theorem isCorrectedPlane_translation_iff (z : Vertex d) (C : OpenComponent ω)
    (q : Fin d → ℝ) (u : C → ℝ) :
    IsCorrectedPlane (openComponentTranslation z ω C) q
      (fun y => u ((openComponentTranslationIso z C).symm y)) ↔
    IsCorrectedPlane C q u := by
  rw [isCorrectedPlane_iff_harmonic_and_slope_asymptotics,
    isCorrectedPlane_iff_harmonic_and_slope_asymptotics,
    componentSlopeAsymptotics_translation_iff]
  have hh : (∀ y, componentLaplacian (openComponentTranslation z ω C)
      (fun y => u ((openComponentTranslationIso z C).symm y)) y = 0) ↔
      (∀ x, componentLaplacian C u x = 0) := by
    constructor
    · intro h x
      rw [← componentLaplacian_translation z C u x]
      exact h _
    · intro h y
      obtain ⟨x, rfl⟩ := (openComponentTranslationIso z C).surjective y
      rw [componentLaplacian_translation]
      exact h x
  exact and_congr_left (fun _ => hh)

/-- Inverse composition preserves the value at the actual translated root. -/
theorem correctedPlane_translation_root (z : Vertex d) (C : OpenComponent ω)
    (u : C → ℝ) (a : C) :
    u ((openComponentTranslationIso z C).symm (openComponentTranslationIso z C a)) =
      u a := congrArg u ((openComponentTranslationIso z C).symm_apply_apply a)

/-- Existence of a corrected plane with integer gradients is invariant under translation. -/
theorem exists_integer_gradient_correctedPlane_translation_iff (z : Vertex d)
    (C : OpenComponent ω) (q : Fin d → ℝ) :
    (∃ v : openComponentTranslation z ω C → ℝ,
      IsCorrectedPlane (openComponentTranslation z ω C) q v ∧
      ∀ x y, (componentGraph (openComponentTranslation z ω C)).Adj x y →
        ∃ n : ℤ, v y - v x = (n : ℝ)) ↔
    (∃ u : C → ℝ, IsCorrectedPlane C q u ∧
      ∀ x y, (componentGraph C).Adj x y → ∃ n : ℤ, u y - u x = (n : ℝ)) := by
  let e := openComponentTranslationIso z C
  constructor
  · rintro ⟨v, hv, hi⟩
    let u : C → ℝ := fun x => v (e x)
    have he : (fun y => u (e.symm y)) = v := by
      funext y
      exact congrArg v (e.apply_symm_apply y)
    refine ⟨u, (isCorrectedPlane_translation_iff z C q u).mp ?_, ?_⟩
    · change IsCorrectedPlane _ q (fun y => u (e.symm y))
      rw [he]
      exact hv
    · apply (component_integer_gradient_translation_iff z C u).mp
      change ∀ x y, (componentGraph _).Adj x y →
        ∃ n : ℤ, (fun y => u (e.symm y)) y - (fun y => u (e.symm y)) x = (n : ℝ)
      rw [he]
      exact hi
  · rintro ⟨u, hu, hi⟩
    exact ⟨(fun y => u (e.symm y)),
      (isCorrectedPlane_translation_iff z C q u).mpr hu,
      (component_integer_gradient_translation_iff z C u).mpr hi⟩

end

end LatticeProb.Percolation
