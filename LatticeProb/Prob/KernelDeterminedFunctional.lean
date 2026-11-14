import Mathlib

/-!
# A jointly measurable determining functional for a family of couplings

Let `κ` be a Markov kernel from `α` to `X × ℝ` with `X` standard Borel.  Suppose that for every
parameter `a` the second coordinate of `κ a` is almost surely a measurable function `g a` of the
first coordinate (the function may depend on `a` in an arbitrary way).  Then the functions `g a` can
be chosen jointly measurably in `(a, x)`: there is a single measurable `G : α × X → ℝ` such that for
every `a`, almost surely under `κ a`, the second coordinate equals `G (a, ·)` of the first.

The proof disintegrates `κ` along its first marginal into a conditional kernel `κ.condKernel`, which
is a point mass at `g a x` for almost every `x`, and reads off the point mass from the mean of
`arctan`, which is a measurable function of `(a, x)` by measurability of kernel integrals.

## Main result

* `exists_measurable_of_kernel_ae_eq_fun`.
-/

open MeasureTheory ProbabilityTheory

namespace LatticeProb

variable {α X : Type*} [MeasurableSpace α] [MeasurableSpace X] [StandardBorelSpace X]

/-- **A jointly measurable determining functional.**  If for every parameter `a` the real
coordinate of a Markov kernel `κ a` on `X × ℝ` is almost surely a measurable function of the `X`
coordinate, then one measurable function `G : α × X → ℝ` serves for all `a` simultaneously. -/
theorem exists_measurable_of_kernel_ae_eq_fun (κ : Kernel α (X × ℝ)) [IsMarkovKernel κ]
    (h : ∀ a, ∃ g : X → ℝ, Measurable g ∧ ∀ᵐ p ∂(κ a), p.2 = g p.1) :
    ∃ G : α × X → ℝ, Measurable G ∧ ∀ a, ∀ᵐ p ∂(κ a), p.2 = G (a, p.1) := by
  classical
  refine ⟨fun q => Real.tan (∫ y, Real.arctan y ∂(κ.condKernel q)), ?_, ?_⟩
  · have hm : Measurable fun q : α × X => ∫ y, Real.arctan y ∂(κ.condKernel q) :=
      (StronglyMeasurable.integral_kernel (κ := κ.condKernel)
        Real.continuous_arctan.stronglyMeasurable).measurable
    have hs := Real.measurable_sin.comp hm
    have hc := Real.measurable_cos.comp hm
    simp only [Real.tan_eq_sin_div_cos]
    exact hs.div hc
  · intro a
    obtain ⟨g, hg, hga⟩ := h a
    have hcomp : (κ.fst ⊗ₖ κ.condKernel) a = κ a := by
      rw [Kernel.disintegrate κ κ.condKernel]
    have h2 : ∀ᵐ p ∂((κ.fst ⊗ₖ κ.condKernel) a), p.2 = g p.1 := by
      rwa [hcomp]
    have h3 := Kernel.ae_ae_of_ae_compProd h2
    have h4 : ∀ᵐ x ∂(κ.fst a),
        Real.tan (∫ y, Real.arctan y ∂(κ.condKernel (a, x))) = g x := by
      filter_upwards [h3] with x hx
      have : ∫ y, Real.arctan y ∂(κ.condKernel (a, x)) = Real.arctan (g x) := by
        rw [integral_congr_ae (g := fun _ => Real.arctan (g x))
          (hx.mono fun y hy => by rw [hy])]
        simp
      rw [this, Real.tan_arctan]
    have h5 : ∀ᵐ p ∂(κ a), Real.tan (∫ y, Real.arctan y ∂(κ.condKernel (a, p.1))) = g p.1 := by
      rw [Kernel.fst_apply] at h4
      exact ae_of_ae_map measurable_fst.aemeasurable h4
    filter_upwards [hga, h5] with p hp1 hp2
    rw [hp2, hp1]

end LatticeProb
