import Mathlib

/-!
# The distance of curves modulo time parametrization

For paths `f g : ℝ≥0 → E` in a pseudo-extended-metric space, the distance modulo time
parametrization is `inf_φ sup_t edist (f t) (g (φ t))`, the infimum over the increasing
homeomorphisms (order automorphisms) `φ` of `[0, ∞)`. This is the metric on curves viewed modulo
time parametrization used in invariance principles for random walks in random environments
(Gwynne, Miller and Sheffield, *An invariance principle for ergodic scale-free random
environments*, arXiv 1807.07515, (2.2) and Theorem 1.16).

It vanishes on the diagonal, is symmetric and satisfies the triangle inequality, so the open
`κ`-neighbourhoods `A^κ = {b | ∃ f ∈ A, d(b, f) < κ}` compose: `(A^κ₁)^κ₂ ⊆ A^(κ₁ + κ₂)`.
Consequently one-sided Prokhorov bounds `P A ≤ Q (A^κ) + κ` compose along a chain of laws, which is
how a convergence statement for random walks is transferred between starting points and between
stopping domains.

## Main statements

* `LatticeProb.ReparamEDist.reparamEDist_self`, `reparamEDist_comm`, `reparamEDist_triangle`.
* `reparamEDist_le_iSup_edist`: bounded by the uniform distance.
* `reparamEDist_add_const`, `reparamEDist_add_const_le`: translation invariance in a normed group.
* `thickening_thickening_subset`, `subset_thickening`, `thickening_mono`.
* `le_thickening_add_trans`: composition of one-sided Prokhorov bounds.
-/

open Set
open scoped ENNReal NNReal

namespace LatticeProb.ReparamEDist

variable {E : Type*} [PseudoEMetricSpace E]

/-- The distance of curves modulo time parametrization: `inf_φ sup_t edist (f t) (g (φ t))` over
the order automorphisms `φ` of `[0, ∞)`. -/
noncomputable def reparamEDist (f g : ℝ≥0 → E) : ℝ≥0∞ :=
  ⨅ φ : ℝ≥0 ≃o ℝ≥0, ⨆ t : ℝ≥0, edist (f t) (g (φ t))

theorem reparamEDist_le_of_orderIso (f g : ℝ≥0 → E) (φ : ℝ≥0 ≃o ℝ≥0) :
    reparamEDist f g ≤ ⨆ t : ℝ≥0, edist (f t) (g (φ t)) :=
  iInf_le _ φ

/-- The distance modulo time parametrization is at most the uniform distance. -/
theorem reparamEDist_le_iSup_edist (f g : ℝ≥0 → E) :
    reparamEDist f g ≤ ⨆ t : ℝ≥0, edist (f t) (g t) :=
  iInf_le_of_le (OrderIso.refl ℝ≥0) le_rfl

theorem reparamEDist_self (f : ℝ≥0 → E) : reparamEDist f f = 0 :=
  nonpos_iff_eq_zero.1 ((reparamEDist_le_iSup_edist f f).trans (by simp))

/-- Substituting `φ⁻¹` exchanges the two curves. -/
theorem iSup_edist_comp_eq (f g : ℝ≥0 → E) (φ : ℝ≥0 ≃o ℝ≥0) :
    ⨆ t : ℝ≥0, edist (f t) (g (φ t)) = ⨆ s : ℝ≥0, edist (g s) (f (φ.symm s)) := by
  refine le_antisymm (iSup_le fun t => ?_) (iSup_le fun s => ?_)
  · rw [edist_comm]
    calc edist (g (φ t)) (f t) = edist (g (φ t)) (f (φ.symm (φ t))) := by
          rw [φ.symm_apply_apply]
      _ ≤ ⨆ s : ℝ≥0, edist (g s) (f (φ.symm s)) :=
          le_iSup (fun s => edist (g s) (f (φ.symm s))) (φ t)
  · rw [edist_comm]
    calc edist (f (φ.symm s)) (g s) = edist (f (φ.symm s)) (g (φ (φ.symm s))) := by
          rw [φ.apply_symm_apply]
      _ ≤ ⨆ t : ℝ≥0, edist (f t) (g (φ t)) :=
          le_iSup (fun t => edist (f t) (g (φ t))) (φ.symm s)

theorem reparamEDist_le_comm (f g : ℝ≥0 → E) : reparamEDist f g ≤ reparamEDist g f := by
  refine le_iInf fun φ => ?_
  calc reparamEDist f g ≤ ⨆ s : ℝ≥0, edist (f s) (g (φ.symm s)) :=
        reparamEDist_le_of_orderIso f g φ.symm
    _ = ⨆ t : ℝ≥0, edist (g t) (f (φ t)) := (iSup_edist_comp_eq g f φ).symm

theorem reparamEDist_comm (f g : ℝ≥0 → E) : reparamEDist f g = reparamEDist g f :=
  le_antisymm (reparamEDist_le_comm f g) (reparamEDist_le_comm g f)

/-- **Triangle inequality** for the distance modulo time parametrization. -/
theorem reparamEDist_triangle (f g h : ℝ≥0 → E) :
    reparamEDist f h ≤ reparamEDist f g + reparamEDist g h := by
  refine ENNReal.le_iInf_add_iInf fun φ ψ => ?_
  calc reparamEDist f h ≤ ⨆ t : ℝ≥0, edist (f t) (h ((φ.trans ψ) t)) :=
        reparamEDist_le_of_orderIso f h (φ.trans ψ)
    _ ≤ (⨆ t : ℝ≥0, edist (f t) (g (φ t))) + ⨆ s : ℝ≥0, edist (g s) (h (ψ s)) := by
        refine iSup_le fun t => ?_
        rw [OrderIso.trans_apply]
        exact (edist_triangle _ (g (φ t)) _).trans
          (add_le_add (le_iSup (fun t => edist (f t) (g (φ t))) t)
            (le_iSup (fun s => edist (g s) (h (ψ s))) (φ t)))

section Translation

variable {F : Type*} [SeminormedAddCommGroup F]

/-- Translating both curves by the same vector does not change the distance. -/
theorem reparamEDist_add_const (f g : ℝ≥0 → F) (v : F) :
    reparamEDist (fun t => f t + v) (fun t => g t + v) = reparamEDist f g := by
  simp only [reparamEDist, edist_add_right]

/-- Translating a curve by `v` moves it by at most `edist v 0`. -/
theorem reparamEDist_add_const_le (f : ℝ≥0 → F) (v : F) :
    reparamEDist (fun t => f t + v) f ≤ edist v 0 := by
  refine (reparamEDist_le_iSup_edist _ f).trans (iSup_le fun t => ?_)
  calc edist (f t + v) (f t) = edist (f t + v) (f t + 0) := by rw [add_zero]
    _ = edist v 0 := edist_add_left _ _ _
    _ ≤ edist v 0 := le_rfl

end Translation

/-- The open `κ`-neighbourhood of a set of curves for the distance modulo time parametrization. -/
def thickening (κ : ℝ≥0∞) (A : Set (ℝ≥0 → E)) : Set (ℝ≥0 → E) :=
  {b | ∃ f ∈ A, reparamEDist b f < κ}

theorem mem_thickening {κ : ℝ≥0∞} {A : Set (ℝ≥0 → E)} {b : ℝ≥0 → E} :
    b ∈ thickening κ A ↔ ∃ f ∈ A, reparamEDist b f < κ :=
  Iff.rfl

theorem subset_thickening {κ : ℝ≥0∞} (hκ : 0 < κ) (A : Set (ℝ≥0 → E)) :
    A ⊆ thickening κ A :=
  fun f hf => ⟨f, hf, by rwa [reparamEDist_self]⟩

theorem thickening_mono {κ κ' : ℝ≥0∞} (hκ : κ ≤ κ') {A A' : Set (ℝ≥0 → E)} (hA : A ⊆ A') :
    thickening κ A ⊆ thickening κ' A' := by
  rintro b ⟨f, hf, hb⟩
  exact ⟨f, hA hf, hb.trans_le hκ⟩

/-- Neighbourhoods compose: `(A^κ₁)^κ₂ ⊆ A^(κ₁ + κ₂)`. -/
theorem thickening_thickening_subset (κ₁ κ₂ : ℝ≥0∞) (A : Set (ℝ≥0 → E)) :
    thickening κ₂ (thickening κ₁ A) ⊆ thickening (κ₁ + κ₂) A := by
  rintro b ⟨g, ⟨f, hf, hgf⟩, hbg⟩
  refine ⟨f, hf, ?_⟩
  calc reparamEDist b f ≤ reparamEDist b g + reparamEDist g f := reparamEDist_triangle b g f
    _ < κ₂ + κ₁ := ENNReal.add_lt_add hbg hgf
    _ = κ₁ + κ₂ := add_comm _ _

/-- **Composition of one-sided Prokhorov bounds.** If `P A ≤ Q (A^κ₁) + κ₁` and
`Q A ≤ R (A^κ₂) + κ₂` for all sets of curves `A`, and `R` is monotone, then
`P A ≤ R (A^(κ₁ + κ₂)) + (κ₁ + κ₂)`. -/
theorem le_thickening_add_trans {P Q R : Set (ℝ≥0 → E) → ℝ≥0∞} (hR : Monotone R)
    {κ₁ κ₂ : ℝ≥0∞} (h₁ : ∀ A, P A ≤ Q (thickening κ₁ A) + κ₁)
    (h₂ : ∀ A, Q A ≤ R (thickening κ₂ A) + κ₂) (A : Set (ℝ≥0 → E)) :
    P A ≤ R (thickening (κ₁ + κ₂) A) + (κ₁ + κ₂) := by
  calc P A ≤ Q (thickening κ₁ A) + κ₁ := h₁ A
    _ ≤ (R (thickening κ₂ (thickening κ₁ A)) + κ₂) + κ₁ := by
        gcongr
        exact h₂ _
    _ ≤ (R (thickening (κ₁ + κ₂) A) + κ₂) + κ₁ := by
        gcongr
        exact hR (thickening_thickening_subset κ₁ κ₂ A)
    _ = R (thickening (κ₁ + κ₂) A) + (κ₁ + κ₂) := by
        rw [add_assoc, add_comm κ₂ κ₁]

end LatticeProb.ReparamEDist
