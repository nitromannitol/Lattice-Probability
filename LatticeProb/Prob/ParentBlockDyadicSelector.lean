import LatticeProb.Euclidean.ParentBlockDyadicCover
import LatticeProb.Prob.ParentBlockSelector

/-!
# Measurable selection among dyadic subsquares

The finite family of dyadic descendants of the four parents admits a measurable selector.
-/

set_option autoImplicit false

open Set MeasureTheory

namespace LatticeProb.ParentBlock

/-- Indices for the dyadic subsquares of the four parents at a fixed level. -/
abbrev ParentDyadicIndex (n : ℕ) := (Bool × Bool) × Fin (2 ^ n) × Fin (2 ^ n)

/-- A natural-number enumeration of the finite dyadic index type. -/
noncomputable def parentDyadicEnumeration (n : ℕ) (k : ℕ) : ParentDyadicIndex n :=
  (Encodable.decode k).getD ((false, false), ⟨0, by positivity⟩, ⟨0, by positivity⟩)

/-- Every dyadic index occurs in the enumeration. -/
theorem parentDyadicEnumeration_surjective (n : ℕ) :
    Function.Surjective (parentDyadicEnumeration n) := by
  exact Encodable.surjective_decode_getD _ _

/-- The centre of a dyadic subsquare of one of the four parents. -/
noncomputable def parentDyadicCentre (c : ℂ) (S : ℝ) (n : ℕ)
    (p : ParentDyadicIndex n) : ℂ :=
  parentCorner c S p.1 +
    ⟨((p.2.1 : ℕ) + (1 / 2 : ℝ)) * (2 * S / (2 : ℝ) ^ n),
     ((p.2.2 : ℕ) + (1 / 2 : ℝ)) * (2 * S / (2 : ℝ) ^ n)⟩

/-- Each indexed closed dyadic subsquare is the square with its corresponding centre. -/
theorem parentDyadicSubsquare_eq_closedSquare (c : ℂ) (S : ℝ) (n : ℕ)
    (p : ParentDyadicIndex n) :
    LQG.closedDyadicSubsquare (parentCorner c S p.1).re (parentCorner c S p.1).im
      (2 * S) n p.2.1 p.2.2 =
        closedSquare (parentDyadicCentre c S n p) (2 * S / (2 : ℝ) ^ n) := by
  ext z
  simp only [LQG.closedDyadicSubsquare, Complex.mem_reProdIm, mem_Icc, closedSquare,
    mem_ofPred_eq, parentDyadicCentre, Complex.add_re, Complex.add_im, abs_le]
  constructor <;> rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩ <;>
    constructor <;> constructor <;> linarith

/-- Select a dyadic descendant containing the state, and stop outside the parent block. -/
theorem exists_measurable_parentBlock_dyadic_selector [MeasurableSpace (Option ℕ)]
    (c : ℂ) {S : ℝ} (hS : 0 < S) (n : ℕ)
    (e : ℕ → ParentDyadicIndex n) (he : Function.Surjective e) :
    ∃ f : EuclideanSpace ℝ (Fin 2) → Option ℕ, Measurable f ∧
      (∀ x k, f x = some k →
        Complex.orthonormalBasisOneI.repr.symm x ∈ parentBlock c S ∧
        Complex.orthonormalBasisOneI.repr.symm x ∈
          LQG.closedDyadicSubsquare (parentCorner c S (e k).1).re
            (parentCorner c S (e k).1).im (2 * S) n (e k).2.1 (e k).2.2 ∧
        LQG.closedDyadicSubsquare (parentCorner c S (e k).1).re
            (parentCorner c S (e k).1).im (2 * S) n (e k).2.1 (e k).2.2 ⊆
          dyadicParent c S (e k).1 ∧
        Complex.orthonormalBasisOneI.repr.symm x ∈
          interior (parentBlock (parentDyadicCentre c S n (e k))
            (2 * S / (2 : ℝ) ^ n))) ∧
      (∀ x, f x = none ↔ Complex.orthonormalBasisOneI.repr.symm x ∉ parentBlock c S) := by
  have hs : 0 < 2 * S / (2 : ℝ) ^ n := by positivity
  have hcover : parentBlock c S ⊆
      ⋃ k, closedSquare (parentDyadicCentre c S n (e k)) (2 * S / (2 : ℝ) ^ n) := by
    intro z hz
    obtain ⟨b, i, j, hi, hj, hz, _⟩ := exists_mem_parent_dyadicSubsquare hS hz n
    let p : ParentDyadicIndex n := (b, ⟨i, hi⟩, ⟨j, hj⟩)
    obtain ⟨k, hk⟩ := he p
    apply mem_iUnion.mpr
    refine ⟨k, ?_⟩
    rw [hk, ← parentDyadicSubsquare_eq_closedSquare]
    exact hz
  obtain ⟨f, hf, hsome, hnone⟩ :=
    exists_measurable_parentBlock_selector c hS.le hs
      (fun k => parentDyadicCentre c S n (e k)) hcover
  refine ⟨f, hf, ?_, hnone⟩
  intro x k hx
  obtain ⟨hout, hin, hinterior⟩ := hsome x k hx
  refine ⟨hout, ?_, ?_, hinterior⟩
  · rwa [parentDyadicSubsquare_eq_closedSquare]
  · rw [dyadicParent_eq_reProdIm]
    exact LQG.closedDyadicSubsquare_subset (by positivity) (e k).2.1.isLt (e k).2.2.isLt

end LatticeProb.ParentBlock
