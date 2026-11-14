import LatticeProb.Euclidean.ParentBlock
import LatticeProb.LQG.InternalMetricDyadicChaining

/-!
# Dyadic covers of parent blocks

The dyadic subsquares of the four parents cover the parent block at each level, including its
boundary. Each selected subsquare lies in one of those parents.
-/

set_option autoImplicit false

open Set

namespace LatticeProb.ParentBlock

/-- The lower-left corner of a dyadic parent square. -/
noncomputable def parentCorner (c : ℂ) (s : ℝ) (e : Bool × Bool) : ℂ :=
  c + ⟨sgn e.1 * (s / 2) - s, sgn e.2 * (s / 2) - s⟩

/-- A dyadic parent expressed by its lower-left corner. -/
theorem dyadicParent_eq_reProdIm (c : ℂ) (s : ℝ) (e : Bool × Bool) :
    dyadicParent c s e =
      Icc (parentCorner c s e).re ((parentCorner c s e).re + 2 * s) ×ℂ
      Icc (parentCorner c s e).im ((parentCorner c s e).im + 2 * s) := by
  ext z
  simp only [dyadicParent, closedSquare, mem_ofPred_eq, Complex.mem_reProdIm, mem_Icc,
    parentCorner, Complex.add_re, Complex.add_im, abs_le]
  constructor <;> rintro ⟨⟨h₁, h₂⟩, h₃, h₄⟩ <;>
    constructor <;> constructor <;> linarith

/-- The dyadic subsquares of the four parents cover the parent block at every level. -/
theorem exists_mem_parent_dyadicSubsquare {c z : ℂ} {s : ℝ} (hs : 0 < s)
    (hz : z ∈ parentBlock c s) (n : ℕ) :
    ∃ (e : Bool × Bool) (i j : ℕ), i < 2 ^ n ∧ j < 2 ^ n ∧
      z ∈ LQG.closedDyadicSubsquare (parentCorner c s e).re
        (parentCorner c s e).im (2 * s) n i j ∧
      LQG.closedDyadicSubsquare (parentCorner c s e).re
        (parentCorner c s e).im (2 * s) n i j ⊆ dyadicParent c s e := by
  obtain ⟨e, he⟩ := mem_iUnion.mp hz
  rw [dyadicParent_eq_reProdIm] at he
  let a := parentCorner c s e
  let i := LQG.dyadicIndex ((z.re - a.re) / (2 * s)) n
  let j := LQG.dyadicIndex ((z.im - a.im) / (2 * s)) n
  have hi : i < 2 ^ n := LQG.dyadicIndex_lt _ _
  have hj : j < 2 ^ n := LQG.dyadicIndex_lt _ _
  refine ⟨e, i, j, hi, hj, ?_, ?_⟩
  · exact LQG.mem_closedDyadicSubsquare_dyadicIndex (by positivity) he n
  · rw [dyadicParent_eq_reProdIm]
    exact LQG.closedDyadicSubsquare_subset (by positivity) hi hj

/-- Subdivision level `l + 1` of a parent has the requested side length. -/
theorem parent_subdivision_side (s : ℝ) (l : ℕ) :
    2 * s / (2 : ℝ) ^ (l + 1) = s / 2 ^ l := by
  rw [pow_succ]
  field_simp

end LatticeProb.ParentBlock
