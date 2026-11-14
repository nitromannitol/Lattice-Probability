import Mathlib

/-!
# Closed squares, dyadic parents and the parent block

Squares in the sense of the dyadic systems of Gwynne-Miller-Sheffield (the invariance principle for
random planar maps embedded by cells, Section 2.1 and Notation 3.13).  For the closed axis-parallel
square `S` with centre `c` and side length `s`:

* a *dyadic child* of `S` is one of the four squares of side `s/2` whose corners include one corner
  of `S` and the centre of `S` (`dyadicChild`);
* a *dyadic parent* of `S` is one of the four squares of side `2s` having `S` as a dyadic child
  (`dyadicParent`, `dyadicChild_dyadicParent`);
* the *parent block* `S^P` is the union of the four dyadic parents (`parentBlock`).

Main statements.

* `parentBlock_eq`: `S^P` is the closed square with the same centre and side `3s`.
* `norm_sub_le_of_mem_of_mem_parentBlock`: a point of `S` and a point of `S^P` are at distance at
  most `2√2 s`, hence at most `4s` (`norm_sub_le_four_mul_of_mem_of_mem_parentBlock`).
* `norm_sub_le_of_mapsTo_parentBlock`: the oscillation bound for chaining along exit times of parent
  blocks: a continuous path that starts in `S` and stays in `S^P` on `[a, b)` stays within distance
  `4s` of its starting point on `[a, b]`.
-/

set_option autoImplicit false

noncomputable section

open Set

namespace LatticeProb.ParentBlock

/-- The closed axis-parallel square with centre `c` and side length `s`. -/
def closedSquare (c : ℂ) (s : ℝ) : Set ℂ :=
  {z | |z.re - c.re| ≤ s / 2 ∧ |z.im - c.im| ≤ s / 2}

/-- The sign `+1` or `-1` attached to a Boolean. -/
def sgn (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem sgn_true : sgn true = 1 := rfl

@[simp] theorem sgn_false : sgn false = -1 := rfl

@[simp] theorem sgn_not (b : Bool) : sgn (!b) = -sgn b := by cases b <;> simp [sgn]

/-- The dyadic child of `closedSquare c s` in the quadrant with signs `e`: side `s/2`, centre
`c + (e.1 s/4, e.2 s/4)`. -/
def dyadicChild (c : ℂ) (s : ℝ) (e : Bool × Bool) : Set ℂ :=
  closedSquare (c + ⟨sgn e.1 * (s / 4), sgn e.2 * (s / 4)⟩) (s / 2)

/-- The dyadic parent of `closedSquare c s` in the direction with signs `e`: side `2s`, centre
`c + (e.1 s/2, e.2 s/2)`. -/
def dyadicParent (c : ℂ) (s : ℝ) (e : Bool × Bool) : Set ℂ :=
  closedSquare (c + ⟨sgn e.1 * (s / 2), sgn e.2 * (s / 2)⟩) (2 * s)

/-- `closedSquare c s` is a dyadic child (the one in the opposite quadrant) of each of its dyadic
parents. -/
theorem dyadicChild_dyadicParent (c : ℂ) (s : ℝ) (e : Bool × Bool) :
    dyadicChild (c + ⟨sgn e.1 * (s / 2), sgn e.2 * (s / 2)⟩) (2 * s) (!e.1, !e.2) =
      closedSquare c s := by
  unfold dyadicChild
  congr 1
  · apply Complex.ext <;> simp <;> ring
  · ring

/-- The parent block `S^P` of `S = closedSquare c s`: the union of its four dyadic parents. -/
def parentBlock (c : ℂ) (s : ℝ) : Set ℂ :=
  ⋃ e : Bool × Bool, dyadicParent c s e

private theorem exists_sgn_abs_sub_le_iff {s : ℝ} (hs : 0 ≤ s) (x : ℝ) :
    (∃ b : Bool, |x - sgn b * (s / 2)| ≤ 2 * s / 2) ↔ |x| ≤ 3 * s / 2 := by
  constructor
  · rintro ⟨b, hb⟩
    have h1 : |sgn b * (s / 2)| = s / 2 := by
      cases b <;> simp [abs_of_nonneg (by linarith : (0 : ℝ) ≤ s / 2)]
    calc |x| = |(x - sgn b * (s / 2)) + sgn b * (s / 2)| := by ring_nf
      _ ≤ |x - sgn b * (s / 2)| + |sgn b * (s / 2)| := abs_add_le _ _
      _ ≤ 3 * s / 2 := by rw [h1]; linarith
  · intro hx
    rcases abs_le.mp hx with ⟨hx1, hx2⟩
    rcases le_total 0 x with h0 | h0
    · refine ⟨true, abs_le.mpr ⟨?_, ?_⟩⟩ <;> simp <;> linarith
    · refine ⟨false, abs_le.mpr ⟨?_, ?_⟩⟩ <;> simp <;> linarith

/-- **The parent block is a square.** `S^P` is the closed square with the same centre as `S` and
three times its side. -/
theorem parentBlock_eq {s : ℝ} (hs : 0 ≤ s) (c : ℂ) :
    parentBlock c s = closedSquare c (3 * s) := by
  ext z
  simp only [parentBlock, dyadicParent, closedSquare, mem_iUnion, mem_ofPred_eq, Prod.exists,
    Complex.add_re, Complex.add_im]
  have hre := exists_sgn_abs_sub_le_iff hs (z.re - c.re)
  have him := exists_sgn_abs_sub_le_iff hs (z.im - c.im)
  constructor
  · rintro ⟨b₁, b₂, h₁, h₂⟩
    refine ⟨hre.mp ⟨b₁, ?_⟩, him.mp ⟨b₂, ?_⟩⟩
    · rw [sub_sub]; exact h₁
    · rw [sub_sub]; exact h₂
  · rintro ⟨h₁, h₂⟩
    obtain ⟨b₁, hb₁⟩ := hre.mpr h₁
    obtain ⟨b₂, hb₂⟩ := him.mpr h₂
    refine ⟨b₁, b₂, ?_, ?_⟩
    · rw [sub_sub] at hb₁; exact hb₁
    · rw [sub_sub] at hb₂; exact hb₂

/-- **Distance bound in the parent block.** A point of `S = closedSquare c s` and a point of its
parent block `S^P` are at Euclidean distance at most `2√2 s`. -/
theorem norm_sub_le_of_mem_of_mem_parentBlock {c x y : ℂ} {s : ℝ} (hs : 0 ≤ s)
    (hx : x ∈ closedSquare c s) (hy : y ∈ parentBlock c s) :
    ‖y - x‖ ≤ 2 * Real.sqrt 2 * s := by
  rw [parentBlock_eq hs] at hy
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have hre : |(y - x).re| ≤ 2 * s := by
    rw [Complex.sub_re]
    calc |y.re - x.re| = |(y.re - c.re) - (x.re - c.re)| := by ring_nf
      _ ≤ |y.re - c.re| + |x.re - c.re| := abs_sub _ _
      _ ≤ 2 * s := by linarith
  have him : |(y - x).im| ≤ 2 * s := by
    rw [Complex.sub_im]
    calc |y.im - x.im| = |(y.im - c.im) - (x.im - c.im)| := by ring_nf
      _ ≤ |y.im - c.im| + |x.im - c.im| := abs_sub _ _
      _ ≤ 2 * s := by linarith
  calc ‖y - x‖ ≤ Real.sqrt 2 * max |(y - x).re| |(y - x).im| := Complex.norm_le_sqrt_two_mul_max _
    _ ≤ Real.sqrt 2 * (2 * s) :=
        mul_le_mul_of_nonneg_left (max_le hre him) (Real.sqrt_nonneg 2)
    _ = 2 * Real.sqrt 2 * s := by ring

/-- A point of `S = closedSquare c s` and a point of `S^P` are at distance at most `4s`. -/
theorem norm_sub_le_four_mul_of_mem_of_mem_parentBlock {c x y : ℂ} {s : ℝ} (hs : 0 ≤ s)
    (hx : x ∈ closedSquare c s) (hy : y ∈ parentBlock c s) :
    ‖y - x‖ ≤ 4 * s := by
  have h2 : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  calc ‖y - x‖ ≤ 2 * Real.sqrt 2 * s := norm_sub_le_of_mem_of_mem_parentBlock hs hx hy
    _ ≤ 2 * 2 * s := by gcongr
    _ = 4 * s := by ring

theorem isClosed_closedSquare (c : ℂ) (s : ℝ) : IsClosed (closedSquare c s) := by
  have h1 : Continuous fun z : ℂ => |z.re - c.re| := by fun_prop
  have h2 : Continuous fun z : ℂ => |z.im - c.im| := by fun_prop
  exact (isClosed_le h1 continuous_const).inter (isClosed_le h2 continuous_const)

/-- **Oscillation along one parent-block exit (chaining step).** If a continuous path `f` starts in
`S = closedSquare c s` at time `a` and stays in the parent block `S^P` during `[a, b)`, then
`‖f t - f a‖ ≤ 4s` for all `t ∈ [a, b]` (the endpoint by closedness of `S^P`). -/
theorem norm_sub_le_of_mapsTo_parentBlock {f : ℝ → ℂ} (hf : Continuous f) {a b : ℝ} {c : ℂ}
    {s : ℝ} (hs : 0 ≤ s) (ha : f a ∈ closedSquare c s)
    (hmaps : ∀ t ∈ Ico a b, f t ∈ parentBlock c s) :
    ∀ t ∈ Icc a b, ‖f t - f a‖ ≤ 4 * s := by
  intro t ht
  have hfa : f a ∈ parentBlock c s := by
    rw [parentBlock_eq hs]
    exact ⟨ha.1.trans (by linarith), ha.2.trans (by linarith)⟩
  have hft : f t ∈ parentBlock c s := by
    rcases eq_or_lt_of_le ht.2 with htb | htb
    · rcases eq_or_lt_of_le ht.1 with hat | hat
      · rw [← hat]; exact hfa
      · have hcl : IsClosed (parentBlock c s) := by
          rw [parentBlock_eq hs]; exact isClosed_closedSquare c (3 * s)
        rw [← hcl.closure_eq]
        refine map_mem_closure hf ?_ (fun u hu => hmaps u hu)
        rw [closure_Ico (by rw [htb] at hat; exact hat.ne)]
        exact ⟨ht.1, htb.le⟩
    · exact hmaps t ⟨ht.1, htb⟩
  exact norm_sub_le_four_mul_of_mem_of_mem_parentBlock hs ha hft

end LatticeProb.ParentBlock
