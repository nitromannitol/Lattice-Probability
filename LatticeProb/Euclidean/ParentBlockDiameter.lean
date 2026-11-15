import LatticeProb.Euclidean.ParentBlock

/-! # Diameter of a parent block -/

set_option autoImplicit false

namespace LatticeProb.ParentBlock

/-- Any two points of a parent block are at most six side lengths apart. -/
theorem norm_sub_le_six_mul_of_mem_parentBlock {c x y : ℂ} {s : ℝ}
    (hs : 0 ≤ s) (hx : x ∈ parentBlock c s) (hy : y ∈ parentBlock c s) :
    ‖y - x‖ ≤ 6 * s := by
  rw [parentBlock_eq hs] at hx hy
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  have hre : |(y - x).re| ≤ 3 * s := by
    rw [Complex.sub_re]
    calc
      |y.re - x.re| = |(y.re - c.re) - (x.re - c.re)| := by ring_nf
      _ ≤ |y.re - c.re| + |x.re - c.re| := abs_sub _ _
      _ ≤ 3 * s := by linarith
  have him : |(y - x).im| ≤ 3 * s := by
    rw [Complex.sub_im]
    calc
      |y.im - x.im| = |(y.im - c.im) - (x.im - c.im)| := by ring_nf
      _ ≤ |y.im - c.im| + |x.im - c.im| := abs_sub _ _
      _ ≤ 3 * s := by linarith
  have h2 : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  calc
    ‖y - x‖ ≤ Real.sqrt 2 * max |(y - x).re| |(y - x).im| :=
      Complex.norm_le_sqrt_two_mul_max _
    _ ≤ Real.sqrt 2 * (3 * s) :=
      mul_le_mul_of_nonneg_left (max_le hre him) (Real.sqrt_nonneg 2)
    _ ≤ 2 * (3 * s) := mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = 6 * s := by ring

end LatticeProb.ParentBlock
