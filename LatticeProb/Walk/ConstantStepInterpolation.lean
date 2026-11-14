import LatticeProb.Bonanno.ReflectedGMS.GMS.WalkSRWLaw

/-!
# Constant-step interpolation

A positive constant-speed grid and its affine interpolation through a sequence
of points.
-/

set_option autoImplicit false

noncomputable section

open scoped NNReal

namespace LatticeProb.ConstantStepInterpolation

/-- The time of the `n`th step at speed `m`. -/
def knot (m : ℝ≥0) (n : ℕ) : ℝ≥0 := n / m

/-- Linear interpolation of a sequence, at constant speed. -/
def path {E : Type*} [AddCommGroup E] [Module ℝ E] (m : ℝ) (p : ℕ → E)
    (t : ℝ≥0) : E :=
  let n := ⌊m * t⌋₊
  AffineMap.lineMap (p n) (p (n + 1)) (m * t - n)

theorem knot_zero (m : ℝ≥0) : knot m 0 = 0 := by
  simp [knot]

theorem knot_strictMono {m : ℝ≥0} (hm : 0 < m) : StrictMono (knot m) := by
  intro a b hab
  apply NNReal.coe_lt_coe.mp
  simp only [knot, NNReal.coe_div, NNReal.coe_natCast]
  exact div_lt_div_of_pos_right (by exact_mod_cast hab) (by exact_mod_cast hm)

theorem knot_unbounded {m : ℝ≥0} (hm : 0 < m) (b : ℝ≥0) :
    ∃ n, b < knot m n := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((b : ℝ) * m)
  refine ⟨n, NNReal.coe_lt_coe.mp ?_⟩
  simpa only [knot, NNReal.coe_div, NNReal.coe_natCast] using
    (lt_div_iff₀ (show 0 < (m : ℝ) by exact_mod_cast hm)).2 hn

theorem path_eq_lineMap {E : Type*} [AddCommGroup E] [Module ℝ E]
    {m : ℝ≥0} (hm : 0 < m) (p : ℕ → E) (n : ℕ) (t : ℝ≥0)
    (hlo : knot m n ≤ t) (hhi : t < knot m (n + 1)) :
    path m p t = AffineMap.lineMap (p n) (p (n + 1))
      (((t : ℝ) - knot m n) / ((knot m (n + 1) : ℝ) - knot m n)) := by
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hlo' : (n : ℝ) ≤ (m : ℝ) * t := by
    have h := NNReal.coe_le_coe.mpr hlo
    simp only [knot, NNReal.coe_div, NNReal.coe_natCast] at h
    exact (div_le_iff₀ hm').mp h |>.trans_eq (mul_comm _ _)
  have hhi' : (m : ℝ) * t < (n + 1 : ℕ) := by
    have h := NNReal.coe_lt_coe.mpr hhi
    simp only [knot, NNReal.coe_div, NNReal.coe_natCast] at h
    simpa only [mul_comm] using (lt_div_iff₀ hm').mp h
  have hfloor : ⌊(m : ℝ) * t⌋₊ = n := by
    rw [Nat.floor_eq_iff (show (0 : ℝ) ≤ (m : ℝ) * (t : ℝ) from
      mul_nonneg hm'.le t.2)]
    constructor
    · exact hlo'
    · simpa only [Nat.cast_add, Nat.cast_one] using hhi'
  simp only [path, hfloor, knot, NNReal.coe_div, NNReal.coe_natCast]
  congr 1
  push_cast
  field_simp
  ring

/-- The interpolated path visits each prescribed point at its grid time. -/
theorem path_knot {E : Type*} [AddCommGroup E] [Module ℝ E]
    {m : ℝ≥0} (hm : 0 < m) (p : ℕ → E) (n : ℕ) :
    path m p (knot m n) = p n := by
  rw [path_eq_lineMap hm p n (knot m n) le_rfl
    (knot_strictMono hm (Nat.lt_succ_self n))]
  simp

end LatticeProb.ConstantStepInterpolation
