import LatticeProb.Walk.ContinuousExitPrefix
import LatticeProb.Walk.ConstantStepInterpolation
import LatticeProb.Walk.CellConfigVisitPathLaw

/-! # Finite prefixes of constant-step interpolations -/

set_option autoImplicit false
noncomputable section

open BouRabeeGwynne ReflectedGMS ReflectedGMS.GMS
open scoped NNReal ENNReal

namespace LatticeProb.ConstantStepInterpolation

/-- Agreement through a knot implies agreement of the interpolated paths up to
that knot, including at the initial knot. -/
theorem path_eq_of_prefix {E : Type*} [AddCommGroup E] [Module ℝ E]
    {m : ℝ≥0} (hm : 0 < m) {p q : ℕ → E} {M : ℕ}
    (hpq : ∀ n ≤ M, p n = q n) {t : ℝ≥0} (ht : t ≤ knot m M) :
    path m p t = path m q t := by
  rcases ht.lt_or_eq with ht | rfl
  · have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
    have hlt : (m : ℝ) * t < (M : ℝ) := by
      have h := NNReal.coe_lt_coe.mpr ht
      simp only [knot, NNReal.coe_div, NNReal.coe_natCast] at h
      simpa only [mul_comm] using (lt_div_iff₀ hm').mp h
    have hn : ⌊(m : ℝ) * t⌋₊ < M :=
      (Nat.floor_lt (mul_nonneg hm'.le t.2)).2 hlt
    unfold path
    dsimp only
    rw [hpq _ (Nat.le_of_lt hn), hpq _ hn]
  · rw [path_knot hm p M, path_knot hm q M, hpq M le_rfl]

/-- A common exterior knot preserves the continuous first-exit time and curve. -/
theorem continuousExitTime_and_curve_eq_of_prefix
    {m : ℝ≥0} (hm : 0 < m) {p q : ℕ → Plane} {M : ℕ}
    (hpq : ∀ n ≤ M, p n = q n) {U : Set Plane} (hU : IsOpen U)
    (hout : p M ∉ U) :
    let f := continuousPlanePath m p
    let g := continuousPlanePath m q
    continuousExitTime U 0 f ≠ ∞ ∧
      continuousExitTime U 0 g = continuousExitTime U 0 f ∧
      normalizedPrefixCurve g (continuousExitTime U 0 g).toNNReal =
        normalizedPrefixCurve f (continuousExitTime U 0 f).toNNReal := by
  apply LatticeProb.continuousExitTime_and_curve_eq_of_prefix _ _ hU (knot m M)
  · intro t ht
    exact path_eq_of_prefix hm hpq ht
  · change path m p (knot m M) ∉ U
    rwa [path_knot hm p M]

end LatticeProb.ConstantStepInterpolation
end
