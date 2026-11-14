import LatticeProb.Walk.ConstantStepInterpolation
import Mathlib.MeasureTheory.Function.Floor

/-! # Measurability of constant-step interpolation -/

set_option autoImplicit false

open MeasureTheory
open scoped NNReal

namespace LatticeProb.ConstantStepInterpolation

/-- Interpolation is jointly measurable in the anchors, speed, and time. -/
theorem measurable_path :
    Measurable (fun q : (ℕ → ℂ) × ℝ × ℝ≥0 => path q.2.1 q.1 q.2.2) := by
  let S := (ℕ → ℂ) × ℝ × ℝ≥0
  have hs : Measurable (fun q : S => q.2.1 * (q.2.2 : ℝ)) :=
    (measurable_fst.comp measurable_snd).mul
      (NNReal.continuous_coe.measurable.comp (measurable_snd.comp measurable_snd))
  have hn : Measurable (fun q : S => ⌊q.2.1 * (q.2.2 : ℝ)⌋₊) := hs.nat_floor
  have heval : Measurable (fun z : (ℕ → ℂ) × ℕ => z.1 z.2) :=
    measurable_from_prod_countable_left fun n => measurable_pi_apply n
  have hp : Measurable (fun q : S => q.1 ⌊q.2.1 * (q.2.2 : ℝ)⌋₊) :=
    heval.comp (measurable_fst.prodMk hn)
  have hp' : Measurable (fun q : S => q.1 (⌊q.2.1 * (q.2.2 : ℝ)⌋₊ + 1)) :=
    heval.comp (measurable_fst.prodMk (hn.add measurable_const))
  have hcast : Measurable (fun q : S => (⌊q.2.1 * (q.2.2 : ℝ)⌋₊ : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp hn
  have ha := hs.sub hcast
  unfold path
  simp only [AffineMap.lineMap_apply_module']
  exact (ha.smul (hp'.sub hp)).add hp

end LatticeProb.ConstantStepInterpolation
