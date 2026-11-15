import LatticeProb.Bonanno.ReflectedGMS.GMS.CodingValid
import LatticeProb.Bonanno.ReflectedGMS.GMS.CodeMeasurable

/-! # Measurable transition weights for labelled cell configurations -/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter
open ReflectedGMS ReflectedGMS.GMS

namespace LatticeProb.CellConfigLabelTransition

/-- Total conductance from a canonical label. -/
def rowTotal (H : GMSSpace) (n : ℕ) : ℝ :=
  ∑' m, H.1.codeCond n m

theorem summable_codeCond (H : GMSSpace) (n : ℕ) :
    Summable (H.1.codeCond n) :=
  summable_of_hasFiniteSupport (CellConfig.finiteRows_code H.2 n)

theorem rowTotal_nonneg (H : GMSSpace) (n : ℕ) : 0 ≤ rowTotal H n :=
  tsum_nonneg (fun m => (CellConfig.rawAdmissible_code H.2).nonneg n m)

theorem measurable_rowTotal (n : ℕ) : Measurable (fun H : GMSSpace => rowTotal H n) := by
  apply measurable_of_tendsto_metrizable
    (f := fun k H => ∑ m ∈ Finset.range k, H.1.codeCond n m)
  · intro k
    exact Finset.measurable_fun_sum _ (fun m _ => measurable_codeCond n m)
  · rw [tendsto_pi_nhds]
    intro H
    exact (summable_codeCond H n).hasSum.tendsto_sum_nat

/-- Conductance-proportional transitions, with absorption at a zero row. -/
def step (H : GMSSpace) (n m : ℕ) : ℝ :=
  if rowTotal H n = 0 then (if m = n then 1 else 0)
  else H.1.codeCond n m / rowTotal H n

theorem measurable_step (n m : ℕ) : Measurable (fun H : GMSSpace => step H n m) := by
  unfold step
  exact Measurable.ite ((measurable_rowTotal n) (measurableSet_singleton 0))
    measurable_const ((measurable_codeCond n m).div (measurable_rowTotal n))

theorem step_nonneg (H : GMSSpace) (n m : ℕ) : 0 ≤ step H n m := by
  unfold step
  split_ifs with h h'
  · exact zero_le_one
  · exact le_rfl
  · exact div_nonneg ((CellConfig.rawAdmissible_code H.2).nonneg n m) (rowTotal_nonneg H n)

theorem tsum_step (H : GMSSpace) (n : ℕ) : ∑' m, step H n m = 1 := by
  by_cases h : rowTotal H n = 0
  · simp only [step, h, ↓reduceIte]
    rw [tsum_eq_single n]
    · simp
    · intro m hm
      simp [hm]
  · simp only [step, h, ↓reduceIte]
    rw [tsum_div_const]
    exact div_self h

end LatticeProb.CellConfigLabelTransition
