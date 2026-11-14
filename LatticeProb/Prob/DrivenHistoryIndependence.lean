import LatticeProb.Prob.DrivenPath
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Independent instructions for driven paths

The finite history of a path driven by independent instructions is independent
of the next instruction.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory

namespace LatticeProb

variable {Ω X U : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  [MeasurableSpace U] [Nonempty U]

/-- The path history through time `n` is independent of instruction `n`. -/
theorem indepFun_drivenPath_history_instruction (P : Measure Ω)
    (F : X → U → X) (hF : Measurable (Function.uncurry F)) (x : X)
    (Z : ℕ → Ω → U) (hZ : ∀ j, Measurable (Z j)) (hI : iIndepFun Z P) (n : ℕ) :
    IndepFun (fun ω (i : Finset.Iic n) => drivenPath F x (fun j => Z j ω) i)
      (Z n) P := by
  classical
  let extend : (Finset.range n → U) → ℕ → U := fun u j =>
    if h : j ∈ Finset.range n then u ⟨j, h⟩ else Classical.choice ‹Nonempty U›
  have hextend : Measurable extend := by
    apply Measurable.of_eval
    intro j
    by_cases h : j ∈ Finset.range n
    · simpa only [extend, h, ↓reduceDIte] using
        (measurable_pi_apply (⟨j, h⟩ : Finset.range n) : Measurable (fun u : Finset.range n → U => u ⟨j, h⟩))
    · simpa only [extend, h, ↓reduceDIte] using
        (measurable_const : Measurable (fun _ : Finset.range n → U => Classical.choice ‹Nonempty U›))
  let H : (Finset.range n → U) → (Finset.Iic n → X) :=
    fun u i => drivenPath F x (extend u) i
  have hH : Measurable H := by
    apply Measurable.of_eval
    intro i
    exact ((measurable_pi_apply i.val).comp
      ((measurable_drivenPath F hF).comp (measurable_const.prodMk hextend)))
  let E : (({n} : Finset ℕ) → U) → U := fun u => u ⟨n, Finset.mem_singleton_self n⟩
  have hE : Measurable E := measurable_pi_apply _
  have hi := hI.indepFun_finset (Finset.range n) {n} (by simp) hZ
  have hid : (fun ω (i : Finset.Iic n) => drivenPath F x (fun j => Z j ω) i) =
      H ∘ (fun ω (j : Finset.range n) => Z j ω) := by
    funext ω i
    apply drivenPath_eq_of_prefix_eq
    intro j hj
    have hjn : j ∈ Finset.range n := Finset.mem_range.mpr (lt_of_lt_of_le hj (Finset.mem_Iic.mp i.property))
    simp only [extend, hjn, ↓reduceDIte]
  rw [hid]
  exact hi.comp hH hE

/-- The joint history and instruction law is the product of its marginals. -/
theorem map_drivenPath_history_instruction (P : Measure Ω)
    (F : X → U → X) (hF : Measurable (Function.uncurry F)) (x : X)
    (Z : ℕ → Ω → U) (hZ : ∀ j, Measurable (Z j)) (hI : iIndepFun Z P) (n : ℕ) :
    P.map (fun ω : Ω => ((fun i : Finset.Iic n => drivenPath F x (fun j => Z j ω) i), Z n ω)) =
      (P.map (fun ω (i : Finset.Iic n) => drivenPath F x (fun j => Z j ω) i)).prod
        (P.map (Z n)) := by
  have hpath : Measurable (fun ω => drivenPath F x (fun j => Z j ω)) :=
    (measurable_drivenPath F hF).comp
      (measurable_const.prodMk (Measurable.of_eval hZ))
  have hhist : Measurable (fun ω (i : Finset.Iic n) => drivenPath F x (fun j => Z j ω) i) :=
    Measurable.of_eval (fun i => (measurable_pi_apply i.val).comp hpath)
  let : IsProbabilityMeasure P := hI.isProbabilityMeasure
  exact (indepFun_drivenPath_history_instruction P F hF x Z hZ hI n).map_prod_eq_prod_map_map
    hhist.aemeasurable (hZ n).aemeasurable

/-- The history and instruction law is a composition product with a constant kernel. -/
theorem map_drivenPath_history_instruction_compProd (P : Measure Ω)
    (F : X → U → X) (hF : Measurable (Function.uncurry F)) (x : X)
    (Z : ℕ → Ω → U) (hZ : ∀ j, Measurable (Z j)) (hI : iIndepFun Z P) (n : ℕ) :
    P.map (fun ω : Ω => ((fun i : Finset.Iic n => drivenPath F x (fun j => Z j ω) i), Z n ω)) =
      (P.map (fun ω (i : Finset.Iic n) => drivenPath F x (fun j => Z j ω) i)) ⊗ₘ
        ProbabilityTheory.Kernel.const _ (P.map (Z n)) := by
  let : IsProbabilityMeasure P := hI.isProbabilityMeasure
  rw [Measure.compProd_const]
  exact map_drivenPath_history_instruction P F hF x Z hZ hI n

end LatticeProb
