import Mathlib.Probability.Kernel.Defs
import Mathlib.MeasureTheory.Constructions.Cylinders
import Mathlib.MeasureTheory.Measure.GiryMonad

/-! # Measurable families of measures on countable path spaces -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LatticeProb

/-- Finite measures on countable path spaces form a measurable family when their
finite-prefix singleton masses and total masses are measurable. -/
theorem measurable_measure_of_countable_prefixes {E S : Type*}
    [MeasurableSpace E] [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S]
    (μ : E → Measure (ℕ → S)) [∀ e, IsFiniteMeasure (μ e)]
    (htotal : Measurable (fun e => μ e univ))
    (hprefix : ∀ (n : ℕ) (s : {i : ℕ // i ∈ Finset.Iic n} → S),
      Measurable (fun e => μ e (cylinder (Finset.Iic n) {s}))) :
    Measurable μ := by
  apply Measurable.measure_of_isPiSystem generateFrom_measurableCylinders.symm
    isPiSystem_measurableCylinders ?_ htotal
  intro t ht
  obtain ⟨n, A, hA, rfl⟩ : ∃ n A, MeasurableSet A ∧ t = cylinder (Finset.Iic n) A := by
    simpa [measurableCylinders_nat] using ht
  have hrestrict : Measurable (fun f : ℕ → S => (Finset.Iic n).restrict f) := by
    apply Measurable.of_eval
    intro i
    exact measurable_pi_apply (i : ℕ)
  have heq (e : E) : μ e (cylinder (Finset.Iic n) A) =
      ∑' s : A, μ e (cylinder (Finset.Iic n) {s.1}) := by
    symm
    exact tsum_measure_preimage_singleton (to_countable A)
      (fun s _ => hrestrict (measurableSet_singleton s))
  simp_rw [heq]
  exact Measurable.tsum (fun s => hprefix n s.1)

/-- A measurable family of path measures defines a kernel. -/
noncomputable def countablePathKernel {E S : Type*}
    [MeasurableSpace E] [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S]
    (μ : E → Measure (ℕ → S)) [∀ e, IsFiniteMeasure (μ e)]
    (htotal : Measurable (fun e => μ e univ))
    (hprefix : ∀ (n : ℕ) (s : {i : ℕ // i ∈ Finset.Iic n} → S),
      Measurable (fun e => μ e (cylinder (Finset.Iic n) {s}))) :
    Kernel E (ℕ → S) :=
  ⟨μ, measurable_measure_of_countable_prefixes μ htotal hprefix⟩

/-- A uniform bound on the total masses makes the path kernel finite. -/
theorem isFiniteKernel_countablePathKernel {E S : Type*}
    [MeasurableSpace E] [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S]
    (μ : E → Measure (ℕ → S)) [∀ e, IsFiniteMeasure (μ e)]
    (htotal : Measurable (fun e => μ e univ))
    (hprefix : ∀ (n : ℕ) (s : {i : ℕ // i ∈ Finset.Iic n} → S),
      Measurable (fun e => μ e (cylinder (Finset.Iic n) {s})))
    (C : ℝ≥0∞) (hC : C < ∞) (hbound : ∀ e, μ e univ ≤ C) :
    IsFiniteKernel (countablePathKernel μ htotal hprefix) :=
  ⟨⟨C, hC, hbound⟩⟩

end LatticeProb
