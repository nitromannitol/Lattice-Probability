/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.TrajectoryIdentification at commit fdb5cad;
   local import paths and lint settings are adjusted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.TrajectoryCoupling

set_option linter.unusedSimpArgs false

/-! Identify the full law of an actual sequence from its initial law and the
joint laws of each observed finite history with its next state. -/

open MeasureTheory ProbabilityTheory Set Preorder
open scoped ENNReal

namespace BouRabeeGwynne.TrajectoryCoupling

variable {X : Type*} [MeasurableSpace X]

theorem eq_trajMeasure_of_history_next (ρ : Measure (ℕ → X)) [IsFiniteMeasure ρ]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (κ : (n : ℕ) → Kernel (Finset.Iic n → X) X) [∀ n, IsMarkovKernel (κ n)]
    (hinit : ρ.map (fun ω ↦ ω 0) = μ)
    (hstep : ∀ n, ρ.map (fun ω ↦ (frestrictLe n ω, ω (n + 1))) =
      ρ.map (frestrictLe n) ⊗ₘ κ n) :
    ρ = Kernel.trajMeasure (X := fun _ ↦ X) μ κ := by
  apply measure_eq_of_prefix_eq
  intro n
  induction n with
  | zero =>
    have hc : Measurable (fun x : X ↦ fun _ : Finset.Iic 0 ↦ x) :=
      Measurable.of_eval (fun _ ↦ measurable_id)
    have h0 : Measurable (fun ω : ℕ → X ↦ ω 0) := measurable_pi_apply 0
    rw [prefix_zero, ← hinit,
      Measure.map_map hc h0]
    congr 1
    funext ω i
    have hi : i.val = 0 := by have := Finset.mem_Iic.mp i.property; omega
    simp [Function.comp_def, frestrictLe_apply, hi]
  | succ n ih =>
    rw [prefix_succ, ← ih, ← hstep n,
      Measure.map_map (measurable_append n) (by fun_prop)]
    congr 1
    funext ω
    exact (append_restrict n ω).symm

theorem map_eq_trajMeasure_of_history_next {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (Γ : Ω → ℕ → X) (hΓ : Measurable Γ)
    (μ : Measure X) [IsProbabilityMeasure μ]
    (κ : (n : ℕ) → Kernel (Finset.Iic n → X) X) [∀ n, IsMarkovKernel (κ n)]
    (hinit : P.map (fun ω ↦ Γ ω 0) = μ)
    (hstep : ∀ n, P.map (fun ω ↦ (frestrictLe n (Γ ω), Γ ω (n + 1))) =
      P.map (fun ω ↦ frestrictLe n (Γ ω)) ⊗ₘ κ n) :
    P.map Γ = Kernel.trajMeasure (X := fun _ ↦ X) μ κ := by
  apply eq_trajMeasure_of_history_next (P.map Γ) μ κ
  · simpa only [Measure.map_map (measurable_pi_apply 0) hΓ,
      Function.comp_def] using hinit
  · intro n
    simpa only [Measure.map_map
      ((measurable_frestrictLe n).prodMk (measurable_pi_apply (n + 1))) hΓ,
      Measure.map_map (measurable_frestrictLe n) hΓ, Function.comp_def] using hstep n

end BouRabeeGwynne.TrajectoryCoupling
