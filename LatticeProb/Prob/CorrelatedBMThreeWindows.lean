import LatticeProb.Prob.CorrelatedBMWindowIndependence

/-! # Three independent Brownian windows

Two outer increment processes are jointly independent of an increment on a
third disjoint window. -/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set

namespace LatticeProb.CorrelatedBM

open MatedCRTHarmonic.MatedCRT

/-- For disjoint increment windows, each pair of window processes is
independent, and the pair of outer processes is independent of any coordinate
increment across a third window. -/
theorem indep_outer_windows_and_middle_increment {ι : Type*} {γ : ℝ}
    {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) (l r : ι → ℝ)
    (hsep : ∀ i j, i ≠ j → r i ≤ l j ∨ r j ≤ l i)
    (i j k : ι) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hk : l k ≤ r k) (c : Fin 2) :
    let W := fun n ω (p : Fin 2 × {x : ℝ // x ∈ Icc (l n) (r n)}) =>
      coneIncr p.1 p.2.1 (l n) ω
    IndepFun (W i) (W j) μ ∧
      IndepFun (fun ω => (W i ω, W j ω)) (coneIncr c (r k) (l k)) μ := by
  dsimp only
  let W := fun n ω (p : Fin 2 × {x : ℝ // x ∈ Icc (l n) (r n)}) =>
    coneIncr p.1 p.2.1 (l n) ω
  have hW : iIndepFun W μ := iIndepFun_increment_windows hμ l r hsep
  have hmeas : ∀ n, Measurable (W n) := by
    intro n
    exact measurable_pi_iff.mpr fun p => measurable_coneIncr p.1 p.2.1 (l n)
  refine ⟨hW.indepFun hij, ?_⟩
  have h := hW.indepFun_prodMk hmeas i j k hik hjk
  have heval : Measurable (fun f : Fin 2 × {x : ℝ // x ∈ Icc (l k) (r k)} → ℝ =>
      f (c, ⟨r k, ⟨hk, le_rfl⟩⟩)) := measurable_pi_apply _
  exact h.comp measurable_id heval

end LatticeProb.CorrelatedBM
