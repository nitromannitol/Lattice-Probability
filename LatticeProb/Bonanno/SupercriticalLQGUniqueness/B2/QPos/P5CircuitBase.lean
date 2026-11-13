/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P5CircuitBase at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P5CircuitInput
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P5AnnulusNonempty

 


set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace SupercriticalLQGUniqueness.B2.QPos

private theorem weight_le_inclusivePathCost {V : Type*}
    (weight : V → ℝ) (hw : ∀ v, 0 ≤ weight v)
    (p : List V) (z : V) (hz : z ∈ p) :
    weight z ≤ inclusivePathCost weight p := by
  induction p with
  | nil => simp at hz
  | cons a p ih =>
      simp only [List.mem_cons] at hz
      simp only [inclusivePathCost, List.map_cons, List.sum_cons]
      rcases hz with rfl | hz
      · exact le_add_of_nonneg_right
          (inclusivePathCost_nonneg weight hw p)
      · have hp := ih hz
        have ha := hw a
        change weight z ≤ weight a + inclusivePathCost weight p
        linarith

 
theorem dgffCircuit_forces_distance (n : ℕ) (hn : 4 ≤ n)
    (ξ : Set.Ioi (0 : ℝ))
    (u : ℝ) (h : EuclideanSpace ℝ (DGFFSite n))
    (hc : ∃ p : List (DGFFSite n),
      IsDGFFAroundPath n p ∧ ∀ z ∈ p, -u ≤ h z) :
    Real.exp (-(ξ : ℝ) * u) ≤ dgffAnnulusDistance n (ξ : ℝ) h := by
  rcases hc with ⟨p, hp, hh⟩
  haveI : Nonempty {p : List (DGFFSite n) // IsDGFFAnnulusPath n p} :=
    dgff_annulusPath_nonempty n hn
  unfold dgffAnnulusDistance
  apply le_ciInf
  intro q
  obtain ⟨z, _hzp, hzq⟩ := hp.2.2.2.2 q.1 q.2
  have hz := hh z _hzp
  have hexp : Real.exp (-(ξ : ℝ) * u) ≤
      Real.exp ((ξ : ℝ) * h z) := by
    apply Real.exp_le_exp.mpr
    have hξ : 0 ≤ (ξ : ℝ) := le_of_lt ξ.property
    have hmul := mul_le_mul_of_nonneg_left hz hξ
    nlinarith
  exact hexp.trans (by
    change Real.exp ((ξ : ℝ) * h z) ≤
      inclusivePathCost (fun z => Real.exp ((ξ : ℝ) * h z)) q.1
    exact weight_le_inclusivePathCost
      (fun z : DGFFSite n => Real.exp ((ξ : ℝ) * h z))
      (fun z => (Real.exp_pos _).le) q.1 z hzq)

 

end SupercriticalLQGUniqueness.B2.QPos
