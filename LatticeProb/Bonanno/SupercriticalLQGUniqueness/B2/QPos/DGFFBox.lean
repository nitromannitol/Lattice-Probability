/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.DGFFBox at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.DGFFCore

 



set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.QPos

 
def interiorRadius (n : ℕ) : ℤ := (2 : ℤ) ^ n - 1

 
def interiorSites (n : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-interiorRadius n) (interiorRadius n)).product
    (Finset.Icc (-interiorRadius n) (interiorRadius n))

abbrev DGFFSite (n : ℕ) := {z : ℤ × ℤ // z ∈ interiorSites n}

noncomputable instance (n : ℕ) : Fintype (DGFFSite n) :=
  (interiorSites n).finite_toSet.fintype

 
def latticeAdjacent (z w : ℤ × ℤ) : Prop :=
  (w.1 = z.1 + 1 ∧ w.2 = z.2) ∨
  (w.1 = z.1 - 1 ∧ w.2 = z.2) ∨
  (w.1 = z.1 ∧ w.2 = z.2 + 1) ∨
  (w.1 = z.1 ∧ w.2 = z.2 - 1)

theorem latticeAdjacent_symm {z w : ℤ × ℤ} :
    latticeAdjacent z w → latticeAdjacent w z := by
  rintro (h | h | h | h)
  · exact Or.inr (Or.inl (by constructor <;> omega))
  · exact Or.inl (by constructor <;> omega)
  · exact Or.inr (Or.inr (Or.inr (by constructor <;> omega)))
  · exact Or.inr (Or.inr (Or.inl (by constructor <;> omega)))

theorem not_latticeAdjacent_self (z : ℤ × ℤ) : ¬ latticeAdjacent z z := by
  intro h
  rcases h with h | h | h | h <;> omega

 

def dgffConductance : ℝ := 1 / (2 * Real.pi)

theorem dgffConductance_pos : 0 < dgffConductance := by
  unfold dgffConductance
  positivity

 

def boxBoundaryConductance (n : ℕ) (z : DGFFSite n) : ℝ :=
  dgffConductance *
    ((if z.1.1 = -interiorRadius n then (1 : ℝ) else 0) +
     (if z.1.1 = interiorRadius n then (1 : ℝ) else 0) +
     (if z.1.2 = -interiorRadius n then (1 : ℝ) else 0) +
     (if z.1.2 = interiorRadius n then (1 : ℝ) else 0))

 
def boxConductances (n : ℕ) : WiredConductances (DGFFSite n) := by
  classical
  refine {
    edge := fun z w => if latticeAdjacent z.1 w.1 then dgffConductance else 0
    boundary := boxBoundaryConductance n
    edge_symm := ?_
    edge_self := ?_
    edge_nonneg := ?_
    boundary_nonneg := ?_ }
  ·
    intro z w
    by_cases h : latticeAdjacent z.1 w.1
    · simp [h, latticeAdjacent_symm h]
    · have h' : ¬ latticeAdjacent w.1 z.1 := fun h' => h (latticeAdjacent_symm h')
      simp [h, h']
  ·
    intro z
    simp [not_latticeAdjacent_self]
  ·
    intro z w
    split_ifs
    · exact dgffConductance_pos.le
    · exact le_rfl
  ·
    intro z
    unfold boxBoundaryConductance
    apply mul_nonneg dgffConductance_pos.le
    positivity

end SupercriticalLQGUniqueness.B2.QPos
