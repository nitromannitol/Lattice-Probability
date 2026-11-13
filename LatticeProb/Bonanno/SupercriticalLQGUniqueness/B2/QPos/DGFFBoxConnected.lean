/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.DGFFBoxConnected at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.DGFFPositive
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.DGFFBox

 


set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.QPos

private theorem site_coordinates {n : ℕ} (z : DGFFSite n) :
    -interiorRadius n ≤ z.1.1 ∧ z.1.1 ≤ interiorRadius n ∧
    -interiorRadius n ≤ z.1.2 ∧ z.1.2 ≤ interiorRadius n := by
  have hz := z.property
  have hz' := Finset.mem_product.mp hz
  have hx := Finset.mem_Icc.mp hz'.1
  have hy := Finset.mem_Icc.mp hz'.2
  exact ⟨hx.1, hx.2, hy.1, hy.2⟩

 
private theorem box_edge_of_horizontal_step (n : ℕ) (z w : DGFFSite n)
    (hx : w.1.1 = z.1.1 + 1) (hy : w.1.2 = z.1.2) :
    0 < (boxConductances n).edge z w := by
  have hAdj : latticeAdjacent z.1 w.1 := Or.inl ⟨hx, hy⟩
  simp [boxConductances, hAdj, dgffConductance_pos]

 
private theorem box_boundary_pos_right (n : ℕ) (z : DGFFSite n)
    (hz : z.1.1 = interiorRadius n) :
    0 < (boxConductances n).boundary z := by
  change 0 < boxBoundaryConductance n z
  unfold boxBoundaryConductance
  have hsum : (0 : ℝ) <
      (if z.1.1 = -interiorRadius n then 1 else 0) +
      (if z.1.1 = interiorRadius n then 1 else 0) +
      (if z.1.2 = -interiorRadius n then 1 else 0) +
      (if z.1.2 = interiorRadius n then 1 else 0) := by
    simp only [hz, ↓reduceIte]
    split_ifs <;> norm_num
  exact mul_pos dgffConductance_pos hsum

 

theorem box_reachesBoundary (n : ℕ) :
    (boxConductances n).ReachesBoundary := by
  intro z
  let R : ℤ := interiorRadius n
  have hz := site_coordinates z
  let d : ℕ := (R - z.1.1).toNat
  have hd : (d : ℤ) = R - z.1.1 := by
    dsimp [d]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hz.2.1)
  let site : (k : ℕ) → k ≤ d → DGFFSite n := fun k hk =>
    ⟨(z.1.1 + (k : ℤ), z.1.2), by
      apply Finset.mem_product.mpr
      constructor
      · apply Finset.mem_Icc.mpr
        constructor <;> omega
      · exact Finset.mem_Icc.mpr ⟨hz.2.2.1, hz.2.2.2⟩⟩
  have hstep (k : ℕ) (hk : k + 1 ≤ d) :
      0 < (boxConductances n).edge
        (site k (Nat.le_trans (Nat.le_succ k) hk)) (site (k+1) hk) := by
    apply box_edge_of_horizontal_step
    · dsimp [site]
      omega
    · rfl
  have hwalk : ∀ k : ℕ, ∀ hk : k ≤ d,
      Relation.ReflTransGen
        (fun u v : DGFFSite n => 0 < (boxConductances n).edge u v)
        z (site k hk) := by
    intro k
    induction k with
    | zero =>
        intro hk
        convert Relation.ReflTransGen.refl using 1
        apply Subtype.ext
        simp [site]
    | succ k ih =>
        intro hk
        have hk0 : k ≤ d := Nat.le_trans (Nat.le_succ k) hk
        exact (ih hk0).tail (hstep k hk)
  let b := site d le_rfl
  refine ⟨b, ?_, hwalk d le_rfl⟩
  apply box_boundary_pos_right
  dsimp [b, site]
  omega

 

theorem box_precision_posDef (n : ℕ) :
    (boxConductances n).precision.PosDef :=
  (boxConductances n).precision_posDef_of_reachesBoundary
    (box_reachesBoundary n)

end SupercriticalLQGUniqueness.B2.QPos
