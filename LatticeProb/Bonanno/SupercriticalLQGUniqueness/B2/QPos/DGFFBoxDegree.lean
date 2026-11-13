/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.DGFFBoxDegree at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.DGFFWalkGreen
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.DGFFBoxConnected

 

set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.QPos

attribute [local instance] Classical.propDecidable

private theorem interiorSites_mem_iff (n : ℕ) (z : ℤ × ℤ) :
    z ∈ interiorSites n ↔
      -interiorRadius n ≤ z.1 ∧ z.1 ≤ interiorRadius n ∧
      -interiorRadius n ≤ z.2 ∧ z.2 ≤ interiorRadius n := by
  simp [interiorSites, Finset.mem_product, Finset.mem_Icc, and_assoc]

private def latticeNeighbors (z : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  {(z.1 + 1, z.2), (z.1 - 1, z.2),
    (z.1, z.2 + 1), (z.1, z.2 - 1)}

private theorem adjacent_iff_mem_neighbors (z w : ℤ × ℤ) :
    latticeAdjacent z w ↔ w ∈ latticeNeighbors z := by
  rcases w with ⟨x, y⟩
  simp only [latticeAdjacent, latticeNeighbors, Finset.mem_insert,
    Finset.mem_singleton, Prod.mk.injEq]

private theorem neighborCount (n : ℕ) (z : DGFFSite n) :
    (∑ w : DGFFSite n,
      if latticeAdjacent z.1 w.1 then (1 : ℝ) else 0) =
      ((latticeNeighbors z.1 ∩ interiorSites n).card : ℝ) := by
  classical
  have hs : (∑ w : DGFFSite n,
      if latticeAdjacent z.1 w.1 then (1 : ℝ) else 0) =
      ∑ w ∈ interiorSites n,
        if latticeAdjacent z.1 w then (1 : ℝ) else 0 := by
    exact (Finset.sum_subtype (interiorSites n) (by simp)
      (fun w => if latticeAdjacent z.1 w then (1 : ℝ) else 0)).symm
  rw [hs]
  simp only [← Finset.sum_filter]
  have heq : (interiorSites n).filter (latticeAdjacent z.1) =
      latticeNeighbors z.1 ∩ interiorSites n := by
    ext w
    simp [adjacent_iff_mem_neighbors, and_comm]
  rw [heq]
  simp

private theorem neighborCount_formula (z : ℤ × ℤ) (S : Finset (ℤ × ℤ)) :
    ((latticeNeighbors z ∩ S).card : ℝ) =
      (if (z.1 + 1, z.2) ∈ S then 1 else 0) +
      (if (z.1 - 1, z.2) ∈ S then 1 else 0) +
      (if (z.1, z.2 + 1) ∈ S then 1 else 0) +
      (if (z.1, z.2 - 1) ∈ S then 1 else 0) := by
  classical
  have h1 : (z.1 + 1, z.2) ∉
      ({(z.1 - 1, z.2), (z.1, z.2 + 1), (z.1, z.2 - 1)} : Finset (ℤ × ℤ)) := by
    simp [Prod.mk.injEq]
    omega
  have h2 : (z.1 - 1, z.2) ∉
      ({(z.1, z.2 + 1), (z.1, z.2 - 1)} : Finset (ℤ × ℤ)) := by
    simp [Prod.mk.injEq]
  have h3 : (z.1, z.2 + 1) ∉
      ({(z.1, z.2 - 1)} : Finset (ℤ × ℤ)) := by
    simp [Prod.mk.injEq]
    omega
  have hs : ((latticeNeighbors z ∩ S).card : ℝ) =
      ∑ w ∈ latticeNeighbors z, if w ∈ S then (1 : ℝ) else 0 := by
    rw [← Finset.sum_filter]
    have heq : (latticeNeighbors z).filter (· ∈ S) = latticeNeighbors z ∩ S := by
      ext w
      simp
    rw [heq]
    simp
  rw [hs]
  unfold latticeNeighbors
  rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_insert h3]
  by_cases hlast : (z.1, z.2 - 1) ∈ S <;> simp [hlast] <;> ring

 

theorem box_totalRate_eq (n : ℕ) (z : DGFFSite n) :
    (boxConductances n).totalRate z = 2 / Real.pi := by
  let r := interiorRadius n
  have hz := (interiorSites_mem_iff n z.1).mp z.property
  have hr : (z.1.1 + 1, z.1.2) ∈ interiorSites n ↔ z.1.1 < r := by
    rw [interiorSites_mem_iff]
    dsimp [r] at *
    omega
  have hl : (z.1.1 - 1, z.1.2) ∈ interiorSites n ↔ -r < z.1.1 := by
    rw [interiorSites_mem_iff]
    dsimp [r] at *
    omega
  have hu : (z.1.1, z.1.2 + 1) ∈ interiorSites n ↔ z.1.2 < r := by
    rw [interiorSites_mem_iff]
    dsimp [r] at *
    omega
  have hd : (z.1.1, z.1.2 - 1) ∈ interiorSites n ↔ -r < z.1.2 := by
    rw [interiorSites_mem_iff]
    dsimp [r] at *
    omega
  have hsum : (∑ w : DGFFSite n, (boxConductances n).edge z w) =
      dgffConductance * ((latticeNeighbors z.1 ∩ interiorSites n).card : ℝ) := by
    change (∑ w : DGFFSite n,
      if latticeAdjacent z.1 w.1 then dgffConductance else 0) = _
    conv_lhs =>
      arg 2
      ext w
      rw [show (if latticeAdjacent z.1 w.1 then dgffConductance else 0) =
        dgffConductance * (if latticeAdjacent z.1 w.1 then (1 : ℝ) else 0) by
        split_ifs <;> ring]
    rw [← Finset.mul_sum, neighborCount]
  rw [WiredConductances.totalRate, hsum, neighborCount_formula]
  change dgffConductance *
    ((if z.1.1 = -r then (1 : ℝ) else 0) +
      (if z.1.1 = r then 1 else 0) +
      (if z.1.2 = -r then 1 else 0) +
      (if z.1.2 = r then 1 else 0)) +
    dgffConductance *
    ((if (z.1.1 + 1, z.1.2) ∈ interiorSites n then 1 else 0) +
      (if (z.1.1 - 1, z.1.2) ∈ interiorSites n then 1 else 0) +
      (if (z.1.1, z.1.2 + 1) ∈ interiorSites n then 1 else 0) +
      (if (z.1.1, z.1.2 - 1) ∈ interiorSites n then 1 else 0)) = _
  simp only [hr, hl, hu, hd]
  have hxR : (if z.1.1 = r then (1 : ℝ) else 0) +
      (if z.1.1 < r then 1 else 0) = 1 := by
    by_cases h : z.1.1 = r
    · simp [h]
    · have hlt : z.1.1 < r := by omega
      simp [h, hlt]
  have hxL : (if z.1.1 = -r then (1 : ℝ) else 0) +
      (if -r < z.1.1 then 1 else 0) = 1 := by
    by_cases h : z.1.1 = -r
    · simp [h]
    · have hlt : -r < z.1.1 := by omega
      simp [h, hlt]
  have hyU : (if z.1.2 = r then (1 : ℝ) else 0) +
      (if z.1.2 < r then 1 else 0) = 1 := by
    by_cases h : z.1.2 = r
    · simp [h]
    · have hlt : z.1.2 < r := by omega
      simp [h, hlt]
  have hyD : (if z.1.2 = -r then (1 : ℝ) else 0) +
      (if -r < z.1.2 then 1 else 0) = 1 := by
    by_cases h : z.1.2 = -r
    · simp [h]
    · have hlt : -r < z.1.2 := by omega
      simp [h, hlt]
  let B : ℝ :=
    (if z.1.1 = -r then 1 else 0) + (if z.1.1 = r then 1 else 0) +
    (if z.1.2 = -r then 1 else 0) + (if z.1.2 = r then 1 else 0)
  let I : ℝ :=
    (if z.1.1 < r then 1 else 0) + (if -r < z.1.1 then 1 else 0) +
    (if z.1.2 < r then 1 else 0) + (if -r < z.1.2 then 1 else 0)
  have hfour : B + I = 4 := by
    dsimp [B, I]
    linarith only [hxR, hxL, hyU, hyD]
  change dgffConductance * B + dgffConductance * I = 2 / Real.pi
  rw [← mul_add, hfour]
  unfold dgffConductance
  field_simp
  ring

 

theorem box_killedTransition_apply (n : ℕ) (z w : DGFFSite n) :
    (boxConductances n).killedTransition z w =
      if latticeAdjacent z.1 w.1 then (1 / 4 : ℝ) else 0 := by
  rw [WiredConductances.killedTransition, box_totalRate_eq]
  change (if latticeAdjacent z.1 w.1 then dgffConductance else 0) /
    (2 / Real.pi) = _
  split_ifs <;> simp [dgffConductance] <;> field_simp <;> norm_num

 

end SupercriticalLQGUniqueness.B2.QPos
