import LatticeProb.Prob.Percolation.LatticeIncidentBonds

/-!
# Exact number of bonds incident to an integer box

Unique positive orientation counts every interior and crossing bond exactly once.
The formula also covers radius zero and dimension zero.
-/

namespace LatticeProb.Percolation.LatticeIncident

open LatticeProb

noncomputable section

variable {d : ℕ}

/-- There are `2R+2` choices on the bond axis and `2R+1` on every other axis. -/
theorem card_lowerSites (R : ℕ) (i : Fin d) :
    (lowerSites R i).card = (2 * R + 2) * (2 * R + 1) ^ (d - 1) := by
  classical
  rw [lowerSites, Fintype.card_piFinset,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
  have haxis : (Finset.Icc (if i = i then -(R : ℤ) - 1 else -(R : ℤ)) R).card =
      2 * R + 2 := by
    rw [if_pos rfl, Int.card_Icc]
    omega
  rw [haxis]
  congr 1
  calc
    _ = ∏ _j ∈ (Finset.univ : Finset (Fin d)).erase i, (2 * R + 1) := by
      apply Finset.prod_congr rfl
      intro j hj
      have hji := (Finset.mem_erase.mp hj).1
      rw [if_neg hji, Int.card_Icc]
      omega
    _ = (2 * R + 1) ^ (d - 1) := by
      rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
        Finset.card_univ, Fintype.card_fin]

/-- Every incident bond is counted once, including all bonds crossing the box boundary. -/
theorem card_incidentBonds (d R : ℕ) :
    (incidentBonds d R).card = d * (2 * R + 2) * (2 * R + 1) ^ (d - 1) := by
  classical
  rw [incidentBonds_eq_biUnion, Finset.card_biUnion]
  · have himage : ∀ i : Fin d,
        ((lowerSites R i).image (positiveBond i)).card = (lowerSites R i).card := by
      intro i
      apply Finset.card_image_iff.mpr
      intro v _ w _ h
      exact (positiveBond_injective h).2
    simp only [himage, card_lowerSites, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
    exact (Nat.mul_assoc _ _ _).symm
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro e hei hej
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hei
    obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hej
    exact hij (positiveBond_injective hw.symm).1

/-- In dimension zero there are no bonds, including at radius zero. -/
theorem card_incidentBonds_zero_dimension (R : ℕ) :
    (incidentBonds 0 R).card = 0 := by
  rw [card_incidentBonds]
  simp only [Nat.zero_mul]

/-- At radius zero all `2d` bonds adjacent to the origin are prescribed. -/
theorem card_incidentBonds_zero_radius (d : ℕ) :
    (incidentBonds d 0).card = 2 * d := by
  norm_num [card_incidentBonds]
  omega

/-- The one-dimensional radius-zero cylinder prescribes two bonds. -/
theorem card_incidentBonds_one_zero : (incidentBonds 1 0).card = 2 := by
  rw [card_incidentBonds_zero_radius]

/-- The two-dimensional radius-zero cylinder prescribes four bonds. -/
theorem card_incidentBonds_two_zero : (incidentBonds 2 0).card = 4 := by
  rw [card_incidentBonds_zero_radius]

/-- The one-dimensional radius-one cylinder prescribes four bonds. -/
theorem card_incidentBonds_one_one : (incidentBonds 1 1).card = 4 := by
  norm_num [card_incidentBonds]

/-- The two-dimensional radius-one cylinder prescribes twenty-four bonds. -/
theorem card_incidentBonds_two_one : (incidentBonds 2 1).card = 24 := by
  norm_num [card_incidentBonds]

/-- Every upper-face outward bond is included, although its upper endpoint is outside. -/
theorem upper_crossing_mem (R : ℕ) (i : Fin d) :
    positiveBond i (fun _ => (R : ℤ)) ∈ incidentBonds d R ∧
      (fun j => (R : ℤ) + unit i j) ∉ boxFinset (0 : Site d) R := by
  constructor
  · apply mk_mem_incidentBonds.mpr
    refine ⟨Graph.Zd.adj_iff.mpr ⟨i, Or.inl rfl⟩, Or.inl ?_⟩
    rw [mem_centered_box]
    intro j
    constructor <;> omega
  · intro h
    have hi := mem_centered_box.mp h i
    simp only [unit, Pi.single_eq_same] at hi
    omega

end

end LatticeProb.Percolation.LatticeIncident
