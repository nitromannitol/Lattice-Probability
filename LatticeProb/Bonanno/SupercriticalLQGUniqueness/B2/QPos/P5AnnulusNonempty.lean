/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P5AnnulusNonempty at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.EndpointRadiusGap

 


set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.QPos

theorem dgffOuterRadius_lt_box (n : ℕ) : dgffOuterRadius n < 2 ^ n := by
  unfold dgffOuterRadius
  have hp : (2 : ℝ) ^ ((n : ℝ) - 1 / 2) < ((2 ^ n : ℕ) : ℝ) := by
    calc
      _ < (2 : ℝ) ^ (n : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
      _ = _ := by norm_cast
  exact (Nat.floor_lt (by positivity)).2 hp

theorem dgff_annulusPath_nonempty (n : ℕ) (hn : 4 ≤ n) :
    Nonempty {p : List (DGFFSite n) // IsDGFFAnnulusPath n p} := by
  let R := dgffOuterRadius n
  have hR : R < 2 ^ n := dgffOuterRadius_lt_box n
  have hRz : (R : ℤ) ≤ interiorRadius n := by
    have hpow : ((2 ^ n : ℕ) : ℤ) = (2 : ℤ) ^ n := by norm_cast
    unfold interiorRadius
    omega
  have hR0 : 0 ≤ interiorRadius n := by
    have hpow : (0 : ℤ) < (2 : ℤ) ^ n := by positivity
    unfold interiorRadius
    omega
  let p : ℕ → DGFFSite n := fun k =>
    ⟨(((min k R : ℕ) : ℤ), 0), by
      apply Finset.mem_product.mpr
      constructor
      · apply Finset.mem_Icc.mpr
        have hk : ((min k R : ℕ) : ℤ) ≤ (R : ℤ) := by exact_mod_cast Nat.min_le_right k R
        omega
      · apply Finset.mem_Icc.mpr
        omega⟩
  have hstart : latticeRadius (p 0).1 ≤ dgffInnerRadius n := by
    simp [p, latticeRadius]
  have hend : dgffOuterRadius n ≤ latticeRadius (p R).1 := by
    simp [p, latticeRadius, R]
  have hpath : ∀ i < R, latticeAdjacent (p i).1 (p (i + 1)).1 := by
    intro i hi
    have hi0 : min i R = i := Nat.min_eq_left (le_of_lt hi)
    have hi1 : min (i + 1) R = i + 1 := Nat.min_eq_left (by omega)
    change latticeAdjacent ((min i R : ℕ), 0) ((min (i + 1) R : ℕ), 0)
    exact Or.inl ⟨by simp [hi0, hi1], rfl⟩
  obtain ⟨q, hq, _⟩ := dgff_annulus_subpath_of_full_path_four
    n R p hn hstart hend hpath 0 (0 : EuclideanSpace ℝ (DGFFSite n))
  exact ⟨⟨q, hq⟩⟩

end SupercriticalLQGUniqueness.B2.QPos
