/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.EndpointRadiusGap at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.EndpointPathAdapter

 


set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.QPos

theorem dgff_radius_gap (n : ℕ) (hn : 4 ≤ n) :
    dgffInnerRadius n + 1 < dgffOuterRadius n := by
  have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel (by omega : 1 ≤ n)
  have hcast : (n : ℝ) - 1 / 2 = ((n - 1 : ℕ) : ℝ) + 1 / 2 := by
    have hh : (((n - 1 : ℕ) : ℝ) + 1) = (n : ℝ) := by exact_mod_cast hn1
    linarith
  have hp8 : 8 ≤ 2 ^ (n - 1) := by
    have hh : 3 ≤ n - 1 := by omega
    simpa using (Nat.pow_le_pow_right (by omega : 0 < 2) hh)
  have hsqrt : (5 / 4 : ℝ) ≤ Real.sqrt 2 := by
    have hh := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hnon := Real.sqrt_nonneg 2
    nlinarith
  have hpow : (2 : ℝ) ^ ((n : ℝ) - 1 / 2) =
      ((2 ^ (n - 1) : ℕ) : ℝ) * Real.sqrt 2 := by
    rw [hcast, Real.rpow_add (by norm_num : (0 : ℝ) < 2),
      Real.rpow_natCast, ← Real.sqrt_eq_rpow]
    norm_cast
  have hbound : (((2 ^ (n - 1) : ℕ) : ℝ) + 2) ≤
      (2 : ℝ) ^ ((n : ℝ) - 1 / 2) := by
    rw [hpow]
    have hr : (8 : ℝ) ≤ ((2 ^ (n - 1) : ℕ) : ℝ) := by exact_mod_cast hp8
    have hmul := mul_nonneg
      (show (0 : ℝ) ≤ ((2 ^ (n - 1) : ℕ) : ℝ) by positivity)
      (sub_nonneg.mpr hsqrt)
    nlinarith
  have hfloor : 2 ^ (n - 1) + 2 ≤ dgffOuterRadius n := by
    unfold dgffOuterRadius
    apply Nat.le_floor
    exact_mod_cast hbound
  unfold dgffInnerRadius
  omega

theorem dgff_annulus_subpath_of_full_path_four
    (n N : ℕ) (p : ℕ → DGFFSite n) (hn : 4 ≤ n)
    (hstart : latticeRadius (p 0).1 ≤ dgffInnerRadius n)
    (hend : dgffOuterRadius n ≤ latticeRadius (p N).1)
    (hpath : ∀ i < N, latticeAdjacent (p i).1 (p (i + 1)).1)
    (ξ : ℝ) (h : EuclideanSpace ℝ (DGFFSite n)) :
    ∃ q : List (DGFFSite n), IsDGFFAnnulusPath n q ∧
      dgffPathCost n ξ h q ≤
        dgffPathCost n ξ h (List.ofFn fun i : Fin (N + 1) => p i) :=
  dgff_annulus_subpath_of_full_path n N p (dgff_radius_gap n hn)
    hstart hend hpath ξ h

theorem dgffAnnulusDistance_le_fullPathCost_four
    (n N : ℕ) (p : ℕ → DGFFSite n) (hn : 4 ≤ n)
    (hstart : latticeRadius (p 0).1 ≤ dgffInnerRadius n)
    (hend : dgffOuterRadius n ≤ latticeRadius (p N).1)
    (hpath : ∀ i < N, latticeAdjacent (p i).1 (p (i + 1)).1)
    (ξ : ℝ) (h : EuclideanSpace ℝ (DGFFSite n)) :
    dgffAnnulusDistance n ξ h ≤
      dgffPathCost n ξ h (List.ofFn fun i : Fin (N + 1) => p i) :=
  dgffAnnulusDistance_le_fullPathCost n N p (dgff_radius_gap n hn)
    hstart hend hpath ξ h

end SupercriticalLQGUniqueness.B2.QPos
