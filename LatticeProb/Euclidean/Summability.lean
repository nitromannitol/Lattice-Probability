import LatticeProb.Euclidean.Lattice
import LatticeProb.Euclidean.Cube
import LatticeProb.Euclidean.Shell

/-!
# Summability of the radial error series

The series `∑_{w ≠ 0} |w|^{-(d+1)}` over the integer lattice, with the Euclidean radius, is
summable for `d ≥ 1`.  The proof groups the points by the integer part of their radius and
bounds each group by a shell count.  The constant `radialErrorConstant d` is the value of the
series over the nonzero points.
-/

noncomputable section

open scoped BigOperators
open LatticeProb.Euclidean.Lattice LatticeProb.Euclidean.Cube LatticeProb.Euclidean.Shell

namespace LatticeProb.Euclidean.Summability

/-- The contribution of one radial shell to the radial error series is at most `shellConstant d / n²`. -/
lemma shell_error_sum_bound (d : ℕ) (hd : 1 ≤ d) (n : ℕ) (s : Finset (Site d))
    (hs : ∀ w ∈ s, Nat.floor (radius (physical 1 w)) = n) :
    ∑ w ∈ s, radius (physical 1 w)^(-((d+1:ℕ):ℤ)) ≤
      shellConstant d * (1/(n:ℝ)^2) := by
  classical
  by_cases hn : n = 0
  · subst n
    have hz : ∀ w ∈ s, w = 0 := by
      intro w hw
      by_contra h
      have hge := (Nat.one_le_floor_iff _).mpr (lattice_radius_ge_one h)
      rw [hs w hw] at hge
      omega
    have hzero : ∀ w ∈ s, radius (physical 1 w)^(-((d+1:ℕ):ℤ)) = 0 := by
      intro w hw
      rw [hz w hw]
      have hr : radius (physical 1 (0 : Site d)) = 0 := by simp [radius, physical]
      rw [hr, zpow_neg, zpow_natCast]
      simp
    rw [Finset.sum_eq_zero hzero]
    simp
  · have hn' : 1 ≤ n := by omega
    have hnreal : (1:ℝ) ≤ n := by exact_mod_cast hn'
    have hnpos : (0:ℝ) < n := by exact_mod_cast (Nat.pos_of_ne_zero hn)
    have hdom : ∀ w ∈ s, (n:ℝ) ≤ radius (physical 1 w) ∧ radius (physical 1 w) < n+1 := by
      intro w hw
      constructor
      · rw [← hs w hw]
        exact Nat.floor_le (radius_nonneg _)
      · rw [← hs w hw]
        exact Nat.lt_floor_add_one _
    have hc := shell_card d hd n hnreal s hdom
    have hp : ∀ w ∈ s, radius (physical 1 w)^(-((d+1:ℕ):ℤ)) ≤ (n:ℝ)^(-((d+1:ℕ):ℤ)) := by
      intro w hw
      have ht := (hdom w hw).1
      have hi := inv_anti₀ hnpos ht
      have hpow := pow_le_pow_left₀ (inv_nonneg.mpr (hnpos.le.trans ht)) hi (d+1)
      simpa only [zpow_neg, zpow_natCast, inv_pow] using hpow
    calc
      _ ≤ ∑ _w ∈ s, (n:ℝ)^(-((d+1:ℕ):ℤ)) := Finset.sum_le_sum hp
      _ = (s.card:ℝ) * (n:ℝ)^(-((d+1:ℕ):ℤ)) := by simp
      _ ≤ (shellConstant d * (n:ℝ)^(d-1)) * (n:ℝ)^(-((d+1:ℕ):ℤ)) :=
        mul_le_mul_of_nonneg_right hc (zpow_nonneg hnpos.le _)
      _ = shellConstant d * (1/(n:ℝ)^2) := by
        rw [mul_assoc, ← zpow_natCast, ← zpow_add₀ hnpos.ne']
        have he : ((d-1:ℕ):ℤ) + -((d+1:ℕ):ℤ) = -2 := by omega
        rw [he]
        simp only [zpow_neg, zpow_ofNat, one_div]

/-- The radial error series `∑ |w|^{-(d+1)}` over all integer points is summable for `d ≥ 1`. -/
theorem euclidean_radial_error_summable (d : ℕ) (hd : 1 ≤ d) :
    Summable (fun w : Site d => radius (physical 1 w)^(-((d+1:ℕ):ℤ))) := by
  classical
  have hp : Summable (fun n : ℕ => 1/(n:ℝ)^2) := Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hg := hp.mul_left (shellConstant d)
  apply summable_of_sum_le (c := ∑' n : ℕ, shellConstant d * (1/(n:ℝ)^2))
    (fun w => zpow_nonneg (radius_nonneg _) _)
  intro u
  let g : Site d → ℕ := fun w => Nat.floor (radius (physical 1 w))
  have he := Finset.sum_fiberwise_of_maps_to (s := u) (t := u.image g)
    (fun w hw => Finset.mem_image_of_mem g hw)
    (fun w : Site d => radius (physical 1 w)^(-((d+1:ℕ):ℤ)))
  calc
    _ = ∑ n ∈ u.image g, ∑ w ∈ u.filter (fun w => g w = n),
        radius (physical 1 w)^(-((d+1:ℕ):ℤ)) := he.symm
    _ ≤ ∑ n ∈ u.image g, shellConstant d * (1/(n:ℝ)^2) := by
      apply Finset.sum_le_sum
      intro n _
      apply shell_error_sum_bound d hd
      intro w hw
      exact (Finset.mem_filter.mp hw).2
    _ ≤ _ := hg.sum_le_tsum _ (fun _ _ => by unfold shellConstant unitBallVolume; positivity)

/-- The radial error series over the nonzero integer points is summable for `d ≥ 1`. -/
theorem nonzero_radial_error_summable (d : ℕ) (hd : 1 ≤ d) :
    Summable (fun w : {w : Site d // w ≠ 0} =>
      radius (physical 1 w.val)^(-((d+1:ℕ):ℤ))) :=
  (euclidean_radial_error_summable d hd).subtype (fun w => w ≠ 0)

/-- The real-exponent radial error series over the nonzero integer points is summable for `d ≥ 1`. -/
theorem nonzero_radial_error_summable_real (d : ℕ) (hd : 1 ≤ d) :
    Summable (fun w : {w : Site d // w ≠ 0} =>
      Real.rpow (radius (physical 1 w.val)) (-(d:ℝ)-1)) := by
  have he : -(d:ℝ)-1 = -((d+1:ℕ):ℝ) := by push_cast; ring
  rw [he]
  exact (nonzero_radial_error_summable d hd).congr
    (fun w => (Real.rpow_neg_natCast (radius (physical 1 w.val)) (d+1)).symm)

/-- The global radial error constant `∑_{w ≠ 0} |w|^{-(d+1)}`; it depends only on `d`. -/
def radialErrorConstant (d : ℕ) : ℝ :=
  ∑' w : {w : Site d // w ≠ 0},
    Real.rpow (radius (physical 1 w.val)) (-(d : ℝ)-1)

/-- The global radial error constant is nonnegative. -/
lemma radialErrorConstant_nonneg (d : ℕ) : 0 ≤ radialErrorConstant d :=
  tsum_nonneg (fun _ => Real.rpow_nonneg (radius_nonneg _) _)

end LatticeProb.Euclidean.Summability
