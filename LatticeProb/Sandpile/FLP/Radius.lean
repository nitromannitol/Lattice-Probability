import LatticeProb.Sandpile.FLP.LowHeightOuter
import LatticeProb.Sandpile.FLP.SlabStabilizer
import LatticeProb.External.FeyLevinePeresRadius

/-!
# Radius bound for the abelian sandpile

The Euclidean outer bound for low backgrounds and the one-coordinate slab stabilizers imply
the cube radius bound of Fey, Levine and Peres, assuming the shell estimate of Levine and Peres.
-/

namespace LatticeProb.Sandpile.FLP

open LatticeProb LatticeProb.Sandpile

private theorem profile_le (d : ℕ) (h : ℤ) (hdh : (d : ℤ) ≤ h)
    (hh : h ≤ 2 * (d : ℤ) - 2) (r₀ r₁ : ℕ) (t : ℤ) :
    flpProfile d h r₀ r₁ t ≤ 2 * (d : ℤ) - 1 - h := by
  unfold flpProfile
  split_ifs <;> omega

private theorem profile_le_inside (d : ℕ) (h : ℤ) (hdh : (d : ℤ) ≤ h)
    (r₀ r₁ : ℕ) (t : ℤ) (ht : |t| < r₀) :
    flpProfile d h r₀ r₁ t ≤ (d : ℤ) - 1 - h := by
  unfold flpProfile
  split_ifs <;> omega

private theorem coord_abs_le_euclidNorm {d : ℕ} (x : Site d) (i : Fin d) :
    |(x i : ℝ)| ≤ euclidNorm x := by
  have hi := supNorm_le_iff.mp (show supNorm x ≤ supNorm x from le_rfl) i
  have hi' : |(x i : ℝ)| ≤ (supNorm x : ℝ) := by exact_mod_cast hi
  exact hi'.trans (supNorm_le_euclidNorm x)

private theorem coord_abs_le_neighbor_add {d : ℕ} (x : Site d) (i j : Fin d) :
    |(x i : ℝ)| ≤ euclidNorm (x + unit j) + 1 := by
  have hi := coord_abs_le_euclidNorm (x + unit j) i
  have hunit : |((unit j) i : ℝ)| ≤ 1 := by
    by_cases hij : i = j <;> simp [unit, hij]
  have heq : (x i : ℝ) = ((x + unit j) i : ℝ) - ((unit j) i : ℝ) := by simp
  rw [heq]
  have htri := abs_sub ((x + unit j) i : ℝ) ((unit j) i : ℝ)
  linarith

private theorem coord_abs_le_neighbor_sub {d : ℕ} (x : Site d) (i j : Fin d) :
    |(x i : ℝ)| ≤ euclidNorm (x - unit j) + 1 := by
  have hi := coord_abs_le_euclidNorm (x - unit j) i
  have hunit : |((unit j) i : ℝ)| ≤ 1 := by
    by_cases hij : i = j <;> simp [unit, hij]
  have heq : (x i : ℝ) = ((x - unit j) i : ℝ) + ((unit j) i : ℝ) := by simp
  rw [heq]
  have htri := abs_add_le ((x - unit j) i : ℝ) ((unit j) i : ℝ)
  linarith

private theorem lap_add {d : ℕ} (u v : Site d → ℤ) (x : Site d) :
    lap (fun y => u y + v y) x = lap u x + lap v x := by
  have heq : nbrSumZ (fun y => u y + v y) x = nbrSumZ u x + nbrSumZ v x := by
    unfold nbrSumZ
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  unfold lap
  rw [heq]
  ring

private theorem radius_of_low_odometer {d : ℕ} (_hd : 1 ≤ d) (h : ℤ)
    (hdh : (d : ℤ) ≤ h) (hh : h ≤ 2 * (d : ℤ) - 2) (n : ℕ) (ρ R : ℝ)
    (hρ : 0 < ρ) (hρR : ρ ≤ R) (hR1 : (flpR1 d h ρ : ℝ) ≤ R)
    (T : ℕ)
    (hstable : ∀ x : Site d, ((d : ℤ) - 1) + (n : ℤ) * dirac 0 x +
      lap (podo (fun y : Site d => ((d : ℤ) - 1) + (n : ℤ) * dirac 0 y) T) x < 2 * (d : ℤ))
    (hzero : ∀ x : Site d, ρ - 1 ≤ euclidNorm x →
      podo (fun y : Site d => ((d : ℤ) - 1) + (n : ℤ) * dirac 0 y) T x = 0) :
    ∀ t x, 0 < podo (fun y : Site d => h + (n : ℤ) * dirac 0 y) t x →
      ∀ i : Fin d, |(x i : ℝ)| ≤ R := by
  let w := podo (fun y : Site d => ((d : ℤ) - 1) + (n : ℤ) * dirac 0 y) T
  obtain ⟨g, hg0, hgzero, hglap⟩ := exists_slabStabilizer d h hdh hh ρ hρ.le
  have hr0 := (flpR0_spec d h hh ρ).1
  have hw0 : ∀ x, 0 ≤ w x := fun x => (podo_isLegal _).nonneg T x
  have hstab : ∀ (i : Fin d) (x : Site d),
      h + (n : ℤ) * dirac 0 x + lap (fun y => w y + g (y i)) x < 2 * (d : ℤ) := by
    intro i x
    rw [lap_add, hglap]
    by_cases hx : |(x i : ℝ)| < ρ
    · have hx0 : |x i| < (flpR0 d h ρ : ℤ) := by
        have hx' : |(x i : ℝ)| < (flpR0 d h ρ : ℝ) := hx.trans hr0
        exact_mod_cast hx'
      have hp := profile_le_inside d h hdh (flpR0 d h ρ) (flpR1 d h ρ) (x i) hx0
      have hs := hstable x
      change ((d : ℤ) - 1) + (n : ℤ) * dirac 0 x + lap w x < 2 * (d : ℤ) at hs
      omega
    · have hx' : ρ ≤ |(x i : ℝ)| := le_of_not_gt hx
      have hwn : ∀ j : Fin d, w (x + unit j) = 0 ∧ w (x - unit j) = 0 := by
        intro j
        have ha := coord_abs_le_neighbor_add x i j
        have hb := coord_abs_le_neighbor_sub x i j
        exact ⟨hzero _ (by linarith), hzero _ (by linarith)⟩
      have hwx : w x = 0 := hzero x (by have ht := coord_abs_le_euclidNorm x i; linarith)
      have hΔ : lap w x = 0 := by
        unfold lap nbrSumZ
        simp only [hwx, mul_zero, sub_zero]
        apply Finset.sum_eq_zero
        intro j _
        rw [(hwn j).1, (hwn j).2, add_zero]
      have hx0 : x ≠ 0 := by
        intro hx0
        subst x
        simp only [Pi.zero_apply, Int.cast_zero, abs_zero] at hx'
        linarith
      have hp := profile_le d h hdh hh (flpR0 d h ρ) (flpR1 d h ρ) (x i)
      rw [hΔ, dirac_of_ne hx0, mul_zero, add_zero]
      omega
  intro t x htop i
  by_contra hx
  have hx' : R < |(x i : ℝ)| := lt_of_not_ge hx
  have hwx : w x = 0 := hzero x (by have ht := coord_abs_le_euclidNorm x i; linarith)
  have hgx : g (x i) = 0 := by
    apply hgzero
    have hc : (flpR1 d h ρ : ℝ) - 1 ≤ |(x i : ℝ)| := by linarith
    exact_mod_cast hc
  have hle := le_of_isLegalToppling
    (podo_isLegal (fun y : Site d => h + (n : ℤ) * dirac 0 y))
    (fun y => add_nonneg (hw0 y) (hg0 (y i))) (hstab i) t x
  rw [hwx, hgx, add_zero] at hle
  omega

private theorem radius_tendsto (d : ℕ) (hd : 0 < d) :
    Filter.Tendsto (fun n : ℕ => ((n : ℝ) / omegaD d) ^ (1 / (d : ℝ)))
      Filter.atTop Filter.atTop := by
  have hd' : 0 < (d : ℝ) := by exact_mod_cast hd
  have hn : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hdiv : Filter.Tendsto (fun n : ℕ => (n : ℝ) / omegaD d) Filter.atTop Filter.atTop :=
    (Filter.tendsto_div_const_atTop_of_pos (omegaD_pos d)).2 hn
  exact (tendsto_rpow_atTop (by positivity : 0 < 1 / (d : ℝ))).comp hdiv

private theorem radius_bounds (d h ε r : ℝ) (hd : 0 < d) (hε : 0 < ε)
    (hq : 0 < 2 * d - 1 - h) (hqd : 2 * d - 1 - h ≤ d) (hr : 0 ≤ r)
    (hlarge : d ≤ (ε / (2 * (2 * d - 1 - h))) * r) :
    (1 + ε / (2 * d)) * r ≤ ((d + ε) / (2 * d - 1 - h)) * r ∧
      d * (((1 + ε / (2 * d)) * r) / (2 * d - 1 - h) + 1) ≤
        ((d + ε) / (2 * d - 1 - h)) * r := by
  let q := 2 * d - 1 - h
  have hq0 : 0 < q := hq
  have hqd' : q ≤ d := hqd
  have hmul := mul_le_mul_of_nonneg_left hqd' (show 0 ≤ ε / (2 * d) by positivity)
  have heps : (ε / (2 * d)) * d = ε / 2 := by field_simp
  have hcoef : 1 + ε / (2 * d) ≤ (d + ε) / q := by
    apply (le_div_iff₀ hq0).2
    nlinarith
  constructor
  · exact mul_le_mul_of_nonneg_right hcoef hr
  · have heq1 : d * (((1 + ε / (2 * d)) * r) / q + 1) =
        ((d + ε / 2) / q) * r + d := by
      field_simp
    have heq2 : ((d + ε) / q) * r =
        ((d + ε / 2) / q) * r + (ε / (2 * q)) * r := by ring
    rw [heq1, heq2]
    linarith

/-- The radius bound of Fey, Levine and Peres follows from the shell estimate of
Levine and Peres. -/
theorem feyLevinePeresRadius_of_shell (hLP : LatticeProb.External.LevinePeresShellBound) :
    LatticeProb.External.FeyLevinePeresRadius := by
  intro d h hdh hh ε hε
  have hd2 : 2 ≤ d := by omega
  have hd1 : 1 ≤ d := by omega
  have hdreal : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hhreal : (h : ℝ) ≤ 2 * (d : ℝ) - 2 := by exact_mod_cast hh
  have hdhreal : (d : ℝ) ≤ h := by exact_mod_cast hdh
  let q : ℝ := 2 * (d : ℝ) - 1 - h
  have hq : 0 < q := by dsimp [q]; linarith
  have hqd : q ≤ d := by dsimp [q]; linarith
  let r : ℕ → ℝ := fun n => ((n : ℝ) / omegaD d) ^ (1 / (d : ℝ))
  have hr : Filter.Tendsto r Filter.atTop Filter.atTop :=
    radius_tendsto d (by omega)
  have hcoef : 0 < ε / (2 * q) := by positivity
  have hg : Filter.Tendsto (fun n : ℕ => (ε / (2 * q)) * r n)
      Filter.atTop Filter.atTop :=
    (Filter.tendsto_const_mul_atTop_of_pos hcoef).2 hr
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp ((Filter.tendsto_atTop.mp hg) d)
  obtain ⟨n1, hn1⟩ := lowHeight_outer hLP d hd2 ε hε
  refine ⟨max 1 (max N n1), ?_⟩
  intro n hn x hx i
  have hn0 : 1 ≤ n := (le_max_left _ _).trans hn
  have hnN : N ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hnn1 : n1 ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hrpos : 0 < r n := by
    dsimp [r]
    apply Real.rpow_pos_of_pos
    exact div_pos (by exact_mod_cast (show 0 < n by omega)) (omegaD_pos d)
  let ρ : ℝ := (1 + ε / (2 * d)) * r n
  let R : ℝ := (((d : ℝ) + ε) / q) * r n
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hlarge : (d : ℝ) ≤ (ε / (2 * q)) * r n := hN n hnN
  have hbounds := radius_bounds (d : ℝ) h ε (r n) hdreal hε hq hqd hrpos.le hlarge
  have hρR : ρ ≤ R := hbounds.1
  have hR1 : (flpR1 d h ρ : ℝ) ≤ R :=
    (flpR1_le d h hdh hh ρ hρ.le).trans hbounds.2
  have hsmall : (d : ℤ) - 1 ≤ 2 * (d : ℤ) - 2 := by
    have : (1 : ℤ) ≤ d := by exact_mod_cast hd1
    omega
  obtain ⟨T, _, hstable⟩ := stabilizable_of_le d hd1 ((d : ℤ) - 1) hsmall n
  have hzero : ∀ y : Site d, ρ - 1 ≤ euclidNorm y →
      podo (fun z : Site d => ((d : ℤ) - 1) + (n : ℤ) * dirac 0 z) T y = 0 := by
    intro y hy
    exact hn1 n hnn1 T y hy
  obtain ⟨t, ht⟩ := hx
  have hout := radius_of_low_odometer hd1 h hdh hh n ρ R hρ hρR hR1 T hstable hzero t x ht i
  change |(x i : ℝ)| ≤ R
  exact hout

end LatticeProb.Sandpile.FLP

