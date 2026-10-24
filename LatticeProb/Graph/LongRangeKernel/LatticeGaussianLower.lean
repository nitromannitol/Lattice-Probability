import LatticeProb.Graph.LongRangeKernel.LatticeDistance
import LatticeProb.Walk.SRWMultinomial
import LatticeProb.Walk.BinomialLower
import LatticeProb.Walk.LocalCLTWindow
import LatticeProb.Walk.SRWPos
import LatticeProb.Walk.SRWDiag
import LatticeProb.Walk.RangeBox

/-!
# Lower bounds for the lattice heat kernel

A single reachable path gives an exponential lower bound, with the parity correction
implemented by adding one time step. The paired local central limit theorem also gives
a Gaussian lower estimate on the unit diffusive window in graph distance. Single-path
estimates give the complementary outer linear region. Parity-corrected finite boxes
and floor time increments give fixed-time chaining in the intermediate region. Together
these prove the full Gaussian lower antecedent in the MSC volume normalization.
-/

namespace LatticeProb.Graph.LongRangeKernel

open LatticeProb

noncomputable section

variable {d : ℕ}

/-- A reachable site receives at least the probability of one prescribed walk path. -/
theorem srwHeat_ge_single_path (hd : 0 < d) {n : ℕ} {x : Site d}
    (hle : graphNorm x ≤ n) (hpar : graphNorm x % 2 = n % 2) :
    (1 / (2 * (d : ℝ))) ^ n ≤ srwHeat d n x := by
  induction n generalizing x with
  | zero =>
      have hx : x = 0 := graphNorm_eq_zero_iff.mp (by omega)
      simp [hx]
  | succ n ih =>
      obtain ⟨a, hle', hpar'⟩ : ∃ a : Dir d,
          graphNorm (x + dirVec a) ≤ n ∧
          graphNorm (x + dirVec a) % 2 = n % 2 := by
        by_cases hx : x = 0
        · refine ⟨(⟨0, hd⟩, true), ?_, ?_⟩ <;>
            simp only [hx, zero_add, graphNorm_dirVec, graphNorm_zero] at * <;> omega
        · obtain ⟨a, ha⟩ := exists_dirVec_graphNorm_eq_sub_one hx
          have hpos : 0 < graphNorm x :=
            Nat.pos_of_ne_zero (fun h => hx (graphNorm_eq_zero_iff.mp h))
          exact ⟨a, by omega, by omega⟩
      have hterm := ih hle' hpar'
      have hsum := Finset.single_le_sum
        (f := fun b : Dir d => srwHeat d n (x + dirVec b))
        (fun b _ => srwHeat_nonneg n _) (Finset.mem_univ a)
      rw [srwHeat_succ_eq_sum_dir, pow_succ]
      calc
        _ = (1 / (2 * (d : ℝ))) ^ n / (2 * d) := by ring
        _ ≤ srwHeat d n (x + dirVec a) / (2 * d) :=
          div_le_div_of_nonneg_right hterm (by positivity)
        _ ≤ _ := div_le_div_of_nonneg_right hsum (by positivity)

/-- Pairing adjacent times removes the parity restriction from the single-path bound. -/
theorem srwHeat_add_succ_ge_single_path (hd : 0 < d) {n : ℕ} (x : Site d)
    (hle : graphNorm x ≤ n) :
    (1 / (2 * (d : ℝ))) ^ (n + 1) ≤ srwHeat d n x + srwHeat d (n + 1) x := by
  have hbase : 1 / (2 * (d : ℝ)) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    linarith
  by_cases hp : graphNorm x % 2 = n % 2
  · calc
      _ ≤ (1 / (2 * (d : ℝ))) ^ n :=
        pow_le_pow_of_le_one (by positivity) hbase (by omega)
      _ ≤ srwHeat d n x := srwHeat_ge_single_path hd hle hp
      _ ≤ _ := le_add_of_nonneg_right (srwHeat_nonneg _ _)
  · have hp' : graphNorm x % 2 = (n + 1) % 2 := by omega
    exact (srwHeat_ge_single_path hd (by omega) hp').trans
      (le_add_of_nonneg_left (srwHeat_nonneg _ _))

/-- The normalized lattice inherits the parity-corrected single-path lower bound. -/
theorem weightedLattice_heat_add_succ_ge_single_path (hd : 0 < d)
    (x y : Site d) {n : ℕ} (hle : (weightedLattice d hd).graph.dist x y ≤ n) :
    ENNReal.ofReal ((1 / (2 * (d : ℝ))) ^ (n + 1)) ≤
      (weightedLattice d hd).heat n x y + (weightedLattice d hd).heat (n + 1) x y := by
  have hdist : graphNorm (y - x) ≤ n := by
    change (lattice d).dist x y ≤ n at hle
    rwa [lattice_dist_eq_graphNorm hd] at hle
  rw [weightedLattice_heat_eq, weightedLattice_heat_eq,
    ← ENNReal.ofReal_add (srwHeat_nonneg _ _) (srwHeat_nonneg _ _)]
  exact ENNReal.ofReal_le_ofReal (srwHeat_add_succ_ge_single_path hd _ hdist)

/-- On a Euclidean diffusive window, the paired kernel has a uniform polynomial lower bound
once the time exceeds a dimension-dependent threshold. -/
theorem exists_srwHeat_add_succ_lower_window (hd : 0 < d) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, 1 ≤ n → N ≤ n →
      ∀ x : Site d, euclidNorm x ^ 2 ≤ (n : ℝ) →
        c * (n : ℝ) ^ (-(d : ℝ) / 2) ≤
          srwHeat d n x + srwHeat d (n + 1) x := by
  obtain ⟨C, hC, hclt⟩ := LocalCLT.exists_abs_srwHeat_add_succ_sub_le (by omega : 1 ≤ d)
  let A : ℝ := (2 * Real.pi / d) ^ (-(d : ℝ) / 2) * Real.exp (-(d : ℝ) / 2)
  have hA : 0 < A := by dsimp [A]; positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (C / A)
  refine ⟨A, hA, N, fun n hn hNn x hx => ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlarge : C / A ≤ (n : ℝ) :=
    hN.le.trans (by exact_mod_cast hNn)
  have herror : C / (n : ℝ) ≤ A := by
    apply (div_le_iff₀ hnpos).mpr
    have := (div_le_iff₀ hA).mp hlarge
    linarith
  have hpow : (n : ℝ) ^ (-((d : ℝ) + 2) / 2) =
      (n : ℝ) ^ (-(d : ℝ) / 2) / n := by
    rw [show -((d : ℝ) + 2) / 2 = -(d : ℝ) / 2 - 1 by ring,
      Real.rpow_sub hnpos, Real.rpow_one]
  have herr : C * (n : ℝ) ^ (-((d : ℝ) + 2) / 2) ≤
      A * (n : ℝ) ^ (-(d : ℝ) / 2) := by
    rw [hpow]
    calc
      _ = (C / n) * (n : ℝ) ^ (-(d : ℝ) / 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right herror (Real.rpow_nonneg hnpos.le _)
  have hexponent : -(d * euclidNorm x ^ 2 / 2) / (n : ℝ) ≥ -(d : ℝ) / 2 := by
    apply (le_div_iff₀ hnpos).mpr
    have hdR : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    nlinarith [mul_le_mul_of_nonneg_left hx hdR]
  have hgauss : A * (n : ℝ) ^ (-(d : ℝ) / 2) ≤ ContinuousTime.ctGauss d n x := by
    rw [ContinuousTime.ctGauss_eq (by omega : 1 ≤ d) hnpos x]
    rw [show -((d : ℝ) / 2) = -(d : ℝ) / 2 by ring]
    dsimp only [A]
    rw [mul_assoc, mul_comm (Real.exp _) ((n : ℝ) ^ _)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent)
      (Real.rpow_nonneg hnpos.le _)
  have hb := (abs_le.mp (hclt n hn x)).1
  linarith

/-- The paired kernel has a dimension-dependent polynomial lower bound throughout the
unit diffusive window in graph distance, including the finitely many small times. -/
theorem exists_srwHeat_add_succ_lower_graph_window (hd : 0 < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → ∀ x : Site d,
      (graphNorm x : ℝ) ^ 2 ≤ (n : ℝ) →
        c * (n : ℝ) ^ (-(d : ℝ) / 2) ≤
          srwHeat d n x + srwHeat d (n + 1) x := by
  obtain ⟨A, hA, N, hwindow⟩ := exists_srwHeat_add_succ_lower_window hd
  let b : ℝ := 1 / (2 * (d : ℝ))
  have hb : 0 < b := by dsimp [b]; positivity
  have hb1 : b ≤ 1 := by
    dsimp [b]
    apply (div_le_one (by positivity)).mpr
    have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
    linarith
  refine ⟨min A (b ^ (N + 1)), lt_min hA (pow_pos hb _), fun n hn x hx => ?_⟩
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ (-(d : ℝ) / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hnR
      (by have hdR := Nat.cast_nonneg (α := ℝ) d; linarith)
  by_cases hN : N ≤ n
  · have heuc : euclidNorm x ^ 2 ≤ (n : ℝ) := by
      have habs : (graphNorm x : ℝ) = ∑ i : Fin d, |(x i : ℝ)| := by
        simp only [graphNorm, Nat.cast_sum, Nat.cast_natAbs, Int.cast_abs]
      have hsq := Finset.sum_sq_le_sq_sum_of_nonneg
        (s := (Finset.univ : Finset (Fin d)))
        (f := fun i => |(x i : ℝ)|) (fun i _ => abs_nonneg _)
      rw [euclidNorm, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
      rw [habs] at hx
      have hs : (∑ i : Fin d, (x i : ℝ) ^ 2) ≤
          (∑ i : Fin d, |(x i : ℝ)|) ^ 2 := by
        simpa only [sq_abs] using hsq
      exact hs.trans hx
    exact (mul_le_mul_of_nonneg_right (min_le_left _ _)
      (Real.rpow_nonneg (by positivity) _)).trans (hwindow n hn hN x heuc)
  · have hle : graphNorm x ≤ n := by
      have hL : (0 : ℝ) ≤ graphNorm x := Nat.cast_nonneg _
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
      have : (graphNorm x : ℝ) ≤ n := by
        by_cases hzero : graphNorm x = 0
        · simp only [hzero, Nat.cast_zero]; exact hn0
        · have hL1 : (1 : ℝ) ≤ graphNorm x := by
            exact_mod_cast (by omega : 1 ≤ graphNorm x)
          nlinarith
      exact_mod_cast this
    calc
      _ ≤ min A (b ^ (N + 1)) :=
        mul_le_of_le_one_right (le_of_lt (lt_min hA (pow_pos hb _))) hpow
      _ ≤ b ^ (N + 1) := min_le_right _ _
      _ ≤ b ^ (n + 1) := pow_le_pow_of_le_one hb.le hb1 (by omega)
      _ ≤ _ := srwHeat_add_succ_ge_single_path hd x hle

/-- The normalized lattice satisfies the Gaussian lower estimate on the unit diffusive
window in graph distance, in the volume normalization used by Murugan--Saloff-Coste. -/
theorem weightedLattice_gaussian_lower_near_diagonal (hd : 0 < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ x y (n : ℕ), 1 ≤ n →
      ((weightedLattice d hd).graph.dist x y : ℝ) ^ 2 ≤ (n : ℝ) →
      ENNReal.ofReal
        (c / latticeVolumeProfile d ((n : ℝ) ^ (1 / (2 : ℝ))) *
          Real.exp (-((((weightedLattice d hd).graph.dist x y : ℝ) ^ (2 : ℝ) /
            (c * n)) ^ (1 / ((2 : ℝ) - 1))))) ≤
        (weightedLattice d hd).heat n x y + (weightedLattice d hd).heat (n + 1) x y := by
  obtain ⟨c, hc, hlow⟩ := exists_srwHeat_add_succ_lower_graph_window hd
  refine ⟨c, hc, fun x y n hn hdist => ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hdist' : (graphNorm (y - x) : ℝ) ^ 2 ≤ (n : ℝ) := by
    change ((lattice d).dist x y : ℝ) ^ 2 ≤ (n : ℝ) at hdist
    rwa [lattice_dist_eq_graphNorm hd] at hdist
  let t : ℝ := (n : ℝ) ^ (1 / (2 : ℝ))
  have ht : 0 < t := Real.rpow_pos_of_pos hnpos _
  have hpow : (n : ℝ) ^ (-(d : ℝ) / 2) = (t ^ d)⁻¹ := by
    rw [show -(d : ℝ) / 2 = -((1 / (2 : ℝ)) * d) by ring,
      Real.rpow_neg hnpos.le, Real.rpow_mul hnpos.le, Real.rpow_natCast]
  have hpre : c / (1 + t) ^ d ≤ c * (n : ℝ) ^ (-(d : ℝ) / 2) := by
    rw [hpow, ← div_eq_mul_inv]
    exact div_le_div_of_nonneg_left hc.le (pow_pos ht d)
      (pow_le_pow_left₀ ht.le (by linarith) d)
  have hexp : Real.exp (-((((weightedLattice d hd).graph.dist x y : ℝ) ^ (2 : ℝ) /
      (c * n)) ^ (1 / ((2 : ℝ) - 1)))) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact neg_nonpos.mpr (Real.rpow_nonneg (by positivity) _)
  rw [weightedLattice_heat_eq, weightedLattice_heat_eq,
    ← ENNReal.ofReal_add (srwHeat_nonneg _ _) (srwHeat_nonneg _ _)]
  apply ENNReal.ofReal_le_ofReal
  change c / (1 + t) ^ d * _ ≤ _
  exact (mul_le_of_le_one_right (by positivity) hexp).trans
    (hpre.trans (hlow n hn (y - x) hdist'))

/-- Restricting Chapman--Kolmogorov to any finite set gives a lower bound. -/
theorem sum_srwHeat_mul_le (a b : ℕ) (x : Site d) (s : Finset (Site d)) :
    ∑ y ∈ s, srwHeat d a y * srwHeat d b (x - y) ≤ srwHeat d (a + b) x := by
  rw [srwHeat_add]
  exact (summable_srwHeat_mul a _).sum_le_tsum s
    (fun y _ => mul_nonneg (srwHeat_nonneg _ _) (srwHeat_nonneg _ _))

/-- Outside a fixed linear fraction of the reachable ball, one path already gives
Gaussian decay. The constant is explicit and depends only on dimension and that fraction. -/
theorem srwHeat_add_succ_ge_gaussian_outer (hd : 0 < d) {A : ℝ} (hA : 0 < A)
    {n : ℕ} (hn : 1 ≤ n) (x : Site d) (hle : graphNorm x ≤ n)
    (houter : (n : ℝ) ≤ A * graphNorm x) :
    Real.exp (-(2 * Real.log (2 * (d : ℝ)) * A ^ 2 *
      (graphNorm x : ℝ) ^ 2 / n)) ≤ srwHeat d n x + srwHeat d (n + 1) x := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hnR
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hlog : 0 ≤ Real.log (2 * (d : ℝ)) := Real.log_nonneg (by linarith)
  have hsquare : (n : ℝ) ^ 2 ≤ A ^ 2 * (graphNorm x : ℝ) ^ 2 := by
    have hsq := (sq_le_sq₀ hnpos.le
      (mul_nonneg hA.le (Nat.cast_nonneg (graphNorm x)))).mpr houter
    simpa only [mul_pow] using hsq
  have htime : (n : ℝ) + 1 ≤ 2 * A ^ 2 * (graphNorm x : ℝ) ^ 2 / n := by
    apply (le_div_iff₀ hnpos).mpr
    nlinarith
  have hexponent : -(2 * Real.log (2 * (d : ℝ)) * A ^ 2 *
      (graphNorm x : ℝ) ^ 2 / n) ≤
      ((n : ℝ) + 1) * -Real.log (2 * (d : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_left htime hlog
    calc
      _ = -(Real.log (2 * (d : ℝ)) *
          (2 * A ^ 2 * (graphNorm x : ℝ) ^ 2 / n)) := by ring
      _ ≤ -(Real.log (2 * (d : ℝ)) * ((n : ℝ) + 1)) := neg_le_neg hmul
      _ = _ := by ring
  calc
    _ ≤ Real.exp (((n : ℝ) + 1) * -Real.log (2 * (d : ℝ))) :=
      Real.exp_le_exp.mpr hexponent
    _ = (1 / (2 * (d : ℝ))) ^ (n + 1) := by
      rw [← Nat.cast_add_one, Real.exp_nat_mul, Real.exp_neg,
        Real.exp_log (by positivity), one_div]
    _ ≤ _ := srwHeat_add_succ_ge_single_path hd x hle

/-- At sites of the correct parity, the paired near-diagonal estimate is an estimate
for the single-time kernel. This is the form used for fixed-time convolution chains. -/
theorem exists_srwHeat_lower_graph_window (hd : 0 < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, 1 ≤ n → ∀ x : Site d,
      (graphNorm x : ℝ) ^ 2 ≤ (n : ℝ) → graphNorm x % 2 = n % 2 →
        c * (n : ℝ) ^ (-(d : ℝ) / 2) ≤ srwHeat d n x := by
  obtain ⟨c, hc, hlow⟩ := exists_srwHeat_add_succ_lower_graph_window hd
  refine ⟨c, hc, fun n hn x hx hp => ?_⟩
  have hzero : srwHeat d (n + 1) x = 0 := by
    apply srwHeat_eq_zero_of_parity
    intro heq
    have hmod := (ZMod.natCast_eq_natCast_iff' (graphNorm x) (n + 1) 2).mp heq
    omega
  simpa only [hzero, add_zero] using hlow n hn x hx

/-- The normalized lattice has the MSC Gaussian lower bound in the outer linear region.
The constant depends only on dimension and the fixed ratio between time and distance. -/
theorem weightedLattice_gaussian_lower_outer (hd : 0 < d) {A : ℝ} (hA : 0 < A) :
    ∃ c : ℝ, 0 < c ∧ ∀ x y (n : ℕ), 1 ≤ n →
      (weightedLattice d hd).graph.dist x y ≤ n →
      (n : ℝ) ≤ A * (weightedLattice d hd).graph.dist x y →
      ENNReal.ofReal
        (c / latticeVolumeProfile d ((n : ℝ) ^ (1 / (2 : ℝ))) *
          Real.exp (-((((weightedLattice d hd).graph.dist x y : ℝ) ^ (2 : ℝ) /
            (c * n)) ^ (1 / ((2 : ℝ) - 1))))) ≤
        (weightedLattice d hd).heat n x y + (weightedLattice d hd).heat (n + 1) x y := by
  let C : ℝ := 2 * Real.log (2 * (d : ℝ)) * A ^ 2
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hC : 0 ≤ C := mul_nonneg
    (mul_nonneg (by norm_num) (Real.log_nonneg (by linarith))) (sq_nonneg A)
  let c : ℝ := 1 / (1 + C)
  have hc : 0 < c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := by
    dsimp [c]
    exact (div_le_one (by positivity)).mpr (by linarith)
  have hcC : c * C ≤ 1 := by
    dsimp [c]
    rw [one_div_mul_eq_div]
    exact (div_le_one (by positivity)).mpr (by linarith)
  refine ⟨c, hc, fun x y n hn hle houter => ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hdist : (weightedLattice d hd).graph.dist x y = graphNorm (y - x) :=
    lattice_dist_eq_graphNorm hd x y
  rw [hdist] at hle houter ⊢
  have hratio : C * (graphNorm (y - x) : ℝ) ^ 2 / n ≤
      (graphNorm (y - x) : ℝ) ^ 2 / (c * n) := by
    apply (le_div_iff₀ (mul_pos hc hnpos)).mpr
    have hh := mul_le_mul_of_nonneg_right hcC
      (sq_nonneg (graphNorm (y - x) : ℝ))
    calc
      _ = (c * C) * (graphNorm (y - x) : ℝ) ^ 2 := by field_simp [ne_of_gt hnpos]
      _ ≤ _ := by simpa only [one_mul] using hh
  have hvol : 1 ≤ latticeVolumeProfile d ((n : ℝ) ^ (1 / (2 : ℝ))) := by
    change 1 ≤ (1 + (n : ℝ) ^ (1 / (2 : ℝ))) ^ d
    apply one_le_pow₀
    have := Real.rpow_nonneg (Nat.cast_nonneg n) (1 / (2 : ℝ))
    linarith
  have hpre : c / latticeVolumeProfile d ((n : ℝ) ^ (1 / (2 : ℝ))) ≤ 1 :=
    (div_le_self hc.le hvol).trans hc1
  rw [weightedLattice_heat_eq, weightedLattice_heat_eq,
    ← ENNReal.ofReal_add (srwHeat_nonneg _ _) (srwHeat_nonneg _ _)]
  apply ENNReal.ofReal_le_ofReal
  simp only [show (1 : ℝ) / (2 - 1) = 1 by norm_num, Real.rpow_one,
    Real.rpow_two]
  calc
    _ ≤ Real.exp (-((graphNorm (y - x) : ℝ) ^ 2 / (c * n))) :=
      mul_le_of_le_one_left (Real.exp_nonneg _) hpre
    _ ≤ Real.exp (-(C * (graphNorm (y - x) : ℝ) ^ 2 / n)) :=
      Real.exp_le_exp.mpr (neg_le_neg hratio)
    _ ≤ _ := srwHeat_add_succ_ge_gaussian_outer hd hA hn (y - x) hle houter

/-- Iterated finite convolution propagates a pointwise lower bound along prescribed
finite sets. Each factor records the preceding set's cardinality and one edge bound. -/
theorem srwHeat_lower_finite_chain (s : ℕ → ℕ) (S : ℕ → Finset (Site d))
    (q : ℕ → ℝ) (hzero : S 0 = {0}) (hq : ∀ j, 0 ≤ q j)
    (hedge : ∀ j, ∀ y ∈ S j, ∀ z ∈ S (j + 1),
      q j ≤ srwHeat d (s j) (z - y)) (N : ℕ) :
    ∀ x ∈ S N,
      (∏ j ∈ Finset.range N, ((S j).card : ℝ) * q j) ≤
        srwHeat d (∑ j ∈ Finset.range N, s j) x := by
  classical
  induction N with
  | zero =>
      intro x hx
      have hx0 : x = 0 := by simpa only [hzero, Finset.mem_singleton] using hx
      simp only [Finset.range_zero, Finset.prod_empty, Finset.sum_empty, hx0,
        srwHeat_zero, ite_true, le_refl]
  | succ N ih =>
      intro x hx
      rw [Finset.prod_range_succ, Finset.sum_range_succ]
      calc
        _ = ∑ y ∈ S N,
            (∏ j ∈ Finset.range N, ((S j).card : ℝ) * q j) * q N := by
          rw [Finset.sum_const, nsmul_eq_mul]
          ring
        _ ≤ ∑ y ∈ S N,
            srwHeat d (∑ j ∈ Finset.range N, s j) y *
              srwHeat d (s N) (x - y) := by
          apply Finset.sum_le_sum
          intro y hy
          exact mul_le_mul (ih y hy) (hedge N y hy x hx) (hq N)
            (srwHeat_nonneg _ _)
        _ ≤ _ := sum_srwHeat_mul_le _ _ x (S N)

/-- The single-time diffusive estimate propagates along any finite chain whose every
edge lies in the correct parity window. This retains all intermediate cardinalities. -/
theorem exists_srwHeat_lower_window_chain (hd : 0 < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (s : ℕ → ℕ) (S : ℕ → Finset (Site d)),
      S 0 = {0} → (∀ j, 1 ≤ s j) →
      (∀ j, ∀ y ∈ S j, ∀ z ∈ S (j + 1),
        (graphNorm (z - y) : ℝ) ^ 2 ≤ s j ∧
          graphNorm (z - y) % 2 = s j % 2) →
      ∀ N x, x ∈ S N →
        (∏ j ∈ Finset.range N,
          ((S j).card : ℝ) * (c * (s j : ℝ) ^ (-(d : ℝ) / 2))) ≤
            srwHeat d (∑ j ∈ Finset.range N, s j) x := by
  obtain ⟨c, hc, hwindow⟩ := exists_srwHeat_lower_graph_window hd
  refine ⟨c, hc, fun s S hzero hs hedge N x hx => ?_⟩
  apply srwHeat_lower_finite_chain s S
    (fun j => c * (s j : ℝ) ^ (-(d : ℝ) / 2)) hzero
    (fun j => mul_nonneg hc.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)) ?_ N x hx
  intro j y hy z hz
  exact hwindow (s j) (hs j) (z - y) (hedge j y hy z hz).1
    (hedge j y hy z hz).2

/-- The floor partition of a fixed time has no increment below the quotient. -/
theorem floor_time_increment_ge (m N j : ℕ) :
    m / N ≤ (j + 1) * m / N - j * m / N := by
  have h := Nat.div_add_div_le_add_div (x := j * m) (y := m) (z := N)
  rw [show (j + 1) * m = j * m + m by ring]
  omega

/-- The floor partition has no increment more than one above the quotient. -/
theorem floor_time_increment_le (m j : ℕ) {N : ℕ} (hN : 0 < N) :
    (j + 1) * m / N - j * m / N ≤ m / N + 1 := by
  rw [show (j + 1) * m = j * m + m by ring, Nat.add_div hN]
  rw [Nat.add_assoc, Nat.add_sub_cancel_left]
  apply Nat.add_le_add_left
  split_ifs <;> decide

/-- The floor time increments telescope to the prescribed total time exactly. -/
theorem sum_floor_time_increments (m : ℕ) {N : ℕ} (hN : 0 < N) :
    (∑ j ∈ Finset.range N, ((j + 1) * m / N - j * m / N)) = m := by
  have hprefix : ∀ k : ℕ,
      (∑ j ∈ Finset.range k, ((j + 1) * m / N - j * m / N)) = k * m / N := by
    intro k
    induction k with
    | zero => simp only [Finset.range_zero, Finset.sum_empty, zero_mul, Nat.zero_div]
    | succ k ih =>
        rw [Finset.sum_range_succ, ih]
        have hmono := Nat.div_add_div_le_add_div (x := k * m) (y := m) (z := N)
        rw [show (k + 1) * m = k * m + m by ring]
        have hle : k * m / N ≤ (k * m + m) / N :=
          (Nat.le_add_right _ _).trans hmono
        simpa only [Nat.add_comm] using Nat.sub_add_cancel hle
  rw [hprefix N, Nat.mul_div_cancel_left m hN]

/-- Every prefix of the floor-time increments has exactly its prescribed elapsed time. -/
theorem sum_floor_time_increments_prefix (m N j : ℕ) :
    (∑ i ∈ Finset.range j, ((i + 1) * m / N - i * m / N)) = j * m / N := by
  have hmono : Monotone (fun i : ℕ => i * m / N) := by
    intro a b hab
    exact Nat.div_le_div_right (Nat.mul_le_mul_right m hab)
  simpa only [zero_mul, Nat.zero_div, Nat.sub_zero] using Finset.sum_range_tsub hmono j

/-- Coordinatewise integer floors of the straight segment from zero to `k`. -/
def chainCenter (k : Site d) (N j : ℕ) : Site d :=
  fun i => ⌊(j : ℝ) * (k i : ℝ) / N⌋

/-- The straight-segment floor centers start at the origin. -/
theorem chainCenter_zero (k : Site d) (N : ℕ) : chainCenter k N 0 = 0 := by
  ext i
  simp only [chainCenter, Nat.cast_zero, zero_mul, zero_div, Int.floor_zero, Pi.zero_apply]

/-- For a positive number of links the last floor center is exactly the target site. -/
theorem chainCenter_end (k : Site d) {N : ℕ} (hN : 0 < N) :
    chainCenter k N N = k := by
  ext i
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  simp only [chainCenter, mul_div_cancel_left₀ (k i : ℝ) hNR, Int.floor_intCast]

/-- Rounding two real coordinates down increases their distance by at most one. -/
theorem abs_floor_sub_floor_le (a b : ℝ) :
    |((⌊a⌋ - ⌊b⌋ : ℤ) : ℝ)| ≤ |a - b| + 1 := by
  rw [Int.cast_sub, abs_le]
  have ha := Int.floor_le a
  have hb := Int.floor_le b
  have ha' := Int.lt_floor_add_one a
  have hb' := Int.lt_floor_add_one b
  constructor <;> linarith [le_abs_self (a - b), neg_abs_le (a - b)]

/-- Every successive floor-center displacement has graph length at most `L/N + d`. -/
theorem graphNorm_chainCenter_step_le (k : Site d) {N : ℕ} (hN : 0 < N)
    (j : ℕ) :
    (graphNorm (chainCenter k N (j + 1) - chainCenter k N j) : ℝ) ≤
      (graphNorm k : ℝ) / N + d := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hcoord : ∀ i : Fin d,
      |((chainCenter k N (j + 1) i - chainCenter k N j i : ℤ) : ℝ)| ≤
        |(k i : ℝ)| / N + 1 := by
    intro i
    have h := abs_floor_sub_floor_le
      ((j + 1 : ℕ) * (k i : ℝ) / N) ((j : ℝ) * (k i : ℝ) / N)
    have heq : ((j + 1 : ℕ) : ℝ) * (k i : ℝ) / N -
        (j : ℝ) * (k i : ℝ) / N = (k i : ℝ) / N := by
      push_cast
      ring
    rw [heq, abs_div, abs_of_pos hNR] at h
    exact h
  calc
    _ = ∑ i : Fin d,
        |((chainCenter k N (j + 1) i - chainCenter k N j i : ℤ) : ℝ)| := by
      simp only [graphNorm, Nat.cast_sum, Nat.cast_natAbs, Int.cast_abs, Pi.sub_apply]
    _ ≤ ∑ i : Fin d, (|(k i : ℝ)| / N + 1) :=
      Finset.sum_le_sum (fun i _ => hcoord i)
    _ = (graphNorm k : ℝ) / N + d := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
        graphNorm, Nat.cast_sum, Nat.cast_natAbs, Int.cast_abs]

/-- A translate of the even sublattice box, with its prescribed coordinate radius. -/
def chainBox (z : Site d) (ρ : ℕ) : Finset (Site d) :=
  (originBox d ρ).image (fun w => z + 2 • w)

/-- Scaling integer sites by two and translating is injective. -/
theorem chainBox_map_injective (z : Site d) :
    Function.Injective (fun w : Site d => z + 2 • w) := by
  intro w v h
  ext i
  have hi := congrFun h i
  simp only [two_nsmul, Pi.add_apply] at hi
  omega

/-- The parity box has exactly the number of sites in its unscaled coordinate box. -/
theorem card_chainBox (z : Site d) (ρ : ℕ) :
    (chainBox z ρ).card = (2 * ρ + 1) ^ d := by
  classical
  rw [chainBox, Finset.card_image_of_injective _ (chainBox_map_injective z)]
  exact card_originBox ρ

/-- Membership in a parity box bounds each coordinate's displacement from its center. -/
theorem abs_sub_le_of_mem_chainBox {z y : Site d} {ρ : ℕ}
    (hy : y ∈ chainBox z ρ) (i : Fin d) :
    |y i - z i| ≤ 2 * (ρ : ℤ) := by
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
  have hi := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hw i)
  simp only [two_nsmul, Pi.add_apply]
  rw [abs_le]
  constructor <;> omega

/-- Every parity-box point has the same coordinate-sum residue as its center. -/
theorem sum_mod_two_of_mem_chainBox {z y : Site d} {ρ : ℕ}
    (hy : y ∈ chainBox z ρ) :
    (∑ i, y i) % 2 = (∑ i, z i) % 2 := by
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
  simp only [two_nsmul, Pi.add_apply, Finset.sum_add_distrib]
  omega

/-- A parity-box point is at graph distance at most twice dimension times radius. -/
theorem graphNorm_sub_le_of_mem_chainBox {z y : Site d} {ρ : ℕ}
    (hy : y ∈ chainBox z ρ) : graphNorm (y - z) ≤ 2 * d * ρ := by
  have hcoord : ∀ i : Fin d, (y i - z i).natAbs ≤ 2 * ρ := by
    intro i
    have hi := abs_sub_le_of_mem_chainBox hy i
    rw [← Int.natCast_natAbs] at hi
    exact_mod_cast hi
  calc
    _ ≤ ∑ _i : Fin d, 2 * ρ := Finset.sum_le_sum (fun i _ => hcoord i)
    _ = 2 * d * ρ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
      ring

/-- One unit in the first coordinate corrects a coordinate-sum residue when necessary. -/
def chainParityOffset (hd : 0 < d) (z : Site d) (p : ℕ) : Site d :=
  if (∑ i, z i) % 2 = (p % 2 : ℕ) then 0 else Pi.single ⟨0, hd⟩ 1

/-- The parity correction puts its center in the required coordinate-sum class. -/
theorem sum_chainParityOffset_mod_two (hd : 0 < d) (z : Site d) (p : ℕ) :
    (∑ i, (z + chainParityOffset hd z p) i) % 2 = (p % 2 : ℕ) := by
  classical
  simp only [chainParityOffset]
  split_ifs with h
  · simpa only [add_zero] using h
  · simp only [Pi.add_apply, Finset.sum_add_distrib, Pi.single_apply,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have hp : p % 2 < 2 := Nat.mod_lt p (by decide)
    have hz := Int.emod_nonneg (∑ i, z i) (by decide : (2 : ℤ) ≠ 0)
    have hz' := Int.emod_lt_of_pos (∑ i, z i) (by decide : (0 : ℤ) < 2)
    omega

/-- The parity offset has graph norm at most one. -/
theorem graphNorm_chainParityOffset_le (hd : 0 < d) (z : Site d) (p : ℕ) :
    graphNorm (chainParityOffset hd z p) ≤ 1 := by
  classical
  simp only [chainParityOffset]
  split_ifs
  · simp only [graphNorm_zero, zero_le]
  · simp only [graphNorm, Pi.single_apply, apply_ite Int.natAbs,
      Int.natAbs_one, Int.natAbs_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
      le_refl]

/-- Two points from consecutive parity boxes satisfy the center-distance bound. -/
theorem graphNorm_sub_le_of_mem_chainBoxes {z z' y y' : Site d} {ρ : ℕ}
    (hy : y ∈ chainBox z ρ) (hy' : y' ∈ chainBox z' ρ) :
    graphNorm (y' - y) ≤ graphNorm (z' - z) + 4 * d * ρ := by
  have hdecomp : y' - y = (y' - z') + (z' - z) + -(y - z) := by abel
  rw [hdecomp]
  have htri := (graphNorm_add_le ((y' - z') + (z' - z)) (-(y - z))).trans
    (Nat.add_le_add_right (graphNorm_add_le (y' - z') (z' - z)) _)
  rw [graphNorm_neg] at htri
  have hleft := graphNorm_sub_le_of_mem_chainBox hy'
  have hright := graphNorm_sub_le_of_mem_chainBox hy
  have hfour : 4 * d * ρ = 2 * d * ρ + 2 * d * ρ := by ring
  rw [hfour]
  omega

/-- The prescribed square-root radius of each parity box. -/
def chainRadius (d s : ℕ) : ℕ := ⌊Real.sqrt s / (16 * d)⌋₊

/-- Rounding the box radius down preserves the required upper bound on edge errors. -/
theorem chainRadius_le_sqrt (hd : 0 < d) (s : ℕ) :
    4 * (d : ℝ) * chainRadius d s ≤ Real.sqrt s / 4 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have h := Nat.floor_le (div_nonneg (Real.sqrt_nonneg (s : ℝ))
    (by positivity : (0 : ℝ) ≤ 16 * d))
  change (chainRadius d s : ℝ) ≤ Real.sqrt s / (16 * d) at h
  have hm := (le_div_iff₀ (by positivity : (0 : ℝ) < 16 * d)).mp h
  linarith

/-- The fixed time threshold absorbs the center-rounding and parity-offset errors. -/
theorem graphNorm_chain_step_error_le (hd : 0 < d) {s : ℕ}
    (hs : 256 * (d + 2) ^ 2 ≤ s) {r : ℝ}
    (hr : r ≤ Real.sqrt s / 4) :
    r + d + 2 + 4 * (d : ℝ) * chainRadius d s ≤ (3 / 4 : ℝ) * Real.sqrt s := by
  have hsR : 256 * ((d : ℝ) + 2) ^ 2 ≤ (s : ℝ) := by exact_mod_cast hs
  have hsqrt : 16 * ((d : ℝ) + 2) ≤ Real.sqrt s := by
    apply (Real.le_sqrt (by positivity) (Nat.cast_nonneg s)).mpr
    nlinarith
  have hρ := chainRadius_le_sqrt hd s
  linarith

/-- The integer coordinate sum and graph norm have exactly the same residue modulo two. -/
theorem graphNorm_int_mod_two (x : Site d) :
    (graphNorm x : ℤ) % 2 = (∑ i, x i) % 2 := by
  apply (ZMod.intCast_eq_intCast_iff' _ _ 2).mp
  simpa only [Int.cast_natCast] using graphNorm_cast_zmod x

/-- The chain uses singleton endpoints and the prescribed parity boxes in its interior. -/
def chainSets (hd : 0 < d) (k : Site d) (m N ρ j : ℕ) : Finset (Site d) :=
  if j = 0 then {0} else if j = N then {k}
  else chainBox (chainCenter k N j +
    chainParityOffset hd (chainCenter k N j) (j * m / N)) ρ

/-- The initial chaining set is the singleton origin. -/
theorem chainSets_zero (hd : 0 < d) (k : Site d) (m N ρ : ℕ) :
    chainSets hd k m N ρ 0 = {0} := by
  simp only [chainSets, ↓reduceIte]

/-- The terminal chaining set is exactly the singleton target. -/
theorem chainSets_end (hd : 0 < d) (k : Site d) (m ρ : ℕ) {N : ℕ}
    (hN : 0 < N) : chainSets hd k m N ρ N = {k} := by
  simp only [chainSets, if_neg (Nat.ne_of_gt hN), ↓reduceIte]

/-- Every interior chaining set has the exact parity-box cardinality. -/
theorem card_chainSets (hd : 0 < d) (k : Site d) (m N ρ : ℕ) {j : ℕ}
    (hj : 0 < j) (hjN : j < N) :
    (chainSets hd k m N ρ j).card = (2 * ρ + 1) ^ d := by
  rw [chainSets, if_neg (by omega), if_neg (by omega)]
  exact card_chainBox _ _

/-- Every point of a chaining set has the prescribed elapsed-time parity. -/
theorem sum_mod_two_of_mem_chainSets (hd : 0 < d) (k : Site d) (m ρ : ℕ)
    {N : ℕ} (hN : 0 < N) (hp : graphNorm k % 2 = m % 2) {j : ℕ} {y : Site d}
    (hy : y ∈ chainSets hd k m N ρ j) :
    (∑ i, y i) % 2 = (j * m / N % 2 : ℕ) := by
  classical
  unfold chainSets at hy
  split_ifs at hy with hj hjN
  · subst j
    have hy0 : y = 0 := Finset.mem_singleton.mp hy
    simp only [hy0, Pi.zero_apply, Finset.sum_const_zero, Int.zero_emod,
      zero_mul, Nat.zero_div, Nat.zero_mod, Nat.cast_zero]
  · subst j
    have hyk : y = k := Finset.mem_singleton.mp hy
    rw [hyk, Nat.mul_div_cancel_left m hN, ← graphNorm_int_mod_two]
    exact_mod_cast hp
  · exact (sum_mod_two_of_mem_chainBox hy).trans
      (sum_chainParityOffset_mod_two hd _ _)

/-- The center of a parity box always belongs to that box. -/
theorem mem_chainBox_self (z : Site d) (ρ : ℕ) : z ∈ chainBox z ρ := by
  classical
  apply Finset.mem_image.mpr
  refine ⟨0, ?_, by simp only [smul_zero, add_zero]⟩
  apply Fintype.mem_piFinset.mpr
  intro i
  simp only [Pi.zero_apply, Finset.mem_Icc]
  constructor <;> omega

/-- The endpoints also lie in the corresponding corrected-center boxes. -/
theorem mem_chainBox_of_mem_chainSets (hd : 0 < d) (k : Site d) (m ρ : ℕ)
    {N : ℕ} (hN : 0 < N) (hp : graphNorm k % 2 = m % 2) {j : ℕ} {y : Site d}
    (hy : y ∈ chainSets hd k m N ρ j) :
    y ∈ chainBox (chainCenter k N j +
      chainParityOffset hd (chainCenter k N j) (j * m / N)) ρ := by
  classical
  unfold chainSets at hy
  split_ifs at hy with hj hjN
  · subst j
    have hy0 : y = 0 := Finset.mem_singleton.mp hy
    rw [hy0, chainCenter_zero]
    have hzero : chainParityOffset hd (0 : Site d) (0 * m / N) = 0 := by
      simp only [chainParityOffset, Pi.zero_apply, Finset.sum_const_zero, Int.zero_emod,
        zero_mul, Nat.zero_div, Nat.zero_mod, Nat.cast_zero, ↓reduceIte]
    rw [hzero, add_zero]
    exact mem_chainBox_self 0 ρ
  · subst j
    have hyk : y = k := Finset.mem_singleton.mp hy
    rw [hyk, chainCenter_end k hN, Nat.mul_div_cancel_left m hN]
    have hpar : (∑ i, k i) % 2 = (m % 2 : ℕ) := by
      rw [← graphNorm_int_mod_two]
      exact_mod_cast hp
    rw [chainParityOffset, if_pos hpar, add_zero]
    exact mem_chainBox_self k ρ
  · exact hy

/-- Coordinate-sum parity at two times gives the correct parity for their displacement. -/
theorem graphNorm_sub_mod_two_of_sum_mod_two (y y' : Site d) {p q : ℕ}
    (hpq : p ≤ q) (hp : (∑ i, y i) % 2 = (p % 2 : ℕ))
    (hq : (∑ i, y' i) % 2 = (q % 2 : ℕ)) :
    graphNorm (y' - y) % 2 = (q - p) % 2 := by
  have hg := graphNorm_int_mod_two (y' - y)
  simp only [Pi.sub_apply, Finset.sum_sub_distrib] at hg
  have hp' : (∑ i, y i) % 2 = (p : ℤ) % 2 := by exact_mod_cast hp
  have hq' : (∑ i, y' i) % 2 = (q : ℤ) % 2 := by exact_mod_cast hq
  have hsub : ((q - p : ℕ) : ℤ) = (q : ℤ) - p := Int.ofNat_sub hpq
  have heq : (graphNorm (y' - y) : ℤ) % 2 = ((q - p : ℕ) : ℤ) % 2 := by
    rw [hsub]
    omega
  exact_mod_cast heq

/-- Consecutive chaining sets have exactly the parity of their floor time increment. -/
theorem graphNorm_chainSets_step_mod_two (hd : 0 < d) (k : Site d) (m ρ : ℕ)
    {N : ℕ} (hN : 0 < N) (hp : graphNorm k % 2 = m % 2)
    (j : ℕ) {y y' : Site d} (hy : y ∈ chainSets hd k m N ρ j)
    (hy' : y' ∈ chainSets hd k m N ρ (j + 1)) :
    graphNorm (y' - y) % 2 = ((j + 1) * m / N - j * m / N) % 2 := by
  apply graphNorm_sub_mod_two_of_sum_mod_two y y'
    (Nat.div_le_div_right (Nat.mul_le_mul_right m (Nat.le_succ j)))
  · exact sum_mod_two_of_mem_chainSets hd k m ρ hN hp hy
  · exact sum_mod_two_of_mem_chainSets hd k m ρ hN hp hy'

/-- The unit parity offsets add at most two to the distance between floor centers. -/
theorem graphNorm_corrected_chainCenter_step_le (hd : 0 < d) (k : Site d)
    (m : ℕ) {N : ℕ} (hN : 0 < N) (j : ℕ) :
    (graphNorm ((chainCenter k N (j + 1) +
        chainParityOffset hd (chainCenter k N (j + 1)) ((j + 1) * m / N)) -
      (chainCenter k N j + chainParityOffset hd (chainCenter k N j) (j * m / N))) : ℝ)
      ≤ (graphNorm k : ℝ) / N + d + 2 := by
  let a := chainCenter k N (j + 1)
  let b := chainCenter k N j
  let e := chainParityOffset hd a ((j + 1) * m / N)
  let f := chainParityOffset hd b (j * m / N)
  have he := graphNorm_chainParityOffset_le hd a ((j + 1) * m / N)
  have hf := graphNorm_chainParityOffset_le hd b (j * m / N)
  change graphNorm e ≤ 1 at he
  change graphNorm f ≤ 1 at hf
  have htri : graphNorm ((a + e) - (b + f)) ≤ graphNorm (a - b) + 2 := by
    rw [show (a + e) - (b + f) = (a - b) + e + -f by abel]
    have h := (graphNorm_add_le ((a - b) + e) (-f)).trans
      (Nat.add_le_add_right (graphNorm_add_le (a - b) e) _)
    rw [graphNorm_neg] at h
    omega
  have htriR : (graphNorm ((a + e) - (b + f)) : ℝ) ≤
      (graphNorm (a - b) : ℝ) + 2 := by exact_mod_cast htri
  exact htriR.trans (by
    have hcenter := graphNorm_chainCenter_step_le k hN j
    dsimp only [a, b] at *
    linarith)

/-- Every edge between consecutive chaining sets obeys the explicit box-distance bound. -/
theorem graphNorm_chainSets_step_le (hd : 0 < d) (k : Site d) (m ρ : ℕ)
    {N : ℕ} (hN : 0 < N) (hp : graphNorm k % 2 = m % 2)
    (j : ℕ) {y y' : Site d} (hy : y ∈ chainSets hd k m N ρ j)
    (hy' : y' ∈ chainSets hd k m N ρ (j + 1)) :
    (graphNorm (y' - y) : ℝ) ≤ (graphNorm k : ℝ) / N + d + 2 + 4 * d * ρ := by
  have hbox := graphNorm_sub_le_of_mem_chainBoxes
    (mem_chainBox_of_mem_chainSets hd k m ρ hN hp hy)
    (mem_chainBox_of_mem_chainSets hd k m ρ hN hp hy')
  have hboxR : (graphNorm (y' - y) : ℝ) ≤
      (graphNorm ((chainCenter k N (j + 1) +
        chainParityOffset hd (chainCenter k N (j + 1)) ((j + 1) * m / N)) -
        (chainCenter k N j +
          chainParityOffset hd (chainCenter k N j) (j * m / N))) : ℝ) +
            4 * d * ρ := by exact_mod_cast hbox
  have hcenter := graphNorm_corrected_chainCenter_step_le hd k m hN j
  linarith

/-- The prescribed number of links for the intermediate Gaussian regime. -/
def chainLength (L : ℕ) (m : ℕ) : ℕ := ⌈64 * (L : ℝ) ^ 2 / m⌉₊

/-- When time is at most squared distance, the link count is at least sixty-four. -/
theorem chainLength_ge {L m : ℕ} (hm : 0 < m) (hLm : (m : ℝ) ≤ (L : ℝ) ^ 2) :
    64 ≤ chainLength L m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h := Nat.le_ceil (64 * (L : ℝ) ^ 2 / m)
  have hratio : (64 : ℝ) ≤ 64 * (L : ℝ) ^ 2 / m := by
    apply (le_div_iff₀ hmR).mpr
    linarith
  exact (Nat.cast_le (α := ℝ)).mp (hratio.trans h)

/-- Rounding the link count up costs at most a factor two in the intermediate regime. -/
theorem chainLength_le {L m : ℕ} (hm : 0 < m) (hLm : (m : ℝ) ≤ (L : ℝ) ^ 2) :
    (chainLength L m : ℝ) ≤ 128 * (L : ℝ) ^ 2 / m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hratio : (1 : ℝ) ≤ 64 * (L : ℝ) ^ 2 / m := by
    apply (le_div_iff₀ hmR).mpr
    nlinarith [sq_nonneg (L : ℝ)]
  have h := Nat.ceil_lt_add_one
    (div_nonneg (by positivity : (0 : ℝ) ≤ 64 * (L : ℝ) ^ 2) hmR.le)
  change (chainLength L m : ℝ) < 64 * (L : ℝ) ^ 2 / m + 1 at h
  have heq : 128 * (L : ℝ) ^ 2 / m = 2 * (64 * (L : ℝ) ^ 2 / m) := by ring
  rw [heq]
  linarith

/-- An algebraic bound turns the linear-region assumption into a minimum time per link. -/
theorem chain_time_scale_algebra {D L m N : ℝ} (hD : 0 ≤ D) (hm : 0 < m)
    (hL : 0 ≤ L) (hlinear : 256 * D * L ≤ m) (hN : N * m ≤ 128 * L ^ 2) :
    512 * D ^ 2 * N ≤ m := by
  have hsquare : (256 * D * L) ^ 2 ≤ m ^ 2 :=
    (sq_le_sq₀ (by positivity) hm.le).mpr hlinear
  have hmul := mul_le_mul_of_nonneg_left hN (sq_nonneg D)
  have hcancel : (512 * D ^ 2 * N) * m ≤ m * m := by
    nlinarith only [hsquare, hmul]
  exact (mul_le_mul_iff_left₀ hm).mp (by simpa only [mul_comm m] using hcancel)

/-- The fixed linear-region cutoff makes the floor time at least the required threshold. -/
theorem chain_floor_time_ge (_hd : 0 < d) {L m : ℕ} (hm : 0 < m)
    (hLm : (m : ℝ) ≤ (L : ℝ) ^ 2)
    (hlinear : (L : ℝ) ≤ (m : ℝ) / (256 * (d + 2))) :
    256 * (d + 2) ^ 2 ≤ m / chainLength L m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hlinear' : 256 * ((d : ℝ) + 2) * L ≤ (m : ℝ) := by
    have h := (le_div_iff₀ (by positivity : (0 : ℝ) < 256 * (d + 2))).mp hlinear
    linarith
  have hN := (le_div_iff₀ hmR).mp (chainLength_le hm hLm)
  have hscale := chain_time_scale_algebra (by positivity : (0 : ℝ) ≤ d + 2)
    hmR (Nat.cast_nonneg L) hlinear' hN
  have hscale' : 512 * (d + 2) ^ 2 * chainLength L m ≤ m := by
    exact_mod_cast hscale
  have hNpos : 0 < chainLength L m := lt_of_lt_of_le (by decide : 0 < 64)
    (chainLength_ge hm hLm)
  apply (Nat.le_div_iff_mul_le hNpos).mpr
  have hle : 256 * (d + 2) ^ 2 * chainLength L m ≤
      512 * (d + 2) ^ 2 * chainLength L m :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide : 256 ≤ 512))
  exact hle.trans hscale'

/-- A positive integer quotient is at least half of the corresponding real quotient. -/
theorem time_le_two_mul_floor {m N : ℕ} (hN : 0 < N) (hs : 1 ≤ m / N) :
    m ≤ 2 * N * (m / N) := by
  have hlt := Nat.lt_mul_div_succ m hN
  have hinc : m / N + 1 ≤ 2 * (m / N) := by omega
  have hmul := Nat.mul_le_mul_left N hinc
  nlinarith only [hlt, hmul]

/-- The center displacement fits within one quarter of the minimum diffusive radius. -/
theorem chainCenter_scale_le {L m : ℕ} (hm : 0 < m)
    (hLm : (m : ℝ) ≤ (L : ℝ) ^ 2) (hs : 1 ≤ m / chainLength L m) :
    (L : ℝ) / chainLength L m ≤ Real.sqrt (m / chainLength L m : ℕ) / 4 := by
  let N := chainLength L m
  let s := m / N
  have hN : 0 < N := lt_of_lt_of_le (by decide : 0 < 64) (chainLength_ge hm hLm)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hceil := Nat.le_ceil (64 * (L : ℝ) ^ 2 / m)
  have hlower : 64 * (L : ℝ) ^ 2 ≤ (N : ℝ) * m := by
    exact (div_le_iff₀ hmR).mp hceil
  have hfloor : (m : ℝ) ≤ 2 * N * (s : ℝ) := by
    exact_mod_cast time_le_two_mul_floor hN hs
  have hmul := mul_le_mul_of_nonneg_right hfloor hNR.le
  have hsquare : (4 * (L : ℝ)) ^ 2 ≤ (Real.sqrt s * N) ^ 2 := by
    simp only [mul_pow, Real.sq_sqrt (Nat.cast_nonneg s)]
    nlinarith only [hlower, hmul]
  have hroot : 4 * (L : ℝ) ≤ Real.sqrt s * N :=
    (sq_le_sq₀ (by positivity) (by positivity)).mp hsquare
  apply (div_le_iff₀ hNR).mpr
  dsimp only [s] at hroot
  linarith

/-- With the fixed parameters, every chaining edge lies inside its single-time window. -/
theorem chainSets_step_window (hd : 0 < d) (k : Site d) {m : ℕ} (hm : 0 < m)
    (hLm : (m : ℝ) ≤ (graphNorm k : ℝ) ^ 2)
    (hlinear : (graphNorm k : ℝ) ≤ (m : ℝ) / (256 * (d + 2)))
    (hp : graphNorm k % 2 = m % 2) (j : ℕ) {y y' : Site d}
    (hy : y ∈ chainSets hd k m (chainLength (graphNorm k) m)
      (chainRadius d (m / chainLength (graphNorm k) m)) j)
    (hy' : y' ∈ chainSets hd k m (chainLength (graphNorm k) m)
      (chainRadius d (m / chainLength (graphNorm k) m)) (j + 1)) :
    (graphNorm (y' - y) : ℝ) ^ 2 ≤
        ((j + 1) * m / chainLength (graphNorm k) m -
          j * m / chainLength (graphNorm k) m : ℕ) ∧
      graphNorm (y' - y) % 2 =
        ((j + 1) * m / chainLength (graphNorm k) m -
          j * m / chainLength (graphNorm k) m) % 2 := by
  let N := chainLength (graphNorm k) m
  let s := m / N
  have hN : 0 < N := lt_of_lt_of_le (by decide : 0 < 64) (chainLength_ge hm hLm)
  have hs := chain_floor_time_ge hd hm hLm hlinear
  have hspos : 1 ≤ s := by
    have hpos : 0 < 256 * (d + 2) ^ 2 := by positivity
    dsimp only [s, N]
    omega
  have hscale := chainCenter_scale_le hm hLm hspos
  have hdist := graphNorm_chainSets_step_le hd k m (chainRadius d s) hN hp j hy hy'
  have herr := graphNorm_chain_step_error_le hd hs hscale
  have hlength : (graphNorm (y' - y) : ℝ) ≤ Real.sqrt s := by
    have hnonneg := Real.sqrt_nonneg (s : ℝ)
    dsimp only [N, s] at *
    linarith
  refine ⟨?_, graphNorm_chainSets_step_mod_two hd k m _ hN hp j hy hy'⟩
  have hsq := (sq_le_sq₀ (Nat.cast_nonneg _) (Real.sqrt_nonneg (s : ℝ))).mpr hlength
  rw [Real.sq_sqrt (Nat.cast_nonneg s)] at hsq
  exact hsq.trans (by exact_mod_cast floor_time_increment_ge m N j)

/-- The actual floor-time parity boxes give a fixed-time lower bound with no geometric
premises left over. The product retains their exact cardinalities and increments. -/
theorem exists_srwHeat_lower_chainBoxes (hd : 0 < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (m : ℕ), 0 < m → ∀ k : Site d,
      (m : ℝ) ≤ (graphNorm k : ℝ) ^ 2 →
      (graphNorm k : ℝ) ≤ (m : ℝ) / (256 * (d + 2)) →
      graphNorm k % 2 = m % 2 →
      let N := chainLength (graphNorm k) m
      let ρ := chainRadius d (m / N)
      (∏ j ∈ Finset.range N,
        ((chainSets hd k m N ρ j).card : ℝ) *
          (c * (((j + 1) * m / N - j * m / N : ℕ) : ℝ) ^ (-(d : ℝ) / 2))) ≤
            srwHeat d m k := by
  obtain ⟨c, hc, hchain⟩ := exists_srwHeat_lower_window_chain hd
  refine ⟨c, hc, fun m hm k hLm hlinear hp => ?_⟩
  dsimp only
  let N := chainLength (graphNorm k) m
  let ρ := chainRadius d (m / N)
  have hN : 0 < N := lt_of_lt_of_le (by decide : 0 < 64) (chainLength_ge hm hLm)
  have hs := chain_floor_time_ge hd hm hLm hlinear
  have hspos : 1 ≤ m / N := by
    have hpos : 0 < 256 * (d + 2) ^ 2 := by positivity
    dsimp only [N]
    omega
  have hbound := hchain (fun j => (j + 1) * m / N - j * m / N)
    (chainSets hd k m N ρ) (chainSets_zero hd k m N ρ)
    (fun j => hspos.trans (floor_time_increment_ge m N j))
    (fun j y hy y' hy' => chainSets_step_window hd k hm hLm hlinear hp j hy hy')
    N k (by rw [chainSets_end hd k m ρ hN]; exact Finset.mem_singleton_self k)
  rw [sum_floor_time_increments m hN] at hbound
  exact hbound

/-- The negative half-dimensional power of a square cancels its dimensional power. -/
theorem sq_rpow_neg_half (a : ℝ) (ha : 0 < a) :
    (a ^ 2) ^ (-(d : ℝ) / 2) = (a ^ d)⁻¹ := by
  calc
    _ = a ^ ((2 : ℝ) * (-(d : ℝ) / 2)) :=
      (Real.rpow_natCast_mul ha.le 2 _).symm
    _ = a ^ (-(d : ℝ)) := by congr 1; ring
    _ = (a ^ d)⁻¹ := by rw [Real.rpow_neg ha.le, Real.rpow_natCast]

/-- The rounded parity-box width dominates the unrounded diffusive width. -/
theorem sqrt_le_chainRadius_width (hd : 0 < d) (s : ℕ) :
    Real.sqrt s ≤ 16 * (d : ℝ) * (2 * chainRadius d s + 1) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have h := Nat.lt_floor_add_one (Real.sqrt s / (16 * d))
  change Real.sqrt s / (16 * d) < (chainRadius d s : ℝ) + 1 at h
  have hmul := (div_lt_iff₀ (by positivity : (0 : ℝ) < 16 * d)).mp h
  have hρ : (0 : ℝ) ≤ chainRadius d s := Nat.cast_nonneg _
  nlinarith only [hmul, mul_nonneg hdR.le hρ]

/-- A box width at the prescribed radius supplies the exact dimensional factor needed
at every interior convolution step. -/
theorem chainBox_card_mul_rpow_ge (hd : 0 < d) {s t : ℕ}
    (ht : 0 < t) (hts : t ≤ 2 * s) :
    (512 * (d : ℝ) ^ 2) ^ (-(d : ℝ) / 2) ≤
      (((2 * chainRadius d s + 1) ^ d : ℕ) : ℝ) *
        (t : ℝ) ^ (-(d : ℝ) / 2) := by
  let a : ℝ := 2 * chainRadius d s + 1
  have ha : 0 < a := by dsimp only [a]; positivity
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hwidth := sqrt_le_chainRadius_width hd s
  have hsquare : (s : ℝ) ≤ 256 * (d : ℝ) ^ 2 * a ^ 2 := by
    have h := (sq_le_sq₀ (Real.sqrt_nonneg (s : ℝ))
      (by dsimp only [a]; positivity : (0 : ℝ) ≤ 16 * d * a)).mpr hwidth
    rw [Real.sq_sqrt (Nat.cast_nonneg s)] at h
    nlinarith only [h]
  have hbound : (t : ℝ) ≤ (512 * (d : ℝ) ^ 2) * a ^ 2 := by
    have htR' : (t : ℝ) ≤ 2 * s := by exact_mod_cast hts
    linarith
  have hneg : -(d : ℝ) / 2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg d)) (by norm_num)
  have hpow := Real.rpow_le_rpow_of_nonpos htR hbound hneg
  rw [Real.mul_rpow (by positivity) (sq_nonneg a), sq_rpow_neg_half a ha] at hpow
  have hmul := mul_le_mul_of_nonneg_left hpow (pow_nonneg ha.le d)
  have hcancel : a ^ d *
      ((512 * (d : ℝ) ^ 2) ^ (-(d : ℝ) / 2) * (a ^ d)⁻¹) =
        (512 * (d : ℝ) ^ 2) ^ (-(d : ℝ) / 2) := by
    rw [mul_left_comm, mul_inv_cancel₀ (ne_of_gt (pow_pos ha d)), mul_one]
  rw [hcancel] at hmul
  simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, a] using hmul

/-- Counting all intermediate parity boxes leaves a dimensional factor for every link
except the first, and one polynomial prefactor at the minimum time. -/
theorem exists_srwHeat_lower_chain_power (hd : 0 < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (m : ℕ), 0 < m → ∀ k : Site d,
      (m : ℝ) ≤ (graphNorm k : ℝ) ^ 2 →
      (graphNorm k : ℝ) ≤ (m : ℝ) / (256 * (d + 2)) →
      graphNorm k % 2 = m % 2 →
      let N := chainLength (graphNorm k) m
      let s := m / N
      c * (2 * (s : ℝ)) ^ (-(d : ℝ) / 2) *
        (c * (512 * (d : ℝ) ^ 2) ^ (-(d : ℝ) / 2)) ^ (N - 1) ≤ srwHeat d m k := by
  obtain ⟨c, hc, hchain⟩ := exists_srwHeat_lower_chainBoxes hd
  refine ⟨c, hc, fun m hm k hLm hlinear hp => ?_⟩
  dsimp only
  let N := chainLength (graphNorm k) m
  let s := m / N
  let ρ := chainRadius d s
  let f : ℕ → ℝ := fun j => ((chainSets hd k m N ρ j).card : ℝ) *
    (c * (((j + 1) * m / N - j * m / N : ℕ) : ℝ) ^ (-(d : ℝ) / 2))
  let b : ℝ := c * (512 * (d : ℝ) ^ 2) ^ (-(d : ℝ) / 2)
  have hN : 0 < N := lt_of_lt_of_le (by decide : 0 < 64) (chainLength_ge hm hLm)
  have hs := chain_floor_time_ge hd hm hLm hlinear
  have hspos : 1 ≤ s := by
    have hpos : 0 < 256 * (d + 2) ^ 2 := by positivity
    dsimp only [s, N]
    omega
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hneg : -(d : ℝ) / 2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg d)) (by norm_num)
  have hfirst : c * (2 * (s : ℝ)) ^ (-(d : ℝ) / 2) ≤ f 0 := by
    have hsR : (0 : ℝ) < s := by exact_mod_cast hspos
    have hpow := Real.rpow_le_rpow_of_nonpos hsR (by linarith : (s : ℝ) ≤ 2 * s) hneg
    simpa only [f, chainSets_zero, Finset.card_singleton, Nat.cast_one, one_mul,
      zero_add, zero_mul, Nat.zero_div, Nat.sub_zero] using
      mul_le_mul_of_nonneg_left hpow hc.le
  have hinterior : ∀ j < N - 1, b ≤ f (j + 1) := by
    intro j hj
    have hcard := card_chainSets hd k m N ρ (by omega : 0 < j + 1)
      (by omega : j + 1 < N)
    have hlow := floor_time_increment_ge m N (j + 1)
    have hupp := floor_time_increment_le m (j + 1) hN
    have ht : 0 < (j + 1 + 1) * m / N - (j + 1) * m / N := by
      dsimp only [s] at hspos
      omega
    have hts : (j + 1 + 1) * m / N - (j + 1) * m / N ≤ 2 * s := by
      dsimp only [s] at *
      omega
    have hfactor := mul_le_mul_of_nonneg_left (chainBox_card_mul_rpow_ge hd ht hts) hc.le
    dsimp only [f, b]
    rw [hcard]
    dsimp only [ρ]
    nlinarith only [hfactor]
  have hprod : b ^ (N - 1) ≤ ∏ j ∈ Finset.range (N - 1), f (j + 1) := by
    calc
      _ = ∏ _j ∈ Finset.range (N - 1), b := by
        rw [Finset.prod_const, Finset.card_range]
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => hb)
        (fun j hj => hinterior j (Finset.mem_range.mp hj))
  have hbound := mul_le_mul hprod hfirst (by positivity)
    (Finset.prod_nonneg (fun j _ => by dsimp only [f]; positivity))
  have hNpred : N - 1 + 1 = N := by omega
  rw [← Finset.prod_range_succ', hNpred] at hbound
  have hactual := hchain m hm k hLm hlinear hp
  dsimp only at hactual
  calc
    _ = b ^ (N - 1) * (c * (2 * (s : ℝ)) ^ (-(d : ℝ) / 2)) := by
      dsimp only [b]
      ring
    _ ≤ ∏ j ∈ Finset.range N, f j := hbound
    _ ≤ _ := hactual

/-- A positive per-link factor has exponential loss controlled by any upper bound on
its link count; factors larger than one incur no loss. -/
theorem exp_neg_log_min_le_pow {b r : ℝ} (hb : 0 < b) {N : ℕ} (hN : (N : ℝ) ≤ r) :
    Real.exp (-r * Real.log (1 / min b 1)) ≤ b ^ (N - 1) := by
  have ha : 0 < min b 1 := lt_min hb zero_lt_one
  have ha1 : min b 1 ≤ 1 := min_le_right _ _
  have hlog : Real.log (min b 1) ≤ 0 := Real.log_nonpos ha.le ha1
  have hpred : ((N - 1 : ℕ) : ℝ) ≤ r :=
    (show ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) by exact_mod_cast (Nat.sub_le N 1)).trans hN
  have hexponent : -r * Real.log (1 / min b 1) ≤
      ((N - 1 : ℕ) : ℝ) * Real.log (min b 1) := by
    rw [one_div, Real.log_inv]
    nlinarith only [mul_le_mul_of_nonpos_right hpred hlog]
  calc
    _ ≤ Real.exp (((N - 1 : ℕ) : ℝ) * Real.log (min b 1)) :=
      Real.exp_le_exp.mpr hexponent
    _ = min b 1 ^ (N - 1) := by
      rw [Real.exp_nat_mul, Real.exp_log ha]
    _ ≤ _ := pow_le_pow_left₀ ha.le (min_le_left _ _) _

/-- The parity-box chain gives the Gaussian lower bound throughout the intermediate
linear region, at a single time of the target site's parity. -/
theorem exists_srwHeat_lower_gaussian_intermediate (hd : 0 < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (m : ℕ), 0 < m → ∀ k : Site d,
      (m : ℝ) ≤ (graphNorm k : ℝ) ^ 2 →
      (graphNorm k : ℝ) ≤ (m : ℝ) / (256 * (d + 2)) →
      graphNorm k % 2 = m % 2 →
      c * (2 * (m : ℝ)) ^ (-(d : ℝ) / 2) *
        Real.exp (-(128 * Real.log
          (1 / min (c * (512 * (d : ℝ) ^ 2) ^ (-(d : ℝ) / 2)) 1) *
            (graphNorm k : ℝ) ^ 2 / m)) ≤ srwHeat d m k := by
  obtain ⟨c, hc, hpower⟩ := exists_srwHeat_lower_chain_power hd
  refine ⟨c, hc, fun m hm k hLm hlinear hp => ?_⟩
  let N := chainLength (graphNorm k) m
  let s := m / N
  let b := c * (512 * (d : ℝ) ^ 2) ^ (-(d : ℝ) / 2)
  have hb : 0 < b := by dsimp only [b]; positivity
  have hs := chain_floor_time_ge hd hm hLm hlinear
  have hspos : 0 < s := by
    have hpos : 0 < 256 * (d + 2) ^ 2 := by positivity
    dsimp only [s, N]
    omega
  have hsR : (0 : ℝ) < 2 * s := by positivity
  have hsm : (2 * s : ℝ) ≤ 2 * m := by
    have hdiv : s ≤ m := Nat.div_le_self m N
    exact_mod_cast Nat.mul_le_mul_left 2 hdiv
  have hneg : -(d : ℝ) / 2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg d)) (by norm_num)
  have hpre := mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos hsR hsm hneg) hc.le
  have hexp := exp_neg_log_min_le_pow hb (chainLength_le hm hLm)
  have hactual := hpower m hm k hLm hlinear hp
  dsimp only at hactual
  have hbound := mul_le_mul hpre hexp (Real.exp_nonneg _)
    (by positivity : 0 ≤ c * (2 * (s : ℝ)) ^ (-(d : ℝ) / 2))
  have heq : -(128 * Real.log (1 / min b 1) * (graphNorm k : ℝ) ^ 2 / m) =
      -(128 * (graphNorm k : ℝ) ^ 2 / m) * Real.log (1 / min b 1) := by ring
  change c * (2 * (m : ℝ)) ^ (-(d : ℝ) / 2) * Real.exp
    (-(128 * Real.log (1 / min b 1) * (graphNorm k : ℝ) ^ 2 / m)) ≤ _
  rw [heq]
  exact hbound.trans hactual

/-- The paired kernel has Gaussian decay with dimension-dependent constants throughout
the entire reachable ball, combining the diffusive, chaining, and single-path regions. -/
theorem exists_srwHeat_add_succ_lower_gaussian (hd : 0 < d) :
    ∃ a C : ℝ, 0 < a ∧ 0 ≤ C ∧ ∀ n : ℕ, 1 ≤ n → ∀ k : Site d,
      graphNorm k ≤ n → a * (n : ℝ) ^ (-(d : ℝ) / 2) *
        Real.exp (-(C * (graphNorm k : ℝ) ^ 2 / n)) ≤
          srwHeat d n k + srwHeat d (n + 1) k := by
  obtain ⟨a₀, ha₀, hnear⟩ := exists_srwHeat_add_succ_lower_graph_window hd
  obtain ⟨c, hc, hinter⟩ := exists_srwHeat_lower_gaussian_intermediate hd
  let A : ℝ := 256 * (d + 2)
  let b : ℝ := c * (512 * (d : ℝ) ^ 2) ^ (-(d : ℝ) / 2)
  let C₁ : ℝ := 128 * Real.log (1 / min b 1)
  let C₂ : ℝ := 2 * Real.log (2 * (d : ℝ)) * A ^ 2
  let C := max C₁ C₂
  let a := min a₀ (min (c * (4 : ℝ) ^ (-(d : ℝ) / 2)) 1)
  have hA : 0 < A := by dsimp only [A]; positivity
  have hb : 0 < b := by dsimp only [b]; positivity
  have hC₁ : 0 ≤ C₁ := by
    dsimp only [C₁]
    apply mul_nonneg (by norm_num)
    apply Real.log_nonneg
    exact (one_le_div (lt_min hb zero_lt_one)).mpr (min_le_right _ _)
  have hC : 0 ≤ C := hC₁.trans (le_max_left _ _)
  have ha : 0 < a := by dsimp only [a]; positivity
  have ha₀' : a ≤ a₀ := min_le_left _ _
  have hac : a ≤ c * (4 : ℝ) ^ (-(d : ℝ) / 2) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have ha1 : a ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨a, C, ha, hC, fun n hn k hkn => ?_⟩
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hneg : -(d : ℝ) / 2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Nat.cast_nonneg d)) (by norm_num)
  have hpre : 0 ≤ a * (n : ℝ) ^ (-(d : ℝ) / 2) := by positivity
  by_cases hdiff : (graphNorm k : ℝ) ^ 2 ≤ n
  · have hexp : Real.exp (-(C * (graphNorm k : ℝ) ^ 2 / n)) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      exact neg_nonpos.mpr (div_nonneg (mul_nonneg hC (sq_nonneg _)) hnpos.le)
    exact (mul_le_of_le_one_right hpre hexp).trans
      ((mul_le_mul_of_nonneg_right ha₀' (by positivity)).trans (hnear n hn k hdiff))
  · by_cases hlinear : (graphNorm k : ℝ) ≤ (n : ℝ) / A
    · have hsingle : ∀ m : ℕ, n ≤ m → m ≤ n + 1 →
          graphNorm k % 2 = m % 2 →
          a * (n : ℝ) ^ (-(d : ℝ) / 2) *
            Real.exp (-(C * (graphNorm k : ℝ) ^ 2 / n)) ≤ srwHeat d m k := by
        intro m hnm hmn hp
        have hm : 0 < m := by omega
        have hmR : (0 : ℝ) < m := by exact_mod_cast hm
        have hnmR : (n : ℝ) ≤ m := by exact_mod_cast hnm
        have hmnR : (m : ℝ) ≤ n + 1 := by exact_mod_cast hmn
        have hLm : (m : ℝ) ≤ (graphNorm k : ℝ) ^ 2 := by
          have hnat : n < (graphNorm k) ^ 2 := by exact_mod_cast (lt_of_not_ge hdiff)
          exact_mod_cast (show m ≤ (graphNorm k) ^ 2 by omega)
        have hlinm : (graphNorm k : ℝ) ≤ (m : ℝ) / (256 * (d + 2)) :=
          hlinear.trans (div_le_div_of_nonneg_right hnmR hA.le)
        have hpow := Real.rpow_le_rpow_of_nonpos
          (by positivity : (0 : ℝ) < 2 * m)
          (by linarith : (2 * m : ℝ) ≤ 4 * n) hneg
        have hpref : a * (n : ℝ) ^ (-(d : ℝ) / 2) ≤
            c * (2 * (m : ℝ)) ^ (-(d : ℝ) / 2) := by
          have hh := mul_le_mul_of_nonneg_left hpow hc.le
          rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) hnpos.le] at hh
          exact (mul_le_mul_of_nonneg_right hac (by positivity)).trans (by
            convert hh using 1; ring)
        have hratio : C₁ * (graphNorm k : ℝ) ^ 2 / m ≤
            C * (graphNorm k : ℝ) ^ 2 / n :=
          (div_le_div_of_nonneg_left (mul_nonneg hC₁ (sq_nonneg _)) hnpos hnmR).trans
            (div_le_div_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) (sq_nonneg _)) hnpos.le)
        have hexp := Real.exp_le_exp.mpr (neg_le_neg hratio)
        have hraw := hinter m hm k hLm hlinm hp
        exact (mul_le_mul hpref hexp (Real.exp_nonneg _) (by positivity)).trans hraw
      by_cases hp : graphNorm k % 2 = n % 2
      · exact (hsingle n (by omega) (by omega) hp).trans
          (le_add_of_nonneg_right (srwHeat_nonneg _ _))
      · have hp' : graphNorm k % 2 = (n + 1) % 2 := by omega
        exact (hsingle (n + 1) (by omega) (by omega) hp').trans
          (le_add_of_nonneg_left (srwHeat_nonneg _ _))
    · have houter : (n : ℝ) ≤ A * graphNorm k := by
        have h := (div_lt_iff₀ hA).mp (lt_of_not_ge hlinear)
        linarith
      have hpref : a * (n : ℝ) ^ (-(d : ℝ) / 2) ≤ 1 :=
        (mul_le_of_le_one_right ha.le
          (Real.rpow_le_one_of_one_le_of_nonpos hnR hneg)).trans ha1
      have hratio : C₂ * (graphNorm k : ℝ) ^ 2 / n ≤
          C * (graphNorm k : ℝ) ^ 2 / n :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) (sq_nonneg _)) hnpos.le
      exact (mul_le_of_le_one_left (Real.exp_nonneg _) hpref).trans
        ((Real.exp_le_exp.mpr (neg_le_neg hratio)).trans
          (srwHeat_add_succ_ge_gaussian_outer hd hA hn k hkn houter))

/-- The normalized lattice satisfies the full MSC Gaussian lower antecedent at all
positive times and all reachable sites, with one constant depending only on dimension. -/
theorem weightedLattice_gaussian_lower (hd : 0 < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ x y (n : ℕ), 1 ≤ n →
      (weightedLattice d hd).graph.dist x y ≤ n →
      ENNReal.ofReal
        (c / latticeVolumeProfile d ((n : ℝ) ^ (1 / (2 : ℝ))) *
          Real.exp (-((((weightedLattice d hd).graph.dist x y : ℝ) ^ (2 : ℝ) /
            (c * n)) ^ (1 / ((2 : ℝ) - 1))))) ≤
        (weightedLattice d hd).heat n x y + (weightedLattice d hd).heat (n + 1) x y := by
  obtain ⟨a, C, ha, hC, hlow⟩ := exists_srwHeat_add_succ_lower_gaussian hd
  let c := min a (1 / (1 + C))
  have hc : 0 < c := by dsimp only [c]; positivity
  have hca : c ≤ a := min_le_left _ _
  have hcC : c * C ≤ 1 := by
    calc
      _ ≤ (1 / (1 + C)) * C :=
        mul_le_mul_of_nonneg_right (min_le_right _ _) hC
      _ = C / (1 + C) := by ring
      _ ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
  refine ⟨c, hc, fun x y n hn hle => ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hdist : (weightedLattice d hd).graph.dist x y = graphNorm (y - x) :=
    lattice_dist_eq_graphNorm hd x y
  rw [hdist] at hle ⊢
  let t : ℝ := (n : ℝ) ^ (1 / (2 : ℝ))
  have ht : 0 < t := Real.rpow_pos_of_pos hnpos _
  have hpow : (n : ℝ) ^ (-(d : ℝ) / 2) = (t ^ d)⁻¹ := by
    rw [show -(d : ℝ) / 2 = -((1 / (2 : ℝ)) * d) by ring,
      Real.rpow_neg hnpos.le, Real.rpow_mul hnpos.le, Real.rpow_natCast]
  have hpre : c / (1 + t) ^ d ≤ a * (n : ℝ) ^ (-(d : ℝ) / 2) := by
    calc
      _ ≤ c / t ^ d := div_le_div_of_nonneg_left hc.le (pow_pos ht d)
        (pow_le_pow_left₀ ht.le (by linarith) d)
      _ = c * (n : ℝ) ^ (-(d : ℝ) / 2) := by rw [hpow, div_eq_mul_inv]
      _ ≤ _ := mul_le_mul_of_nonneg_right hca (by positivity)
  have hratio : C * (graphNorm (y - x) : ℝ) ^ 2 / n ≤
      (graphNorm (y - x) : ℝ) ^ 2 / (c * n) := by
    apply (le_div_iff₀ (mul_pos hc hnpos)).mpr
    have hh := mul_le_mul_of_nonneg_right hcC
      (sq_nonneg (graphNorm (y - x) : ℝ))
    calc
      _ = (c * C) * (graphNorm (y - x) : ℝ) ^ 2 := by
        field_simp [ne_of_gt hnpos]
      _ ≤ _ := by simpa only [one_mul] using hh
  rw [weightedLattice_heat_eq, weightedLattice_heat_eq,
    ← ENNReal.ofReal_add (srwHeat_nonneg _ _) (srwHeat_nonneg _ _)]
  apply ENNReal.ofReal_le_ofReal
  simp only [show (1 : ℝ) / (2 - 1) = 1 by norm_num, Real.rpow_one, Real.rpow_two]
  exact (mul_le_mul hpre (Real.exp_le_exp.mpr (neg_le_neg hratio))
    (Real.exp_nonneg _) (by positivity)).trans (hlow n hn (y - x) hle)

end

end LatticeProb.Graph.LongRangeKernel
