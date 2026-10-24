import LatticeProb.Graph.LongRangeKernel.LatticeDistance
import LatticeProb.Walk.SRWMultinomial
import LatticeProb.Walk.BinomialLower
import LatticeProb.Walk.LocalCLTWindow
import LatticeProb.Walk.SRWPos

/-!
# Lower bounds for the lattice heat kernel

A single reachable path gives an exponential lower bound, with the parity correction
implemented by adding one time step. The paired local central limit theorem also gives
a Gaussian lower estimate on the unit diffusive window in graph distance.
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

end

end LatticeProb.Graph.LongRangeKernel
