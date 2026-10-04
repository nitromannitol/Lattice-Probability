import Mathlib
import LatticeProb.Walk.GreenPointwise
import LatticeProb.Walk.GreenTwoSided.Kernels
import LatticeProb.Walk.VarianceScale
import LatticeProb.Walk.Shells
import LatticeProb.Walk.GreenIdentity
import LatticeProb.Network.Killed
import LatticeProb.Network.Caccioppoli

set_option autoImplicit false
set_option relaxedAutoImplicit false

open MeasureTheory

noncomputable section

namespace LatticeProb.BallGreen

/-- The box `Q(0, r) = {y ∈ ℤ⁴ : max_i |y_i| ≤ r}`. -/
def box (r : ℕ) : Set (Site 4) :=
  {y | ∀ i : Fin 4, (y i).natAbs ≤ r}

/-- The killed Green kernel `g^D(x, y) = ∑_k P_x(X_k = y, k < τ_D)` on `ℤ⁴`. -/
def killedGreen (D : Set (Site 4)) (x y : Site 4) : ℝ :=
  ∑' k : ℕ, Graph.killedHeat (lattice 4) D k x y

/-- The killed finite-time Green kernel `g_t^D(x, y) = ∑_{k<t} P_x(X_k = y, k < τ_D)`. -/
def killedGreenTime (D : Set (Site 4)) (t : ℕ) (x y : Site 4) : ℝ :=
  ∑ k ∈ Finset.range t, Graph.killedHeat (lattice 4) D k x y

/-- A cutoff: `φ : [0, ∞) → [0, 1]`, `2`-Lipschitz, `0` on `[0, 1]` and `1` on `[2, ∞)`. -/
def IsCutoff (φ : ℝ → ℝ) : Prop :=
  (∀ s : ℝ, 0 ≤ s → φ s ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ s t : ℝ, 0 ≤ s → 0 ≤ t → |φ s - φ t| ≤ 2 * |s - t|) ∧
    (∀ s : ℝ, 0 ≤ s → s ≤ 1 → φ s = 0) ∧
    (∀ s : ℝ, 2 ≤ s → φ s = 1)

/-- The cut-off ball-killed Green field `h(u) = g^{Q(0,r)}(0, u) φ(|u|/L)`. -/
def cutField (r : ℕ) (L : ℕ) (φ : ℝ → ℝ) (u : Site 4) : ℝ :=
  killedGreen (box r) 0 u * φ (euclidNorm u / (L : ℝ))

/-- The finite-time tail `q_{r,A}(u) = g^{Q(0,r)}(0, u) - g^{Q(0,r)}_{⌊A r²⌋}(0, u)`. -/
def timeTail (r : ℕ) (A : ℝ) (u : Site 4) : ℝ :=
  killedGreen (box r) 0 u - killedGreenTime (box r) ⌊A * (r : ℝ) ^ 2⌋₊ 0 u

/-! ### A. The point bound and the square sums -/

theorem summable_killedHeat (D : Set (Site 4)) (x y : Site 4) :
    Summable fun k : ℕ => Graph.killedHeat (lattice 4) D k x y := by
  refine Summable.of_nonneg_of_le (fun k => Network.killedHeat_nonneg D k x y)
    (fun k => ?_) (summable_srwHeat (by norm_num) (x - y))
  simpa only [zero_sub, srwHeat_neg] using
    LatticeProb.GreenTwoSided.killedHeat_le_srwHeat_sub (d := 4) D k x y
theorem killedGreen_nonneg (D : Set (Site 4)) (x y : Site 4) : 0 ≤ killedGreen D x y := by
  unfold killedGreen
  exact tsum_nonneg (fun k => Network.killedHeat_nonneg D k x y)
theorem killedGreen_le_srwGreenInf (D : Set (Site 4)) (u : Site 4) :
    killedGreen D 0 u ≤ srwGreenInf 4 u := by
  unfold killedGreen srwGreenInf
  refine Summable.tsum_le_tsum (fun k => ?_) (summable_killedHeat D 0 u)
    (summable_srwHeat (by norm_num) u)
  simpa only [zero_sub, srwHeat_neg] using
    LatticeProb.GreenTwoSided.killedHeat_le_srwHeat_sub (d := 4) D k 0 u
theorem killedGreen_eq_zero_of_notMem (D : Set (Site 4)) {u : Site 4} (hu : u ∉ D) :
    killedGreen D 0 u = 0 := by
  unfold killedGreen
  have h : (fun k : ℕ => Graph.killedHeat (lattice 4) D k 0 u) = fun _ => (0 : ℝ) :=
    funext fun k => Network.killedHeat_of_target_not_mem (C := D) (y := u) hu k 0
  rw [h, tsum_zero]
theorem exists_srwGreenInf_four_le :
    ∃ C : ℝ, 0 < C ∧ ∀ u : Site 4, srwGreenInf 4 u ≤ C / (1 + euclidNorm u) ^ 2 := by
  obtain ⟨C, hCpos, hC⟩ := exists_srwGreenInf_le (k := 0)
  refine ⟨C, hCpos, fun u => ?_⟩
  have hbase : srwGreenInf 4 u ≤ C / (1 + ((graphNorm u : ℕ) : ℝ)) ^ 2 := by
    simpa using hC u
  have hle : (1 + euclidNorm u) ^ 2 ≤ (1 + ((graphNorm u : ℕ) : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (by linarith [euclidNorm_nonneg u])
      (by linarith [euclidNorm_le_graphNorm u]) 2
  exact hbase.trans
    (div_le_div_of_nonneg_left hCpos.le (pow_pos (by linarith [euclidNorm_nonneg u]) 2) hle)
private theorem mem_box_iff_supNorm_le (u : Site 4) (r : ℕ) :
    u ∈ box r ↔ supNorm u ≤ r := by
  rw [box, supNorm_le_iff]
  constructor
  · intro h i
    have hi : ((u i).natAbs : ℤ) ≤ (r : ℤ) := by exact_mod_cast h i
    rwa [Int.natCast_natAbs] at hi
  · intro h i
    have hi : ((u i).natAbs : ℤ) ≤ (r : ℤ) := by
      rw [Int.natCast_natAbs]
      exact h i
    exact_mod_cast hi

/-- The square of the ball-killed Green function is bounded by the square of the
pointwise Green bound, written against the sup-norm. -/

private theorem killedGreen_sq_le (r : ℕ) {C0 : ℝ} (hC0 : 0 < C0)
    (hC0bound : ∀ u : Site 4, srwGreenInf 4 u ≤ C0 / (1 + euclidNorm u) ^ 2)
    (u : Site 4) :
    killedGreen (box r) 0 u ^ 2 ≤ C0 ^ 2 * (1 / (1 + (supNorm u : ℝ)) ^ 4) := by
  have hgnn : 0 ≤ killedGreen (box r) 0 u := killedGreen_nonneg (box r) 0 u
  have hse : (supNorm u : ℝ) ≤ euclidNorm u := supNorm_le_euclidNorm u
  have hden_s : (0 : ℝ) < (1 + (supNorm u : ℝ)) ^ 2 := by positivity
  have hden_e : (0 : ℝ) < (1 + euclidNorm u) ^ 2 := by
    have h1 : (0 : ℝ) < 1 + euclidNorm u := by linarith [euclidNorm_nonneg u]
    positivity
  have hratio : C0 / (1 + euclidNorm u) ^ 2 ≤ C0 / (1 + (supNorm u : ℝ)) ^ 2 := by
    rw [div_le_div_iff₀ hden_e hden_s]
    have hle : (1 + (supNorm u : ℝ)) ^ 2 ≤ (1 + euclidNorm u) ^ 2 := by
      apply pow_le_pow_left₀ (by positivity)
      linarith
    nlinarith [hC0.le]
  have hg : killedGreen (box r) 0 u ≤ C0 / (1 + (supNorm u : ℝ)) ^ 2 :=
    le_trans (killedGreen_le_srwGreenInf (box r) u) (le_trans (hC0bound u) hratio)
  have hsq : killedGreen (box r) 0 u ^ 2 ≤ (C0 / (1 + (supNorm u : ℝ)) ^ 2) ^ 2 :=
    pow_le_pow_left₀ hgnn hg 2
  refine hsq.trans (le_of_eq ?_)
  have hne : (1 + (supNorm u : ℝ)) ≠ 0 := by positivity
  field_simp

theorem exists_sum_box_inv_pow_four_le :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      ∑ u ∈ boxFinset (0 : Site 4) n, 1 / (1 + (supNorm u : ℝ)) ^ 4
        ≤ C * Real.log ((n : ℝ) + 2) := by
  refine ⟨64 + 1 / Real.log 2, by positivity, fun n => ?_⟩
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hterm : ∀ k ∈ Finset.Icc 1 n,
      (shellCard 4 k : ℝ) * (1 / (1 + (k : ℝ)) ^ 4) ≤ 64 * (1 / ((k : ℝ) + 1)) := by
    intro k hk
    have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
    have hshell : (shellCard 4 k : ℝ) ≤ 8 * (2 * (k : ℝ) + 1) ^ 3 := by
      have h := shellCard_le 4 hk1
      norm_num at h
      exact h
    have hbase : 2 * (k : ℝ) + 1 ≤ 2 * ((k : ℝ) + 1) := by linarith
    have hpow : (2 * (k : ℝ) + 1) ^ 3 ≤ 8 * ((k : ℝ) + 1) ^ 3 := by
      calc (2 * (k : ℝ) + 1) ^ 3 ≤ (2 * ((k : ℝ) + 1)) ^ 3 :=
            pow_le_pow_left₀ (by positivity) hbase 3
        _ = 8 * ((k : ℝ) + 1) ^ 3 := by ring
    have hshell3 : (shellCard 4 k : ℝ) ≤ 64 * ((k : ℝ) + 1) ^ 3 := by
      calc (shellCard 4 k : ℝ) ≤ 8 * (2 * (k : ℝ) + 1) ^ 3 := hshell
        _ ≤ 8 * (8 * ((k : ℝ) + 1) ^ 3) := by linarith [hpow]
        _ = 64 * ((k : ℝ) + 1) ^ 3 := by ring
    have hfac : (1 : ℝ) / (1 + (k : ℝ)) ^ 4 = 1 / ((k : ℝ) + 1) ^ 4 := by ring_nf
    calc (shellCard 4 k : ℝ) * (1 / (1 + (k : ℝ)) ^ 4)
        = (shellCard 4 k : ℝ) * (1 / ((k : ℝ) + 1) ^ 4) := by rw [hfac]
      _ ≤ (64 * ((k : ℝ) + 1) ^ 3) * (1 / ((k : ℝ) + 1) ^ 4) :=
            mul_le_mul hshell3 le_rfl (by positivity) (by positivity)
      _ = 64 * (1 / ((k : ℝ) + 1)) := by
            have hk : (k : ℝ) + 1 ≠ 0 := by positivity
            field_simp
  rw [sum_box_radial (fun m => 1 / (1 + (m : ℝ)) ^ 4) n]
  calc
    1 / (1 + ((0 : ℕ) : ℝ)) ^ 4
        + ∑ k ∈ Finset.Icc 1 n, (shellCard 4 k : ℝ) * (1 / (1 + (k : ℝ)) ^ 4)
        ≤ 1 + ∑ k ∈ Finset.Icc 1 n, 64 * (1 / ((k : ℝ) + 1)) := by
          rw [show (1 : ℝ) / (1 + ((0 : ℕ) : ℝ)) ^ 4 = 1 by norm_num]
          exact add_le_add le_rfl (Finset.sum_le_sum hterm)
    _ = 1 + 64 * ∑ k ∈ Finset.Icc 1 n, (1 / ((k : ℝ) + 1)) := by
          rw [Finset.mul_sum]
    _ ≤ 1 + 64 * Real.log ((n : ℝ) + 1) := by
          exact add_le_add le_rfl
            (mul_le_mul_of_nonneg_left (sum_inv_succ_le_log n) (by norm_num))
    _ ≤ (64 + 1 / Real.log 2) * Real.log ((n : ℝ) + 2) := by
          have hL12 : Real.log ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 2) :=
            Real.log_le_log (by positivity) (by linarith)
          have hL2ge : Real.log 2 ≤ Real.log ((n : ℝ) + 2) := by
            apply Real.log_le_log (by norm_num)
            linarith
          have hone : (1 : ℝ) ≤ (1 / Real.log 2) * Real.log ((n : ℝ) + 2) := by
            have h := mul_le_mul_of_nonneg_left hL2ge
              (by positivity : (0 : ℝ) ≤ 1 / Real.log 2)
            rwa [one_div_mul_cancel (ne_of_gt hlog2)] at h
          have h64 : 64 * Real.log ((n : ℝ) + 1) ≤ 64 * Real.log ((n : ℝ) + 2) :=
            mul_le_mul_of_nonneg_left hL12 (by norm_num)
          nlinarith [hone, h64]
theorem exists_tsum_killedGreen_sq_le :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℕ, 2 ≤ r →
      ∑' u : Site 4, killedGreen (box r) 0 u ^ 2 ≤ C * Real.log (r : ℝ) := by
  obtain ⟨C0, hC0pos, hC0⟩ := exists_srwGreenInf_four_le
  obtain ⟨C1, hC1pos, hC1⟩ := exists_sum_box_inv_pow_four_le
  refine ⟨C0 ^ 2 * (C1 * 2), by positivity, fun r hr => ?_⟩
  have hsupp : ∀ u : Site 4, u ∉ boxFinset (0 : Site 4) r →
      killedGreen (box r) 0 u ^ 2 = 0 := by
    intro u hu
    have hnot : u ∉ box r := by
      intro hmem
      exact hu (mem_boxFinset_zero_iff.mpr ((mem_box_iff_supNorm_le u r).mp hmem))
    rw [killedGreen_eq_zero_of_notMem (box r) hnot]
    norm_num
  rw [tsum_eq_sum (s := boxFinset (0 : Site 4) r) hsupp]
  have hlog : Real.log ((r : ℝ) + 2) ≤ 2 * Real.log (r : ℝ) := by
    have hle : (r : ℝ) + 2 ≤ (r : ℝ) ^ 2 := by
      have h2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      nlinarith
    calc Real.log ((r : ℝ) + 2) ≤ Real.log ((r : ℝ) ^ 2) :=
          Real.log_le_log (by positivity) hle
      _ = 2 * Real.log (r : ℝ) := by rw [Real.log_pow]; norm_num
  calc
    ∑ u ∈ boxFinset (0 : Site 4) r, killedGreen (box r) 0 u ^ 2
        ≤ ∑ u ∈ boxFinset (0 : Site 4) r, C0 ^ 2 * (1 / (1 + (supNorm u : ℝ)) ^ 4) :=
          Finset.sum_le_sum fun u _ => killedGreen_sq_le r hC0pos hC0 u
    _ = C0 ^ 2 * ∑ u ∈ boxFinset (0 : Site 4) r, 1 / (1 + (supNorm u : ℝ)) ^ 4 := by
          rw [Finset.mul_sum]
    _ ≤ C0 ^ 2 * (C1 * Real.log ((r : ℝ) + 2)) :=
          mul_le_mul_of_nonneg_left (hC1 r) (by positivity)
    _ ≤ C0 ^ 2 * (C1 * (2 * Real.log (r : ℝ))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hlog hC1pos.le) (by positivity)
    _ = C0 ^ 2 * (C1 * 2) * Real.log (r : ℝ) := by ring
theorem exists_tsum_near_killedGreen_sq_le :
    ∃ C : ℝ, 0 < C ∧ ∀ r L : ℕ, 2 ≤ L →
      ∑' u : {u : Site 4 // euclidNorm u ≤ 2 * (L : ℝ)},
          killedGreen (box r) 0 (u : Site 4) ^ 2
        ≤ C * Real.log (2 * (L : ℝ) + 2) := by
  obtain ⟨C0, hC0pos, hC0⟩ := exists_srwGreenInf_four_le
  obtain ⟨C1, hC1pos, hC1⟩ := exists_sum_box_inv_pow_four_le
  refine ⟨C0 ^ 2 * C1, by positivity, fun r L _ => ?_⟩
  have hsub : (∑' u : {u : Site 4 // euclidNorm u ≤ 2 * (L : ℝ)},
        killedGreen (box r) 0 (u : Site 4) ^ 2)
      = ∑' u : Site 4, {u : Site 4 | euclidNorm u ≤ 2 * (L : ℝ)}.indicator
          (fun u => killedGreen (box r) 0 u ^ 2) u := by
    change (∑' u : ↥{u : Site 4 | euclidNorm u ≤ 2 * (L : ℝ)},
        killedGreen (box r) 0 (u : Site 4) ^ 2) = _
    rw [tsum_subtype (f := fun u : Site 4 => killedGreen (box r) 0 u ^ 2)]
  rw [hsub]
  have hsupp : ∀ u : Site 4, u ∉ boxFinset (0 : Site 4) (2 * L) →
      {u : Site 4 | euclidNorm u ≤ 2 * (L : ℝ)}.indicator
        (fun u => killedGreen (box r) 0 u ^ 2) u = 0 := by
    intro u hu
    rw [Set.indicator_of_notMem]
    intro huT
    exact hu (by
      rw [mem_boxFinset_zero_iff]
      exact_mod_cast le_trans (supNorm_le_euclidNorm u) huT)
  rw [tsum_eq_sum (s := boxFinset (0 : Site 4) (2 * L)) hsupp]
  calc
    ∑ u ∈ boxFinset (0 : Site 4) (2 * L),
        {u : Site 4 | euclidNorm u ≤ 2 * (L : ℝ)}.indicator
          (fun u => killedGreen (box r) 0 u ^ 2) u
        ≤ ∑ u ∈ boxFinset (0 : Site 4) (2 * L),
            C0 ^ 2 * (1 / (1 + (supNorm u : ℝ)) ^ 4) := by
          apply Finset.sum_le_sum
          intro u _
          by_cases huT : u ∈ {u : Site 4 | euclidNorm u ≤ 2 * (L : ℝ)}
          · rw [Set.indicator_of_mem huT]
            exact killedGreen_sq_le r hC0pos hC0 u
          · rw [Set.indicator_of_notMem huT]
            positivity
    _ = C0 ^ 2 * ∑ u ∈ boxFinset (0 : Site 4) (2 * L),
            1 / (1 + (supNorm u : ℝ)) ^ 4 := by
          rw [Finset.mul_sum]
    _ ≤ C0 ^ 2 * (C1 * Real.log (((2 * L : ℕ) : ℝ) + 2)) :=
          mul_le_mul_of_nonneg_left (hC1 (2 * L)) (by positivity)
    _ = C0 ^ 2 * C1 * Real.log (2 * (L : ℝ) + 2) := by
          have hcast : (((2 * L : ℕ) : ℝ)) = 2 * (L : ℝ) := by push_cast; ring
          rw [hcast]
          ring
/-! ### B. The time tail -/

theorem box_eq_coe_boxFinset (r : ℕ) : box r = ↑(boxFinset (0 : Site 4) r) := by
  ext y
  simp only [box, Set.mem_setOf_eq, Finset.mem_coe, mem_boxFinset_zero_iff, supNorm_le_iff]
  constructor
  · intro h i
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h i
  · intro h i
    have h' := h i
    rw [Int.abs_eq_natAbs] at h'
    exact_mod_cast h'
theorem exists_survival_box_le_half :
    ∃ K : ℕ, 0 < K ∧ ∀ r : ℕ, 1 ≤ r → ∀ v : Site 4,
      Network.survival (lattice 4) (boxFinset (0 : Site 4) r) (K * r ^ 2) v ≤ 1 / 2 := by
  have hD : (0 : ℝ) < diagConst 4 := diagConst_pos 4
  have h162 : (0 : ℝ) < 162 * diagConst 4 := by positivity
  obtain ⟨K, hK⟩ := exists_nat_gt (Real.sqrt (162 * diagConst 4))
  have hKpos : 0 < K := by
    have hs : 0 < Real.sqrt (162 * diagConst 4) := Real.sqrt_pos.mpr h162
    exact_mod_cast (lt_trans hs hK)
  have hKsq : 162 * diagConst 4 ≤ (K : ℝ) ^ 2 := by
    have hsq : Real.sqrt (162 * diagConst 4) ^ 2 = 162 * diagConst 4 :=
      Real.sq_sqrt h162.le
    have hsnn : 0 ≤ Real.sqrt (162 * diagConst 4) := Real.sqrt_nonneg _
    nlinarith
  refine ⟨K, hKpos, fun r hr v => ?_⟩
  have hN1 : 1 ≤ K * r ^ 2 := by
    have : 0 < K * r ^ 2 := Nat.mul_pos hKpos (pow_pos hr 2)
    omega
  have hcard : ((boxFinset (0 : Site 4) r).card : ℝ) ≤ 81 * (r : ℝ) ^ 4 := by
    rw [card_boxFinset_zero]
    have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have hbase : 2 * (r : ℝ) + 1 ≤ 3 * (r : ℝ) := by linarith
    calc (((2 * r + 1) ^ 4 : ℕ) : ℝ) = (2 * (r : ℝ) + 1) ^ 4 := by push_cast; ring
      _ ≤ (3 * (r : ℝ)) ^ 4 := pow_le_pow_left₀ (by positivity) hbase 4
      _ = 81 * (r : ℝ) ^ 4 := by ring
  have hNcast : (((K * r ^ 2 : ℕ) : ℝ)) = (K : ℝ) * (r : ℝ) ^ 2 := by push_cast; ring
  rw [Network.survival]
  have hterm : ∀ u ∈ boxFinset (0 : Site 4) r,
      Graph.killedHeat (lattice 4) (↑(boxFinset (0 : Site 4) r)) (K * r ^ 2) v u
        ≤ diagConst 4 / (((K : ℝ) * (r : ℝ) ^ 2) ^ 2) := by
    intro u _
    refine (GreenTwoSided.killedHeat_le_srwHeat_sub _ _ _ _).trans ?_
    refine (srwHeat_sup_le (d := 4) (by norm_num) hN1 (v - u)).trans ?_
    have hsqrt : Real.sqrt (((K * r ^ 2 : ℕ) : ℝ)) ^ 4 = (((K * r ^ 2 : ℕ) : ℝ)) ^ 2 :=
      sqrt_pow_four _ (Nat.cast_nonneg _)
    rw [hsqrt, hNcast]
  calc ∑ u ∈ boxFinset (0 : Site 4) r,
        Graph.killedHeat (lattice 4) (↑(boxFinset (0 : Site 4) r)) (K * r ^ 2) v u
      ≤ ∑ _u ∈ boxFinset (0 : Site 4) r,
          diagConst 4 / (((K : ℝ) * (r : ℝ) ^ 2) ^ 2) := Finset.sum_le_sum hterm
    _ = ((boxFinset (0 : Site 4) r).card : ℝ)
          * (diagConst 4 / (((K : ℝ) * (r : ℝ) ^ 2) ^ 2)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (81 * (r : ℝ) ^ 4) * (diagConst 4 / (((K : ℝ) * (r : ℝ) ^ 2) ^ 2)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 81 * diagConst 4 / (K : ℝ) ^ 2 := by
        have hrne : (r : ℝ) ≠ 0 := by positivity
        have hKne : (K : ℝ) ≠ 0 := by positivity
        field_simp
    _ ≤ 1 / 2 := by
      have hK2pos : (0 : ℝ) < (K : ℝ) ^ 2 := by positivity
      rw [div_le_iff₀ hK2pos]
      nlinarith

/-- The geometric decay of the iterated half-time survival bound: `(1/2)^{k/(K r²)}`
is dominated by `2 exp(-(log 2 / K) k / r²)`. -/
private lemma half_pow_div_le_exp (K r k : ℕ) (hK : 0 < K) (hr : 1 ≤ r) :
    (1 / 2 : ℝ) ^ (k / (K * r ^ 2))
      ≤ 2 * Real.exp (-(Real.log 2 / (K : ℝ)) * (k : ℝ) / (r : ℝ) ^ 2) := by
  set j : ℕ := k / (K * r ^ 2) with hjdef
  have hNpos : 0 < K * r ^ 2 := Nat.mul_pos hK (pow_pos hr 2)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hNcast : (((K * r ^ 2 : ℕ)) : ℝ) = (K : ℝ) * (r : ℝ) ^ 2 := by push_cast; ring
  have hKne : (K : ℝ) ≠ 0 := by positivity
  have hrne : (r : ℝ) ≠ 0 := by positivity
  have hdiv : (k : ℝ) / (((K * r ^ 2 : ℕ)) : ℝ) < (j : ℝ) + 1 := by
    rw [hNcast, div_lt_iff₀ (by positivity : (0 : ℝ) < (K : ℝ) * (r : ℝ) ^ 2)]
    have hklt : k < (j + 1) * (K * r ^ 2) := by
      have : k / (K * r ^ 2) < j + 1 := by rw [← hjdef]; exact Nat.lt_succ_self j
      exact (Nat.div_lt_iff_lt_mul hNpos).mp this
    exact_mod_cast hklt
  have hexp1 : (1 / 2 : ℝ) ^ j = Real.exp (-(j : ℝ) * Real.log 2) := by
    rw [show (1 / 2 : ℝ) = Real.exp (-(Real.log 2)) by
      rw [Real.exp_neg, Real.exp_log (by norm_num), one_div]]
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hexp2 : 2 * Real.exp (-(Real.log 2 / (K : ℝ)) * (k : ℝ) / (r : ℝ) ^ 2)
      = Real.exp (Real.log 2 + (-(Real.log 2) * (k : ℝ) / (((K * r ^ 2 : ℕ)) : ℝ))) := by
    rw [← Real.exp_log (show (0 : ℝ) < 2 by norm_num), ← Real.exp_add]
    congr 1
    rw [hNcast]
    field_simp
    rw [Real.log_exp]
    ring
  rw [hexp1, hexp2]
  apply Real.exp_le_exp.mpr
  have hml : Real.log 2 * ((k : ℝ) / (((K * r ^ 2 : ℕ)) : ℝ))
      ≤ Real.log 2 * ((j : ℝ) + 1) :=
    le_of_lt (mul_lt_mul_of_pos_left hdiv hlog2)
  rw [mul_div_assoc]
  nlinarith

/-- The survival probability of the box decays exponentially in the ratio of time to
`r²`, obtained by iterating the half-time bound `exists_survival_box_le_half`. -/

private theorem survival_box_exp_le :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ, 1 ≤ r → ∀ k : ℕ, ∀ v : Site 4,
      Network.survival (lattice 4) (boxFinset (0 : Site 4) r) k v
        ≤ 2 * Real.exp (-c * (k : ℝ) / (r : ℝ) ^ 2) := by
  obtain ⟨K, hKpos, hK⟩ := exists_survival_box_le_half
  refine ⟨Real.log 2 / (K : ℝ), ?_, fun r hr k v => ?_⟩
  · have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  · set j : ℕ := k / (K * r ^ 2) with hjdef
    have hmono : Network.survival (lattice 4) (boxFinset (0 : Site 4) r) k v
        ≤ Network.survival (lattice 4) (boxFinset (0 : Site 4) r) (j * (K * r ^ 2)) v :=
      Network.survival_antitone _ (by rw [hjdef]; exact Nat.div_mul_le_self k (K * r ^ 2)) v
    have hpow : Network.survival (lattice 4) (boxFinset (0 : Site 4) r) (j * (K * r ^ 2)) v
        ≤ (1 / 2 : ℝ) ^ j := by
      have h := Network.survival_le_pow (G := lattice 4) (C := boxFinset (0 : Site 4) r)
        (N := K * r ^ 2) (θ := (1 / 2 : ℝ)) (by norm_num) (fun w => hK r hr w) j 0 v
      simpa using h
    exact hmono.trans (hpow.trans (by simpa only [hjdef] using half_pow_div_le_exp K r k hKpos hr))

/-- The exponential factor of the recent-time block is absorbed into the survival factor:
`exp(-cs m / r²) ≤ exp(cs/4) exp(-(cs/4) k / r²)` when `k ≤ 2m + 1` and `r ≥ 1`. -/

private lemma exp_shift_le (cs : ℝ) (hcs : 0 < cs) (r k m : ℕ)
    (hm : (k : ℝ) ≤ 2 * (m : ℝ) + 1) (hr : 1 ≤ r) :
    -cs * (m : ℝ) / (r : ℝ) ^ 2 ≤ -(cs / 4) * (k : ℝ) / (r : ℝ) ^ 2 + cs / 4 := by
  have hr2pos : (0 : ℝ) < (r : ℝ) ^ 2 := by positivity
  have hr2 : (1 : ℝ) ≤ (r : ℝ) ^ 2 := by
    have hr1R : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    nlinarith
  rw [div_le_iff₀ hr2pos, add_mul, div_mul_cancel₀ _ hr2pos.ne']
  nlinarith

theorem exists_killedHeat_box_le :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ r : ℕ, 1 ≤ r → ∀ k : ℕ, 1 ≤ k →
      ∀ x y : Site 4,
      Graph.killedHeat (lattice 4) (box r) k x y
        ≤ C / (k : ℝ) ^ 2 * Real.exp (-c * k / (r : ℝ) ^ 2) := by
  obtain ⟨cs, hcs, hsurv⟩ := survival_box_exp_le
  refine ⟨8 * diagConst 4 * Real.exp (cs / 4), cs / 4, ?_, ?_, ?_⟩
  · have hD := diagConst_pos 4
    positivity
  · positivity
  · intro r hr k hk x y
    rw [box_eq_coe_boxFinset]
    set m : ℕ := k / 2 with hmdef
    set n : ℕ := k - k / 2 with hndef
    have hmn : m + n = k := by omega
    have hn1 : 1 ≤ n := by omega
    have hsplit : Graph.killedHeat (lattice 4) (↑(boxFinset (0 : Site 4) r)) (m + n) x y
        ≤ Network.survival (lattice 4) (boxFinset (0 : Site 4) r) m x
            * (diagConst 4 / (n : ℝ) ^ 2) := by
      refine GreenTwoSided.killedHeat_add_le_survival_mul _ m n x y _ ?_
      intro z _
      refine (GreenTwoSided.killedHeat_le_srwHeat_sub _ n z y).trans ?_
      refine (srwHeat_sup_le (d := 4) (by norm_num) hn1 (z - y)).trans ?_
      rw [sqrt_pow_four _ (Nat.cast_nonneg _)]
    rw [hmn] at hsplit
    have hsurv' := hsurv r hr m x
    have hn2 : ((k : ℝ) ^ 2) / 4 ≤ (n : ℝ) ^ 2 := by
      have hnge : (k : ℝ) ≤ 2 * (n : ℝ) := by
        have h : k ≤ 2 * n := by omega
        exact_mod_cast h
      have hsq := mul_self_le_mul_self (show (0 : ℝ) ≤ (k : ℝ) by positivity) hnge
      nlinarith
    have hm : (k : ℝ) ≤ 2 * (m : ℝ) + 1 := by
      have h : k ≤ 2 * m + 1 := by omega
      exact_mod_cast h
    have hexp_le := exp_shift_le cs hcs r k m hm hr
    have hD := diagConst_pos 4
    calc Graph.killedHeat (lattice 4) (↑(boxFinset (0 : Site 4) r)) k x y
        ≤ Network.survival (lattice 4) (boxFinset (0 : Site 4) r) m x
            * (diagConst 4 / (n : ℝ) ^ 2) := hsplit
      _ ≤ (2 * Real.exp (-cs * (m : ℝ) / (r : ℝ) ^ 2))
            * (diagConst 4 / (n : ℝ) ^ 2) := by
          apply mul_le_mul_of_nonneg_right hsurv'
          positivity
      _ ≤ (2 * Real.exp (-cs * (m : ℝ) / (r : ℝ) ^ 2))
            * (diagConst 4 * (4 / (k : ℝ) ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have hinf : 1 / (n : ℝ) ^ 2 ≤ 4 / (k : ℝ) ^ 2 := by
            rw [div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith [hn2]
          calc diagConst 4 / (n : ℝ) ^ 2 = diagConst 4 * (1 / (n : ℝ) ^ 2) := by ring
            _ ≤ diagConst 4 * (4 / (k : ℝ) ^ 2) := mul_le_mul_of_nonneg_left hinf hD.le
      _ = 8 * diagConst 4 / (k : ℝ) ^ 2 * Real.exp (-cs * (m : ℝ) / (r : ℝ) ^ 2) := by ring
      _ ≤ 8 * diagConst 4 / (k : ℝ) ^ 2
            * (Real.exp (cs / 4) * Real.exp (-(cs / 4) * (k : ℝ) / (r : ℝ) ^ 2)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          calc Real.exp (-cs * (m : ℝ) / (r : ℝ) ^ 2)
              ≤ Real.exp (-(cs / 4) * (k : ℝ) / (r : ℝ) ^ 2 + cs / 4) :=
                Real.exp_le_exp.mpr hexp_le
            _ = Real.exp (cs / 4) * Real.exp (-(cs / 4) * (k : ℝ) / (r : ℝ) ^ 2) := by
                rw [Real.exp_add, mul_comm]
      _ = (8 * diagConst 4 * Real.exp (cs / 4)) / (k : ℝ) ^ 2
            * Real.exp (-(cs / 4) * (k : ℝ) / (r : ℝ) ^ 2) := by ring
theorem exists_survival_box_le :
    ∃ c : ℝ, 0 < c ∧ ∀ r : ℕ, 1 ≤ r → ∀ k : ℕ, ∀ v : Site 4,
      Network.survival (lattice 4) (boxFinset (0 : Site 4) r) k v
        ≤ 2 * Real.exp (-c * k / (r : ℝ) ^ 2) :=
  survival_box_exp_le

/-- The partial sums of `∑_j (j+t)^{-2}` are at most `4/t` for `t ≥ 2`. -/
private lemma sum_range_inv_sq_shift_le {t n : ℕ} (ht : 2 ≤ t) :
    ∑ j ∈ Finset.range n, 1 / ((j + t : ℕ) : ℝ) ^ 2 ≤ 4 / (t : ℝ) := by
  have hterm : ∀ j ∈ Finset.range n,
      1 / ((j + t : ℕ) : ℝ) ^ 2
        ≤ 1 / ((j + (t - 1) : ℕ) : ℝ) - 1 / (((j + 1) + (t - 1) : ℕ) : ℝ) := by
    intro j _
    have hjt : (j + 1) + (t - 1) = j + t := by omega
    have hjt' : j + (t - 1) = j + t - 1 := by omega
    rw [hjt, hjt']
    have hk : 2 ≤ j + t := by omega
    have hkpos : (0 : ℝ) < ((j + t : ℕ) : ℝ) := by positivity
    have hkm1 : (0 : ℝ) < (((j + t - 1 : ℕ)) : ℝ) := by
      have : 0 < j + t - 1 := by omega
      exact_mod_cast this
    have hcast : (((j + t - 1 : ℕ)) : ℝ) = ((j + t : ℕ) : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ j + t), Nat.cast_one]
    have hsub : 1 / (((j + t - 1 : ℕ)) : ℝ) - 1 / ((j + t : ℕ) : ℝ)
        = 1 / ((((j + t - 1 : ℕ)) : ℝ) * ((j + t : ℕ) : ℝ)) := by
      rw [div_sub_div 1 1 hkm1.ne' hkpos.ne', one_mul, mul_one, hcast]
      congr 1
      ring
    rw [hsub]
    apply one_div_le_one_div_of_le
    · positivity
    · nlinarith
  calc ∑ j ∈ Finset.range n, 1 / ((j + t : ℕ) : ℝ) ^ 2
      ≤ ∑ j ∈ Finset.range n,
          (1 / ((j + (t - 1) : ℕ) : ℝ) - 1 / (((j + 1) + (t - 1) : ℕ) : ℝ)) :=
        Finset.sum_le_sum hterm
    _ = 1 / ((0 + (t - 1) : ℕ) : ℝ) - 1 / ((n + (t - 1) : ℕ) : ℝ) :=
        Finset.sum_range_sub' (fun i => 1 / ((i + (t - 1) : ℕ) : ℝ)) n
    _ ≤ 1 / (((t - 1 : ℕ)) : ℝ) := by
        have h : (0 : ℝ) ≤ 1 / ((n + (t - 1) : ℕ) : ℝ) := by positivity
        have h0 : (0 + (t - 1) : ℕ) = t - 1 := by omega
        rw [h0]
        linarith
    _ ≤ 4 / (t : ℝ) := by
        have htm1pos : (0 : ℝ) < (((t - 1 : ℕ)) : ℝ) := by
          have : 0 < t - 1 := by omega
          exact_mod_cast this
        have htpos : (0 : ℝ) < (t : ℝ) := by positivity
        have htm1 : (((t - 1 : ℕ)) : ℝ) = (t : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ t), Nat.cast_one]
        have ht2 : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
        rw [div_le_div_iff₀ htm1pos htpos, one_mul, htm1]
        nlinarith

/-- The time tail is the tail of the summable killed-heat series from the cutoff. -/

private lemma timeTail_eq_tsum (r : ℕ) (A : ℝ) (u : Site 4) :
    timeTail r A u
      = ∑' j : ℕ, Graph.killedHeat (lattice 4) (box r)
          (j + ⌊A * (r : ℝ) ^ 2⌋₊) 0 u := by
  have hsum : Summable (fun k : ℕ => Graph.killedHeat (lattice 4) (box r) k 0 u) :=
    summable_killedHeat (box r) 0 u
  have h := hsum.sum_add_tsum_nat_add (⌊A * (r : ℝ) ^ 2⌋₊)
  unfold timeTail killedGreen killedGreenTime
  linarith

/-- The time tail is nonnegative, being the tail of a series of nonnegative terms. -/

private lemma timeTail_nonneg (r : ℕ) (A : ℝ) (u : Site 4) : 0 ≤ timeTail r A u := by
  rw [timeTail_eq_tsum]
  exact tsum_nonneg fun j => Network.killedHeat_nonneg _ _ _ _

/-- The time tail vanishes away from the box, where the killed kernel is supported. -/

private lemma timeTail_eq_zero_of_notMem {r : ℕ} (A : ℝ) {u : Site 4} (hu : u ∉ box r) :
    timeTail r A u = 0 := by
  unfold timeTail killedGreenTime
  rw [killedGreen_eq_zero_of_notMem (box r) hu]
  have h : ∑ k ∈ Finset.range ⌊A * (r : ℝ) ^ 2⌋₊,
      Graph.killedHeat (lattice 4) (box r) k 0 u = 0 :=
    Finset.sum_eq_zero fun k _ => Network.killedHeat_of_target_not_mem hu k 0
  rw [h]
  ring

theorem exists_abs_timeTail_le :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ r : ℕ, 2 ≤ r → ∀ A : ℝ, 1 ≤ A →
      ∀ u : Site 4,
      |timeTail r A u| ≤ C / (r : ℝ) ^ 2 * Real.exp (-c * A) := by
  obtain ⟨C0, c0, hC0, hc0, hK⟩ := exists_killedHeat_box_le
  refine ⟨8 * C0, c0 / 2, by positivity, by positivity, fun r hr A hA u => ?_⟩
  have hr1 : 1 ≤ r := by omega
  have hrpos : (0 : ℝ) < (r : ℝ) := by positivity
  have hr2pos : (0 : ℝ) < (r : ℝ) ^ 2 := by positivity
  have hAr : (4 : ℝ) ≤ A * (r : ℝ) ^ 2 := by
    have hA1 : (1 : ℝ) ≤ A := hA
    have hr2 : (4 : ℝ) ≤ (r : ℝ) ^ 2 := by
      have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
      nlinarith
    nlinarith
  set t : ℕ := ⌊A * (r : ℝ) ^ 2⌋₊ with htdef
  have ht_lower : A * (r : ℝ) ^ 2 / 2 ≤ (t : ℝ) := by
    have hlt : A * (r : ℝ) ^ 2 < (t : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  have ht2 : 2 ≤ t := by
    have : (2 : ℝ) ≤ (t : ℝ) := by linarith [ht_lower, hAr]
    exact_mod_cast this
  have hnonneg : 0 ≤ timeTail r A u := by
    rw [timeTail_eq_tsum, ← htdef]
    exact tsum_nonneg fun j => Network.killedHeat_nonneg _ _ _ _
  rw [abs_of_nonneg hnonneg, timeTail_eq_tsum, ← htdef]
  have htail : ∑' j : ℕ, Graph.killedHeat (lattice 4) (box r) (j + t) 0 u
      ≤ C0 * Real.exp (-c0 * (t : ℝ) / (r : ℝ) ^ 2) * (4 / (t : ℝ)) := by
    apply Real.tsum_le_of_sum_range_le
    · intro j
      exact Network.killedHeat_nonneg _ _ _ _
    · intro n
      have hterm : ∀ j ∈ Finset.range n,
          Graph.killedHeat (lattice 4) (box r) (j + t) 0 u
            ≤ C0 / (((j + t : ℕ)) : ℝ) ^ 2
                * Real.exp (-c0 * (((j + t : ℕ)) : ℝ) / (r : ℝ) ^ 2) := by
        intro j _
        exact hK r hr1 (j + t) (by omega) 0 u
      calc ∑ j ∈ Finset.range n, Graph.killedHeat (lattice 4) (box r) (j + t) 0 u
          ≤ ∑ j ∈ Finset.range n, C0 / (((j + t : ℕ)) : ℝ) ^ 2
              * Real.exp (-c0 * (((j + t : ℕ)) : ℝ) / (r : ℝ) ^ 2) :=
            Finset.sum_le_sum hterm
        _ ≤ ∑ j ∈ Finset.range n, C0 * Real.exp (-c0 * (t : ℝ) / (r : ℝ) ^ 2)
              * (1 / (((j + t : ℕ)) : ℝ) ^ 2) := by
            apply Finset.sum_le_sum
            intro j _
            have hjt : (t : ℝ) ≤ (((j + t : ℕ)) : ℝ) := by
              have : t ≤ j + t := by omega
              exact_mod_cast this
            have hexp : Real.exp (-c0 * (((j + t : ℕ)) : ℝ) / (r : ℝ) ^ 2)
                ≤ Real.exp (-c0 * (t : ℝ) / (r : ℝ) ^ 2) := by
              apply Real.exp_le_exp.mpr
              apply div_le_div_of_nonneg_right ?_ hr2pos.le
              nlinarith
            have hnum : (0 : ℝ) ≤ C0 / (((j + t : ℕ)) : ℝ) ^ 2 := by positivity
            calc C0 / (((j + t : ℕ)) : ℝ) ^ 2
                    * Real.exp (-c0 * (((j + t : ℕ)) : ℝ) / (r : ℝ) ^ 2)
                ≤ C0 / (((j + t : ℕ)) : ℝ) ^ 2
                    * Real.exp (-c0 * (t : ℝ) / (r : ℝ) ^ 2) :=
                  mul_le_mul_of_nonneg_left hexp hnum
              _ = C0 * Real.exp (-c0 * (t : ℝ) / (r : ℝ) ^ 2)
                    * (1 / (((j + t : ℕ)) : ℝ) ^ 2) := by ring
        _ = C0 * Real.exp (-c0 * (t : ℝ) / (r : ℝ) ^ 2)
              * (∑ j ∈ Finset.range n, 1 / (((j + t : ℕ)) : ℝ) ^ 2) := by
            rw [Finset.mul_sum]
        _ ≤ C0 * Real.exp (-c0 * (t : ℝ) / (r : ℝ) ^ 2) * (4 / (t : ℝ)) := by
            apply mul_le_mul_of_nonneg_left (sum_range_inv_sq_shift_le ht2)
            positivity
  refine htail.trans ?_
  have htpos : (0 : ℝ) < (t : ℝ) := by positivity
  have h4t : (4 : ℝ) / (t : ℝ) ≤ 8 / (r : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ htpos hr2pos]
    have hA1 : (1 : ℝ) ≤ A := hA
    nlinarith [ht_lower, hAr]
  have hexp2 : Real.exp (-c0 * (t : ℝ) / (r : ℝ) ^ 2) ≤ Real.exp (-(c0 / 2) * A) := by
    apply Real.exp_le_exp.mpr
    rw [div_le_iff₀ hr2pos]
    nlinarith [ht_lower]
  calc C0 * Real.exp (-c0 * (t : ℝ) / (r : ℝ) ^ 2) * (4 / (t : ℝ))
      = (C0 * (4 / (t : ℝ))) * Real.exp (-c0 * (t : ℝ) / (r : ℝ) ^ 2) := by ring
    _ ≤ (C0 * (8 / (r : ℝ) ^ 2)) * Real.exp (-(c0 / 2) * A) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left h4t hC0.le
        · exact hexp2
        · positivity
        · positivity
    _ = (8 * C0) / (r : ℝ) ^ 2 * Real.exp (-(c0 / 2) * A) := by ring

/-- The box of radius `r` carries at most `81 r⁴` sites. -/
private lemma card_boxFinset_zero_le (r : ℕ) (hr : 1 ≤ r) :
    ((boxFinset (0 : Site 4) r).card : ℝ) ≤ 81 * (r : ℝ) ^ 4 := by
  rw [card_boxFinset_zero]
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hbase : 2 * (r : ℝ) + 1 ≤ 3 * (r : ℝ) := by linarith
  calc (((2 * r + 1) ^ 4 : ℕ) : ℝ) = (2 * (r : ℝ) + 1) ^ 4 := by push_cast; ring
    _ ≤ (3 * (r : ℝ)) ^ 4 := pow_le_pow_left₀ (by positivity) hbase 4
    _ = 81 * (r : ℝ) ^ 4 := by ring

theorem exists_tsum_timeTail_le :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ r : ℕ, 2 ≤ r → ∀ A : ℝ, 1 ≤ A →
      ∑' u : Site 4, timeTail r A u ≤ C * (r : ℝ) ^ 2 * Real.exp (-c * A) := by
  obtain ⟨C0, c0, hC0, hc0, htail⟩ := exists_abs_timeTail_le
  refine ⟨81 * C0, c0, by positivity, hc0, fun r hr A hA => ?_⟩
  have hr1 : 1 ≤ r := by omega
  have hzero : ∀ u : Site 4, u ∉ boxFinset (0 : Site 4) r → timeTail r A u = 0 := by
    intro u hu
    apply timeTail_eq_zero_of_notMem A
    rw [box_eq_coe_boxFinset]
    exact fun h => hu h
  rw [tsum_eq_sum (s := boxFinset (0 : Site 4) r) hzero]
  calc ∑ u ∈ boxFinset (0 : Site 4) r, timeTail r A u
      ≤ ∑ _u ∈ boxFinset (0 : Site 4) r,
          C0 / (r : ℝ) ^ 2 * Real.exp (-c0 * A) := by
        apply Finset.sum_le_sum
        intro u _
        exact le_trans (le_abs_self _) (htail r hr A hA u)
    _ = ((boxFinset (0 : Site 4) r).card : ℝ)
          * (C0 / (r : ℝ) ^ 2 * Real.exp (-c0 * A)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (81 * (r : ℝ) ^ 4) * (C0 / (r : ℝ) ^ 2 * Real.exp (-c0 * A)) := by
        apply mul_le_mul_of_nonneg_right (card_boxFinset_zero_le r hr1)
        positivity
    _ = 81 * C0 * (r : ℝ) ^ 2 * Real.exp (-c0 * A) := by
        have hrne : (r : ℝ) ≠ 0 := by positivity
        field_simp
theorem exists_tsum_timeTail_sq_le :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ r : ℕ, 2 ≤ r → ∀ A : ℝ, 1 ≤ A →
      ∑' u : Site 4, timeTail r A u ^ 2 ≤ C * Real.exp (-c * A) := by
  obtain ⟨C1, c1, hC1, hc1, htail⟩ := exists_abs_timeTail_le
  obtain ⟨C2, c2, hC2, hc2, hsum⟩ := exists_tsum_timeTail_le
  refine ⟨C1 * C2, c1 + c2, by positivity, by positivity, fun r hr A hA => ?_⟩
  have hzero : ∀ u : Site 4, u ∉ boxFinset (0 : Site 4) r → timeTail r A u ^ 2 = 0 := by
    intro u hu
    have hu' : u ∉ box r := by
      rw [box_eq_coe_boxFinset]
      exact fun h => hu h
    rw [timeTail_eq_zero_of_notMem A hu', sq, mul_zero]
  rw [tsum_eq_sum (s := boxFinset (0 : Site 4) r) hzero]
  have hQ : ∀ u : Site 4,
      timeTail r A u ≤ C1 / (r : ℝ) ^ 2 * Real.exp (-c1 * A) := fun u =>
    le_trans (le_abs_self _) (htail r hr A hA u)
  have hQpos : (0 : ℝ) ≤ C1 / (r : ℝ) ^ 2 * Real.exp (-c1 * A) := by positivity
  have hsupp : ∑ u ∈ boxFinset (0 : Site 4) r, timeTail r A u
      = ∑' u : Site 4, timeTail r A u :=
    (tsum_eq_sum (s := boxFinset (0 : Site 4) r) (fun u hu => by
      apply timeTail_eq_zero_of_notMem
      rw [box_eq_coe_boxFinset]
      exact fun h => hu h)).symm
  calc ∑ u ∈ boxFinset (0 : Site 4) r, timeTail r A u ^ 2
      ≤ ∑ u ∈ boxFinset (0 : Site 4) r,
          (C1 / (r : ℝ) ^ 2 * Real.exp (-c1 * A)) * timeTail r A u := by
        apply Finset.sum_le_sum
        intro u _
        rw [sq]
        exact mul_le_mul_of_nonneg_right (hQ u) (timeTail_nonneg r A u)
    _ = (C1 / (r : ℝ) ^ 2 * Real.exp (-c1 * A))
          * (∑ u ∈ boxFinset (0 : Site 4) r, timeTail r A u) := by
        rw [Finset.mul_sum]
    _ = (C1 / (r : ℝ) ^ 2 * Real.exp (-c1 * A))
          * (∑' u : Site 4, timeTail r A u) := by rw [hsupp]
    _ ≤ (C1 / (r : ℝ) ^ 2 * Real.exp (-c1 * A))
          * (C2 * (r : ℝ) ^ 2 * Real.exp (-c2 * A)) := by
        apply mul_le_mul_of_nonneg_left (hsum r hr A hA) hQpos
    _ = C1 * C2 * Real.exp (-(c1 + c2) * A) := by
        have hrne : (r : ℝ) ≠ 0 := by positivity
        have hprod : (C1 / (r : ℝ) ^ 2 * Real.exp (-c1 * A))
              * (C2 * (r : ℝ) ^ 2 * Real.exp (-c2 * A))
            = C1 * C2 * (Real.exp (-c1 * A) * Real.exp (-c2 * A)) := by
          field_simp
        have hexpadd : Real.exp (-c1 * A) * Real.exp (-c2 * A)
            = Real.exp (-(c1 + c2) * A) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [hprod, hexpadd]
/-! ### C. The annular gradient and the cut-off field -/

private theorem killedHeat_lattice_symm (D : Set (Site 4)) (k : ℕ) (x y : Site 4) :
    Graph.killedHeat (lattice 4) D k x y = Graph.killedHeat (lattice 4) D k y x := by
  have h := Network.killedHeat_reversible (G := lattice 4) D k x y
  rw [Graph.Zd.degree_eq (d := 4) x, Graph.Zd.degree_eq (d := 4) y] at h
  norm_num at h
  linarith

open scoped Classical in
theorem killedHeat_succ_forward (D : Set (Site 4)) (k : ℕ) (x y : Site 4) :
    Graph.killedHeat (lattice 4) D (k + 1) x y
      = if y ∈ D then
          (∑ i : Fin 4, (Graph.killedHeat (lattice 4) D k x (y + unit i)
            + Graph.killedHeat (lattice 4) D k x (y - unit i))) / 8
        else 0 := by
  rw [killedHeat_lattice_symm D (k + 1) x y,
    Graph.Zd.killedHeat_succ_walkOp (d := 4) D k y x]
  by_cases hy : y ∈ D
  · rw [if_pos hy, if_pos hy]
    simp only [LatticeProb.walkOp, LatticeProb.nbrSum]
    rw [show (2 : ℝ) * ((4 : ℕ) : ℝ) = 8 by norm_num]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [killedHeat_lattice_symm D k (y + unit i) x,
      killedHeat_lattice_symm D k (y - unit i) x]
  · rw [if_neg hy, if_neg hy]
theorem killedGreen_eq_avg (D : Set (Site 4)) {y : Site 4} (hy : y ∈ D) (hy0 : y ≠ 0) :
    killedGreen D 0 y
      = (∑ i : Fin 4, (killedGreen D 0 (y + unit i) + killedGreen D 0 (y - unit i))) / 8 := by
  have hsum : Summable (fun k : ℕ => Graph.killedHeat (lattice 4) D k 0 y) :=
    summable_killedHeat D 0 y
  have h0 : Graph.killedHeat (lattice 4) D 0 0 y = 0 := by
    rw [Network.killedHeat_zero]
    by_cases h : (0 : Site 4) ∈ D
    · rw [if_pos h, if_neg (Ne.symm hy0)]
    · rw [if_neg h]
  have hstep : ∀ k : ℕ,
      Graph.killedHeat (lattice 4) D (k + 1) 0 y
        = (∑ i : Fin 4, (Graph.killedHeat (lattice 4) D k 0 (y + unit i)
            + Graph.killedHeat (lattice 4) D k 0 (y - unit i))) / 8 := by
    intro k
    rw [killedHeat_succ_forward D k 0 y, if_pos hy]
  have hsum_i : ∀ i : Fin 4,
      Summable (fun k : ℕ => Graph.killedHeat (lattice 4) D k 0 (y + unit i)
        + Graph.killedHeat (lattice 4) D k 0 (y - unit i)) :=
    fun i => (summable_killedHeat D 0 (y + unit i)).add
      (summable_killedHeat D 0 (y - unit i))
  have hgreen : ∀ i : Fin 4,
      (∑' k : ℕ, (Graph.killedHeat (lattice 4) D k 0 (y + unit i)
        + Graph.killedHeat (lattice 4) D k 0 (y - unit i)))
        = killedGreen D 0 (y + unit i) + killedGreen D 0 (y - unit i) := by
    intro i
    rw [Summable.tsum_add (summable_killedHeat D 0 (y + unit i))
      (summable_killedHeat D 0 (y - unit i))]
    rfl
  have htsum : (∑' k : ℕ, Graph.killedHeat (lattice 4) D (k + 1) 0 y)
      = (∑ i : Fin 4,
          (killedGreen D 0 (y + unit i) + killedGreen D 0 (y - unit i))) / 8 := by
    simp only [hstep]
    rw [tsum_div_const]
    congr 1
    rw [Summable.tsum_finsetSum (s := Finset.univ)
      (f := fun i k => Graph.killedHeat (lattice 4) D k 0 (y + unit i)
        + Graph.killedHeat (lattice 4) D k 0 (y - unit i))
      (fun i _ => hsum_i i)]
    exact Finset.sum_congr rfl fun i _ => hgreen i
  calc killedGreen D 0 y
      = ∑' k : ℕ, Graph.killedHeat (lattice 4) D k 0 y := rfl
    _ = Graph.killedHeat (lattice 4) D 0 0 y
          + ∑' k : ℕ, Graph.killedHeat (lattice 4) D (k + 1) 0 y :=
        hsum.tsum_eq_zero_add
    _ = ∑' k : ℕ, Graph.killedHeat (lattice 4) D (k + 1) 0 y := by rw [h0, zero_add]
    _ = (∑ i : Fin 4,
          (killedGreen D 0 (y + unit i) + killedGreen D 0 (y - unit i))) / 8 := htsum
private theorem supNorm_adj_le {x y : Site 4} (hxy : (lattice 4).Adj x y) :
    supNorm y ≤ supNorm x + 1 ∧ supNorm x ≤ supNorm y + 1 := by
  have hunit : ∀ i : Fin 4, supNorm (unit i) ≤ 1 := by
    intro i
    rw [supNorm_le_iff]
    intro j
    by_cases hji : j = i
    · subst j; simp [unit]
    · simp [unit, hji]
  have hplus : ∀ z : Site 4, ∀ i : Fin 4, supNorm (z + unit i) ≤ supNorm z + 1 := by
    intro z i
    exact (supNorm_add_le z (unit i)).trans (Nat.add_le_add_left (hunit i) _)
  have hminus : ∀ z : Site 4, ∀ i : Fin 4, supNorm (z - unit i) ≤ supNorm z + 1 := by
    intro z i
    calc supNorm (z - unit i) ≤ supNorm z + supNorm (-unit i) := by
          simpa only [sub_eq_add_neg] using supNorm_add_le z (-unit i)
      _ = supNorm z + supNorm (unit i) := by rw [supNorm_neg]
      _ ≤ supNorm z + 1 := Nat.add_le_add_left (hunit i) _
  have hforward : supNorm y ≤ supNorm x + 1 := by
    rcases (Graph.Zd.adj_iff.mp hxy) with ⟨i, rfl | rfl⟩
    · exact hplus x i
    · exact hminus x i
  have hback : supNorm x ≤ supNorm y + 1 := by
    rcases (Graph.Zd.adj_iff.mp hxy) with ⟨i, hy | hx⟩
    · have h := hminus y i
      rw [hy] at h
      have heq : (x + unit i) - unit i = x := by abel
      rw [heq] at h
      rw [hy]; exact h
    · have h := hplus y i
      rw [hx] at h
      have heq : (x - unit i) + unit i = x := by abel
      rw [heq] at h
      rw [hx]; exact h
  exact ⟨hforward, hback⟩

/-- The radial cutoff of the annular Caccioppoli argument: it ramps from `0` to `1` on
`[R/8, R/4]`, is `1` on `[R/4, 3R]`, and ramps back to `0` on `[3R, 4R]`. -/

private def annulusCutoff (R : ℕ) (x : Site 4) : ℝ :=
  min (max 0 (((supNorm x : ℝ) - (R : ℝ) / 8) / ((R : ℝ) / 8)))
    (max 0 (min 1 ((4 * (R : ℝ) - (supNorm x : ℝ)) / (R : ℝ))))

/-- `annulusCutoff R` vanishes on the inner region `supNorm x ≤ R/8`. -/

private theorem annulusCutoff_eq_zero_of_le {R : ℕ} (hR : 0 < R) (x : Site 4)
    (hx : (supNorm x : ℝ) ≤ (R : ℝ) / 8) : annulusCutoff R x = 0 := by
  unfold annulusCutoff
  have hq : ((supNorm x : ℝ) - (R : ℝ) / 8) / ((R : ℝ) / 8) ≤ 0 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (R : ℝ) / 8)).2
    linarith
  rw [max_eq_left hq]
  simp

/-- `annulusCutoff R` equals `1` on the plateau `R/4 ≤ supNorm x ≤ 3R`. -/

private theorem annulusCutoff_eq_one_of_mem {R : ℕ} (hR : 0 < R) (x : Site 4)
    (hx1 : (R : ℝ) / 4 ≤ (supNorm x : ℝ)) (hx2 : (supNorm x : ℝ) ≤ 3 * (R : ℝ)) :
    annulusCutoff R x = 1 := by
  unfold annulusCutoff
  have hi : 1 ≤ ((supNorm x : ℝ) - (R : ℝ) / 8) / ((R : ℝ) / 8) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (R : ℝ) / 8)).2
    linarith
  have ho : 1 ≤ (4 * (R : ℝ) - (supNorm x : ℝ)) / (R : ℝ) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (R : ℝ))).2
    linarith
  have hia : 1 ≤ max 0 (((supNorm x : ℝ) - (R : ℝ) / 8) / ((R : ℝ) / 8)) :=
    le_max_of_le_right hi
  have hob : max 0 (min 1 ((4 * (R : ℝ) - (supNorm x : ℝ)) / (R : ℝ))) = 1 := by
    rw [min_eq_left ho, max_eq_right (by norm_num)]
  rw [hob, min_eq_right hia]

/-- `annulusCutoff R` vanishes on the outer region `4R ≤ supNorm x`. -/

private theorem annulusCutoff_eq_zero_of_ge {R : ℕ} (hR : 0 < R) (x : Site 4)
    (hx : 4 * (R : ℝ) ≤ (supNorm x : ℝ)) : annulusCutoff R x = 0 := by
  unfold annulusCutoff
  have hq : (4 * (R : ℝ) - (supNorm x : ℝ)) / (R : ℝ) ≤ 0 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (R : ℝ))).2
    linarith
  have hq1 : (4 * (R : ℝ) - (supNorm x : ℝ)) / (R : ℝ) ≤ 1 := by linarith
  rw [min_eq_right hq1, max_eq_left hq]
  have hi : 0 ≤ max 0 (((supNorm x : ℝ) - (R : ℝ) / 8) / ((R : ℝ) / 8)) := le_max_left _ _
  rw [min_eq_right hi]

/-- `annulusCutoff R` is `8/R`-Lipschitz across an edge of the lattice graph. -/

private theorem annulusCutoff_lipschitz {R : ℕ} (hR : 0 < R)
    {x y : Site 4} (hxy : (lattice 4).Adj x y) :
    |annulusCutoff R x - annulusCutoff R y| ≤ 8 / (R : ℝ) := by
  have hs := supNorm_adj_le hxy
  have hdist : |(supNorm x : ℝ) - (supNorm y : ℝ)| ≤ 1 := by
    have h1 : (supNorm y : ℝ) ≤ (supNorm x : ℝ) + 1 := by exact_mod_cast hs.1
    have h2 : (supNorm x : ℝ) ≤ (supNorm y : ℝ) + 1 := by exact_mod_cast hs.2
    rw [abs_le]
    constructor <;> linarith
  have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
  have hR8ne : ((R : ℝ) / 8) ≠ 0 := by positivity
  have hRne : (R : ℝ) ≠ 0 := by positivity
  have hA : |max 0 (((supNorm x : ℝ) - (R : ℝ) / 8) / ((R : ℝ) / 8))
        - max 0 (((supNorm y : ℝ) - (R : ℝ) / 8) / ((R : ℝ) / 8))|
      ≤ (8 / (R : ℝ)) * |(supNorm x : ℝ) - (supNorm y : ℝ)| := by
    have h := abs_max_sub_max_le_max (0 : ℝ)
      (((supNorm x : ℝ) - (R : ℝ) / 8) / ((R : ℝ) / 8)) (0 : ℝ)
      (((supNorm y : ℝ) - (R : ℝ) / 8) / ((R : ℝ) / 8))
    refine h.trans ?_
    rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)]
    have heq : ((supNorm x : ℝ) - (R : ℝ) / 8) / ((R : ℝ) / 8)
        - ((supNorm y : ℝ) - (R : ℝ) / 8) / ((R : ℝ) / 8)
        = (8 / (R : ℝ)) * ((supNorm x : ℝ) - (supNorm y : ℝ)) := by
      field_simp
      ring
    rw [heq, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 8 / (R : ℝ))]
  have hB : |max 0 (min 1 ((4 * (R : ℝ) - (supNorm x : ℝ)) / (R : ℝ)))
        - max 0 (min 1 ((4 * (R : ℝ) - (supNorm y : ℝ)) / (R : ℝ)))|
      ≤ (1 / (R : ℝ)) * |(supNorm x : ℝ) - (supNorm y : ℝ)| := by
    have h := abs_max_sub_max_le_max (0 : ℝ)
      (min 1 ((4 * (R : ℝ) - (supNorm x : ℝ)) / (R : ℝ))) (0 : ℝ)
      (min 1 ((4 * (R : ℝ) - (supNorm y : ℝ)) / (R : ℝ)))
    refine h.trans ?_
    rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)]
    have h2 := abs_min_sub_min_le_max (1 : ℝ)
      ((4 * (R : ℝ) - (supNorm x : ℝ)) / (R : ℝ)) (1 : ℝ)
      ((4 * (R : ℝ) - (supNorm y : ℝ)) / (R : ℝ))
    refine h2.trans ?_
    rw [sub_self, abs_zero, max_eq_right (abs_nonneg _)]
    have heq : (4 * (R : ℝ) - (supNorm x : ℝ)) / (R : ℝ)
        - (4 * (R : ℝ) - (supNorm y : ℝ)) / (R : ℝ)
        = (1 / (R : ℝ)) * ((supNorm y : ℝ) - (supNorm x : ℝ)) := by
      field_simp
      ring
    rw [heq, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (R : ℝ)), abs_sub_comm]
  have hcut : |annulusCutoff R x - annulusCutoff R y|
      ≤ max |max 0 (((supNorm x : ℝ) - (R : ℝ) / 8) / ((R : ℝ) / 8))
              - max 0 (((supNorm y : ℝ) - (R : ℝ) / 8) / ((R : ℝ) / 8))|
            |max 0 (min 1 ((4 * (R : ℝ) - (supNorm x : ℝ)) / (R : ℝ)))
              - max 0 (min 1 ((4 * (R : ℝ) - (supNorm y : ℝ)) / (R : ℝ)))| := by
    simpa only [annulusCutoff] using
      abs_min_sub_min_le_max
        (max 0 (((supNorm x : ℝ) - (R : ℝ) / 8) / ((R : ℝ) / 8)))
        (max 0 (min 1 ((4 * (R : ℝ) - (supNorm x : ℝ)) / (R : ℝ))))
        (max 0 (((supNorm y : ℝ) - (R : ℝ) / 8) / ((R : ℝ) / 8)))
        (max 0 (min 1 ((4 * (R : ℝ) - (supNorm y : ℝ)) / (R : ℝ))))
  refine hcut.trans ?_
  apply max_le
  · refine hA.trans ?_
    calc (8 / (R : ℝ)) * |(supNorm x : ℝ) - (supNorm y : ℝ)|
        ≤ (8 / (R : ℝ)) * 1 := mul_le_mul_of_nonneg_left hdist (by positivity)
      _ = 8 / (R : ℝ) := by ring
  · refine hB.trans ?_
    calc (1 / (R : ℝ)) * |(supNorm x : ℝ) - (supNorm y : ℝ)|
        ≤ (8 / (R : ℝ)) * |(supNorm x : ℝ) - (supNorm y : ℝ)| :=
          mul_le_mul_of_nonneg_right (by
            apply div_le_div_of_nonneg_right <;> norm_num) (abs_nonneg _)
      _ ≤ (8 / (R : ℝ)) * 1 := mul_le_mul_of_nonneg_left hdist (by positivity)
      _ = 8 / (R : ℝ) := by ring

/-- A discrete Caccioppoli inequality on a conductance network: if `f` is harmonic on `B`
and the test function `f * η²` vanishes outside `B`, the `η`-weighted Dirichlet energy of `f`
is controlled by the `f²`-weighted gradient energy of `η`. -/

private theorem caccioppoli_of_support {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
    {c : V → V → ℝ} (hc : Network.IsCond G c)
    (S B : Finset V) (f η : V → ℝ)
    (hf : ∀ x ∈ B, Network.netLaplacian G c f x = 0)
    (htest : ∀ x, x ∉ B → f x * η x ^ 2 = 0) (hBS : B ⊆ S)
    (hnb : ∀ x ∈ B, ∀ y, G.Adj x y → y ∈ S) :
    ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
        c x y * (f x - f y) ^ 2 * η x ^ 2 ≤
      4 * ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
        c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2 := by
  have hform := Network.formOn_eq_neg_two_mul hc S B f
    (fun x => f x * η x ^ 2) htest hBS hnb
  have hharm : ∑ x ∈ B, f x * η x ^ 2 * Network.netLaplacian G c f x = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [hf x hx]
    ring
  rw [hharm, mul_zero] at hform
  have hpt : ∀ x ∈ S, ∀ y ∈ G.neighborFinset x,
      c x y * (f x - f y) ^ 2 * η x ^ 2 ≤
        2 * (c x y * (f x - f y) * (f x * η x ^ 2 - f y * η y ^ 2)) +
          4 * (c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2) := by
    intro x _ y _
    have hc0 := hc.nonneg x y
    nlinarith [Network.caccioppoli_pointwise (f x) (f y) (η x) (η y),
      mul_nonneg hc0 (sq_nonneg (f x - f y)), mul_nonneg hc0 (sq_nonneg (η x - η y))]
  calc ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
        c x y * (f x - f y) ^ 2 * η x ^ 2
      ≤ ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
          (2 * (c x y * (f x - f y) * (f x * η x ^ 2 - f y * η y ^ 2)) +
            4 * (c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2)) :=
        Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => hpt x hx y hy
    _ = 2 * Network.formOn G c S f (fun x => f x * η x ^ 2) +
          4 * ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
            c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2 := by
      have h1 : (∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
            2 * (c x y * (f x - f y) * (f x * η x ^ 2 - f y * η y ^ 2))) =
          2 * Network.formOn G c S f (fun x => f x * η x ^ 2) := by
        simp only [Network.formOn, Finset.mul_sum]
      have h2 : (∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
            4 * (c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2)) =
          4 * ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
            c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2 := by
        simp only [Finset.mul_sum]
      rw [show (∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
            (2 * (c x y * (f x - f y) * (f x * η x ^ 2 - f y * η y ^ 2)) +
              4 * (c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2))) =
          (∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
            2 * (c x y * (f x - f y) * (f x * η x ^ 2 - f y * η y ^ 2))) +
            ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
              4 * (c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2) from by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun x _ => Finset.sum_add_distrib]
      rw [h1, h2]
    _ = 4 * ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
          c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2 := by
      rw [hform]
      ring

/-- The killed Green function `x ↦ killedGreen (box r) 0 x` is harmonic at every
point of the box except the source `0`. -/

private theorem killedGreen_netLaplacian_eq_zero (r : ℕ) {y : Site 4}
    (hy : y ∈ box r) (hy0 : y ≠ 0) :
    Network.netLaplacian (lattice 4) (Network.unitCond (lattice 4))
      (fun x => killedGreen (box r) 0 x) y = 0 := by
  rw [Network.netLaplacian_unitCond,
    Graph.laplacian_eq_zero_iff_walkOp (fun x => killedGreen (box r) 0 x)
      (by rw [Graph.Zd.degree_eq]; norm_num)]
  rw [Graph.Zd.walkOp_eq, LatticeProb.walkOp, LatticeProb.nbrSum,
    killedGreen_eq_avg (box r) hy hy0]
  norm_num

theorem exists_annulus_gradient_le :
    ∃ C : ℝ, 0 < C ∧ ∀ r R : ℕ, 1 ≤ R → ∀ i : Fin 4,
      ∑' u : {u : Site 4 // (R : ℝ) ≤ euclidNorm u ∧ euclidNorm u ≤ 2 * (R : ℝ)},
          (killedGreen (box r) 0 ((u : Site 4) + unit i) - killedGreen (box r) 0 (u : Site 4)) ^ 2
        ≤ C / (R : ℝ) ^ 2 := by
  classical
  obtain ⟨C₀, hC₀, hfree⟩ := exists_srwGreenInf_four_le
  let C : ℝ := C₀ ^ 2 * (2 ^ 40 * 11 ^ 4 + 4 * 63 ^ 4 * 256)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro r R hR i
  have hbound : ∀ z : Site 4, 0 ≤ killedGreen (box r) 0 z ∧
      killedGreen (box r) 0 z ≤ C₀ / (1 + euclidNorm z) ^ 2 := by
    intro z
    exact ⟨killedGreen_nonneg (box r) 0 z,
      (killedGreen_le_srwGreenInf (box r) z).trans (hfree z)⟩
  by_cases hRbig : 16 ≤ R
  · have hRbig' : (16 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hRbig
    have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast (show 0 < R by omega)
    let G := lattice 4
    let Cfin : Finset (Site 4) := boxFinset (0 : Site 4) r
    let S : Finset (Site 4) := boxFinset (0 : Site 4) (4 * R + 1)
    let B : Finset (Site 4) :=
      (boxFinset (0 : Site 4) (4 * R)).filter
        (fun x => x ∈ Cfin ∧ (R : ℝ) / 8 < (supNorm x : ℝ))
    let f : Site 4 → ℝ := fun x => killedGreen (box r) 0 x
    let eta : Site 4 → ℝ := annulusCutoff R
    have hf : ∀ x ∈ B, Network.netLaplacian G (Network.unitCond G) f x = 0 := by
      intro x hx
      have hxB := Finset.mem_filter.mp hx
      have hxCfin : x ∈ Cfin := hxB.2.1
      have hxr : x ∈ box r := by
        rw [box_eq_coe_boxFinset]
        simpa [Cfin] using hxCfin
      have hx0 : x ≠ 0 := by
        intro hzero
        have hbad := hxB.2.2
        rw [hzero] at hbad
        simp [supNorm] at hbad
        have hpos : (0 : ℝ) < (R : ℝ) / 8 := by positivity
        linarith
      exact killedGreen_netLaplacian_eq_zero r hxr hx0
    have htest : ∀ x, x ∉ B → f x * eta x ^ 2 = 0 := by
      intro x hx
      by_cases hxCfin : x ∈ Cfin
      · by_cases hxbox : x ∈ boxFinset (0 : Site 4) (4 * R)
        · have hinner : ¬ (R : ℝ) / 8 < (supNorm x : ℝ) := by
            intro hinner
            exact hx (Finset.mem_filter.mpr ⟨hxbox, hxCfin, hinner⟩)
          have hη := annulusCutoff_eq_zero_of_le (R := R) (by omega) x (le_of_not_gt hinner)
          simp [f, eta, hη]
        · have hsup : 4 * R < supNorm x := by
            by_contra hnot
            apply hxbox
            rw [mem_boxFinset_zero_iff]
            exact le_of_not_gt hnot
          have hsup' : 4 * (R : ℝ) ≤ (supNorm x : ℝ) := by exact_mod_cast (Nat.le_of_lt hsup)
          have hη := annulusCutoff_eq_zero_of_ge (R := R) (by omega) x hsup'
          simp [f, eta, hη]
      · have hxr : x ∉ box r := by
          intro hxr
          apply hxCfin
          rw [box_eq_coe_boxFinset] at hxr
          simpa [Cfin] using hxr
        have hzero := killedGreen_eq_zero_of_notMem (box r) hxr
        simp [f, hzero]
    have hBS : B ⊆ S := by
      intro x hx
      have hxbox := (Finset.mem_filter.mp hx).1
      have hsup := (mem_boxFinset_zero_iff.mp hxbox)
      rw [mem_boxFinset_zero_iff]
      exact hsup.trans (by omega)
    have hnb : ∀ x ∈ B, ∀ y, G.Adj x y → y ∈ S := by
      intro x hx y hxy
      have hxbox := (Finset.mem_filter.mp hx).1
      have hsupx := (mem_boxFinset_zero_iff.mp hxbox)
      have hsupy := (supNorm_adj_le hxy).1
      rw [mem_boxFinset_zero_iff]
      omega
    have henergy := caccioppoli_of_support (G := G) (c := Network.unitCond G)
      Network.isCond_unitCond S B f eta hf htest hBS hnb
    have hsup_le_norm : ∀ z : Site 4, (supNorm z : ℝ) ≤ euclidNorm z :=
      fun z => supNorm_le_euclidNorm z
    have hnorm_le_sup : ∀ z : Site 4, euclidNorm z ≤ 2 * (supNorm z : ℝ) := by
      intro z
      have h := euclidNorm_le_sqrt_mul_supNorm (d := 4) z
      have h4 : Real.sqrt ((4 : ℕ) : ℝ) = 2 := by norm_num
      rwa [h4] at h
    have heta_one : ∀ z : Site 4,
        (R : ℝ) ≤ euclidNorm z → euclidNorm z ≤ 2 * (R : ℝ) → eta z = 1 := by
      intro z hz1 hz2
      have hlow : (R : ℝ) / 4 ≤ (supNorm z : ℝ) := by
        have := hnorm_le_sup z
        linarith
      have hupp : (supNorm z : ℝ) ≤ 3 * (R : ℝ) :=
        (hsup_le_norm z).trans hz2 |>.trans (by linarith)
      exact annulusCutoff_eq_one_of_mem (R := R) (by omega) z hlow hupp
    have hadj : ∀ u : Site 4, G.Adj u (u + unit i) := by
      intro u
      dsimp [G]
      exact Graph.Zd.adj_iff.mpr ⟨i, Or.inl rfl⟩
    let A : Set (Site 4) := {u | (R : ℝ) ≤ euclidNorm u ∧ euclidNorm u ≤ 2 * (R : ℝ)}
    change (∑' u : A, (killedGreen (box r) 0 ((u : Site 4) + unit i)
        - killedGreen (box r) 0 (u : Site 4)) ^ 2) ≤ C / (R : ℝ) ^ 2
    rw [tsum_subtype A (fun u : Site 4 =>
      (killedGreen (box r) 0 (u + unit i) - killedGreen (box r) 0 u) ^ 2)]
    have hzero : ∀ u : Site 4, u ∉ S →
        A.indicator (fun u : Site 4 =>
          (killedGreen (box r) 0 (u + unit i) - killedGreen (box r) 0 u) ^ 2) u = 0 := by
      intro u hu
      have huA : u ∉ A := by
        intro huA
        have hsup : (supNorm u : ℝ) ≤ 2 * (R : ℝ) := (hsup_le_norm u).trans huA.2
        have hsup' : supNorm u ≤ 2 * R := by exact_mod_cast hsup
        apply hu
        rw [mem_boxFinset_zero_iff]
        exact hsup'.trans (by omega)
      rw [Set.indicator_of_notMem huA]
    rw [tsum_eq_sum (s := S) hzero]
    have hrow : ∀ u : Site 4, u ∈ S →
        A.indicator (fun u : Site 4 =>
          (killedGreen (box r) 0 (u + unit i) - killedGreen (box r) 0 u) ^ 2) u ≤
        ∑ y ∈ G.neighborFinset u,
          Network.unitCond G u y * (f u - f y) ^ 2 * eta u ^ 2 := by
      intro u hu
      have hrow_nonneg : 0 ≤ ∑ y ∈ G.neighborFinset u,
          Network.unitCond G u y * (f u - f y) ^ 2 * eta u ^ 2 := by
        apply Finset.sum_nonneg
        intro y hy
        exact mul_nonneg
          (mul_nonneg (Network.isCond_unitCond.nonneg u y) (sq_nonneg _)) (sq_nonneg _)
      by_cases huA : u ∈ A
      · have huone := heta_one u huA.1 huA.2
        have hsingle : Network.unitCond G u (u + unit i) *
            (f u - f (u + unit i)) ^ 2 * eta u ^ 2 ≤
            ∑ y ∈ G.neighborFinset u,
              Network.unitCond G u y * (f u - f y) ^ 2 * eta u ^ 2 :=
          Finset.single_le_sum
            (f := fun y => Network.unitCond G u y * (f u - f y) ^ 2 * eta u ^ 2)
            (fun y hy => mul_nonneg
              (mul_nonneg (Network.isCond_unitCond.nonneg u y) (sq_nonneg _))
              (sq_nonneg _))
            (SimpleGraph.mem_neighborFinset _ _ _ |>.mpr (hadj u))
        rw [Set.indicator_of_mem huA]
        calc (killedGreen (box r) 0 (u + unit i) - killedGreen (box r) 0 u) ^ 2
            = (f u - f (u + unit i)) ^ 2 := by simp [f]; ring
          _ ≤ ∑ y ∈ G.neighborFinset u,
              Network.unitCond G u y * (f u - f y) ^ 2 * eta u ^ 2 := by
              have hc : Network.unitCond G u (u + unit i) = 1 :=
                by simp [Network.unitCond, hadj u]
              simpa [huone, hc] using hsingle
      · rw [Set.indicator_of_notMem huA]
        exact hrow_nonneg
    have hcompare : (∑ u ∈ S,
        A.indicator (fun u : Site 4 =>
          (killedGreen (box r) 0 (u + unit i) - killedGreen (box r) 0 u) ^ 2) u) ≤
        ∑ u ∈ S, ∑ y ∈ G.neighborFinset u,
          Network.unitCond G u y * (f u - f y) ^ 2 * eta u ^ 2 :=
      Finset.sum_le_sum hrow
    have htarget : (∑ u ∈ S,
        A.indicator (fun u : Site 4 =>
          (killedGreen (box r) 0 (u + unit i) - killedGreen (box r) 0 u) ^ 2) u) ≤
        4 * ∑ u ∈ S, ∑ y ∈ G.neighborFinset u,
          Network.unitCond G u y * (f u ^ 2 + f y ^ 2) * (eta u - eta y) ^ 2 :=
      hcompare.trans henergy
    let A₀ : ℝ := (C₀ / ((R : ℝ) / 16) ^ 2) ^ 2
    have hK_sq : ∀ z : Site 4, (R : ℝ) / 16 ≤ euclidNorm z → f z ^ 2 ≤ A₀ := by
      intro z hz
      have hpoint := hbound z
      have hden : (R : ℝ) / 16 ≤ 1 + euclidNorm z :=
        by linarith [show (0 : ℝ) ≤ 1 by norm_num]
      have hdenpow : ((R : ℝ) / 16) ^ 2 ≤ (1 + euclidNorm z) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hden 2
      have hb : f z ≤ C₀ / ((R : ℝ) / 16) ^ 2 :=
        hpoint.2.trans (div_le_div_of_nonneg_left hC₀.le (by positivity) hdenpow)
      have hfnonneg : 0 ≤ f z := hpoint.1
      have hright : 0 ≤ C₀ / ((R : ℝ) / 16) ^ 2 := by positivity
      dsimp [A₀]
      exact (sq_le_sq₀ hfnonneg hright).mpr hb
    have hterm_energy : ∀ x : Site 4, x ∈ S →
        ∀ y, y ∈ G.neighborFinset x →
          Network.unitCond G x y * (f x ^ 2 + f y ^ 2) * (eta x - eta y) ^ 2 ≤
            2 * A₀ * (8 / (R : ℝ)) ^ 2 := by
      intro x hx y hy
      have hxy : G.Adj x y := (SimpleGraph.mem_neighborFinset _ _ _).mp hy
      have hcond : Network.unitCond G x y = 1 := by simp [Network.unitCond, hxy]
      by_cases heq : eta x = eta y
      · simp [heq, hcond]
        dsimp [A₀]
        positivity
      · have hη := annulusCutoff_lipschitz (R := R) (by omega) hxy
        have hηsq : (eta x - eta y) ^ 2 ≤ (8 / (R : ℝ)) ^ 2 := by
          have habs : |eta x - eta y| ≤ 8 / (R : ℝ) := by simpa [eta] using hη
          have habs_sq := (sq_le_sq₀ (abs_nonneg (eta x - eta y))
            (by positivity : (0 : ℝ) ≤ 8 / (R : ℝ))).mpr habs
          simpa [sq_abs] using habs_sq
        have hnonzero : eta x ≠ 0 ∨ eta y ≠ 0 := by
          by_cases hx0 : eta x = 0
          · by_cases hy0 : eta y = 0
            · exact False.elim (heq (by rw [hx0, hy0]))
            · exact Or.inr hy0
          · exact Or.inl hx0
        have hnormx : (R : ℝ) / 16 ≤ euclidNorm x := by
          rcases hnonzero with hxη | hyη
          · have hsup : (R : ℝ) / 8 < (supNorm x : ℝ) := by
              by_contra hnot
              have hz := annulusCutoff_eq_zero_of_le (R := R) (by omega) x
                (le_of_not_gt hnot)
              exact hxη (by simpa [eta] using hz)
            have := hsup_le_norm x
            linarith
          · have hsupy : (R : ℝ) / 8 < (supNorm y : ℝ) := by
              by_contra hnot
              have hz := annulusCutoff_eq_zero_of_le (R := R) (by omega) y
                (le_of_not_gt hnot)
              exact hyη (by simpa [eta] using hz)
            have hsupxy : (supNorm y : ℝ) ≤ (supNorm x : ℝ) + 1 :=
              by exact_mod_cast (supNorm_adj_le hxy).1
            have hsupx : (R : ℝ) / 8 - 1 < (supNorm x : ℝ) := by linarith
            have := hsup_le_norm x
            linarith
        have hnormy : (R : ℝ) / 16 ≤ euclidNorm y := by
          rcases hnonzero with hxη | hyη
          · have hsupx : (R : ℝ) / 8 < (supNorm x : ℝ) := by
              by_contra hnot
              have hz := annulusCutoff_eq_zero_of_le (R := R) (by omega) x
                (le_of_not_gt hnot)
              exact hxη (by simpa [eta] using hz)
            have hsupxy : (supNorm x : ℝ) ≤ (supNorm y : ℝ) + 1 :=
              by exact_mod_cast (supNorm_adj_le hxy).2
            have hsupy : (R : ℝ) / 8 - 1 < (supNorm y : ℝ) := by linarith
            have := hsup_le_norm y
            linarith
          · have hsup : (R : ℝ) / 8 < (supNorm y : ℝ) := by
              by_contra hnot
              have hz := annulusCutoff_eq_zero_of_le (R := R) (by omega) y
                (le_of_not_gt hnot)
              exact hyη (by simpa [eta] using hz)
            have := hsup_le_norm y
            linarith
        have hfx := hK_sq x hnormx
        have hfy := hK_sq y hnormy
        have hsumf : f x ^ 2 + f y ^ 2 ≤ 2 * A₀ := by linarith
        rw [hcond]
        calc 1 * (f x ^ 2 + f y ^ 2) * (eta x - eta y) ^ 2
            ≤ (2 * A₀) * (eta x - eta y) ^ 2 :=
              mul_le_mul_of_nonneg_right (by simpa using hsumf) (sq_nonneg _)
          _ ≤ (2 * A₀) * (8 / (R : ℝ)) ^ 2 :=
              mul_le_mul_of_nonneg_left hηsq (by positivity)
    let M : ℝ := 2 * A₀ * (8 / (R : ℝ)) ^ 2
    have henergy_bound :
        (∑ u ∈ S, ∑ y ∈ G.neighborFinset u,
          Network.unitCond G u y * (f u ^ 2 + f y ^ 2) * (eta u - eta y) ^ 2) ≤
          (S.card : ℝ) * 8 * M := by
      calc _ ≤ ∑ u ∈ S, ∑ y ∈ G.neighborFinset u, M := by
            apply Finset.sum_le_sum
            intro u hu
            apply Finset.sum_le_sum
            intro y hy
            exact hterm_energy u hu y hy
        _ = (S.card : ℝ) * 8 * M := by
            calc (∑ u ∈ S, ∑ y ∈ G.neighborFinset u, M)
                = ∑ u ∈ S, ((G.neighborFinset u).card : ℝ) * M := by
                  apply Finset.sum_congr rfl
                  intro u hu
                  rw [Finset.sum_const, nsmul_eq_mul]
              _ = (S.card : ℝ) * 8 * M := by
                  have hdeg : ∀ u : Site 4, (G.neighborFinset u).card = 8 := by
                    intro u
                    dsimp [G]
                    norm_num [Graph.Zd.degree_eq]
                  simp [hdeg, Finset.sum_const, nsmul_eq_mul]
                  ring
    have hcardS : (S.card : ℝ) ≤ (11 * (R : ℝ)) ^ 4 := by
      dsimp [S]
      rw [card_boxFinset_zero]
      push_cast
      have hbase : 2 * (4 * (R : ℝ) + 1) + 1 ≤ 11 * (R : ℝ) := by
        have hRone : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast (show 1 ≤ R by omega)
        linarith
      exact pow_le_pow_left₀ (by positivity) hbase 4
    have hM : 0 ≤ M := by dsimp [M, A₀]; positivity
    have hcount : 4 * ((S.card : ℝ) * 8 * M) ≤ 4 * ((11 * (R : ℝ)) ^ 4 * 8 * M) := by
      have hcard8 : (S.card : ℝ) * 8 ≤ (11 * (R : ℝ)) ^ 4 * 8 :=
        mul_le_mul_of_nonneg_right hcardS (by norm_num)
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard8 hM) (by norm_num)
    have hscale : 4 * ((11 * (R : ℝ)) ^ 4 * 8 * M) ≤ C / (R : ℝ) ^ 2 := by
      have heq : 4 * ((11 * (R : ℝ)) ^ 4 * 8 * M)
          = C₀ ^ 2 * ((2 : ℝ) ^ 28 * 11 ^ 4) / (R : ℝ) ^ 2 := by
        dsimp [M, A₀]
        field_simp [ne_of_gt hRpos]
        ring
      rw [heq]
      apply (div_le_div_iff_of_pos_right (by positivity : (0 : ℝ) < (R : ℝ) ^ 2)).2
      have hcoef : C₀ ^ 2 * ((2 : ℝ) ^ 28 * 11 ^ 4)
          ≤ C₀ ^ 2 * ((2 : ℝ) ^ 40 * 11 ^ 4) := by
        gcongr <;> norm_num
      have hCbig : C₀ ^ 2 * ((2 : ℝ) ^ 40 * 11 ^ 4) ≤ C := by
        dsimp [C]
        nlinarith [sq_nonneg C₀]
      exact hcoef.trans hCbig
    exact htarget.trans ((mul_le_mul_of_nonneg_left henergy_bound (by norm_num)).trans
      (hcount.trans hscale))
  · have hRle : R ≤ 15 := by omega
    have hRpos : (0 : ℝ) < (R : ℝ) := by exact_mod_cast (show 0 < R by omega)
    let A : Set (Site 4) := {u | (R : ℝ) ≤ euclidNorm u ∧ euclidNorm u ≤ 2 * (R : ℝ)}
    change (∑' u : A, (killedGreen (box r) 0 ((u : Site 4) + unit i)
        - killedGreen (box r) 0 (u : Site 4)) ^ 2) ≤ C / (R : ℝ) ^ 2
    rw [tsum_subtype A (fun u : Site 4 =>
      (killedGreen (box r) 0 (u + unit i) - killedGreen (box r) 0 u) ^ 2)]
    let T : Finset (Site 4) := boxFinset (0 : Site 4) (2 * R + 1)
    have hzero : ∀ u : Site 4, u ∉ T →
        A.indicator (fun u : Site 4 =>
          (killedGreen (box r) 0 (u + unit i) - killedGreen (box r) 0 u) ^ 2) u = 0 := by
      intro u hu
      have huA : u ∉ A := by
        intro huA
        have hsup : (supNorm u : ℝ) ≤ 2 * (R : ℝ) := (supNorm_le_euclidNorm u).trans huA.2
        have hsup' : supNorm u ≤ 2 * R := by exact_mod_cast hsup
        apply hu
        rw [mem_boxFinset_zero_iff]
        exact hsup'.trans (by omega)
      rw [Set.indicator_of_notMem huA]
    rw [tsum_eq_sum (s := T) hzero]
    have hterm : ∀ u : Site 4, u ∈ T →
        A.indicator (fun u : Site 4 =>
          (killedGreen (box r) 0 (u + unit i) - killedGreen (box r) 0 u) ^ 2) u ≤
        4 * C₀ ^ 2 := by
      intro u hu
      by_cases huA : u ∈ A
      · rw [Set.indicator_of_mem huA]
        have huC := (hbound u).2
        have huvC := (hbound (u + unit i)).2
        have huB : killedGreen (box r) 0 u ≤ C₀ := by
          have hden : (1 : ℝ) ≤ (1 + euclidNorm u) ^ 2 :=
            by nlinarith [euclidNorm_nonneg u]
          have hq : C₀ / (1 + euclidNorm u) ^ 2 ≤ C₀ := by
            apply (div_le_iff₀ (by positivity : (0 : ℝ) < (1 + euclidNorm u) ^ 2)).2
            nlinarith [hC₀.le, hden]
          exact huC.trans hq
        have huvB : killedGreen (box r) 0 (u + unit i) ≤ C₀ := by
          have hden : (1 : ℝ) ≤ (1 + euclidNorm (u + unit i)) ^ 2 :=
            by nlinarith [euclidNorm_nonneg (u + unit i)]
          have hq : C₀ / (1 + euclidNorm (u + unit i)) ^ 2 ≤ C₀ := by
            apply (div_le_iff₀ (by positivity : (0 : ℝ) < (1 + euclidNorm (u + unit i)) ^ 2)).2
            nlinarith [hC₀.le, hden]
          exact huvC.trans hq
        have hu0 : 0 ≤ killedGreen (box r) 0 u := killedGreen_nonneg (box r) 0 u
        have huv0 : 0 ≤ killedGreen (box r) 0 (u + unit i) :=
          killedGreen_nonneg (box r) 0 (u + unit i)
        nlinarith [sq_nonneg (killedGreen (box r) 0 (u + unit i) - killedGreen (box r) 0 u)]
      · rw [Set.indicator_of_notMem huA]
        positivity
    have hsum : (∑ u ∈ T,
        A.indicator (fun u : Site 4 =>
          (killedGreen (box r) 0 (u + unit i) - killedGreen (box r) 0 u) ^ 2) u) ≤
        4 * C₀ ^ 2 * (T.card : ℝ) := by
      calc _ ≤ ∑ u ∈ T, (4 * C₀ ^ 2) := Finset.sum_le_sum hterm
        _ = 4 * C₀ ^ 2 * (T.card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            ring
    have hcard : (T.card : ℝ) ≤ 63 ^ 4 := by
      dsimp [T]
      rw [card_boxFinset_zero]
      have hnat : 2 * (2 * R + 1) + 1 ≤ 63 := by omega
      have hcast : (2 * (2 * R + 1) + 1 : ℝ) ≤ 63 := by exact_mod_cast hnat
      push_cast
      exact pow_le_pow_left₀ (by positivity) hcast 4
    have hmain : 4 * C₀ ^ 2 * (T.card : ℝ) ≤ C / (R : ℝ) ^ 2 := by
      have hR2 : (R : ℝ) ^ 2 ≤ 256 := by
        have : (R : ℝ) ≤ 15 := by exact_mod_cast hRle
        nlinarith
      have hprod : (4 * C₀ ^ 2 * (63 : ℝ) ^ 4) * (R : ℝ) ^ 2 ≤ C := by
        calc (4 * C₀ ^ 2 * (63 : ℝ) ^ 4) * (R : ℝ) ^ 2
              ≤ 4 * C₀ ^ 2 * (63 : ℝ) ^ 4 * 256 := by gcongr
          _ ≤ C := by dsimp [C]; nlinarith [sq_nonneg C₀]
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < (R : ℝ) ^ 2)).2
      calc 4 * C₀ ^ 2 * (T.card : ℝ) * (R : ℝ) ^ 2
            ≤ (4 * C₀ ^ 2 * (63 : ℝ) ^ 4) * (R : ℝ) ^ 2 := by gcongr
        _ ≤ C := hprod
    exact hsum.trans hmain
theorem exists_abs_cutField_le :
    ∃ C : ℝ, 0 < C ∧ ∀ r L : ℕ, 2 ≤ L → ∀ φ : ℝ → ℝ, IsCutoff φ →
      ∀ u : Site 4,
      |cutField r L φ u| ≤ C / (L : ℝ) ^ 2 := by
  obtain ⟨C0, hC0pos, hC0⟩ := exists_srwGreenInf_four_le
  refine ⟨C0, hC0pos, fun r L hL φ hφ u => ?_⟩
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
  have hgnn : 0 ≤ killedGreen (box r) 0 u := killedGreen_nonneg (box r) 0 u
  have hgle : killedGreen (box r) 0 u ≤ C0 / (1 + euclidNorm u) ^ 2 :=
    le_trans (killedGreen_le_srwGreenInf (box r) u) (hC0 u)
  have harg : 0 ≤ euclidNorm u / (L : ℝ) := div_nonneg (euclidNorm_nonneg u) hLpos.le
  have hφnn : 0 ≤ φ (euclidNorm u / (L : ℝ)) := (hφ.1 _ harg).1
  have hφle : φ (euclidNorm u / (L : ℝ)) ≤ 1 := (hφ.1 _ harg).2
  rw [cutField, abs_mul, abs_of_nonneg hgnn, abs_of_nonneg hφnn]
  by_cases h : euclidNorm u ≤ (L : ℝ)
  · have hle1 : euclidNorm u / (L : ℝ) ≤ 1 := (div_le_one hLpos).mpr h
    have hzero : φ (euclidNorm u / (L : ℝ)) = 0 := hφ.2.2.1 _ harg hle1
    rw [hzero, mul_zero]
    exact div_nonneg hC0pos.le (by positivity)
  · have hgt : (L : ℝ) < euclidNorm u := lt_of_not_ge h
    have hden : (L : ℝ) ^ 2 ≤ (1 + euclidNorm u) ^ 2 := by
      have h1 : (L : ℝ) ≤ 1 + euclidNorm u := by linarith
      exact pow_le_pow_left₀ hLpos.le h1 2
    calc killedGreen (box r) 0 u * φ (euclidNorm u / (L : ℝ))
        ≤ killedGreen (box r) 0 u * 1 := mul_le_mul_of_nonneg_left hφle hgnn
      _ = killedGreen (box r) 0 u := mul_one _
      _ ≤ C0 / (1 + euclidNorm u) ^ 2 := hgle
      _ ≤ C0 / (L : ℝ) ^ 2 := div_le_div_of_nonneg_left hC0pos.le (by positivity) hden

/-- The tail of the inverse-square series: `∑_{m ≤ k < n} 1/(k+1)³ ≤ 2/m²`. -/
private theorem sum_Ico_inv_cube_le (m n : ℕ) (hm : 1 ≤ m) :
    ∑ k ∈ Finset.Ico m n, 1 / ((k : ℝ) + 1) ^ 3 ≤ 2 / (m : ℝ) ^ 2 := by
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hterm : ∀ k ∈ Finset.Ico m n,
      1 / ((k : ℝ) + 1) ^ 3 ≤ (1 / (m : ℝ)) * (((k : ℝ)) ^ 2)⁻¹ := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hle : 1 / ((k : ℝ) + 1) ≤ 1 / (m : ℝ) :=
      one_div_le_one_div_of_le hmR (by exact_mod_cast le_trans hk.1 (Nat.le_succ k))
    have hs : 1 / ((k : ℝ) + 1) ^ 2 ≤ (((k : ℝ)) ^ 2)⁻¹ := by
      rw [← one_div]
      have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_trans hm hk.1
      have hpos : (0 : ℝ) < (k : ℝ) ^ 2 := pow_pos (by linarith) 2
      have hle2 : (k : ℝ) ^ 2 ≤ ((k : ℝ) + 1) ^ 2 := by
        apply pow_le_pow_left₀ (by linarith)
        linarith
      exact one_div_le_one_div_of_le hpos hle2
    calc 1 / ((k : ℝ) + 1) ^ 3
        = (1 / ((k : ℝ) + 1)) * (1 / ((k : ℝ) + 1) ^ 2) := by
            field_simp
      _ ≤ (1 / (m : ℝ)) * (1 / ((k : ℝ) + 1) ^ 2) :=
          mul_le_mul_of_nonneg_right hle (by positivity)
      _ ≤ (1 / (m : ℝ)) * (((k : ℝ)) ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_left hs (by positivity)
  calc ∑ k ∈ Finset.Ico m n, 1 / ((k : ℝ) + 1) ^ 3
      ≤ ∑ k ∈ Finset.Ico m n, (1 / (m : ℝ)) * (((k : ℝ)) ^ 2)⁻¹ :=
        Finset.sum_le_sum hterm
    _ = (1 / (m : ℝ)) * ∑ k ∈ Finset.Ico m n, (((k : ℝ)) ^ 2)⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ (1 / (m : ℝ)) * (2 / (m : ℝ)) :=
        mul_le_mul_of_nonneg_left (sum_Ico_inv_sq_le hm n) (by positivity)
    _ = 2 / (m : ℝ) ^ 2 := by ring

/-- The inverse-sixth-power tail over the lattice: outside the ball of radius
`L`, `∑ 1/(1+|u|)⁶ ≤ 2048/L²`. -/

private theorem sum_inv_six_filter_le (r L : ℕ) (hL : 2 ≤ L) :
    ∑ u ∈ (boxFinset (0 : Site 4) r).filter (fun u => (L : ℝ) ≤ euclidNorm u),
        1 / (1 + euclidNorm u) ^ 6 ≤ 2048 / (L : ℝ) ^ 2 := by
  classical
  set m : ℕ := L / 2 with hm
  have hm1 : 1 ≤ m := by omega
  have hmL : (m : ℝ) ≤ (L : ℝ) / 2 := by
    have h2m : 2 * m ≤ L := by
      rw [hm, mul_comm]
      exact Nat.div_mul_le_self L 2
    have hcast : (2 : ℝ) * (m : ℝ) ≤ (L : ℝ) := by exact_mod_cast h2m
    linarith
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
  set g : ℕ → ℝ := fun k => if (L : ℝ) / 2 ≤ (k : ℝ) then 1 / (1 + (k : ℝ)) ^ 6 else 0
    with hg
  have hg0 : g 0 = 0 := by
    simp only [hg]
    rw [if_neg]
    have hL2 : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    linarith
  have hA1 : ∑ u ∈ (boxFinset (0 : Site 4) r).filter (fun u => (L : ℝ) ≤ euclidNorm u),
        1 / (1 + euclidNorm u) ^ 6
      ≤ ∑ u ∈ (boxFinset (0 : Site 4) r).filter (fun u => (L : ℝ) ≤ euclidNorm u),
          g (supNorm u) := by
    refine Finset.sum_le_sum fun u hu => ?_
    rw [Finset.mem_filter] at hu
    obtain ⟨_, huL⟩ := hu
    have hsl : (supNorm u : ℝ) ≤ euclidNorm u := supNorm_le_euclidNorm u
    have h2s : euclidNorm u ≤ 2 * (supNorm u : ℝ) := by
      have h := euclidNorm_le_sqrt_mul_supNorm (d := 4) u
      have h4 : Real.sqrt ((4 : ℕ) : ℝ) = 2 := by norm_num
      rwa [h4] at h
    have hcond : (L : ℝ) / 2 ≤ (supNorm u : ℝ) := by linarith
    simp only [hg, if_pos hcond]
    exact one_div_le_one_div_of_le (by positivity)
      (by apply pow_le_pow_left₀ (by positivity); linarith)
  have hA2 : ∑ u ∈ (boxFinset (0 : Site 4) r).filter (fun u => (L : ℝ) ≤ euclidNorm u),
        g (supNorm u) ≤ ∑ u ∈ boxFinset (0 : Site 4) r, g (supNorm u) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun u _ _ => by simp only [hg]; split_ifs <;> positivity)
  have hB : ∑ u ∈ boxFinset (0 : Site 4) r, g (supNorm u)
      = g 0 + ∑ k ∈ Finset.Icc 1 r, (shellCard 4 k : ℝ) * g k := sum_box_radial g r
  have hC : ∑ k ∈ Finset.Icc 1 r, (shellCard 4 k : ℝ) * g k
      ≤ ∑ k ∈ Finset.Icc m r, 64 / ((k : ℝ) + 1) ^ 3 := by
    have hsub : Finset.Icc m r ⊆ Finset.Icc 1 r := by
      intro k hk
      rw [Finset.mem_Icc] at hk ⊢
      exact ⟨le_trans hm1 hk.1, hk.2⟩
    have hzero : ∀ k ∈ Finset.Icc 1 r, k ∉ Finset.Icc m r →
        (shellCard 4 k : ℝ) * g k = 0 := by
      intro k hk hknot
      rw [Finset.mem_Icc] at hk
      have hkm : k < m := by
        by_contra h
        exact hknot (Finset.mem_Icc.mpr ⟨by omega, hk.2⟩)
      have hklt : (k : ℝ) < (L : ℝ) / 2 := by
        have : (k : ℝ) < (m : ℝ) := by exact_mod_cast hkm
        linarith
      simp only [hg, if_neg (by linarith : ¬ (L : ℝ) / 2 ≤ (k : ℝ)), mul_zero]
    have hEq : ∑ k ∈ Finset.Icc 1 r, (shellCard 4 k : ℝ) * g k
        = ∑ k ∈ Finset.Icc m r, (shellCard 4 k : ℝ) * g k :=
      (Finset.sum_subset hsub hzero).symm
    rw [hEq]
    refine Finset.sum_le_sum fun k hk => ?_
    rw [Finset.mem_Icc] at hk
    by_cases hcond : (L : ℝ) / 2 ≤ (k : ℝ)
    · simp only [hg, if_pos hcond]
      have hshell : (shellCard 4 k : ℝ) ≤ 64 * ((k : ℝ) + 1) ^ 3 := by
        have hk1 : 1 ≤ k := le_trans hm1 hk.1
        have h := shellCard_le 4 hk1
        norm_num at h
        calc (shellCard 4 k : ℝ) ≤ 8 * (2 * (k : ℝ) + 1) ^ 3 := h
          _ ≤ 8 * (2 * ((k : ℝ) + 1)) ^ 3 := by
              apply mul_le_mul_of_nonneg_left _ (by norm_num)
              apply pow_le_pow_left₀ (by positivity); linarith
          _ = 64 * ((k : ℝ) + 1) ^ 3 := by ring
      calc (shellCard 4 k : ℝ) * (1 / (1 + (k : ℝ)) ^ 6)
          ≤ (64 * ((k : ℝ) + 1) ^ 3) * (1 / (1 + (k : ℝ)) ^ 6) :=
            mul_le_mul_of_nonneg_right hshell (by positivity)
        _ = 64 / ((k : ℝ) + 1) ^ 3 := by
            have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
            field_simp
            ring
    · simp only [hg, if_neg hcond, mul_zero]
      exact div_nonneg (by norm_num) (by positivity)
  have hD : ∑ k ∈ Finset.Icc m r, 64 / ((k : ℝ) + 1) ^ 3 ≤ 64 * (2 / (m : ℝ) ^ 2) := by
    have hsum : ∑ k ∈ Finset.Icc m r, 64 / ((k : ℝ) + 1) ^ 3
        = 64 * ∑ k ∈ Finset.Icc m r, 1 / ((k : ℝ) + 1) ^ 3 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [hsum]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    rw [← Finset.Ico_succ_right_eq_Icc]
    exact sum_Ico_inv_cube_le m (r + 1) hm1
  have hE : 64 * (2 / (m : ℝ) ^ 2) ≤ 2048 / (L : ℝ) ^ 2 := by
    have hLpos : (0 : ℝ) < (L : ℝ) := by positivity
    have hmle : (L : ℝ) / 4 ≤ (m : ℝ) := by
      have h : L ≤ 3 * m := by omega
      have hcast : (L : ℝ) ≤ 3 * (m : ℝ) := by exact_mod_cast h
      linarith [hmpos.le]
    have h4 : (L : ℝ) ^ 2 ≤ 16 * (m : ℝ) ^ 2 := by
      have h4m : (L : ℝ) / 4 ≤ (m : ℝ) := hmle
      have : (L : ℝ) ≤ 4 * (m : ℝ) := by linarith
      have hsq : (L : ℝ) ^ 2 ≤ (4 * (m : ℝ)) ^ 2 := pow_le_pow_left₀ hLpos.le this 2
      nlinarith [hsq]
    rw [show 64 * (2 / (m : ℝ) ^ 2) = 128 / (m : ℝ) ^ 2 by ring]
    rw [div_le_div_iff₀ (by positivity : (0:ℝ) < (m:ℝ)^2) (by positivity : (0:ℝ) < (L:ℝ)^2)]
    nlinarith [h4]
  calc ∑ u ∈ (boxFinset (0 : Site 4) r).filter (fun u => (L : ℝ) ≤ euclidNorm u),
        1 / (1 + euclidNorm u) ^ 6
      ≤ ∑ u ∈ boxFinset (0 : Site 4) r, g (supNorm u) := le_trans hA1 hA2
    _ = g 0 + ∑ k ∈ Finset.Icc 1 r, (shellCard 4 k : ℝ) * g k := hB
    _ = ∑ k ∈ Finset.Icc 1 r, (shellCard 4 k : ℝ) * g k := by rw [hg0, zero_add]
    _ ≤ ∑ k ∈ Finset.Icc m r, 64 / ((k : ℝ) + 1) ^ 3 := hC
    _ ≤ 64 * (2 / (m : ℝ) ^ 2) := hD
    _ ≤ 2048 / (L : ℝ) ^ 2 := hE

theorem exists_tsum_cutField_cube_le :
    ∃ C : ℝ, 0 < C ∧ ∀ r L : ℕ, 2 ≤ L → ∀ φ : ℝ → ℝ, IsCutoff φ →
      ∑' u : Site 4, cutField r L φ u ^ 3 ≤ C / (L : ℝ) ^ 2 := by
  obtain ⟨C0, hC0pos, hC0⟩ := exists_srwGreenInf_four_le
  refine ⟨C0 ^ 3 * 2048, by positivity, fun r L hL φ hφ => ?_⟩
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
  have hsupp : ∀ u : Site 4, u ∉ boxFinset (0 : Site 4) r → cutField r L φ u ^ 3 = 0 := by
    intro u hu
    have hnot : u ∉ box r := by
      intro hmem
      exact hu (by rwa [box_eq_coe_boxFinset r] at hmem)
    rw [cutField, killedGreen_eq_zero_of_notMem (box r) hnot, zero_mul]
    exact zero_pow (by norm_num)
  rw [tsum_eq_sum hsupp]
  have hkey : ∑ u ∈ boxFinset (0 : Site 4) r, cutField r L φ u ^ 3
      ≤ C0 ^ 3 * ∑ u ∈ (boxFinset (0 : Site 4) r).filter (fun u => (L : ℝ) ≤ euclidNorm u),
          1 / (1 + euclidNorm u) ^ 6 := by
    have hterm : ∀ u ∈ boxFinset (0 : Site 4) r, cutField r L φ u ^ 3
        ≤ (if (L : ℝ) ≤ euclidNorm u then C0 ^ 3 / (1 + euclidNorm u) ^ 6 else 0) := by
      intro u _
      by_cases huL : (L : ℝ) ≤ euclidNorm u
      · rw [if_pos huL]
        have hgnn : 0 ≤ killedGreen (box r) 0 u := killedGreen_nonneg (box r) 0 u
        have hgle : killedGreen (box r) 0 u ≤ C0 / (1 + euclidNorm u) ^ 2 :=
          le_trans (killedGreen_le_srwGreenInf (box r) u) (hC0 u)
        have harg : 0 ≤ euclidNorm u / (L : ℝ) := div_nonneg (euclidNorm_nonneg u) hLpos.le
        have hφnn : 0 ≤ φ (euclidNorm u / (L : ℝ)) := (hφ.1 _ harg).1
        have hφle : φ (euclidNorm u / (L : ℝ)) ≤ 1 := (hφ.1 _ harg).2
        have hcub : cutField r L φ u ≤ killedGreen (box r) 0 u := by
          rw [cutField]
          calc killedGreen (box r) 0 u * φ (euclidNorm u / (L : ℝ))
              ≤ killedGreen (box r) 0 u * 1 := mul_le_mul_of_nonneg_left hφle hgnn
            _ = killedGreen (box r) 0 u := mul_one _
        have hcube : killedGreen (box r) 0 u ^ 3 ≤ (C0 / (1 + euclidNorm u) ^ 2) ^ 3 :=
          pow_le_pow_left₀ hgnn hgle 3
        have hcfnn : 0 ≤ cutField r L φ u := by
          rw [cutField]; exact mul_nonneg hgnn hφnn
        calc cutField r L φ u ^ 3 ≤ killedGreen (box r) 0 u ^ 3 :=
              pow_le_pow_left₀ hcfnn hcub 3
          _ ≤ (C0 / (1 + euclidNorm u) ^ 2) ^ 3 := hcube
          _ = C0 ^ 3 / (1 + euclidNorm u) ^ 6 := by
              rw [div_pow]
              congr 1
              ring
      · rw [if_neg huL]
        have hle1 : euclidNorm u / (L : ℝ) ≤ 1 := (div_le_one hLpos).mpr (le_of_lt (lt_of_not_ge huL))
        have hzero : φ (euclidNorm u / (L : ℝ)) = 0 :=
          hφ.2.2.1 _ (div_nonneg (euclidNorm_nonneg u) hLpos.le) hle1
        rw [cutField, hzero]
        norm_num
    calc ∑ u ∈ boxFinset (0 : Site 4) r, cutField r L φ u ^ 3
        ≤ ∑ u ∈ boxFinset (0 : Site 4) r,
            (if (L : ℝ) ≤ euclidNorm u then C0 ^ 3 / (1 + euclidNorm u) ^ 6 else 0) :=
          Finset.sum_le_sum hterm
      _ = C0 ^ 3 * ∑ u ∈ (boxFinset (0 : Site 4) r).filter (fun u => (L : ℝ) ≤ euclidNorm u),
            1 / (1 + euclidNorm u) ^ 6 := by
          rw [Finset.mul_sum, Finset.sum_filter]
          refine Finset.sum_congr rfl fun u _ => ?_
          by_cases huL : (L : ℝ) ≤ euclidNorm u
          · rw [if_pos huL, if_pos huL]; ring
          · rw [if_neg huL, if_neg huL]
  calc ∑ u ∈ boxFinset (0 : Site 4) r, cutField r L φ u ^ 3
      ≤ C0 ^ 3 * ∑ u ∈ (boxFinset (0 : Site 4) r).filter (fun u => (L : ℝ) ≤ euclidNorm u),
          1 / (1 + euclidNorm u) ^ 6 := hkey
    _ ≤ C0 ^ 3 * (2048 / (L : ℝ) ^ 2) := by
        exact mul_le_mul_of_nonneg_left (sum_inv_six_filter_le r L hL)
          (by positivity)
    _ = C0 ^ 3 * 2048 / (L : ℝ) ^ 2 := by ring
private lemma euclidNorm_neg (z : Site 4) : euclidNorm (-z) = euclidNorm z := by
  unfold euclidNorm
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.neg_apply]
  push_cast
  ring

/-- Minkowski's triangle inequality for the Euclidean norm, via Cauchy-Schwarz. -/

private lemma euclidNorm_add_le (a b : Site 4) :
    euclidNorm (a + b) ≤ euclidNorm a + euclidNorm b := by
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin 4))
    (fun i => ((a i : ℤ) : ℝ)) (fun i => ((b i : ℤ) : ℝ))
  have hA : (0 : ℝ) ≤ euclidNorm a := euclidNorm_nonneg a
  have hB : (0 : ℝ) ≤ euclidNorm b := euclidNorm_nonneg b
  have hpt : ∀ i : Fin 4, (((a + b) i : ℤ) : ℝ) ^ 2 =
      ((a i : ℤ) : ℝ) ^ 2 + 2 * (((a i : ℤ) : ℝ) * ((b i : ℤ) : ℝ))
        + ((b i : ℤ) : ℝ) ^ 2 := by
    intro i
    have hi : ((a + b) i : ℤ) = (a i : ℤ) + (b i : ℤ) := by simp [Pi.add_apply]
    rw [hi]
    push_cast
    ring
  have hexpand : (∑ i : Fin 4, (((a + b) i : ℤ) : ℝ) ^ 2) =
      (∑ i : Fin 4, ((a i : ℤ) : ℝ) ^ 2)
        + 2 * (∑ i : Fin 4, ((a i : ℤ) : ℝ) * ((b i : ℤ) : ℝ))
        + (∑ i : Fin 4, ((b i : ℤ) : ℝ) ^ 2) := by
    rw [Finset.sum_congr rfl (fun i _ => hpt i)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hcross : (∑ i : Fin 4, ((a i : ℤ) : ℝ) * ((b i : ℤ) : ℝ)) ≤
      euclidNorm a * euclidNorm b := hcs
  have haa : euclidNorm a ^ 2 = ∑ i : Fin 4, ((a i : ℤ) : ℝ) ^ 2 := by
    unfold euclidNorm
    rw [Real.sq_sqrt (by positivity)]
  have hbb : euclidNorm b ^ 2 = ∑ i : Fin 4, ((b i : ℤ) : ℝ) ^ 2 := by
    unfold euclidNorm
    rw [Real.sq_sqrt (by positivity)]
  have hsq : (∑ i : Fin 4, (((a + b) i : ℤ) : ℝ) ^ 2) ≤
      (euclidNorm a + euclidNorm b) ^ 2 := by
    rw [hexpand]
    have hring : (euclidNorm a + euclidNorm b) ^ 2 =
        euclidNorm a ^ 2 + 2 * (euclidNorm a * euclidNorm b) + euclidNorm b ^ 2 := by ring
    rw [hring, haa, hbb]
    linarith [hcross]
  calc euclidNorm (a + b) = Real.sqrt (∑ i : Fin 4, (((a + b) i : ℤ) : ℝ) ^ 2) := rfl
    _ ≤ Real.sqrt ((euclidNorm a + euclidNorm b) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = euclidNorm a + euclidNorm b := Real.sqrt_sq (by linarith [hA, hB])

/-- The reverse triangle inequality for the Euclidean norm. -/

private lemma abs_euclidNorm_sub_le (a b : Site 4) :
    |euclidNorm a - euclidNorm b| ≤ euclidNorm (a - b) := by
  have h1 := euclidNorm_add_le b (a - b)
  have h2 : b + (a - b) = a := by abel
  rw [h2] at h1
  have h3 := euclidNorm_add_le a (b - a)
  have h4 : a + (b - a) = b := by abel
  rw [h4] at h3
  have h5 : euclidNorm (b - a) = euclidNorm (a - b) := by
    rw [show b - a = -(a - b) by abel, euclidNorm_neg]
  rw [h5] at h3
  rw [abs_sub_le_iff]
  exact ⟨by linarith, by linarith⟩

/-- The discrete Caccioppoli inequality in the form used here: harmonicity is needed only
on `B`, and only `f · η² = 0` is required off `B`. -/

private theorem caccioppoli_vanishing {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
    {c : V → V → ℝ} (hc : Network.IsCond G c)
    (S B : Finset V) (f η : V → ℝ)
    (hf : ∀ x ∈ B, Network.netLaplacian G c f x = 0)
    (hg : ∀ x, x ∉ B → f x * η x ^ 2 = 0) (hBS : B ⊆ S)
    (hnb : ∀ x ∈ B, ∀ y, G.Adj x y → y ∈ S) :
    ∑ x ∈ S, ∑ y ∈ G.neighborFinset x, c x y * (f x - f y) ^ 2 * η x ^ 2
      ≤ 4 * ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
          c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2 := by
  classical
  have hform := Network.formOn_eq_neg_two_mul hc S B f (fun x => f x * η x ^ 2) hg hBS hnb
  have hharm : ∑ x ∈ B, f x * η x ^ 2 * Network.netLaplacian G c f x = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    rw [hf x hx]
    ring
  rw [hharm, mul_zero] at hform
  have hpt : ∀ x ∈ S, ∀ y ∈ G.neighborFinset x,
      c x y * (f x - f y) ^ 2 * η x ^ 2
        ≤ 2 * (c x y * (f x - f y) * (f x * η x ^ 2 - f y * η y ^ 2))
          + 4 * (c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2) := by
    intro x _ y _
    have hc0 := hc.nonneg x y
    nlinarith [Network.caccioppoli_pointwise (f x) (f y) (η x) (η y),
      mul_nonneg hc0 (sq_nonneg (f x - f y)), mul_nonneg hc0 (sq_nonneg (η x - η y))]
  calc ∑ x ∈ S, ∑ y ∈ G.neighborFinset x, c x y * (f x - f y) ^ 2 * η x ^ 2
      ≤ ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
          (2 * (c x y * (f x - f y) * (f x * η x ^ 2 - f y * η y ^ 2))
            + 4 * (c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2)) :=
        Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => hpt x hx y hy
    _ = 2 * Network.formOn G c S f (fun x => f x * η x ^ 2)
          + 4 * ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
              c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2 := by
        have h1 : (∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
              2 * (c x y * (f x - f y) * (f x * η x ^ 2 - f y * η y ^ 2)))
            = 2 * Network.formOn G c S f (fun x => f x * η x ^ 2) := by
          simp only [Network.formOn, Finset.mul_sum]
        have h2 : (∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
              4 * (c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2))
            = 4 * ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
                c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2 := by
          simp only [Finset.mul_sum]
        rw [show (∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
              (2 * (c x y * (f x - f y) * (f x * η x ^ 2 - f y * η y ^ 2))
                + 4 * (c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2)))
            = (∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
                2 * (c x y * (f x - f y) * (f x * η x ^ 2 - f y * η y ^ 2)))
              + ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
                  4 * (c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2) from by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun x _ => Finset.sum_add_distrib]
        rw [h1, h2]
    _ = 4 * ∑ x ∈ S, ∑ y ∈ G.neighborFinset x,
          c x y * (f x ^ 2 + f y ^ 2) * (η x - η y) ^ 2 := by
        rw [hform]; ring

/-- The Euclidean norm of a coordinate unit vector is one. -/

private lemma euclidNorm_unit (i : Fin 4) : euclidNorm (unit i) = 1 := by
  have hsum : (∑ j : Fin 4, (((unit i) j : ℤ) : ℝ) ^ 2) = 1 := by
    classical
    rw [Finset.sum_eq_single i]
    · simp [unit]
    · intro j _ hji
      simp [unit, hji]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  unfold euclidNorm
  rw [hsum, Real.sqrt_one]

/-- The sup-norm grows by at most one under a unit shift. -/

private lemma supNorm_add_unit_le (u : Site 4) (i : Fin 4) :
    supNorm (u + unit i) ≤ supNorm u + 1 := by
  refine Finset.sup_le fun j _ => ?_
  have h : (u j).natAbs ≤ supNorm u := Finset.le_sup (f := fun j : Fin 4 => (u j).natAbs)
    (Finset.mem_univ j)
  have h2 : ((u + unit i) j).natAbs ≤ (u j).natAbs + 1 := by
    by_cases hj : j = i
    · rw [hj]
      have h3 := Int.natAbs_add_le (u i) 1
      simpa [unit, Pi.add_apply, Pi.single_eq_same] using h3
    · have hji : (u + unit i) j = u j := by
        simp [unit, Pi.add_apply, Pi.single_eq_of_ne hj]
      rw [hji]; omega
  omega

/-- The sup-norm grows by at most one under a downward unit shift. -/

private lemma supNorm_sub_unit_le (u : Site 4) (i : Fin 4) :
    supNorm (u - unit i) ≤ supNorm u + 1 := by
  refine Finset.sup_le fun j _ => ?_
  have h : (u j).natAbs ≤ supNorm u := Finset.le_sup (f := fun j : Fin 4 => (u j).natAbs)
    (Finset.mem_univ j)
  have h2 : ((u - unit i) j).natAbs ≤ (u j).natAbs + 1 := by
    by_cases hj : j = i
    · rw [hj]
      have h3 := Int.natAbs_add_le (u i) (-1)
      simpa [sub_eq_add_neg, unit, Pi.sub_apply, Pi.single_eq_same] using h3
    · have hji : (u - unit i) j = u j := by
        simp [unit, Pi.sub_apply, Pi.single_eq_of_ne hj]
      rw [hji]; omega
  omega

/-- The cutoff `φ(|·|/L)` is `2/L`-Lipschitz in the lattice: at unit shifts its values
differ by at most `2/L`. -/

private lemma cutoff_sub_le {L : ℕ} (hL : 1 ≤ L) {φ : ℝ → ℝ} (hφ : IsCutoff φ)
    {x y : Site 4} (hxy : euclidNorm (x - y) ≤ 1) :
    |φ (euclidNorm x / (L : ℝ)) - φ (euclidNorm y / (L : ℝ))| ≤ 2 / L := by
  have hLpos : (0 : ℝ) < (L : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hL)
  have htri : |euclidNorm x - euclidNorm y| ≤ 1 := by
    have := abs_euclidNorm_sub_le x y
    linarith
  have ha : 0 ≤ euclidNorm x / (L : ℝ) :=
    div_nonneg (euclidNorm_nonneg x) hLpos.le
  have hb : 0 ≤ euclidNorm y / (L : ℝ) :=
    div_nonneg (euclidNorm_nonneg y) hLpos.le
  have h1 := hφ.2.1 _ _ ha hb
  have h2 : |euclidNorm x / (L : ℝ) - euclidNorm y / (L : ℝ)| ≤ 1 / L := by
    rw [← sub_div, abs_div, abs_of_pos hLpos]
    rw [div_le_div_iff₀ hLpos hLpos]
    exact mul_le_mul_of_nonneg_right htri hLpos.le
  calc |φ (euclidNorm x / (L : ℝ)) - φ (euclidNorm y / (L : ℝ))|
      ≤ 2 * |euclidNorm x / (L : ℝ) - euclidNorm y / (L : ℝ)| := h1
    _ ≤ 2 * (1 / L) := by linarith
    _ = 2 / L := by ring

/-- The neighbour sum on `ℤ⁴` is the sum over the `±eᵢ`. -/

private lemma sum_neighborFinset_eq_nbrSum_four (H : Site 4 → ℝ) (x : Site 4) :
    ∑ y ∈ (lattice 4).neighborFinset x, H y = nbrSum H x := by
  have hwalk := Graph.Zd.walkOp_eq (d := 4) H x
  have hdeg : (((lattice 4).degree x : ℕ) : ℝ) = 8 := by
    rw [Graph.Zd.degree_eq]; norm_num
  rw [Graph.walkOp, hdeg, LatticeProb.walkOp] at hwalk
  have h24 : (2 : ℝ) * ((4 : ℕ) : ℝ) = 8 := by norm_num
  rw [h24] at hwalk
  have h8 := congrArg (fun z : ℝ => z * 8) hwalk
  rwa [div_mul_cancel₀ _ (by norm_num : (8 : ℝ) ≠ 0),
    div_mul_cancel₀ _ (by norm_num : (8 : ℝ) ≠ 0)] at h8

/-- The mean-value property `killedGreen_eq_avg` makes the killed Green function
harmonic away from the origin. -/

private lemma laplacian_killedGreen_eq_zero (r : ℕ) {x : Site 4}
    (hx : x ∈ box r) (hx0 : x ≠ 0) :
    Graph.laplacian (lattice 4) (fun u => killedGreen (box r) 0 u) x = 0 := by
  have hmv := killedGreen_eq_avg (box r) hx hx0
  have hsum := sum_neighborFinset_eq_nbrSum_four (fun u => killedGreen (box r) 0 u) x
  have hnbr : nbrSum (fun u => killedGreen (box r) 0 u) x = 8 * killedGreen (box r) 0 x := by
    rw [LatticeProb.nbrSum]; linarith [hmv]
  have hdeg : (((lattice 4).degree x : ℕ) : ℝ) = 8 := by
    rw [Graph.Zd.degree_eq]; norm_num
  rw [Graph.laplacian, Finset.sum_sub_distrib, Finset.sum_const,
    SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul, hdeg, hsum, hnbr]
  ring

/-- The neighbour sum on `ℤ⁴` with unit conductance is the sum over the `±eᵢ`. -/

private lemma neighbor_unitCond_sum (x : Site 4) (F : Site 4 → ℝ) :
    ∑ y ∈ (lattice 4).neighborFinset x, Network.unitCond (lattice 4) x y * F y
      = ∑ i : Fin 4, (F (x + unit i) + F (x - unit i)) := by
  have h1 : ∑ y ∈ (lattice 4).neighborFinset x, Network.unitCond (lattice 4) x y * F y
      = ∑ y ∈ (lattice 4).neighborFinset x, F y := by
    apply Finset.sum_congr rfl
    intro y hy
    rw [Network.unitCond, if_pos ((SimpleGraph.mem_neighborFinset _ _ _).mp hy), one_mul]
  rw [h1, sum_neighborFinset_eq_nbrSum_four F x, LatticeProb.nbrSum]

/-- The radial indicator of the transition shell `L - 1 ≤ |z| ≤ 2L + 1`. -/

private def shellInd (L : ℕ) (z : Site 4) : ℝ :=
  if (L : ℝ) - 1 ≤ euclidNorm z ∧ euclidNorm z ≤ 2 * (L : ℝ) + 1 then 1 else 0

private lemma shellInd_nonneg (L : ℕ) (z : Site 4) : 0 ≤ shellInd L z := by
  unfold shellInd; split <;> norm_num

private lemma shellInd_le_one (L : ℕ) (z : Site 4) : shellInd L z ≤ 1 := by
  unfold shellInd; split <;> norm_num

private lemma shellInd_eq_zero_or_one (L : ℕ) (z : Site 4) :
    shellInd L z = 0 ∨ shellInd L z = 1 := by
  unfold shellInd; split <;> simp

private lemma shellInd_eq_one_iff (L : ℕ) (z : Site 4) :
    shellInd L z = 1 ↔ (L : ℝ) - 1 ≤ euclidNorm z ∧ euclidNorm z ≤ 2 * (L : ℝ) + 1 := by
  unfold shellInd
  by_cases h : (L : ℝ) - 1 ≤ euclidNorm z ∧ euclidNorm z ≤ 2 * (L : ℝ) + 1
  · rw [if_pos h]; exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [if_neg h]; exact ⟨fun h1 => absurd h1 (by norm_num), fun h1 => absurd h1 h⟩

private lemma shellInd_eq_zero_iff (L : ℕ) (z : Site 4) :
    shellInd L z = 0 ↔
      ¬((L : ℝ) - 1 ≤ euclidNorm z ∧ euclidNorm z ≤ 2 * (L : ℝ) + 1) := by
  constructor
  · intro h hc
    rw [shellInd_eq_one_iff L z |>.mpr hc] at h
    norm_num at h
  · intro h
    rcases shellInd_eq_zero_or_one L z with h0 | h1
    · exact h0
    · exact absurd ((shellInd_eq_one_iff L z).mp h1) h

/-- On adjacent sites, the cut-off `φ(|·|/L)` differs only inside the transition shell, and
 there by at most `2/L`. -/

private lemma cutoff_sq_le_shell {L : ℕ} (hL : 2 ≤ L) {φ : ℝ → ℝ} (hφ : IsCutoff φ)
    {x y : Site 4} (hxy : (lattice 4).Adj x y) :
    (φ (euclidNorm x / (L : ℝ)) - φ (euclidNorm y / (L : ℝ))) ^ 2
      ≤ (4 / (L : ℝ) ^ 2) * (shellInd L x * shellInd L y) := by
  have hL1 : 1 ≤ L := by omega
  have hLpos : (0 : ℝ) < (L : ℝ) := by positivity
  have hnd : euclidNorm (x - y) = 1 := by
    rcases Graph.Zd.adj_iff.mp hxy with ⟨i, rfl | rfl⟩
    · rw [show x - (x + unit i) = -unit i by abel, euclidNorm_neg, euclidNorm_unit]
    · rw [show x - (x - unit i) = unit i by abel, euclidNorm_unit]
  have htri : |euclidNorm x - euclidNorm y| ≤ 1 := by
    have := abs_euclidNorm_sub_le x y
    rwa [hnd] at this
  have hlip : |φ (euclidNorm x / (L : ℝ)) - φ (euclidNorm y / (L : ℝ))| ≤ 2 / L :=
    cutoff_sub_le hL1 hφ (by rw [hnd])
  have hAz : ∀ u : Site 4, euclidNorm u ≤ (L : ℝ) →
      φ (euclidNorm u / (L : ℝ)) = 0 := fun u hu =>
    hφ.2.2.1 _ (div_nonneg (euclidNorm_nonneg u) hLpos.le) ((div_le_one hLpos).mpr hu)
  have hAo : ∀ u : Site 4, 2 * (L : ℝ) ≤ euclidNorm u →
      φ (euclidNorm u / (L : ℝ)) = 1 := fun u hu =>
    hφ.2.2.2 _ ((le_div_iff₀ hLpos).mpr hu)
  have hsame_of_zero : ∀ z w : Site 4, shellInd L z = 0 → (lattice 4).Adj z w →
      φ (euclidNorm z / (L : ℝ)) = φ (euclidNorm w / (L : ℝ)) := by
    intro z w hz hzw
    have hzw' : |euclidNorm z - euclidNorm w| ≤ 1 := by
      have h := abs_euclidNorm_sub_le z w
      rcases Graph.Zd.adj_iff.mp hzw with ⟨i, rfl | rfl⟩
      · rwa [show z - (z + unit i) = -unit i by abel, euclidNorm_neg, euclidNorm_unit] at h
      · rwa [show z - (z - unit i) = unit i by abel, euclidNorm_unit] at h
    have hnot := (shellInd_eq_zero_iff L z).mp hz
    rw [not_and_or] at hnot
    rcases hnot with hsmall | hbig
    · have hzle : euclidNorm z ≤ (L : ℝ) := by
        have := not_le.mp hsmall; linarith
      have hwle : euclidNorm w ≤ (L : ℝ) := by
        have := abs_le.mp hzw'; linarith
      rw [hAz z hzle, hAz w hwle]
    · have hzge : 2 * (L : ℝ) ≤ euclidNorm z := by
        have := not_le.mp hbig; linarith
      have hwge : 2 * (L : ℝ) ≤ euclidNorm w := by
        have := abs_le.mp hzw'; linarith
      rw [hAo z hzge, hAo w hwge]
  rcases shellInd_eq_zero_or_one L x with hx0 | hx1
  · rw [hx0, zero_mul, mul_zero]
    rw [hsame_of_zero x y hx0 hxy]
    simp
  · rcases shellInd_eq_zero_or_one L y with hy0 | hy1
    · rw [hy0, mul_zero, mul_zero]
      rw [hsame_of_zero y x hy0 hxy.symm]
      simp
    · rw [hx1, hy1, mul_one]
      have hsq : (φ (euclidNorm x / (L : ℝ)) - φ (euclidNorm y / (L : ℝ))) ^ 2
          ≤ (2 / (L : ℝ)) ^ 2 := by
        rw [sq_le_sq, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 / (L : ℝ))]
        exact hlip
      have h2 : (2 / (L : ℝ)) ^ 2 = 4 / (L : ℝ) ^ 2 := by ring
      linarith [hsq]

/-- A sum of a nonnegative function over the neighbours of a box is at most eight times
 the sum over the next box. -/

private lemma sum_neighborFinset_le_eight (F : Site 4 → ℝ) (hF : ∀ y, 0 ≤ F y) (r : ℕ) :
    ∑ x ∈ boxFinset (0 : Site 4) (r + 1),
        ∑ y ∈ (lattice 4).neighborFinset x, F y
      ≤ 8 * ∑ y ∈ boxFinset (0 : Site 4) (r + 2), F y := by
  have hunit : ∀ i : Fin 4, supNorm (unit i) ≤ 1 := by
    intro i
    rw [supNorm_le_iff]
    intro j
    by_cases hji : j = i
    · subst j; simp [unit]
    · simp [unit, hji]
  have hshift : ∀ a : Site 4, supNorm a ≤ 1 →
      ∑ x ∈ boxFinset (0 : Site 4) (r + 1), F (x + a)
        ≤ ∑ y ∈ boxFinset (0 : Site 4) (r + 2), F y := by
    intro a ha
    have hsub : (boxFinset (0 : Site 4) (r + 1)).image (fun x => x + a)
        ⊆ boxFinset (0 : Site 4) (r + 2) := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
      rw [mem_boxFinset_zero_iff] at hx ⊢
      exact (supNorm_add_le x a).trans (by omega)
    have heq : ∑ x ∈ boxFinset (0 : Site 4) (r + 1), F (x + a)
        = ∑ y ∈ (boxFinset (0 : Site 4) (r + 1)).image (fun x => x + a), F y := by
      rw [Finset.sum_image]
      intro x _ y _ hxy
      exact add_right_cancel hxy
    rw [heq]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun y _ _ => hF y)
  rw [show (∑ x ∈ boxFinset (0 : Site 4) (r + 1),
        ∑ y ∈ (lattice 4).neighborFinset x, F y)
      = ∑ x ∈ boxFinset (0 : Site 4) (r + 1),
          ∑ i : Fin 4, (F (x + unit i) + F (x - unit i)) by
    apply Finset.sum_congr rfl
    intro x _
    have h1 : ∑ y ∈ (lattice 4).neighborFinset x, Network.unitCond (lattice 4) x y * F y
        = ∑ y ∈ (lattice 4).neighborFinset x, F y := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [Network.unitCond, if_pos ((SimpleGraph.mem_neighborFinset _ _ _).mp hy), one_mul]
    rw [← h1, neighbor_unitCond_sum x F]]
  rw [Finset.sum_comm]
  have hper : ∀ i : Fin 4,
      ∑ x ∈ boxFinset (0 : Site 4) (r + 1), (F (x + unit i) + F (x - unit i))
        ≤ 2 * ∑ y ∈ boxFinset (0 : Site 4) (r + 2), F y := by
    intro i
    have h1 : ∑ x ∈ boxFinset (0 : Site 4) (r + 1), F (x + unit i)
        ≤ ∑ y ∈ boxFinset (0 : Site 4) (r + 2), F y :=
      hshift (unit i) (hunit i)
    have h2 : ∑ x ∈ boxFinset (0 : Site 4) (r + 1), F (x - unit i)
        ≤ ∑ y ∈ boxFinset (0 : Site 4) (r + 2), F y := by
      have h := hshift (-unit i) (by simpa using hunit i)
      simpa [sub_eq_add_neg] using h
    rw [Finset.sum_add_distrib]
    linarith
  calc ∑ i : Fin 4, ∑ x ∈ boxFinset (0 : Site 4) (r + 1),
          (F (x + unit i) + F (x - unit i))
      ≤ ∑ _i : Fin 4, (2 * ∑ y ∈ boxFinset (0 : Site 4) (r + 2), F y) :=
        Finset.sum_le_sum (fun i _ => hper i)
    _ = 8 * ∑ y ∈ boxFinset (0 : Site 4) (r + 2), F y := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- Bound the cut-off gradient term of the Caccioppoli estimate: the `φ`-weighted gradient
 energy of the killed Green function on the transition shell is `O(L⁻²)`. -/

private lemma energy_rhs_bound (C₁ : ℝ) (hC₁pos : 0 < C₁)
    (hC₁ : ∀ u : Site 4, srwGreenInf 4 u ≤ C₁ / (1 + euclidNorm u) ^ 2)
    (r L : ℕ) (hL : 2 ≤ L) (φ : ℝ → ℝ) (hφ : IsCutoff φ) :
    (∑ x ∈ boxFinset (0 : Site 4) (r + 1),
        ∑ y ∈ (lattice 4).neighborFinset x,
          Network.unitCond (lattice 4) x y
            * (killedGreen (box r) 0 x ^ 2 + killedGreen (box r) 0 y ^ 2)
            * (φ (euclidNorm x / (L : ℝ)) - φ (euclidNorm y / (L : ℝ))) ^ 2)
      ≤ 2 ^ 25 * C₁ ^ 2 / (L : ℝ) ^ 2 := by
  have hL1 : 1 ≤ L := by omega
  have hL2R : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hLpos : (0 : ℝ) < (L : ℝ) := by positivity
  set g : Site 4 → ℝ := fun u => killedGreen (box r) 0 u with hgdef
  set A : Site 4 → ℝ := fun u => φ (euclidNorm u / (L : ℝ)) with hAdef
  set S : Finset (Site 4) := boxFinset (0 : Site 4) (r + 1) with hSdef
  set RHS : ℝ := ∑ x ∈ S, ∑ y ∈ (lattice 4).neighborFinset x,
      Network.unitCond (lattice 4) x y * (g x ^ 2 + g y ^ 2) * (A x - A y) ^ 2 with hRHSdef
  change RHS ≤ 2 ^ 25 * C₁ ^ 2 / (L : ℝ) ^ 2
  have hg0 : ∀ u, 0 ≤ g u := fun u => killedGreen_nonneg (box r) 0 u
  have hgle : ∀ u, g u ≤ C₁ / (1 + euclidNorm u) ^ 2 := fun u =>
    le_trans (killedGreen_le_srwGreenInf (box r) u) (hC₁ u)
  have hAz : ∀ u : Site 4, euclidNorm u ≤ (L : ℝ) → A u = 0 := fun u hu =>
    hφ.2.2.1 _ (div_nonneg (euclidNorm_nonneg u) hLpos.le) ((div_le_one hLpos).mpr hu)
  have hAo : ∀ u : Site 4, 2 * (L : ℝ) ≤ euclidNorm u → A u = 1 := fun u hu =>
    hφ.2.2.2 _ ((le_div_iff₀ hLpos).mpr hu)

  have hadj_dist : ∀ x y : Site 4, (lattice 4).Adj x y → euclidNorm (x - y) ≤ 1 := by
    intro x y hxy
    obtain ⟨i, hi | hi⟩ := hxy
    · rw [hi, show x - (x + unit i) = -unit i by abel, euclidNorm_neg, euclidNorm_unit]
    · rw [hi, show (y + unit i) - y = unit i by abel, euclidNorm_unit]
  have hAnn : ∀ x y : Site 4, (lattice 4).Adj x y →
      (euclidNorm x < (L : ℝ) - 1 ∨ 2 * (L : ℝ) + 1 < euclidNorm x) →
      (A x - A y) ^ 2 = 0 := by
    intro x y hxy hout
    have hdist := hadj_dist x y hxy
    have hAy : A y = A x := by
      rcases hout with hx | hx
      · have hy : euclidNorm y ≤ (L : ℝ) := by
          have htri : euclidNorm y ≤ euclidNorm x + euclidNorm (y - x) := by
            have h := euclidNorm_add_le x (y - x)
            rwa [show x + (y - x) = y by abel] at h
          have hneg : euclidNorm (y - x) = euclidNorm (x - y) := by
            rw [show y - x = -(x - y) by abel, euclidNorm_neg]
          rw [hneg] at htri
          linarith
        rw [hAz y hy, hAz x (by linarith)]
      · have hy : 2 * (L : ℝ) ≤ euclidNorm y := by
          have htri : euclidNorm x ≤ euclidNorm y + euclidNorm (x - y) := by
            have h := euclidNorm_add_le y (x - y)
            rwa [show y + (x - y) = x by abel] at h
          linarith
        rw [hAo y hy, hAo x (by linarith)]
    rw [hAy]; ring
  set T : Finset (Site 4) := S.filter (fun x => (L : ℝ) - 1 ≤ euclidNorm x ∧
      euclidNorm x ≤ 2 * (L : ℝ) + 1) with hTdef
  have hRHS_eq : RHS = ∑ x ∈ T, ∑ y ∈ (lattice 4).neighborFinset x,
      Network.unitCond (lattice 4) x y * (g x ^ 2 + g y ^ 2) * (A x - A y) ^ 2 := by
    rw [hRHSdef]
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro x hxS hxT
    apply Finset.sum_eq_zero
    intro y hy
    have hxT' : ¬ ((L : ℝ) - 1 ≤ euclidNorm x ∧ euclidNorm x ≤ 2 * (L : ℝ) + 1) :=
      fun hp => hxT (Finset.mem_filter.mpr ⟨hxS, hp⟩)
    have hnot : euclidNorm x < (L : ℝ) - 1 ∨ 2 * (L : ℝ) + 1 < euclidNorm x := by
      rcases lt_or_ge (euclidNorm x) ((L : ℝ) - 1) with h | h
      · exact Or.inl h
      · exact Or.inr (lt_of_not_ge fun hc => hxT' ⟨h, hc⟩)
    have hadj : (lattice 4).Adj x y := (SimpleGraph.mem_neighborFinset _ _ _).mp hy
    rw [hAnn x y hadj hnot, mul_zero]
  have hTcard : (T.card : ℝ) ≤ (4 * (L : ℝ) + 3) ^ 4 := by
    have hsub : T ⊆ boxFinset (0 : Site 4) (2 * L + 1) := by
      intro x hxT
      have hx := (Finset.mem_filter.mp hxT).2.2
      rw [mem_boxFinset_zero_iff]
      have h1 : (supNorm x : ℝ) ≤ 2 * (L : ℝ) + 1 := le_trans (supNorm_le_euclidNorm x) hx
      have h2 : ((2 * L + 1 : ℕ) : ℝ) = 2 * (L : ℝ) + 1 := by push_cast; ring
      rw [← h2] at h1
      exact_mod_cast h1
    calc (T.card : ℝ) ≤ ((boxFinset (0 : Site 4) (2 * L + 1)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ = (4 * (L : ℝ) + 3) ^ 4 := by
          rw [card_boxFinset_zero]; push_cast; ring
  have hRHSbound : RHS ≤ 2 ^ 25 * C₁ ^ 2 / (L : ℝ) ^ 2 := by
    rw [hRHS_eq]
    have hterm : ∀ x ∈ T, ∀ y ∈ (lattice 4).neighborFinset x,
        Network.unitCond (lattice 4) x y * (g x ^ 2 + g y ^ 2) * (A x - A y) ^ 2
          ≤ 128 * C₁ ^ 2 / (L : ℝ) ^ 6 := by
      intro x hxT y hy
      have hxlow : (L : ℝ) - 1 ≤ euclidNorm x := (Finset.mem_filter.mp hxT).2.1
      have hadj : (lattice 4).Adj x y := (SimpleGraph.mem_neighborFinset _ _ _).mp hy
      have hdist := hadj_dist x y hadj
      have hylow : (L : ℝ) - 2 ≤ euclidNorm y := by
        have htri : euclidNorm x ≤ euclidNorm y + euclidNorm (x - y) := by
          have h := euclidNorm_add_le y (x - y)
          rwa [show y + (x - y) = x by abel] at h
        linarith
      have hcx : Network.unitCond (lattice 4) x y ≤ 1 := by
        rw [Network.unitCond, if_pos hadj]
      have hgx : g x ^ 2 ≤ 16 * C₁ ^ 2 / (L : ℝ) ^ 4 := by
        have h1 : g x ≤ 4 * C₁ / (L : ℝ) ^ 2 := by
          refine (hgle x).trans ?_
          have hden : (L : ℝ) ^ 2 / 4 ≤ (1 + euclidNorm x) ^ 2 := by
            have h : (L : ℝ) ≤ 1 + euclidNorm x := by linarith
            nlinarith
          calc C₁ / (1 + euclidNorm x) ^ 2 ≤ C₁ / ((L : ℝ) ^ 2 / 4) :=
                div_le_div_of_nonneg_left hC₁pos.le (by positivity) hden
            _ = 4 * C₁ / (L : ℝ) ^ 2 := by ring
        calc g x ^ 2 = g x * g x := by ring
          _ ≤ (4 * C₁ / (L : ℝ) ^ 2) * (4 * C₁ / (L : ℝ) ^ 2) :=
              mul_self_le_mul_self (hg0 x) h1
          _ = 16 * C₁ ^ 2 / (L : ℝ) ^ 4 := by
              rw [div_mul_div_comm]; ring
      have hgy : g y ^ 2 ≤ 16 * C₁ ^ 2 / (L : ℝ) ^ 4 := by
        have h1 : g y ≤ 4 * C₁ / (L : ℝ) ^ 2 := by
          refine (hgle y).trans ?_
          have hden : (L : ℝ) ^ 2 / 4 ≤ (1 + euclidNorm y) ^ 2 := by
            have h : (L : ℝ) / 2 ≤ 1 + euclidNorm y := by linarith
            nlinarith
          calc C₁ / (1 + euclidNorm y) ^ 2 ≤ C₁ / ((L : ℝ) ^ 2 / 4) :=
                div_le_div_of_nonneg_left hC₁pos.le (by positivity) hden
            _ = 4 * C₁ / (L : ℝ) ^ 2 := by ring
        calc g y ^ 2 = g y * g y := by ring
          _ ≤ (4 * C₁ / (L : ℝ) ^ 2) * (4 * C₁ / (L : ℝ) ^ 2) :=
              mul_self_le_mul_self (hg0 y) h1
          _ = 16 * C₁ ^ 2 / (L : ℝ) ^ 4 := by
              rw [div_mul_div_comm]; ring
      have hAdiff : (A x - A y) ^ 2 ≤ (2 / (L : ℝ)) ^ 2 := by
        have h := cutoff_sub_le hL1 hφ hdist
        have h2 : (A x - A y) ^ 2 = |A x - A y| ^ 2 := (sq_abs _).symm
        rw [h2]
        exact pow_le_pow_left₀ (abs_nonneg _) h 2
      have hgxy : g x ^ 2 + g y ^ 2 ≤ 32 * C₁ ^ 2 / (L : ℝ) ^ 4 := by
        calc g x ^ 2 + g y ^ 2
            ≤ 16 * C₁ ^ 2 / (L : ℝ) ^ 4 + 16 * C₁ ^ 2 / (L : ℝ) ^ 4 :=
              add_le_add hgx hgy
          _ = 32 * C₁ ^ 2 / (L : ℝ) ^ 4 := by ring
      have hstep : Network.unitCond (lattice 4) x y * (g x ^ 2 + g y ^ 2) * (A x - A y) ^ 2
          ≤ 1 * (32 * C₁ ^ 2 / (L : ℝ) ^ 4) * (2 / (L : ℝ)) ^ 2 := by
        apply mul_le_mul
        · exact mul_le_mul hcx hgxy (by positivity) (by norm_num)
        · exact hAdiff
        · positivity
        · positivity
      calc _ ≤ 1 * (32 * C₁ ^ 2 / (L : ℝ) ^ 4) * (2 / (L : ℝ)) ^ 2 := hstep
        _ = 128 * C₁ ^ 2 / (L : ℝ) ^ 6 := by ring
    calc ∑ x ∈ T, ∑ y ∈ (lattice 4).neighborFinset x,
          Network.unitCond (lattice 4) x y * (g x ^ 2 + g y ^ 2) * (A x - A y) ^ 2
        ≤ ∑ x ∈ T, ∑ _y ∈ (lattice 4).neighborFinset x, 128 * C₁ ^ 2 / (L : ℝ) ^ 6 :=
          Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun y hy => hterm x hx y hy
      _ = ∑ x ∈ T, 8 * (128 * C₁ ^ 2 / (L : ℝ) ^ 6) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, Graph.Zd.degree_eq]
          norm_num
      _ = 8 * (128 * C₁ ^ 2 / (L : ℝ) ^ 6) * (T.card : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ 8 * (128 * C₁ ^ 2 / (L : ℝ) ^ 6) * (4 * (L : ℝ) + 3) ^ 4 := by
          apply mul_le_mul_of_nonneg_left hTcard; positivity
      _ ≤ 2 ^ 25 * C₁ ^ 2 / (L : ℝ) ^ 2 := by
          have h4 : (4 * (L : ℝ) + 3) ^ 4 ≤ (6 * (L : ℝ)) ^ 4 := by
            apply pow_le_pow_left₀ (by positivity); linarith
          have hstep : 8 * (128 * C₁ ^ 2 / (L : ℝ) ^ 6) * (4 * (L : ℝ) + 3) ^ 4
              ≤ 8 * (128 * C₁ ^ 2 / (L : ℝ) ^ 6) * (6 * (L : ℝ)) ^ 4 :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
          refine hstep.trans ?_
          rw [show 8 * (128 * C₁ ^ 2 / (L : ℝ) ^ 6) * (6 * (L : ℝ)) ^ 4
              = 1327104 * C₁ ^ 2 / (L : ℝ) ^ 2 by field_simp; ring]
          rw [div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [hC₁pos, mul_nonneg (sq_nonneg C₁) (sq_nonneg (L : ℝ))]
  exact hRHSbound

theorem exists_energy_cutField_le :
    ∃ C : ℝ, 0 < C ∧ ∀ r L : ℕ, 2 ≤ L → ∀ φ : ℝ → ℝ, IsCutoff φ →
      ∑' u : Site 4, ∑ i : Fin 4, (cutField r L φ (u + unit i) - cutField r L φ u) ^ 2
        ≤ C / (L : ℝ) ^ 2 := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := exists_srwGreenInf_four_le
  refine ⟨2 ^ 30 * C₁ ^ 2 + 1, by positivity, fun r L hL φ hφ => ?_⟩
  have hL1 : 1 ≤ L := by omega
  have hLpos : (0 : ℝ) < (L : ℝ) := by positivity
  have hL2R : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  set g : Site 4 → ℝ := fun u => killedGreen (box r) 0 u with hgdef
  set A : Site 4 → ℝ := fun u => φ (euclidNorm u / (L : ℝ)) with hAdef
  set S : Finset (Site 4) := boxFinset (0 : Site 4) (r + 1) with hSdef
  have hg0 : ∀ u, 0 ≤ g u := fun u => killedGreen_nonneg (box r) 0 u
  have hgle : ∀ u, g u ≤ C₁ / (1 + euclidNorm u) ^ 2 := fun u =>
    le_trans (killedGreen_le_srwGreenInf (box r) u) (hC₁ u)
  have hA0 : ∀ u, 0 ≤ A u := fun u =>
    (hφ.1 _ (div_nonneg (euclidNorm_nonneg u) hLpos.le)).1
  have hAz : ∀ u, euclidNorm u ≤ (L : ℝ) → A u = 0 := fun u hu =>
    hφ.2.2.1 _ (div_nonneg (euclidNorm_nonneg u) hLpos.le) ((div_le_one hLpos).mpr hu)
  have hAo : ∀ u, 2 * (L : ℝ) ≤ euclidNorm u → A u = 1 := fun u hu =>
    hφ.2.2.2 _ ((le_div_iff₀ hLpos).mpr hu)
  have hsupp : ∀ u : Site 4, u ∉ S →
      (∑ i : Fin 4, (cutField r L φ (u + unit i) - cutField r L φ u) ^ 2) = 0 := by
    intro u hu
    apply Finset.sum_eq_zero
    intro i _
    have hu1 : g u = 0 := by
      apply killedGreen_eq_zero_of_notMem
      intro hmem
      have hmem' : u ∈ boxFinset (0 : Site 4) r := by
        rwa [box_eq_coe_boxFinset r] at hmem
      exact hu (by rw [hSdef]; exact boxFinset_zero_subset (by omega : r ≤ r + 1) hmem')
    have hu2 : g (u + unit i) = 0 := by
      apply killedGreen_eq_zero_of_notMem
      intro hmem
      have hmem' : supNorm (u + unit i) ≤ r := by
        rw [box_eq_coe_boxFinset r] at hmem
        exact mem_boxFinset_zero_iff.mp hmem
      have hgt : r + 1 < supNorm u := by
        have hnot : ¬ supNorm u ≤ r + 1 := by
          intro h
          exact hu (by rw [hSdef, mem_boxFinset_zero_iff]; exact h)
        omega
      have hle : supNorm u ≤ supNorm (u + unit i) + 1 := by
        have h := supNorm_sub_unit_le (u + unit i) i
        rwa [show (u + unit i) - unit i = u by abel] at h
      omega
    have h1 : cutField r L φ (u + unit i) = g (u + unit i) * A (u + unit i) := rfl
    have h2 : cutField r L φ u = g u * A u := rfl
    rw [h1, h2, hu2, hu1]
    ring
  rw [tsum_eq_sum (s := S) hsupp]
  set E1 := ∑ u ∈ S, ∑ i : Fin 4, (g (u + unit i) - g u) ^ 2 * A u ^ 2 with hE1def
  set E2 := ∑ u ∈ S, ∑ i : Fin 4, g (u + unit i) ^ 2 * (A (u + unit i) - A u) ^ 2
    with hE2def
  set LHS := ∑ x ∈ S, ∑ y ∈ (lattice 4).neighborFinset x,
      Network.unitCond (lattice 4) x y * (g x - g y) ^ 2 * A x ^ 2 with hLHSdef
  set RHS := ∑ x ∈ S, ∑ y ∈ (lattice 4).neighborFinset x,
      Network.unitCond (lattice 4) x y * (g x ^ 2 + g y ^ 2) * (A x - A y) ^ 2 with hRHSdef
  have hpoint : ∀ u : Site 4, ∀ i : Fin 4,
      (cutField r L φ (u + unit i) - cutField r L φ u) ^ 2
        ≤ 2 * ((g (u + unit i) - g u) ^ 2 * A u ^ 2)
          + 2 * ((g (u + unit i)) ^ 2 * (A (u + unit i) - A u) ^ 2) := by
    intro u i
    have h1 : cutField r L φ (u + unit i) = g (u + unit i) * A (u + unit i) := rfl
    have h2 : cutField r L φ u = g u * A u := rfl
    rw [h1, h2]
    nlinarith [sq_nonneg ((g (u + unit i) - g u) * A u
      - g (u + unit i) * (A (u + unit i) - A u))]
  have hE_le : (∑ u ∈ S, ∑ i : Fin 4,
        (cutField r L φ (u + unit i) - cutField r L φ u) ^ 2) ≤ 2 * E1 + 2 * E2 := by
    have hsum : (∑ u ∈ S, ∑ i : Fin 4,
          (cutField r L φ (u + unit i) - cutField r L φ u) ^ 2)
        ≤ ∑ u ∈ S, ∑ i : Fin 4, (2 * ((g (u + unit i) - g u) ^ 2 * A u ^ 2)
            + 2 * (g (u + unit i) ^ 2 * (A (u + unit i) - A u) ^ 2)) :=
      Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun i _ => hpoint u i
    have heq : (∑ u ∈ S, ∑ i : Fin 4, (2 * ((g (u + unit i) - g u) ^ 2 * A u ^ 2)
          + 2 * (g (u + unit i) ^ 2 * (A (u + unit i) - A u) ^ 2)))
        = 2 * E1 + 2 * E2 := by
      simp only [hE1def, hE2def, Finset.mul_sum, Finset.sum_add_distrib]
    rw [heq] at hsum
    exact hsum
  have hE1_le : E1 ≤ LHS := by
    rw [hE1def, hLHSdef]
    apply Finset.sum_le_sum
    intro u _
    have hL : (∑ y ∈ (lattice 4).neighborFinset u,
          Network.unitCond (lattice 4) u y * (g u - g y) ^ 2 * A u ^ 2)
        = A u ^ 2 * ∑ i : Fin 4,
            ((g u - g (u + unit i)) ^ 2 + (g u - g (u - unit i)) ^ 2) := by
      rw [show (∑ y ∈ (lattice 4).neighborFinset u,
            Network.unitCond (lattice 4) u y * (g u - g y) ^ 2 * A u ^ 2)
          = (∑ y ∈ (lattice 4).neighborFinset u,
              Network.unitCond (lattice 4) u y * (g u - g y) ^ 2) * A u ^ 2 by
            rw [Finset.sum_mul]]
      rw [neighbor_unitCond_sum u (fun y => (g u - g y) ^ 2)]
      ring
    rw [hL, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have h := mul_nonneg (sq_nonneg (g u - g (u - unit i))) (sq_nonneg (A u))
    nlinarith [sq_nonneg (g (u + unit i) - g u)]
  have hE2_le : E2 ≤ RHS := by
    rw [hE2def, hRHSdef]
    apply Finset.sum_le_sum
    intro u _
    have hR : (∑ y ∈ (lattice 4).neighborFinset u,
          Network.unitCond (lattice 4) u y * (g u ^ 2 + g y ^ 2) * (A u - A y) ^ 2)
        = ∑ i : Fin 4,
            ((g u ^ 2 + g (u + unit i) ^ 2) * (A u - A (u + unit i)) ^ 2
              + (g u ^ 2 + g (u - unit i) ^ 2) * (A u - A (u - unit i)) ^ 2) := by
      rw [show (∑ y ∈ (lattice 4).neighborFinset u,
            Network.unitCond (lattice 4) u y * (g u ^ 2 + g y ^ 2) * (A u - A y) ^ 2)
          = ∑ y ∈ (lattice 4).neighborFinset u,
              Network.unitCond (lattice 4) u y * ((g u ^ 2 + g y ^ 2) * (A u - A y) ^ 2) by
            apply Finset.sum_congr rfl; intro y _; ring]
      rw [neighbor_unitCond_sum u (fun y => (g u ^ 2 + g y ^ 2) * (A u - A y) ^ 2)]
    rw [hR]
    apply Finset.sum_le_sum
    intro i _
    have h := mul_nonneg (add_nonneg (sq_nonneg (g u)) (sq_nonneg (g (u + unit i))))
      (sq_nonneg (A u - A (u + unit i)))
    nlinarith [sq_nonneg (g (u + unit i))]
  have hcacc : LHS ≤ 4 * RHS := by
    rw [hLHSdef, hRHSdef]
    refine caccioppoli_vanishing (G := lattice 4) (c := Network.unitCond (lattice 4))
      Network.isCond_unitCond S ((boxFinset (0 : Site 4) r).erase 0) g A ?_ ?_ ?_ ?_
    · intro x hx
      rw [Network.netLaplacian_unitCond]
      have hxmem : x ∈ box r := by
        rw [box_eq_coe_boxFinset]
        exact (Finset.mem_erase.mp hx).2
      exact laplacian_killedGreen_eq_zero r hxmem (Finset.mem_erase.mp hx).1
    · intro x hx
      by_cases hx0 : x = 0
      · subst hx0
        rw [hAdef]
        simp only [euclidNorm_zero, zero_div]
        rw [hφ.2.2.1 0 le_rfl (by norm_num : (0 : ℝ) ≤ 1)]
        ring
      · have hxnot : x ∉ box r := by
          intro hmem
          have hmem' : x ∈ boxFinset (0 : Site 4) r := by rwa [box_eq_coe_boxFinset r] at hmem
          exact hx (Finset.mem_erase.mpr ⟨hx0, hmem'⟩)
        change killedGreen (box r) 0 x * A x ^ 2 = 0
        rw [killedGreen_eq_zero_of_notMem (box r) hxnot]
        ring
    · intro x hx
      exact boxFinset_zero_subset (by omega : r ≤ r + 1) (Finset.mem_of_mem_erase hx)
    · intro x hx y hxy
      have hxmem : x ∈ boxFinset (0 : Site 4) r := (Finset.mem_erase.mp hx).2
      have hsupx : supNorm x ≤ r := mem_boxFinset_zero_iff.mp hxmem
      obtain ⟨i, hi | hi⟩ := hxy
      · have h1 : supNorm y ≤ supNorm x + 1 := by rw [hi]; exact supNorm_add_unit_le x i
        rw [hSdef, mem_boxFinset_zero_iff]; omega
      · have hy : y = x - unit i := by rw [hi]; abel
        have h1 : supNorm y ≤ supNorm x + 1 := by rw [hy]; exact supNorm_sub_unit_le x i
        rw [hSdef, mem_boxFinset_zero_iff]; omega
  have hRHSbound : RHS ≤ 2 ^ 25 * C₁ ^ 2 / (L : ℝ) ^ 2 := by
    rw [hRHSdef]
    exact energy_rhs_bound C₁ hC₁pos hC₁ r L hL φ hφ

  have hmid : 2 * E1 + 2 * E2 ≤ 10 * RHS := by
    have h1 : 2 * E1 + 2 * E2 ≤ 2 * LHS + 2 * RHS :=
      add_le_add (mul_le_mul_of_nonneg_left hE1_le (by norm_num))
        (mul_le_mul_of_nonneg_left hE2_le (by norm_num))
    have h2 : 2 * LHS + 2 * RHS ≤ 10 * RHS := by
      calc 2 * LHS + 2 * RHS ≤ 2 * (4 * RHS) + 2 * RHS :=
            add_le_add (mul_le_mul_of_nonneg_left hcacc (by norm_num)) le_rfl
        _ = 10 * RHS := by ring
    exact h1.trans h2
  have hstep2 : 10 * RHS ≤ (2 ^ 30 * C₁ ^ 2 + 1) / (L : ℝ) ^ 2 := by
    have h1 : 10 * RHS ≤ 10 * (2 ^ 25 * C₁ ^ 2 / (L : ℝ) ^ 2) := by
      linarith [hRHSbound]
    refine h1.trans ?_
    rw [show 10 * (2 ^ 25 * C₁ ^ 2 / (L : ℝ) ^ 2)
        = (10 * 2 ^ 25 * C₁ ^ 2) / (L : ℝ) ^ 2 by ring]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hC₁pos, mul_nonneg (sq_nonneg C₁) (sq_nonneg (L : ℝ))]
  exact hE_le.trans (hmid.trans hstep2)
private theorem exists_unit_peel4 {u : Site 4} (hu : u ≠ 0) :
    ∃ g : Site 4, graphNorm g = 1 ∧ graphNorm (u - g) + 1 = graphNorm u := by
  classical
  obtain ⟨i, hi⟩ : ∃ i : Fin 4, u i ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hu (funext fun i => hc i)
  set s : ℤ := if 0 < u i then 1 else -1 with hs
  set g : Site 4 := Pi.single i s with hg
  have hsabs : s.natAbs = 1 := by rw [hs]; split <;> simp
  have hg1 : graphNorm g = 1 := by
    rw [hg, graphNorm, Finset.sum_eq_single i]
    · simp [Pi.single_eq_same, hsabs]
    · intro b _ hb; simp [Pi.single_eq_of_ne hb]
    · intro h; exact absurd (Finset.mem_univ i) h
  refine ⟨g, hg1, ?_⟩
  have hsplit : ∀ f : Fin 4 → ℕ,
      ∑ k ∈ (Finset.univ : Finset (Fin 4)).erase i, f k + f i = ∑ k : Fin 4, f k :=
    fun f => Finset.sum_erase_add _ _ (Finset.mem_univ i)
  have he : ∀ k ∈ (Finset.univ : Finset (Fin 4)).erase i,
      ((u - g) k).natAbs = (u k).natAbs := by
    intro k hk
    have hki : k ≠ i := (Finset.mem_erase.mp hk).1
    simp [hg, Pi.sub_apply, hki]
  have hi' : ((u - g) i).natAbs + 1 = (u i).natAbs := by
    have hval : (u - g) i = u i - s := by simp [hg, Pi.sub_apply]
    rw [hval, hs]
    rcases lt_trichotomy (u i) 0 with h | h | h
    · rw [if_neg (not_lt.mpr h.le)]
      omega
    · exact absurd h hi
    · rw [if_pos h]
      omega
  calc graphNorm (u - g) + 1
      = (∑ k ∈ (Finset.univ : Finset (Fin 4)).erase i, ((u - g) k).natAbs
          + ((u - g) i).natAbs) + 1 := by rw [graphNorm, hsplit]
    _ = ∑ k ∈ (Finset.univ : Finset (Fin 4)).erase i, (u k).natAbs + (u i).natAbs := by
        rw [Finset.sum_congr rfl he]; omega
    _ = graphNorm u := by rw [graphNorm, hsplit]

/-- Young's inequality in the form used for the telescoping bound. -/

private theorem sq_add_le_young (a b ε : ℝ) (hε : 0 < ε) :
    (a + b) ^ 2 ≤ (1 + ε) * a ^ 2 + (1 + 1 / ε) * b ^ 2 := by
  have hdiff : (1 + ε) * a ^ 2 + (1 + 1 / ε) * b ^ 2 - (a + b) ^ 2
      = (ε * a - b) ^ 2 / ε := by
    field_simp
    ring
  have hnonneg : 0 ≤ (ε * a - b) ^ 2 / ε := div_nonneg (sq_nonneg _) hε.le
  linarith

/-- The shift-by-`w` squared difference sum is controlled by the sum of squared
unit gradients, with the `ℓ¹` factor `|w|_1²`. -/

private theorem tsum_sub_shift_sq_le_aux (f : Site 4 → ℝ)
    (hf : ∃ s : Finset (Site 4), ∀ u ∉ s, f u = 0) (w : Site 4) :
    ∑' u : Site 4, (f u - f (u - w)) ^ 2
      ≤ (graphNorm w : ℝ) ^ 2
        * ∑' u : Site 4, ∑ i : Fin 4, (f (u + unit i) - f u) ^ 2 := by
  classical
  obtain ⟨s, hs⟩ := hf
  set E : ℝ := ∑' u : Site 4, ∑ i : Fin 4, (f (u + unit i) - f u) ^ 2 with hE
  have hsum_grad : ∀ v : Site 4, Summable (fun u : Site 4 => (f (u + v) - f u) ^ 2) := by
    intro v
    refine summable_of_ne_finset_zero (s := s ∪ s.image (fun x => x - v)) ?_
    intro u hu
    have hu1 : u ∉ s := fun h => hu (Finset.mem_union_left _ h)
    have hu2 : u + v ∉ s := by
      intro h
      exact hu (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨u + v, h, by abel_nf⟩))
    rw [hs u hu1, hs (u + v) hu2]; ring
  have hS : ∀ v : Site 4, Summable (fun u : Site 4 => (f u - f (u - v)) ^ 2) := by
    intro v
    refine summable_of_ne_finset_zero (s := s ∪ s.image (fun x => x + v)) ?_
    intro u hu
    have hu1 : u ∉ s := fun h => hu (Finset.mem_union_left _ h)
    have hu2 : u - v ∉ s := by
      intro h
      exact hu (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨u - v, h, by abel_nf⟩))
    rw [hs u hu1, hs (u - v) hu2]; ring
  have hE_eq : E = ∑ i : Fin 4, ∑' u : Site 4, (f (u + unit i) - f u) ^ 2 := by
    rw [hE]
    exact Summable.tsum_finsetSum (fun i _ => hsum_grad (unit i))
  have hE_nonneg : 0 ≤ E := by
    rw [hE_eq]
    exact Finset.sum_nonneg fun i _ => tsum_nonneg fun u => sq_nonneg _
  have hunit : ∀ g : Site 4, graphNorm g = 1 →
      (∑' u : Site 4, (f u - f (u - g)) ^ 2) ≤ E := by
    intro g hg
    have hex : ∃ (i : Fin 4) (b : ℤ), b.natAbs = 1 ∧ g = Pi.single i b := by
      rw [graphNorm] at hg
      obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero
        (show ∑ k : Fin 4, (g k).natAbs ≠ 0 from by rw [hg]; simp)
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at hg
      have hui : (g i).natAbs = 1 := by omega
      have hzero : ∑ k ∈ Finset.univ.erase i, (g k).natAbs = 0 := by omega
      refine ⟨i, g i, hui, ?_⟩
      funext k
      by_cases hk : k = i
      · subst hk; simp
      · have hk' : (g k).natAbs = 0 := by
          rw [Finset.sum_eq_zero_iff_of_nonneg (fun k _ => Nat.zero_le _)] at hzero
          exact hzero k (by simp [hk])
        simp [hk, Int.natAbs_eq_zero.mp hk']
    obtain ⟨i, b, hb, rfl⟩ := hex
    have hbcase : b = 1 ∨ b = -1 := by omega
    have hle_i : (∑' z : Site 4, (f (z + unit i) - f z) ^ 2) ≤ E := by
      rw [hE_eq]
      exact Finset.single_le_sum
        (f := fun j : Fin 4 => ∑' u : Site 4, (f (u + unit j) - f u) ^ 2)
        (fun j _ => tsum_nonneg fun u => sq_nonneg _) (Finset.mem_univ i)
    rcases hbcase with rfl | rfl
    · have hreindex : (∑' u : Site 4, (f u - f (u - (Pi.single i (1 : ℤ) : Site 4))) ^ 2)
          = ∑' z : Site 4, (f (z + unit i) - f z) ^ 2 := by
        rw [← (Equiv.addRight (unit i)).tsum_eq
          (fun u : Site 4 => (f u - f (u - (Pi.single i (1 : ℤ) : Site 4))) ^ 2)]
        apply tsum_congr
        intro z
        simp only [Equiv.coe_addRight]
        have hsub : (z + unit i) - (Pi.single i (1 : ℤ) : Site 4) = z := by
          rw [show (Pi.single i (1 : ℤ) : Site 4) = unit i from rfl]
          exact add_sub_cancel_right z (unit i)
        rw [hsub]
      rw [hreindex]; exact hle_i
    · have hpt : ∀ u : Site 4,
          (f u - f (u - (Pi.single i (-1 : ℤ) : Site 4))) ^ 2
            = (f (u + unit i) - f u) ^ 2 := by
        intro u
        have hsub : u - (Pi.single i (-1 : ℤ) : Site 4) = u + unit i := by
          funext j
          by_cases hj : j = i
          · subst hj; simp [unit, Pi.single_eq_same]
          · simp [unit, Pi.single_eq_of_ne hj]
        rw [hsub]; ring
      calc (∑' u : Site 4, (f u - f (u - (Pi.single i (-1 : ℤ) : Site 4))) ^ 2)
          = ∑' u : Site 4, (f (u + unit i) - f u) ^ 2 := tsum_congr hpt
        _ ≤ E := hle_i
  have hmain : ∀ n : ℕ, ∀ w : Site 4, graphNorm w = n →
      (∑' u : Site 4, (f u - f (u - w)) ^ 2) ≤ (n : ℝ) ^ 2 * E := by
    intro n
    induction n with
    | zero =>
        intro w hw
        have hw0 : w = 0 := graphNorm_eq_zero_iff.mp hw
        subst hw0
        have hzero : (fun u : Site 4 => (f u - f (u - 0)) ^ 2) = fun _ => (0 : ℝ) := by
          funext u; simp
        rw [hzero, tsum_zero]
        simp
    | succ n ih =>
        intro w hw
        by_cases hw0 : w = 0
        · subst hw0
          rw [graphNorm_zero] at hw
          omega
        · obtain ⟨g, hg1, hg2⟩ := exists_unit_peel4 hw0
          have hw' : graphNorm (w - g) = n := by omega
          set w' : Site 4 := w - g with hw'def
          have hw_eq : w = g + w' := by rw [hw'def]; abel_nf
          by_cases hn : n = 0
          · subst hn
            have hw'zero : w' = 0 := graphNorm_eq_zero_iff.mp (by simpa using hw')
            have hwg : w = g := by rw [hw_eq, hw'zero, add_zero]
            rw [hwg]
            simpa using hunit g hg1
          · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
            set ε : ℝ := (n : ℝ) with hε
            have hεpos : 0 < ε := by rw [hε]; exact hnpos
            set Ashift : Site 4 → ℝ := fun u => f u - f (u - g) with hAshiftdef
            set Bshift : Site 4 → ℝ := fun u => f (u - g) - f (u - g - w') with hBshiftdef
            have hab : ∀ u : Site 4, f u - f (u - w) = Ashift u + Bshift u := by
              intro u
              rw [hw_eq]
              simp only [hAshiftdef, hBshiftdef]
              abel_nf
            have hle : ∀ u : Site 4,
                (f u - f (u - w)) ^ 2
                  ≤ (1 + ε) * Ashift u ^ 2 + (1 + 1 / ε) * Bshift u ^ 2 := by
              intro u
              rw [hab u]
              exact sq_add_le_young (Ashift u) (Bshift u) ε hεpos
            have ha_sum : Summable (fun u : Site 4 => Ashift u ^ 2) := by
              simpa [hAshiftdef] using hS g
            have hb_sum : Summable (fun u : Site 4 => Bshift u ^ 2) := by
              have h := ((Equiv.addRight (-g)).summable_iff
                (f := fun v : Site 4 => (f v - f (v - w')) ^ 2)).mpr (hS w')
              simpa [hBshiftdef, sub_eq_add_neg, Function.comp_def] using h
            have hrhs : Summable (fun u : Site 4 =>
                (1 + ε) * Ashift u ^ 2 + (1 + 1 / ε) * Bshift u ^ 2) :=
              (ha_sum.mul_left (1 + ε)).add (hb_sum.mul_left (1 + 1 / ε))
            have hlhs : Summable (fun u : Site 4 => (f u - f (u - w)) ^ 2) :=
              Summable.of_nonneg_of_le (fun u => sq_nonneg _) hle hrhs
            have hstep := Summable.tsum_le_tsum hle hlhs hrhs
            have hrhs_eval : (∑' u : Site 4,
                  ((1 + ε) * Ashift u ^ 2 + (1 + 1 / ε) * Bshift u ^ 2))
                = (1 + ε) * (∑' u : Site 4, Ashift u ^ 2)
                  + (1 + 1 / ε) * (∑' u : Site 4, Bshift u ^ 2) := by
              rw [Summable.tsum_add (ha_sum.mul_left (1 + ε))
                (hb_sum.mul_left (1 + 1 / ε)), tsum_mul_left, tsum_mul_left]
            rw [hrhs_eval] at hstep
            have hsum_A : (∑' u : Site 4, Ashift u ^ 2)
                = ∑' u : Site 4, (f u - f (u - g)) ^ 2 := by
              apply tsum_congr; intro u; simp [hAshiftdef]
            have hsum_B : (∑' u : Site 4, Bshift u ^ 2)
                = ∑' v : Site 4, (f v - f (v - w')) ^ 2 := by
              have h2 := (Equiv.addRight (-g)).tsum_eq
                (fun v : Site 4 => (f v - f (v - w')) ^ 2)
              simpa [hBshiftdef, sub_eq_add_neg, Function.comp_def] using h2
            have hunitg : (∑' u : Site 4, (f u - f (u - g)) ^ 2) ≤ E := hunit g hg1
            have ihw' : (∑' v : Site 4, (f v - f (v - w')) ^ 2) ≤ (n : ℝ) ^ 2 * E :=
              ih w' hw'
            calc (∑' u : Site 4, (f u - f (u - w)) ^ 2)
                ≤ (1 + ε) * (∑' u : Site 4, Ashift u ^ 2)
                    + (1 + 1 / ε) * (∑' u : Site 4, Bshift u ^ 2) := hstep
              _ = (1 + ε) * (∑' u : Site 4, (f u - f (u - g)) ^ 2)
                    + (1 + 1 / ε) * (∑' v : Site 4, (f v - f (v - w')) ^ 2) := by
                    rw [hsum_A, hsum_B]
              _ ≤ (1 + ε) * E + (1 + 1 / ε) * ((n : ℝ) ^ 2 * E) := by
                    gcongr
              _ ≤ ((n + 1 : ℕ) : ℝ) ^ 2 * E := by
                    rw [hε]
                    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
                    have hid : (1 + (n : ℝ)) * E + (1 + 1 / (n : ℝ)) * ((n : ℝ) ^ 2 * E)
                        = ((n + 1 : ℕ) : ℝ) ^ 2 * E := by
                      push_cast
                      field_simp
                      ring
                    exact hid.le
  exact hmain (graphNorm w) w rfl

theorem tsum_sub_shift_sq_le (f : Site 4 → ℝ)
    (hf : ∃ s : Finset (Site 4), ∀ u ∉ s, f u = 0) (w : Site 4) :
    ∑' u : Site 4, (f u - f (u - w)) ^ 2
      ≤ (graphNorm w : ℝ) ^ 2 * ∑' u : Site 4, ∑ i : Fin 4, (f (u + unit i) - f u) ^ 2 :=
  tsum_sub_shift_sq_le_aux f hf w
private theorem cutField_eq_zero_of_notMem_box (r L : ℕ) (φ : ℝ → ℝ) {u : Site 4}
    (hu : u ∉ boxFinset (0 : Site 4) r) : cutField r L φ u = 0 := by
  have hnot : u ∉ box r := by
    intro hmem
    exact hu (by rwa [box_eq_coe_boxFinset r] at hmem)
  rw [cutField, killedGreen_eq_zero_of_notMem (box r) hnot, zero_mul]

/-- The `ℓ¹` graph norm on `ℤ⁴` is at most twice the Euclidean norm, by
Cauchy-Schwarz. -/

private theorem graphNorm_le_two_mul_euclidNorm (w : Site 4) :
    (graphNorm w : ℝ) ≤ 2 * euclidNorm w := by
  have habs : ((graphNorm w : ℕ) : ℝ) = ∑ i : Fin 4, |(w i : ℝ)| := by
    rw [graphNorm]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Int.cast_abs, ← Int.natCast_natAbs (w i)]
    simp
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 4))
    (fun _ => (1 : ℝ)) (fun i => |(w i : ℝ)|)
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, sq_abs] at hcs
  have hnn : (0 : ℝ) ≤ ∑ i : Fin 4, |(w i : ℝ)| :=
    Finset.sum_nonneg fun i _ => abs_nonneg _
  have hy : (0 : ℝ) ≤ (4 : ℝ) * ∑ i : Fin 4, (w i : ℝ) ^ 2 := by positivity
  have hsqrt : ∑ i : Fin 4, |(w i : ℝ)|
      ≤ Real.sqrt ((4 : ℝ) * ∑ i : Fin 4, (w i : ℝ) ^ 2) :=
    (Real.le_sqrt hnn hy).mpr hcs
  rw [habs]
  calc (∑ i : Fin 4, |(w i : ℝ)|)
      ≤ Real.sqrt ((4 : ℝ) * ∑ i : Fin 4, (w i : ℝ) ^ 2) := hsqrt
    _ = 2 * euclidNorm w := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
          show Real.sqrt (4 : ℝ) = 2 by norm_num, euclidNorm]

theorem exists_tsum_cutField_shift_le :
    ∃ C : ℝ, 0 < C ∧ ∀ r L : ℕ, 2 ≤ L → ∀ φ : ℝ → ℝ, IsCutoff φ →
      ∀ M : ℝ, 1 ≤ M → ∀ w : Site 4, euclidNorm w ≤ M * (L : ℝ) →
        ∑' u : Site 4, (cutField r L φ u - cutField r L φ (u - w)) ^ 2 ≤ C * (1 + M) ^ 4 := by
  obtain ⟨C1, hC1pos, hC1⟩ := exists_energy_cutField_le
  refine ⟨4 * C1, by positivity, fun r L hL φ hφ M hM w hw => ?_⟩
  have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : 0 < L)
  have hsupp : ∃ s : Finset (Site 4), ∀ u ∉ s, cutField r L φ u = 0 :=
    ⟨boxFinset (0 : Site 4) r, fun u hu => cutField_eq_zero_of_notMem_box r L φ hu⟩
  have hshift := tsum_sub_shift_sq_le (cutField r L φ) hsupp w
  have henergy := hC1 r L hL φ hφ
  have hstep1 : ∑' u : Site 4, (cutField r L φ u - cutField r L φ (u - w)) ^ 2
      ≤ (graphNorm w : ℝ) ^ 2 * (C1 / (L : ℝ) ^ 2) :=
    hshift.trans (mul_le_mul_of_nonneg_left henergy (sq_nonneg _))
  have hgn : (graphNorm w : ℝ) ≤ 2 * M * (L : ℝ) := by
    calc (graphNorm w : ℝ) ≤ 2 * euclidNorm w := graphNorm_le_two_mul_euclidNorm w
      _ ≤ 2 * (M * (L : ℝ)) := by linarith
      _ = 2 * M * (L : ℝ) := by ring
  have hgn2 : (graphNorm w : ℝ) ^ 2 ≤ (2 * M * (L : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hgn 2
  have hstep2 : (graphNorm w : ℝ) ^ 2 * (C1 / (L : ℝ) ^ 2)
      ≤ (2 * M * (L : ℝ)) ^ 2 * (C1 / (L : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_right hgn2 (by positivity)
  have hval : (2 * M * (L : ℝ)) ^ 2 * (C1 / (L : ℝ) ^ 2) = 4 * C1 * M ^ 2 := by
    have hLne : (L : ℝ) ≠ 0 := ne_of_gt hLpos
    field_simp
    ring
  have hM2 : M ^ 2 ≤ (1 + M) ^ 4 := by
    nlinarith [hM, sq_nonneg M, sq_nonneg (M ^ 2), sq_nonneg (M + 1), sq_nonneg ((M + 1) ^ 2)]
  calc ∑' u : Site 4, (cutField r L φ u - cutField r L φ (u - w)) ^ 2
      ≤ (graphNorm w : ℝ) ^ 2 * (C1 / (L : ℝ) ^ 2) := hstep1
    _ ≤ (2 * M * (L : ℝ)) ^ 2 * (C1 / (L : ℝ) ^ 2) := hstep2
    _ = 4 * C1 * M ^ 2 := hval
    _ ≤ 4 * C1 * (1 + M) ^ 4 := mul_le_mul_of_nonneg_left hM2 (by positivity)
/-! ### D. The ball-killed Green estimates -/

theorem ballGreenBounds :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ r : ℕ, 2 ≤ r →
      (∀ u : Site 4,
          0 ≤ killedGreen (box r) 0 u ∧
            killedGreen (box r) 0 u ≤ srwGreenInf 4 u ∧
            srwGreenInf 4 u ≤ C / (1 + euclidNorm u) ^ 2) ∧
      (∑' u : Site 4, killedGreen (box r) 0 u ^ 2) ≤ C * Real.log (r : ℝ) ∧
      (∀ L : ℕ, 2 ≤ L →
          (∑' u : {u : Site 4 // euclidNorm u ≤ 2 * (L : ℝ)},
              killedGreen (box r) 0 (u : Site 4) ^ 2) ≤
            C * Real.log (2 * (L : ℝ) + 2)) ∧
      (∀ R : ℕ, 2 ≤ R → ∀ i : Fin 4,
          (∑' u : {u : Site 4 // (R : ℝ) ≤ euclidNorm u ∧ euclidNorm u ≤ 2 * (R : ℝ)},
              (killedGreen (box r) 0 ((u : Site 4) + unit i) -
                killedGreen (box r) 0 (u : Site 4)) ^ 2) ≤ C / (R : ℝ) ^ 2) ∧
      (∀ L : ℕ, 2 ≤ L → ∀ φ : ℝ → ℝ, IsCutoff φ →
          (∀ u : Site 4, |cutField r L φ u| ≤ C / (L : ℝ) ^ 2) ∧
            (∑' u : Site 4, cutField r L φ u ^ 3) ≤ C / (L : ℝ) ^ 2 ∧
            ∀ M : ℝ, 1 ≤ M → ∀ w : Site 4, euclidNorm w ≤ M * (L : ℝ) →
              (∑' u : Site 4, (cutField r L φ u - cutField r L φ (u - w)) ^ 2) ≤
                C * (1 + M) ^ 4) ∧
      (∀ A : ℝ, 1 ≤ A →
          (∀ u : Site 4, |timeTail r A u| ≤ C / (r : ℝ) ^ 2 * Real.exp (-c * A)) ∧
            (∑' u : Site 4, timeTail r A u ^ 2) ≤ C * Real.exp (-c * A)) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := exists_srwGreenInf_four_le
  obtain ⟨C₂, hC₂pos, hC₂⟩ := exists_tsum_killedGreen_sq_le
  obtain ⟨C₃, hC₃pos, hC₃⟩ := exists_tsum_near_killedGreen_sq_le
  obtain ⟨C₄, hC₄pos, hC₄⟩ := exists_annulus_gradient_le
  obtain ⟨C₅₁, hC₅₁pos, hC₅₁⟩ := exists_abs_cutField_le
  obtain ⟨C₅₂, hC₅₂pos, hC₅₂⟩ := exists_tsum_cutField_cube_le
  obtain ⟨C₅₃, hC₅₃pos, hC₅₃⟩ := exists_tsum_cutField_shift_le
  obtain ⟨C₆₁, c₆₁, hC₆₁pos, hc₆₁pos, hC₆₁⟩ := exists_abs_timeTail_le
  obtain ⟨C₆₂, c₆₂, hC₆₂pos, hc₆₂pos, hC₆₂⟩ := exists_tsum_timeTail_sq_le
  let C : ℝ := C₁ + C₂ + C₃ + C₄ + C₅₁ + C₅₂ + C₅₃ + C₆₁ + C₆₂
  let c : ℝ := min c₆₁ c₆₂
  have hCpos : 0 < C := by dsimp only [C]; positivity
  have hcpos : 0 < c := by dsimp only [c]; positivity
  have hc₁ : c ≤ c₆₁ := by dsimp only [c]; exact min_le_left _ _
  have hc₂ : c ≤ c₆₂ := by dsimp only [c]; exact min_le_right _ _
  have hC₁C : C₁ ≤ C := by
    dsimp only [C]
    linarith [hC₂pos, hC₃pos, hC₄pos,
      hC₅₁pos, hC₅₂pos, hC₅₃pos, hC₆₁pos, hC₆₂pos]
  have hC₂C : C₂ ≤ C := by
    dsimp only [C]
    linarith [hC₁pos, hC₃pos, hC₄pos,
      hC₅₁pos, hC₅₂pos, hC₅₃pos, hC₆₁pos, hC₆₂pos]
  have hC₃C : C₃ ≤ C := by
    dsimp only [C]
    linarith [hC₁pos, hC₂pos, hC₄pos,
      hC₅₁pos, hC₅₂pos, hC₅₃pos, hC₆₁pos, hC₆₂pos]
  have hC₄C : C₄ ≤ C := by
    dsimp only [C]
    linarith [hC₁pos, hC₂pos, hC₃pos,
      hC₅₁pos, hC₅₂pos, hC₅₃pos, hC₆₁pos, hC₆₂pos]
  have hC₅₁C : C₅₁ ≤ C := by
    dsimp only [C]
    linarith [hC₁pos, hC₂pos, hC₃pos,
      hC₄pos, hC₅₂pos, hC₅₃pos, hC₆₁pos, hC₆₂pos]
  have hC₅₂C : C₅₂ ≤ C := by
    dsimp only [C]
    linarith [hC₁pos, hC₂pos, hC₃pos,
      hC₄pos, hC₅₁pos, hC₅₃pos, hC₆₁pos, hC₆₂pos]
  have hC₅₃C : C₅₃ ≤ C := by
    dsimp only [C]
    linarith [hC₁pos, hC₂pos, hC₃pos,
      hC₄pos, hC₅₁pos, hC₅₂pos, hC₆₁pos, hC₆₂pos]
  have hC₆₁C : C₆₁ ≤ C := by
    dsimp only [C]
    linarith [hC₁pos, hC₂pos, hC₃pos,
      hC₄pos, hC₅₁pos, hC₅₂pos, hC₅₃pos, hC₆₂pos]
  have hC₆₂C : C₆₂ ≤ C := by
    dsimp only [C]
    linarith [hC₁pos, hC₂pos, hC₃pos,
      hC₄pos, hC₅₁pos, hC₅₂pos, hC₅₃pos, hC₆₁pos]
  refine ⟨C, c, hCpos, hcpos, fun r hr => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro u
    exact ⟨killedGreen_nonneg (box r) 0 u, killedGreen_le_srwGreenInf (box r) u,
      (hC₁ u).trans (div_le_div_of_nonneg_right hC₁C (by positivity))⟩
  · have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast (show 1 ≤ r by omega)
    exact (hC₂ r hr).trans (mul_le_mul_of_nonneg_right hC₂C (Real.log_nonneg hr1))
  · intro L hL
    have hL1 : (1 : ℝ) ≤ 2 * (L : ℝ) + 2 := by
      have hL2 : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
      linarith
    exact (hC₃ r L hL).trans
      (mul_le_mul_of_nonneg_right hC₃C (Real.log_nonneg hL1))
  · intro R hR i
    exact (hC₄ r R (by omega) i).trans
      (div_le_div_of_nonneg_right hC₄C (by positivity))
  · intro L hL φ hφ
    exact ⟨fun u => (hC₅₁ r L hL φ hφ u).trans
        (div_le_div_of_nonneg_right hC₅₁C (by positivity)),
      (hC₅₂ r L hL φ hφ).trans
        (div_le_div_of_nonneg_right hC₅₂C (by positivity)),
      fun M hM w hw => (hC₅₃ r L hL φ hφ M hM w hw).trans
        (mul_le_mul_of_nonneg_right hC₅₃C (by positivity))⟩
  · intro A hA
    have hA0 : (0 : ℝ) ≤ A := by linarith
    have harg₁ : -c₆₁ * A ≤ -c * A := by
      have hmono : c * A ≤ c₆₁ * A := mul_le_mul_of_nonneg_right hc₁ hA0
      linarith
    have harg₂ : -c₆₂ * A ≤ -c * A := by
      have hmono : c * A ≤ c₆₂ * A := mul_le_mul_of_nonneg_right hc₂ hA0
      linarith
    exact ⟨fun u => (hC₆₁ r hr A hA u).trans
        (mul_le_mul (div_le_div_of_nonneg_right hC₆₁C (by positivity))
          (Real.exp_le_exp.mpr harg₁) (Real.exp_pos _).le
          (div_nonneg hCpos.le (by positivity))),
      (hC₆₂ r hr A hA).trans
        (mul_le_mul hC₆₂C (Real.exp_le_exp.mpr harg₂) (Real.exp_pos _).le hCpos.le)⟩
end LatticeProb.BallGreen
