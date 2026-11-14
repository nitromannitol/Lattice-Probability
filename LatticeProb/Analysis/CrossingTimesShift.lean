import LatticeProb.Analysis.CrossingTimes

/-!
# Shifts, translations and scalings of crossing times

For a path `f : ℝ≥0 → E` the successive `ε`-crossing times `σ_k = crossTime ε f k` satisfy:

* **Restart identity** (`crossTime_succ_eq_add`): `σ_{k+1} = σ_k + σ_1 (θ_{σ_k} f)`, where
  `θ_a f = f (a + ·)` is the shifted path (`⊤` if `σ_k = ⊤`).  The increments of the crossing
  times are the first crossing times of the successively restarted paths.
* **Translation** (`crossTime_sub_const`): subtracting a constant does not change the crossing times.
* **Scaling in space** (`crossTime_smul`): `σ_k^{c ε}(c • f) = σ_k^ε(f)` for `c > 0`.
* **Scaling in time** (`mul_crossTime_comp_mul`): `c * σ_k^ε (f (c ·)) = σ_k^ε (f)` for `c ≠ 0`.
* **Brownian scaling** (`crossTime_scaled`): `c² σ_k^1 (c⁻¹ • f (c² ·)) = σ_k^c (f)`.
-/

open scoped NNReal ENNReal

namespace LatticeProb

section Shift

variable {E : Type*} [PseudoMetricSpace E]

theorem crossTime_one_eq (ε : ℝ) (f : ℝ≥0 → E) : crossTime ε f 1 = nextCrossTime ε f 0 := by
  rw [crossTime_succ, crossTime_zero]

/-- The first crossing after the time `a + b` is `a` plus the first crossing after `b` of the path
shifted by `a`. -/
theorem nextCrossTime_add_coe (ε : ℝ) (f : ℝ≥0 → E) (a : ℝ≥0) (b : ℝ≥0∞) :
    nextCrossTime ε f ((a : ℝ≥0∞) + b) =
      (a : ℝ≥0∞) + nextCrossTime ε (fun s => f (a + s)) b := by
  rcases eq_or_ne b ⊤ with rfl | hb
  · simp [nextCrossTime_top]
  lift b to ℝ≥0 using hb
  rw [← ENNReal.coe_add]
  apply le_antisymm
  · simp only [nextCrossTime, ENNReal.toNNReal_coe]
    rw [ENNReal.add_iInf]
    refine le_iInf fun s => ?_
    rw [ENNReal.add_iInf]
    refine le_iInf fun hs => ?_
    refine (nextCrossTime_le_of_lt (s := a + s) ?_ ?_).trans (le_of_eq (by rw [ENNReal.coe_add]))
    · rw [ENNReal.coe_lt_coe]
      exact (add_lt_add_iff_left a).2 (by exact_mod_cast hs.1)
    · simpa only [ENNReal.toNNReal_coe] using hs.2
  · rw [le_nextCrossTime_coe_iff]
    intro s hs hdist
    have has : a ≤ s := (le_add_right le_rfl).trans hs.le
    have hb' : (b : ℝ≥0∞) < ((s - a : ℝ≥0) : ℝ≥0∞) := by
      rw [ENNReal.coe_lt_coe]
      exact lt_tsub_iff_left.2 hs
    have h3 := nextCrossTime_le_of_lt (ε := ε) (f := fun s' => f (a + s')) (a := (b : ℝ≥0∞))
      (s := s - a) hb' (by simpa [add_tsub_cancel_of_le has] using hdist)
    calc (a : ℝ≥0∞) + nextCrossTime ε (fun s => f (a + s)) b
        ≤ (a : ℝ≥0∞) + ((s - a : ℝ≥0) : ℝ≥0∞) := by gcongr
      _ = s := by rw [← ENNReal.coe_add, add_tsub_cancel_of_le has]

/-- **Restart identity.**  The `(k+1)`-st crossing time is the `k`-th plus the first crossing time of
the path restarted at the `k`-th (`⊤` if the `k`-th is `⊤`). -/
theorem crossTime_succ_eq_add (ε : ℝ) (f : ℝ≥0 → E) (k : ℕ) :
    crossTime ε f (k + 1) =
      crossTime ε f k + crossTime ε (fun s => f ((crossTime ε f k).toNNReal + s)) 1 := by
  rcases eq_or_ne (crossTime ε f k) ⊤ with h | h
  · rw [crossTime_succ, h, nextCrossTime_top]
    simp
  · obtain ⟨a, ha⟩ : ∃ a : ℝ≥0, crossTime ε f k = a :=
      ⟨_, (ENNReal.coe_toNNReal h).symm⟩
    rw [crossTime_succ, crossTime_one_eq, ha, ENNReal.toNNReal_coe]
    simpa using nextCrossTime_add_coe ε f a 0

end Shift

section Scaling

theorem eq_of_forall_le_coe_iff {x y : ℝ≥0∞} (h : ∀ u : ℝ≥0, x ≤ u ↔ y ≤ u) : x = y := by
  refine le_antisymm ?_ ?_
  · rcases eq_or_ne y ⊤ with rfl | hy
    · exact le_top
    · calc x ≤ (y.toNNReal : ℝ≥0∞) := (h _).2 (ENNReal.coe_toNNReal hy).ge
        _ = y := ENNReal.coe_toNNReal hy
  · rcases eq_or_ne x ⊤ with rfl | hx
    · exact le_top
    · calc y ≤ (x.toNNReal : ℝ≥0∞) := (h _).1 (ENNReal.coe_toNNReal hx).ge
        _ = x := ENNReal.coe_toNNReal hx

variable {E : Type*} [PseudoMetricSpace E]

/-- **Scaling in time.** -/
theorem mul_crossTime_comp_mul {ε : ℝ} (f : ℝ≥0 → E) {c : ℝ≥0} (hc : c ≠ 0) (k : ℕ) :
    (c : ℝ≥0∞) * crossTime ε (fun s => f (c * s)) k = crossTime ε f k := by
  have hcpos : 0 < c := pos_iff_ne_zero.2 hc
  have hτm : StrictMono fun s : ℝ≥0 => c * s := fun s t h => mul_lt_mul_of_pos_left h hcpos
  have hτc : Continuous fun s : ℝ≥0 => c * s := continuous_const.mul continuous_id
  refine eq_of_forall_le_coe_iff fun u => ?_
  have key := crossTime_comp_le_iff (τ := fun s : ℝ≥0 => c * s) hτc hτm (by simp) ε f k (u / c)
  have hmul : c * (u / c) = u := mul_div_cancel₀ u hc
  simp only [hmul] at key
  change crossTime ε (fun s => f (c * s)) k ≤ ((u / c : ℝ≥0) : ℝ≥0∞) ↔ _ at key
  rw [← key, ENNReal.coe_div hc]
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hc)) (Or.inl ENNReal.coe_ne_top),
    mul_comm]

end Scaling

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
/-- Subtracting a constant from a path does not change its crossing times. -/
theorem crossTime_sub_const (ε : ℝ) (f : ℝ≥0 → E) (v : E) :
    crossTime ε (fun s => f s - v) = crossTime ε f :=
  crossTime_comp_isometry (φ := fun x : E => x - v) (IsometryEquiv.subRight v).isometry ε f

/-- **Scaling in space.** -/
theorem crossTime_smul (ε : ℝ) {c : ℝ} (hc : 0 < c) (f : ℝ≥0 → E) (k : ℕ) :
    crossTime (c * ε) (fun s => c • f s) k = crossTime ε f k := by
  have h : nextCrossTime (c * ε) (fun s => c • f s) = nextCrossTime ε f := by
    funext a
    simp only [nextCrossTime, dist_smul₀, Real.norm_eq_abs, abs_of_pos hc,
      mul_le_mul_iff_right₀ hc]
  simp only [crossTime, h]

/-- **Brownian scaling of the crossing times.** -/
theorem crossTime_scaled (f : ℝ≥0 → E) {c : ℝ≥0} (hc : c ≠ 0) (k : ℕ) :
    ((c ^ 2 : ℝ≥0) : ℝ≥0∞) * crossTime 1 (fun s => (c : ℝ)⁻¹ • f (c ^ 2 * s)) k =
      crossTime (c : ℝ) f k := by
  have hc' : (c : ℝ) ≠ 0 := by exact_mod_cast hc
  have hcpos : 0 < (c : ℝ)⁻¹ := inv_pos.2 (by positivity)
  have h1 := crossTime_smul (c : ℝ) hcpos (fun s => f (c ^ 2 * s)) k
  rw [inv_mul_cancel₀ hc'] at h1
  rw [h1]
  exact mul_crossTime_comp_mul (ε := (c : ℝ)) f (pow_ne_zero 2 hc) k

end Normed

end LatticeProb
