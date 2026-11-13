import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Additive functions on the half-line with values in `ℝ≥0∞`

A function `m : ℝ → ℝ≥0∞` which is additive on `[0, ∞)`, `m (a + b) = m a + m b` for `a, b ≥ 0`, is linear there:
`m b = b * m 1` for every `b > 0`. No finiteness or regularity is assumed: additivity with nonnegative values
forces monotonicity, and a monotone solution of the Cauchy functional equation is linear (also when `m 1 = ∞`).

* `monotoneOn_of_add`: an additive function on `[0, ∞)` with values in `ℝ≥0∞` is monotone there;
* `eq_ofReal_mul_of_add`: it is `b ↦ b * m 1` on `(0, ∞)`.
-/

open Filter Topology
open scoped ENNReal

namespace LatticeProb

variable {m : ℝ → ℝ≥0∞}

/-- An additive function on `[0, ∞)` with values in `ℝ≥0∞` is monotone on `[0, ∞)`. -/
theorem monotoneOn_of_add (hadd : ∀ a b, 0 ≤ a → 0 ≤ b → m (a + b) = m a + m b) :
    MonotoneOn m (Set.Ici 0) := by
  intro a ha b _ hab
  have h := hadd a (b - a) ha (sub_nonneg.2 hab)
  rw [add_sub_cancel] at h
  rw [h]
  exact le_self_add

/-- **Cauchy's functional equation on the half-line, with values in `ℝ≥0∞`.** If `m : ℝ → ℝ≥0∞` is additive on
`[0, ∞)`, then `m b = b * m 1` for every `b > 0`. -/
theorem eq_ofReal_mul_of_add (hadd : ∀ a b, 0 ≤ a → 0 ≤ b → m (a + b) = m a + m b) {b : ℝ} (hb : 0 < b) :
    m b = ENNReal.ofReal b * m 1 := by
  have hmono := monotoneOn_of_add hadd
  have h0b : (0 : ℝ) ≤ b := hb.le
  by_cases h0 : m 0 = ⊤
  · have hmb : m b = ⊤ := by
      have h := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 h0b) h0b
      rw [h0] at h
      exact top_unique h
    have hm1 : m 1 = ⊤ := by
      have h := hmono (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 zero_le_one) zero_le_one
      rw [h0] at h
      exact top_unique h
    rw [hmb, hm1, ENNReal.mul_top (ENNReal.ofReal_pos.2 hb).ne']
  have hm0 : m 0 = 0 := by
    have h := hadd 0 0 le_rfl le_rfl
    rw [add_zero] at h
    exact (ENNReal.add_right_inj h0).1 (by rw [add_zero]; exact h.symm)
  have hnat : ∀ (n : ℕ) (x : ℝ), 0 ≤ x → m (n * x) = n * m x := by
    intro n x hx
    induction n with
    | zero => simp [hm0]
    | succ n ih =>
      rw [Nat.cast_succ, add_mul, one_mul, hadd _ _ (by positivity) hx, ih, Nat.cast_succ, add_mul, one_mul]
  have hval : ∀ (n k : ℕ), 0 < n → m ((k : ℝ) / n) = ENNReal.ofReal ((k : ℝ) / n) * m 1 := by
    intro n k hn
    have hn' : (0 : ℝ) < n := Nat.cast_pos.2 hn
    have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast hn.ne'
    have hgrid : (n : ℝ≥0∞) * m ((k : ℝ) / n) = k * m 1 := by
      rw [← hnat n _ (by positivity), show (n : ℝ) * ((k : ℝ) / n) = k by field_simp]
      simpa using hnat k 1 zero_le_one
    rw [ENNReal.ofReal_div_of_pos hn', ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
      div_eq_mul_inv (k : ℝ≥0∞) (n : ℝ≥0∞),
      mul_right_comm, ← hgrid, mul_right_comm, ENNReal.mul_inv_cancel hn0 (ENNReal.natCast_ne_top n), one_mul]
  have hlim : ∀ g : ℝ → ℕ, Tendsto (fun x : ℝ => (g x : ℝ) / x) atTop (𝓝 b) →
      Tendsto (fun n : ℕ => ENNReal.ofReal ((g n : ℝ) / n) * m 1) atTop (𝓝 (ENNReal.ofReal b * m 1)) := by
    intro g hg
    exact ENNReal.Tendsto.mul_const
      ((ENNReal.continuous_ofReal.tendsto b).comp (hg.comp tendsto_natCast_atTop_atTop))
      (Or.inl (ENNReal.ofReal_pos.2 hb).ne')
  refine le_antisymm ?_ ?_
  · refine ge_of_tendsto (hlim (fun x => ⌈b * x⌉₊) (tendsto_nat_ceil_mul_div_atTop h0b)) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
    rw [← hval n _ (by omega)]
    exact hmono (Set.mem_Ici.2 h0b) (Set.mem_Ici.2 (by positivity)) ((le_div_iff₀ hn').2 (Nat.le_ceil _))
  · refine le_of_tendsto (hlim (fun x => ⌊b * x⌋₊) (tendsto_nat_floor_mul_div_atTop h0b)) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := Nat.cast_pos.2 (by omega)
    rw [← hval n _ (by omega)]
    exact hmono (Set.mem_Ici.2 (by positivity)) (Set.mem_Ici.2 h0b)
      ((div_le_iff₀ hn').2 (Nat.floor_le (by positivity)))

end LatticeProb
