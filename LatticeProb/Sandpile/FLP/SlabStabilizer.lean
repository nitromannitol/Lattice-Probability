import LatticeProb.Sandpile.FLP.OneDimensional
import LatticeProb.Sandpile.Toppling

/-!
# Slab stabilizers

For a background height `d ≤ h ≤ 2d - 2` and a radius `ρ ≥ 0`, Fey, Levine and Peres
(A. Fey, L. Levine and Y. Peres, *Growth rates and explosions in sandpiles*, J. Stat. Phys. 138
(2010), 143–159, Section 3.2) build a nonnegative function of one coordinate whose
`d`-dimensional Laplacian is the profile

* `2(d - 1 - h)` at `0`,
* `d - 1 - h` for `0 < |t| < r₀`,
* `2d - 1 - h` for `r₀ ≤ |t| < r₁`,
* `0` for `|t| ≥ r₁`,

where `r₀` is the smallest positive multiple of `2d - 1 - h` exceeding `ρ` (`flpR0`) and
`r₁ = d r₀ / (2d - 1 - h)` (`flpR1`). The profile has total mass `2(r₁(2d - 1 - h) - d r₀) = 0`
and is even.

The stabilizer is written in closed form, `g(t) = (2d - 1 - h) T(r₁ - |t|) - d T(r₀ - |t|)` with
the triangular numbers `T(s) = ∑_{0 ≤ k < s} k` (`tri`), whose second difference is the
indicator of `s ≥ 1` (`tri_secondDiff`). It vanishes for `|t| ≥ r₁ - 1`, and it is nonnegative
by the minimum principle `nonneg_of_secondDiff`: where `g < 0` one has `|t| < r₀`, and there the
profile is negative. The function `x ↦ g(x_i)` has Laplacian `profile(x_i)`
(`exists_slabStabilizer`).
-/

namespace LatticeProb.Sandpile.FLP

open LatticeProb LatticeProb.Sandpile

/-- `r₀`: the smallest positive multiple of `2d - 1 - h` exceeding `ρ`, and
`r₁ = d r₀ / (2d - 1 - h)` (`flpR1`). -/
noncomputable def flpR0 (d : ℕ) (h : ℤ) (ρ : ℝ) : ℕ :=
  (⌊ρ / (2 * (d : ℝ) - 1 - h)⌋₊ + 1) * (2 * (d : ℤ) - 1 - h).toNat

/-- `r₁ = d r₀ / (2d - 1 - h)`, where `r₀ = flpR0 d h ρ` is the smallest positive multiple of
`2d - 1 - h` exceeding `ρ`. -/
noncomputable def flpR1 (d : ℕ) (h : ℤ) (ρ : ℝ) : ℕ :=
  d * (⌊ρ / (2 * (d : ℝ) - 1 - h)⌋₊ + 1)

/-- The one-dimensional profile of the slab stabilizer. -/
def flpProfile (d : ℕ) (h : ℤ) (r₀ r₁ : ℕ) (t : ℤ) : ℤ :=
  if t = 0 then 2 * ((d : ℤ) - 1 - h) else if |t| < r₀ then (d : ℤ) - 1 - h
  else if |t| < r₁ then 2 * (d : ℤ) - 1 - h else 0

private theorem toNat_cast_eq {d : ℕ} {h : ℤ} (hh : h ≤ 2 * (d : ℤ) - 2) :
    (((2 * (d : ℤ) - 1 - h).toNat : ℕ) : ℤ) = 2 * (d : ℤ) - 1 - h :=
  Int.toNat_of_nonneg (by omega)

private theorem toNat_cast_eq_real {d : ℕ} {h : ℤ} (hh : h ≤ 2 * (d : ℤ) - 2) :
    (((2 * (d : ℤ) - 1 - h).toNat : ℕ) : ℝ) = 2 * (d : ℝ) - 1 - h := by
  rw [← Int.cast_natCast, toNat_cast_eq hh]
  push_cast
  ring

theorem flpR0_spec (d : ℕ) (h : ℤ) (hh : h ≤ 2 * (d : ℤ) - 2) (ρ : ℝ) :
    ρ < flpR0 d h ρ ∧ (2 * (d : ℤ) - 1 - h) ∣ (flpR0 d h ρ : ℤ) ∧
    (flpR1 d h ρ : ℤ) * (2 * (d : ℤ) - 1 - h) = d * flpR0 d h ρ := by
  have hqR : (0 : ℝ) < 2 * (d : ℝ) - 1 - h := by
    have : (h : ℝ) ≤ 2 * (d : ℝ) - 2 := by exact_mod_cast hh
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [flpR0, Nat.cast_mul, toNat_cast_eq_real hh, Nat.cast_add, Nat.cast_one,
      ← div_lt_iff₀ hqR]
    exact Nat.lt_floor_add_one _
  · rw [flpR0, Nat.cast_mul, toNat_cast_eq hh]
    exact Dvd.intro_left _ rfl
  · rw [flpR0, flpR1, Nat.cast_mul, Nat.cast_mul, toNat_cast_eq hh]
    ring

/-- `r₀` is the smallest positive multiple of `2d - 1 - h` exceeding `ρ`. -/
theorem flpR0_le_of_lt (d : ℕ) (h : ℤ) (hh : h ≤ 2 * (d : ℤ) - 2) (ρ : ℝ) {k : ℕ} (hk : 0 < k)
    (hρk : ρ < k * (2 * (d : ℝ) - 1 - h)) :
    flpR0 d h ρ ≤ k * (2 * (d : ℤ) - 1 - h).toNat := by
  have hqR : (0 : ℝ) < 2 * (d : ℝ) - 1 - h := by
    have : (h : ℝ) ≤ 2 * (d : ℝ) - 2 := by exact_mod_cast hh
    linarith
  rw [flpR0]
  refine Nat.mul_le_mul_right _ ?_
  rcases Nat.eq_zero_or_pos ⌊ρ / (2 * (d : ℝ) - 1 - h)⌋₊ with h0 | h0
  · omega
  · by_contra hlt
    have hle : k ≤ ⌊ρ / (2 * (d : ℝ) - 1 - h)⌋₊ := by omega
    have hfl := (Nat.le_floor_iff' (Nat.pos_iff_ne_zero.mp hk)).mp hle
    rw [le_div_iff₀ hqR] at hfl
    linarith

theorem flpR1_le (d : ℕ) (h : ℤ) (_hdh : (d : ℤ) ≤ h) (hh : h ≤ 2 * (d : ℤ) - 2) (ρ : ℝ)
    (hρ : 0 ≤ ρ) :
    (flpR1 d h ρ : ℝ) ≤ d * (ρ / (2 * (d : ℝ) - 1 - h) + 1) := by
  have hqR : (0 : ℝ) < 2 * (d : ℝ) - 1 - h := by
    have : (h : ℝ) ≤ 2 * (d : ℝ) - 2 := by exact_mod_cast hh
    linarith
  rw [flpR1, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  gcongr
  exact Nat.floor_le (div_nonneg hρ hqR.le)

/-- The triangular numbers `T(s) = ∑_{0 ≤ k < s} k`, equal to `s (s - 1) / 2` for `s ≥ 0` and
to `0` for `s < 0`. -/
def tri (s : ℤ) : ℤ := ∑ k ∈ Finset.range s.toNat, (k : ℤ)

theorem tri_succ (s : ℤ) : tri (s + 1) = tri s + s.toNat := by
  unfold tri
  rcases le_or_gt 0 s with hs | hs
  · rw [show (s + 1).toNat = s.toNat + 1 by omega, Finset.sum_range_succ]
  · rw [show (s + 1).toNat = 0 by omega, show s.toNat = 0 by omega]
    simp

theorem tri_secondDiff (s : ℤ) :
    tri (s - 1) + tri (s + 1) - 2 * tri s = if 1 ≤ s then 1 else 0 := by
  have h1 := tri_succ s
  have h2 := tri_succ (s - 1)
  rw [sub_add_cancel] at h2
  split_ifs <;> omega

theorem tri_nonneg (s : ℤ) : 0 ≤ tri s :=
  Finset.sum_nonneg fun k _ => Int.natCast_nonneg k

theorem tri_eq_zero {s : ℤ} (hs : s ≤ 1) : tri s = 0 :=
  Finset.sum_eq_zero fun k hk => by
    rw [Finset.mem_range] at hk
    have : k = 0 := by omega
    simp [this]

/-- For `t ≠ 0` the absolute values `|t + 1|` and `|t - 1|` are `|t| ± 1`. -/
theorem tri_abs_add_tri_abs (r t : ℤ) (ht : t ≠ 0) :
    tri (r - |t + 1|) + tri (r - |t - 1|) = tri (r - |t| - 1) + tri (r - |t| + 1) := by
  rcases lt_or_gt_of_ne ht with ht | ht
  · rw [abs_of_nonpos (by omega : t + 1 ≤ 0), abs_of_neg (by omega : t - 1 < 0), abs_of_neg ht,
      add_comm (tri _)]
    congr 2 <;> ring
  · rw [abs_of_pos (by omega : 0 < t + 1), abs_of_nonneg (by omega : 0 ≤ t - 1), abs_of_pos ht]
    congr 2 <;> ring

theorem exists_slabStabilizer (d : ℕ) (h : ℤ) (hdh : (d : ℤ) ≤ h) (hh : h ≤ 2 * (d : ℤ) - 2)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ∃ g : ℤ → ℤ, (∀ t, 0 ≤ g t) ∧ (∀ t, (flpR1 d h ρ : ℤ) - 1 ≤ |t| → g t = 0) ∧
      ∀ (i : Fin d) (x : Site d),
        lap (fun y : Site d => g (y i)) x = flpProfile d h (flpR0 d h ρ) (flpR1 d h ρ) (x i) := by
  obtain ⟨hρ0, -, hspec⟩ := flpR0_spec d h hh ρ
  set r₀ : ℕ := flpR0 d h ρ
  set r₁ : ℕ := flpR1 d h ρ
  have hr₀1 : 1 ≤ (r₀ : ℤ) := by
    have : (0 : ℝ) < r₀ := hρ.trans_lt hρ0
    exact_mod_cast (Nat.cast_pos.mp this : 0 < r₀)
  have hr₀₁ : (r₀ : ℤ) ≤ r₁ := by
    by_contra hlt
    push Not at hlt
    nlinarith
  obtain ⟨g, hg⟩ : ∃ g : ℤ → ℤ, ∀ t,
      g t = (2 * (d : ℤ) - 1 - h) * tri (r₁ - |t|) - d * tri (r₀ - |t|) := ⟨_, fun _ => rfl⟩
  have hΔ : ∀ t, g (t + 1) - 2 * g t + g (t - 1) = flpProfile d h r₀ r₁ t := by
    intro t
    rw [hg, hg, hg]
    by_cases ht : t = 0
    · subst ht
      have e₁ := tri_succ ((r₁ : ℤ) - 1)
      have e₀ := tri_succ ((r₀ : ℤ) - 1)
      rw [sub_add_cancel, Int.toNat_of_nonneg (by omega)] at e₁
      rw [sub_add_cancel, Int.toNat_of_nonneg (by omega)] at e₀
      simp only [flpProfile, ite_true, zero_add, zero_sub, abs_neg, abs_one,
        abs_zero, sub_zero]
      linear_combination (-2 * (2 * (d : ℤ) - 1 - h)) * e₁ + (2 * (d : ℤ)) * e₀ - 2 * hspec
    · have a₁ := tri_abs_add_tri_abs r₁ t ht
      have a₀ := tri_abs_add_tri_abs r₀ t ht
      have s₁ := tri_secondDiff ((r₁ : ℤ) - |t|)
      have s₀ := tri_secondDiff ((r₀ : ℤ) - |t|)
      simp only [flpProfile, ite_eq_right ht]
      split_ifs at s₁ s₀ ⊢ <;>
        first
        | (exfalso; omega)
        | linear_combination (2 * (d : ℤ) - 1 - h) * (a₁ + s₁) - (d : ℤ) * (a₀ + s₀)
  have hzero : ∀ t, (r₁ : ℤ) - 1 ≤ |t| → g t = 0 := by
    intro t ht
    rw [hg, tri_eq_zero (by omega), tri_eq_zero (by omega)]
    ring
  refine ⟨g, fun t => ?_, hzero, fun i x => ?_⟩
  · have hneg : ∀ x, g x < 0 → flpProfile d h r₀ r₁ x ≤ 0 := by
      intro x hx
      have hx₀ : |x| < r₀ := by
        by_contra hge
        push Not at hge
        rw [hg, tri_eq_zero (s := (r₀ : ℤ) - |x|) (by omega)] at hx
        have := tri_nonneg ((r₁ : ℤ) - |x|)
        nlinarith
      unfold flpProfile
      split_ifs <;> omega
    refine nonneg_of_secondDiff (r₁ : ℤ) hΔ (fun z hz => hzero z ?_) hneg t
    have := le_abs_self z
    have := neg_abs_le z
    omega
  · rw [lap_eq_sum_second_diff, Finset.sum_eq_single i]
    · simp only [unit, Pi.add_apply, Pi.sub_apply, Pi.single_eq_same]
      linarith [hΔ (x i)]
    · intro j _ hji
      simp only [unit, Pi.add_apply, Pi.sub_apply, Pi.single_eq_of_ne (Ne.symm hji), add_zero,
        sub_zero]
      ring
    · simp

end LatticeProb.Sandpile.FLP
