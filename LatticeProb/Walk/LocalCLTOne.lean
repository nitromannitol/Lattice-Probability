/-
The one-dimensional local central limit theorem.

At an even time `2m` and an even site `2k` the one-dimensional kernel is
`C(2m, m+k)/4^m` (`LatticeProb.srwHeat_one_two_mul_binom`), and that factors as
the ratio `C(2m,m+k)/C(2m,m)` times the peak value `C(2m,m)/4^m`.  The ratio is
`exp(-k^2/m)` uniformly on the diffusive scale `|k| \leq A\sqrt m`
(`LatticeProb.exists_binomRatio_sub_exp_le`, proved with no Stirling formula),
and the peak value is `1/\sqrt{\pi m}` (`LatticeProb.tendsto_centralBinom_mul_sqrt`,
two applications of the Stirling limit).  Multiplying the two approximations is
the whole content of this file: the ratio is at most one, so the error of the
peak value is not amplified, and the two errors add.

The result is the statement

  `|\sqrt{\pi m}\, P^{2m}(0, 2k) - e^{-k^2/m}| \leq \varepsilon`

for every `m` past a threshold depending only on `A` and `\varepsilon`, and every
`k` with `|k| \leq A\sqrt m`.  It is the one-dimensional case of the local
central limit theorem in the parity form: the sites of the wrong parity are not
mentioned because the kernel vanishes there, and the factor `2` of the
`d`-dimensional parity form is the density of one parity class.
-/
import LatticeProb.Walk.BinomRatio
import LatticeProb.Walk.CentralBinom
import LatticeProb.Walk.SRWOneDim

noncomputable section

namespace LatticeProb

/-! ### Two thresholds -/

/-- On the diffusive scale the site is well inside the reachable range: from
`k \leq A\sqrt m` and `(2A+2)^2 \leq m` follows `2k \leq m`. -/
theorem two_mul_le_of_le_mul_sqrt {A : ℝ} (hA : 0 < A) {m k : ℕ}
    (hm : (2 * A + 2) ^ 2 ≤ (m : ℝ)) (hk : (k : ℝ) ≤ A * Real.sqrt (m : ℝ)) :
    2 * k ≤ m := by
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hbig : (2 * A + 2) ≤ Real.sqrt (m : ℝ) := by
    have h2 : Real.sqrt ((2 * A + 2) ^ 2) ≤ Real.sqrt (m : ℝ) := Real.sqrt_le_sqrt hm
    rwa [Real.sqrt_sq (by linarith)] at h2
  have hspos : (0 : ℝ) < Real.sqrt (m : ℝ) := by linarith
  have hsq : Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) = (m : ℝ) := Real.mul_self_sqrt hm0
  have h2k : 2 * (k : ℝ) ≤ (m : ℝ) := by nlinarith
  exact_mod_cast h2k

theorem exists_centralBinom_sqrt_sub_le {ε : ℝ} (hε : 0 < ε) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      |(Nat.choose (2 * m) m : ℝ) / 4 ^ m * Real.sqrt (Real.pi * (m : ℝ)) - 1| ≤ ε := by
  obtain ⟨m₀, hm₀⟩ := (Metric.tendsto_atTop.mp tendsto_centralBinom_mul_sqrt) ε hε
  exact ⟨m₀, fun m hm => le_of_lt (by simpa [Real.dist_eq] using hm₀ m hm)⟩

theorem exists_srwHeat_one_sub_gauss_le {A ε : ℝ} (hA : 0 < A) (hε : 0 < ε) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∀ k : ℕ, (k : ℝ) ≤ A * Real.sqrt (m : ℝ) →
      |Real.sqrt (Real.pi * (m : ℝ)) * srwHeat 1 (2 * m) ![2 * (k : ℤ)]
        - Real.exp (-((k : ℝ) ^ 2 / (m : ℝ)))| ≤ ε := by
  obtain ⟨m₁, hm₁1, hm₁⟩ := exists_binomRatio_sub_exp_le hA (half_pos hε)
  obtain ⟨m₂, hm₂⟩ := exists_centralBinom_sqrt_sub_le (half_pos hε)
  refine ⟨max (max m₁ m₂) (⌈(2 * A + 2) ^ 2⌉₊ + 1), ?_, ?_⟩
  · exact le_trans hm₁1 (le_trans (le_max_left _ _) (le_max_left _ _))
  · intro m hm k hk
    have hm1 : m₁ ≤ m := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hm)
    have hm2 : m₂ ≤ m := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hm)
    have hmc : ⌈(2 * A + 2) ^ 2⌉₊ + 1 ≤ m := le_trans (le_max_right _ _) hm
    have hMle : (2 * A + 2) ^ 2 ≤ (m : ℝ) := by
      have h1 : (2 * A + 2) ^ 2 ≤ (⌈(2 * A + 2) ^ 2⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : ((⌈(2 * A + 2) ^ 2⌉₊ : ℕ) : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast (by omega : ⌈(2 * A + 2) ^ 2⌉₊ ≤ m)
      linarith
    have h2k : 2 * k ≤ m := two_mul_le_of_le_mul_sqrt hA hMle hk
    have hkm : k ≤ m := by omega
    have hBpos : (0 : ℝ) < (Nat.choose (2 * m) m : ℝ) := by
      exact_mod_cast choose_two_mul_pos m
    set r : ℝ := (Nat.choose (2 * m) (m + k) : ℝ) / (Nat.choose (2 * m) m : ℝ) with hr
    set S : ℝ := (Nat.choose (2 * m) m : ℝ) / 4 ^ m * Real.sqrt (Real.pi * (m : ℝ)) with hS
    have hkey : Real.sqrt (Real.pi * (m : ℝ)) * srwHeat 1 (2 * m) ![2 * (k : ℤ)] = r * S := by
      rw [srwHeat_one_two_mul_binom m k hkm, hr, hS]
      field_simp
    have hrpos : 0 < r := binomRatio_pos m k hkm
    have hr1 : r ≤ 1 := binomRatio_le_one m k
    have hS1 : |S - 1| ≤ ε / 2 := hm₂ m hm2
    have hre : |r - Real.exp (-((k : ℝ) ^ 2 / (m : ℝ)))| ≤ ε / 2 := hm₁ m hm1 k hk
    rw [hkey]
    have hsplit : r * S - Real.exp (-((k : ℝ) ^ 2 / (m : ℝ)))
        = r * (S - 1) + (r - Real.exp (-((k : ℝ) ^ 2 / (m : ℝ)))) := by ring
    rw [hsplit]
    have h1 : |r * (S - 1)| ≤ ε / 2 := by
      rw [abs_mul, abs_of_pos hrpos]
      nlinarith [abs_nonneg (S - 1)]
    calc |r * (S - 1) + (r - Real.exp (-((k : ℝ) ^ 2 / (m : ℝ))))|
        ≤ |r * (S - 1)| + |r - Real.exp (-((k : ℝ) ^ 2 / (m : ℝ)))| := abs_add_le _ _
      _ ≤ ε / 2 + ε / 2 := add_le_add h1 hre
      _ = ε := by ring

/-! ### The kernel is symmetric under reflection -/

/-- The one-dimensional kernel at an even time is even in the site. -/
theorem srwHeat_one_two_mul_neg (m : ℕ) (k : ℤ) :
    srwHeat 1 (2 * m) ![2 * (-k)] = srwHeat 1 (2 * m) ![2 * k] := by
  rw [srwHeat_one_two_mul, srwHeat_one_two_mul]
  unfold P1
  congr 1
  rw [show ((m : ℤ) + -k) = ((2 * m : ℕ) : ℤ) - ((m : ℤ) + k) from by push_cast; ring]
  exact binomZ_symm (2 * m) ((m : ℤ) + k)

/-- **The one-dimensional local central limit theorem**, at every even site of
the diffusive window.  This is the form the `d`-dimensional statement uses, with
the site an integer of either sign. -/
theorem exists_srwHeat_one_sub_gauss_le_int {A ε : ℝ} (hA : 0 < A) (hε : 0 < ε) :
    ∃ m₀ : ℕ, 1 ≤ m₀ ∧ ∀ m : ℕ, m₀ ≤ m → ∀ k : ℤ, |(k : ℝ)| ≤ A * Real.sqrt (m : ℝ) →
      |Real.sqrt (Real.pi * (m : ℝ)) * srwHeat 1 (2 * m) ![2 * k]
        - Real.exp (-((k : ℝ) ^ 2 / (m : ℝ)))| ≤ ε := by
  obtain ⟨m₀, hm₀, h⟩ := exists_srwHeat_one_sub_gauss_le hA hε
  refine ⟨m₀, hm₀, fun m hm k hk => ?_⟩
  have habs : ((k.natAbs : ℕ) : ℝ) = |(k : ℝ)| := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs k, Int.cast_natCast]
  have hsq : ((k.natAbs : ℕ) : ℝ) ^ 2 = (k : ℝ) ^ 2 := by rw [habs, sq_abs]
  have hkey : srwHeat 1 (2 * m) ![2 * k] = srwHeat 1 (2 * m) ![2 * ((k.natAbs : ℕ) : ℤ)] := by
    rcases Int.natAbs_eq k with h | h
    · rw [← h]
    · rw [← srwHeat_one_two_mul_neg m ((k.natAbs : ℕ) : ℤ), ← h]
  rw [hkey, ← hsq]
  exact h m hm k.natAbs (by rw [habs]; exact hk)

end LatticeProb
