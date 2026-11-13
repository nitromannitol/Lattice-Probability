/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4b.L46SLogCompare at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46STailAsymptotic

set_option autoImplicit false
noncomputable section

open Filter Topology MatedCRTHarmonic.GMSLemma27
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4b

/-- Absorb the three-root factor and the ceiling in the spare log power.
The graph radius is `2k` because a point on a grid line belongs to two cells. -/
theorem l46s_graphball_le_polylog_eventually (k : ℕ) {ζ : ℝ} (hζ : 0 < ζ) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (9 : ℝ) * ((⌈(Real.log ε⁻¹) ^ (1 + ζ / 2)⌉₊ + 1 : ℕ) : ℝ) ^ (2 * k) ≤
        (Real.log ε⁻¹) ^ ((2 * k : ℝ) * (1 + ζ) + 1) := by
  have hlog : Tendsto (fun ε : ℝ => Real.log ε⁻¹) (𝓝[>] (0 : ℝ)) atTop :=
    Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  have hspare : 0 < (2 * k : ℝ) * (ζ / 2) + 1 := by positivity
  have hpow := (tendsto_rpow_atTop hspare).comp hlog
  have hlarge := hpow.eventually_ge_atTop (9 * 3 ^ (2 * k) : ℝ)
  have hlog1 := hlog.eventually_ge_atTop 1
  filter_upwards [hlarge, hlog1, self_mem_nhdsWithin] with ε hlarge hL1 hε0
  have hεpos : 0 < ε := hε0
  let L : ℝ := Real.log ε⁻¹
  let A : ℝ := L ^ (1 + ζ / 2)
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hL1
  have hA1 : 1 ≤ A := Real.one_le_rpow hL1 (by linarith)
  have hA0 : 0 ≤ A := by positivity
  have hn : ((⌈A⌉₊ + 1 : ℕ) : ℝ) ≤ 3 * A := by
    have hc := Nat.ceil_lt_add_one hA0
    simp only [Nat.cast_add, Nat.cast_one] at *
    linarith
  have hn0 : (0 : ℝ) ≤ ((⌈A⌉₊ + 1 : ℕ) : ℝ) := by positivity
  have hpowbound : ((⌈A⌉₊ + 1 : ℕ) : ℝ) ^ (2 * k) ≤ (3 * A) ^ (2 * k) :=
    pow_le_pow_left₀ hn0 hn _
  have hAexp : A ^ (2 * k) = L ^ ((2 * k : ℝ) * (1 + ζ / 2)) := by
    dsimp [A]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
    congr 1
    push_cast
    ring
  have hprod : L ^ ((2 * k : ℝ) * (1 + ζ / 2)) *
      L ^ ((2 * k : ℝ) * (ζ / 2) + 1) =
      L ^ ((2 * k : ℝ) * (1 + ζ) + 1) := by
    rw [← Real.rpow_add hLpos]
    congr 1
    ring
  have hAexp0 : 0 ≤ A ^ (2 * k) := by positivity
  change 9 * 3 ^ (2 * k) ≤ L ^ ((2 * k : ℝ) * (ζ / 2) + 1) at hlarge
  have hmul := mul_le_mul_of_nonneg_right hlarge hAexp0
  calc
    9 * ((⌈A⌉₊ + 1 : ℕ) : ℝ) ^ (2 * k) ≤
        9 * (3 * A) ^ (2 * k) := by gcongr
    _ = (9 * 3 ^ (2 * k)) * A ^ (2 * k) := by rw [mul_pow]; ring
    _ ≤ A ^ (2 * k) * L ^ ((2 * k : ℝ) * (ζ / 2) + 1) := by
      simpa only [mul_comm] using hmul
    _ = L ^ ((2 * k : ℝ) * (1 + ζ) + 1) := by rw [hAexp, hprod]

/-- The preceding numerical comparison in the extended-natural / ENNReal
types of `degreeIn`. -/
theorem l46s_graphball_ENNReal_le_polylog {k : ℕ} {ε ζ : ℝ}
    (h : (9 : ℝ) * ((⌈(Real.log ε⁻¹) ^ (1 + ζ / 2)⌉₊ + 1 : ℕ) : ℝ) ^ (2 * k) ≤
      (Real.log ε⁻¹) ^ ((2 * k : ℝ) * (1 + ζ) + 1)) :
    (((9 : ℕ∞) * ((⌈(Real.log ε⁻¹) ^ (1 + ζ / 2)⌉₊ + 1 : ℕ∞) ^ (2 * k))) : ℝ≥0∞) ≤
      ENNReal.ofReal ((Real.log ε⁻¹) ^ ((2 * k : ℝ) * (1 + ζ) + 1)) := by
  have hcast :
      (((9 : ℕ∞) * ((⌈(Real.log ε⁻¹) ^ (1 + ζ / 2)⌉₊ + 1 : ℕ∞) ^ (2 * k))) : ℝ≥0∞) =
      ENNReal.ofReal ((9 : ℝ) * ((⌈(Real.log ε⁻¹) ^ (1 + ζ / 2)⌉₊ + 1 : ℕ) : ℝ) ^ (2 * k)) := by
    norm_cast
  rw [hcast]
  exact ENNReal.ofReal_le_ofReal h

end MatedCRTHarmonic.GMS4b
