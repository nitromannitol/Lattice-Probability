/-
The dyadic approximation of a stopping time from above.

For a stopping time `τ` with values in `ℝ≥0`, the times `⌈2ⁿ τ⌉ / 2ⁿ` are again
stopping times, they take only the countably many values `k / 2ⁿ`, they are at
least `τ`, and they converge to `τ`.  That is what turns a statement proved for
stopping times with countably many values into one for an arbitrary stopping
time, once the paths of the process are continuous.

The stopping-time property is the only step that is not arithmetic: the event
`⌈2ⁿ τ⌉ / 2ⁿ ≤ i` is the event `τ ≤ ⌊2ⁿ i⌋ / 2ⁿ`, because the left side is a
dyadic rational, and that event belongs to the filtration at the dyadic time
`⌊2ⁿ i⌋ / 2ⁿ`, which precedes `i`.
-/
import Mathlib

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace LatticeProb

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- The dyadic approximation from above of a nonnegative real. -/
def dyUp (n : ℕ) (r : ℝ≥0) : ℝ≥0 := (⌈(2 ^ n : ℝ≥0) * r⌉₊ : ℝ≥0) / 2 ^ n

theorem le_dyUp (n : ℕ) (r : ℝ≥0) : r ≤ dyUp n r := by
  have h : (0 : ℝ≥0) < 2 ^ n := pow_pos two_pos n
  rw [dyUp, le_div_iff₀ h, mul_comm]
  exact Nat.le_ceil _

theorem dyUp_le_add (n : ℕ) (r : ℝ≥0) : dyUp n r ≤ r + (2 ^ n)⁻¹ := by
  have h : (0 : ℝ≥0) < 2 ^ n := pow_pos two_pos n
  have hceil : ((⌈(2 ^ n : ℝ≥0) * r⌉₊ : ℕ) : ℝ≥0) ≤ (2 ^ n : ℝ≥0) * r + 1 := by
    refine le_trans (Nat.cast_le.2 (Nat.ceil_le_floor_add_one _)) ?_
    push_cast
    exact add_le_add (Nat.floor_le zero_le) le_rfl
  rw [dyUp, div_le_iff₀ h, add_mul, inv_mul_cancel₀ h.ne']
  refine le_trans hceil ?_
  rw [mul_comm r]

theorem dyUp_le_div_iff (n : ℕ) (r : ℝ≥0) (k : ℕ) :
    dyUp n r ≤ (k : ℝ≥0) / 2 ^ n ↔ r ≤ (k : ℝ≥0) / 2 ^ n := by
  have h : (0 : ℝ≥0) < 2 ^ n := pow_pos two_pos n
  rw [dyUp, div_le_iff₀ h, div_mul_cancel₀ _ h.ne', le_div_iff₀ h, Nat.cast_le, Nat.ceil_le,
    mul_comm ((2 : ℝ≥0) ^ n) r]

theorem tendsto_dyUp (r : ℝ≥0) : Tendsto (fun n => dyUp n r) atTop (𝓝 r) := by
  rw [← NNReal.tendsto_coe]
  have hz : Tendsto (fun n : ℕ => ((2 : ℝ) ^ n)⁻¹) atTop (𝓝 0) := by
    simpa [inv_pow] using
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 2⁻¹) (by norm_num)
  have hup : Tendsto (fun n : ℕ => (r : ℝ) + ((2 : ℝ) ^ n)⁻¹) atTop (𝓝 ((r : ℝ) + 0)) :=
    tendsto_const_nhds.add hz
  rw [add_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun n => by exact_mod_cast le_dyUp n r) (fun n => ?_)
  have := dyUp_le_add n r
  have := (NNReal.coe_le_coe).2 this
  simpa using this

theorem dyUp_eq (n : ℕ) (r : ℝ≥0) : dyUp n r = ((⌈(2 ^ n : ℝ≥0) * r⌉₊ : ℕ) : ℝ≥0) / 2 ^ n := rfl

theorem range_dyUp_subset (n : ℕ) :
    Set.range (dyUp n) ⊆ Set.range (fun k : ℕ => (k : ℝ≥0) / 2 ^ n) := by
  rintro _ ⟨r, rfl⟩
  exact ⟨⌈(2 ^ n : ℝ≥0) * r⌉₊, rfl⟩

theorem dyUp_le_iff (n : ℕ) (r i : ℝ≥0) :
    dyUp n r ≤ i ↔ r ≤ ((⌊i * (2 ^ n : ℝ≥0)⌋₊ : ℕ) : ℝ≥0) / 2 ^ n := by
  have h : (0 : ℝ≥0) < 2 ^ n := pow_pos two_pos n
  rw [dyUp, div_le_iff₀ h, le_div_iff₀ h, ← Nat.le_floor_iff zero_le, Nat.ceil_le,
    mul_comm ((2 : ℝ≥0) ^ n) r]

theorem isStoppingTime_dyUp {𝔽 : Filtration ℝ≥0 m0} {τ : Ω → ℝ≥0}
    (hτ : IsStoppingTime 𝔽 fun ω => (τ ω : ℝ≥0∞)) (n : ℕ) :
    IsStoppingTime 𝔽 fun ω => ((dyUp n (τ ω) : ℝ≥0) : ℝ≥0∞) := by
  intro i
  have hle : ((⌊i * (2 ^ n : ℝ≥0)⌋₊ : ℕ) : ℝ≥0) / 2 ^ n ≤ i := by
    have h : (0 : ℝ≥0) < 2 ^ n := pow_pos two_pos n
    rw [div_le_iff₀ h]
    exact Nat.floor_le zero_le
  refine MeasurableSet.congr
    (𝔽.mono hle _ (hτ (((⌊i * (2 ^ n : ℝ≥0)⌋₊ : ℕ) : ℝ≥0) / 2 ^ n))) ?_
  ext ω
  simp only [Set.mem_setOf_eq]
  exact ENNReal.coe_le_coe.trans ((dyUp_le_iff n (τ ω) i).symm.trans ENNReal.coe_le_coe.symm)

theorem countable_range_dyUp (n : ℕ) (τ : Ω → ℝ≥0) :
    (Set.range fun ω => ((dyUp n (τ ω) : ℝ≥0) : ℝ≥0∞)).Countable := by
  refine Set.Countable.mono ?_ (Set.countable_range fun k : ℕ => ((((k : ℝ≥0) / 2 ^ n : ℝ≥0)) : ℝ≥0∞))
  rintro _ ⟨ω, rfl⟩
  exact ⟨⌈(2 ^ n : ℝ≥0) * τ ω⌉₊, rfl⟩

end LatticeProb

end
