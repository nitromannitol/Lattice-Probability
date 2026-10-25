module

/-
Copyright (c) 2025 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
/-
Selected numerical stopping-time approximation section from
RemyDegenne/brownian-motion commit 314f04a34ff75e18fd383917ae7fe7d77beb1b6f,
BrownianMotion/StochasticIntegral/ApproxSeq.lean.
Adapted from Leonardo Bonanno's formalizations:
https://github.com/leobon12/lean-formalizations
Source: BouRabeeGwynne/DyadicExitApprox.lean and BouRabeeGwynne/BrownianStoppingApprox.lean.
-/

public import LatticeProb.Prob.StoppingDyadic
public import Mathlib.Probability.Process.Stopping
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Dyadic approximation of stopping times with values in `WithTop ℝ≥0`

`nnrealApproxSeq τ n` rounds a random time `τ` with values in `WithTop ℝ≥0` up to the grid
`2⁻ⁿ ℕ`, and keeps `⊤` at `⊤`. The approximations are stopping times, they are antitone in `n`,
they dominate `τ`, and they converge to `τ` pointwise.

The file also gives the same construction for `ℝ≥0`-valued times as `dyadicStoppingTime`, with
its finite range `dyadicStoppingRange`. The stopping-time and convergence facts for
`dyadicStoppingTime` are the statements of `LatticeProb.StoppingDyadic` for `dyUp`, with the
factors of the product swapped, so they are proved from those.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LatticeProb

variable {Ω : Type*} {m0 : MeasurableSpace Ω}

/-- The dyadic approximation from above of a `WithTop ℝ≥0`-valued random time `τ`:
`nnrealApproxSeq τ n ω = ⌈τ ω * 2ⁿ⌉ / 2ⁿ`, with `⊤` kept at `⊤`. -/
noncomputable def nnrealApproxSeq (τ : Ω → WithTop ℝ≥0) (n : ℕ) (ω : Ω) :
    WithTop ℝ≥0 :=
  WithTop.map (fun x : ℝ≥0 ↦ ⌈x * (2 : ℝ≥0) ^ n⌉₊ / (2 : ℝ≥0) ^ n) (τ ω)

/-- `nnrealApproxSeq τ n ω ≤ t` holds exactly when `τ ω` is at most the dyadic time
`⌊t * 2ⁿ⌋ / 2ⁿ`, which is the largest dyadic time of level `n` below `t`. -/
theorem nnrealApproxSeq_le_iff (τ : Ω → WithTop ℝ≥0) (n : ℕ) (ω : Ω) (t : ℝ≥0) :
    nnrealApproxSeq τ n ω ≤ t ↔ τ ω ≤ (⌊t * (2 : ℝ≥0) ^ n⌋₊ / (2 : ℝ≥0) ^ n : ℝ≥0) := by
  unfold nnrealApproxSeq
  cases hτ : τ ω with
  | top => simp only [WithTop.map_top, top_le_iff, WithTop.coe_ne_top]
  | coe x =>
    simp only [WithTop.map_coe, WithTop.coe_le_coe]
    rw [div_le_iff₀ (by positivity), le_div_iff₀ (by positivity)]
    exact ⟨fun h ↦ le_trans (Nat.le_ceil _) (Nat.cast_le.mpr (Nat.le_floor h)),
           fun h ↦ le_trans (Nat.cast_le.mpr (Nat.ceil_le.mpr h)) (Nat.floor_le (by positivity))⟩

/-- The dyadic approximation `nnrealApproxSeq τ n` of a stopping time `τ` is a stopping time. -/
theorem nnrealApproxSeq_isStoppingTime (𝓕 : Filtration ℝ≥0 m0)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓕 τ) (n : ℕ) :
    IsStoppingTime 𝓕 (nnrealApproxSeq τ n) := by
  intro t
  have h2 : (0 : ℝ≥0) < (2 : ℝ≥0) ^ n := pow_pos (by norm_num) n
  set s := ((⌊t * (2 : ℝ≥0) ^ n⌋₊ : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n
  suffices MeasurableSet[𝓕 t] {ω | τ ω ≤ s} by
    convert this using 1
    ext ω
    simp only [Set.mem_setOf_eq]
    exact nnrealApproxSeq_le_iff τ n ω t
  exact 𝓕.mono' (div_le_of_le_mul₀ h2.le (by positivity) (Nat.floor_le (by positivity))) _ (hτ s)

/-- For a fixed level `n`, the dyadic approximations `nnrealApproxSeq τ n` take countably many
values: the dyadic grid `k / 2ⁿ` together with `⊤`. -/
theorem nnrealApproxSeq_countable (τ : Ω → WithTop ℝ≥0) (n : ℕ) :
    (Set.range (nnrealApproxSeq τ n)).Countable := by
  apply (Set.countable_range
    (fun k : ℕ ↦ ((k : ℝ≥0) / (2 : ℝ≥0) ^ n : WithTop ℝ≥0)) |>.insert ⊤).mono
  rintro _ ⟨ω, rfl⟩
  simp only [nnrealApproxSeq]
  cases hτ : τ ω with
  | top => simp [Set.mem_insert_iff]
  | coe x =>
    simp only [WithTop.map_coe, Set.mem_insert_iff, WithTop.coe_ne_top, false_or]
    exact ⟨⌈x * 2 ^ n⌉₊, rfl⟩

/-- The dyadic approximations `nnrealApproxSeq τ n` decrease in the level `n`. -/
theorem nnrealApproxSeq_antitone (τ : Ω → WithTop ℝ≥0) :
    Antitone (nnrealApproxSeq τ) := by
  intro m n hmn ω
  simp only [nnrealApproxSeq]
  cases hτ : τ ω with
  | top => simp
  | coe x =>
    simp only [WithTop.map_coe, WithTop.coe_le_coe]
    erw [div_le_div_iff₀ (by positivity) (by positivity)]
    have key : (⌈x * 2 ^ n⌉₊ : ℕ) ≤ ⌈x * 2 ^ m⌉₊ * 2 ^ (n - m) := by
      rw [Nat.ceil_le]
      calc x * (2 : ℝ≥0) ^ n = x * (2 : ℝ≥0) ^ m * (2 : ℝ≥0) ^ (n - m) := by
            rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hmn]
        _ ≤ (⌈x * 2 ^ m⌉₊ : ℝ≥0) * (2 : ℝ≥0) ^ (n - m) :=
            mul_le_mul_of_nonneg_right (Nat.le_ceil _) (by positivity)
        _ = ((⌈x * 2 ^ m⌉₊ * 2 ^ (n - m) : ℕ) : ℝ≥0) := by push_cast; ring
    calc (⌈x * 2 ^ n⌉₊ : ℝ≥0) * 2 ^ m
        ≤ ((⌈x * 2 ^ m⌉₊ * 2 ^ (n - m) : ℕ) : ℝ≥0) * 2 ^ m :=
          mul_le_mul_of_nonneg_right (Nat.cast_le.mpr key) (by positivity)
      _ = (⌈x * 2 ^ m⌉₊ : ℝ≥0) * ((2 : ℝ≥0) ^ (n - m) * 2 ^ m) := by
          push_cast; ring
      _ = (⌈x * 2 ^ m⌉₊ : ℝ≥0) * 2 ^ n := by
          rw [← pow_add, Nat.sub_add_cancel hmn]

/-- The dyadic approximations `nnrealApproxSeq τ n` dominate `τ`. -/
theorem nnrealApproxSeq_le (τ : Ω → WithTop ℝ≥0) (n : ℕ) :
    τ ≤ nnrealApproxSeq τ n := by
  intro ω
  simp only [nnrealApproxSeq]
  cases hτ : τ ω with
  | top => simp
  | coe x =>
    simp only [WithTop.map_coe, WithTop.coe_le_coe]
    rw [le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ≥0) < 2) n)]
    exact Nat.le_ceil _

/-- At each `ω`, the dyadic approximations `nnrealApproxSeq τ n ω` tend to `τ ω` as `n → ∞`. -/
theorem nnrealApproxSeq_tendsto (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
    Tendsto (nnrealApproxSeq τ · ω) atTop (𝓝 (τ ω)) := by
  simp only [nnrealApproxSeq]
  cases hτ : τ ω with
  | top => simp
  | coe x =>
    simp only [WithTop.map_coe]
    apply (WithTop.continuous_coe.tendsto x).comp
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    · conv_rhs => rw [← add_zero x]
      exact tendsto_const_nhds.add
        ((tendsto_inv_atTop_zero.comp (tendsto_pow_atTop_atTop_of_one_lt
          (by norm_num : (1 : ℝ≥0) < 2))).congr (fun n => (one_mul _).symm))
    · intro n
      rw [le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ≥0) < 2) n)]
      exact Nat.le_ceil _
    · intro n
      calc (⌈x * 2 ^ n⌉₊ : ℝ≥0) / 2 ^ n
          ≤ (x * 2 ^ n + 1) / 2 ^ n :=
            div_le_div_of_nonneg_right (Nat.ceil_lt_add_one <| by positivity).le (by positivity)
        _ = x + 1 / 2 ^ n := by
            rw [add_div, mul_div_cancel_of_imp]
            exact fun h ↦ absurd h (by positivity)

/-- The dyadic approximation from above of a `ℝ≥0`-valued time `σ` at level `n`:
`dyadicStoppingTime σ n ω = ⌈σ ω * 2ⁿ⌉ / 2ⁿ`. -/
noncomputable def dyadicStoppingTime {Ω : Type*} (σ : Ω → ℝ≥0) (n : ℕ) (ω : Ω) : ℝ≥0 :=
  ⌈σ ω * (2 : ℝ≥0) ^ n⌉₊ / (2 : ℝ≥0) ^ n

/-- `dyadicStoppingTime σ n` is the `ℝ≥0`-valued dyadic approximation `dyUp n` of `σ`, with the
factors of the product written in the other order. -/
theorem dyadicStoppingTime_eq_dyUp {Ω : Type*} (σ : Ω → ℝ≥0) (n : ℕ) (ω : Ω) :
    dyadicStoppingTime σ n ω = dyUp n (σ ω) := by
  rw [dyadicStoppingTime, dyUp, mul_comm]

/-- The dyadic approximation of a `ℝ≥0`-valued time is the `nnrealApproxSeq` of its coercion to
`WithTop ℝ≥0`. -/
theorem nnrealApproxSeq_coe_eq_dyadicStoppingTime {Ω : Type*}
    (σ : Ω → ℝ≥0) (n : ℕ) :
    nnrealApproxSeq (fun ω ↦ (σ ω : WithTop ℝ≥0)) n =
      fun ω ↦ (dyadicStoppingTime σ n ω : WithTop ℝ≥0) := rfl

/-- If `σ` is a stopping time, so is its dyadic approximation `dyadicStoppingTime σ n`. -/
theorem isStoppingTime_dyadicStoppingTime {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (F : Filtration ℝ≥0 mΩ) {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime F (fun ω ↦ (σ ω : ℝ≥0∞))) (n : ℕ) :
    IsStoppingTime F (fun ω ↦ (dyadicStoppingTime σ n ω : ℝ≥0∞)) := by
  simpa only [dyadicStoppingTime_eq_dyUp] using isStoppingTime_dyUp hσ n

/-- The dyadic approximation `dyadicStoppingTime σ n` is at least `σ`. -/
theorem le_dyadicStoppingTime {Ω : Type*} (σ : Ω → ℝ≥0) (n : ℕ) (ω : Ω) :
    σ ω ≤ dyadicStoppingTime σ n ω := by
  rw [dyadicStoppingTime_eq_dyUp]
  exact le_dyUp n (σ ω)

/-- At each `ω`, the dyadic approximations `dyadicStoppingTime σ n ω` tend to `σ ω`. -/
theorem tendsto_dyadicStoppingTime {Ω : Type*} (σ : Ω → ℝ≥0) (ω : Ω) :
    Tendsto (fun n ↦ dyadicStoppingTime σ n ω) atTop (𝓝 (σ ω)) := by
  simpa only [dyadicStoppingTime_eq_dyUp] using tendsto_dyUp (σ ω)

/-- The finite set of dyadic grid points `k / 2ⁿ` with `k ≤ ⌈N * 2ⁿ⌉`. It contains every value of
`dyadicStoppingTime σ n` when `σ ≤ N`. -/
noncomputable def dyadicStoppingRange (N : ℝ≥0) (n : ℕ) : Finset ℝ≥0 := by
  classical
  exact (Finset.range (⌈N * (2 : ℝ≥0) ^ n⌉₊ + 1)).image
    (fun k : ℕ ↦ (k : ℝ≥0) / (2 : ℝ≥0) ^ n)

/-- If `σ ≤ N` everywhere, the dyadic approximation `dyadicStoppingTime σ n` takes its values in
the finite set `dyadicStoppingRange N n`. -/
theorem dyadicStoppingTime_mem_range {Ω : Type*} {σ : Ω → ℝ≥0} {N : ℝ≥0}
    (hN : ∀ ω, σ ω ≤ N) (n : ℕ) (ω : Ω) :
    dyadicStoppingTime σ n ω ∈ dyadicStoppingRange N n := by
  classical
  refine Finset.mem_image.mpr ⟨⌈σ ω * (2 : ℝ≥0) ^ n⌉₊, ?_, rfl⟩
  apply Finset.mem_range.mpr
  exact Nat.lt_succ_of_le (Nat.ceil_mono (mul_le_mul_of_nonneg_right (hN ω) (by positivity)))

namespace DyadicExitApproxExample

/-- The constant time `c` is a stopping time: the event `{c ≤ t}` is either everything or
nothing. -/
theorem isStoppingTime_const_withTop (𝓕 : Filtration ℝ≥0 m0) (c : ℝ≥0) :
    IsStoppingTime 𝓕 (fun _ : Ω ↦ (c : WithTop ℝ≥0)) := by
  intro t
  by_cases h : c ≤ t
  · have hset : {ω : Ω | (c : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} = Set.univ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact WithTop.coe_le_coe.mpr h
    rw [hset]
    exact MeasurableSet.univ
  · have hset : {ω : Ω | (c : WithTop ℝ≥0) ≤ (t : WithTop ℝ≥0)} = ∅ := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact fun hle ↦ h (WithTop.coe_le_coe.mp hle)
    rw [hset]
    exact @MeasurableSet.empty Ω (𝓕 t)

/-- The dyadic approximation of the constant stopping time `c` is a stopping time. -/
theorem nnrealApproxSeq_const_isStoppingTime (𝓕 : Filtration ℝ≥0 m0) (c : ℝ≥0) (n : ℕ) :
    IsStoppingTime 𝓕 (nnrealApproxSeq (fun _ : Ω ↦ (c : WithTop ℝ≥0)) n) :=
  nnrealApproxSeq_isStoppingTime 𝓕 (isStoppingTime_const_withTop 𝓕 c) n

/-- The dyadic approximations of the constant time `c` converge to `c` at every `ω`. -/
theorem nnrealApproxSeq_const_tendsto (c : ℝ≥0) (ω : Ω) :
    Tendsto (fun n ↦ nnrealApproxSeq (fun _ : Ω ↦ (c : WithTop ℝ≥0)) n ω) atTop
      (𝓝 (c : WithTop ℝ≥0)) :=
  nnrealApproxSeq_tendsto (fun _ : Ω ↦ (c : WithTop ℝ≥0)) ω

/-- The `ℝ≥0`-valued dyadic approximation of the constant time `c` is a stopping time. -/
theorem dyadicStoppingTime_const_isStoppingTime (𝓕 : Filtration ℝ≥0 m0) (c : ℝ≥0) (n : ℕ) :
    IsStoppingTime 𝓕 (fun ω : Ω ↦ (dyadicStoppingTime (fun _ ↦ c) n ω : ℝ≥0∞)) :=
  isStoppingTime_dyadicStoppingTime 𝓕 (isStoppingTime_const_withTop 𝓕 c) n

/-- The dyadic approximations of the constant time `c` converge to `c` at every `ω`. -/
theorem dyadicStoppingTime_const_tendsto (c : ℝ≥0) (ω : Ω) :
    Tendsto (fun n ↦ dyadicStoppingTime (fun _ : Ω ↦ c) n ω) atTop (𝓝 c) :=
  tendsto_dyadicStoppingTime (fun _ : Ω ↦ c) ω

/-- The dyadic approximations of the constant time `c` lie in `dyadicStoppingRange c n`. -/
theorem dyadicStoppingTime_const_mem_range (c : ℝ≥0) (n : ℕ) (ω : Ω) :
    dyadicStoppingTime (fun _ : Ω ↦ c) n ω ∈ dyadicStoppingRange c n :=
  dyadicStoppingTime_mem_range (fun _ ↦ le_rfl) n ω

end DyadicExitApproxExample

end LatticeProb
