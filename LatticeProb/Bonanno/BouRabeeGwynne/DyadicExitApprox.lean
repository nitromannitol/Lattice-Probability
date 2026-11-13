/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.DyadicExitApprox at commit fdb5cad; only the module paths of local imports are changed. -/
/-
Copyright (c) 2025 Kexing Ying. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying
-/
/-
Selected numerical stopping-time approximation section from
RemyDegenne/brownian-motion commit 314f04a34ff75e18fd383917ae7fe7d77beb1b6f,
BrownianMotion/StochasticIntegral/ApproxSeq.lean. Only its definition and six
NNReal approximation lemmas are retained. No optional-sampling, Cadlag,
UniformIntegrable, or Approximable typeclass import is used.
The original Apache-2.0 license is retained in
BouRabeeGwynne/Upstream/BrownianMotion/LICENSE. See the provenance record there.
-/
import Mathlib.Probability.Process.Stopping
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Filter TopologicalSpace Function
open scoped NNReal ENNReal Topology
namespace MeasureTheory
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The approximation sequence for a stopping time `τ` taking values in `ℝ≥0` defined by
`nnrealApproxSeq τ n ω = ⌈(τ ω) * 2^n⌉ / 2^n`. -/
noncomputable def nnrealApproxSeq (τ : Ω → WithTop ℝ≥0) (n : ℕ) (ω : Ω) :
    WithTop ℝ≥0 :=
  WithTop.map (fun x : ℝ≥0 ↦ ⌈x * (2 : ℝ≥0) ^ n⌉₊ / (2 : ℝ≥0) ^ n) (τ ω)

lemma nnrealApproxSeq_le_iff (τ : Ω → WithTop ℝ≥0) (n : ℕ) (ω : Ω) (t : ℝ≥0) :
    nnrealApproxSeq τ n ω ≤ t ↔ τ ω ≤ (⌊t * (2 : ℝ≥0) ^ n⌋₊ / (2 : ℝ≥0) ^ n : ℝ≥0) := by
  unfold nnrealApproxSeq
  cases hτ : τ ω with
  | top => simp only [WithTop.map_top, top_le_iff, WithTop.coe_ne_top]
  | coe x =>
    simp only [WithTop.map_coe, WithTop.coe_le_coe]
    rw [div_le_iff₀ (by positivity), le_div_iff₀ (by positivity)]
    exact ⟨fun h ↦ le_trans (Nat.le_ceil _) (Nat.cast_le.mpr (Nat.le_floor h)),
           fun h ↦ le_trans (Nat.cast_le.mpr (Nat.ceil_le.mpr h)) (Nat.floor_le (by positivity))⟩

lemma nnrealApproxSeq_isStoppingTime (𝓕 : Filtration ℝ≥0 mΩ)
    {τ : Ω → WithTop ℝ≥0} (hτ : IsStoppingTime 𝓕 τ) (n : ℕ) :
    IsStoppingTime 𝓕 (nnrealApproxSeq τ n) := by
  intro t
  have h2 : (0 : ℝ≥0) < (2 : ℝ≥0) ^ n := pow_pos (by norm_num) n
  set s := ((⌊t * (2 : ℝ≥0) ^ n⌋₊ : ℕ) : ℝ≥0) / (2 : ℝ≥0) ^ n
  suffices MeasurableSet[𝓕 t] {ω | τ ω ≤ s} by
    convert this using 1
    ext ω
    simp only [Set.mem_ofPred_eq]
    exact nnrealApproxSeq_le_iff τ n ω t
  exact 𝓕.mono' (div_le_of_le_mul₀ h2.le (by positivity) (Nat.floor_le (by positivity))) _ (hτ s)

lemma nnrealApproxSeq_countable (τ : Ω → WithTop ℝ≥0) (n : ℕ) :
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

lemma nnrealApproxSeq_antitone (τ : Ω → WithTop ℝ≥0) :
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

lemma nnrealApproxSeq_le (τ : Ω → WithTop ℝ≥0) (n : ℕ) :
    τ ≤ nnrealApproxSeq τ n := by
  intro ω
  simp only [nnrealApproxSeq]
  cases hτ : τ ω with
  | top => simp
  | coe x =>
    simp only [WithTop.map_coe, WithTop.coe_le_coe]
    rw [le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ≥0) < 2) n)]
    exact Nat.le_ceil _

lemma nnrealApproxSeq_tendsto (τ : Ω → WithTop ℝ≥0) (ω : Ω) :
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


end MeasureTheory

