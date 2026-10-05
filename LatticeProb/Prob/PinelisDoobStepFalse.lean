/-
# `PinelisDoobStep` is false as stated

`LatticeProb.PinelisDoobStep` (`Prob/PinelisReduction.lean`) asserts, for every `p ≥ 2`, a constant
`K > 0` such that for every filtered probability space and every adapted process `S` (with the
stated integrability) the cumulative cross term

  `∑_{i ∈ range k} (E|S i|^p)^{(p-2)/p} (E v(i+1)^{p/2})^{2/p}`

is at most `K (E V_k^{p/2})^{2/p} (E|S k|^p)^{(p-2)/p} + K ∑_{i ∈ Icc 1 k} E|S i|^p`.

The left sum runs over `i = 0, …, k-1` and so includes the term `i = 0`, but the right side only
sees `S i` for `i ∈ Icc 1 k`; nothing constrains `S 0`.  **Counterexample.**  Take `p = 4`, `Ω` a
point with the Dirac measure, the constant filtration, `S i = 1_{i = 0}`, `v i = 1` and `k = 1`.
Every function is constant in `ω`, so all hypotheses hold.  The left side is
`(E|S 0|^4)^{1/2} (E v 1 ^2)^{1/2} = 1`, while the right side is
`K (E (v 1)^2)^{1/2} (E |S 1|^4)^{1/2} + K E|S 1|^4 = 0` (as `(0 : ℝ) ^ (1/2) = 0`), so `1 ≤ 0`
fails for every `K`.

**What the repair must be.**  In the application `S = martingalePartialSum ξ`
(`Prob/BernsteinOneStep.lean`), and `martingalePartialSum ξ 0 = fun ω => ∑ j ∈ Icc 1 0, ξ j ω = 0`,
so `S 0 = 0` there; the counterexample above uses a process with `S 0 ≠ 0`, which the application
never produces.  But that hypothesis (or taking the right-hand sums over `Finset.range (k + 1)`) is
not enough by itself.  The statement lets `S` and `v` be unrelated, and a second one-point
counterexample survives `S 0 = 0`: `p = 4`, `S = (0, c, 0, 0, …)`, `v i = 1`, `k = 2` gives left
side `c²` and right side `K c⁴`, which fails for `c = 1 / (K + 1)`.  The missing ingredient is the
link that the application supplies and the statement discards, namely `S (i + 1) = S i + ξ (i + 1)`
with `v (i + 1) = E[ξ (i + 1)² | F i]` (a martingale-difference structure).
-/
import LatticeProb.Prob.PinelisReduction

open MeasureTheory ProbabilityTheory

universe u

namespace LatticeProb

/-- **`PinelisDoobStep` is false as stated.**  The one-point probability space with the process
`S i = 1_{i = 0}`, `v i = 1`, `p = 4` and `k = 1` makes the left side `1` and the right side `0`,
for every `K`: the term `i = 0` of the left sum is invisible to the right side. -/
theorem not_pinelisDoobStep : ¬ PinelisDoobStep.{u} := by
  intro h
  obtain ⟨K, hK, hbound⟩ := h 4 (by norm_num)
  have key := @hbound PUnit.{u + 1} _ (Measure.dirac PUnit.unit) _ _
    (Filtration.const ℕ inferInstance le_rfl)
    (fun i _ => if i = 0 then (1 : ℝ) else 0) (fun _ _ => (1 : ℝ))
    (fun i => stronglyMeasurable_const) (fun i => memLp_const _) (fun i => memLp_const _)
    (fun i => integrable_const _) 1
  simp [Finset.Icc_self, integral_const] at key
  rw [Real.zero_rpow (by norm_num)] at key
  linarith

/-- `PinelisDoobStep` with the start `S 0 = 0` of the application added as a hypothesis.  With it,
the right-hand sum over `Icc 1 k` equals the sum over `range (k + 1)`, so this is also the variant
whose right side sees every `S i` of the left sum. -/
def PinelisDoobStepStartZero : Prop :=
  ∀ p : ℝ, 2 ≤ p → ∃ K : ℝ, 0 < K ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {m₀}
      (F : Filtration ℕ m₀) (S : ℕ → Ω → ℝ) (v : ℕ → Ω → ℝ),
      (∀ ω, S 0 ω = 0) →
      (∀ i, StronglyMeasurable[F i] (S i)) →
      (∀ i, MemLp (fun ω => |S i ω| ^ (p - 2)) (ENNReal.ofReal (p / (p - 2))) μ) →
      (∀ i, MemLp (v (i + 1)) (ENNReal.ofReal (p / 2)) μ) →
      (∀ i, Integrable (fun ω => |S i ω| ^ (p - 2) * v (i + 1) ω) μ) →
      ∀ k,
        ∑ i ∈ Finset.range k,
            (∫ ω, |S i ω| ^ p ∂μ) ^ ((p - 2) / p)
              * (∫ ω, v (i + 1) ω ^ (p / 2) ∂μ) ^ (2 / p)
          ≤ K * (∫ ω, (∑ i ∈ Finset.Icc 1 k, v i ω) ^ (p / 2) ∂μ) ^ (2 / p)
              * (∫ ω, |S k ω| ^ p ∂μ) ^ ((p - 2) / p)
            + K * ∑ i ∈ Finset.Icc 1 k, ∫ ω, |S i ω| ^ p ∂μ

/-- **Adding `S 0 = 0` does not repair `PinelisDoobStep`.**  On the one-point space take `p = 4`,
`S = (0, c, 0, 0, …)`, `v i = 1` and `k = 2`: the left side is `c²` and the right side is `K c⁴`,
which fails for `c = 1 / (K + 1)`.  The statement lets `S` and `v` be unrelated; the application
links them by `S (i + 1) = S i + ξ (i + 1)` and `v (i + 1) = E[ξ (i + 1)² | F i]`. -/
theorem not_pinelisDoobStepStartZero : ¬ PinelisDoobStepStartZero.{u} := by
  intro h
  obtain ⟨K, hK, hbound⟩ := h 4 (by norm_num)
  set c : ℝ := 1 / (K + 1) with hc
  have key := @hbound PUnit.{u + 1} _ (Measure.dirac PUnit.unit) _ _
    (Filtration.const ℕ inferInstance le_rfl)
    (fun i _ => if i = 1 then c else 0) (fun _ _ => (1 : ℝ)) (fun _ => by simp)
    (fun i => stronglyMeasurable_const) (fun i => memLp_const _) (fun i => memLp_const _)
    (fun i => integrable_const _) 2
  have hI : Finset.Icc 1 2 = {1, 2} := by decide
  simp [Finset.sum_range_succ, hI, integral_const] at key
  have hc0 : 0 < c := by positivity
  have h1 : (|c| ^ 4) ^ (((4 : ℝ) - 2) / 4) = c ^ 2 := by
    rw [abs_of_pos hc0, show c ^ 4 = c ^ (4 : ℝ) by norm_num, ← Real.rpow_mul hc0.le]
    norm_num
  have h2 : |c| ^ 4 = c ^ 4 := by rw [abs_of_pos hc0]
  rw [Real.zero_rpow (by norm_num)] at key
  rw [h1, h2] at key
  have h3 : K * c ^ 2 < 1 := by
    rw [hc, one_div, inv_pow, ← div_eq_mul_inv, div_lt_one (by positivity)]
    nlinarith
  nlinarith [pow_pos hc0 2]

end LatticeProb
