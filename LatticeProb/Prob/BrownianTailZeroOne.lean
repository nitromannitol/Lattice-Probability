/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: QuantumZipper/Proofs/Probability/TailTrivial.lean.
-/
import LatticeProb.Prob.BrownianGermZeroOne
import LatticeProb.Prob.BrownianContAll
import Mathlib.Probability.BrownianMotion.Basic
import Mathlib.Probability.StrongLaw

/-!
# Tail triviality of Brownian motion at large times

For a process `A : ℝ≥0 → Ω → ℝ`, `tailFar A` is the σ-algebra `⋂ t, σ(A u : u ≥ t)` of the
large-time behaviour of `A`.

* `ae_tendsto_div_nat`: for a pre-Brownian motion with measurable coordinates, `B n / n → 0`
  almost surely along the natural numbers (the strong law of large numbers for its increments).
* `isTrivialSigma_tailFar`: for a pre-Brownian motion with measurable coordinates, the large-time
  tail σ-algebra is trivial. The proof applies the Blumenthal-type law `isTrivialSigma_iInf_bmPast_of`
  to the time-inverted process `t ↦ t * B (1 / t)`.
* `isTrivialSigma_tailFar_drift`: the same for `c * B t + μ * t`, with any `c μ : ℝ`.

The namespace `BrownianTailZeroOneExample` checks that the hypotheses are satisfiable.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace LatticeProb

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

/-- Strong law of large numbers for a pre-Brownian motion along the integers:
`B n / n → 0` almost surely. -/
theorem ae_tendsto_div_nat {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (n : ℝ)⁻¹ * B n ω) atTop (nhds 0) := by
  haveI : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set X : ℕ → Ω → ℝ := fun i ω => B ((i : ℝ≥0) + 1) ω - B i ω with hX
  have hXm : ∀ i, Measurable (X i) := fun i => (hBm _).sub (hBm _)
  have hlaw : ∀ i, P.map (X i) = gaussianReal 0 1 := by
    intro i
    have h := (hB.hasLaw_sub ((i : ℝ≥0) + 1) (i : ℝ≥0)).map_eq
    convert h using 2
    all_goals first
      | rfl
      | (apply NNReal.eq; simp [coe_nndist])
  have hident : ∀ i, IdentDistrib (X i) (X 0) P P :=
    fun i => ⟨(hXm i).aemeasurable, (hXm 0).aemeasurable, by rw [hlaw, hlaw]⟩
  have hindep : Pairwise fun i j => IndepFun (X i) (X j) P := by
    have key : ∀ i j : ℕ, i < j → IndepFun (X j) (X i) P := by
      intro i j hij
      set t₀ : ℝ≥0 := (i : ℝ≥0) + 1
      have hle : t₀ ≤ (j : ℝ≥0) := by
        simp only [t₀]; exact_mod_cast Nat.succ_le_of_lt hij
      have h := hB.indepFun_shift t₀
      have hφ : Measurable fun f : ℝ≥0 → ℝ =>
          f ((j : ℝ≥0) + 1 - t₀) - f ((j : ℝ≥0) - t₀) :=
        (measurable_pi_apply ((j : ℝ≥0) + 1 - t₀)).sub (measurable_pi_apply ((j : ℝ≥0) - t₀))
      have hψ : Measurable fun g : Set.Iic t₀ → ℝ =>
          g ⟨t₀, Set.mem_Iic.2 le_rfl⟩ - g ⟨(i : ℝ≥0), by simp [t₀]⟩ :=
        (measurable_pi_apply (⟨t₀, Set.mem_Iic.2 le_rfl⟩ : Set.Iic t₀)).sub
          (measurable_pi_apply (⟨(i : ℝ≥0), by simp [t₀]⟩ : Set.Iic t₀))
      have h2 := h.comp hφ hψ
      convert h2 using 1
      · funext ω
        simp only [Function.comp_apply, X]
        rw [add_tsub_cancel_of_le (hle.trans le_self_add), add_tsub_cancel_of_le hle]
        ring
      · funext ω
        simp [X, t₀]
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact (key i j h).symm
    · exact key j i h
  have hint : Integrable (X 0) P :=
    (hB.integrable_eval _).sub (hB.integrable_eval _)
  have hmean : P[X 0] = 0 := by
    rw [integral_sub (hB.integrable_eval _) (hB.integrable_eval _), hB.integral_eval,
      hB.integral_eval, sub_zero]
  have hslln := strong_law_ae X hint hindep hident
  filter_upwards [hslln, hB.eval_zero_ae_eq_zero] with ω hω h0
  rw [hmean] at hω
  refine hω.congr fun n => ?_
  have hs : ∑ i ∈ Finset.range n, X i ω = ∑ i ∈ Finset.range n,
      ((fun i : ℕ => B (i : ℝ≥0) ω) (i + 1) - (fun i : ℕ => B (i : ℝ≥0) ω) i) :=
    Finset.sum_congr rfl fun i _ => by simp [X]
  rw [smul_eq_mul, hs, Finset.sum_range_sub (fun i : ℕ => B (i : ℝ≥0) ω) n]
  simp [h0]

/-- The large-time tail σ-algebra `⋂ t, σ(A u : u ≥ t)` of a process. -/
@[reducible] noncomputable def tailFar (A : ℝ≥0 → Ω → ℝ) : MeasurableSpace Ω :=
  ⨅ t : ℝ≥0, MeasurableSpace.comap (fun ω (u : Set.Ici t) => A u ω) inferInstance

/-- Tail triviality of Brownian motion at large times: for a pre-Brownian motion with measurable
coordinates, the σ-algebra `tailFar B` is trivial. -/
theorem isTrivialSigma_tailFar {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) : IsTrivialSigma (tailFar B) P := by
  set W : ℝ≥0 → Ω → ℝ := fun t ω => t * B (1 / t) ω with hW
  have hWB : IsPreBrownianReal W P := hB.inv
  have hWm : ∀ t, Measurable (W t) := fun t => (hBm _).const_mul _
  have hW0 : ∀ᵐ ω ∂P, W 0 ω = 0 := ae_of_all _ fun ω => by simp [W]
  have hWlim : ∀ᵐ ω ∂P, Tendsto (fun n => W (epsSeq n) ω) atTop (nhds 0) := by
    filter_upwards [ae_tendsto_div_nat hB hBm] with ω hω
    have h1 := (tendsto_add_atTop_iff_nat 1).2 hω
    refine h1.congr fun n => ?_
    simp only [W, epsSeq, one_div, inv_inv]
    push_cast
    ring
  refine (isTrivialSigma_iInf_bmPast_of hWB hWm hW0 hWlim).mono (le_iInf fun n => ?_)
  refine (iInf_le _ ((n : ℝ≥0) + 1)).trans (Measurable.comap_le (measurable_pi_of fun u => ?_))
  have hu0 : (u : ℝ≥0) ≠ 0 := by
    intro h; have := u.2; rw [Set.mem_Ici, h] at this
    exact absurd this (not_le.2 (by positivity))
  have hle : 1 / (u : ℝ≥0) ≤ epsSeq n := by
    rw [epsSeq, one_div]; exact inv_anti₀ (by positivity) u.2
  have e : (fun ω => B u ω) = fun ω => (u : ℝ) * W (1 / (u : ℝ≥0)) ω := by
    funext ω
    simp only [W, one_div, inv_inv]
    push_cast
    rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hu0), one_mul]
  show Measurable[bmPast W (epsSeq n)] fun ω => B u ω
  rw [e]
  exact (measurable_bmPast_coord (B := W) hle).const_mul _

/-- Tail triviality at large times for Brownian motion with drift `c * B t + μ * t`. -/
theorem isTrivialSigma_tailFar_drift {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (c μ : ℝ) :
    IsTrivialSigma (tailFar fun t ω => c * B t ω + μ * (t : ℝ)) P := by
  refine (isTrivialSigma_tailFar hB hBm).mono (le_iInf fun t => (iInf_le _ t).trans ?_)
  exact Measurable.comap_le (measurable_pi_of fun u =>
    ((measurable_comap_coord (fun ω (u : Set.Ici t) => B u ω) u).const_mul c).add
      measurable_const)

namespace BrownianTailZeroOneExample

-- Nonvacuity: the Brownian motion of `exists_isBrownianReal_cont`, with every path continuous,
-- meets the hypotheses of `isTrivialSigma_tailFar`.
example :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : @MeasureTheory.Measure Ω mΩ)
      (B : ℝ≥0 → Ω → ℝ), @IsPreBrownianReal Ω mΩ B P ∧ (∀ t, @Measurable Ω ℝ mΩ _ (B t)) ∧
      @IsTrivialSigma Ω mΩ (tailFar B) P := by
  obtain ⟨Ω, mΩ, P, B, hm, hB, -⟩ := exists_isBrownianReal_cont
  exact ⟨Ω, mΩ, P, B, hB.toIsPreBrownianReal, hm,
    isTrivialSigma_tailFar hB.toIsPreBrownianReal hm⟩

-- Nonvacuity: the same Brownian motion meets the hypotheses of `isTrivialSigma_tailFar_drift`,
-- for every choice of the drift coefficients.
example :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : @MeasureTheory.Measure Ω mΩ)
      (B : ℝ≥0 → Ω → ℝ), @IsPreBrownianReal Ω mΩ B P ∧ (∀ t, @Measurable Ω ℝ mΩ _ (B t)) ∧
      ∀ c μ : ℝ, @IsTrivialSigma Ω mΩ
        (tailFar fun t ω => c * B t ω + μ * (t : ℝ)) P := by
  obtain ⟨Ω, mΩ, P, B, hm, hB, -⟩ := exists_isBrownianReal_cont
  exact ⟨Ω, mΩ, P, B, hB.toIsPreBrownianReal, hm,
    fun c μ => isTrivialSigma_tailFar_drift hB.toIsPreBrownianReal hm c μ⟩

end BrownianTailZeroOneExample

end LatticeProb
