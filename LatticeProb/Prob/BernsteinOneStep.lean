/-
The filtration instantiation of the one-step moment estimate.

`LatticeProb.integral_abs_add_rpow_le` (`Prob/BernsteinMartingale.lean`) is the integrated
one-step estimate for a single martingale increment.  This file reads it along a filtration
`F`: with `S i = ∑_{j=1}^{i} ξ_j` and `v i = μ[ξ_i² | F (i-1)]`, it gives

  `E |S (i+1)|^p ≤ E |S i|^p + C (E[|S i|^{p-2} v (i+1)] + E |ξ (i+1)|^p)`,

the per-step inequality iterated in Pinelis's proof of `Parking.External.Bernstein`.  The
cross term is rewritten from `ξ (i+1)²` to `v (i+1)` by the pull-out property, since
`|S i|^{p-2}` is `F i`-measurable.

The step is taken as a hypothesis here (the caller derives it from the filtration); the
remaining research-level obligation is the cumulative Pinelis induction, recorded in
`scratch/pk/bernstein-route.md`.
-/
import LatticeProb.Prob.BernsteinMartingale

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace LatticeProb

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}

/-- The partial sum `∑_{j=1}^{i} ξ_j` of a sequence of martingale differences. -/
noncomputable def martingalePartialSum (ξ : ℕ → Ω → ℝ) (i : ℕ) : Ω → ℝ :=
  fun ω => ∑ j ∈ Finset.Icc 1 i, ξ j ω

/-- The partial sums satisfy `S (i+1) = S i + ξ (i+1)`. -/
theorem martingalePartialSum_succ (ξ : ℕ → Ω → ℝ) (i : ℕ) :
    martingalePartialSum ξ (i + 1) = martingalePartialSum ξ i + ξ (i + 1) := by
  funext ω
  simp only [martingalePartialSum, Pi.add_apply]
  rw [Finset.sum_Icc_succ_top (by omega) (fun j => ξ j ω)]

/-- The cross term `∫ |S|^{p-2} ξ²` equals `∫ |S|^{p-2} μ[ξ² | m]`: the `m`-measurable
factor `|S|^{p-2}` pulls out. -/
theorem integral_rpow_mul_condExp_sq_eq [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ m₀) {p : ℝ} {S ξ v : Ω → ℝ}
    (hS : StronglyMeasurable[m] fun ω => |S ω| ^ (p - 2))
    (hv : μ[fun ω => ξ ω ^ 2 | m] =ᵐ[μ] v)
    (hSξ2 : Integrable (fun ω => |S ω| ^ (p - 2) * ξ ω ^ 2) μ)
    (hξ2 : Integrable (fun ω => ξ ω ^ 2) μ) :
    ∫ ω, |S ω| ^ (p - 2) * ξ ω ^ 2 ∂μ
      = ∫ ω, |S ω| ^ (p - 2) * v ω ∂μ := by
  have hpoint := condExp_mul_of_stronglyMeasurable_left (μ := μ) (m := m) hS hSξ2 hξ2
  have h1 : ∫ ω, |S ω| ^ (p - 2) * ξ ω ^ 2 ∂μ
      = ∫ ω, ((fun ω => |S ω| ^ (p - 2)) * (μ[fun ω => ξ ω ^ 2 | m])) ω ∂μ := by
    calc ∫ ω, |S ω| ^ (p - 2) * ξ ω ^ 2 ∂μ
        = ∫ ω, (μ[fun ω => |S ω| ^ (p - 2) * ξ ω ^ 2 | m]) ω ∂μ :=
          (integral_condExp hm).symm
      _ = ∫ ω, ((fun ω => |S ω| ^ (p - 2)) * (μ[fun ω => ξ ω ^ 2 | m])) ω ∂μ :=
          integral_congr_ae hpoint
  have h2 : ∫ ω, ((fun ω => |S ω| ^ (p - 2)) * (μ[fun ω => ξ ω ^ 2 | m])) ω ∂μ
      = ∫ ω, ((fun ω => |S ω| ^ (p - 2)) * v) ω ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hv] with ω hω
    simp only [Pi.mul_apply]
    rw [hω]
  rw [h1, h2]
  simp only [Pi.mul_apply]

/-- **The one-step estimate along a filtration.**  For `p ≥ 2` there is a universal `C ≥ 1`
such that, for a filtration `F`, a family `ξ` of martingale differences, and
`v i = μ[ξ i² | F (i-1)]`, the partial sums `S i = ∑_{j=1}^{i} ξ_j` satisfy

  `E |S (i+1)|^p ≤ E |S i|^p + C (E[|S i|^{p-2} v (i+1)] + E |ξ (i+1)|^p)`.

The measurability and integrability of the partial sums are taken as hypotheses; they are
supplied by the caller from the filtration and the moment bounds. -/
theorem martingaleOneStep {p : ℝ} (hp : 2 ≤ p) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {Ω : Type*} {m₀ : MeasurableSpace Ω} (μ : @Measure Ω m₀) [IsProbabilityMeasure μ]
        (F : Filtration ℕ m₀) (ξ : ℕ → Ω → ℝ) (v : ℕ → Ω → ℝ),
        (∀ i, AEMeasurable (martingalePartialSum ξ i) μ) →
        (∀ i, StronglyMeasurable[F i] (fun ω => |martingalePartialSum ξ i ω| ^ p)) →
        (∀ i, StronglyMeasurable[F i]
          (fun ω => |martingalePartialSum ξ i ω| ^ (p - 2) * martingalePartialSum ξ i ω)) →
        (∀ i, StronglyMeasurable[F i] (fun ω => |martingalePartialSum ξ i ω| ^ (p - 2))) →
        (∀ i, μ[ξ (i + 1) | F i] =ᵐ[μ] 0) →
        (∀ i, μ[fun ω => ξ (i + 1) ω ^ 2 | F i] =ᵐ[μ] v (i + 1)) →
        (∀ i, Integrable (fun ω => |martingalePartialSum ξ i ω| ^ p) μ) →
        (∀ i, Integrable (fun ω => |martingalePartialSum ξ i ω| ^ (p - 2)
          * martingalePartialSum ξ i ω * ξ (i + 1) ω) μ) →
        (∀ i, Integrable (fun ω => |martingalePartialSum ξ i ω| ^ (p - 2)
          * ξ (i + 1) ω ^ 2) μ) →
        (∀ i, Integrable (fun ω => |martingalePartialSum ξ i ω| ^ (p - 2)
          * v (i + 1) ω) μ) →
        (∀ i, Integrable (ξ (i + 1)) μ) →
        (∀ i, Integrable (fun ω => ξ (i + 1) ω ^ 2) μ) →
        (∀ i, Integrable (fun ω => |ξ (i + 1) ω| ^ p) μ) →
        ∀ i,
          ∫ ω, |martingalePartialSum ξ (i + 1) ω| ^ p ∂μ
            ≤ ∫ ω, |martingalePartialSum ξ i ω| ^ p ∂μ
              + C * (∫ ω, |martingalePartialSum ξ i ω| ^ (p - 2) * v (i + 1) ω ∂μ
                + ∫ ω, |ξ (i + 1) ω| ^ p ∂μ) := by
  obtain ⟨C, hC1, hstep⟩ := integral_abs_add_rpow_le hp
  refine ⟨C, hC1, ?_⟩
  intro Ω m₀ μ _ F ξ v hAe hAst hfst hf2st hmean hv hAint hfξ hf2ξ2 _hf2v hξint hξ2int
    hξpint i
  have hstep_i := hstep (m := F i) μ (F.le i) (martingalePartialSum ξ i) (ξ (i + 1))
    (hAe i) (hAst i) (hfst i) (hmean i) (hAint i) (hfξ i) (hf2ξ2 i)
    (hξint i) (hξ2int i) (hξpint i)
  have hvpull := integral_rpow_mul_condExp_sq_eq (μ := μ) (m := F i) (F.le i)
    (hf2st i) (hv i) (hf2ξ2 i) (hξ2int i)
  have hSsucc : (fun ω => |martingalePartialSum ξ i ω + ξ (i + 1) ω| ^ p)
      = fun ω => |martingalePartialSum ξ (i + 1) ω| ^ p := by
    funext ω
    have h := congrFun (martingalePartialSum_succ ξ i) ω
    simp only [Pi.add_apply] at h
    rw [← h]
  rw [hSsucc] at hstep_i
  rw [hvpull] at hstep_i
  exact hstep_i

end LatticeProb
