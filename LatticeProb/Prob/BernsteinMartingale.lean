/-
# The one-step integrated estimate behind `Parking.External.Bernstein`

The martingale Rosenthal–Burkholder inequality (`Parking.External.Bernstein`) is
assembled from a one-step moment estimate for a martingale difference.  With `S`
measurable for the past `m`, `ξ` a martingale difference (`μ[ξ | m] = 0`), and `p ≥ 2`,
the pointwise second-order bound

  `|S + ξ|^p ≤ |S|^p + p |S|^{p-2} S ξ + C (|S|^{p-2} ξ² + |ξ|^p)`

(`LatticeProb.exists_abs_add_rpow_bound`) has conditional expectation

  `E[|S + ξ|^p | m] = |S|^p + C (|S|^{p-2} E[ξ² | m] + E[|ξ|^p | m])`

(`LatticeProb.condExp_abs_add_rpow_eq`, `Prob/MartingaleRosenthal.lean`).  This file
integrates that identity: the linear term has mean zero, so

  `E |S + ξ|^p ≤ E |S|^p + C (E[|S|^{p-2} ξ²] + E |ξ|^p)`.

This is step 1 of the route recorded in `Prob/MartingaleRosenthal.lean.DONE`; the
remaining assembly (Pinelis's induction over the filtration and the factorial-moment
clause) is recorded in `scratch/pk/bernstein-route.md`.
-/
import LatticeProb.Prob.MartingaleRosenthal
import LatticeProb.Prob.PowerIneq

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace LatticeProb

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀}

/-- **The linear term of the second-order bound has mean zero.**  If `S` is
`m`-strongly-measurable, `E[ξ | m] = 0`, and `|S|^{p-2} S ξ` is integrable, then
`E[|S|^{p-2} S ξ | m] = 0`: the `m`-measurable factor `|S|^{p-2} S` pulls out of the
conditional expectation and annihilates `E[ξ | m]`. -/
theorem condExp_mul_mul_ae_eq_zero' [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    {p : ℝ} {S ξ : Ω → ℝ}
    (hS : StronglyMeasurable[m] fun ω => |S ω| ^ (p - 2) * S ω)
    (hmean : μ[ξ | m] =ᵐ[μ] 0)
    (hint : Integrable (fun ω => |S ω| ^ (p - 2) * S ω * ξ ω) μ)
    (hξ : Integrable ξ μ) :
    μ[fun ω => |S ω| ^ (p - 2) * S ω * ξ ω | m] =ᵐ[μ] (0 : Ω → ℝ) := by
  change μ[(fun ω => |S ω| ^ (p - 2) * S ω) * ξ | m] =ᵐ[μ] (0 : Ω → ℝ)
  have hpull := condExp_mul_of_stronglyMeasurable_left (μ := μ) (m := m) hS hint hξ
  filter_upwards [hpull, hmean] with ω e1 e2
  simp only [Pi.mul_apply, Pi.zero_apply] at e1 e2 ⊢
  rw [e1, e2, mul_zero]

/-- **Conditional Lyapunov bound.**  For `p ≥ 2`,
`E[ξ² | m] ≤ (E[|ξ|^p | m])^{2/p}`, the conditional form of `L² ⊆ L^p` on a
probability space.  This is what turns the cross term `E[|S|^{p-2} ξ²]` of the
one-step estimate into the exponent-`p/2` quantity of the Rosenthal bound. -/
theorem condExp_sq_le_rpow_condExp {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    [IsProbabilityMeasure μ] {p : ℝ} (hp : 2 ≤ p) {ξ : Ω → ℝ}
    (hξ2 : Integrable (fun ω => ξ ω ^ 2) μ)
    (hξp : Integrable (fun ω => |ξ ω| ^ p) μ) :
    μ[fun ω => ξ ω ^ 2 | m]
      ≤ᵐ[μ] fun ω => ((μ[fun ω => |ξ ω| ^ p | m]) ω) ^ (2 / p) := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hq1 : (1 : ℝ) ≤ p / 2 := by linarith
  have hq0 : (0 : ℝ) < p / 2 := by linarith
  set f : Ω → ℝ := fun ω => ξ ω ^ 2 with hf
  have hfnn : ∀ ω, f ω ∈ Set.Ici (0 : ℝ) := fun ω => by
    simp only [Set.mem_Ici, hf]; positivity
  have hφf : (fun ω => f ω ^ (p / 2)) = fun ω => |ξ ω| ^ p := by
    funext ω
    change (ξ ω ^ 2) ^ (p / 2) = |ξ ω| ^ p
    rw [show |ξ ω| ^ p = |ξ ω| ^ (2 * (p / 2)) by congr 1; ring,
      Real.rpow_mul (abs_nonneg (ξ ω)) (2 : ℝ) (p / 2)]
    congr 1
    exact_mod_cast (sq_abs (ξ ω) : |ξ ω| ^ 2 = ξ ω ^ 2).symm
  have hl : LowerSemicontinuousOn (fun x : ℝ => x ^ (p / 2)) (Set.Ici 0) :=
    (Real.continuous_rpow_const hq0.le).lowerSemicontinuous.lowerSemicontinuousOn _
  have hφint : Integrable ((fun x : ℝ => x ^ (p / 2)) ∘ f) μ := by
    rw [show ((fun x : ℝ => x ^ (p / 2)) ∘ f) = fun ω => |ξ ω| ^ p from hφf]
    exact hξp
  have hmain : (fun ω => (μ[f | m]) ω ^ (p / 2)) ≤ᵐ[μ] μ[fun ω => |ξ ω| ^ p | m] :=
    ((convexOn_rpow hq1).map_condExp_le hm hl (Filter.Eventually.of_forall hfnn)
      isClosed_Ici hξ2 hφint).trans
      (condExp_congr_ae (Filter.Eventually.of_forall fun ω => congrFun hφf ω)).le
  have hZnn : 0 ≤ᵐ[μ] μ[f | m] :=
    condExp_nonneg (Filter.Eventually.of_forall fun ω => by
      simp only [hf]; positivity)
  have hWnn : 0 ≤ᵐ[μ] μ[fun ω => |ξ ω| ^ p | m] :=
    condExp_nonneg (Filter.Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg _) _)
  filter_upwards [hmain, hZnn, hWnn] with ω hm1 hZ _hW
  have hexp : p / 2 * (2 / p) = 1 := by field_simp
  have hpow : ((μ[f | m]) ω ^ (p / 2)) ^ (2 / p) = (μ[f | m]) ω := by
    rw [← Real.rpow_mul hZ, hexp, Real.rpow_one]
  calc (μ[f | m]) ω
      = ((μ[f | m]) ω ^ (p / 2)) ^ (2 / p) := hpow.symm
    _ ≤ ((μ[fun ω => |ξ ω| ^ p | m]) ω) ^ (2 / p) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hZ _) hm1 (by positivity)

/-- **The integrated one-step estimate.**  For `p ≥ 2` there is a universal `C ≥ 1`
such that, for a martingale difference `ξ` with `μ[ξ | m] = 0` and an `m`-measurable
partial sum `S`, the pointwise second-order bound integrates to

  `E |S + ξ|^p ≤ E |S|^p + C (E[|S|^{p-2} ξ²] + E |ξ|^p)`.

This is the one-step estimate of Pinelis's Rosenthal–Burkholder induction. -/
theorem integral_abs_add_rpow_le {p : ℝ} (hp : 2 ≤ p) :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {Ω : Type*} {m₀ : MeasurableSpace Ω} (μ : @Measure Ω m₀) [IsProbabilityMeasure μ]
        {m : MeasurableSpace Ω} (hm : m ≤ m₀) [SigmaFinite (μ.trim hm)] (S ξ : Ω → ℝ),
        AEMeasurable S μ →
        StronglyMeasurable[m] (fun ω => |S ω| ^ p) →
        StronglyMeasurable[m] (fun ω => |S ω| ^ (p - 2) * S ω) →
        μ[ξ | m] =ᵐ[μ] 0 →
        Integrable (fun ω => |S ω| ^ p) μ →
        Integrable (fun ω => |S ω| ^ (p - 2) * S ω * ξ ω) μ →
        Integrable (fun ω => |S ω| ^ (p - 2) * ξ ω ^ 2) μ →
        Integrable ξ μ →
        Integrable (fun ω => ξ ω ^ 2) μ →
        Integrable (fun ω => |ξ ω| ^ p) μ →
        ∫ ω, |S ω + ξ ω| ^ p ∂μ ≤
          ∫ ω, |S ω| ^ p ∂μ
            + C * (∫ ω, |S ω| ^ (p - 2) * ξ ω ^ 2 ∂μ + ∫ ω, |ξ ω| ^ p ∂μ) := by
  obtain ⟨C, hC1, hpt⟩ := exists_abs_add_rpow_bound hp
  refine ⟨C, hC1, ?_⟩
  intro Ω m₀ μ _ m hm _ S ξ hSmeas hAstrong hfstrong hmean hA hfξ hf2ξ2 hξ hξ2 hξp
  have hp0 : (0 : ℝ) ≤ p := by linarith
  -- the pointwise second-order bound
  have hpoint : ∀ ω, |S ω + ξ ω| ^ p
      ≤ |S ω| ^ p + p * |S ω| ^ (p - 2) * S ω * ξ ω
        + C * (|S ω| ^ (p - 2) * ξ ω ^ 2 + |ξ ω| ^ p) :=
    fun ω => hpt (S ω) (ξ ω)
  -- integrability of the right side
  have hLint : Integrable (fun ω => p * |S ω| ^ (p - 2) * S ω * ξ ω) μ :=
    (by simpa only [mul_assoc] using hfξ.const_mul p :
      Integrable (fun ω => p * |S ω| ^ (p - 2) * S ω * ξ ω) μ)
  have hQint : Integrable (fun ω => C * (|S ω| ^ (p - 2) * ξ ω ^ 2 + |ξ ω| ^ p)) μ :=
    (hf2ξ2.add hξp).const_mul C
  have hDint : Integrable (fun ω => |S ω| ^ p
      + p * |S ω| ^ (p - 2) * S ω * ξ ω
      + C * (|S ω| ^ (p - 2) * ξ ω ^ 2 + |ξ ω| ^ p)) μ :=
    (hA.add hLint).add hQint
  -- integrability of the left side, from the pointwise bound
  have hXmeas : AEMeasurable (fun ω => |S ω + ξ ω| ^ p) μ :=
    (Real.continuous_rpow_const hp0).measurable.comp_aemeasurable
      (continuous_abs.measurable.comp_aemeasurable (hSmeas.add hξ.aemeasurable))
  have hXint : Integrable (fun ω => |S ω + ξ ω| ^ p) μ := by
    refine Integrable.mono' hDint hXmeas.aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    exact hpoint ω
  -- the linear term vanishes
  have hlin : ∫ ω, |S ω| ^ (p - 2) * S ω * ξ ω ∂μ = 0 := by
    have hcond := integral_condExp (μ := μ) (m := m) hm
      (f := fun ω => |S ω| ^ (p - 2) * S ω * ξ ω)
    rw [← hcond]
    exact integral_eq_zero_of_ae
      (condExp_mul_mul_ae_eq_zero' (μ := μ) (m := m) hfstrong hmean hfξ hξ)
  have hlinmul : ∫ ω, p * |S ω| ^ (p - 2) * S ω * ξ ω ∂μ = 0 := by
    rw [show (fun ω => p * |S ω| ^ (p - 2) * S ω * ξ ω)
        = fun ω => p * (|S ω| ^ (p - 2) * S ω * ξ ω) from by
      funext ω; ring,
      integral_const_mul, hlin, mul_zero]
  -- split the integral of the right side
  have hDval : ∫ ω, (|S ω| ^ p
        + p * |S ω| ^ (p - 2) * S ω * ξ ω
        + C * (|S ω| ^ (p - 2) * ξ ω ^ 2 + |ξ ω| ^ p)) ∂μ
      = ∫ ω, |S ω| ^ p ∂μ
        + C * (∫ ω, |S ω| ^ (p - 2) * ξ ω ^ 2 ∂μ + ∫ ω, |ξ ω| ^ p ∂μ) := by
    have h1 : ∫ ω, (|S ω| ^ p + p * |S ω| ^ (p - 2) * S ω * ξ ω
          + C * (|S ω| ^ (p - 2) * ξ ω ^ 2 + |ξ ω| ^ p)) ∂μ
        = ∫ ω, (|S ω| ^ p + p * |S ω| ^ (p - 2) * S ω * ξ ω) ∂μ
          + ∫ ω, C * (|S ω| ^ (p - 2) * ξ ω ^ 2 + |ξ ω| ^ p) ∂μ :=
      integral_add (hA.add hLint) hQint
    have h2 : ∫ ω, (|S ω| ^ p + p * |S ω| ^ (p - 2) * S ω * ξ ω) ∂μ
        = ∫ ω, |S ω| ^ p ∂μ + ∫ ω, p * |S ω| ^ (p - 2) * S ω * ξ ω ∂μ :=
      integral_add hA hLint
    rw [h1, h2, integral_const_mul, integral_add hf2ξ2 hξp, hlinmul, add_zero]
  calc ∫ ω, |S ω + ξ ω| ^ p ∂μ
      ≤ ∫ ω, (|S ω| ^ p
          + p * |S ω| ^ (p - 2) * S ω * ξ ω
          + C * (|S ω| ^ (p - 2) * ξ ω ^ 2 + |ξ ω| ^ p)) ∂μ :=
        integral_mono hXint hDint (fun ω => hpoint ω)
    _ = ∫ ω, |S ω| ^ p ∂μ
          + C * (∫ ω, |S ω| ^ (p - 2) * ξ ω ^ 2 ∂μ + ∫ ω, |ξ ω| ^ p ∂μ) := hDval

end LatticeProb
