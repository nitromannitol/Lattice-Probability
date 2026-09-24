/-
A martingale with conditionally centred increments on an abstract filtration has second moment
equal to the sum of its increments' second moments. `Ω` is an arbitrary probability space,
`𝔽 : ℕ → MeasurableSpace Ω` an arbitrary filtration (each piece below the ambient σ-algebra
`m₀`), and `ξ k` an arbitrary sequence of real-valued, square-integrable increments whose
PARTIAL SUMS are `𝔽`-adapted (`∑_{k<t} ξ k` is `𝔽 t`-measurable for every `t`) with
`E[ξ k | 𝔽 k] = 0`.

The hypothesis is adaptedness of the partial sums rather than `𝔽(k+1)`-measurability of each
individual increment, because an increment built from a `𝔽 k`-measurable random range of raw
terms is in general only almost surely, not pathwise, `𝔽(k+1)`-measurable. The orthogonality of
distinct increments this file needs is the ordinary tower-property pull-out
`E[X·Y] = E[X·E[Y|G]]` for `X` a `G`-measurable partial sum of earlier increments and
`Y := ξ t`, `G := 𝔽 t`; no covariance structure beyond `E[ξ t | 𝔽 t] =ᵐ 0` is assumed or used, so
the increments need not be independent, only conditionally centred.

Moved from Parking-Sharpness.
-/
import Mathlib

open MeasureTheory

noncomputable section

namespace LatticeProb.Scaling.RoundMartingale

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : @Measure Ω m₀} [IsProbabilityMeasure μ]

/-- **The sum-of-squares identity for a martingale with conditionally centred increments on an
abstract filtration.**  If `𝔽 : ℕ → MeasurableSpace Ω` has every `𝔽 k ≤ m₀`, `ξ k` is
square-integrable with `E[ξ k | 𝔽 k] =ᵐ 0`, and the partial sum `∑_{k<t} ξ k` is `𝔽 t`-measurable
for every `t`, then that partial sum is square-integrable and its second moment is the sum of
the increments' second moments. -/
theorem integral_sq_sum_eq_sum_integral_sq
    (𝔽 : ℕ → MeasurableSpace Ω) (hle : ∀ k, 𝔽 k ≤ m₀)
    (ξ : ℕ → Ω → ℝ)
    (hSnmeas : ∀ t : ℕ, Measurable[𝔽 t] (fun ω => ∑ k ∈ Finset.range t, ξ k ω))
    (hint : ∀ k, Integrable (ξ k) μ)
    (hint2 : ∀ k, Integrable (fun ω => (ξ k ω) ^ 2) μ)
    (hcond0 : ∀ k, μ[ξ k | 𝔽 k] =ᵐ[μ] 0) (t : ℕ) :
    Integrable (fun ω => (∑ k ∈ Finset.range t, ξ k ω) ^ 2) μ ∧
      ∫ ω, (∑ k ∈ Finset.range t, ξ k ω) ^ 2 ∂μ
        = ∑ k ∈ Finset.range t, ∫ ω, (ξ k ω) ^ 2 ∂μ := by
  induction t with
  | zero => simp
  | succ t ih =>
    obtain ⟨ihI0, ihE0⟩ := ih
    set Sn : Ω → ℝ := fun ω => ∑ k ∈ Finset.range t, ξ k ω with hSndef
    have ihI : Integrable (fun ω => (Sn ω) ^ 2) μ := ihI0
    have ihE : ∫ ω, (Sn ω) ^ 2 ∂μ = ∑ k ∈ Finset.range t, ∫ ω, (ξ k ω) ^ 2 ∂μ := ihE0
    have hSnmeas' : Measurable[𝔽 t] Sn := hSnmeas t
    haveI hfinT : IsFiniteMeasure (μ.trim (hle t)) := isFiniteMeasure_trim (hle t)
    have hSnmeasamb : AEStronglyMeasurable Sn μ :=
      (hSnmeas'.mono (hle t) le_rfl).aestronglyMeasurable
    have hξtmeasamb : AEStronglyMeasurable (ξ t) μ := (hint t).aestronglyMeasurable
    have hprodmeas : AEStronglyMeasurable (fun ω => Sn ω * ξ t ω) μ := hSnmeasamb.mul hξtmeasamb
    -- Integrability of the cross term, by AM-GM domination.
    have hdomI : Integrable (fun ω => ((Sn ω) ^ 2 + (ξ t ω) ^ 2) / 2) μ :=
      (ihI.add (hint2 t)).div_const 2
    have hcrossI : Integrable (fun ω => Sn ω * ξ t ω) μ := by
      refine Integrable.mono' hdomI hprodmeas (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> nlinarith [sq_nonneg (Sn ω - ξ t ω), sq_nonneg (Sn ω + ξ t ω)]
    -- The cross term integrates to zero: the tower-property pull-out plus `E[ξ t|𝔽 t]=0`.
    have hpullout := MeasureTheory.condExp_mul_of_aestronglyMeasurable_left
      (m := 𝔽 t) (μ := μ) (f := Sn) (g := ξ t)
      hSnmeas'.aestronglyMeasurable hcrossI (hint t)
    have hSnZero : (fun ω => Sn ω * (μ[ξ t | 𝔽 t]) ω) =ᵐ[μ] fun _ : Ω => (0 : ℝ) := by
      filter_upwards [hcond0 t] with ω hω
      simp [hω]
    have heq0 : μ[fun ω => Sn ω * ξ t ω | 𝔽 t] =ᵐ[μ] fun _ : Ω => (0 : ℝ) :=
      hpullout.trans hSnZero
    have hcrossZero : ∫ ω, Sn ω * ξ t ω ∂μ = 0 := by
      calc ∫ ω, Sn ω * ξ t ω ∂μ
          = ∫ ω, (μ[fun ω => Sn ω * ξ t ω | 𝔽 t]) ω ∂μ := (integral_condExp (hle t)).symm
        _ = ∫ _ : Ω, (0 : ℝ) ∂μ := integral_congr_ae heq0
        _ = 0 := integral_zero _ _
    -- Assemble.
    have hpt : ∀ ω, (∑ k ∈ Finset.range (t + 1), ξ k ω) ^ 2
        = (Sn ω) ^ 2 + 2 * (Sn ω * ξ t ω) + (ξ t ω) ^ 2 := by
      intro ω; rw [Finset.sum_range_succ, hSndef]; ring
    have hrw : (fun ω => (∑ k ∈ Finset.range (t + 1), ξ k ω) ^ 2)
        = fun ω => (Sn ω) ^ 2 + 2 * (Sn ω * ξ t ω) + (ξ t ω) ^ 2 := funext hpt
    have hfullI : Integrable (fun ω => (∑ k ∈ Finset.range (t + 1), ξ k ω) ^ 2) μ := by
      rw [hrw]; exact (ihI.add (hcrossI.const_mul 2)).add (hint2 t)
    refine ⟨hfullI, ?_⟩
    have hsplit1 : ∫ ω, (Sn ω) ^ 2 + 2 * (Sn ω * ξ t ω) + (ξ t ω) ^ 2 ∂μ
        = ∫ ω, (Sn ω) ^ 2 + 2 * (Sn ω * ξ t ω) ∂μ + ∫ ω, (ξ t ω) ^ 2 ∂μ :=
      integral_add (ihI.add (hcrossI.const_mul 2)) (hint2 t)
    have hsplit2 : ∫ ω, (Sn ω) ^ 2 + 2 * (Sn ω * ξ t ω) ∂μ
        = ∫ ω, (Sn ω) ^ 2 ∂μ + ∫ ω, 2 * (Sn ω * ξ t ω) ∂μ :=
      integral_add ihI (hcrossI.const_mul 2)
    have hsplit3 : ∫ ω, 2 * (Sn ω * ξ t ω) ∂μ = 2 * ∫ ω, Sn ω * ξ t ω ∂μ :=
      integral_const_mul 2 _
    rw [hrw, hsplit1, hsplit2, hsplit3, hcrossZero, mul_zero, add_zero, Finset.sum_range_succ, ihE]

end LatticeProb.Scaling.RoundMartingale

end
