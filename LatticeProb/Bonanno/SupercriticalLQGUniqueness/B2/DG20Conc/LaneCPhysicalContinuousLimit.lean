/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPhysicalContinuousLimit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPhysicalContinuousArc

 








set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise

 

theorem laneC_physical_boundary_resampling_le_of_continuous_arc
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) (Q : PsiParams) (ξ : ℝ)
    {K n : ℕ} (hKn : K ≤ n) {s r : ℝ}
    (hσ : ∀ t ∈ Icc (((2 : ℝ)⁻¹ ^ n) ^ 2)
      (((2 : ℝ)⁻¹ ^ K) ^ 2), Q.sigma t ≤ s)
    (hr : (2 : ℝ)⁻¹ ^ K + 2 * s ≤ r) :
    ∀ᵐ z ∂(P.prod P), ∀ b ∈ T20B.nearIdx K,
      ∀ α γ : ℝ → ℂ,
      ContinuousOn α (Icc (0 : ℝ) 1) →
      (∀ t ∈ Icc (0 : ℝ) 1,
        r < dist (α t) (T20.dyCenter K b) ∧
          dist (α t) (T20.dyCenter K b) < 2 * r) →
      (∀ t ∈ Icc (0 : ℝ) 1, α t ∈ (rectAB 1 1).toSet) →
      AdmPath (rectAB 1 1).toSet (rectAB 1 1).side₁
        (rectAB 1 1).side₂ γ →
      lfppLen ξ (fun x => psiMN Q W P 0 n x z.1) γ ≠ ⊤ →
      ∀ M : ℝ, 0 < M →
        (lfppContMetric ξ (fun x => psiMN Q W P 0 n x z.1)
          ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont z.1)).len α 0 1 <
            ENNReal.ofReal M →
      ∀ t₀ t₁ : ℝ,
        t₀ ∈ Icc (0 : ℝ) 1 → t₁ ∈ Icc (0 : ℝ) 1 → t₀ ≤ t₁ →
        ((γ t₀ = α 0 ∧ ∀ t ∈ Icc (0 : ℝ) t₀,
            r ≤ dist (γ t) (T20.dyCenter K b)) ∨
          (t₀ = 0 ∧ α 0 ∈ (rectAB 1 1).side₁)) →
        ((γ t₁ = α 1 ∧ ∀ t ∈ Icc t₁ (1 : ℝ),
            r ≤ dist (γ t) (T20.dyCenter K b)) ∨
          (t₁ = 1 ∧ α 1 ∈ (rectAB 1 1).side₂)) →
      (rectLen ξ (fun x => psiMN Q W P 0 n x z.1 -
        T20B.blkKn Q W P K n b x z.1 +
          T20B.blkKn Q W P K n b x z.2) (rectAB 1 1)).toReal ≤
        (lfppLen ξ (fun x => psiMN Q W P 0 n x z.1) γ).toReal + M := by
  filter_upwards [laneC_physical_boundary_resampling_lt_of_continuous_arc
      hW Q ξ hKn hσ hr] with z hz b hb α γ hα hring hsq hγ hγfin
    M hM hlen t₀ t₁ ht₀ ht₁ htord hstart hend
  apply le_of_forall_pos_lt_add
  intro η hη
  have h := hz b hb α γ hα hring hsq hγ hγfin M η hM hη hlen
    t₀ t₁ ht₀ ht₁ htord hstart hend
  simpa only [add_assoc] using h

end SupercriticalLQGUniqueness.B2.DG20Conc
