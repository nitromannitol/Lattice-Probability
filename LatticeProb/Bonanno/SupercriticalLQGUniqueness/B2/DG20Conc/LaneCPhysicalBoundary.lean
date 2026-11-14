/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPhysicalBoundary at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCBoundaryDetour
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCSupportAnnulus

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise

theorem laneC_physical_boundary_resampling_le_of_arc
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) (Q : PsiParams) (ξ : ℝ)
    {K n : ℕ} (hKn : K ≤ n) {s r : ℝ}
    (hσ : ∀ t ∈ Icc (((2 : ℝ)⁻¹ ^ n) ^ 2)
      (((2 : ℝ)⁻¹ ^ K) ^ 2), Q.sigma t ≤ s)
    (hr : (2 : ℝ)⁻¹ ^ K + 2 * s ≤ r) :
    ∀ᵐ z ∂(P.prod P), ∀ b ∈ T20B.nearIdx K,
      ∀ ρ γ : ℝ → ℂ,
      (∀ t ∈ Icc (0 : ℝ) 1,
        r < dist (ρ t) (T20.dyCenter K b) ∧
          dist (ρ t) (T20.dyCenter K b) < 2 * r) →
      (∀ t ∈ Icc (0 : ℝ) 1, ρ t ∈ (rectAB 1 1).toSet) →
      IsPiecewiseC1Path ρ (ρ 0) (ρ 1) →
      lfppLen ξ (fun x => psiMN Q W P 0 n x z.1) ρ ≠ ⊤ →
      AdmPath (rectAB 1 1).toSet (rectAB 1 1).side₁
        (rectAB 1 1).side₂ γ →
      lfppLen ξ (fun x => psiMN Q W P 0 n x z.1) γ ≠ ⊤ →
      ∀ t₀ t₁ s₀ s₁ : ℝ,
        t₀ ∈ Icc (0 : ℝ) 1 → t₁ ∈ Icc (0 : ℝ) 1 → t₀ ≤ t₁ →
        s₀ ∈ Icc (0 : ℝ) 1 → s₁ ∈ Icc (0 : ℝ) 1 →
        ((γ t₀ = ρ s₀ ∧ ∀ t ∈ Icc (0 : ℝ) t₀,
            r ≤ dist (γ t) (T20.dyCenter K b)) ∨
          (t₀ = 0 ∧ ρ s₀ ∈ (rectAB 1 1).side₁)) →
        ((γ t₁ = ρ s₁ ∧ ∀ t ∈ Icc t₁ (1 : ℝ),
            r ≤ dist (γ t) (T20.dyCenter K b)) ∨
          (t₁ = 1 ∧ ρ s₁ ∈ (rectAB 1 1).side₂)) →
      (rectLen ξ (fun x => psiMN Q W P 0 n x z.1 -
        T20B.blkKn Q W P K n b x z.1 +
          T20B.blkKn Q W P K n b x z.2) (rectAB 1 1)).toReal ≤
        (lfppLen ξ (fun x => psiMN Q W P 0 n x z.1) γ).toReal +
          (lfppLen ξ (fun x => psiMN Q W P 0 n x z.1) ρ).toReal := by
  filter_upwards [laneC_resampled_field_eq_on_outer_region hW Q hKn hσ
      (T20.dyCenter K) ((2 : ℝ)⁻¹ ^ K) r
      (fun b _ => laneC_hoBlock_subset_center_ball K b) hr]
    with z hz b hb ρ γ hring hsq hρ hρfin hγ hγfin
      t₀ t₁ s₀ s₁ ht₀ ht₁ htord hs₀ hs₁ hstart hend
  let Fr : Set ℂ := {x | r ≤ dist x (T20.dyCenter K b)}
  have hfield : ∀ x ∈ Fr,
      psiMN Q W P 0 n x z.1 - T20B.blkKn Q W P K n b x z.1 +
        T20B.blkKn Q W P K n b x z.2 = psiMN Q W P 0 n x z.1 :=
    fun x hx => hz b hb x hx
  obtain ⟨z₀, hz₀, z₁, hz₁, hpath, hU⟩ := hγ
  have hγ' : AdmPath (rectAB 1 1).toSet (rectAB 1 1).side₁
      (rectAB 1 1).side₂ γ := ⟨z₀, hz₀, z₁, hz₁, hpath, hU⟩
  have hsqγ : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ (rectAB 1 1).toSet := hU
  apply laneC_one_boundary_detour_le (Fr := Fr) hfield hγ' hγfin hρ hρfin
    (fun t ht => ⟨hsq t ht, (hring t ht).1.le⟩)
    ht₀ ht₁ htord hs₀ hs₁
  · rcases hstart with ⟨hmeet, hbefore⟩ | hside
    · left
      exact ⟨hmeet, fun t ht =>
        ⟨hsqγ t ⟨ht.1, ht.2.trans ht₀.2⟩, hbefore t ht⟩⟩
    · exact Or.inr hside
  · rcases hend with ⟨hmeet, hafter⟩ | hside
    · left
      exact ⟨hmeet, fun t ht =>
        ⟨hsqγ t ⟨ht₁.1.trans ht.1, ht.2⟩, hafter t ht⟩⟩
    · exact Or.inr hside

end SupercriticalLQGUniqueness.B2.DG20Conc
