/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistGradientEvent at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistSquareCover

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Topology
open LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.SupTail

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 

theorem pt_dist_grad_bounded_tail (V : Set ℂ)
    (hV : Bornology.IsBounded V) :
    ∃ C σ2 : ℝ, 0 < C ∧ 0 < σ2 ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
        {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
        ∀ (k : ℕ) (Y : ℂ → Ω → ℝ),
          (∀ x, (fun ω => Y x ω) =ᵐ[P] phi W ((2 : ℝ) ^ k)⁻¹ 1 x) →
          (∀ ω, ContDiff ℝ 1 fun x => Y x ω) →
          ∀ t : ℝ, 0 ≤ t →
          P.real {ω | ∃ z ∈ V,
            t ≤ ((2 : ℝ) ^ k)⁻¹ * ‖fderiv ℝ (fun x => Y x ω) z‖} ≤
            C * 4 ^ k * Real.exp (-t ^ 2 / (2 * σ2)) := by
  obtain ⟨F, hcover⟩ := exists_pt_dist_square_cover V hV
  obtain ⟨C₀, σ2, hC₀, hσ2, htail⟩ := pt_dist_grad_shift_tail
  let C : ℝ := (F.card + 1) * C₀
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, σ2, hC, hσ2, ?_⟩
  intro Ω _ P W hW k Y hY hYc t ht
  letI : IsProbabilityMeasure P := hW.isProbabilityMeasure
  let bad : ℂ → Set Ω := fun c => {ω | t ≤ ((2 : ℝ) ^ k)⁻¹ *
    ⨆ z : ferniqueBox 0 1,
      ‖fderiv ℝ (fun x => Y (x + c) ω) z‖}
  have hbdd (c : ℂ) (ω : Ω) :
      BddAbove (range fun z : ferniqueBox 0 1 =>
        ‖fderiv ℝ (fun x => Y (x + c) ω) z‖) := by
    have hc : Continuous fun z => ‖fderiv ℝ (fun x => Y (x + c) ω) z‖ :=
      (((hYc ω).comp (contDiff_id.add contDiff_const)).continuous_fderiv
        (by norm_num)).norm
    have h := (isCompact_ferniqueBox 0 1).bddAbove_image hc.continuousOn
    rwa [image_eq_range] at h
  have hsub : {ω | ∃ z ∈ V,
      t ≤ ((2 : ℝ) ^ k)⁻¹ * ‖fderiv ℝ (fun x => Y x ω) z‖} ⊆
      ⋃ c ∈ F, bad c := by
    intro ω hω
    obtain ⟨z, hz, hbad⟩ := hω
    obtain ⟨c, hc, hzc⟩ := hcover z hz
    refine mem_biUnion hc ?_
    change t ≤ ((2 : ℝ) ^ k)⁻¹ *
      ⨆ v : ferniqueBox 0 1,
        ‖fderiv ℝ (fun x => Y (x + c) ω) v‖
    have heq : ‖fderiv ℝ (fun x => Y x ω) z‖ =
        ‖fderiv ℝ (fun x => Y (x + c) ω) (z - c)‖ := by
      rw [fderiv_comp_add_right (f := fun x => Y x ω), sub_add_cancel]
    rw [heq] at hbad
    exact hbad.trans (mul_le_mul_of_nonneg_left
      (le_ciSup (hbdd c ω) ⟨z - c, hzc⟩) (by positivity))
  calc
    P.real {ω | ∃ z ∈ V,
        t ≤ ((2 : ℝ) ^ k)⁻¹ * ‖fderiv ℝ (fun x => Y x ω) z‖} ≤
        P.real (⋃ c ∈ F, bad c) := measureReal_mono hsub (measure_ne_top P _)
    _ ≤ ∑ c ∈ F, P.real (bad c) := measureReal_biUnion_finset_le F bad
    _ ≤ ∑ _c ∈ F, C₀ * 4 ^ k * Real.exp (-t ^ 2 / (2 * σ2)) :=
      Finset.sum_le_sum fun c _ => htail hW k Y hY hYc c t ht
    _ ≤ C * 4 ^ k * Real.exp (-t ^ 2 / (2 * σ2)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      dsimp [C]
      have hfac : 0 ≤ C₀ * 4 ^ k * Real.exp (-t ^ 2 / (2 * σ2)) := by positivity
      nlinarith

end SupercriticalLQGUniqueness.B2.DG20Pt
