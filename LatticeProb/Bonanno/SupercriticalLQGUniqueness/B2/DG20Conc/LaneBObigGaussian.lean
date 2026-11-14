/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBObigGaussian at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBOscTail

 






set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.SupTail LQGMetric.WhiteNoise

 


theorem laneB_Obig_gaussian_tail : ∃ C σ2 : ℝ, 0 < C ∧ 0 < σ2 ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ},
      IsWhiteNoise P W →
    ∀ (K : ℕ) (Y : ℂ → Ω → ℝ),
      (∀ x, (fun ω => Y x ω) =ᵐ[P] phi W ((2 : ℝ) ^ K)⁻¹ 1 x) →
      (∀ ω, ContDiff ℝ 1 fun x => Y x ω) →
      ∀ x : ℝ, 0 ≤ x →
    P.real {ω | x ≤ T20C.Obig K Y ω} ≤
      C * 4 ^ K * Real.exp (-x ^ 2 / (2 * σ2)) := by
  obtain ⟨C, σ2, hC, hσ2, htail⟩ := laneB_prop3_tail_shift
  refine ⟨25 * C, σ2, by positivity, hσ2, ?_⟩
  intro Ω _ P W hW K Y hY hYc x hx
  have : IsProbabilityMeasure P := hW.isProbabilityMeasure
  let A : ℂ → Set Ω := fun c => {ω | x ≤ ((2 : ℝ) ^ K)⁻¹ *
    ⨆ z : ferniqueBox 0 1, ‖fderiv ℝ (fun y => Y (y + c) ω) z‖}
  have hsub : {ω | x ≤ T20C.Obig K Y ω} ⊆ ⋃ c ∈ T20C.offs, A c := by
    intro ω hω
    change x ≤ T20C.offs.sup' T20C.offs_nonempty (fun c =>
      ((2 : ℝ) ^ K)⁻¹ *
        ⨆ z : ferniqueBox 0 1, ‖fderiv ℝ (fun y => Y (y + c) ω) z‖) at hω
    obtain ⟨c, hc, h⟩ := (Finset.le_sup'_iff T20C.offs_nonempty).1 hω
    exact mem_biUnion hc h
  have hfin : P (⋃ c ∈ T20C.offs, A c) ≠ ⊤ :=
    measure_ne_top_of_subset (subset_univ _) (by simp)
  have hsum : P.real {ω | x ≤ T20C.Obig K Y ω} ≤
      ∑ c ∈ T20C.offs, P.real (A c) :=
    (measureReal_mono hsub hfin).trans (measureReal_biUnion_finset_le _ _)
  have hboxes : ∑ c ∈ T20C.offs, P.real (A c) ≤
      ∑ _c ∈ T20C.offs, C * 4 ^ K * Real.exp (-x ^ 2 / (2 * σ2)) := by
    apply Finset.sum_le_sum
    intro c _
    exact htail hW K Y hY hYc c x hx
  have hcard : ((T20C.offs.card : ℕ) : ℝ) ≤ 25 := by
    exact_mod_cast T20C.card_offs_le
  calc
    P.real {ω | x ≤ T20C.Obig K Y ω}
      ≤ ∑ c ∈ T20C.offs, P.real (A c) := hsum
    _ ≤ ∑ _c ∈ T20C.offs, C * 4 ^ K * Real.exp (-x ^ 2 / (2 * σ2)) := hboxes
    _ = (T20C.offs.card : ℝ) * (C * 4 ^ K * Real.exp (-x ^ 2 / (2 * σ2))) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 25 * (C * 4 ^ K * Real.exp (-x ^ 2 / (2 * σ2))) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (25 * C) * 4 ^ K * Real.exp (-x ^ 2 / (2 * σ2)) := by ring

end SupercriticalLQGUniqueness.B2.DG20Conc
