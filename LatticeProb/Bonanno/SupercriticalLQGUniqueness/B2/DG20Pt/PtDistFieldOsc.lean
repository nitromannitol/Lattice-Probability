/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistFieldOsc at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistGradientEvent
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenObs

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Topology Metric
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 


theorem pt_dist_field_osc_tail (V : Set ℂ)
    (hV : Bornology.IsBounded V) (hconv : Convex ℝ V) (R : ℝ) (hR : 0 < R) :
    ∃ C σ2 : ℝ, 0 < C ∧ 0 < σ2 ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
        {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
        ∀ (k : ℕ) (t : ℝ), 0 ≤ t →
          P.real {ω | ∃ z ∈ V, ∃ w ∈ V,
            dist z w ≤ R * ((2 : ℝ) ^ k)⁻¹ ∧
            R * t < |phiMN W P 0 k z ω - phiMN W P 0 k w ω|} ≤
              C * 4 ^ k * Real.exp (-t ^ 2 / (2 * σ2)) := by
  obtain ⟨C, σ2, hC, hσ2, htail⟩ := pt_dist_grad_bounded_tail V hV
  refine ⟨C, σ2, hC, hσ2, ?_⟩
  intro Ω _ P W hW k t ht
  letI : IsProbabilityMeasure P := hW.isProbabilityMeasure
  have hpn : ((2 : ℝ) ^ k)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  obtain ⟨Y, -, hYae, _, hYc, -⟩ :=
    exists_C1_modification_phi hW (a := ((2 : ℝ) ^ k)⁻¹) (b := 1)
      (by positivity) hpn
  have hφ := isPhiVersion_phiMN hW (Nat.zero_le k)
  have hind : ∀ᵐ ω ∂P, ∀ x, phiMN W P 0 k x ω = Y x ω :=
    ae_eq_of_continuous_modification hφ.cont
      (fun ω => (hYc ω).continuous) (fun x => by
        have hx := hφ.ae_eq x
        rw [inv_pow, pow_zero] at hx
        exact hx.trans (hYae x).symm)
  have hnull : P {ω | ¬ ∀ x, phiMN W P 0 k x ω = Y x ω} = 0 :=
    ae_iff.mp hind
  let G : Set Ω := {ω | ∃ z ∈ V,
    t ≤ ((2 : ℝ) ^ k)⁻¹ * ‖fderiv ℝ (fun x => Y x ω) z‖}
  let N : Set Ω := {ω | ¬ ∀ x, phiMN W P 0 k x ω = Y x ω}
  have hsub : {ω | ∃ z ∈ V, ∃ w ∈ V,
      dist z w ≤ R * ((2 : ℝ) ^ k)⁻¹ ∧
      R * t < |phiMN W P 0 k z ω - phiMN W P 0 k w ω|} ⊆ G ∪ N := by
    intro ω hω
    obtain ⟨z, hz, w, hw, hzw, hbad⟩ := hω
    by_cases heq : ∀ x, phiMN W P 0 k x ω = Y x ω
    · by_contra hnot
      have hng : ω ∉ G := by
        intro hmem
        exact hnot (Or.inl hmem)
      have hgrad (u : ℂ) (hu : u ∈ V) :
          ‖fderiv ℝ (fun x => Y x ω) u‖ ≤ (2 : ℝ) ^ k * t := by
        have hu' : ((2 : ℝ) ^ k)⁻¹ * ‖fderiv ℝ (fun x => Y x ω) u‖ < t := by
          exact lt_of_not_ge (fun hh => hng ⟨u, hu, hh⟩)
        have he : ‖fderiv ℝ (fun x => Y x ω) u‖ =
            (2 : ℝ) ^ k * (((2 : ℝ) ^ k)⁻¹ *
              ‖fderiv ℝ (fun x => Y x ω) u‖) := by
          field_simp
        rw [he]
        exact (mul_le_mul_of_nonneg_left hu'.le (by positivity))
      have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le
        (fun u _ => ((hYc ω).differentiable (by norm_num)) u)
        hgrad hconv hw hz
      have hclose : |phiMN W P 0 k z ω - phiMN W P 0 k w ω| ≤ R * t := by
        rw [heq z, heq w]
        have hpow : 0 ≤ (2 : ℝ) ^ k * t := by positivity
        calc
          |Y z ω - Y w ω| ≤ ((2 : ℝ) ^ k * t) * dist z w := by
            simpa only [Real.norm_eq_abs, dist_eq_norm, norm_sub_rev] using hmv
          _ ≤ ((2 : ℝ) ^ k * t) * (R * ((2 : ℝ) ^ k)⁻¹) :=
            mul_le_mul_of_nonneg_left hzw hpow
          _ = R * t := by field_simp
      exact (not_lt_of_ge hclose) hbad
    · exact Or.inr heq
  have hNreal : P.real N = 0 := by simpa [N, Measure.real] using congrArg ENNReal.toReal hnull
  calc
    P.real {ω | ∃ z ∈ V, ∃ w ∈ V,
        dist z w ≤ R * ((2 : ℝ) ^ k)⁻¹ ∧
        R * t < |phiMN W P 0 k z ω - phiMN W P 0 k w ω|} ≤
      P.real (G ∪ N) := measureReal_mono hsub (measure_ne_top P _)
    _ ≤ P.real G + P.real N := measureReal_union_le _ _
    _ = P.real G := by rw [hNreal, add_zero]
    _ ≤ C * 4 ^ k * Real.exp (-t ^ 2 / (2 * σ2)) := htail hW k Y hYae hYc t ht

end SupercriticalLQGUniqueness.B2.DG20Pt
