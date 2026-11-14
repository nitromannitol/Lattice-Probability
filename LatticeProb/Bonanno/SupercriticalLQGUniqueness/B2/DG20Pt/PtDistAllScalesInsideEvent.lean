/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistAllScalesInsideEvent at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistAllScalesEvent
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistScaleInside

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 


theorem exists_pt_dist_all_scales_inside_event_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (ζ : ℝ) (hζ : 0 < ζ)
    (V : Set ℂ) (hV : Bornology.IsBounded V) (hconv : Convex ℝ V)
    (R : ℝ) (hR : 0 < R) :
    ∃ Cnet : ℕ, 0 < Cnet ∧
    ∃ C a₀ a₁ b₀ b₁ D σ2 : ℝ,
      0 < C ∧ 0 < a₀ ∧ 0 < a₁ ∧ 0 < b₀ ∧ 0 < b₁ ∧
      0 < D ∧ 0 < σ2 ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n : ℕ, ∀ T : ℝ, 3 < T →
          ∀ t : ℕ → ℝ, (∀ k ≤ n, 0 ≤ t k) →
          ∃ F : ℕ → Finset ℂ,
            (∀ k ≤ n, (F k).card ≤ Cnet * 4 ^ k ∧
              (∀ x ∈ F k, x ∈ V) ∧
              ∀ z ∈ V, ∃ x ∈ F k,
                dist z x < ((2 : ℝ)⁻¹) ^ (k + 2)) ∧
            P (ptDistAllScalesGood P W ξ Q ζ C n F V R T t)ᶜ ≤
              ∑ k ∈ Finset.range (n + 1),
                ptDistScaleRate Cnet a₀ a₁ b₀ b₁ D σ2 ζ T k (t k) := by
  obtain ⟨Cnet, hCnet, C, a₀, a₁, b₀, b₁, D, σ2,
    hC, ha₀, ha₁, hb₀, hb₁, hD, hσ2, hscale⟩ :=
      exists_pt_dist_scale_inside_of_inputs hPerc hExp ξ Q hQ ζ hζ V hV hconv R hR
  refine ⟨Cnet, hCnet, C, a₀, a₁, b₀, b₁, D, σ2,
    hC, ha₀, ha₁, hb₀, hb₁, hD, hσ2, ?_⟩
  intro Ω _ P _ W hW n T hT t ht
  have hchoices (k : ℕ) : ∃ F : Finset ℂ, k ≤ n →
      F.card ≤ Cnet * 4 ^ k ∧
      (∀ x ∈ F, x ∈ V) ∧
      (∀ z ∈ V, ∃ x ∈ F, dist z x < ((2 : ℝ)⁻¹) ^ (k + 2)) ∧
      P (ptDistScaleGood P W ξ Q ζ C n k F V R (t k) T)ᶜ ≤
        ptDistScaleRate Cnet a₀ a₁ b₀ b₁ D σ2 ζ T k (t k) := by
    by_cases hk : k ≤ n
    · obtain ⟨F, hcard, hinside, hcover, htail⟩ :=
        hscale P W hW n k hk T (t k) hT (ht k hk)
      refine ⟨F, fun _ => ⟨hcard, hinside, hcover, ?_⟩⟩
      simpa only [ptDistScaleRate] using htail
    · exact ⟨∅, fun h => False.elim (hk h)⟩
  let F (k : ℕ) : Finset ℂ := Classical.choose (hchoices k)
  have hF (k : ℕ) : k ≤ n →
      (F k).card ≤ Cnet * 4 ^ k ∧
              (∀ x ∈ F k, x ∈ V) ∧
      (∀ z ∈ V, ∃ x ∈ F k, dist z x < ((2 : ℝ)⁻¹) ^ (k + 2)) ∧
      P (ptDistScaleGood P W ξ Q ζ C n k (F k) V R (t k) T)ᶜ ≤
        ptDistScaleRate Cnet a₀ a₁ b₀ b₁ D σ2 ζ T k (t k) :=
    Classical.choose_spec (hchoices k)
  refine ⟨F, (fun k hk => ⟨(hF k hk).1, (hF k hk).2.1, (hF k hk).2.2.1⟩), ?_⟩
  calc
    P (ptDistAllScalesGood P W ξ Q ζ C n F V R T t)ᶜ ≤
        ∑ k ∈ Finset.range (n + 1),
          P (ptDistScaleGood P W ξ Q ζ C n k (F k) V R (t k) T)ᶜ :=
      pt_dist_all_scales_bad_le P W ξ Q ζ C n F V R T t
    _ ≤ _ := Finset.sum_le_sum fun k hk =>
      (hF k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))).2.2.2

end SupercriticalLQGUniqueness.B2.DG20Pt
