/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistScaleInside at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistScaleEvent
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistNetInside

 

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open LQGMetric.DDDF LQGMetric.WhiteNoise

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem exists_pt_dist_scale_inside_of_inputs
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
        IsWhiteNoise P W → ∀ n k : ℕ, k ≤ n →
          ∀ T t : ℝ, 3 < T → 0 ≤ t →
          let S : ℝ := T * (2 : ℝ) ^ ((ζ / 2) * (k : ℝ))
          ∃ F : Finset ℂ,
            F.card ≤ Cnet * 4 ^ k ∧
            (∀ x ∈ F, x ∈ V) ∧
            (∀ z ∈ V, ∃ x ∈ F, dist z x < ((2 : ℝ)⁻¹) ^ (k + 2)) ∧
            P (ptDistScaleGood P W ξ Q ζ C n k F V R t T)ᶜ ≤
              ((Cnet * 4 ^ k : ℕ) : ℝ≥0∞) *
                (ENNReal.ofReal (a₀ * Real.exp
                  (-a₁ * (Real.log S) ^ 2 / Real.log (Real.log S))) +
                 ENNReal.ofReal (b₀ * Real.exp
                  (-b₁ * (Real.log S) ^ 2 / Real.log (Real.log S)))) +
              ENNReal.ofReal (D * 4 ^ k * Real.exp (-t ^ 2 / (2 * σ2))) := by
  obtain ⟨Cnet, hCnet, hnet⟩ := exists_pt_dist_net_inside V hV
  obtain ⟨C, a₀, a₁, b₀, b₁, hC, ha₀, ha₁, hb₀, hb₁, htail⟩ :=
    pt_dist_site_bad_boost_of_inputs hPerc hExp ξ Q hQ ζ hζ
  obtain ⟨D, σ2, hD, hσ2, hosc⟩ :=
    pt_dist_field_osc_tail V hV hconv R hR
  refine ⟨Cnet, hCnet, C, a₀, a₁, b₀, b₁, D, σ2,
    hC, ha₀, ha₁, hb₀, hb₁, hD, hσ2, ?_⟩
  intro Ω _ P _ W hW n k hkn T t hT ht
  obtain ⟨F, hcard, hinside, hcover⟩ := hnet k
  refine ⟨F, hcard, hinside, hcover, ?_⟩
  have hsite := pt_dist_all_sites_bad_le P W ξ Q ζ C n k F T
    (ENNReal.ofReal (a₀ * Real.exp
      (-a₁ * (Real.log (T * (2 : ℝ) ^ ((ζ / 2) * (k : ℝ)))) ^ 2 /
        Real.log (Real.log (T * (2 : ℝ) ^ ((ζ / 2) * (k : ℝ)))))) +
     ENNReal.ofReal (b₀ * Real.exp
      (-b₁ * (Real.log (T * (2 : ℝ) ^ ((ζ / 2) * (k : ℝ)))) ^ 2 /
        Real.log (Real.log (T * (2 : ℝ) ^ ((ζ / 2) * (k : ℝ)))))))
    (fun x _ => htail P W hW n k hkn x T hT)
  have hsite' : P (ptDistAllSitesGood P W ξ Q ζ C n k F T)ᶜ ≤
      ((Cnet * 4 ^ k : ℕ) : ℝ≥0∞) *
        (ENNReal.ofReal (a₀ * Real.exp
          (-a₁ * (Real.log (T * (2 : ℝ) ^ ((ζ / 2) * (k : ℝ)))) ^ 2 /
            Real.log (Real.log (T * (2 : ℝ) ^ ((ζ / 2) * (k : ℝ)))))) +
         ENNReal.ofReal (b₀ * Real.exp
          (-b₁ * (Real.log (T * (2 : ℝ) ^ ((ζ / 2) * (k : ℝ)))) ^ 2 /
            Real.log (Real.log (T * (2 : ℝ) ^ ((ζ / 2) * (k : ℝ))))))) :=
    hsite.trans (by gcongr)
  have hbad_eq : (ptDistOscGood P W V k R t)ᶜ =
      {ω | ∃ z ∈ V, ∃ w ∈ V,
        dist z w ≤ R * ((2 : ℝ) ^ k)⁻¹ ∧
        R * t < |phiMN W P 0 k z ω - phiMN W P 0 k w ω|} := by
    ext ω
    simp only [ptDistOscGood, mem_compl_iff, mem_ofPred_eq]
    push Not
    rfl
  have hbadOsc : P (ptDistOscGood P W V k R t)ᶜ ≤
      ENNReal.ofReal (D * 4 ^ k * Real.exp (-t ^ 2 / (2 * σ2))) := by
    rw [hbad_eq, ← ofReal_measureReal (measure_ne_top P _)]
    exact ENNReal.ofReal_le_ofReal (hosc hW k t ht)
  calc
    P (ptDistScaleGood P W ξ Q ζ C n k F V R t T)ᶜ ≤
        P (ptDistAllSitesGood P W ξ Q ζ C n k F T)ᶜ +
          P (ptDistOscGood P W V k R t)ᶜ := by
        simpa only [ptDistScaleGood, compl_inter] using
          (measure_union_le
            (ptDistAllSitesGood P W ξ Q ζ C n k F T)ᶜ
            (ptDistOscGood P W V k R t)ᶜ)
    _ ≤ _ := add_le_add hsite' hbadOsc

end SupercriticalLQGUniqueness.B2.DG20Pt
