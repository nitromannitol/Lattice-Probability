/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistLocalGaussianTail at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistLocalGaussianBudget

 



set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_local_gaussian_budget_tail_of_inputs
    (hPerc : SupercriticalLQGUniqueness.B2.Iface.DG20PercEstimate')
    (hExp : SupercriticalLQGUniqueness.B2.Iface.DG20ExponentRelation)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (ζ : ℝ) (hζ : 0 < ζ)
    (V : Set ℂ) (hV : Bornology.IsBounded V) (hconv : Convex ℝ V)
    (R : ℝ) (hR : 1 ≤ R) :
    ∃ C Clam c₀ c₁ : ℝ, 0 < C ∧ 0 < Clam ∧ 0 < c₀ ∧ 0 < c₁ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (W : WNSpace → Ω → ℝ),
        IsWhiteNoise P W → ∀ n k₀ : ℕ, 1 ≤ k₀ → k₀ ≤ n →
        ∀ U : Set ℂ, ∀ z w : ℂ, z ∈ V → w ∈ V →
        dist z w ≤ 2 * ((2 : ℝ)⁻¹ ^ k₀) →
        (∀ k, k₀ ≤ k → ∀ x : ℂ,
          dist z x < ((2 : ℝ)⁻¹) ^ k / 4 →
          ball x (17 * ((2 : ℝ)⁻¹ ^ k)) ⊆ U) →
        (∀ k, k₀ ≤ k → ∀ x : ℂ,
          dist w x < ((2 : ℝ)⁻¹) ^ k / 4 →
          ball x (17 * ((2 : ℝ)⁻¹ ^ k)) ⊆ U) →
        closedBall z ((2 : ℝ)⁻¹ ^ n) ⊆ V →
        closedBall w ((2 : ℝ)⁻¹ ^ n) ⊆ V →
        closedBall z ((2 : ℝ)⁻¹ ^ n) ⊆ U →
        closedBall w ((2 : ℝ)⁻¹ ^ n) ⊆ U →
        ∀ T L β : ℝ, 3 < T → 0 ≤ L → 0 < β →
          P {ω | ¬ lfppDOn (ξ : ℝ)
            (fun y => phiMN W P 0 n y ω) U z w ≤
              ptDistLocalGaussianBudget (ξ : ℝ) Q ζ L β T C Clam
                (lambdaN ξ W P n) n k₀} ≤
          ENNReal.ofReal (c₀ * Real.exp
            (-c₁ * (Real.log T) ^ 2 / Real.log (Real.log T))) +
          2 * ENNReal.ofReal
            (2 * Real.exp (-(β / (2 * (ξ : ℝ) ^ 2 * Real.log 2)) * L) *
              (Real.exp (-(β / (2 * (ξ : ℝ) ^ 2 * Real.log 2)) * β) /
                (1 - Real.exp (-(β / (2 * (ξ : ℝ) ^ 2 * Real.log 2)) * β)))) := by
  obtain ⟨C, Clam, c₀, c₁, hC, hClam, hc₀, hc₁, htail⟩ :=
    pt_dist_local_point_budget_tail_of_inputs
      hPerc hExp ξ Q hQ ζ hζ V hV hconv R hR
  refine ⟨C, Clam, c₀, c₁, hC, hClam, hc₀, hc₁, ?_⟩
  intro Ω _ P _ W hW n k₀ hk₀ hkn U z w hz hw hzw hcollarZ hcollarW
    hVballZ hVballW hUballZ hUballW T L β hT hL hβ
  let E₀ : Set Ω := {ω | ¬ lfppDOn (ξ : ℝ)
      (fun y => phiMN W P 0 n y ω) U z w ≤
        ptDistLocalPointBudget P W ξ Q ζ C Clam T n k₀ z w ω}
  let Ez : Set Ω := (ptDistPointFieldGood P W (ξ : ℝ) L β n z)ᶜ
  let Ew : Set Ω := (ptDistPointFieldGood P W (ξ : ℝ) L β n w)ᶜ
  have hsub :
      {ω | ¬ lfppDOn (ξ : ℝ) (fun y => phiMN W P 0 n y ω) U z w ≤
        ptDistLocalGaussianBudget (ξ : ℝ) Q ζ L β T C Clam
          (lambdaN ξ W P n) n k₀} ⊆ E₀ ∪ Ez ∪ Ew := by
    intro ω hω
    by_cases h0 : ω ∈ E₀
    · exact Or.inl (Or.inl h0)
    by_cases hzG : ω ∈ ptDistPointFieldGood P W (ξ : ℝ) L β n z
    · by_cases hwG : ω ∈ ptDistPointFieldGood P W (ξ : ℝ) L β n w
      · exfalso
        apply hω
        have hlocal : lfppDOn (ξ : ℝ)
            (fun y => phiMN W P 0 n y ω) U z w ≤
            ptDistLocalPointBudget P W ξ Q ζ C Clam T n k₀ z w ω :=
          not_not.mp h0
        exact hlocal.trans
          (pt_dist_local_point_budget_le_gaussian_budget P W ξ Q ζ L β
            T C Clam n k₀ hk₀ hkn hβ.le (by linarith) hC.le hClam.le
            (lambdaN_pos hW n).le z w ω hzG hwG)
      · exact Or.inr (by simpa only [Ew, mem_compl_iff] using hwG)
    · exact Or.inl (Or.inr (by simpa only [Ez, mem_compl_iff] using hzG))
  have hpoint : P E₀ ≤ ENNReal.ofReal (c₀ * Real.exp
      (-c₁ * (Real.log T) ^ 2 / Real.log (Real.log T))) :=
    htail P W hW n k₀ hkn U z w hz hw hzw hcollarZ hcollarW
      hVballZ hVballW hUballZ hUballW T hT
  have hzTail := pt_dist_point_field_uniform_tail P W hW (ξ : ℝ) L β
    ξ.2 hL hβ n z
  have hwTail := pt_dist_point_field_uniform_tail P W hW (ξ : ℝ) L β
    ξ.2 hL hβ n w
  calc
    _ ≤ P (E₀ ∪ Ez ∪ Ew) := measure_mono hsub
    _ ≤ P E₀ + P Ez + P Ew := by
      exact (measure_union_le _ _).trans
        (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ _ := by
      have hz' : P Ez ≤ ENNReal.ofReal
          (2 * Real.exp (-(β / (2 * (ξ : ℝ) ^ 2 * Real.log 2)) * L) *
            (Real.exp (-(β / (2 * (ξ : ℝ) ^ 2 * Real.log 2)) * β) /
              (1 - Real.exp (-(β / (2 * (ξ : ℝ) ^ 2 * Real.log 2)) * β)))) :=
        hzTail
      have hw' : P Ew ≤ ENNReal.ofReal
          (2 * Real.exp (-(β / (2 * (ξ : ℝ) ^ 2 * Real.log 2)) * L) *
            (Real.exp (-(β / (2 * (ξ : ℝ) ^ 2 * Real.log 2)) * β) /
              (1 - Real.exp (-(β / (2 * (ξ : ℝ) ^ 2 * Real.log 2)) * β)))) :=
        hwTail
      calc
        _ ≤ ENNReal.ofReal (c₀ * Real.exp
          (-c₁ * (Real.log T) ^ 2 / Real.log (Real.log T))) +
          ENNReal.ofReal
            (2 * Real.exp (-(β / (2 * (ξ : ℝ) ^ 2 * Real.log 2)) * L) *
              (Real.exp (-(β / (2 * (ξ : ℝ) ^ 2 * Real.log 2)) * β) /
                (1 - Real.exp (-(β / (2 * (ξ : ℝ) ^ 2 * Real.log 2)) * β)))) +
          ENNReal.ofReal
            (2 * Real.exp (-(β / (2 * (ξ : ℝ) ^ 2 * Real.log 2)) * L) *
              (Real.exp (-(β / (2 * (ξ : ℝ) ^ 2 * Real.log 2)) * β) /
                (1 - Real.exp (-(β / (2 * (ξ : ℝ) ^ 2 * Real.log 2)) * β)))) :=
            add_le_add (add_le_add hpoint hz') hw'
        _ = _ := by ring

end SupercriticalLQGUniqueness.B2.DG20Pt
