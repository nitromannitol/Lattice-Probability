/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6Thm12Sq at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Thm12Top

/-!
# DDDF Theorem 1 (2) for `D = (−1,2)²`: tightness over `δ ∈ (0,1)` (task P2-DDDF6e, O9)

DDDF = arXiv:1904.08021, `tightness.tex` l. 160–161, 1497–1498. `δ ∈ (0,1/2)`:
`s6_thm12_tight_half` (Prop 29 coupling + Theorem 1 (1)); `δ ∈ [1/2,1)` (D-DDDF-13):
`tight_of_sup_bound`, with `λ_{√δ} ≥ e^{-C} min(λ_0, λ_1)` from (6.98) and the uniform sup bound
of `p_{δ/2} * h̊` on `B(0,6)` (hypothesis `hsup`, open).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace LQGMetric
namespace DDDF
namespace S6Thm

open WhiteNoise Blueprint DFGPS HeatSq

/-- `λ_a ≥ e^{-C} min(λ_0, λ_1) > 0` for `a ∈ (1/4, 1)`, from (6.98) -/
lemma lambdaDelta_lower_of_698 {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} {ξ : ℝ} (hW : IsWhiteNoise P W) (h698 : S6Eq6_98 ξ W P) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : ℝ, 1 / 4 < a → a < 1 → c ≤ lambdaDelta ξ W P a := by
  obtain ⟨C, hC⟩ := h698
  refine ⟨Real.exp (-C) * min (lambdaN ξ W P 0) (lambdaN ξ W P 1),
    mul_pos (Real.exp_pos _) (lt_min (lambdaN_pos hW 0) (lambdaN_pos hW 1)), fun a ha4 ha1 => ?_⟩
  obtain ⟨n, r, hr0, hr1, hdef⟩ := S6.exists_split (lt_trans (by norm_num) ha4) ha1
  have hn : n ≤ 1 := by
    by_contra hn
    push_neg at hn
    have h2 : (2 : ℕ) ≤ n := hn
    have : (2 : ℝ) ^ (-((n : ℝ) + r)) ≤ (2 : ℝ) ^ (-(2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
        have : (2 : ℝ) ≤ n := by exact_mod_cast h2
        linarith)
    rw [show (2 : ℝ) ^ (-(2 : ℝ)) = 1 / 4 by norm_num [Real.rpow_neg, Real.rpow_two]] at this
    linarith
  rw [hdef]
  refine le_trans ?_ (hC n r hr0 hr1).1
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  interval_cases n
  · exact min_le_left _ _
  · exact min_le_right _ _

/-- **DDDF Theorem 1 (2)**, tightness part, for `D = (−1,2)²` and all `δ ∈ (0,1)`, from
Theorem 1 (1), Prop 29 on the square, (5.54) (for `λ` bounded below) and the uniform sup bound
of `p_{δ/2} * h̊` for `δ ∈ [1/2,1)`. -/
theorem s6_thm12_tight_sq (h11 : DDDFThm1_1) (h29 : DDDFProp29Sq) {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') (W' : WNSpace → Ω' → ℝ)
    (hW' : IsWhiteNoise P' W') (h554 : S6Eq5_54 (xiGamma γ) (LQGMetric.Q γ) W' P')
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Xh : BddOn (sqOpen (-1) 3) → Ω → ℝ)
    (hX : IsZBGFFProcessExt (sqOpens (-1) 3) Xh P) (Y : ℝ → ℂ → Ω → ℝ)
    (hY : ∀ δ ∈ Ioo (0 : ℝ) 1,
      IsContVersion (fun x => Xh (heatBdd (sqOpens (-1) 3) (δ / 2) x)) (Y δ) P)
    (hsup : ∀ ζ : ℝ, 0 < ζ → ∃ M : ℝ, ∀ δ ∈ Ico (1 / 2 : ℝ) 1,
      P {ω | ∃ x ∈ closedBall (0 : ℂ) 6, M < |Y δ x ω|} ≤ ENNReal.ofReal ζ) :
    IsTightMeasureSet {μ | ∃ δ ∈ Ioo (0 : ℝ) 1, μ = P.map fun ω =>
      sqMetricC (xiGamma γ) (lambdaDelta (xiGamma γ) W' P' (Real.sqrt δ)) (fun x => Y δ x ω)} := by
  have h1 := s6_thm12_tight_half h11 h29 hγ hγ2 P' W' hW' P Xh hX Y hY
  obtain ⟨c, hc, hlam⟩ := lambdaDelta_lower_of_698 hW' (s6_eq6_98_of_554 hγ hγ2 hW' h554)
  have hI : ∀ δ ∈ Ico (1 / 2 : ℝ) 1, δ ∈ Ioo (0 : ℝ) 1 := fun δ hδ =>
    ⟨lt_of_lt_of_le (by norm_num) hδ.1, hδ.2⟩
  have h2 := tight_of_sup_bound P (I := Ico (1 / 2 : ℝ) 1) Y
    (fun δ => lambdaDelta (xiGamma γ) W' P' (Real.sqrt δ)) (xiGamma γ)
    (fun δ hδ => (hY δ (hI δ hδ)).1) (fun δ hδ => (hY δ (hI δ hδ)).2.1) hc
    (fun δ hδ => hlam _ (by
      have h0 : (0 : ℝ) < δ := lt_of_lt_of_le (by norm_num) hδ.1
      have : δ ≤ Real.sqrt δ := (Real.le_sqrt' h0).2 (by nlinarith [hδ.2])
      linarith [hδ.1])
      ((Real.sqrt_lt' one_pos).2 (by rw [one_pow]; exact hδ.2))) hsup
  refine (h1.union h2).subset ?_
  rintro μ ⟨δ, hδ, rfl⟩
  rcases lt_or_ge δ (1 / 2) with h | h
  · exact Or.inl ⟨δ, ⟨hδ.1, h⟩, rfl⟩
  · exact Or.inr ⟨δ, ⟨h, hδ.2⟩, rfl⟩

end S6Thm
end DDDF
end LQGMetric
