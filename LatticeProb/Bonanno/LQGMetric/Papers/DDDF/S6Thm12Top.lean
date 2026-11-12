/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6Thm12Top at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Thm12Half

/-!
# Tightness of the square metrics from a uniform sup bound (task P2-DDDF6e, O9, `δ ∈ [1/2,1)`)

For the range `δ ∈ [1/2,1)` of DDDF Theorem 1 (2), outside Prop 29's `t ∈ (0,1/2)`
(D-DDDF-13, "handled directly"): if `λ ≥ c > 0` and `sup_{B(0,6)} |Y_δ|` is tight uniformly in
`δ`, the metrics `λ^{-1} e^{ξ Y_δ} ds` on `[0,1]²` are uniformly Lipschitz off a small event
(`d(z,w) ≤ λ^{-1} e^{|ξ| M} |z − w|`, segment bound `LFPP.segCost_le`), hence tight by the
modulus criterion. Own elementary argument (DEVIATIONS D-DDDF-13).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace LQGMetric
namespace DDDF
namespace S6Thm

open WhiteNoise Blueprint DFGPS

local notation "SQ" => C(closedUnitSquare × closedUnitSquare, ℝ)

/-- the Lipschitz bound `λ^{-1} d_f(z,w) ≤ λ^{-1} e^{|ξ|M} |z − w|` if `|f| ≤ M` on `B(0,6)` -/
lemma sqMetricC_le_lip {ξ a M : ℝ} (ha : 0 < a) {f : ℂ → ℝ} (hf : Continuous f)
    (hM : ∀ x ∈ closedBall (0 : ℂ) 6, |f x| ≤ M) (z w : closedUnitSquare) :
    sqMetricC ξ a f (z, w) ≤ a⁻¹ * (Real.exp (|ξ| * M) * ‖(w : ℂ) - z‖) := by
  rw [sqMetricC_apply' hf]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.2 ha.le)
  simp only [lenMetricOn, crossLenIn_singleton]
  have hz := closedUnitSquare_subset_closedBall z.2
  have hw := closedUnitSquare_subset_closedBall w.2
  rw [mem_closedBall, dist_zero_right] at hz hw
  have hseg := (LFPP.lfppDOn_le_segCost (ξ := ξ) (φ := f) DFGPS.convex_closedUnitSquare z.2 w.2).trans
    (LFPP.segCost_le (B := Real.exp (|ξ| * M)) fun x hx => by
      rw [mem_closedBall, dist_eq_norm] at hx
      have hx4 : x ∈ closedBall (0 : ℂ) 6 := by
        rw [mem_closedBall, dist_zero_right]
        calc ‖x‖ = ‖(x - z) + z‖ := by rw [sub_add_cancel]
          _ ≤ ‖x - z‖ + ‖(z : ℂ)‖ := norm_add_le _ _
          _ ≤ ‖(w : ℂ) - z‖ + 2 := add_le_add hx hz
          _ ≤ (‖(w : ℂ)‖ + ‖(z : ℂ)‖) + 2 := by linarith [norm_sub_le (w : ℂ) z]
          _ ≤ 6 := by linarith
      exact Real.exp_le_exp.2 ((le_abs_self _).trans (by
        rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hM x hx4) (abs_nonneg _))))
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hseg

/-- **Tightness from a uniform sup bound** (D-DDDF-13): uniformly Lipschitz metrics off small
events. -/
theorem tight_of_sup_bound {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {I : Set ℝ}
    (Y : ℝ → ℂ → Ω → ℝ) (lam : ℝ → ℝ) (ξ : ℝ)
    (hYc : ∀ δ ∈ I, ∀ ω, Continuous fun x => Y δ x ω) (hYm : ∀ δ ∈ I, ∀ x, Measurable (Y δ x))
    {c : ℝ} (hc : 0 < c) (hlam : ∀ δ ∈ I, c ≤ lam δ)
    (hsup : ∀ ζ : ℝ, 0 < ζ → ∃ M : ℝ, ∀ δ ∈ I,
      P {ω | ∃ x ∈ closedBall (0 : ℂ) 6, M < |Y δ x ω|} ≤ ENNReal.ofReal ζ) :
    IsTightMeasureSet {μ | ∃ δ ∈ I, μ = P.map fun ω => sqMetricC ξ (lam δ) (fun x => Y δ x ω)} := by
  have : ConnectedSpace closedUnitSquare := isConnected_iff_connectedSpace.1
    (DFGPS.convex_closedUnitSquare.isConnected ⟨0, by simp [closedUnitSquare]⟩)
  refine LFPP.isTightMeasureSet_of_modulus _ ?_ ?_
  · rintro μ ⟨δ, hδ, rfl⟩
    have hms : MeasurableSet (pmetSet closedUnitSquare)ᶜ :=
      (isClosed_pmetSet _).isOpen_compl.measurableSet
    have e : {d : SQ | ¬ ((∀ x, d (x, x) = 0) ∧ ∀ x y z, d (x, z) ≤ d (x, y) + d (y, z))} =
        (pmetSet closedUnitSquare)ᶜ := rfl
    rw [e, Measure.map_apply (measurable_sqMetric_path (hYc δ hδ) (hYm δ hδ) _ _) hms]
    convert measure_empty (μ := P)
    ext ω
    simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_not]
    exact pmet_sq (hc.le.trans (hlam δ hδ)) (hYc δ hδ ω)
  · intro ζ hζ
    obtain ⟨M, hM⟩ := hsup ζ hζ
    set η : ℝ := ζ * c * Real.exp (-(|ξ| * M))
    have hη : 0 < η := by positivity
    refine ⟨η, hη, ?_⟩
    rintro μ ⟨δ, hδ, rfl⟩
    change (P.map fun ω => sqMetricC ξ (lam δ) (fun x => Y δ x ω)) (modBad η ζ) ≤ _
    rw [Measure.map_apply (measurable_sqMetric_path (hYc δ hδ) (hYm δ hδ) _ _)
      (measurableSet_modBad η ζ)]
    refine (measure_mono fun ω hω => ?_).trans (hM δ hδ)
    by_contra hn
    simp only [mem_ofPred_eq, not_exists, not_and, not_lt] at hn
    refine hω fun z w hzw => ?_
    have hl0 : 0 < lam δ := hc.trans_le (hlam δ hδ)
    have h1 := sqMetricC_le_lip (ξ := ξ) hl0 (hYc δ hδ ω) hn z w
    have hd : ‖(w : ℂ) - z‖ ≤ η := by rwa [Subtype.dist_eq, dist_eq_norm, norm_sub_rev] at hzw
    refine h1.trans ?_
    calc (lam δ)⁻¹ * (Real.exp (|ξ| * M) * ‖(w : ℂ) - z‖)
        ≤ c⁻¹ * (Real.exp (|ξ| * M) * η) :=
          mul_le_mul (inv_anti₀ hc (hlam δ hδ)) (mul_le_mul_of_nonneg_left hd (Real.exp_pos _).le)
            (by positivity) (by positivity)
      _ = ζ := by
          simp only [η]
          rw [Real.exp_neg]
          field_simp

end S6Thm
end DDDF
end LQGMetric
