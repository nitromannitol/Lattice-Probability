/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianBoundaryExcursion at commit fdb5cad; local import paths and proof style are adjusted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianLandingRange
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianExcursionRange
import LatticeProb.Bonanno.BouRabeeGwynne.BrownianExcursionKernel
import LatticeProb.Bonanno.BouRabeeGwynne.ExteriorBallBuffer

/-! A uniform contraction of boundary-collar survival for the actual full
Brownian excursion out of a larger ball. -/

open MeasureTheory ProbabilityTheory Set Metric
open scoped NNReal ENNReal unitInterval

namespace BouRabeeGwynne

def curveRangeEvent {d : ℕ} (K : Set (Euc d)) : Set C(unitInterval, Euc d) :=
  {f | ∀ t, f t ∈ K}

lemma isClosed_curveRangeEvent {d : ℕ} {K : Set (Euc d)} (hK : IsClosed K) :
    IsClosed (curveRangeEvent K) := by
  simp only [curveRangeEvent, ofPred_forall]
  exact isClosed_iInter fun t => hK.preimage (continuous_eval_const t)

theorem standardBrownianLaw_uniform_boundary_excursion_survival {d : ℕ}
    (hd : 1 ≤ d) (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ]
    (hμ : IsStandardBrownianLaw μ) {κ : ℝ} (hκ : 0 < κ) :
    ∃ q R : ℝ, 0 ≤ q ∧ q < 1 ∧ 1 < R ∧
      ∀ (U : Set (Euc d)) (p c : Euc d) (r : ℝ≥0), 0 < r →
        ∀ (x : Euc d) (δ : ℝ), dist c p = (r : ℝ) →
          closedBall c (κ * (r : ℝ)) ⊆ Uᶜ → dist x p ≤ (r : ℝ) →
          δ < κ * (r : ℝ) / 2 →
          brownianExcursionKernel (U := ball p (R * (r : ℝ))) isOpen_ball μ x
            (curveRangeEvent (cthickening δ U)) ≤ ENNReal.ofReal q := by
  obtain ⟨a, L, ha, haone, hL, hlanding⟩ :=
    standardBrownianLaw_uniform_scaled_landing_and_range_probability hμ (half_pos hκ)
  refine ⟨1 - a / 2, L + 2, by linarith, by linarith, by linarith, ?_⟩
  intro U p c r hr x δ hcp hext hxp hδ
  have hrR : 0 < (r : ℝ) := hr
  let V : Set (Euc d) := ball p ((L + 2) * (r : ℝ))
  let K : Set (Euc d) := cthickening δ U
  let E : Set (BrownianPath d) := {ω |
    x + ω (r ^ 2) ∈ ball c ((κ / 2) * (r : ℝ)) ∧
      ω ∈ pathRangeEvent (r ^ 2) (L * (r : ℝ))}
  let A : Set (BrownianPath d) :=
    stoppedBrownianRepresentative V x ⁻¹' curveRangeEvent K
  have hcx : dist c x ≤ 2 * (r : ℝ) := by
    calc
      dist c x ≤ dist c p + dist p x := dist_triangle _ _ _
      _ ≤ (r : ℝ) + (r : ℝ) := add_le_add hcp.le (by simpa only [dist_comm] using hxp)
      _ = 2 * (r : ℝ) := by ring
  have hprob : ENNReal.ofReal (a / 2) ≤ μ E := hlanding r hr x c hcx
  have hK : IsClosed K := isClosed_cthickening
  have hA : MeasurableSet A := (isClosed_curveRangeEvent hK).measurableSet.preimage
    (measurable_stoppedBrownianRepresentative (U := V) isOpen_ball x)
  have hsub : E ≤ᵐ[μ] Aᶜ := by
    filter_upwards [standardBrownianLaw_ae_finiteExit hd hμ
      (show Bornology.IsBounded V from isBounded_ball) x] with ω hfinite
    intro hE
    have hinside : ∀ t ∈ Icc (0 : ℝ≥0) (r ^ 2), x + ω t ∈ V := by
      intro t ht
      have hnorm := hE.2 t ht
      have hshift : dist (x + ω t) x = ‖ω t‖ := by
        rw [dist_eq_norm]
        congr 1
        abel
      change dist (x + ω t) p < (L + 2) * (r : ℝ)
      calc
        dist (x + ω t) p ≤ dist (x + ω t) x + dist x p := dist_triangle _ _ _
        _ ≤ L * (r : ℝ) + (r : ℝ) := by rw [hshift]; exact add_le_add hnorm hxp
        _ < (L + 2) * (r : ℝ) := by nlinarith
    have hvisit : x + ω (r ^ 2) ∉ K := by
      apply closedBall_subset_compl_cthickening_of_exteriorBall
        (mul_pos hκ hrR) hext hδ
      have hmem := hE.1
      rw [show (κ / 2) * (r : ℝ) = κ * (r : ℝ) / 2 by ring] at hmem
      exact ball_subset_closedBall hmem
    exact stoppedBrownianRepresentative_not_all_mem_of_visit
      (U := V) (K := K) isOpen_ball hfinite hinside hvisit
  have hbad : ENNReal.ofReal (a / 2) ≤ μ Aᶜ := hprob.trans (measure_mono_ae hsub)
  have hsum : μ A + ENNReal.ofReal (a / 2) ≤ 1 := by
    calc
      μ A + ENNReal.ofReal (a / 2) ≤ μ A + μ Aᶜ := add_le_add le_rfl hbad
      _ = 1 := by rw [measure_add_measure_compl hA, measure_univ]
  have hreal : (μ A).toReal + a / 2 ≤ 1 := by
    apply (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 1)).mp
    simpa only [ENNReal.ofReal_add ENNReal.toReal_nonneg (half_pos ha).le,
      ENNReal.ofReal_toReal (measure_ne_top μ A), ENNReal.ofReal_one] using hsum
  have hbound : μ A ≤ ENNReal.ofReal (1 - a / 2) := by
    calc
      μ A = ENNReal.ofReal (μ A).toReal := (ENNReal.ofReal_toReal (measure_ne_top μ A)).symm
      _ ≤ ENNReal.ofReal (1 - a / 2) := ENNReal.ofReal_le_ofReal (by linarith)
  rw [brownianExcursionKernel_apply,
    Measure.map_apply (measurable_stoppedBrownianRepresentative isOpen_ball x)
      (isClosed_curveRangeEvent hK).measurableSet]
  exact hbound

theorem HasLipschitzBoundary.uniform_brownian_excursion_survival {d : ℕ}
    (hd : 1 ≤ d) {U : Set (Euc d)} (hL : HasLipschitzBoundary U)
    (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (μ : Measure (BrownianPath d)) [IsProbabilityMeasure μ]
    (hμ : IsStandardBrownianLaw μ) :
    ∃ s > 0, ∃ κ > 0, ∃ q R : ℝ, 0 ≤ q ∧ q < 1 ∧ 1 < R ∧
      ∀ p ∈ frontier U, ∀ r : ℝ≥0, 0 < r → (r : ℝ) < s →
        ∀ (x : Euc d) (δ : ℝ), dist x p ≤ (r : ℝ) →
          δ < κ * (r : ℝ) / 2 →
          brownianExcursionKernel (U := ball p (R * (r : ℝ))) isOpen_ball μ x
            (curveRangeEvent (cthickening δ U)) ≤ ENNReal.ofReal q := by
  obtain ⟨s, hs, κ, hκ, _, hballs⟩ := hL.exists_uniform_exterior_balls hU hUb
  obtain ⟨q, R, hq, hqone, hR, hsurvival⟩ :=
    standardBrownianLaw_uniform_boundary_excursion_survival hd μ hμ hκ
  refine ⟨s, hs, κ, hκ, q, R, hq, hqone, hR, ?_⟩
  intro p hp r hr hrs x δ hxp hδ
  obtain ⟨c, hcp, hext⟩ := hballs p hp (r : ℝ) hr hrs
  exact hsurvival U p c r hr x δ hcp hext hxp hδ

end BouRabeeGwynne
