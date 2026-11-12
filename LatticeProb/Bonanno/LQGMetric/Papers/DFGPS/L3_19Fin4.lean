/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L3_19Fin4 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_19Fin
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P3_9Final

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 3.19, square part: the moment bound

DFGPS arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), Lemma 3.19 (`eqn-ep-diam-square`,
T:2269–2272), "proven similarly but with Proposition 3.10 used in place of Proposition 3.9"
(T:2300).

* `indepFun_internalDiamU`: `indepFun_internalDiam` for the internal diameter in an open set
  `U ⊆ B̄_ρ(z)` (here the square `S^{ε𝕣}(z) ⊆ B̄_{ε𝕣}(z)`), Axioms II and III (T:2275–2281).
* `moment_of_local`: the factorization (3.31) for any local functional.
* `moment_sq_corner`: Prop 3.10 at the corner `w` of the square (translation, Axiom IV′).
* `moment_sq_centre`: the same normalized at the centre `z` of the square: Prop 3.10 is
  normalized by `h_ρ(w)` at the corner while (3.31) needs `h_ρ(z)`; the difference
  `h_ρ(w) − h_ρ(z)` is Gaussian with variance `≤ 2`, absorbed by Hölder's inequality (`p` lies
  strictly below the threshold of Prop 3.10). This Hölder step is our own detail filling in
  "proven similarly" (DEVIATIONS DFA7b-2).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped ENNReal

namespace LQGMetric.DFGPS
open Blueprint

namespace L319

variable {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}

/-- **T:2275–2281** for the internal diameter in an open set `U ⊆ B̄_ρ(z)`. -/
theorem indepFun_internalDiamU (hD : IsWeakLQGMetric γ D c) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P) (z : ℂ)
    {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r) (U : Opens ℂ) (hU : (U : Set ℂ) ⊆ closedBall z ρ)
    {A : Set ℂ} (hA : A ⊆ U) (hAne : A.Nonempty) :
    ∃ Y : Ω → ℝ≥0∞, Measurable Y ∧
      IndepFun (fun ω => circleAvg (h ω) ρ z - circleAvg (h ω) r z) Y P ∧
      ∀ᵐ ω ∂P, Y ω = ENNReal.ofReal (Real.exp (-(xiGamma γ * circleAvg (h ω) ρ z))) *
        internalDiam (D (h ω)) A U := by
  set g : Ω → DistC := fun ω => addConst (h ω) (-circleAvg (h ω) ρ z) with hg_def
  have hm : Measurable fun ω => -circleAvg (h ω) ρ z :=
    ((measurable_circleAvg_left ρ z).comp hh.measurable).neg
  have hg : IsWholePlaneGFF g P := hh.addConst hm
  obtain ⟨Φ, hΦ, hΦae⟩ := hD.locality P g (GM.Tight.isGFFPlusCont_of_wp hg) U
  obtain ⟨a, haA, haD⟩ := L32M.exists_denseSeq hAne
  set G : DistOn U → ℝ≥0∞ := fun T => ⨆ p : ℕ × ℕ, Φ T (a p.1) (a p.2)
  have hG : Measurable G := Measurable.iSup fun p =>
    (measurable_pi_apply _).comp ((measurable_pi_apply _).comp hΦ)
  have hR : Measurable fun ω => restrictTo U (g ω) := (measurable_restrictTo U).comp hg.measurable
  refine ⟨fun ω => G (restrictTo U (g ω)), hG.comp hR, ?_, ?_⟩
  · have hI := CircleAvgIndep.indepFun_circleAvg_restrict hh z hρ hρr U hU
    exact hI.comp measurable_id hG
  · filter_upwards [hΦae, hD.length P g (GM.Tight.isGFFPlusCont_of_wp hg),
      hD.ae_dist_addConst (GM.Tight.isGFFPlusCont_of_wp hh)] with ω h1 hl hsc
    have e1 : G (restrictTo U (g ω)) = internalDiam (D (g ω)) A U := by
      rw [L32M.internalDiam_eq_iSup (D (g ω)) hl U.isOpen hA haA haD]
      exact iSup_congr fun p => (h1 _ (hA (haA _)) _ (hA (haA _))).symm
    rw [e1]
    rw [show -(xiGamma γ * circleAvg (h ω) ρ z) = xiGamma γ * (-circleAvg (h ω) ρ z) by ring]
    exact L32M.internalDiam_of_scale (Real.exp_pos _) (hsc (-circleAvg (h ω) ρ z)) _ _

/-- **(3.31)** for a local functional `Dm` (independent of `h_ρ(z) − h_r(z)` after
normalization by `e^{−ξ h_ρ(z)}`). -/
theorem moment_of_local (hD : IsWeakLQGMetric γ D c) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P) (z : ℂ)
    {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r) (Dm : Ω → ℝ≥0∞) {Y : Ω → ℝ≥0∞} (hYm : Measurable Y)
    (hI : IndepFun (fun ω => circleAvg (h ω) ρ z - circleAvg (h ω) r z) Y P)
    (hYae : ∀ᵐ ω ∂P, Y ω = ENNReal.ofReal (Real.exp (-(xiGamma γ * circleAvg (h ω) ρ z))) * Dm ω)
    {p C : ℝ} (hp0 : 0 ≤ p)
    (hloc : ∫⁻ ω, (ENNReal.ofReal (scaleFac (xiGamma γ) c (h ω) ρ z)⁻¹ * Dm ω) ^ p ∂P ≤
      ENNReal.ofReal C) :
    AEMeasurable (fun ω => ENNReal.ofReal (scaleFac (xiGamma γ) c (h ω) r z)⁻¹ * Dm ω) P ∧
    ∫⁻ ω, (ENNReal.ofReal (scaleFac (xiGamma γ) c (h ω) r z)⁻¹ * Dm ω) ^ p ∂P ≤
      ENNReal.ofReal ((c ρ / c r) ^ p *
        Real.exp ((Real.log r - Real.log ρ) * (p * xiGamma γ) ^ 2 / 2) * C) := by
  have hr : 0 < r := hρ.trans_le hρr
  set ξ := xiGamma γ with hξ_def
  set Y' : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (c ρ)⁻¹ * Y ω with hY'_def
  have hY'm : Measurable Y' := measurable_const.mul hYm
  have hI' : IndepFun (fun ω => circleAvg (h ω) ρ z - circleAvg (h ω) r z) Y' P :=
    hI.comp (φ := id) (ψ := fun y : ℝ≥0∞ => ENNReal.ofReal (c ρ)⁻¹ * y) measurable_id
      (measurable_const.mul measurable_id)
  have hfac := lintegral_factor hh z hρ hρr hY'm hI' ξ p hp0
  have hcρ : 0 < c ρ := hD.tightness.1 ρ hρ
  have hcr : 0 < c r := hD.tightness.1 r hr
  set X : Ω → ℝ := fun ω => circleAvg (h ω) ρ z - circleAvg (h ω) r z with hX_def
  have hXm : Measurable X := CircleAvg.measurable_cInc hh ρ z r z
  have hae : ∀ᵐ ω ∂P, ENNReal.ofReal (scaleFac ξ c (h ω) r z)⁻¹ * Dm ω =
      ENNReal.ofReal (c ρ / c r) * (ENNReal.ofReal (Real.exp (ξ * X ω)) * Y' ω) := by
    filter_upwards [hYae] with ω hω
    rw [hY'_def]
    simp only
    rw [hω, ← mul_assoc, ← mul_assoc, ← mul_assoc,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    rw [scaleFac, hX_def]
    simp only
    rw [mul_sub, Real.exp_sub, Real.exp_neg]
    field_simp
  have hae2 : ∀ᵐ ω ∂P, Y' ω = ENNReal.ofReal (scaleFac ξ c (h ω) ρ z)⁻¹ * Dm ω := by
    filter_upwards [hYae] with ω hω
    rw [hY'_def]
    simp only
    rw [hω, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    rw [scaleFac, Real.exp_neg, mul_inv]
  have hmeasW : Measurable fun ω => ENNReal.ofReal (c ρ / c r) *
      (ENNReal.ofReal (Real.exp (ξ * X ω)) * Y' ω) :=
    measurable_const.mul ((ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul hXm))).mul hY'm)
  refine ⟨hmeasW.aemeasurable.congr (hae.mono fun ω hω => hω.symm), ?_⟩
  rw [lintegral_congr_ae (hae.mono fun ω hω => by rw [hω])]
  set W : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (ξ * X ω)) * Y' ω with hW_def
  have hWm : Measurable W := (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul hXm))).mul hY'm
  rw [show (fun ω => (ENNReal.ofReal (c ρ / c r) * W ω) ^ p) =
      fun ω => ENNReal.ofReal (c ρ / c r) ^ p * W ω ^ p from
    funext fun ω => ENNReal.mul_rpow_of_nonneg _ _ hp0, lintegral_const_mul _ (hWm.pow_const p)]
  rw [hfac, lintegral_congr_ae (hae2.mono fun ω hω => by rw [hω])]
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity), mul_assoc]
  gcongr

/-- **Prop 3.10 at the corner `w`** (translation by Axiom IV′, as in `moment_ball`). -/
theorem moment_sq_corner (h310 : Prop3_10) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c) {q : ℝ} (hq : q < 4 * dGamma γ / γ ^ 2) :
    ∃ C : ℝ, ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsNormalizedWPGFF h P → ∀ ρ : ℝ, 0 < ρ → ∀ w : ℂ,
        ∫⁻ ω, (ENNReal.ofReal (scaleFac (xiGamma γ) c (h ω) ρ w)⁻¹ *
          internalDiam (D (h ω)) (scaleSet ρ w unitSq) (scaleSet ρ w unitSq)) ^ q ∂P ≤
            ENNReal.ofReal C := by
  obtain ⟨C, hC⟩ := h310 γ hγ0 hγ2 D c hD q hq
  refine ⟨C, ?_⟩
  intro Ω _ P _ h hh ρ hρ w
  refine le_trans (le_of_eq (lintegral_congr_ae ?_)) (hC P (fun ω => transField w (h ω))
    (isNormalized_transField hh.1 w) ρ hρ)
  filter_upwards [ae_transField hD hh.1 w hρ] with ω ⟨hd1, hd2⟩
  congr 1
  set e := Real.exp (-(xiGamma γ * circleAvg (h ω) 1 w)) with he_def
  have he : 0 < e := Real.exp_pos _
  have hS : scaleFac (xiGamma γ) c (transField w (h ω)) ρ 0 =
      e * scaleFac (xiGamma γ) c (h ω) ρ w := by
    unfold scaleFac
    rw [hd2, mul_sub, sub_eq_add_neg, Real.exp_add, he_def]
    ring
  have hX : internalDiam (D (transField w (h ω))) (rS ρ) (rS ρ) = ENNReal.ofReal e *
      internalDiam (D (h ω)) (scaleSet ρ w unitSq) (scaleSet ρ w unitSq) := by
    rw [rS, scaleSet_zero_eq_image ρ w]
    exact internalDiam_transl_smul he w hd1 _ _
  have hs : 0 < scaleFac (xiGamma γ) c (h ω) ρ w :=
    mul_pos (hD.tightness.1 ρ hρ) (Real.exp_pos _)
  have hk : ENNReal.ofReal (e * scaleFac (xiGamma γ) c (h ω) ρ w)⁻¹ * ENNReal.ofReal e =
      ENNReal.ofReal (scaleFac (xiGamma γ) c (h ω) ρ w)⁻¹ := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  rw [hS, hX, ← mul_assoc, hk]

end L319
end LQGMetric.DFGPS
