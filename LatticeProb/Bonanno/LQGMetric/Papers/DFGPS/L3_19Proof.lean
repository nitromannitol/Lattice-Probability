/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L3_19Proof at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgIndep2
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_2Meas

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 3.19, step 1: independence of the coarse increment and the local diameter

DFGPS arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Lemma 3.19,
T:2275–2281: "`h_{2ε𝕣}(z) − h_𝕣(z)` … is independent from `(h − h_{2ε𝕣}(z))|_{B_{2ε𝕣}(z)}`.
By Axioms II and III, `h_{2ε𝕣}(z) − h_𝕣(z)` is also independent from the internal metric
`D_{h − h_{2ε𝕣}(z)}(u, v; B_{2ε𝕣}(z)) = e^{−ξ h_{2ε𝕣}(z)} D_h(u, v; B_{2ε𝕣}(z))`."

`indepFun_internalDiam`: for `A ⊆ B_ρ(z)` nonempty and `ρ ≤ r`, there is a measurable
`Y : Ω → ℝ≥0∞` independent of `h_ρ(z) − h_r(z)` with `Y = e^{−ξ h_ρ(z)} diam(A; B_ρ(z))` a.s.
(locality as in `L32M.aeEventIn_annEvent`: the internal diameter is a countable supremum over a
dense sequence, `L32M.internalDiam_eq_iSup`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped ENNReal

namespace LQGMetric.DFGPS
open Blueprint

namespace L319

/-- **T:2275–2281**: the coarse increment `h_ρ(z) − h_r(z)` is independent of
`e^{−ξ h_ρ(z)} diam(A; B_ρ(z))` (a.s. equal to a measurable function of
`(h − h_ρ(z))|_{B_ρ(z)}`). -/
theorem indepFun_internalDiam {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P) (z : ℂ) {ρ r : ℝ}
    (hρ : 0 < ρ) (hρr : ρ ≤ r) {A : Set ℂ} (hA : A ⊆ ball z ρ) (hAne : A.Nonempty) :
    ∃ Y : Ω → ℝ≥0∞, Measurable Y ∧
      IndepFun (fun ω => circleAvg (h ω) ρ z - circleAvg (h ω) r z) Y P ∧
      ∀ᵐ ω ∂P, Y ω = ENNReal.ofReal (Real.exp (-(xiGamma γ * circleAvg (h ω) ρ z))) *
        internalDiam (D (h ω)) A (ball z ρ) := by
  set g : Ω → DistC := fun ω => addConst (h ω) (-circleAvg (h ω) ρ z) with hg_def
  have hm : Measurable fun ω => -circleAvg (h ω) ρ z :=
    ((measurable_circleAvg_left ρ z).comp hh.measurable).neg
  have hg : IsWholePlaneGFF g P := hh.addConst hm
  set U : Opens ℂ := ballO z ρ
  obtain ⟨Φ, hΦ, hΦae⟩ := hD.locality P g (GM.Tight.isGFFPlusCont_of_wp hg) U
  obtain ⟨a, haA, haD⟩ := L32M.exists_denseSeq hAne
  set G : DistOn U → ℝ≥0∞ := fun T => ⨆ p : ℕ × ℕ, Φ T (a p.1) (a p.2)
  have hG : Measurable G := Measurable.iSup fun p =>
    (measurable_pi_apply _).comp ((measurable_pi_apply _).comp hΦ)
  have hR : Measurable fun ω => restrictTo U (g ω) := (measurable_restrictTo U).comp hg.measurable
  refine ⟨fun ω => G (restrictTo U (g ω)), hG.comp hR, ?_, ?_⟩
  · have hI := CircleAvgIndep.indepFun_circleAvg_restrict hh z hρ hρr U
      (fun w hw => ball_subset_closedBall hw)
    exact hI.comp measurable_id hG
  · filter_upwards [hΦae, hD.length P g (GM.Tight.isGFFPlusCont_of_wp hg),
      hD.ae_dist_addConst (GM.Tight.isGFFPlusCont_of_wp hh)] with ω h1 hl hsc
    have hU : (U : Set ℂ) = ball z ρ := rfl
    have e1 : G (restrictTo U (g ω)) = internalDiam (D (g ω)) A (ball z ρ) := by
      rw [L32M.internalDiam_eq_iSup (D (g ω)) hl isOpen_ball hA haA haD]
      exact iSup_congr fun p => (h1 _ (hA (haA _)) _ (hA (haA _))).symm
    rw [e1]
    rw [show -(xiGamma γ * circleAvg (h ω) ρ z) = xiGamma γ * (-circleAvg (h ω) ρ z) by ring]
    exact L32M.internalDiam_of_scale (Real.exp_pos _) (hsc (-circleAvg (h ω) ρ z)) _ _

/-- `Var(h_ρ(z) − h_r(z)) = log r − log ρ` for `ρ ≤ r` (DS §3.1) -/
lemma incCov_center {z : ℂ} {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r) :
    CircleAvg.incCov z ρ z r z ρ z r = Real.log r - Real.log ρ := by
  have hr : 0 < r := hρ.trans_le hρr
  rw [CircleAvg.incCov, CircleAvg.circCov_center z hρ ρ hρ, CircleAvg.circCov_center z hρ r hr,
    CircleAvg.circCov_center z hr ρ hρ, CircleAvg.circCov_center z hr r hr,
    inv_mul_cancel₀ hρ.ne', inv_mul_cancel₀ hr.ne']
  have h1 : Real.posLog 1 = 0 := by simp [Real.posLog]
  have h2 : Real.posLog (r⁻¹ * ρ) = 0 := by
    rw [Real.posLog_eq_zero_iff, abs_of_nonneg (by positivity), inv_mul_le_iff₀ hr, mul_one]
    exact hρr
  have h3 : Real.posLog (ρ⁻¹ * r) = Real.log r - Real.log ρ := by
    rw [Real.posLog, max_eq_right, Real.log_mul (inv_ne_zero hρ.ne') hr.ne', Real.log_inv]
    · ring
    · exact Real.log_nonneg (by rw [le_inv_mul_iff₀ hρ, mul_one]; exact hρr)
  rw [h1, h2, h3]
  ring

/-- `E e^{tX} = e^{v t²/2}` for `X ~ N(0, v)` (as a lower integral) -/
lemma lintegral_exp_of_map {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    (hX : Measurable X) {v : NNReal} (hmap : P.map X = gaussianReal 0 v) (t : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (t * X ω)) ∂P = ENNReal.ofReal (Real.exp (v * t ^ 2 / 2)) := by
  have hf : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (t * x)) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul measurable_id))
  rw [← lintegral_map hf hX, hmap, ← ofReal_integral_eq_lintegral_ofReal
    (integrable_exp_mul_gaussianReal t) (Eventually.of_forall fun x => (Real.exp_pos _).le)]
  congr 1
  have := congrFun (mgf_id_gaussianReal (μ := 0) (v := v)) t
  simpa [mgf] using this

/-- **(3.31), the factorization**: with `Y` independent of `X = h_ρ(z) − h_r(z)`,
`E[(e^{ξX} Y)^p] = e^{ξ²p² log(r/ρ)/2} E[Y^p]`. -/
theorem lintegral_factor {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistC} (hh : IsWholePlaneGFF h P) (z : ℂ) {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r)
    {Y : Ω → ℝ≥0∞} (hY : Measurable Y)
    (hI : IndepFun (fun ω => circleAvg (h ω) ρ z - circleAvg (h ω) r z) Y P) (ξ p : ℝ)
    (hp : 0 ≤ p) :
    ∫⁻ ω, (ENNReal.ofReal (Real.exp (ξ * (circleAvg (h ω) ρ z - circleAvg (h ω) r z))) * Y ω) ^ p
        ∂P = ENNReal.ofReal (Real.exp ((Real.log r - Real.log ρ) * (p * ξ) ^ 2 / 2)) *
          ∫⁻ ω, Y ω ^ p ∂P := by
  have hr : 0 < r := hρ.trans_le hρr
  set X := fun ω => circleAvg (h ω) ρ z - circleAvg (h ω) r z
  have hXm : Measurable X := CircleAvg.measurable_cInc hh ρ z r z
  obtain ⟨hmap, -⟩ := CircleAvg.map_cInc hh hρ hr z z
  rw [incCov_center hρ hρr] at hmap
  have hE : ∀ ω, (ENNReal.ofReal (Real.exp (ξ * X ω))) ^ p =
      ENNReal.ofReal (Real.exp ((p * ξ) * X ω)) := fun ω => by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hp, ← Real.exp_mul]
    ring_nf
  have hmf : Measurable fun x : ℝ => (ENNReal.ofReal (Real.exp (ξ * x))) ^ p :=
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul measurable_id))).pow_const p
  have hI' := hI.comp hmf (Measurable.pow_const measurable_id p)
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp]
  have := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun'' (hmf.comp hXm).aemeasurable
    (hY.pow_const p).aemeasurable hI'
  simp only [Function.comp_apply] at this
  rw [this]
  congr 1
  simp_rw [hE]
  rw [lintegral_exp_of_map hXm hmap, Real.coe_toNNReal _ (by
    linarith [Real.log_le_log hρ hρr])]

end L319
end LQGMetric.DFGPS
