/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_17Core2D at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17Core2C
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_17CoreS
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_6
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8FinCmp

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.17, core case: the law of `(h, D₁)` in the limit coupling (step C5 (i))

Source: DFGPS = arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Lemma 2.17,
Step 3 (T:1240–1256): the first coordinate of the limit coupling is the limit `D_h` of the
original sequence, for the normalized field `h − h_r(z)` multiplied by `e^{−ξ h_r(z)}`
(T:1150–1155, Weyl scaling by a constant, Lemma 2.6 with `r = 1`). Decision D80, packet P-C (iii).

* `ae_lfppC_normField` — a.s. `𝔞⁻¹D^ε_{h − h_r(z)} = e^{−ξ h_r(z)} 𝔞⁻¹D^ε_h` (from
  `lem2_6_ae_const` with `r = 1`).
* `map_coupling_fst_eq` — if `(J h, lfppJoint(h − h_r(z)), Y₂ₙ) → ρ` in law along `εₙ` and
  `(J h, 𝔞⁻¹D^εₙ_h) → (J h, D_h)` jointly (the hypothesis of `Lem2_17Core`, D90 coordinates), then the law of
  `(x, D₁)` under `ρ` is that of `(J h, e^{−ξ h_r(z)} D_h)`. Since `h_r(z)` is only a measurable
  function of `J h`, this uses stable convergence (`tendsto_law_of_fixed_marginal`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace Metric
open scoped ENNReal BoundedContinuousFunction

namespace LQGMetric.DFGPS.L217

open Blueprint LFPP

theorem affineComp_one_zero_l217 (g : DistC) : affineComp 1 0 g = g := by
  refine DFunLike.ext _ _ fun φ => ?_
  have e : testAffinePull 1 0 φ = φ := TestFunction.ext fun x => by
    rw [testAffinePull_apply _ _ one_ne_zero]; simp
  rw [GFFInv.affineComp_apply, e]; simp

/-- **Weyl scaling by the constant `−h_r(z)` at the LFPP level** (Lemma 2.6 with `r = 1`) -/
theorem ae_lfppC_normField {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) (ξ : ℝ) {ε : ℝ} (hε : 0 < ε) (z : ℂ) (r : ℝ) :
    ∀ᵐ ω ∂P, lfppC ξ ε (normField h z r ω) =
      Real.exp (-ξ * circleAvg (h ω) r z) • lfppC ξ ε (h ω) := by
  filter_upwards [lem2_6_ae_const hh ξ hε one_pos,
    hh.ae_tendstoLocallyUniformly_heatMollify ε hε.ne'] with ω h6 hc
  set c := circleAvg (h ω) r z
  have hmg : ∀ x, heatMollify ε (normField h z r ω) x = heatMollify ε (h ω) x + -c := fun x =>
    heatMollify_addConst_of_tendsto hε.ne'
      ((tendstoLocallyUniformlyOn_univ.2 hc.1).tendsto_at (mem_univ x)) (-c)
  have hgc : Continuous (heatMollify ε (normField h z r ω)) := by
    have : heatMollify ε (normField h z r ω) = fun x => heatMollify ε (h ω) x + -c := funext hmg
    rw [this]; exact hc.2.add continuous_const
  ext p
  rw [ContinuousMap.smul_apply, lfppC_apply_of_continuous hgc, lfppC_apply_of_continuous hc.2,
    smul_eq_mul]
  have hD := h6 c p.1 p.2
  rw [div_one, affineComp_one_zero_l217, inv_one, one_mul] at hD
  simp only [Complex.ofReal_one, one_mul] at hD
  rw [show normField h z r ω = addConst (h ω) (-c) from rfl, hD, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.exp_pos _).le]
  ring

/-- `x ↦ h_r(z)` for `x = J h` (a measurable function of the coordinates) -/
def cbar (r : ℝ) (z : ℂ) (x : CoordJ → ℝ) : ℝ := circleAvg (pairJInv ⊤ x) r z

/-- the bounded continuous function `((x, a), d) ↦ g (x, e^{−ξ a} d)` -/
def scaleBCF (ξ : ℝ) (g : (CoordJ → ℝ) × C(ℂ × ℂ, ℝ) →ᵇ ℝ) :
    ((CoordJ → ℝ) × ℝ) × C(ℂ × ℂ, ℝ) →ᵇ ℝ :=
  ⟨⟨fun y => g (y.1.1, Real.exp (-ξ * y.1.2) • y.2),
    g.continuous.comp ((continuous_fst.comp continuous_fst).prodMk
      (((Real.continuous_exp.comp (continuous_const.mul
        (continuous_snd.comp continuous_fst)))).smul continuous_snd))⟩, 2 * ‖g‖, fun x y => by
      refine (dist_triangle (y := 0) _ _).trans ?_
      rw [dist_zero_right, dist_zero_left]
      have := g.norm_coe_le_norm
      linarith [this (x.1.1, Real.exp (-ξ * x.1.2) • x.2),
        this (y.1.1, Real.exp (-ξ * y.1.2) • y.2)]⟩

theorem scaleBCF_apply (ξ : ℝ) (g : (CoordJ → ℝ) × C(ℂ × ℂ, ℝ) →ᵇ ℝ)
    (y : ((CoordJ → ℝ) × ℝ) × C(ℂ × ℂ, ℝ)) :
    scaleBCF ξ g y = g (y.1.1, Real.exp (-ξ * y.1.2) • y.2) := rfl

/-- **stable convergence of `(J h, e^{−ξ h_r(z)} 𝔞⁻¹D^εₙ_h)`** -/
theorem tendsto_integral_scaled_lfppC {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {Dh : Ω → ContMetric}
    (hDm : Measurable Dh) (ξ : ℝ) (z : ℂ) (r : ℝ) {εs : ℕ → ℝ} (hεs : ∀ n, 0 < εs n)
    (hconvD : ∀ φ : (CoordJ → ℝ) × C(ℂ × ℂ, ℝ) → ℝ, Continuous φ → (∃ C, ∀ x, |φ x| ≤ C) →
      Tendsto (fun n => ∫ ω, φ (pairJ ⊤ (h ω), toCMap fun p =>
          (aEpsDF ξ (εs n))⁻¹ * lfppDist ξ (εs n) (h ω) p) ∂P) atTop
        (𝓝 (∫ ω, φ (pairJ ⊤ (h ω), (Dh ω).1) ∂P)))
    (g : (CoordJ → ℝ) × C(ℂ × ℂ, ℝ) →ᵇ ℝ) :
    Tendsto (fun n => ∫ ω, g (pairJ ⊤ (h ω),
        Real.exp (-ξ * circleAvg (h ω) r z) • lfppC ξ (εs n) (h ω)) ∂P) atTop
      (𝓝 (∫ ω, g (pairJ ⊤ (h ω), Real.exp (-ξ * circleAvg (h ω) r z) • (Dh ω).1) ∂P)) := by
  have hJm : Measurable fun ω => pairJ ⊤ (h ω) := (measurable_pairJ ⊤).comp hh.measurable
  have hcb : Measurable (cbar r z) := (measurable_circleAvg_left r z).comp (measurable_pairJInv ⊤)
  have hcbJ : ∀ ω, cbar r z (pairJ ⊤ (h ω)) = circleAvg (h ω) r z := fun ω => by
    simp only [cbar, pairJInv_pairJ]
  have hYm : ∀ n, AEMeasurable (fun ω => lfppC ξ (εs n) (h ω)) P := fun n =>
    aemeasurable_lfppC (isGFFPlusBddCont_of_wp hh) (hεs n).ne'
  have hDm' : Measurable fun ω => (Dh ω).1 := measurable_subtype_coe.comp hDm
  have hc0 : ∀ φ : (CoordJ → ℝ) × C(ℂ × ℂ, ℝ) → ℝ, Continuous φ → (∃ C, ∀ x, |φ x| ≤ C) →
      Tendsto (fun n => ∫ ω, φ (pairJ ⊤ (h ω), (hYm n).mk _ ω) ∂P) atTop
        (𝓝 (∫ ω, φ (pairJ ⊤ (h ω), (Dh ω).1) ∂P)) := fun φ hφ hb => by
    refine (hconvD φ hφ hb).congr fun n => integral_congr_ae ?_
    filter_upwards [(hYm n).ae_eq_mk] with ω hω
    simp only [← hω]
    rfl
  have hst := tendsto_law_of_fixed_marginal (P := P) (P' := P) hJm hJm rfl
    (fun n => (hYm n).measurable_mk) hDm' hc0 (Φ := fun x => (x, cbar r z x))
    (measurable_id.prodMk hcb)
  have k1 := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hst) (scaleBCF ξ g)
  simp only [ProbabilityMeasure.coe_mk] at k1
  have hJc : Measurable fun ω => (pairJ ⊤ (h ω), cbar r z (pairJ ⊤ (h ω))) :=
    hJm.prodMk (hcb.comp hJm)
  have hm1 : Measurable fun ω => ((pairJ ⊤ (h ω), cbar r z (pairJ ⊤ (h ω))), (Dh ω).1) :=
    hJc.prodMk hDm'
  rw [integral_map hm1.aemeasurable (scaleBCF ξ g).continuous.aestronglyMeasurable] at k1
  have k1' := k1.congr (f₂ := fun n => ∫ ω, g (pairJ ⊤ (h ω),
      Real.exp (-ξ * circleAvg (h ω) r z) • lfppC ξ (εs n) (h ω)) ∂P) fun n => by
    have hm2 : Measurable fun ω => ((pairJ ⊤ (h ω), cbar r z (pairJ ⊤ (h ω))), (hYm n).mk _ ω) :=
      hJc.prodMk (hYm n).measurable_mk
    rw [integral_map hm2.aemeasurable (scaleBCF ξ g).continuous.aestronglyMeasurable]
    refine integral_congr_ae ?_
    filter_upwards [(hYm n).ae_eq_mk] with ω hω
    simp only [scaleBCF_apply, hcbJ, ← hω]
  simpa only [scaleBCF_apply, hcbJ] using k1'

/-- **the law of `(x, D₁)` under the limit coupling** (T:1240–1256 with T:1150–1155) -/
theorem map_coupling_fst_eq {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P) {Dh : Ω → ContMetric}
    (hDm : Measurable Dh) (ξ : ℝ) (z : ℂ) (r : ℝ) {εs : ℕ → ℝ} (hεs : ∀ n, 0 < εs n)
    (hconvD : ∀ φ : (CoordJ → ℝ) × C(ℂ × ℂ, ℝ) → ℝ, Continuous φ → (∃ C, ∀ x, |φ x| ≤ C) →
      Tendsto (fun n => ∫ ω, φ (pairJ ⊤ (h ω), toCMap fun p =>
          (aEpsDF ξ (εs n))⁻¹ * lfppDist ξ (εs n) (h ω) p) ∂P) atTop
        (𝓝 (∫ ω, φ (pairJ ⊤ (h ω), (Dh ω).1) ∂P)))
    {Y₂ : ℕ → Ω → DyProd} {ρ : ProbabilityMeasure ((CoordJ → ℝ) × (DyProd × DyProd))}
    (hρ : ∀ f : (CoordJ → ℝ) × (DyProd × DyProd) →ᵇ ℝ, Tendsto (fun n => ∫ ω, f (pairJ ⊤ (h ω),
        (lfppJoint ξ (εs n) (normField h z r ω), Y₂ n ω)) ∂P) atTop
      (𝓝 (∫ p, f p ∂(ρ : Measure ((CoordJ → ℝ) × (DyProd × DyProd)))))) :
    (ρ : Measure ((CoordJ → ℝ) × (DyProd × DyProd))).map (fun p => (p.1, p.2.1.1)) =
      P.map fun ω => (pairJ ⊤ (h ω), Real.exp (-ξ * circleAvg (h ω) r z) • (Dh ω).1) := by
  have hJm : Measurable fun ω => pairJ ⊤ (h ω) := (measurable_pairJ ⊤).comp hh.measurable
  have hqc : Continuous fun p : (CoordJ → ℝ) × (DyProd × DyProd) => (p.1, p.2.1.1) :=
    continuous_fst.prodMk (continuous_fst.comp (continuous_fst.comp continuous_snd))
  have hDm' : Measurable fun ω => (Dh ω).1 := measurable_subtype_coe.comp hDm
  have hsm : Measurable fun ω => Real.exp (-ξ * circleAvg (h ω) r z) • (Dh ω).1 :=
    (measurable_const.mul ((measurable_circleAvg_left r z).comp hh.measurable)).exp.smul hDm'
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun g => ?_
  have k1 := tendsto_integral_scaled_lfppC hh hDm ξ z r hεs hconvD g
  have k2 := hρ (g.compContinuous ⟨_, hqc⟩)
  rw [integral_map hqc.aemeasurable g.continuous.aestronglyMeasurable,
    integral_map (hJm.prodMk hsm).aemeasurable g.continuous.aestronglyMeasurable]
  refine tendsto_nhds_unique k2 (k1.congr' ?_)
  filter_upwards [] with n
  refine integral_congr_ae ?_
  filter_upwards [ae_lfppC_normField hh ξ (hεs n) z r] with ω hn
  simp only [BoundedContinuousFunction.compContinuous_apply, ContinuousMap.coe_mk, lfppJoint, hn]

end L217

end LQGMetric.DFGPS
