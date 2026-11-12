/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_20Bilip at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_20
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_20Tight
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.Bilip
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightC

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.20: the bi-Lipschitz-type bounds (T:1325–1330) from Lemma 2.13

DFGPS = arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Lemma 2.20: "Lemma 2.13
along with the translation invariance of the law of `h`, modulo additive constant, implies that
there exists `C > 0` … such that for each `z ∈ ℂ` and each `r > 0`" the two displays T:1325–1330
hold. This file proves `Lem2_20Bilip` from

* `Lem2_13` (proved, `lem2_13`): tightness of the laws of `X_r = 𝔠_r⁻¹ e^{−ξ h_r(0)} D_h(r·, r·)`,
  `r > 0`, with Prokhorov limit points carried by continuous metrics;
* `Lem2_20Transl` (open node): the translation invariance used by the paper, in the form
  "the law of `e^{−ξ h_r(z)} D_h(r· + z, r· + z)` does not depend on `z`".

From Lemma 2.13 the uniform bounds come from the compactness argument of `L2_20Tight.lean`
(lower bound for `inf_{∂B_{1/2} × ∂B_1} X_r`, and the two chain conditions); the internal diameter
of `∂B_r(z)` in the annulus is then bounded by chaining (`GM.Tight.internal_le_of_chain`,
`GM.Tight.exists_chain_compact`: the argument of GM S2.4c, D-A3, which the paper's (eq:tight),
T:370–374, asserts without proof). Own argument for the chaining step (as in GM S2.4c,
DEVIATIONS DA5); DEVIATIONS DFB12-4.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint GM.Tight

namespace L220

/-- the rescaled pair `(g, D) ↦ 𝔠_r⁻¹ e^{−ξ g_r(z)} D(r· + z, r· + z)` -/
def resc (ξ : ℝ) (c : ℝ → ℝ) (r : ℝ) (z : ℂ) (x : DistC × ContMetric) : C(ℂ × ℂ, ℝ) :=
  ((c r)⁻¹ * Real.exp (-ξ * circleAvg x.1 r z)) • x.2.1.comp (affArgs r z)

lemma resc_apply (ξ : ℝ) (c : ℝ → ℝ) (r : ℝ) (z : ℂ) (x : DistC × ContMetric) (p : ℂ × ℂ) :
    resc ξ c r z x p = ((c r)⁻¹ * Real.exp (-ξ * circleAvg x.1 r z)) *
      x.2.1 ((r : ℂ) * p.1 + z, (r : ℂ) * p.2 + z) := rfl

theorem measurable_resc (ξ : ℝ) (c : ℝ → ℝ) (r : ℝ) (z : ℂ) : Measurable (resc ξ c r z) := by
  have h1 : Measurable fun x : DistC × ContMetric => x.2.1.comp (affArgs r z) :=
    (ContinuousMap.continuous_precomp (affArgs r z)).measurable.comp
      (measurable_subtype_coe.comp measurable_snd)
  have h2 : Measurable fun x : DistC × ContMetric =>
      (c r)⁻¹ * Real.exp (-ξ * circleAvg x.1 r z) :=
    measurable_const.mul (Real.measurable_exp.comp
      (measurable_const.mul ((measurable_circleAvg_left r z).comp measurable_fst)))
  exact h2.smul h1

end L220

open L220 in
/-- **Translation invariance used in the proof of DFGPS Lemma 2.20** (T:1323–1324, "the
translation invariance of the law of `h`, modulo additive constant"): for a subsequential limit
coupling `(h, D_h)` as in `Lem2_20`, the law of `e^{−ξ h_r(z)} D_h(r· + z, r· + z)` does not
depend on `z`. Open node. -/
def Lem2_20Transl : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (Dh : Ω → ContMetric) (εn : ℕ → ℝ),
    IsNormalizedWPGFF h P → Measurable Dh → (∀ n, 0 < εn n) → Tendsto εn atTop (𝓝 0) →
    (∀ φ : (CoordJ → ℝ) × C(ℂ × ℂ, ℝ) → ℝ, Continuous φ → (∃ C, ∀ x, |φ x| ≤ C) →
      Tendsto (fun n => ∫ ω, φ (pairJ ⊤ (h ω), toCMap fun p =>
          (aEpsDF (xiGamma γ) (εn n))⁻¹ * lfppDist (xiGamma γ) (εn n) (h ω) p) ∂P) atTop
        (𝓝 (∫ ω, φ (pairJ ⊤ (h ω), (Dh ω).1) ∂P))) →
    ∀ (z : ℂ) (r : ℝ), 0 < r →
      P.map (fun ω => resc (xiGamma γ) (fun _ => 1) r z (h ω, Dh ω)) =
        P.map (fun ω => resc (xiGamma γ) (fun _ => 1) r 0 (h ω, Dh ω))

namespace L220

lemma resc_eq_smul (ξ : ℝ) (c : ℝ → ℝ) (r : ℝ) (z : ℂ) (x : DistC × ContMetric) :
    resc ξ c r z x = (c r)⁻¹ • resc ξ (fun _ => 1) r z x := by
  ext p
  simp only [resc_apply, ContinuousMap.smul_apply, smul_eq_mul, inv_one, one_mul]
  ring

/-- the law of the rescaled metric at centre `z` equals that at centre `0` -/
lemma map_resc_eq (hT : Lem2_20Transl) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {Ω : Type}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}
    {Dh : Ω → ContMetric} {εn : ℕ → ℝ} (hh : IsNormalizedWPGFF h P) (hDm : Measurable Dh)
    (hεp : ∀ n, 0 < εn n) (hεt : Tendsto εn atTop (𝓝 0))
    (hconv : ∀ φ : (CoordJ → ℝ) × C(ℂ × ℂ, ℝ) → ℝ, Continuous φ → (∃ C, ∀ x, |φ x| ≤ C) →
      Tendsto (fun n => ∫ ω, φ (pairJ ⊤ (h ω), toCMap fun p =>
          (aEpsDF (xiGamma γ) (εn n))⁻¹ * lfppDist (xiGamma γ) (εn n) (h ω) p) ∂P) atTop
        (𝓝 (∫ ω, φ (pairJ ⊤ (h ω), (Dh ω).1) ∂P))) (c : ℝ → ℝ) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    P.map (fun ω => resc (xiGamma γ) c r z (h ω, Dh ω)) =
      P.map (fun ω => resc (xiGamma γ) c r 0 (h ω, Dh ω)) := by
  have hpair : Measurable fun ω => (h ω, Dh ω) := hh.1.measurable.prodMk hDm
  have hs : Measurable fun d : C(ℂ × ℂ, ℝ) => (c r)⁻¹ • d := (continuous_const_smul _).measurable
  have e : ∀ w : ℂ, (fun ω => resc (xiGamma γ) c r w (h ω, Dh ω)) =
      (fun d : C(ℂ × ℂ, ℝ) => (c r)⁻¹ • d) ∘
        fun ω => resc (xiGamma γ) (fun _ => 1) r w (h ω, Dh ω) := fun w => by
    funext ω; exact resc_eq_smul _ _ _ _ _
  have hm : ∀ w : ℂ, Measurable fun ω => resc (xiGamma γ) (fun _ => 1) r w (h ω, Dh ω) :=
    fun w => (measurable_resc _ _ _ _).comp hpair
  rw [e z, e 0, ← Measure.map_map hs (hm z), ← Measure.map_map hs (hm 0),
    hT γ hγ hγ2 P h Dh εn hh hDm hεp hεt hconv z r hr]

end L220

end LQGMetric.DFGPS
