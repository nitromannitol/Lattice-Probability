/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.L23CondField at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.L23Cond

/-!
# DDDF (5.59), field form: resampling the Gaussian part of the field

DDDF = arXiv:1904.08021, `tightness.tex` l. 1086–1091 ((5.59) = `eq:SndTerm`, Step 3 of the proof
of Theorem 20; blueprint row DDDF.L23, second half): with `ψ_{0,n} = (ψ_{0,n} − ψ_{0,K}) + ψ_{0,K}`
and `ψ̃_{0,K}` an independent copy of `ψ_{0,K}`,
`E((log L^K_n(ψ) − log L_n(ψ))²) = 2 E Var(log L_n(ψ) | ψ_{0,n} − ψ_{0,K}) ≤ C K`,
"using Gaussian concentration as in the proof of Lemma 23".

`L23.dddf_eq559_generic` is this step for general continuous fields: `V` (playing
`ψ_{0,n} − ψ_{0,K}`), a centered Gaussian process `Y` (playing `ψ_{0,K}`) with
`Var Y(x) ≤ s` on `[0,1]²` and an identically distributed copy `Y'`, with `Y ⟂ Y'` and
`(Y, Y') ⟂ V`:
`E (log L(V + Y') − log L(V + Y))² ≤ 2 ξ² s`. (For `ψ_{0,K}`, `s = O(K)`.)
Proof as for Lemma 23: discretize `V + Y` and `V + Y'` on the dyadic grid of mesh `2^{-k}`
(`L23Disc.lean`), apply the finite-dimensional bound `L23.lintegral_sq_sub_copy_le`
(conditionally on `V`, `2 Var ≤ 2 ξ² s`), and pass to the limit `k → ∞` by Fatou.
The instantiation with `ψ` (which needs the independent copy `ψ̃_{0,K}`, i.e. the resampling
set-up of Theorem 20's Efron–Stein step) belongs to DDDF.T20.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace LQGMetric
namespace DDDF
namespace L23

/-- restriction of a function to the dyadic grid -/
def gridRestr (k : ℕ) (f : ℂ → ℝ) : grid k → ℝ := fun c => f c

lemma measurable_gridRestr (k : ℕ) : Measurable (gridRestr k) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

lemma tendsto_disc_add {ξ : ℝ} {V Y : ℂ → ℝ} (hV : Continuous V) (hY : Continuous Y) :
    Tendsto (fun k => discLogLen ξ k (gridRestr k V + gridRestr k Y)) atTop
      (𝓝 (logLen ξ fun x => V x + Y x)) := by
  have h := tendsto_logLen_snap (ξ := ξ) (hV.add hY)
  unfold discLogLen
  exact h

/-- **DDDF (5.59), field form**: `E (log L(V + Y') − log L(V + Y))² ≤ 2 ξ² s` for a centered
Gaussian process `Y` with `Var Y ≤ s` on `[0,1]²`, an i.d. copy `Y' ⟂ Y`, and `(Y, Y') ⟂ V`. -/
theorem dddf_eq559_generic {ξ s : ℝ} {Y Y' V : ℂ → Ω → ℝ}
    (hYc : ∀ ω, Continuous fun x => Y x ω) (hY'c : ∀ ω, Continuous fun x => Y' x ω)
    (hVc : ∀ ω, Continuous fun x => V x ω) (hYm : ∀ x, Measurable (Y x))
    (hY'm : ∀ x, Measurable (Y' x)) (hVm : ∀ x, Measurable (V x))
    (hY : IsGaussianProcess Y P) (h0 : ∀ x, ∫ ω, Y x ω ∂P = 0) (hs : 0 ≤ s)
    (hvar : ∀ x ∈ sq01, Var[Y x; P] ≤ s)
    (hid : IdentDistrib (fun ω x => Y x ω) (fun ω x => Y' x ω) P P)
    (hind1 : IndepFun (fun ω x => Y x ω) (fun ω x => Y' x ω) P)
    (hind2 : IndepFun (fun ω => ((fun x => Y x ω), (fun x => Y' x ω))) (fun ω x => V x ω) P) :
    Integrable (fun ω => (logLen ξ (fun x => V x ω + Y' x ω) -
      logLen ξ (fun x => V x ω + Y x ω)) ^ 2) P ∧
    ∫ ω, (logLen ξ (fun x => V x ω + Y' x ω) - logLen ξ (fun x => V x ω + Y x ω)) ^ 2 ∂P ≤
      2 * (ξ ^ 2 * s) := by
  have hYf : Measurable fun ω x => Y x ω := measurable_pi_iff.2 hYm
  have hY'f : Measurable fun ω x => Y' x ω := measurable_pi_iff.2 hY'm
  have hVf : Measurable fun ω x => V x ω := measurable_pi_iff.2 hVm
  set g : ℕ → (ℂ → ℝ) → (ℂ → ℝ) → ℝ := fun k a b =>
    discLogLen ξ k (gridRestr k b + gridRestr k a)
  -- the discretized bound
  have hk : ∀ k, ∫⁻ ω, ENNReal.ofReal ((g k (fun x => Y' x ω) (fun x => V x ω) -
      g k (fun x => Y x ω) (fun x => V x ω)) ^ 2) ∂P ≤ ENNReal.ofReal (2 * (ξ ^ 2 * s)) := by
    intro k
    have hr := measurable_gridRestr k
    have hgc : Continuous (Function.uncurry fun (a b : grid k → ℝ) => discLogLen ξ k (b + a)) :=
      (lipschitzWith_discLogLen ξ k).continuous.comp
        (by fun_prop : Continuous fun p : (grid k → ℝ) × (grid k → ℝ) => p.2 + p.1)
    have hg : ∀ b : grid k → ℝ, LipschitzWith ‖ξ‖₊ fun a => discLogLen ξ k (b + a) := by
      intro b
      have h := (lipschitzWith_discLogLen ξ k).comp
        (LipschitzWith.of_dist_le_mul (f := fun a : grid k → ℝ => b + a) fun a a' => by
          rw [dist_add_left, NNReal.coe_one, one_mul])
      rw [mul_one] at h
      exact h
    have h := lintegral_sq_sub_copy_le (A := fun ω => gridRestr k fun x => Y x ω)
      (A' := fun ω => gridRestr k fun x => Y' x ω) (B := fun ω => gridRestr k fun x => V x ω)
      (hY.hasGaussianLaw (grid k)) (fun c => h0 c) hs (fun c => hvar c (grid_subset c.2))
      (hr.comp hYf) (hr.comp hY'f) (hr.comp hVf) (hid.comp hr) (hind1.comp hr hr)
      (hind2.comp (hr.prodMap hr) hr) hgc hg
    rwa [coe_nnnorm, Real.norm_eq_abs, sq_abs] at h
  -- pass to the limit
  set D : Ω → ℝ := fun ω => (logLen ξ (fun x => V x ω + Y' x ω) -
    logLen ξ (fun x => V x ω + Y x ω)) ^ 2
  have hconv : ∀ ω, Tendsto (fun k => ENNReal.ofReal ((g k (fun x => Y' x ω) (fun x => V x ω) -
      g k (fun x => Y x ω) (fun x => V x ω)) ^ 2)) atTop (𝓝 (ENNReal.ofReal (D ω))) := fun ω =>
    ENNReal.tendsto_ofReal (((tendsto_disc_add (hVc ω) (hY'c ω)).sub
      (tendsto_disc_add (hVc ω) (hYc ω))).pow 2)
  have hmk : ∀ k, Measurable fun ω => ENNReal.ofReal ((g k (fun x => Y' x ω) (fun x => V x ω) -
      g k (fun x => Y x ω) (fun x => V x ω)) ^ 2) := by
    intro k
    have hr := measurable_gridRestr k
    have hc := (lipschitzWith_discLogLen ξ k).continuous.measurable
    exact ((((hc.comp ((hr.comp hVf).add (hr.comp hY'f))).sub
      (hc.comp ((hr.comp hVf).add (hr.comp hYf)))).pow_const 2)).ennreal_ofReal
  have hfat := lintegral_liminf_le' (μ := P) (u := atTop) (fun k => (hmk k).aemeasurable)
  simp_rw [fun ω => (hconv ω).liminf_eq] at hfat
  have hle : ∫⁻ ω, ENNReal.ofReal (D ω) ∂P ≤ ENNReal.ofReal (2 * (ξ ^ 2 * s)) :=
    hfat.trans (liminf_le_of_frequently_le' (Frequently.of_forall hk))
  have hL : ∀ (Z : ℂ → Ω → ℝ), (∀ ω, Continuous fun x => Z x ω) → (∀ x, Measurable (Z x)) →
      Measurable fun ω => logLen ξ (fun x => V x ω + Z x ω) := fun Z hZc hZm =>
    (measurable_lenObs (Y := fun x ω => V x ω + Z x ω) (fun ω => (hVc ω).add (hZc ω))
      (fun x => (hVm x).add (hZm x)) (rectAB 1 1)).log
  have hDm : Measurable D := ((hL Y' hY'c hY'm).sub (hL Y hYc hYm)).pow_const 2
  have hint : Integrable D P :=
    (lintegral_ofReal_ne_top_iff_integrable hDm.aestronglyMeasurable
      (ae_of_all _ fun ω => sq_nonneg _)).1 (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle)
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun ω => sq_nonneg _)
    hDm.aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hle

end L23
end DDDF
end LQGMetric
