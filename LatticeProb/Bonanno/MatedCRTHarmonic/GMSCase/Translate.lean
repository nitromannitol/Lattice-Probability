/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSCase.Translate at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCase.JointLawR
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCase.Gaussian
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSCase.ConeLaw

/-!
# Translation invariance of the normalized whole-plane GFF inside the unit disk

Source: (`[18]:N`), Proposition 4.10, Cases 3–4,
`[18]`, and the repair of the Case 3 random-mesh gap .

A whole-plane GFF normalized by `h_1(0) = 0` has covariance `−log|x − y|` for `x, y ∈ 𝔻`, which is
translation invariant there. Hence for every root `z` with `‖z‖ + r ≤ 1` the translated field
`h(· + z)` restricted to `B_r(0)` has the law of `h|_{B_r(0)}`: no renormalization of the additive
constant and no rescaling are needed, so [18]'s detour through `h³ = h² − h²_{1/2}(z)` and the
dilation `h⁴ = h³(·/2 + z)` (which changes the mesh by the random factor `e^{γ h²_{1/2}(z)}`) can be
avoided altogether.

Proof in Lean, through the radius-`r` decomposition: the pair `(h_r(z), (h(r · + z) − h_r(z))|_𝔻)`
has the law `N(0, log(1/r)) ⊗ law(h|_𝔻)` for every such `z` (exact Lemma A.2 independence
`GMSAppA.lemmaA2_indepFun`, the Gaussian computation `map_radAvg_normalized` and the affine
invariance `map_caseNormalized`), and `h(· + z)|_{B_r(0)}` is a fixed measurable function
`transRecon` of that pair; compare with `z = 0`.

* `resSub`, `restrictTo_eq_resSub`: restriction from `W` to an open `V ⊆ W`;
* `dilLocal`, `restrictTo_eq_dilLocal`: the local dilation `DistOn 𝔻 → DistOn B_r(0)`;
* `transRecon`, `restrictTo_affineComp_one_eq`: the reconstruction of `h(· + z)|_{B_r(0)}`;
* `indepFun_radAvg_caseLocal'`, `map_radAvg_caseLocal`: the law of the radius-`r` decomposition;
* **`map_restrict_affineComp_one`** (translation invariance inside `𝔻`),
  `map_restrict_affineComp_one_pair` (jointly with a law-preserving transform of an independent
  observation), `map_restrict_affineComp_one_marked` (independent random root).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric TopologicalSpace Filter
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSCase

open LQGMetric LQGMetric.Blueprint

/-! ## Restriction to a smaller open set -/

/-- Restriction of distributions from `W` to an open `V` (meaningful for `V ⊆ W`). -/
def resSub (V W : Opens ℂ) : DistOn W → DistOn V :=
  fun T => T.comp (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := V) (Ω₂ := W))

theorem measurable_resSub (V W : Opens ℂ) : Measurable (resSub V W) := by
  refine measurable_distOn_iff.2 fun ψ => ?_
  exact measurable_distOn_apply _

theorem restrictTo_eq_resSub {V W : Opens ℂ} (hVW : V ≤ W) (g : DistC) :
    restrictTo V g = resSub V W (restrictTo W g) := by
  refine DFunLike.ext _ _ fun ψ => ?_
  show g (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := V) (Ω₂ := ⊤) ψ) =
    g (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := W) (Ω₂ := ⊤)
      (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := V) (Ω₂ := W) ψ))
  congr 1
  ext x
  simp [TestFunction.monoCLM_apply, hVW]

theorem ballO_le_ballO {r s : ℝ} (hrs : r ≤ s) (z : ℂ) : ballO z r ≤ ballO z s := by
  intro w hw
  have hw' : w ∈ ball z r := hw
  show w ∈ ball z s
  exact ball_subset_ball hrs hw'

/-! ## The local dilation -/

theorem mem_ballO_one_iff_smul {r : ℝ} (hr : 0 < r) (y : ℂ) :
    y ∈ ballO (0 : ℂ) 1 ↔ r • y + 0 ∈ ballO (0 : ℂ) r := by
  simp only [ballO, Opens.mem_mk, Metric.mem_ball, dist_zero_right, add_zero, norm_smul,
    Real.norm_eq_abs, abs_of_pos hr]
  constructor
  · intro h
    calc r * ‖y‖ < r * 1 := mul_lt_mul_of_pos_left h hr
      _ = r := mul_one r
  · intro h
    by_contra hc
    have hc' : 1 ≤ ‖y‖ := not_lt.mp hc
    have := mul_le_mul_of_nonneg_left hc' hr.le
    linarith

/-- The local dilation `T ↦ r² · T(ψ(r ·))`, `DistOn 𝔻 → DistOn B_r(0)`. -/
def dilLocal {r : ℝ} (hr : 0 < r) : DistOn (ballO (0 : ℂ) 1) → DistOn (ballO (0 : ℂ) r) :=
  fun T => (r ^ 2) • T.comp (GM.testScalePush hr.ne' (mem_ballO_one_iff_smul hr))

theorem measurable_dilLocal {r : ℝ} (hr : 0 < r) : Measurable (dilLocal hr) := by
  refine measurable_distOn_iff.2 fun ψ => ?_
  show Measurable fun T : DistOn (ballO (0 : ℂ) 1) =>
    r ^ 2 * T (GM.testScalePush hr.ne' (mem_ballO_one_iff_smul hr) ψ)
  exact (measurable_distOn_apply _).const_mul _

/-- `g|_{B_r(0)}` is the local dilation of `g(r ·)|_𝔻`. -/
theorem restrictTo_eq_dilLocal {r : ℝ} (hr : 0 < r) (g : DistC) :
    restrictTo (ballO (0 : ℂ) r) g =
      dilLocal hr (restrictTo (ballO (0 : ℂ) 1) (affineComp r 0 g)) := by
  refine DFunLike.ext _ _ fun ψ => ?_
  rw [GM.restrictTo_apply_eq_scale hr (mem_ballO_one_iff_smul hr)]
  rfl

/-! ## Reconstruction of the translated field -/

/-- The constant `1` restricted to the unit disk. -/
def oneOn : DistOn (ballO (0 : ℂ) 1) := restrictTo (ballO (0 : ℂ) 1) (addConst 0 1)

theorem restrictTo_addConst_one (g : DistC) (c : ℝ) :
    restrictTo (ballO (0 : ℂ) 1) (addConst g c) = restrictTo (ballO (0 : ℂ) 1) g + c • oneOn := by
  refine DFunLike.ext _ _ fun ψ => ?_
  set φ : TestC := TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := ballO (0 : ℂ) 1)
    (Ω₂ := ⊤) ψ with hφ
  show addConst g c φ = g φ + c * addConst 0 1 φ
  rw [GFFInv.addConst_apply, GFFInv.addConst_apply]
  simp only [zero_apply, zero_add, mul_one]
  ring

/-- The reconstruction `(a, T) ↦ (T + a)(·/r)` on `B_r(0)`. -/
def transRecon {r : ℝ} (hr : 0 < r) (p : ℝ × DistOn (ballO (0 : ℂ) 1)) :
    DistOn (ballO (0 : ℂ) r) :=
  dilLocal hr (p.2 + p.1 • oneOn)

theorem measurable_transRecon {r : ℝ} (hr : 0 < r) : Measurable (transRecon hr) := by
  have h1 : Measurable fun p : ℝ × DistOn (ballO (0 : ℂ) 1) => p.2 + p.1 • oneOn := by
    refine measurable_distOn_iff.2 fun ψ => ?_
    show Measurable fun p : ℝ × DistOn (ballO (0 : ℂ) 1) => p.2 ψ + p.1 * oneOn ψ
    exact ((measurable_distOn_apply ψ).comp measurable_snd).add (measurable_fst.mul_const _)
  exact (measurable_dilLocal hr).comp h1

/-- **`g(· + z)|_{B_r(0)}` from the radius-`r` decomposition at `z`.** -/
theorem restrictTo_affineComp_one_eq {r : ℝ} (hr : 0 < r) (z : ℂ) (g : DistC) :
    restrictTo (ballO (0 : ℂ) r) (affineComp 1 z g) =
      transRecon hr (radAvg r g z, restrictTo (ballO (0 : ℂ) 1) (caseNormalized r g z)) := by
  rw [restrictTo_eq_dilLocal hr]
  have e1 : affineComp r 0 (affineComp 1 z g) = affineComp r z g := by
    rw [GM.affineComp_comp hr.ne' one_ne_zero 0 z g]
    simp
  have e2 : affineComp r z g = addConst (caseNormalized r g z) (radAvg r g z) := by
    rw [caseNormalized, GFFLaw.addConst_addConst, show radAvg r g z = circleAvg g r z from rfl,
      neg_add_cancel, GFFLaw.addConst_zero']
  rw [e1, e2, restrictTo_addConst_one]
  rfl

/-! ## The law of the radius-`r` decomposition -/

section Law

variable {Ω 𝒴 : Type*} [MeasurableSpace Ω] [MeasurableSpace 𝒴] {P : Measure Ω}
  {h : Ω → DistC} {Y : Ω → 𝒴} {τ : ℂ → 𝒴 → 𝒴}

theorem closedBall_subset_of_norm_add_le {z : ℂ} {r : ℝ} (hz : ‖z‖ + r ≤ 1) :
    closedBall z r ⊆ closedBall (0 : ℂ) 1 := by
  intro w hw
  rw [mem_closedBall, dist_eq_norm] at hw
  rw [mem_closedBall, dist_zero_right]
  calc ‖w‖ = ‖(w - z) + z‖ := by rw [sub_add_cancel]
    _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
    _ ≤ 1 := by linarith

/-- Exact Lemma A.2 independence at radius `r`, without an auxiliary observation. -/
theorem indepFun_radAvg_caseLocal' (hh : IsNormalizedWPGFF h P) {r : ℝ} (hr : 0 < r) {z₀ : ℂ}
    (hz : closedBall z₀ r ⊆ closedBall (0 : ℂ) 1) :
    IndepFun (fun ω => radAvg r (h ω) z₀)
      (fun ω => restrictTo (ballO (0 : ℂ) 1) (caseNormalized r (h ω) z₀)) P := by
  set a : DistC → ℝ := fun g => circleAvg g r z₀ with ha_def
  have ham : Measurable a := measurable_circleAvg_left r z₀
  set R : DistC → DistOn (ballO z₀ r) := fun g =>
    restrictTo (ballO z₀ r) (addConst g (-a g)) with hR_def
  have hXY : IndepFun (fun ω => a (h ω)) (fun ω => R (h ω)) P :=
    GMSAppA.lemmaA2_indepFun hh hr hz
  have H2 := hXY.comp measurable_id (measurable_caseLocalPull hr z₀)
  have e1 : (fun ω => radAvg r (h ω) z₀) = (id ∘ fun ω => a (h ω)) := rfl
  have e2 : (fun ω => restrictTo (ballO (0 : ℂ) 1) (caseNormalized r (h ω) z₀)) =
      (caseLocalPull hr z₀ ∘ fun ω => R (h ω)) := by
    funext ω
    simp only [Function.comp_apply, hR_def, ha_def]
    rw [restrictTo_caseNormalized hr]
  rw [e1, e2]
  exact H2

/-- **The law of the radius-`r` decomposition** does not depend on the root `z` with
`‖z‖ + r ≤ 1`: it is `N(0, log(1/r)) ⊗ law(h|_𝔻)`. -/
theorem map_radAvg_caseLocal (hh : IsNormalizedWPGFF h P) {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : ‖z‖ + r ≤ 1) :
    P.map (fun ω => (radAvg r (h ω) z, restrictTo (ballO (0 : ℂ) 1) (caseNormalized r (h ω) z))) =
      (gaussianReal 0 (-Real.log r).toNNReal).prod
        (P.map fun ω => restrictTo (ballO (0 : ℂ) 1) (h ω)) := by
  have := hh.1.gaussian.isProbabilityMeasure
  have hind := indepFun_radAvg_caseLocal' hh hr (closedBall_subset_of_norm_add_le hz)
  have ham : Measurable fun ω => radAvg r (h ω) z :=
    (measurable_circleAvg_left r z).comp hh.1.measurable
  have hFm : Measurable fun g : DistC => restrictTo (ballO (0 : ℂ) 1) (caseNormalized r g z) :=
    (measurable_restrictTo _).comp (measurable_caseNormalized_left r z)
  have hlm : Measurable fun ω => restrictTo (ballO (0 : ℂ) 1) (caseNormalized r (h ω) z) :=
    hFm.comp hh.1.measurable
  rw [hind.map_prod_eq_prod_map_map ham.aemeasurable hlm.aemeasurable,
    map_radAvg_normalized hh hr hz]
  congr 1
  have hcm : Measurable fun ω => caseNormalized r (h ω) z :=
    (measurable_caseNormalized_left r z).comp hh.1.measurable
  have e1 : P.map (fun ω => restrictTo (ballO (0 : ℂ) 1) (caseNormalized r (h ω) z)) =
      (P.map fun ω => caseNormalized r (h ω) z).map (restrictTo (ballO (0 : ℂ) 1)) := by
    rw [Measure.map_map (measurable_restrictTo _) hcm]
    rfl
  rw [e1, map_caseNormalized hh hr z, Measure.map_map (measurable_restrictTo _) hh.1.measurable]
  rfl

/-- `g ↦ g(· + z)|_{B_r(0)}` is measurable. -/
theorem measurable_restrict_affineComp_one (r : ℝ) (z : ℂ) :
    Measurable fun g : DistC => restrictTo (ballO (0 : ℂ) r) (affineComp 1 z g) := by
  have hpair : Measurable fun g : DistC => ((g, z) : DistC × ℂ) :=
    measurable_id.prodMk measurable_const
  have e : Measurable ((fun p : DistC × ℂ => affineComp 1 p.2 p.1) ∘
      (fun g : DistC => ((g, z) : DistC × ℂ))) := (measurable_affineComp_center 1).comp hpair
  exact (measurable_restrictTo _).comp e

/-- **Translation invariance inside the unit disk.** For a whole-plane GFF normalized by
`h_1(0) = 0`, `0 < r` and `‖z‖ + r ≤ 1`, `h(· + z)|_{B_r(0)}` has the law of `h|_{B_r(0)}`. -/
theorem map_restrict_affineComp_one (hh : IsNormalizedWPGFF h P) {r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : ‖z‖ + r ≤ 1) :
    P.map (fun ω => restrictTo (ballO (0 : ℂ) r) (affineComp 1 z (h ω))) =
      P.map (fun ω => restrictTo (ballO (0 : ℂ) r) (h ω)) := by
  have hz0 : ‖(0 : ℂ)‖ + r ≤ 1 := by
    rw [norm_zero, zero_add]
    linarith [norm_nonneg z]
  have hpair : ∀ w : ℂ, Measurable fun ω =>
      (radAvg r (h ω) w, restrictTo (ballO (0 : ℂ) 1) (caseNormalized r (h ω) w)) := fun w =>
    ((measurable_circleAvg_left r w).comp hh.1.measurable).prodMk
      (((measurable_restrictTo _).comp (measurable_caseNormalized_left r w)).comp hh.1.measurable)
  have eL : (fun ω => restrictTo (ballO (0 : ℂ) r) (affineComp 1 z (h ω))) =
      transRecon hr ∘ fun ω =>
        (radAvg r (h ω) z, restrictTo (ballO (0 : ℂ) 1) (caseNormalized r (h ω) z)) :=
    funext fun ω => restrictTo_affineComp_one_eq hr z (h ω)
  have eR : (fun ω => restrictTo (ballO (0 : ℂ) r) (h ω)) =
      transRecon hr ∘ fun ω =>
        (radAvg r (h ω) 0, restrictTo (ballO (0 : ℂ) 1) (caseNormalized r (h ω) 0)) := by
    funext ω
    simp only [Function.comp_apply]
    rw [← restrictTo_affineComp_one_eq hr 0 (h ω), GM.affineComp_one_zero]
  rw [eL, eR, ← Measure.map_map (measurable_transRecon hr) (hpair z),
    ← Measure.map_map (measurable_transRecon hr) (hpair 0), map_radAvg_caseLocal hh hr hz,
    map_radAvg_caseLocal hh hr hz0]

/-- **Translation invariance jointly with an independent observation** transformed by a
law-preserving map. -/
theorem map_restrict_affineComp_one_pair (hh : IsNormalizedWPGFF h P) {r : ℝ} (hr : 0 < r)
    (hY : Measurable Y) (hτ : Measurable fun p : ℂ × 𝒴 => τ p.1 p.2) (hind : IndepFun h Y P)
    {z : ℂ} (hz : ‖z‖ + r ≤ 1) (hlaw : P.map (fun ω => τ z (Y ω)) = P.map Y) :
    P.map (fun ω => (restrictTo (ballO (0 : ℂ) r) (affineComp 1 z (h ω)), τ z (Y ω))) =
      P.map (fun ω => (restrictTo (ballO (0 : ℂ) r) (h ω), Y ω)) := by
  have := hh.1.gaussian.isProbabilityMeasure
  have hF := measurable_restrict_affineComp_one r z
  have hG := measurable_transform_right hτ z
  have hind1 : IndepFun (fun ω => restrictTo (ballO (0 : ℂ) r) (affineComp 1 z (h ω)))
      (fun ω => τ z (Y ω)) P := hind.comp hF hG
  have hind2 : IndepFun (fun ω => restrictTo (ballO (0 : ℂ) r) (h ω)) Y P :=
    hind.comp (measurable_restrictTo _) measurable_id
  have hFm : Measurable fun ω => restrictTo (ballO (0 : ℂ) r) (affineComp 1 z (h ω)) :=
    hF.comp hh.1.measurable
  have hGm : Measurable fun ω => τ z (Y ω) := hG.comp hY
  have hRm : Measurable fun ω => restrictTo (ballO (0 : ℂ) r) (h ω) :=
    (measurable_restrictTo _).comp hh.1.measurable
  rw [hind1.map_prod_eq_prod_map_map hFm.aemeasurable hGm.aemeasurable,
    hind2.map_prod_eq_prod_map_map hRm.aemeasurable hY.aemeasurable,
    map_restrict_affineComp_one hh hr hz, hlaw]

end Law

end MatedCRTHarmonic.GMSCase
