/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S3.DeterministicScale at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.GFFInvariance
import LatticeProb.Bonanno.LQGMetric.Field.Measurable
import LatticeProb.Bonanno.LQGMetric.Blueprint.M2Defs

/-!
# GM Lemma 3.1, ingredient: restrictions of a rescaled field (task P2-M2D)

Decision D15 (`decisions/DEC-A.md` (d), "Verification"): an event determined by
`(h − c)|_{B_R(z)}` is determined by `(h^R − c)|_{B_1(z/R)}` for `h^R := h(R ·)`, so GM Lemma 2.7
(stated for unit balls) applies to the rescaled field.

* `GM.testScalePush r z U V`: `ψ ↦ ψ(r · + z)` from `𝓓(U)` to `𝓓(V)` when
  `V = {y | r y + z ∈ U}`;
* `GM.restrictTo_eq_scale`: `g|_U = r² · (g(r · + z))|_V ∘ testScalePush` (change of variables);
* `GM.fieldSigma_le_affineComp`: `σ(g|_U) ≤ σ(g(r · + z)|_V)`;
* `GM.affineComp_addConst`: `(g + a)(r · + z) = g(r · + z) + a`.

Own elementary arguments (definitions unfolded; no source needed).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped Distributions

namespace LQGMetric.GM

open GFFInv Blueprint

section Push

variable {r : ℝ} {z : ℂ} {U V : Opens ℂ}

lemma affMap_inv_apply (hr : r ≠ 0) (z y : ℂ) :
    affMap r⁻¹ (-(r⁻¹ • z)) y = r • y + z := by
  simp only [affMap, inv_inv, neg_neg, smul_add, smul_smul, mul_inv_cancel₀ hr, one_smul]

lemma affK_inv_subset (hr : r ≠ 0) (hUV : ∀ y : ℂ, y ∈ V ↔ r • y + z ∈ U) {K : Compacts ℂ}
    (hK : (K : Set ℂ) ⊆ U) : (affK r⁻¹ (-(r⁻¹ • z)) K : Set ℂ) ⊆ V := by
  rintro _ ⟨y, hy, rfl⟩
  refine (hUV _).2 ?_
  have : r • (r⁻¹ • y + -(r⁻¹ • z)) + z = y := by
    rw [smul_add, smul_smul, mul_inv_cancel₀ hr, one_smul, smul_neg, smul_smul,
      mul_inv_cancel₀ hr, one_smul]; abel
  rw [this]; exact hK hy

/-- the test function `ψ(r · + z) ∈ 𝓓(V)` for `ψ ∈ 𝓓(U)` -/
def scalePushFun (hr : r ≠ 0) (hUV : ∀ y : ℂ, y ∈ V ↔ r • y + z ∈ U) (ψ : TestOn U) :
    TestOn V :=
  ⟨ψ ∘ affMap r⁻¹ (-(r⁻¹ • z)), contDiff_comp_affMap _ _ ψ.contDiff,
    hasCompactSupport_comp_affMap _ _ (inv_ne_zero hr) ψ.hasCompactSupport, by
      refine (tsupport_comp_subset_preimage _ (by unfold affMap; fun_prop)).trans fun y hy => ?_
      refine (hUV y).2 ?_
      rw [← affMap_inv_apply hr z y]
      exact ψ.tsupport_subset hy⟩

/-- `ψ ↦ ψ(r · + z)` as a continuous linear map `𝓓(U) → 𝓓(V)` -/
def testScalePush (hr : r ≠ 0) (hUV : ∀ y : ℂ, y ∈ V ↔ r • y + z ∈ U) :
    TestOn U →L[ℝ] TestOn V :=
  TestFunction.mkCLM ℝ (scalePushFun hr hUV) (fun _ _ => rfl) (fun _ _ => rfl) (fun K hK => by
    have : scalePushFun hr hUV ∘ TestFunction.ofSupportedIn hK =
        TestFunction.ofSupportedInCLM ℝ (affK_inv_subset hr hUV hK) ∘
          pullK r⁻¹ (-(r⁻¹ • z)) (inv_ne_zero hr) K := by
      funext φ; ext x; rfl
    rw [this]
    exact (TestFunction.ofSupportedInCLM ℝ _).continuous.comp
      (continuous_pullK _ _ (inv_ne_zero hr) K))

lemma testScalePush_apply (hr : r ≠ 0) (hUV : ∀ y : ℂ, y ∈ V ↔ r • y + z ∈ U) (ψ : TestOn U)
    (y : ℂ) : testScalePush hr hUV ψ y = ψ (r • y + z) := by
  show ψ (affMap r⁻¹ (-(r⁻¹ • z)) y) = _
  rw [affMap_inv_apply hr]

/-- the change of variables `g|_U = r² · (g(r · + z))|_V ∘ testScalePush` -/
theorem restrictTo_apply_eq_scale (hr : 0 < r) (hUV : ∀ y : ℂ, y ∈ V ↔ r • y + z ∈ U)
    (g : DistC) (ψ : TestOn U) :
    restrictTo U g ψ = r ^ 2 * restrictTo V (affineComp r z g) (testScalePush hr.ne' hUV ψ) := by
  have key : testAffinePull r z (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := V) (Ω₂ := ⊤)
      (testScalePush hr.ne' hUV ψ)) =
      TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := U) (Ω₂ := ⊤) ψ := by
    ext x
    rw [testAffinePull_apply r z hr.ne', TestFunction.monoCLM_apply, TestFunction.monoCLM_apply]
    simp only [le_refl, le_top, and_self, ite_true]
    rw [testScalePush_apply]
    congr 1
    rw [Complex.real_smul, mul_div_cancel₀ _ (by exact_mod_cast hr.ne'), sub_add_cancel]
  show g (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := U) (Ω₂ := ⊤) ψ) =
    r ^ 2 * affineComp r z g (TestFunction.monoCLM ℝ (n₁ := ⊤) (n₂ := ⊤) (Ω₁ := V) (Ω₂ := ⊤)
      (testScalePush hr.ne' hUV ψ))
  rw [affineComp_apply, key]
  field_simp

/-- **`σ(g|_U) ≤ σ(g(r · + z)|_V)`** for `V = {y | r y + z ∈ U}` -/
theorem fieldSigma_le_affineComp {Ω : Type} [MeasurableSpace Ω] (hr : 0 < r)
    (hUV : ∀ y : ℂ, y ∈ V ↔ r • y + z ∈ U) (g : Ω → DistC) :
    fieldSigma g U ≤ fieldSigma (fun ω => affineComp r z (g ω)) V := by
  let Φ : DistOn V → DistOn U := fun T => (r ^ 2) • T.comp (testScalePush hr.ne' hUV)
  have hΦ : Measurable Φ := measurable_distOn_iff.2 fun ψ => by
    show Measurable fun T : DistOn V => r ^ 2 * T (testScalePush hr.ne' hUV ψ)
    exact (measurable_distOn_apply (testScalePush hr.ne' hUV ψ)).const_mul _
  have he : (fun ω => restrictTo U (g ω)) = Φ ∘ fun ω => restrictTo V (affineComp r z (g ω)) := by
    funext ω
    refine DFunLike.ext _ _ fun ψ => ?_
    show restrictTo U (g ω) ψ = r ^ 2 * restrictTo V (affineComp r z (g ω)) _
    exact restrictTo_apply_eq_scale hr hUV (g ω) ψ
  unfold fieldSigma
  rw [he, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hΦ.comap_le

end Push

/-- `(g + a)(r · + z) = g(r · + z) + a` -/
theorem affineComp_addConst {r : ℝ} (hr : 0 < r) (z : ℂ) (g : DistC) (a : ℝ) :
    affineComp r z (addConst g a) = addConst (affineComp r z g) a := by
  refine DFunLike.ext _ _ fun φ => ?_
  rw [affineComp_apply, addConst_apply, addConst_apply, affineComp_apply,
    integral_testAffinePull φ hr z]
  field_simp

/-- the unit ball around `w` corresponds to the ball of radius `R` around `R w` -/
lemma mem_ballO_iff_scale {R : ℝ} (hR : 0 < R) (w y : ℂ) :
    y ∈ ballO w 1 ↔ R • y + 0 ∈ ballO (R • w) R := by
  simp only [ballO, Opens.mem_mk, Metric.mem_ball, add_zero, dist_eq_norm, ← smul_sub,
    norm_smul, Real.norm_eq_abs, abs_of_pos hR]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

end LQGMetric.GM
