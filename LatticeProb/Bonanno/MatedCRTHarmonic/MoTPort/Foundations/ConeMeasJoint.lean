/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTPort.Foundations.ConeMeasJoint at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.Cone
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.Measurability
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.GoodSample
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg
import LatticeProb.Bonanno.LQGMetric.Field.GFFInvariance

/-!
# C.meas (part 2): joint measurability of rotation and dilation; `surfMapC` is a.e.-measurable

* `measurable_rotateField_joint`: `(θ, h) ↦ rotateField θ h` is measurable on `ℝ × Field`;
* `measurable_affineComp_joint`: `(s, h) ↦ affineComp s 0 h` is measurable on `ℝ × Field`;
* `aemeasurable_canonicalC`, `aemeasurable_surfMapC`: for an a.e.-measurable random field `Y`
  whose whole-plane area approximations a.s. have a vague limit (node C.area-exist for `Y`), the
  canonical representative and the law map of `surfLawC` are a.e.-measurable;
* `coneRefMeas_of`: node C.meas (`ConeRefMeas`, Cone.lean) follows from a.e.-measurability of the
  cone field and C.area-exist for it.

Proofs: Carathéodory (mathlib `measurable_uncurry_of_continuous_of_measurable`) with the
continuity of the test-function families `θ ↦ φ(e^{-iθ}·)` and `u ↦ φ(e^{-u}·)` into `𝓓(ℂ)`,
obtained exactly as LQGMetric's `continuous_bumpTest` (LQGMetric/Field/MeasurableAvg.lean) from
`LQGMetric.continuous_testFamK`; `continuous_iteratedFDeriv_snd_real` is a copy of LQGMetric's
`continuous_iteratedFDeriv_snd` (LQGMetric/Field/Measurable.lean) with a real parameter. Negative
dilations are reduced to positive ones through `φ ↦ φ(−·)`. Own bookkeeping only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric TopologicalSpace
open scoped NNReal ENNReal Topology

namespace MatedCRTHarmonic.MoTPort

open QuantumZipper LQGMetric FieldOps

namespace ConeMeas

/-- copy of LQGMetric `continuous_iteratedFDeriv_snd` with a real parameter -/
theorem continuous_iteratedFDeriv_snd_real {Ψ : ℝ → ℂ → ℝ}
    (hΨ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry Ψ)) (i : ℕ) :
    Continuous fun p : ℝ × ℂ => iteratedFDeriv ℝ i (Ψ p.1) p.2 := by
  let ι : ℂ →L[ℝ] ℝ × ℂ := ContinuousLinearMap.inr ℝ ℝ ℂ
  have key : ∀ p : ℝ × ℂ, iteratedFDeriv ℝ i (Ψ p.1) p.2 =
      (iteratedFDeriv ℝ i (Function.uncurry Ψ) p).compContinuousLinearMap fun _ => ι := by
    intro p
    have h1 : Ψ p.1 = (fun w => Function.uncurry Ψ (w + (p.1, 0))) ∘ ι := by
      funext y; simp [ι]
    have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun w => Function.uncurry Ψ (w + (p.1, 0)) :=
      hΨ.comp (contDiff_id.add contDiff_const)
    rw [h1, ι.iteratedFDeriv_comp_right hg _ (by exact_mod_cast le_top),
      iteratedFDeriv_comp_add_right]
    congr 2
    simp [ι]
  simp_rw [key]
  let L := ContinuousMultilinearMap.compContinuousLinearMapL (𝕜 := ℝ)
    (E := fun _ : Fin i => ℂ) (E₁ := fun _ : Fin i => ℝ × ℂ) (F := ℝ) (fun _ => ι)
  exact L.continuous.comp (hΨ.continuous_iteratedFDeriv (by exact_mod_cast le_top))

/-- the pairing with a continuous family of test functions is jointly measurable (Carathéodory) -/
theorem measurable_apply_family {ψ : ℝ → TestC} (hψ : Continuous ψ) :
    Measurable fun p : ℝ × Field => p.2 (ψ p.1) :=
  measurable_uncurry_of_continuous_of_measurable (u := fun (x : ℝ) (h : Field) => h (ψ x))
    (fun h => (map_continuous h).comp hψ) (fun x => measurable_distOn_apply _)

/-- **`u ↦ φ(e^{-u} ·)` is continuous into `𝓓(ℂ)`** (dilation by `e^u`) -/
theorem continuous_dilTest (φ : TestC) :
    Continuous fun u : ℝ => testAffinePull (Real.exp u) 0 φ := by
  obtain ⟨R, hR⟩ := φ.hasCompactSupport.isCompact.isBounded.subset_closedBall (0 : ℂ)
  let Ψ' : ℝ → ℂ → ℝ := fun u y => φ (Complex.ofRealCLM (Real.exp (-u)) * y)
  have hΨ' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry Ψ') := by
    show ContDiff ℝ _ fun p : ℝ × ℂ => φ (Complex.ofRealCLM (Real.exp (-p.1)) * p.2)
    exact φ.contDiff.comp ((Complex.ofRealCLM.contDiff.comp
      (Real.contDiff_exp.comp contDiff_fst.neg)).mul contDiff_snd)
  have hval : ∀ u y, testAffinePull (Real.exp u) 0 φ y = Ψ' u y := by
    intro u y
    rw [testAffinePull_apply _ _ (Real.exp_pos u).ne']
    show φ ((y - 0) / (Real.exp u : ℂ)) = φ (Complex.ofRealCLM (Real.exp (-u)) * y)
    rw [Complex.ofRealCLM_apply, Real.exp_neg, Complex.ofReal_inv, sub_zero, div_eq_inv_mul]
  rw [continuous_iff_continuousAt]
  intro u₀
  let S := closedBall u₀ 1
  have : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let K : Compacts ℂ := ⟨closedBall 0 (Real.exp (u₀ + 1) * |R|), isCompact_closedBall _ _⟩
  let Ψ : S → ℂ → ℝ := fun u y => Ψ' u.1 y
  have hs : ∀ u : S, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Ψ u) := fun u =>
    hΨ'.comp (contDiff_const.prodMk contDiff_id)
  have hK : ∀ u : S, ∀ y ∉ (K : Set ℂ), Ψ u y = 0 := by
    intro u y hy
    refine image_eq_zero_of_notMem_tsupport (f := φ) fun h => hy ?_
    have h1 := hR h
    rw [mem_closedBall, dist_zero_right, norm_mul, Complex.ofRealCLM_apply, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at h1
    have hu : u.1 ≤ u₀ + 1 := by
      have := u.2
      rw [mem_closedBall, Real.dist_eq] at this
      linarith [le_abs_self (u.1 - u₀)]
    show y ∈ closedBall (0 : ℂ) (Real.exp (u₀ + 1) * |R|)
    rw [mem_closedBall, dist_zero_right]
    have h2 : ‖y‖ ≤ Real.exp u.1 * R := by
      have hpos := Real.exp_pos u.1
      rw [Real.exp_neg] at h1
      rw [inv_mul_le_iff₀ hpos] at h1
      linarith
    calc ‖y‖ ≤ Real.exp u.1 * R := h2
      _ ≤ Real.exp u.1 * |R| := mul_le_mul_of_nonneg_left (le_abs_self R) (Real.exp_pos _).le
      _ ≤ Real.exp (u₀ + 1) * |R| :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hu) (abs_nonneg R)
  have hD : ∀ i : ℕ, Continuous fun p : S × ℂ => iteratedFDeriv ℝ i (Ψ p.1) p.2 := fun i =>
    (continuous_iteratedFDeriv_snd_real hΨ' i).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  have hc := continuous_testFamK K Ψ hs hK hD
  have e : (fun u : S => testAffinePull (Real.exp u.1) 0 φ) = ofSuppC K ∘ testFamK K Ψ hs hK := by
    funext u
    ext y
    exact hval u.1 y
  have h2 : Continuous fun u : S => testAffinePull (Real.exp u.1) 0 φ := by
    rw [e]; exact (ofSuppC K).continuous.comp hc
  exact (continuousOn_iff_continuous_domRestrict.2 h2).continuousAt
    (closedBall_mem_nhds _ one_pos)

/-- `φ(−·)` -/
def negTest (φ : TestC) : TestC := testPullCLE (ContinuousLinearEquiv.neg ℝ) φ

/-- **dilation is jointly measurable**: `(s, h) ↦ affineComp s 0 h` -/
theorem measurable_affineComp_joint : Measurable fun p : ℝ × Field => LQGMetric.affineComp p.1 0 p.2 := by
  refine measurable_distOn_iff.2 fun φ => ?_
  show Measurable fun p : ℝ × Field => (p.1 ^ 2)⁻¹ * p.2 (testAffinePull p.1 0 φ)
  refine (measurable_fst.pow_const 2).inv.mul ?_
  have hpos := (measurable_apply_family (continuous_dilTest φ)).comp
    (Real.measurable_log.comp measurable_fst |>.prodMk measurable_snd)
  have hneg := (measurable_apply_family (continuous_dilTest (negTest φ))).comp
    ((Real.measurable_log.comp measurable_fst.neg).prodMk measurable_snd)
  have e : (fun p : ℝ × Field => p.2 (testAffinePull p.1 0 φ)) = fun p =>
      if 0 < p.1 then p.2 (testAffinePull (Real.exp (Real.log p.1)) 0 φ)
      else if p.1 < 0 then p.2 (testAffinePull (Real.exp (Real.log (-p.1))) 0 (negTest φ))
      else 0 := by
    funext p
    by_cases h1 : 0 < p.1
    · rw [if_pos h1, Real.exp_log h1]
    · rw [if_neg h1]
      by_cases h2 : p.1 < 0
      · rw [if_pos h2, Real.exp_log (neg_pos.2 h2)]
        congr 1
        ext x
        rw [testAffinePull_apply _ _ h2.ne, testAffinePull_apply _ _ (neg_pos.2 h2).ne']
        simp only [negTest, testPullCLE_apply, ContinuousLinearEquiv.coe_neg, sub_zero]
        congr 1
        simp [div_neg]
      · rw [if_neg h2]
        have h0 : p.1 = 0 := by linarith [not_lt.1 h1, not_lt.1 h2]
        rw [h0]
        simp [testAffinePull]
  rw [e]
  exact Measurable.ite (measurableSet_lt measurable_const measurable_fst) hpos
    (Measurable.ite (measurableSet_lt measurable_fst measurable_const) hneg measurable_const)

variable {γ : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

end ConeMeas

end MatedCRTHarmonic.MoTPort
