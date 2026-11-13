/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMCFacts.ReplacedDefs at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.Lateral
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.RadialProcess
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeMeas2

/-!
# The whole-plane GFF with replaced radial part: definitions and pairings

For a whole-plane GFF `X` and a continuous path `w : ℝ → ℝ`, the field

  `X̃ = lateral(X) + w(−log|·|)` (`replField X W ω = lateralPartC (X ω) + ofFunC (radialW (W ω))`)

has the lateral part of `X` and radial part `w` (the cone-to-whole-plane comparison; DMS §4.1, Def 4.10). This file
proves the deterministic and almost-sure pairing identities used in `Replaced.lean`:

* `replField_apply`, `ae_replField_apply`: `⟨X̃, φ⟩ = ⟨X, φ − φ̄⟩ + ⟨w(−log|·|), φ̄⟩` a.s. (`Lateral.lean`);
* `pairW_symmTest`: `⟨w(−log|·|), φ⟩ = ⟨w(−log|·|), φ̄⟩` for every `w` (the function is radial);
* `ae_pairW_radialProcess`: for the radial process `ρ` of `X` (`exists_radialProcess`) and `∫ φ = 0`,
  a.s. `⟨ρ(−log|·|), φ̄⟩ = ⟨X, φ̄⟩`;
* measurability of all pairings (`measurable_pairW`, `measurable_lateralPartC_apply`, `measurable_replField`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.GMCFacts

open LQGMetric LQGMetric.CircleAvg MatedCRTHarmonic.MoTPort

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The radial function `z ↦ w(−log|z|)` of a path `w`. -/
def radialW (w : C(ℝ, ℝ)) (z : ℂ) : ℝ := w (-Real.log ‖z‖)

/-- The pairing `⟨w(−log|·|), φ⟩` (junk `0` if `w(−log|·|)` is not locally integrable). -/
def pairW (φ : TestC) (w : C(ℝ, ℝ)) : ℝ := ofFunC (radialW w) φ

/-- **The field with replaced radial part**: `lateral(X) + w(−log|·|)`. -/
def replField (X : Ω → DistC) (W : Ω → C(ℝ, ℝ)) (ω : Ω) : DistC :=
  lateralPartC (X ω) + ofFunC (radialW (W ω))

omit [MeasurableSpace Ω] in
lemma replField_apply (X : Ω → DistC) (W : Ω → C(ℝ, ℝ)) (ω : Ω) (φ : TestC) :
    replField X W ω φ = lateralPartC (X ω) φ + pairW φ (W ω) := rfl

lemma isRotInv_radialW (w : C(ℝ, ℝ)) : IsRotInv (radialW w) := by
  intro α z
  simp only [radialW, norm_mul, norm_exp_ofReal_mul_I', one_mul]

/-- The pairing with a radial function only sees the rotation average of the test function. -/
lemma pairW_symmTest (φ : TestC) (w : C(ℝ, ℝ)) : pairW (symmTest φ) w = pairW φ w := by
  classical
  simp only [pairW, ofFunC, Distribution.ofFun_apply_eq_ite]
  split_ifs with h
  · simp only [smul_eq_mul]
    simp only [TopologicalSpace.Opens.coe_top, locallyIntegrableOn_univ] at h
    exact integral_symmTest_mul φ (isRotInv_radialW w) h
  · rfl

/-! ### Measurability -/

/-- The Borel σ-algebra of `C(ℝ, ℝ)` is the trace of the product σ-algebra. -/
lemma continuousMap_measurableSpace_eq :
    (inferInstance : MeasurableSpace C(ℝ, ℝ)) =
      MeasurableSpace.comap (fun f : C(ℝ, ℝ) => (⇑f : ℝ → ℝ)) MeasurableSpace.pi := by
  rw [ContinuousMap.measurableSpace_eq_iSup_comap_eval, MeasurableSpace.pi,
    MeasurableSpace.comap_iSup]
  simp_rw [MeasurableSpace.comap_comp]
  rfl

/-- Joint measurability of `(w, z) ↦ w(−log|z|)`. -/
lemma measurable_radialW_uncurry :
    Measurable fun p : C(ℝ, ℝ) × ℂ => radialW p.1 p.2 := by
  have h : Continuous fun p : C(ℝ, ℝ) × ℝ => p.1 p.2 := continuous_eval
  exact h.measurable.comp (measurable_fst.prodMk
    ((Real.measurable_log.comp (measurable_norm.comp measurable_snd)).neg))

lemma measurable_pairW (φ : TestC) : Measurable (pairW φ) :=
  ConeMeas2.measurable_ofFunC_apply (F := radialW) measurable_radialW_uncurry φ

/-- Joint measurability of `(h, z) ↦ h_{|z|}(0)`. -/
lemma measurable_radialFun_uncurry : Measurable fun p : DistC × ℂ => radialFun p.1 p.2 :=
  measurable_circleAvg.comp (f := fun p : DistC × ℂ => (p.1, ‖p.2‖, (0 : ℂ)))
    (measurable_fst.prodMk ((measurable_norm.comp measurable_snd).prodMk measurable_const))

lemma measurable_lateralPartC_apply (φ : TestC) : Measurable fun h : DistC => lateralPartC h φ :=
  (GFFInv.measurable_pair φ).sub
    (ConeMeas2.measurable_ofFunC_apply (F := radialFun) measurable_radialFun_uncurry φ)

lemma measurable_replField {X : Ω → DistC} {W : Ω → C(ℝ, ℝ)} (hX : Measurable X)
    (hW : Measurable W) : Measurable (replField X W) := by
  exact GFFInv.measurable_distC_iff.2 fun φ =>
    ((measurable_lateralPartC_apply φ).comp hX).add ((measurable_pairW φ).comp hW)

/-! ### Almost-sure pairing identities -/

variable {X : Ω → DistC}

/-- **The pairings of the replaced field**: a.s. `⟨X̃, φ⟩ = ⟨X, φ − φ̄⟩ + ⟨w(−log|·|), φ̄⟩`. -/
theorem ae_replField_apply (hX : IsWholePlaneGFF X P) (W : Ω → C(ℝ, ℝ)) (φ : TestC) :
    ∀ᵐ ω ∂P, replField X W ω φ = X ω (φ - symmTest φ) + pairW (symmTest φ) (W ω) := by
  filter_upwards [ae_lateralPartC_apply hX φ] with ω hω
  rw [replField_apply, hω, pairW_symmTest]

/-- **The radial process reproduces the radial pairings of `X`**: for the radial process `ρ` of `X` and a mean-zero
test function `φ`, a.s. `⟨ρ(−log|·|), φ̄⟩ = ⟨X, φ̄⟩`. -/
theorem ae_pairW_radialProcess (hX : IsWholePlaneGFF X P) {ρ : Ω → C(ℝ, ℝ)} (hρm : Measurable ρ)
    (hρ : ∀ t, (fun ω => ρ ω t) =ᵐ[P]
      fun ω => circleAvg (X ω) (Real.exp (-t)) 0 - circleAvg (X ω) 1 0)
    {φ : TestC} (hφ : ∫ x, φ x = 0) :
    ∀ᵐ ω ∂P, pairW (symmTest φ) (ρ ω) = X ω (symmTest φ) := by
  have := hX.gaussian.isProbabilityMeasure
  -- `ρ(−log|z|) = X_{|z|}(0) − X_1(0)` for a.e. `z`, a.s.
  have hS : MeasurableSet {p : Ω × ℂ |
      radialW (ρ p.1) p.2 = radialFun (X p.1) p.2 - circleAvg (X p.1) 1 0} := by
    refine measurableSet_eq_fun (measurable_radialW_uncurry.comp
      ((hρm.comp measurable_fst).prodMk measurable_snd)) ?_
    exact (measurable_radialFun_uncurry.comp ((hX.measurable.comp measurable_fst).prodMk
      measurable_snd)).sub ((measurable_circleAvg_left 1 0).comp (hX.measurable.comp measurable_fst))
  have hne : ∀ᵐ z ∂(volume : Measure ℂ), z ≠ 0 := compl_mem_ae_iff.2 (measure_singleton 0)
  have hjoint : ∀ᵐ ω ∂P, ∀ᵐ z ∂(volume : Measure ℂ),
      radialW (ρ ω) z = radialFun (X ω) z - circleAvg (X ω) 1 0 := by
    rw [Measure.ae_ae_comm hS]
    filter_upwards [hne] with z hz
    filter_upwards [hρ (-Real.log ‖z‖)] with ω hω
    simp only [radialW, hω, neg_neg, Real.exp_log (norm_pos_iff.2 hz)]
    rfl
  filter_upwards [hjoint, ConeArea4.ae_radial_R2 hX,
    ConeArea7.ae_lateralPartC_radial hX (isRadialTest_symmTest φ)] with ω hω h3 h0
  obtain ⟨R, -, -, hRe, hRl⟩ := h3
  have hloc : LocallyIntegrable (radialFun (X ω)) volume := hRl.congr hRe.symm
  set c := circleAvg (X ω) 1 0
  have hs0 : ∫ x, symmTest φ x = 0 := by rw [integral_symmTest, hφ]
  have e1 : pairW (symmTest φ) (ρ ω) = ofFunC (radialFun (X ω)) (symmTest φ) +
      ofFunC (fun _ => -c) (symmTest φ) := by
    rw [pairW, ConeArea3.ofFunC_congr_ae hω]
    have e : (fun z => radialFun (X ω) z - c) = radialFun (X ω) + fun _ => -c := by
      funext z; simp [sub_eq_add_neg]
    rw [e, ofFunC, Distribution.ofFun_add (by simpa using hloc.locallyIntegrableOn univ)
      (by simpa using (locallyIntegrable_const (-c)).locallyIntegrableOn univ)]
    rfl
  have e2 : ofFunC (fun _ => -c) (symmTest φ) = 0 := by
    rw [ofFunC, Distribution.ofFun_apply (by simpa using (locallyIntegrable_const (-c)).locallyIntegrableOn univ)]
    simp only [smul_eq_mul]
    rw [integral_mul_const, hs0, zero_mul]
  have e3 : X ω (symmTest φ) = lateralPartC (X ω) (symmTest φ) + ofFunC (radialFun (X ω)) (symmTest φ) := by
    simp [lateralPartC]
  rw [e1, e2, e3, h0, zero_add, add_zero]

end MatedCRTHarmonic.GMCFacts
