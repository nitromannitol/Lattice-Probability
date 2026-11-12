/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.KilledHeatDef at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeat
import LatticeProb.Bonanno.LQGMetric.Statement.Field
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.BMExistence
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Killed heat kernel, part 3: the canonical planar Brownian motion and the definition of `p_A`
(task P2-KILLED, decision D-KHK1, `decisions/DEC-KHK.md`)

The canonical planar Brownian motion `planarBM` lives on `Ω2 = Bool → ℕ → ℝ` with the product
`P2` of two copies of QuantumZipper's `stdP`; its coordinates are two independent copies of QZ's
real Brownian motion (`QuantumZipper.BMExist.exists_isBrownianReal_stdP`). Independence of the
coordinates is mathlib's `iIndepFun_infinitePi`, joint Gaussianity `iIndepFun.hasGaussianLaw`.

Definition (Ding–Zeitouni–Zhang arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 467–469):
`killedHeat A t z w = (2πt)⁻¹ e^{−|z−w|²/(2t)} · P(B_s − (s/t)B_t + z + (s/t)(w − z) ∈ A, s ≤ t)`.

Main results: `IsPlanarBM planarBM P2`; `bridgeStay_eq_of_isPlanarBridge` (any planar bridge on
any probability space gives the same probability); `killedHeat_nonneg`, `killedHeat_le_heatKernel`,
`killedHeat_mono`, `killedHeat_univ`, `killedHeat_symm` (symmetry by time reversal of the bridge,
`IsPlanarBridge.reverse`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal
open LQGDimension.ExistAsm (stdP)

namespace LQGMetric
namespace KilledHeat

/-! ### The canonical planar Brownian motion -/

/-- QuantumZipper's real Brownian motion on `(ℕ → ℝ, stdP)`. -/
def stdBM : ℝ≥0 → (ℕ → ℝ) → ℝ :=
  Classical.choose QuantumZipper.BMExist.exists_isBrownianReal_stdP

lemma isBrownianReal_stdBM : IsBrownianReal stdBM stdP :=
  Classical.choose_spec QuantumZipper.BMExist.exists_isBrownianReal_stdP

/-- A measurable modification of `stdBM s` (used only inside proofs). -/
def stdBMm (s : ℝ≥0) : (ℕ → ℝ) → ℝ := (isBrownianReal_stdBM.aemeasurable s).mk _

lemma measurable_stdBMm (s : ℝ≥0) : Measurable (stdBMm s) := AEMeasurable.measurable_mk _

lemma stdBM_ae_eq (s : ℝ≥0) : stdBM s =ᵐ[stdP] stdBMm s := AEMeasurable.ae_eq_mk _

/-- The sample space of the canonical planar Brownian motion. -/
abbrev Ω2 : Type := Bool → ℕ → ℝ

/-- Two independent copies of `stdP`. -/
def P2 : Measure Ω2 := Measure.infinitePi fun _ : Bool ↦ stdP

instance : IsProbabilityMeasure P2 := by unfold P2; infer_instance

lemma measurePreserving_eval_P2 (b : Bool) : MeasurePreserving (fun ω : Ω2 ↦ ω b) P2 stdP :=
  measurePreserving_eval_infinitePi (fun _ : Bool ↦ stdP) b

/-- The canonical planar Brownian motion `B_s = (stdBM s (ω false), stdBM s (ω true))`. -/
def planarBM (s : ℝ≥0) (ω : Ω2) : ℂ := (stdBM s (ω false) : ℂ) + (stdBM s (ω true) : ℂ) * Complex.I

lemma coordProc_planarBM (p : Bool × ℝ≥0) :
    coordProc planarBM p = fun ω ↦ stdBM p.2 (ω p.1) := by
  ext ω
  rcases p with ⟨b, s⟩
  cases b <;> simp [coordProc, planarBM]

/-- The measurable modification of the coordinate process. -/
def Zm (p : Bool × ℝ≥0) (ω : Ω2) : ℝ := stdBMm p.2 (ω p.1)

lemma coordProc_ae_eq (p : Bool × ℝ≥0) : coordProc planarBM p =ᵐ[P2] Zm p := by
  rw [coordProc_planarBM]
  exact (measurePreserving_eval_P2 p.1).quasiMeasurePreserving.ae_eq_comp (stdBM_ae_eq p.2)

lemma isGaussianProcess_Zm : IsGaussianProcess Zm P2 where
  hasGaussianLaw I := by
    classical
    let J : Finset ℝ≥0 := I.image Prod.snd
    let V : (ℕ → ℝ) → (J → ℝ) := fun x ↦ J.restrict (stdBMm · x)
    have hV : Measurable V := Measurable.of_eval fun j ↦ measurable_stdBMm j
    have hVG : HasGaussianLaw V stdP := by
      refine (isBrownianReal_stdBM.isGaussianProcess.hasGaussianLaw J).congr ?_
      have : ∀ᵐ x ∂stdP, ∀ j : J, stdBM j x = stdBMm j x :=
        ae_all_iff.2 fun j ↦ stdBM_ae_eq j
      filter_upwards [this] with x hx
      funext j
      exact hx j
    have hb : ∀ b : Bool, HasGaussianLaw (fun ω : Ω2 ↦ V (ω b)) P2 := fun b ↦ by
      refine ⟨(hV.comp (measurable_pi_apply b)).aemeasurable, ?_⟩
      have : P2.map (fun ω : Ω2 ↦ V (ω b)) = stdP.map V := by
        rw [← (measurePreserving_eval_P2 b).map_eq, Measure.map_map hV (measurable_pi_apply b)]
        rfl
      rw [this]
      exact hVG.isGaussian_map
    have hind : iIndepFun (fun b (ω : Ω2) ↦ V (ω b)) P2 :=
      iIndepFun_infinitePi (P := fun _ : Bool ↦ stdP) (X := fun _ ↦ V) fun _ ↦ hV
    have hG := iIndepFun.hasGaussianLaw hb hind
    let L : (Bool → J → ℝ) →L[ℝ] (I → ℝ) := ContinuousLinearMap.pi fun i ↦
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : J ↦ ℝ)
        ⟨i.1.2, Finset.mem_image_of_mem _ i.2⟩).comp (ContinuousLinearMap.proj i.1.1)
    have hfun : (fun ω ↦ I.restrict (Zm · ω)) = fun ω ↦ L (fun b ↦ V (ω b)) := by
      funext ω
      funext i
      rfl
    rw [hfun]
    exact hG.map_fun L

lemma integral_comp_eval_P2 (b : Bool) {f : (ℕ → ℝ) → ℝ} (hf : Measurable f) :
    ∫ ω, f (ω b) ∂P2 = ∫ x, f x ∂stdP := by
  rw [← (measurePreserving_eval_P2 b).map_eq, integral_map (measurable_pi_apply b).aemeasurable hf.aestronglyMeasurable]

lemma covariance_Zm (p q : Bool × ℝ≥0) :
    cov[Zm p, Zm q; P2] = if p.1 = q.1 then ((min p.2 q.2 : ℝ≥0) : ℝ) else 0 := by
  rcases p with ⟨b, s⟩
  rcases q with ⟨b', r⟩
  by_cases hb : b = b'
  · subst hb
    simp only [ite_true]
    have h1 : cov[Zm (b, s), Zm (b, r); P2] = cov[stdBMm s, stdBMm r; stdP] := by
      rw [← (measurePreserving_eval_P2 b).map_eq, covariance_map
        (measurable_stdBMm s).aestronglyMeasurable (measurable_stdBMm r).aestronglyMeasurable
        (measurable_pi_apply b).aemeasurable]
      rfl
    have h2 : cov[stdBMm s, stdBMm r; stdP] = cov[stdBM s, stdBM r; stdP] := by
      simp only [covariance]
      rw [integral_congr_ae (stdBM_ae_eq s).symm, integral_congr_ae (stdBM_ae_eq r).symm]
      refine integral_congr_ae ?_
      filter_upwards [stdBM_ae_eq s, stdBM_ae_eq r] with x h1 h2
      simp [h1, h2]
    rw [h1, h2, isBrownianReal_stdBM.covariance_eval]
  · simp only [hb, ite_false]
    have hm1 : MemLp (stdBMm s ∘ fun ω : Ω2 ↦ ω b) 2 P2 :=
      (isGaussianProcess_Zm.hasGaussianLaw_eval (b, s)).memLp_two
    have hm2 : MemLp (stdBMm r ∘ fun ω : Ω2 ↦ ω b') 2 P2 :=
      (isGaussianProcess_Zm.hasGaussianLaw_eval (b', r)).memLp_two
    show cov[stdBMm s ∘ (fun ω : Ω2 ↦ ω b), stdBMm r ∘ (fun ω : Ω2 ↦ ω b'); P2] = 0
    have hind : IndepFun (fun ω : Ω2 ↦ ω b) (fun ω : Ω2 ↦ ω b') P2 :=
      (iIndepFun_infinitePi (P := fun _ : Bool ↦ stdP) (X := fun _ x ↦ x)
        fun _ ↦ measurable_id).indepFun hb
    exact (hind.comp (measurable_stdBMm s) (measurable_stdBMm r)).covariance_eq_zero hm1 hm2

lemma integral_Zm (p : Bool × ℝ≥0) : P2[Zm p] = 0 := by
  rw [show (Zm p) = fun ω : Ω2 ↦ stdBMm p.2 (ω p.1) from rfl,
    integral_comp_eval_P2 p.1 (measurable_stdBMm p.2),
    integral_congr_ae (stdBM_ae_eq p.2).symm, isBrownianReal_stdBM.integral_eval]

/-- The canonical planar Brownian motion is a planar Brownian motion. -/
theorem isPlanarBM_planarBM : IsPlanarBM planarBM P2 := by
  refine ⟨?_, isGaussianProcess_Zm.congr fun p ↦ (coordProc_ae_eq p).symm, fun p ↦ ?_,
    fun p q ↦ ?_⟩
  · have h0 := (measurePreserving_eval_P2 false).quasiMeasurePreserving.ae
      isBrownianReal_stdBM.cont
    have h1 := (measurePreserving_eval_P2 true).quasiMeasurePreserving.ae
      isBrownianReal_stdBM.cont
    filter_upwards [h0, h1] with ω h0 h1
    unfold planarBM
    fun_prop
  · rw [integral_congr_ae (coordProc_ae_eq p), integral_Zm]
  · rw [← covariance_Zm]
    simp only [covariance]
    rw [integral_congr_ae (coordProc_ae_eq p), integral_congr_ae (coordProc_ae_eq q)]
    refine integral_congr_ae ?_
    filter_upwards [coordProc_ae_eq p, coordProc_ae_eq q] with x h1 h2
    simp [h1, h2]

end KilledHeat
end LQGMetric
