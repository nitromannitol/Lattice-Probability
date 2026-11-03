/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.CameronMartin at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.Green
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.CameronMartin
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Cameron–Martin for the whole-plane GFF (task P2-FCM, part 2)

Let `h` be a whole-plane GFF (`IsWholePlaneGFF h P`) and `φ ∈ 𝓓(ℂ)` a test function (mean zero
or not). On the σ-algebra of mean-zero pairings, i.e. for the laws on `TestC0 → ℝ` (product
σ-algebra) of `ψ ↦ ⟨h, ψ⟩` (`lawPair0 h P`) and of `ψ ↦ ⟨h + φ, ψ⟩` (`addFun (h ω) (testCont φ)`):

* `lawPair0_addFun_eq_withDensity` : `law(h + φ) = exp(⟨h, ρ_φ⟩ − (φ, φ)_∇ / 2) · law(h)`, where
  `ρ_φ = −Δφ/(2π)` (`cmTest0 φ`) and `(φ, φ)_∇ = (2π)⁻¹ ∫ |∇φ|²` (`gradEnergy φ`);
  `rnDeriv_lawPair0_addFun` : the same as a Radon–Nikodym derivative;
* `lawPair0_addFun_ac`, `lawPair0_ac_addFun` : mutual absolute continuity;
* `integral_cmDensity_sq` : `E[(dP_{h+φ}/dP_h)²] = exp((φ, φ)_∇)`;
* `lawPair0_addFun_le_sqrt` (and `measureReal_…`) : `P[h + φ ∈ A] ≤ (P[h ∈ A] e^{(φ,φ)_∇})^{1/2}`
  (Cauchy–Schwarz, the form used in Miller–Qian Lemma 4.1 and GM Lemma 2.7);
* `abs_lawPair0_addFun_sub_le` : total variation `≤ (e^{(φ,φ)_∇} − 1)^{1/2}`;
* `integral_comp_addFun` : `E[F(h + φ)] = E[F(h) · exp(⟨h, ρ_φ⟩ − (φ, φ)_∇/2)]`.

Since `IsWholePlaneGFF` only sees mean-zero pairings, a constant shift of `φ` is invisible here
(`∫ ψ (φ + c) = ∫ ψ φ` for `ψ ∈ TestC0`), consistently with `(φ + c, φ + c)_∇ = (φ, φ)_∇`.

Proof: the pairings form a centred Gaussian process indexed by `TestC0`, so the abstract
Cameron–Martin theorem `QuantumZipper.CameronMartin.map_tiltMeasure_path` (with
`integral_tiltDensity_sq`, `integral_mul_tiltDensity`, `abs_measureReal_shift_sub_le`) applies with
`σ = δ_{ρ_φ}`. By the Green identity `logCov_cmTest_right` the shift is `K(ψ, σ) = ∫ ψ φ =
⟨φ, ψ⟩`, and `K(σ, σ) = (φ, φ)_∇` by `logCov_cmTest_cmTest`.

Sources: Cameron–Martin theorem, Bogachev, *Gaussian Measures*, Thm 2.4.5; for the GFF,
Berestycki–Powell, *Gaussian free field and Liouville quantum gravity*, arXiv:2404.16642,
`BookNathanael/definitionGFF.tex` l. 1390, Prop. `lem:CMGFF` (Dirichlet GFF; RN derivative
`exp((h, F)_∇ − (F, F)_∇/2)`); Werner–Powell, *Lecture notes on the GFF*, arXiv:2004.04720,
`GFFArxiVfinal.tex` l. 2962 (Cameron–Martin space of the GFF). Here the whole-plane version, with
`(h, φ)_∇ := ⟨h, −Δφ/(2π)⟩`, is obtained directly from the abstract Gaussian-process theorem. The Cauchy–Schwarz form: Miller–Qian (arXiv:1806.03402) proof of
Lemma 4.1; GM (arXiv:1905.00383) proof of Lemma 2.7.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric

/-- the mean-zero pairings `ψ ↦ ⟨g, ψ⟩` of a distribution -/
def pair0 (g : DistC) : TestC0 → ℝ := fun ψ => g ψ.1

/-- a test function as a continuous function (to form `h + φ` with `addFun`) -/
def testCont (φ : TestC) : C(ℂ, ℝ) := ⟨φ, φ.continuous⟩

/-- the law of the mean-zero pairings of `h` -/
def lawPair0 {Ω : Type*} [MeasurableSpace Ω] (h : Ω → DistC) (P : Measure Ω) :
    Measure (TestC0 → ℝ) :=
  P.map fun ω => pair0 (h ω)

/-- the Cameron–Martin density `ξ ↦ exp(ξ(ρ_φ) − (φ, φ)_∇ / 2)` on paths -/
def cmDensity (φ : TestC) (ξ : TestC0 → ℝ) : ℝ := Real.exp (ξ (cmTest0 φ) - gradEnergy φ / 2)

lemma measurable_cmDensity (φ : TestC) : Measurable (cmDensity φ) :=
  Real.measurable_exp.comp ((measurable_pi_apply _).sub_const _)

lemma measurable_evalDist (ψ : TestC) : Measurable fun g : DistC => g ψ := by
  have : Measurable fun (g : DistC) (φ : TestC) => g φ := fun _ hs => ⟨_, hs, rfl⟩
  exact (measurable_pi_apply ψ).comp this

lemma measurable_pair0 : Measurable pair0 :=
  measurable_pi_iff.mpr fun ψ => measurable_evalDist ψ.1

lemma pair0_addFun (g : DistC) (φ : TestC) (ψ : TestC0) :
    pair0 (addFun g (testCont φ)) ψ = pair0 g ψ + ∫ x, ψ.1 x * φ x := by
  simp only [pair0, addFun, ofCont]
  rw [ContinuousLinearMap.add_apply,
    Distribution.ofFun_apply ((testCont φ).continuous.locallyIntegrable.locallyIntegrableOn _)]
  rfl

section GFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

/-- the Gaussian process of mean-zero pairings `(ψ, ω) ↦ ⟨h ω, ψ⟩` -/
def pairProc (h : Ω → DistC) : TestC0 → Ω → ℝ := fun ψ ω => h ω ψ.1

lemma gaussian_pairProc (hh : IsWholePlaneGFF h P) : IsGaussianProcess (pairProc h) P :=
  hh.gaussian

lemma centered_pairProc (hh : IsWholePlaneGFF h P) (ψ : TestC0) : P[pairProc h ψ] = 0 :=
  hh.centered ψ

lemma covShift_cm (hh : IsWholePlaneGFF h P) (φ : TestC) (ψ : TestC0) :
    QuantumZipper.CameronMartin.covShift (pairProc h) P (Finsupp.single (cmTest0 φ) 1) ψ =
      ∫ x, ψ.1 x * φ x := by
  simp only [QuantumZipper.CameronMartin.covShift, QuantumZipper.CameronMartin.covK,
    Finsupp.support_single _ one_ne_zero, Finset.sum_singleton,
    Finsupp.single_eq_same, one_mul]
  exact (hh.covariance_eq ψ (cmTest0 φ)).trans (logCov_cmTest_right φ ψ.1)

lemma covNorm_cm (hh : IsWholePlaneGFF h P) (φ : TestC) :
    QuantumZipper.CameronMartin.covNorm (pairProc h) P (Finsupp.single (cmTest0 φ) 1) = gradEnergy φ := by
  simp only [QuantumZipper.CameronMartin.covNorm,
    Finsupp.support_single _ one_ne_zero, Finset.sum_singleton,
    Finsupp.single_eq_same, one_mul]
  rw [covShift_cm hh, ← logCov_cmTest_right]
  exact logCov_cmTest_cmTest φ

lemma tiltDensity_cm (hh : IsWholePlaneGFF h P) (φ : TestC) (ω : Ω) :
    QuantumZipper.CameronMartin.tiltDensity (pairProc h) P (Finsupp.single (cmTest0 φ) 1) ω =
      cmDensity φ (pair0 (h ω)) := by
  unfold QuantumZipper.CameronMartin.tiltDensity
  rw [covNorm_cm hh, cmDensity]
  simp only [QuantumZipper.CameronMartin.comb, Finsupp.support_single _ one_ne_zero,
    Finset.sum_singleton, Finsupp.single_eq_same, one_mul]
  rfl

lemma shift_cm (hh : IsWholePlaneGFF h P) (φ : TestC) :
    (fun ω => pair0 (addFun (h ω) (testCont φ))) = fun ω j =>
      (pairProc h) j ω + QuantumZipper.CameronMartin.covShift (pairProc h) P (Finsupp.single (cmTest0 φ) 1) j := by
  funext ω j
  rw [pair0_addFun, covShift_cm hh]
  rfl

lemma measurable_pair0_comp (hh : IsWholePlaneGFF h P) :
    Measurable fun ω => pair0 (h ω) := measurable_pair0.comp hh.measurable

lemma measurable_pair0_addFun (hh : IsWholePlaneGFF h P) (φ : TestC) :
    Measurable fun ω => pair0 (addFun (h ω) (testCont φ)) := by
  rw [shift_cm hh]
  exact measurable_pi_iff.mpr fun j =>
    ((measurable_evalDist j.1).comp hh.measurable).add_const _

/-- **Cameron–Martin for the whole-plane GFF.** On mean-zero pairings,
`law(h + φ) = exp(⟨h, −Δφ/(2π)⟩ − (φ, φ)_∇ / 2) · law(h)`. -/
theorem lawPair0_addFun_eq_withDensity (hh : IsWholePlaneGFF h P) (φ : TestC) :
    lawPair0 (fun ω => addFun (h ω) (testCont φ)) P =
      (lawPair0 h P).withDensity fun ξ => ENNReal.ofReal (cmDensity φ ξ) := by
  have hmeas : ∀ ψ : TestC0, Measurable ((pairProc h) ψ) := fun ψ =>
    (measurable_evalDist ψ.1).comp hh.measurable
  have key := QuantumZipper.CameronMartin.map_tiltMeasure_path (gaussian_pairProc hh) hmeas (centered_pairProc hh)
    (Finsupp.single (cmTest0 φ) 1)
  have hp : Measurable fun ω => pair0 (h ω) := measurable_pair0_comp hh
  rw [lawPair0, shift_cm hh, ← key, lawPair0]
  change Measure.map (fun ω => pair0 (h ω)) _ = _
  ext s hs
  rw [Measure.map_apply hp hs, QuantumZipper.CameronMartin.tiltMeasure, withDensity_apply _ (hp hs),
    withDensity_apply _ hs, setLIntegral_map hs
      (f := fun ξ => ENNReal.ofReal (cmDensity φ ξ))
      (ENNReal.measurable_ofReal.comp (measurable_cmDensity φ)) hp]
  refine setLIntegral_congr_fun (hp hs) fun ω _ => ?_
  rw [tiltDensity_cm hh]
  rfl

theorem lawPair0_addFun_ac (hh : IsWholePlaneGFF h P) (φ : TestC) :
    lawPair0 (fun ω => addFun (h ω) (testCont φ)) P ≪ lawPair0 h P := by
  rw [lawPair0_addFun_eq_withDensity hh]
  exact withDensity_absolutelyContinuous _ _

theorem lawPair0_ac_addFun (hh : IsWholePlaneGFF h P) (φ : TestC) :
    lawPair0 h P ≪ lawPair0 (fun ω => addFun (h ω) (testCont φ)) P := by
  rw [lawPair0_addFun_eq_withDensity hh]
  exact withDensity_absolutelyContinuous'
    (ENNReal.measurable_ofReal.comp (measurable_cmDensity φ)).aemeasurable
    (ae_of_all _ fun ξ => (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne')

end GFF

end LQGMetric
