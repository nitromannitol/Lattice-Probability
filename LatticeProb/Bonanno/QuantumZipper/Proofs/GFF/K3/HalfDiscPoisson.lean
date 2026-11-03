/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.K3.HalfDiscPoisson at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.GFF.Kernels
import LatticeProb.Bonanno.QuantumZipper.Field.Sample
import LatticeProb.Bonanno.LQGDimension.LFPP.CouplingAux1
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
import Mathlib.Probability.Kernel.WithDensity
import Mathlib.Probability.Kernel.Composition.MapComap

/-!
# Half-disc Poisson measure for the free (Neumann) problem (blueprint GFF-K3, node L1)

For a real centre `t` and radius `r > 0`, the half-disc Poisson (balayage) measure of a point
`z ∈ B(t,r)` is the disc Poisson measure on the circle `∂B(t,r)` folded into `Hbar` by `foldH`
(reflection across `ℝ`):
`halfDiscPoisson t r z = ((circleUnif t r).withDensity P_z).map foldH`, with
`P_z(w) = (r² - |z - t|²)/|w - z|²`.

Main results:
* `integral_halfDiscPoisson_of_harmonic`: every `f` harmonic on a neighbourhood of the closed disc
  and even on the circle (`f (conj x) = f x`) is reproduced: `∫ f d(halfDiscPoisson t r z) = f z`.
  Proof: fold back (`f ∘ foldH = f` on the circle) and apply mathlib's disc Poisson formula
  `HarmonicOnNhd.circleAverage_poissonKernel_smul`.
* `integral_neumannH_halfDiscPoisson`: reproduction of `neumannH (·, y)` for `y ∉ closedBall t r`.
* `isProbabilityMeasure_halfDiscPoisson`, `ae_halfDiscPoisson_mem` (support on the folded
  semicircle `sphere t r ∩ Hbar`), and measurability of `z ↦ halfDiscPoisson t r z` via the
  kernel `halfDiscPoissonKernel`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Filter InnerProductSpace
open scoped Real ComplexConjugate ENNReal Topology

namespace QuantumZipper

namespace K3

/-- The half-disc Poisson measure of `z` for the half-disc `B(t,r) ∩ H`, `t ∈ ℝ`: the disc
Poisson measure on `∂B(t,r)` folded into `Hbar` by `foldH`. (For `z ∉ B(t,r)` the density
vanishes and this is the zero measure.) -/
def halfDiscPoisson (t r : ℝ) (z : ℂ) : Measure ℂ :=
  ((circleUnif (t : ℂ) r).withDensity fun w =>
    ENNReal.ofReal ((r ^ 2 - ‖z - t‖ ^ 2) / ‖w - z‖ ^ 2)).map foldH

/-- The Green function of the half-disc with Neumann condition on the diameter and Dirichlet
condition on the arc: `neumannH` minus its harmonic (balayage) part. -/
def halfDiscGreen (t r : ℝ) (x y : ℂ) : ℝ :=
  neumannH x y - ∫ u, neumannH u y ∂(halfDiscPoisson t r x)

/-! ## Elementary facts -/

theorem circleUnif_eq_circMeas_k3 (z : ℂ) (r : ℝ) :
    circleUnif z r = LQGDimension.Coupling.circMeas z r := by
  unfold circleUnif LQGDimension.Coupling.circMeas LQGDimension.Coupling.angMeas
  rw [Measure.map_smul, Measure.restrict_congr_set Ico_ae_eq_Ioc]
  all_goals exact (measurable_circleMap z r).aemeasurable

theorem ae_mem_sphere_circleUnif_k3 (c : ℂ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ w ∂circleUnif c r, w ∈ sphere c r := by
  rw [circleUnif_eq_circMeas_k3]
  filter_upwards [LQGDimension.Coupling.ae_circMeas c r] with w hw
  rw [mem_sphere_iff_norm, hw, abs_of_pos hr]

theorem norm_conj_sub_ofReal_k3 (x : ℂ) (t : ℝ) : ‖conj x - (t : ℂ)‖ = ‖x - t‖ := by
  rw [← Complex.norm_conj, map_sub, Complex.conj_conj, Complex.conj_ofReal]

theorem foldH_mem_sphere_k3 {t r : ℝ} {w : ℂ} (hw : w ∈ sphere (t : ℂ) r) :
    foldH w ∈ sphere (t : ℂ) r := by
  unfold foldH
  split_ifs
  · exact hw
  · rw [mem_sphere_iff_norm] at hw ⊢
    rw [norm_conj_sub_ofReal_k3, hw]

theorem foldH_mem_Hbar_k3 (w : ℂ) : foldH w ∈ Hbar := by
  unfold foldH Hbar
  split_ifs with h
  · exact h
  · simp only [Set.mem_ofPred_eq, Complex.conj_im]
    linarith [not_le.mp h]

theorem measurable_halfDiscPoissonDensity (t r : ℝ) :
    Measurable (Function.uncurry fun (z w : ℂ) =>
      ENNReal.ofReal ((r ^ 2 - ‖z - t‖ ^ 2) / ‖w - z‖ ^ 2)) :=
  ((measurable_const.sub ((measurable_fst.sub measurable_const).norm.pow_const 2)).div
    ((measurable_snd.sub measurable_fst).norm.pow_const 2)).ennreal_ofReal

/-! ## Measurability: the half-disc Poisson kernel -/

/-- `z ↦ halfDiscPoisson t r z` as a Markov-type kernel (a probability measure for
`z ∈ ball t r`, zero otherwise). -/
def halfDiscPoissonKernel (t r : ℝ) : Kernel ℂ ℂ :=
  ((Kernel.const ℂ (circleUnif (t : ℂ) r)).withDensity fun z w =>
    ENNReal.ofReal ((r ^ 2 - ‖z - t‖ ^ 2) / ‖w - z‖ ^ 2)).map foldH

theorem halfDiscPoissonKernel_apply (t r : ℝ) (z : ℂ) :
    halfDiscPoissonKernel t r z = halfDiscPoisson t r z := by
  rw [halfDiscPoissonKernel, Kernel.map_apply _ measurable_foldH,
    Kernel.withDensity_apply _ (measurable_halfDiscPoissonDensity t r), Kernel.const_apply]
  rfl

theorem measurable_halfDiscPoisson (t r : ℝ) : Measurable (halfDiscPoisson t r) := by
  have : halfDiscPoisson t r = fun z => halfDiscPoissonKernel t r z :=
    funext fun z => (halfDiscPoissonKernel_apply t r z).symm
  rw [this]
  exact (halfDiscPoissonKernel t r).measurable

/-! ## Support -/

/-- The half-disc Poisson measure lives on the folded semicircle `∂B(t,r) ∩ Hbar`. -/
theorem ae_halfDiscPoisson_mem {t r : ℝ} (hr : 0 < r) (z : ℂ) :
    ∀ᵐ x ∂halfDiscPoisson t r z, x ∈ sphere (t : ℂ) r ∩ Hbar := by
  unfold halfDiscPoisson
  refine (ae_map_iff measurable_foldH.aemeasurable ?_).2 ?_
  · exact isClosed_sphere.measurableSet.inter isClosed_Hbar.measurableSet
  filter_upwards [(withDensity_absolutelyContinuous _ _).ae_le
    (ae_mem_sphere_circleUnif_k3 (t : ℂ) hr)] with w hw
  exact ⟨foldH_mem_sphere_k3 hw, foldH_mem_Hbar_k3 w⟩

theorem halfDiscPoisson_compl_eq_zero {t r : ℝ} (hr : 0 < r) (z : ℂ) :
    halfDiscPoisson t r z (sphere (t : ℂ) r ∩ Hbar)ᶜ = 0 :=
  mem_ae_iff.1 (ae_halfDiscPoisson_mem hr z)

/-! ## Reproduction of even harmonic functions -/

/-- Unfolding the half-disc Poisson integral to an integral over the circle. -/
theorem integral_halfDiscPoisson_eq_circle (t r : ℝ) (z : ℂ) {f : ℂ → ℝ}
    (hf : AEStronglyMeasurable f (halfDiscPoisson t r z)) :
    ∫ x, f x ∂(halfDiscPoisson t r z) = ∫ w, (ENNReal.ofReal ((r ^ 2 - ‖z - t‖ ^ 2) /
      ‖w - z‖ ^ 2)).toReal • f (foldH w) ∂(circleUnif (t : ℂ) r) := by
  have hdens : Measurable fun w : ℂ => ENNReal.ofReal ((r ^ 2 - ‖z - t‖ ^ 2) / ‖w - z‖ ^ 2) :=
    (measurable_const.div ((measurable_id.sub measurable_const).norm.pow_const 2)).ennreal_ofReal
  unfold halfDiscPoisson at hf ⊢
  rw [integral_map measurable_foldH.aemeasurable hf]
  exact integral_withDensity_eq_integral_toReal_smul hdens
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) _

theorem continuousOn_poissonKernel_sphere_k3 {t r : ℝ} {z : ℂ} (hz : z ∈ ball (t : ℂ) r) :
    ContinuousOn (poissonKernel (t : ℂ) z) (sphere (t : ℂ) r) := by
  have hfun : poissonKernel (t : ℂ) z = fun w : ℂ =>
      (‖w - t‖ ^ 2 - ‖z - t‖ ^ 2) / ‖(w - t) - (z - t)‖ ^ 2 :=
    funext fun w => poissonKernel_def _ _ _
  rw [hfun]
  refine ContinuousOn.div (Continuous.continuousOn (by fun_prop))
    (Continuous.continuousOn (by fun_prop)) fun w hw => ?_
  refine pow_ne_zero 2 (norm_ne_zero_iff.2 fun h => ?_)
  have hwz : w = z := by rw [sub_sub_sub_cancel_right] at h; exact sub_eq_zero.1 h
  rw [hwz] at hw
  exact (ne_of_lt (mem_ball_iff_norm.1 hz)) (mem_sphere_iff_norm.1 hw)

/-- **Half-disc Poisson formula.** A function harmonic on a neighbourhood of the closed disc
`closedBall t r` (`t ∈ ℝ`) and even across `ℝ` on the circle is reproduced by the half-disc
Poisson measure at every `z ∈ ball t r`. -/
theorem integral_halfDiscPoisson_of_harmonic {t r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : z ∈ ball (t : ℂ) r) {f : ℂ → ℝ} (hf : HarmonicOnNhd f (closedBall (t : ℂ) r))
    (heven : ∀ x ∈ sphere (t : ℂ) r, f (conj x) = f x) :
    ∫ x, f x ∂(halfDiscPoisson t r z) = f z := by
  have hSm : MeasurableSet (sphere (t : ℂ) r) := isClosed_sphere.measurableSet
  have hcont : ContinuousOn f (sphere (t : ℂ) r) := fun x hx =>
    (hf x (sphere_subset_closedBall hx)).1.continuousAt.continuousWithinAt
  have hfold : ∀ x ∈ sphere (t : ℂ) r, f (foldH x) = f x := by
    intro x hx
    unfold foldH
    split_ifs
    · rfl
    · exact heven x hx
  have hzt : ‖z - t‖ < r := mem_ball_iff_norm.1 hz
  have hpos : 0 < r ^ 2 - ‖z - t‖ ^ 2 := by nlinarith [norm_nonneg (z - t)]
  have hae : AEStronglyMeasurable f (halfDiscPoisson t r z) := by
    have hconc : ∀ᵐ x ∂halfDiscPoisson t r z, x ∈ sphere (t : ℂ) r :=
      (ae_halfDiscPoisson_mem hr z).mono fun x hx => hx.1
    rw [← Measure.restrict_eq_self_of_ae_mem hconc]
    exact hcont.aestronglyMeasurable hSm
  rw [integral_halfDiscPoisson_eq_circle t r z hae]
  have hcongr : (fun w => (ENNReal.ofReal ((r ^ 2 - ‖z - t‖ ^ 2) / ‖w - z‖ ^ 2)).toReal •
      f (foldH w)) =ᵐ[circleUnif (t : ℂ) r] (poissonKernel (t : ℂ) z • f) := by
    filter_upwards [ae_mem_sphere_circleUnif_k3 (t : ℂ) hr] with w hw
    rw [ENNReal.toReal_ofReal (div_nonneg hpos.le (sq_nonneg _)), hfold w hw]
    change _ * f w = poissonKernel (t : ℂ) z w * f w
    rw [poissonKernel_def, mem_sphere_iff_norm.1 hw, sub_sub_sub_cancel_right]
  have hmeas : AEStronglyMeasurable (poissonKernel (t : ℂ) z • f) (circleUnif (t : ℂ) r) := by
    rw [← Measure.restrict_eq_self_of_ae_mem (ae_mem_sphere_circleUnif_k3 (t : ℂ) hr)]
    exact ((continuousOn_poissonKernel_sphere_k3 hz).smul hcont).aestronglyMeasurable hSm
  rw [integral_congr_ae hcongr]
  rw [circleUnif_eq_circMeas_k3] at hmeas ⊢
  rw [LQGDimension.Coupling.integral_circMeas_eq_circleAverage hmeas]
  exact hf.circleAverage_poissonKernel_smul hz

/-- For `z ∈ ball t r`, the half-disc Poisson measure is a probability measure. -/
theorem isProbabilityMeasure_halfDiscPoisson {t r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : z ∈ ball (t : ℂ) r) : IsProbabilityMeasure (halfDiscPoisson t r z) := by
  have h := integral_halfDiscPoisson_of_harmonic hr hz (f := fun _ => (1 : ℝ))
    (fun x _ => harmonicAt_const 1) (fun _ _ => rfl)
  rw [integral_const, smul_eq_mul, mul_one, measureReal_def] at h
  exact ⟨(ENNReal.toReal_eq_one_iff _).1 h⟩

/-! ## Reproduction of the Neumann kernel -/

theorem neumannH_conj_left_k3 (x y : ℂ) : neumannH (conj x) y = neumannH x y := by
  unfold neumannH
  have h1 : ‖conj x - y‖ = ‖x - conj y‖ := by
    rw [← Complex.norm_conj, map_sub, Complex.conj_conj]
  have h2 : ‖conj x - conj y‖ = ‖x - y‖ := by
    rw [← map_sub, Complex.norm_conj]
  rw [h1, h2]; ring

theorem harmonicAt_neumannH_left_k3 {x y : ℂ} (hxy : x ≠ y) (hxy' : x ≠ conj y) :
    HarmonicAt (fun u => neumannH u y) x := by
  have h1 : HarmonicAt (fun u => Real.log ‖u - y‖) x :=
    AnalyticAt.harmonicAt_log_norm (analyticAt_id.sub analyticAt_const) (sub_ne_zero.2 hxy)
  have h2 : HarmonicAt (fun u => Real.log ‖u - conj y‖) x :=
    AnalyticAt.harmonicAt_log_norm (analyticAt_id.sub analyticAt_const) (sub_ne_zero.2 hxy')
  convert h1.neg.add h2.neg using 1
  funext u
  simp only [neumannH, Pi.add_apply, Pi.neg_apply]
  ring

/-- **Blueprint L1 kernel identity** (for `y` off the closed disc): the half-disc Poisson measure
reproduces the Neumann kernel `neumannH (·, y)`. -/
theorem integral_neumannH_halfDiscPoisson {t r : ℝ} (hr : 0 < r) {z : ℂ}
    (hz : z ∈ ball (t : ℂ) r) {y : ℂ} (hy : y ∉ closedBall (t : ℂ) r) :
    ∫ x, neumannH x y ∂(halfDiscPoisson t r z) = neumannH z y := by
  refine integral_halfDiscPoisson_of_harmonic hr hz
    (fun x hx => harmonicAt_neumannH_left_k3 ?_ ?_) (fun x _ => neumannH_conj_left_k3 x y)
  · rintro rfl; exact hy hx
  · rintro rfl
    refine hy ?_
    rw [mem_closedBall_iff_norm] at hx ⊢
    rwa [← norm_conj_sub_ofReal_k3]

end K3

end QuantumZipper
