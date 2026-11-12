/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_8GffLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffCV
import LatticeProb.Bonanno.LQGMetric.Field.KilledHeatLaw
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.GaussFdd
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Laws of continuous Gaussian paths (DFGPS L2.8, step (a1): transport across couplings)

DFGPS (T:880–881) uses DDDF Theorem 1 and DDDF Proposition 29 (`Blueprint.DDDFProp29`), whose
coupling lives on its own probability space. To transport statements about laws we need: the law
of the path of a process with continuous paths, as a random element of `C(ℂ, ℝ)`, is determined
by its finite-dimensional distributions; for Gaussian processes by means and covariances.

* `pathC` : the path `ω ↦ (x ↦ Y x ω)` as an element of `C(ℂ, ℝ)`; `measurable_pathC`;
* `map_pathC_eq_of_gaussian` : two Gaussian processes with continuous paths and equal means and
  covariances have equal path laws (restriction to a dense sequence is a measurable embedding of
  the Polish space `C(ℂ, ℝ)`, mathlib `Continuous.measurableEmbedding`, and laws on `ℕ → ℝ` are
  determined by means and covariances, `KilledHeat.map_eq_of_gaussian`);
* `map_pathC_heat_eq` : for continuous versions of the heat-smoothed zero-boundary GFF
  `x ↦ Xh (p_s(x − ·) 1_D)` on two probability spaces.

Standard (e.g. Kallenberg, *Foundations of Modern Probability*, 2nd ed., Prop. 2.2 + Lemma 1.17
for the uniqueness of laws on `C` given the finite-dimensional ones); here assembled from mathlib.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace LQGMetric.DFGPS

open Blueprint

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}

/-- the path of a process with continuous paths, in `C(ℂ, ℝ)` -/
def pathC (Y : ℂ → Ω → ℝ) (hYc : ∀ ω, Continuous fun x => Y x ω) (ω : Ω) : C(ℂ, ℝ) :=
  ⟨fun x => Y x ω, hYc ω⟩

lemma measurable_pathC {Y : ℂ → Ω → ℝ} (hYc : ∀ ω, Continuous fun x => Y x ω)
    (hYm : ∀ x, Measurable (Y x)) : Measurable (pathC Y hYc) :=
  ContinuousMap.measurable_iff_eval.2 fun x => hYm x

/-- **Path laws of continuous Gaussian processes** are determined by means and covariances. -/
theorem map_pathC_eq_of_gaussian {Y : ℂ → Ω → ℝ} {Y' : ℂ → Ω' → ℝ}
    (hYc : ∀ ω, Continuous fun x => Y x ω) (hY'c : ∀ ω, Continuous fun x => Y' x ω)
    (hYm : ∀ x, Measurable (Y x)) (hY'm : ∀ x, Measurable (Y' x))
    (hY : IsGaussianProcess Y P) (hY' : IsGaussianProcess Y' P')
    (hm : ∀ x, P[Y x] = P'[Y' x]) (hc : ∀ x y, cov[Y x, Y y; P] = cov[Y' x, Y' y; P']) :
    P.map (pathC Y hYc) = P'.map (pathC Y' hY'c) := by
  obtain ⟨q, hq⟩ := TopologicalSpace.exists_dense_seq ℂ
  set r : C(ℂ, ℝ) → (ℕ → ℝ) := fun f n => f (q n) with hrdef
  have hrc : Continuous r := continuous_pi fun n => continuous_eval_const (q n)
  have hri : Function.Injective r := fun f g hfg =>
    ContinuousMap.ext fun x => congrFun (Continuous.ext_on hq f.continuous g.continuous
      (by rintro _ ⟨n, rfl⟩; exact congrFun hfg n)) x
  have hr : MeasurableEmbedding r := hrc.measurableEmbedding hri
  have hmap : (P.map (pathC Y hYc)).map r = (P'.map (pathC Y' hY'c)).map r := by
    rw [Measure.map_map hr.measurable (measurable_pathC hYc hYm),
      Measure.map_map hr.measurable (measurable_pathC hY'c hY'm)]
    exact KilledHeat.map_eq_of_gaussian (X := fun n => Y (q n)) (Y := fun n => Y' (q n))
      (hY.comp_right q) (hY'.comp_right q) (fun n => hm (q n)) fun m n => hc (q m) (q n)
  ext s hs
  have := congrArg (fun μ : Measure (ℕ → ℝ) => μ (r '' s)) hmap
  rwa [hr.map_apply, hr.map_apply, preimage_image_eq _ hri] at this

/-- **Path laws of continuous versions of the heat-smoothed zero-boundary GFF** agree across
probability spaces. -/
theorem map_pathC_heat_eq [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {D : TopologicalSpace.Opens ℂ} {Xh : BddOn (D : Set ℂ) → Ω → ℝ}
    {Xh' : BddOn (D : Set ℂ) → Ω' → ℝ} (hX : IsZBGFFProcessExt D Xh P)
    (hX' : IsZBGFFProcessExt D Xh' P') {s : ℝ} {Y : ℂ → Ω → ℝ} {Y' : ℂ → Ω' → ℝ}
    (hY : IsContVersion (fun x => Xh (heatBdd D s x)) Y P)
    (hY' : IsContVersion (fun x => Xh' (heatBdd D s x)) Y' P') :
    P.map (pathC Y hY.1) = P'.map (pathC Y' hY'.1) := by
  refine map_pathC_eq_of_gaussian hY.1 hY'.1 hY.2.1 hY'.2.1
    ((hX.gaussian.comp_right (heatBdd D s)).congr fun x => (hY.2.2 x).symm)
    ((hX'.gaussian.comp_right (heatBdd D s)).congr fun x => (hY'.2.2 x).symm)
    (fun x => ?_) fun x y => ?_
  · rw [integral_congr_ae (hY.2.2 x), integral_congr_ae (hY'.2.2 x)]
    exact (hX.centered _).trans (hX'.centered _).symm
  · rw [DDDF.covariance_congr_ae (hY.2.2 x) (hY.2.2 y),
      DDDF.covariance_congr_ae (hY'.2.2 x) (hY'.2.2 y)]
    exact (hX.covariance_eq _ _).trans (hX'.covariance_eq _ _).symm

end LQGMetric.DFGPS
