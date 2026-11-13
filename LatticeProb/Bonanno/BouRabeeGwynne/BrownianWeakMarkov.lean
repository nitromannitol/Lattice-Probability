/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianWeakMarkov at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedCurveLaws
import LatticeProb.Bonanno.BouRabeeGwynne.IndependentCoordinatePairs
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-!
# Euclidean Brownian future independent of the entire past

Coordinate independence is regrouped explicitly; this is the deterministic-time
identity used in the finite dyadic approximation of ball exit times.
-/
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace BouRabeeGwynne

noncomputable def shiftedBrownianPath {d : ℕ} (t : ℝ≥0)
    (ω : BrownianPath d) : BrownianPath d where
  toFun s := ω (t + s) - ω t
  continuous_toFun := by fun_prop

lemma measurable_shiftedBrownianPath {d : ℕ} (t : ℝ≥0) :
    Measurable (shiftedBrownianPath (d := d) t) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro s
  change Measurable (fun ω : BrownianPath d ↦ ω (t + s) - ω t)
  fun_prop

/-- Under the exact standard Brownian-law predicate, the complete future
increment process at a deterministic time is independent of the entire past. -/
theorem standardBrownianLaw_indepFun_shift {d : ℕ}
    {μ : Measure (BrownianPath d)} (hμ : IsStandardBrownianLaw μ) (t : ℝ≥0) :
    IndepFun (fun (ω : BrownianPath d) (s : ℝ≥0) ↦ ω (t + s) - ω t)
      (fun (ω : BrownianPath d) (s : Set.Iic t) ↦ ω s) μ := by
  letI : IsProbabilityMeasure μ := hμ.1
  let f : Fin d → BrownianPath d → (ℝ≥0 → ℝ) :=
    fun i ω s ↦ ω (t + s) i - ω t i
  let g : Fin d → BrownianPath d → (Set.Iic t → ℝ) :=
    fun i ω s ↦ ω s i
  have hf (i : Fin d) : Measurable (f i) := by dsimp [f]; fun_prop
  have hg (i : Fin d) : Measurable (g i) := by
    apply Measurable.of_eval
    intro s
    exact (by fun_prop : Continuous (fun ω : BrownianPath d ↦ ω (s : ℝ≥0) i)).measurable
  have hpairs : iIndepFun (fun i ω ↦ (f i ω, g i ω)) μ :=
    hμ.2.2.comp
      (fun (_ : Fin d) (b : ℝ≥0 → ℝ) ↦
        ((fun s : ℝ≥0 ↦ b (t + s) - b t), (fun s : Set.Iic t ↦ b s)))
      (by intro i; fun_prop)
  have hwithin (i : Fin d) : IndepFun (f i) (g i) μ :=
    (hμ.2.1 i).toIsPreBrownianReal.indepFun_shift t
  have hvec := indepFun_vectors_of_independent_coordinate_pairs hf hg hpairs hwithin
  let assembleFuture : (Fin d → ℝ≥0 → ℝ) → (ℝ≥0 → Euc d) :=
    fun b s ↦ WithLp.toLp 2 (fun i ↦ b i s)
  let assemblePast : (Fin d → Set.Iic t → ℝ) → (Set.Iic t → Euc d) :=
    fun b s ↦ WithLp.toLp 2 (fun i ↦ b i s)
  have hmF : Measurable assembleFuture := by
    apply measurable_pi_lambda
    intro s
    exact (PiLp.continuous_toLp 2 (fun _ : Fin d ↦ ℝ)).measurable.comp (by fun_prop)
  have hmP : Measurable assemblePast := by
    apply measurable_pi_lambda
    intro s
    exact (PiLp.continuous_toLp 2 (fun _ : Fin d ↦ ℝ)).measurable.comp (by fun_prop)
  exact hvec.comp hmF hmP

end BouRabeeGwynne
