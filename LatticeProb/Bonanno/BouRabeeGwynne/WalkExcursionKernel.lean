/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.WalkExcursionKernel at commit fdb5cad;
   local imports and toolchain compatibility details are adapted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.HarmonicMeasureBridge
import LatticeProb.Bonanno.BouRabeeGwynne.ExcursionConcatenation
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-! The full stopped polygonal excursion of the actual finite conductance
walk, as a measurable Markov kernel in its starting vertex. Both its curve
projection and endpoint distribution are the previously defined actual laws. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators unitInterval

namespace BouRabeeGwynne

variable {d : ℕ} {V : Type*} [Fintype V]
  [MeasurableSpace V] [MeasurableSingletonClass V]

/-- Fixed-duration interpolation is measurable into the space of full
continuous paths, before passing to the Fréchet quotient. -/
lemma measurable_polygonalCurve (pos : V → Euc d) (m : ℕ) :
    Measurable (fun ω : ℕ → V => polygonalCurve pos ω m) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  have hp : Measurable pos := measurable_of_finite _
  change Measurable (fun ω : ℕ → V => pos (ω 0) + ∑ k ∈ Finset.range m,
    max (0 : ℝ) (min 1 ((m : ℝ) * (t : ℝ) - (k : ℝ))) •
      (pos (ω (k + 1)) - pos (ω k)))
  fun_prop

set_option linter.unusedSectionVars false in
/-- Every point of the genuine interpolation lies in any convex set
containing all its vertices. -/
lemma polygonalCurve_mem_of_convex (pos : V → Euc d) (ω : ℕ → V)
    {S : Set (Euc d)} (hS : Convex ℝ S) (hpos : ∀ v, pos v ∈ S)
    (m : ℕ) (t : unitInterval) : polygonalCurve pos ω m t ∈ S := by
  cases m with
  | zero => simpa only [polygonalCurve_zero, ContinuousMap.const_apply] using hpos (ω 0)
  | succ m =>
    obtain ⟨i, hlo, hhi⟩ := (TimePartition.uniform m).exists_interval t
    have hl : (i.val : ℝ) / ((m + 1 : ℕ) : ℝ) ≤ (t : ℝ) := hlo
    have hu : (t : ℝ) ≤ ((i.val + 1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) := hhi
    have hu' : (t : ℝ) ≤ ((i.val : ℝ) + 1) / ((m + 1 : ℕ) : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hu
    rw [polygonalCurve_on_segment pos ω i.isLt t hl hu']
    apply hS.add_smul_sub_mem (hpos _) (hpos _)
    have hm : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    have hl' := (div_le_iff₀ hm).mp hl
    have hu'' := (le_div_iff₀ hm).mp hu'
    constructor <;> nlinarith

/-- The exact representative used in `stoppedPolygonalCurve`, including its
existing total convention at infinite exit time. -/
noncomputable def stoppedPolygonalRepresentative (pos : V → Euc d) (A : Set V)
    (ω : ℕ → V) : C(unitInterval, Euc d) :=
  polygonalCurve pos ω ((FiniteConductanceNetwork.exitTime A ω).untopD 0)

lemma measurable_stoppedPolygonalRepresentative (pos : V → Euc d) (A : Set V) :
    Measurable (stoppedPolygonalRepresentative pos A) := by
  have hf : Measurable (fun p : (ℕ → V) × ℕ => polygonalCurve pos p.1 p.2) :=
    measurable_from_prod_countable_left (measurable_polygonalCurve pos)
  exact hf.comp (measurable_id.prodMk (measurable_stoppedPolygonalDuration A))

set_option linter.unusedSectionVars false in
@[simp] lemma stoppedPolygonalRepresentative_start (pos : V → Euc d) (A : Set V)
    (ω : ℕ → V) : stoppedPolygonalRepresentative pos A ω 0 = pos (ω 0) :=
  polygonalCurve_start pos ω _

namespace FiniteConductanceNetwork

variable (N : FiniteConductanceNetwork V)

/-- The actual stopped walk excursion kernel, constructed from the genuine
trajectory law; no lifting or disintegration of endpoint measures is used. -/
noncomputable def walkExcursionKernel (pos : V → Euc d) (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) : Kernel V C(unitInterval, Euc d) where
  toFun v := (N.trajectoryLaw A hpos v).map (stoppedPolygonalRepresentative pos A)
  measurable' := measurable_of_finite _

lemma walkExcursionKernel_apply (pos : V → Euc d) (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (v : V) :
    N.walkExcursionKernel pos A hpos v =
      (N.trajectoryLaw A hpos v).map (stoppedPolygonalRepresentative pos A) := rfl

instance walkExcursionKernel_isMarkov (pos : V → Euc d) (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) :
    IsMarkovKernel (N.walkExcursionKernel pos A hpos) where
  isProbabilityMeasure _v :=
    (Measure.isProbabilityMeasure_map_iff
      (measurable_stoppedPolygonalRepresentative pos A).aemeasurable).mpr inferInstance

lemma walkExcursionKernel_ae_start (pos : V → Euc d) (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (v : V) :
    ∀ᵐ c ∂N.walkExcursionKernel pos A hpos v, c 0 = pos v := by
  rw [N.walkExcursionKernel_apply]
  apply (ae_map_iff (measurable_stoppedPolygonalRepresentative pos A).aemeasurable
    (measurableSet_eq_fun (ContinuousMap.measurable_eval 0) measurable_const)).mpr
  filter_upwards [N.trajectoryLaw_ae_start A hpos v] with ω hω
  simp only [stoppedPolygonalRepresentative_start, hω]

/-- The whole sampled excursion stays in a closed convex set containing the
finite network's embedded vertices. This applies directly to the enlarged
ball containing the closed graph region, including its exit vertices. -/
lemma walkExcursionKernel_ae_mem_convex (pos : V → Euc d) (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (v : V)
    {S : Set (Euc d)} (hS : Convex ℝ S) (hclosed : IsClosed S)
    (hvertices : ∀ w, pos w ∈ S) :
    ∀ᵐ c ∂N.walkExcursionKernel pos A hpos v, ∀ t, c t ∈ S := by
  have hset : MeasurableSet {c : C(unitInterval, Euc d) | ∀ t, c t ∈ S} := by
    simp only [Set.ofPred_forall]
    exact (isClosed_iInter fun t => hclosed.preimage (continuous_eval_const t)).measurableSet
  rw [N.walkExcursionKernel_apply]
  apply (ae_map_iff (measurable_stoppedPolygonalRepresentative pos A).aemeasurable hset).mpr
  exact Filter.Eventually.of_forall fun ω t =>
    polygonalCurve_mem_of_convex pos ω hS hvertices _ t

/-- Projecting the full excursion gives exactly the original stopped curve law. -/
lemma walkExcursionKernel_project (pos : V → Euc d) (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (v : V) :
    (N.walkExcursionKernel pos A hpos v).map CurveSpace.project =
      (N.trajectoryLaw A hpos v).map (stoppedPolygonalCurve pos A) := by
  rw [N.walkExcursionKernel_apply,
    Measure.map_map CurveSpace.continuous_project.measurable
      (measurable_stoppedPolygonalRepresentative pos A)]
  rfl

/-- Its full-path endpoint law is the actual spatial harmonic measure. -/
lemma walkExcursionKernel_endPoint (pos : V → Euc d) (A : Set V)
    (hpos : ∀ v ∈ A, 0 < N.totalConductance v) (v : V) :
    (N.walkExcursionKernel pos A hpos v).map (fun c => c 1) =
      (N.discreteHarmonicMeasure A hpos v).map pos := by
  have h := N.stoppedPolygonalCurve_map_endPoint pos A hpos v
  rw [← N.walkExcursionKernel_project pos A hpos v,
    Measure.map_map CurveSpace.continuous_endPoint.measurable
      CurveSpace.continuous_project.measurable] at h
  exact h

end FiniteConductanceNetwork
end BouRabeeGwynne
