/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.BrownianUniformModulus at commit fdb5cad; the module paths of local imports and lint-related details are adjusted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.StoppedCurveLaws
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.MeasureTheory.Measure.Continuity

/-!
# A measurable uniform modulus on bounded time intervals

For any finite law on continuous Euclidean paths, the probability of a spatial
oscillation of fixed positive size on an interval of length at most `1/(n+1)`
tends to zero. Translation of the path by its initial position leaves these
events unchanged. This supplies the common modulus needed for uniform
ball-skeleton truncation in Section 4.
-/

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
namespace BouRabeeGwynne

/-- A closed modulus event on the actual canonical continuous-path space. -/
def pathModulusEvent {d : ℕ} (T : ℝ≥0) (ε : ℝ) (n : ℕ) : Set (BrownianPath d) :=
  {ω | ∀ s ∈ Icc (0 : ℝ≥0) T, ∀ t ∈ Icc (0 : ℝ≥0) T,
    dist s t ≤ 1 / (n + 1 : ℝ) → dist (ω s) (ω t) ≤ ε}

lemma isClosed_pathModulusEvent {d : ℕ} (T : ℝ≥0) (ε : ℝ) (n : ℕ) :
    IsClosed (pathModulusEvent (d := d) T ε n) := by
  unfold pathModulusEvent
  simp_rw [Set.ofPred_forall]
  exact isClosed_iInter fun s ↦ isClosed_iInter fun _ ↦
    isClosed_iInter fun t ↦ isClosed_iInter fun _ ↦ isClosed_iInter fun _ ↦
      isClosed_le (by fun_prop) continuous_const

lemma monotone_pathModulusEvent {d : ℕ} (T : ℝ≥0) (ε : ℝ) :
    Monotone (pathModulusEvent (d := d) T ε) := by
  intro n m hnm ω hω s hs t ht hst
  apply hω s hs t ht
  exact hst.trans (one_div_le_one_div_of_le (by positivity)
    (by exact_mod_cast Nat.add_le_add_right hnm 1))

lemma iUnion_pathModulusEvent {d : ℕ} (T : ℝ≥0) {ε : ℝ} (hε : 0 < ε) :
    (⋃ n : ℕ, pathModulusEvent (d := d) T ε n) = univ := by
  apply eq_univ_of_forall
  intro ω
  obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuousOn_iff.mp
    (isCompact_Icc.uniformContinuousOn_of_continuous
      (ω.continuous.continuousOn : ContinuousOn ω (Icc 0 T))) ε hε
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / δ)
  have hsmall : 1 / (n + 1 : ℝ) < δ := by
    rw [div_lt_iff₀ (by positivity : 0 < (n : ℝ) + 1)]
    have hlarge : 1 < (n : ℝ) * δ := (div_lt_iff₀ hδpos).mp hn
    nlinarith
  apply mem_iUnion.mpr
  refine ⟨n, fun s hs t ht hst ↦ (hδ s hs t ht (hst.trans_lt hsmall)).le⟩

/-- A single deterministic time mesh controls the modulus outside a set of
arbitrarily small probability. This applies uniformly to all translated starts. -/
theorem measure_compl_pathModulusEvent_tendsto_zero {d : ℕ}
    (μ : Measure (BrownianPath d)) [IsFiniteMeasure μ] (T : ℝ≥0)
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ ↦ μ (pathModulusEvent T ε n)ᶜ) atTop (𝓝 0) := by
  have hanti : Antitone (fun n : ℕ ↦ (pathModulusEvent (d := d) T ε n)ᶜ) := by
    intro n m hnm ω hω hgood
    exact hω ((monotone_pathModulusEvent T ε) hnm hgood)
  have hinter : (⋂ n : ℕ, (pathModulusEvent (d := d) T ε n)ᶜ) = ∅ := by
    rw [← compl_iUnion, iUnion_pathModulusEvent T hε, compl_univ]
  have hlim := tendsto_measure_iInter_atTop (μ := μ)
    (fun n ↦ (isClosed_pathModulusEvent (d := d) T ε n).measurableSet.compl.nullMeasurableSet)
    hanti ⟨0, measure_ne_top _ _⟩
  simpa only [hinter, measure_empty, Function.comp_def] using hlim

end BouRabeeGwynne
