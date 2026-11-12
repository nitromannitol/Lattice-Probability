/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.ItoLite.OptionalStopping at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.HittingTime
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
Blueprint nodes IL-4 and IL-5 (`blueprint/THM11_BLUEPRINT.md`, §3 and §10).

Time is `ℝ≥0`, `𝓕` is an arbitrary filtration, stopping times take values in
`WithTop ℝ≥0` (mathlib's convention).

* `ItoLite.integral_mul_stoppedValue_eq_of_le` : optional sampling for a bounded martingale
  with continuous paths at a bounded stopping time, tested against bounded
  `𝓕_σ`-measurable functions (dyadic approximation from the right).
* `ItoLite.martingale_stoppedProcess_of_continuous` (IL-4) : a bounded martingale with
  continuous paths, stopped at a stopping time, is a martingale.
* `ItoLite.isStoppingTime_hittingBtwn_of_isClosed` (IL-4) : the hitting time of a closed set by
  a continuous adapted process is a stopping time.
* `ItoLite.martingale_glue` (IL-5) : `ξ (M_t - M_{t ∧ ρ})` is a martingale for bounded
  `𝓕_ρ`-measurable `ξ`.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace QuantumZipper
namespace ItoLite

/-! ### Dyadic approximation from the right -/

/-- The dyadic ceiling `⌈r 2^n⌉ / 2^n`. -/
noncomputable def dyadicCeil (n : ℕ) (r : ℝ≥0) : ℝ≥0 :=
  (⌈r * 2 ^ n⌉₊ : ℝ≥0) / 2 ^ n

lemma dyadicCeil_le_iff (n : ℕ) (r u : ℝ≥0) :
    dyadicCeil n r ≤ u ↔ r ≤ (⌊u * 2 ^ n⌋₊ : ℝ≥0) / 2 ^ n := by
  have h2 : (0 : ℝ≥0) < 2 ^ n := pow_pos two_pos n
  unfold dyadicCeil
  rw [div_le_iff₀ h2, le_div_iff₀ h2, ← Nat.le_floor_iff zero_le, Nat.ceil_le]

lemma le_dyadicCeil (n : ℕ) (r : ℝ≥0) : r ≤ dyadicCeil n r := by
  have h2 : (0 : ℝ≥0) < 2 ^ n := pow_pos two_pos n
  unfold dyadicCeil
  rw [le_div_iff₀ h2]
  exact Nat.le_ceil _

lemma dyadicCeil_le_add (n : ℕ) (r : ℝ≥0) : dyadicCeil n r ≤ r + (1 / 2) ^ n := by
  have h2 : (0 : ℝ≥0) < 2 ^ n := pow_pos two_pos n
  unfold dyadicCeil
  rw [div_le_iff₀ h2, add_mul, one_div_pow, div_mul_cancel₀ _ h2.ne']
  exact (Nat.ceil_lt_add_one zero_le).le

lemma floor_div_le (n : ℕ) (u : ℝ≥0) : (⌊u * 2 ^ n⌋₊ : ℝ≥0) / 2 ^ n ≤ u := by
  have h2 : (0 : ℝ≥0) < 2 ^ n := pow_pos two_pos n
  rw [div_le_iff₀ h2]
  exact Nat.floor_le zero_le

lemma tendsto_dyadicCeil (r : ℝ≥0) : Tendsto (fun n => dyadicCeil n r) atTop (𝓝 r) := by
  have h : Tendsto (fun n : ℕ => r + (1 / 2 : ℝ≥0) ^ n) atTop (𝓝 (r + 0)) :=
    tendsto_const_nhds.add
      (NNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num))
  rw [add_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h
    (fun n => le_dyadicCeil n r) (fun n => dyadicCeil_le_add n r)

variable {Ω : Type*} {m : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 m}

/-! ### Boundedness and integrability helpers -/

lemma integrable_of_bound_abs [IsFiniteMeasure P] {f : Ω → ℝ} (hf : StronglyMeasurable f)
    {K : ℝ} (hK : ∀ ω, |f ω| ≤ K) : Integrable f P :=
  Integrable.of_bound hf.aestronglyMeasurable K
    (ae_of_all _ fun ω => by simpa [Real.norm_eq_abs] using hK ω)

/-! ### Optional sampling at bounded stopping times -/

/-! ### IL-4: stopped martingales -/

lemma setIntegral_eq_integral_indicator_one_mul {A : Set Ω} (hA : MeasurableSet A)
    (f : Ω → ℝ) : ∫ ω in A, f ω ∂P = ∫ ω, A.indicator 1 ω * f ω ∂P := by
  rw [← integral_indicator hA]
  congr 1
  ext ω
  by_cases h : ω ∈ A <;> simp [h]

/-! ### IL-4: hitting times of closed sets -/

/-- **IL-4 (hitting times).** The hitting time of a closed set by a continuous adapted process,
capped at `T`, is a stopping time. -/
theorem isStoppingTime_hittingBtwn_of_isClosed {β : Type*} [PseudoMetricSpace β]
    [MeasurableSpace β] [OpensMeasurableSpace β] {U : ℝ≥0 → Ω → β} (hU : Adapted 𝓕 U)
    (hc : ∀ ω, Continuous (U · ω)) {K : Set β} (hK : IsClosed K) (T : ℝ≥0) :
    IsStoppingTime 𝓕 (fun ω => ((hittingBtwn U K 0 T ω : ℝ≥0) : WithTop ℝ≥0)) := by
  intro u
  simp only [WithTop.coe_le_coe]
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · simp only [hittingBtwn_empty]
    exact MeasurableSet.const _
  by_cases hTu : T ≤ u
  · have : {ω | hittingBtwn U K 0 T ω ≤ u} = Set.univ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      exact (hittingBtwn_le ω).trans hTu
    rw [this]; exact MeasurableSet.univ
  have huT : u < T := lt_of_not_ge hTu
  -- step 1: `hit ≤ u` iff the path meets `K` during `[0, u]`
  have step1 : ∀ ω, hittingBtwn U K 0 T ω ≤ u ↔ ∃ j ∈ Set.Icc 0 u, U j ω ∈ K := by
    intro ω
    constructor
    · intro h
      by_cases hex : ∃ j ∈ Set.Icc 0 T, U j ω ∈ K
      · set S : Set ℝ≥0 := Set.Icc 0 T ∩ {i | U i ω ∈ K} with hS
        have hSc : IsClosed S := isClosed_Icc.inter (hK.preimage (hc ω))
        have hSne : S.Nonempty := by
          obtain ⟨j, hj, hjK⟩ := hex; exact ⟨j, hj, hjK⟩
        have hmem := hSc.csInf_mem hSne (OrderBot.bddBelow S)
        have heq : hittingBtwn U K 0 T ω = sInf S := by
          simp only [hittingBtwn, hex, ↓reduceIte, hS]
        rw [heq] at h
        exact ⟨sInf S, ⟨zero_le, h⟩, hmem.2⟩
      · have heq : hittingBtwn U K 0 T ω = T := by
          simp only [hittingBtwn, hex, ↓reduceIte]
        rw [heq] at h
        exact absurd h (not_le.mpr huT)
    · rintro ⟨j, hj, hjK⟩
      exact (hittingBtwn_le_of_mem hj.1 (hj.2.trans huT.le) hjK).trans hj.2
  -- step 2: a countable description
  obtain ⟨D, hDc, hDsub, hDdense⟩ :=
    TopologicalSpace.exists_countable_dense_subset (Set.Icc (0 : ℝ≥0) u)
  have step2 : ∀ ω, (∃ j ∈ Set.Icc 0 u, U j ω ∈ K) ↔
      ∀ k : ℕ, ∃ q ∈ D, Metric.infDist (U q ω) K < 1 / ((k : ℝ) + 1) := by
    intro ω
    constructor
    · rintro ⟨j, hj, hjK⟩ k
      have hε : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
      obtain ⟨δ, hδ, hδU⟩ := Metric.continuous_iff.mp (hc ω) j _ hε
      obtain ⟨q, hqD, hq⟩ := Metric.mem_closure_iff.mp (hDdense hj) δ hδ
      refine ⟨q, hqD, ?_⟩
      calc Metric.infDist (U q ω) K ≤ dist (U q ω) (U j ω) := Metric.infDist_le_dist_of_mem hjK
        _ < _ := hδU q (by rw [dist_comm]; exact hq)
    · intro h
      choose q hqD hq using h
      obtain ⟨a, ha, φ, hφ, hlim⟩ :=
        (isCompact_Icc (a := (0 : ℝ≥0)) (b := u)).tendsto_subseq (fun n => hDsub (hqD n))
      have h1 : Tendsto (fun n => Metric.infDist (U (q (φ n)) ω) K) atTop
          (𝓝 (Metric.infDist (U a ω) K)) :=
        (((Metric.continuous_infDist_pt K).comp (hc ω)).tendsto a).comp hlim
      have h2 : Tendsto (fun n => 1 / ((φ n : ℝ) + 1)) atTop (𝓝 0) :=
        (tendsto_one_div_add_atTop_nhds_zero_nat).comp hφ.tendsto_atTop
      have hle : Metric.infDist (U a ω) K ≤ 0 :=
        le_of_tendsto_of_tendsto' h1 h2 (fun n => (hq (φ n)).le)
      refine ⟨a, ha, ?_⟩
      rw [hK.mem_iff_infDist_zero hKne]
      exact le_antisymm hle Metric.infDist_nonneg
  have hset : {ω | hittingBtwn U K 0 T ω ≤ u} =
      ⋂ k : ℕ, ⋃ q ∈ D, {ω | Metric.infDist (U q ω) K < 1 / ((k : ℝ) + 1)} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion, exists_prop]
    exact (step1 ω).trans (step2 ω)
  rw [hset]
  refine MeasurableSet.iInter fun k => MeasurableSet.biUnion hDc fun q hq => ?_
  have hUq : Measurable[𝓕 u] (U q) := (hU q).mono (𝓕.mono (hDsub hq).2) le_rfl
  exact measurableSet_lt ((Metric.continuous_infDist_pt K).measurable.comp hUq) measurable_const

/-! ### IL-5: the glue lemma -/

end ItoLite
end QuantumZipper
