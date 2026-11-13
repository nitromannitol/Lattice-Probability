/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.PredictableJumpOccupation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.AdaptedJumpOccupation
import LatticeProb.Bonanno.ReflectedGMS.Process.MartingaleIngredients
import Mathlib.MeasureTheory.Function.Piecewise
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Function
open scoped ENNReal NNReal Topology

namespace ReflectedGMS

open ReflectedWalk ReflectedWalk.Theorem16 FullNetworkForm

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V] [DecidableEq V]

private noncomputable def predictableGridWidth (n : ℕ) : ℝ≥0 :=
  ⟨1 / (n + 1 : ℝ), by positivity⟩

private theorem predictableGridWidth_pos (n : ℕ) : 0 < predictableGridWidth n := by
  rw [← NNReal.coe_pos]
  change (0 : ℝ) < 1 / (n + 1 : ℝ)
  positivity

private def predictableGridCell (n : ℕ) : ℕ → Set ℝ≥0
  | 0 => {0}
  | k + 1 => Ioc (k * predictableGridWidth n) ((k + 1) * predictableGridWidth n)

private theorem predictableGridCell_pairwise (n : ℕ) :
    Pairwise (Disjoint on predictableGridCell n) := by
  rintro i j hij
  change Disjoint (predictableGridCell n i) (predictableGridCell n j)
  rw [disjoint_left]
  intro t hti htj
  rcases i with _ | i <;> rcases j with _ | j
  · exact hij rfl
  · simp only [predictableGridCell, mem_singleton_iff, mem_Ioc] at hti htj
    subst t
    exact (not_lt_of_ge (show (0 : ℝ≥0) ≤ _ from bot_le)) htj.1
  · simp only [predictableGridCell, mem_singleton_iff, mem_Ioc] at hti htj
    subst t
    exact (not_lt_of_ge (show (0 : ℝ≥0) ≤ _ from bot_le)) hti.1
  · simp only [predictableGridCell, mem_Ioc] at hti htj
    rcases lt_or_gt_of_ne hij with hij' | hji'
    · have hle : (i + 1) * predictableGridWidth n ≤
          j * predictableGridWidth n := by
        have hik : i + 1 ≤ j := by omega
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hik) bot_le
      exact (not_lt_of_ge (hti.2.trans hle)) htj.1
    · have hle : (j + 1) * predictableGridWidth n ≤
          i * predictableGridWidth n := by
        have hjk : j + 1 ≤ i := by omega
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hjk) bot_le
      exact (not_lt_of_ge (htj.2.trans hle)) hti.1

private theorem predictableGridCell_nonempty (n i : ℕ) :
    (predictableGridCell n i).Nonempty := by
  rcases i with _ | i
  · exact ⟨0, rfl⟩
  · refine ⟨(i + 1) * predictableGridWidth n, ?_, le_rfl⟩
    exact mul_lt_mul_of_pos_right (by exact_mod_cast Nat.lt_succ_self i)
      (predictableGridWidth_pos n)

private theorem predictableGridCell_cover (n : ℕ) (t : ℝ≥0) :
    ∃ i, t ∈ predictableGridCell n i := by
  by_cases ht : t = 0
  · exact ⟨0, ht⟩
  let P : ℕ → Prop := fun i ↦ t ≤ i * predictableGridWidth n
  have hP : ∃ i, P i := by
    obtain ⟨i, hi⟩ := exists_nat_gt ((t : ℝ) / predictableGridWidth n)
    refine ⟨i, ?_⟩
    change t ≤ (i : ℝ≥0) * predictableGridWidth n
    rw [← NNReal.coe_le_coe]
    calc
      (t : ℝ) = ((t : ℝ) / predictableGridWidth n) * predictableGridWidth n := by
        rw [div_mul_cancel₀]
        exact_mod_cast (predictableGridWidth_pos n).ne'
      _ ≤ (i : ℝ) * predictableGridWidth n :=
        mul_le_mul_of_nonneg_right hi.le (NNReal.coe_nonneg _)
  have hi : P (Nat.find hP) := Nat.find_spec hP
  have hi0 : Nat.find hP ≠ 0 := by
    intro hieq
    have ht0 : t ≤ 0 := by simpa [P, hieq] using hi
    exact ht (nonpos_iff_eq_zero.mp ht0)
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hi0
  refine ⟨k + 1, ?_, ?_⟩
  · exact lt_of_not_ge (Nat.find_min hP (hk ▸ Nat.lt_succ_self k))
  · simpa [P, hk] using hi

private noncomputable def predictableGridPartition (n : ℕ) :
    IndexedPartition (predictableGridCell n) :=
  IndexedPartition.mk' _ (predictableGridCell_pairwise n)
    (predictableGridCell_nonempty n) (predictableGridCell_cover n)

private noncomputable def predictableGridTime (n : ℕ) : ℕ → ℝ≥0
  | 0 => 0
  | k + 1 => k * predictableGridWidth n

private noncomputable def predictableStep
    {Ω : Type*} [MeasurableSpace Ω] (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    (a : ℝ≥0 → Ω → ℝ) (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  a (predictableGridTime n ((predictableGridPartition n).index t)) ω

private theorem stronglyMeasurable_predictableStep
    {Ω : Type*} [MeasurableSpace Ω] (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    {a : ℝ≥0 → Ω → ℝ} (ha : StronglyAdapted F a) (n : ℕ) :
    StronglyMeasurable[F.predictable] (Function.uncurry (predictableStep F a n)) := by
  apply Measurable.stronglyMeasurable
  intro B hB
  rw [show Function.uncurry (predictableStep F a n) ⁻¹' B =
      ⋃ i : ℕ, predictableGridCell n i ×ˢ
        (a (predictableGridTime n i) ⁻¹' B) by
    ext p
    simp only [mem_preimage, mem_iUnion, mem_prod]
    constructor
    · intro hp
      refine ⟨(predictableGridPartition n).index p.1,
        (predictableGridPartition n).mem_index p.1, ?_⟩
      exact hp
    · rintro ⟨i, hpi, hpB⟩
      have hi := (predictableGridPartition n).mem_iff_index_eq.mp hpi
      change a (predictableGridTime n ((predictableGridPartition n).index p.1)) p.2 ∈ B
      rw [hi]
      exact hpB]
  apply MeasurableSet.iUnion
  intro i
  rcases i with _ | i
  · exact measurableSet_predictable_singleton_bot_prod ((ha 0).measurable hB)
  · exact measurableSet_predictable_Ioc_prod
      (i * predictableGridWidth n) ((i + 1) * predictableGridWidth n)
      ((ha (i * predictableGridWidth n)).measurable hB)

private theorem tendsto_predictableGridTime (t : ℝ≥0) :
    Tendsto (fun n ↦ predictableGridTime n ((predictableGridPartition n).index t))
      atTop (𝓝 t) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hwidth : Tendsto (fun n : ℕ ↦ (1 / (n + 1 : ℝ))) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hwidth ε hε
  refine ⟨N, fun n hnN ↦ ?_⟩
  have hn : (1 / (n + 1 : ℝ)) < ε := by
    simpa [Real.dist_eq, abs_of_pos (show (0 : ℝ) < n + 1 by positivity)] using hN n hnN
  have hmem := (predictableGridPartition n).mem_index t
  rcases hidx : (predictableGridPartition n).index t with _ | k
  · simp only [hidx, predictableGridCell, mem_singleton_iff] at hmem
    simpa [predictableGridTime, hmem] using hε
  · simp only [hidx, predictableGridCell, mem_Ioc] at hmem
    simp only [predictableGridTime]
    rw [NNReal.dist_eq, abs_of_nonpos]
    · rw [neg_sub]
      change (t : ℝ) - (k : ℝ) * (1 / (n + 1 : ℝ)) < ε
      have hu := hmem.2
      have huR : (t : ℝ) ≤ (((k + 1 : ℕ) : ℝ≥0) * predictableGridWidth n : ℝ≥0) := by
        exact_mod_cast hu
      have heq : ((((k + 1 : ℕ) : ℝ≥0) * predictableGridWidth n : ℝ≥0) : ℝ) =
          (k + 1 : ℝ) * (1 / (n + 1 : ℝ)) := by
        rw [NNReal.coe_mul]
        congr 1
        norm_num
      rw [heq] at huR
      nlinarith
    · rw [sub_nonpos]
      exact_mod_cast hmem.1.le

/-- A real-valued continuous strongly adapted process on nonnegative real time
is predictable.  This is the standard left-grid approximation theorem absent
from the pinned predictable-process API. -/
theorem stronglyPredictable_of_continuous_stronglyAdapted
    {Ω : Type*} [MeasurableSpace Ω] (F : Filtration ℝ≥0 ‹MeasurableSpace Ω›)
    {a : ℝ≥0 → Ω → ℝ} (ha : StronglyAdapted F a)
    (hcont : ∀ ω, Continuous (fun t ↦ a t ω)) :
    IsStronglyPredictable F a := by
  unfold IsStronglyPredictable
  refine stronglyMeasurable_of_tendsto (u := (atTop : Filter ℕ))
    (f := fun n ↦ Function.uncurry (predictableStep F a n)) ?_ ?_
  · exact fun n ↦ stronglyMeasurable_predictableStep F ha n
  · rw [tendsto_pi_nhds]
    intro p
    exact Filter.Tendsto.comp (hcont p.2).continuousAt
      (tendsto_predictableGridTime p.1)

/-- Every bounded truncation of the jump occupation is predictable in the
uncompleted natural filtration. -/
theorem stronglyPredictable_boundedTruncatedJumpOccupation
    (PF : ProcessFamily V) (G : ConductanceGraph V) (m : V → ℝ)
    (u : V → ℝ) (n : ℕ) :
    IsStronglyPredictable PF.naturalFiltration
      (boundedStateOccupationVersion PF
        (truncatedStateVertexCarreDuChamp G m u n)) := by
  apply stronglyPredictable_of_continuous_stronglyAdapted PF.naturalFiltration
    (stronglyAdapted_boundedStateOccupationVersion PF
      (truncatedStateVertexCarreDuChamp G m u n))
  intro ω
  exact continuous_boundedStateOccupationVersion PF
    (truncatedStateVertexCarreDuChamp G m u n)
    (C := (n : ℝ)) (fun q ↦ by
      simpa [Real.norm_eq_abs] using
        norm_truncatedStateVertexCarreDuChamp_le G m u n q) ω

/-- The canonical real-valued jump occupation is predictable in the actual,
uncompleted natural filtration. -/
theorem stronglyPredictable_adaptedJumpOccupation
    (PF : ProcessFamily V) (G : ConductanceGraph V) (m : V → ℝ)
    (u : V → ℝ) :
    IsStronglyPredictable PF.naturalFiltration
      (adaptedJumpOccupation PF G m u) := by
  unfold IsStronglyPredictable
  apply Measurable.stronglyMeasurable
  exact ENNReal.measurable_toReal.comp <| Measurable.iSup fun n ↦
    (stronglyPredictable_boundedTruncatedJumpOccupation PF G m u n).measurable.ennreal_ofReal

private theorem predictable_mono
    {Ω : Type*} [MeasurableSpace Ω]
    {F F' : Filtration ℝ≥0 ‹MeasurableSpace Ω›} (hFF' : F ≤ F') :
    F.predictable ≤ F'.predictable := by
  apply MeasurableSpace.generateFrom_le
  rintro s (⟨A, hA, rfl⟩ | ⟨i, A, hA, rfl⟩)
  · exact measurableSet_predictable_singleton_bot_prod (hFF' 0 A hA)
  · exact measurableSet_predictable_Ioi_prod (hFF' i A hA)

/-- The same canonical occupation is predictable after passing to the
right-continuous natural filtration. -/
theorem stronglyPredictable_rightCont_adaptedJumpOccupation
    (PF : ProcessFamily V) (G : ConductanceGraph V) (m : V → ℝ)
    (u : V → ℝ) :
    IsStronglyPredictable PF.naturalFiltration.rightCont
      (adaptedJumpOccupation PF G m u) := by
  exact (stronglyPredictable_adaptedJumpOccupation PF G m u).mono
    (predictable_mono PF.naturalFiltration.le_rightCont)

@[simp] theorem adaptedJumpOccupation_zero
    (PF : ProcessFamily V) (G : ConductanceGraph V) (m : V → ℝ)
    (u : V → ℝ) (ω : PF.Ω) :
    adaptedJumpOccupation PF G m u 0 ω = 0 := by
  simp [adaptedJumpOccupation, boundedStateOccupationVersion]

theorem adaptedJumpOccupation_nonneg
    (PF : ProcessFamily V) (G : ConductanceGraph V) (m : V → ℝ)
    (u : V → ℝ) (t : ℝ≥0) (ω : PF.Ω) :
    0 ≤ adaptedJumpOccupation PF G m u t ω :=
  ENNReal.toReal_nonneg

/-- Under every reflected starting law, the canonical predictable occupation
starts at zero and has continuous finite-variation paths on every finite
horizon. -/
theorem adaptedJumpOccupation_ae_zero_continuous_boundedVariation
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {u : V → ℝ} (hu : G.HasFiniteEnergy u)
    (z : V) :
    ∀ᵐ ω ∂PF.P z,
      adaptedJumpOccupation PF G m u 0 ω = 0 ∧
      Continuous (fun t ↦ adaptedJumpOccupation PF G m u t ω) ∧
      ∀ T : ℝ≥0, BoundedVariationOn
        (fun t ↦ adaptedJumpOccupation PF G m u t ω) (Icc 0 T) := by
  filter_upwards [adaptedJumpOccupation_ae_eq_all_continuous_monotone
      h hG hm hmsum hu z] with ω hω
  refine ⟨adaptedJumpOccupation_zero PF G m u ω, hω.2.1, ?_⟩
  intro T
  have hloc := hω.2.2.monotoneOn (univ : Set ℝ≥0) |>.locallyBoundedVariationOn
  simpa using hloc (a := (0 : ℝ≥0)) (b := T) (mem_univ _) (mem_univ _)

end ReflectedGMS
