import Mathlib
import LatticeProb.Gauss.GFF
import LatticeProb.LQG.LQGMeasure
import LatticeProb.Topology.PlaneTopology
import LatticeProb.LQG.LQGMeasureLocality

/-! # Square measurability of the γ-Liouville quantum gravity area measure

Adapted from the Lean formalization accompanying [Harmonic balls in Liouville quantum gravity, arXiv:2208.11795],
Lemma 11.10 (the measurability of the LQG area measure on closed dyadic squares). The general statement is given in
terms of this library and Mathlib.

Route (the argument of the source, restated in this library's terms):

1. Locality of the γ-LQG measure (Duplantier-Sheffield 2011, Prop. 1.1 and the locality property of the Gaussian
   multiplicative chaos; Berestycki-Powell, *Gaussian free field, Liouville quantum gravity and Gaussian multiplicative
   chaos*): the input `LQGLocality` says that for every open `U`, the mass
   `μ(U)` is a.s. equal to a `σ(h|_U)`-measurable random variable. It is a hypothesis of the statements below.
2. Hence the open-set masses are a.e. measurable in the ambient σ-algebra (`aemeasurable_lqgMeasure_open`).
3. Pure measure theory, with no LQG content: for a random locally finite measure whose open-set masses are a.e.
   measurable, the Borel-set masses are a.e. measurable (`aemeasurable_measure_of_open_evaluations`, Dynkin induction from
   open sets along a π-system, and monotone limits along balls `B(0, n)`).
4. A closed dyadic square is closed, hence Borel (`isClosed_of_isClosedDyadicSquare`).

The γ-LQG definitions are those of module `LatticeProb.LQG.LQGMeasure` (`LatticeProb.LQG.IsLQGMeasureOfField`),
and the whole-plane field layer is that of module `LatticeProb.Gauss.GFF` (`LatticeProb.Gauss.IsWholePlaneGFF`,
`fieldSigmaAlgebra`).
-/

open LatticeProb.Gauss

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace LatticeProb.LQG

/-! ### Step 3: locally finite random measures with a.e. measurable open-set masses -/

/-- On a finite-mass open set `B`, almost-everywhere measurable open-set masses extend to the masses of `A ∩ B` for every
measurable `A` (Dynkin induction from open sets; `MeasurableSpace.induction_on_inter`). -/
theorem aemeasurable_measure_inter_open_of_open_evaluations
    {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] (P : Measure Ω) (μ : Ω → Measure X)
    (hopen : ∀ U : Set X, IsOpen U → AEMeasurable (fun ω => μ ω U) P)
    {B : Set X} (hB : IsOpen B) (hfin : ∀ᵐ ω ∂P, μ ω B ≠ ∞)
    (A : Set X) (hA : MeasurableSet A) :
    AEMeasurable (fun ω => μ ω (A ∩ B)) P := by
  refine MeasurableSpace.induction_on_inter BorelSpace.measurable_eq isPiSystem_isOpen
    (C := fun A _ => AEMeasurable (fun ω => μ ω (A ∩ B)) P) ?_ ?_ ?_ ?_ A hA
  · simp
  · intro U hU
    exact hopen _ (hU.inter hB)
  · intro U hU ih
    apply ((hopen B hB).sub ih).congr
    filter_upwards [hfin] with ω hω
    have hfin' : μ ω (U ∩ B) ≠ ∞ :=
      ne_top_of_le_ne_top hω (measure_mono Set.inter_subset_right)
    have heq : Uᶜ ∩ B = B \ (U ∩ B) := by ext x; simp [and_comm]
    rw [heq, measure_sdiff Set.inter_subset_right (hU.inter hB.measurableSet).nullMeasurableSet hfin']
    rfl
  · intro f hdisj hfm ih
    have hdisj' : Pairwise (Function.onFun Disjoint fun i => f i ∩ B) :=
      fun i j hij => (hdisj hij).mono Set.inter_subset_left Set.inter_subset_left
    have hm : AEMeasurable (fun ω => ∑' i : ℕ, μ ω (f i ∩ B)) P :=
      AEMeasurable.tsum (fun i => ih i)
    apply hm.congr
    filter_upwards [] with ω
    rw [Set.iUnion_inter, measure_iUnion hdisj' (fun i => (hfm i).inter hB.measurableSet)]

/-- Open-set masses of an a.s. locally finite random measure on `ℂ` determine the a.e. measurable masses of all Borel sets:
if `ω ↦ μ ω U` is a.e. measurable for every open `U`, and `μ ω` is locally finite for a.e. `ω`, then `ω ↦ μ ω A` is a.e.
measurable for every measurable `A`. -/
theorem aemeasurable_measure_of_open_evaluations
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ)
    (hopen : ∀ U : Set ℂ, IsOpen U → AEMeasurable (fun ω => μ ω U) P)
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω))
    (A : Set ℂ) (hA : MeasurableSet A) : AEMeasurable (fun ω => μ ω A) P := by
  let B : ℕ → Set ℂ := fun n => Metric.ball 0 n
  have hBopen : ∀ n, IsOpen (B n) := fun _ => Metric.isOpen_ball
  have hBfin : ∀ n, ∀ᵐ ω ∂P, μ ω (B n) ≠ ∞ := by
    intro n
    filter_upwards [hloc] with ω hω
    have : IsLocallyFiniteMeasure (μ ω) := hω
    exact measure_ball_ne_top
  have hm : AEMeasurable (fun ω => ⨆ n, μ ω (A ∩ B n)) P :=
    .iSup fun n => aemeasurable_measure_inter_open_of_open_evaluations P μ hopen
      (hBopen n) (hBfin n) A hA
  apply hm.congr
  filter_upwards [] with ω
  have hmono : Monotone (fun n => A ∩ B n) := by
    intro m n hmn
    exact Set.inter_subset_inter_right _ (Metric.ball_subset_ball (by exact_mod_cast hmn))
  rw [← hmono.measure_iUnion]
  simp only [← Set.inter_iUnion, B, Metric.iUnion_ball_nat, Set.inter_univ]

/-! ### Locality of the γ-LQG measure and the field σ-algebras -/

/-- The σ-algebra `σ(h|_U)` of the logarithmically shifted field is contained in the ambient σ-algebra: the pairings
`hC ω φ` with test functions are random variables (`IsWholePlaneGFF.measurable_pairing`), and the shift is a constant. -/
theorem fieldSigmaAlgebra_le_ambient {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc) (α₀ : ℝ) (U : Set ℂ) :
    fieldSigmaAlgebra α₀ hC U ≤ mΩ := by
  refine iSup₂_le fun φ hφ => ?_
  exact ((hGFF.measurable_pairing φ ⟨hφ.1, hφ.2.1, Set.subset_univ _⟩).sub_const _).comap_le

/-! ### Step 2 and the general statement -/

/-- Under locality, the mass of every open set is an a.e. measurable random variable in the ambient σ-algebra. -/
theorem aemeasurable_lqgMeasure_open {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGLocality P γ α₀ hC hcirc) {U : Set ℂ} (hU : IsOpen U) :
    AEMeasurable (fun ω => μ ω U) P := by
  obtain ⟨Y, hY, heq⟩ := hloc hGFF hγ hγ2 hα μ hμ U hU
  exact ((hY.mono (fieldSigmaAlgebra_le_ambient hGFF α₀ U) le_rfl).aemeasurable.congr
    (heq.mono fun _ h => h.symm))

/-- **General statement (Borel sets).** Under locality, the γ-LQG area measure `μ` of the field `h = h^ℂ - α₀ log |·|`
gives an a.e. measurable mass `ω ↦ μ_ω(A)` to every Borel set `A ⊆ ℂ`. -/
theorem aemeasurable_lqgMeasure_borel {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGLocality P γ α₀ hC hcirc) (A : Set ℂ) (hA : MeasurableSet A) :
    AEMeasurable (fun ω => μ ω A) P := by
  apply aemeasurable_measure_of_open_evaluations P μ
    (fun U hU => aemeasurable_lqgMeasure_open hγ hγ2 hα hGFF hμ hloc hU) ?_ A hA
  filter_upwards [hμ] with ω hω
  exact hω.isLocallyFiniteMeasure

/-- A closed dyadic square is a closed subset of `ℂ`. -/
theorem isClosed_of_isClosedDyadicSquare {S : Set ℂ} (hS : LatticeProb.Topology.IsClosedDyadicSquare S) :
    IsClosed S := by
  obtain ⟨n, j, k, rfl⟩ := hS
  unfold LatticeProb.Topology.closedDyadicSquare
  exact isClosed_Icc.reProdIm isClosed_Icc

/-- **General statement (closed dyadic squares).** Under locality, the γ-LQG area measure gives an a.e. measurable
mass `ω ↦ μ_ω(S)` to every closed dyadic square `S`. -/
theorem aemeasurable_lqgMeasure_closedDyadicSquare {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGLocality P γ α₀ hC hcirc) {S : Set ℂ} (hS : LatticeProb.Topology.IsClosedDyadicSquare S) :
    AEMeasurable (fun ω => μ ω S) P :=
  aemeasurable_lqgMeasure_borel hγ hγ2 hα hGFF hμ hloc S (isClosed_of_isClosedDyadicSquare hS).measurableSet

/-- **Square measurability without the locality hypothesis (circle-average link form).** The locality hypothesis of
`aemeasurable_lqgMeasure_closedDyadicSquare` is replaced by the GFF-relativised circle-average link `hlink`
(`LQGCircleAverageLink`), from which locality follows by `lqgLocality_of_circleLink` (module
`LatticeProb.LQG.LQGMeasureLocality`). The unconditional link is NOT proved here; under the whole-plane GFF premise it is
proved in the module `LatticeProb.LQG.LQGMeasureLocality2`. -/
theorem aemeasurable_lqgMeasure_closedDyadicSquare_of_circleLink {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {γ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hlink : IsWholePlaneGFF P hC hcirc → LQGCircleAverageLink P α₀ hC hcirc) {S : Set ℂ}
    (hS : LatticeProb.Topology.IsClosedDyadicSquare S) :
    AEMeasurable (fun ω => μ ω S) P :=
  aemeasurable_lqgMeasure_closedDyadicSquare hγ hγ2 hα hGFF hμ
    (lqgLocality_of_circleLink P γ α₀ hC hcirc hlink) hS

end LatticeProb.LQG
