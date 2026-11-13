/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.PlaneCoordinateMartingale at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.LocalMartingaleCombination
import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace

/-!
# Plane-valued local martingales from their two coordinates

The bracket clause `IsLocallySquareIntegrableMartingale P F M` of
`Limit/CanonicalBracketClauses.OrdinaryEdgeBracketClauses` is stated for the
plane-valued process `M : ℝ≥0 → Ω → Plane`, `Plane = EuclideanSpace ℝ (Fin 2)`, while
every martingale producer of `Forms/` is scalar.  This module passes from the two
scalar coordinate processes `fun t ω => M t ω i` to `M`:

* `stronglyMeasurable_euclidean_of_coords` — measurability from the coordinates
  (the Borel σ-algebra of `PiLp` is the product one);
* `martingale_euclidean_of_coords` — the martingale property, by testing the
  set-integral identity coordinatewise (`eval_integral_piLp`);
* `isLocallySquareIntegrableMartingale_euclidean_of_coords` — the localized square
  integrable property, with the pointwise minimum of the two coordinate localizers as
  the common localizing sequence (`Limit/LocalMartingaleCombination`).

Path regularity enters only through the further stopping of each coordinate at the
other coordinate's localizer, exactly as in `LocalMartingaleCombination`.  Nothing
here mentions the reflected walk.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.PlaneCoordinateMartingale

open ReflectedGMS.LocalMartingaleCombination

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- The plane as the concrete `PiLp` type used throughout the project. -/
local notation "Plane₂" => EuclideanSpace ℝ (Fin 2)

/-! ## Measurability and integrability from the coordinates -/

/-- Strong measurability of a plane-valued function from that of its coordinates, for
any σ-algebra on the source. -/
theorem stronglyMeasurable_euclidean_of_coords {m' : MeasurableSpace Ω}
    {f : Ω → Plane₂} (hf : ∀ i : Fin 2, StronglyMeasurable[m'] (fun ω => f ω i)) :
    StronglyMeasurable[m'] f := by
  apply Measurable.stronglyMeasurable
  have hg : Measurable[m'] (fun ω => WithLp.ofLp (f ω)) :=
    measurable_pi_iff.2 fun i => (hf i).measurable
  exact (WithLp.measurable_toLp 2 (Fin 2 → ℝ)).comp hg

/-- Right continuity of a plane-valued path passes to each coordinate path. -/
theorem isRightContinuous_coord {Z : ℝ≥0 → Plane₂} (hZ : IsRightContinuous Z) (i : Fin 2) :
    IsRightContinuous (fun t => Z t i) :=
  hZ.continuous_comp (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) i)

/-! ## The martingale property from the coordinates -/

/-- **A plane-valued process whose two coordinates are martingales is a martingale.**
The set-integral characterization of the conditional expectation is verified
coordinatewise. -/
theorem martingale_euclidean_of_coords
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 m}
    {M : ℝ≥0 → Ω → Plane₂}
    (hM : ∀ i : Fin 2, Martingale (fun t ω => M t ω i) F P) :
    Martingale M F P := by
  have hadapt : StronglyAdapted F M := fun t =>
    stronglyMeasurable_euclidean_of_coords fun i => (hM i).stronglyAdapted t
  have hint : ∀ t, Integrable (M t) P := fun t =>
    integrable_piLp_iff.2 fun i => (hM i).integrable t
  refine ⟨hadapt, fun s t hst => ?_⟩
  refine (ae_eq_condExp_of_forall_setIntegral_eq (F.le s) (hint t)
    (fun _ _ _ => (hint s).integrableOn) (fun A hA _ => ?_)
    (hadapt s).aestronglyMeasurable).symm
  apply PiLp.ext
  intro i
  rw [eval_integral_piLp (fun i => ((hM i).integrable s).integrableOn),
    eval_integral_piLp (fun i => ((hM i).integrable t).integrableOn)]
  exact (hM i).setIntegral_eq hst hA

/-! ## The localized square-integrable property from the coordinates -/

/-- The coordinates of the exact localization of a plane-valued process are the exact
localizations of its coordinates. -/
theorem stoppedProcess_indicator_coord
    (M : ℝ≥0 → Ω → Plane₂) (ρ : Ω → WithTop ℝ≥0) (i : Fin 2) (t : ℝ≥0) (ω : Ω) :
    stoppedProcess (fun t => {ω | ⊥ < ρ ω}.indicator (M t)) ρ t ω i =
      stoppedProcess (fun t => {ω | ⊥ < ρ ω}.indicator (fun ω => M t ω i)) ρ t ω := by
  simp only [stoppedProcess, Set.indicator]
  split_ifs <;> simp

/-- **A plane-valued process whose two coordinates are locally square-integrable
martingales is one**, localized by the pointwise minimum of the two coordinate
localizers.  Almost-sure right continuity of the paths is needed for the further
stopping of each coordinate. -/
theorem isLocallySquareIntegrableMartingale_euclidean_of_coords
    {P : Measure Ω} [IsFiniteMeasure P] {F : Filtration ℝ≥0 m}
    {M : ℝ≥0 → Ω → Plane₂}
    (hM : ∀ i : Fin 2,
      MartingaleIngredients.IsLocallySquareIntegrableMartingale P F (fun t ω => M t ω i))
    (hnull : ∀ (t : ℝ≥0) (A : Set Ω), P A = 0 → MeasurableSet[F t] A)
    (hr : ∀ᵐ ω ∂P, IsRightContinuous (fun t => M t ω)) :
    MartingaleIngredients.IsLocallySquareIntegrableMartingale P F M := by
  have hri : ∀ i : Fin 2, ∀ᵐ ω ∂P, IsRightContinuous (fun t => M t ω i) := fun i =>
    hr.mono fun ω hω => isRightContinuous_coord hω i
  refine ⟨fun t => stronglyMeasurable_euclidean_of_coords fun i => (hM i).1 t, ?_⟩
  let σ := (hM 0).2.localSeq
  let τ := (hM 1).2.localSeq
  refine ⟨fun n ω => min (σ n ω) (τ n ω), ?_, fun n => ?_⟩
  · exact (hM 0).2.isLocalizingSequence_localSeq.min (hM 1).2.isLocalizingSequence_localSeq
  · have key : ∀ i : Fin 2,
        Martingale (stoppedProcess (fun t => {ω | ⊥ < min (σ n ω) (τ n ω)}.indicator
            (fun ω => M t ω i)) (fun ω => min (σ n ω) (τ n ω))) F P ∧
        ∀ t, MemLp (stoppedProcess (fun t => {ω | ⊥ < min (σ n ω) (τ n ω)}.indicator
            (fun ω => M t ω i)) (fun ω => min (σ n ω) (τ n ω)) t) 2 P := by
      intro i
      match i with
      | 0 => exact ⟨martingale_indicator_stoppedProcess_of_eq_min (fun ω => rfl)
            ((hM 1).2.isLocalizingSequence_localSeq.isStoppingTime n) hnull (hri 0)
            ((hM 0).2.stoppedProcess_localSeq n).1,
          memLp_two_indicator_stoppedProcess_of_eq_min (fun ω => rfl)
            ((hM 1).2.isLocalizingSequence_localSeq.isStoppingTime n) (hri 0)
            ((hM 0).2.stoppedProcess_localSeq n).1 ((hM 0).2.stoppedProcess_localSeq n).2⟩
      | 1 => exact ⟨martingale_indicator_stoppedProcess_of_eq_min (fun ω => min_comm _ _)
            ((hM 0).2.isLocalizingSequence_localSeq.isStoppingTime n) hnull (hri 1)
            ((hM 1).2.stoppedProcess_localSeq n).1,
          memLp_two_indicator_stoppedProcess_of_eq_min (fun ω => min_comm _ _)
            ((hM 0).2.isLocalizingSequence_localSeq.isStoppingTime n) (hri 1)
            ((hM 1).2.stoppedProcess_localSeq n).1 ((hM 1).2.stoppedProcess_localSeq n).2⟩
    have hcoordM : ∀ i : Fin 2, Martingale (fun t ω =>
        stoppedProcess (fun t => {ω | ⊥ < min (σ n ω) (τ n ω)}.indicator (M t))
          (fun ω => min (σ n ω) (τ n ω)) t ω i) F P := by
      intro i
      have heq : (fun t ω =>
          stoppedProcess (fun t => {ω | ⊥ < min (σ n ω) (τ n ω)}.indicator (M t))
            (fun ω => min (σ n ω) (τ n ω)) t ω i) =
          stoppedProcess (fun t => {ω | ⊥ < min (σ n ω) (τ n ω)}.indicator
            (fun ω => M t ω i)) (fun ω => min (σ n ω) (τ n ω)) := by
        funext t ω
        exact stoppedProcess_indicator_coord M _ i t ω
      rw [heq]
      exact (key i).1
    have hcoordL : ∀ (i : Fin 2) (t : ℝ≥0), MemLp (fun ω =>
        stoppedProcess (fun t => {ω | ⊥ < min (σ n ω) (τ n ω)}.indicator (M t))
          (fun ω => min (σ n ω) (τ n ω)) t ω i) 2 P := by
      intro i t
      have heq : (fun ω =>
          stoppedProcess (fun t => {ω | ⊥ < min (σ n ω) (τ n ω)}.indicator (M t))
            (fun ω => min (σ n ω) (τ n ω)) t ω i) =
          stoppedProcess (fun t => {ω | ⊥ < min (σ n ω) (τ n ω)}.indicator
            (fun ω => M t ω i)) (fun ω => min (σ n ω) (τ n ω)) t := by
        funext ω
        exact stoppedProcess_indicator_coord M _ i t ω
      rw [heq]
      exact (key i).2 t
    exact ⟨martingale_euclidean_of_coords hcoordM,
      fun t => memLp_piLp_iff.2 fun i => hcoordL i t⟩

end ReflectedGMS.PlaneCoordinateMartingale
