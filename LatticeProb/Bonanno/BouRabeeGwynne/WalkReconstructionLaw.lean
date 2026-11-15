/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.WalkReconstructionLaw at commit fdb5cad17d11550228cf8dbaf6216e69fc3d2d82;
   imports and one deprecated proof lemma are adapted to the local library. -/
import LatticeProb.Bonanno.BouRabeeGwynne.WalkStoppedReconstruction
import LatticeProb.Bonanno.BouRabeeGwynne.ReconstructedLawComparison

/-! Terminated actual excursion prefixes recover the stopped walk law.
The only loss in replacing that law by the finite reconstruction is the
probability that the skeleton is still active. -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace BouRabeeGwynne.FiniteConductanceNetwork

variable {d : ℕ} {V J : Type*} [Fintype V] [MeasurableSpace V]
  [MeasurableSingletonClass V] [Countable J]
  [MeasurableSpace (Option J)] [MeasurableSingletonClass (Option J)]

theorem actualWalkStage_exit_le_of_stopped (pos : V → Euc d) (B : J → Set V)
    (initial : J) (select : ℕ → V → Option J) (A : Set V)
    (hselect : ∀ n v, select n v = none → v ∉ A) (ω : ℕ → V) (n : ℕ)
    (hfinite : (actualWalkStage pos B initial select n ω).1 ≠ ⊤)
    (hstop : (actualWalkStage pos B initial select n ω).2.1 = true) :
    exitTime A ω ≤ (actualWalkStage pos B initial select n ω).1 := by
  induction n with
  | zero => simp only [actualWalkStage, Bool.false_eq_true] at hstop
  | succ n ih =>
    have hle := actualWalkStage_clock_mono pos B initial select ω (Nat.le_succ n)
    have hprevious : (actualWalkStage pos B initial select n ω).1 ≠ ⊤ :=
      ne_top_of_le_ne_top hfinite hle
    by_cases hflag : (actualWalkStage pos B initial select n ω).2.1 = true
    · exact (ih hprevious hflag).trans hle
    · let τ := fun ξ => (actualWalkStage pos B initial select n ξ).1
      let h := observedHistory τ ω
      let choice := walkStageSelector (actualWalkStage pos B initial select n) (select n)
      have hnone : choice h = none := by
        change (selectedClockedExcursion pos B (choice h, h.2 h.1) (futureAt τ ω)).1 = true at hstop
        cases hc : choice h with
        | none => rfl
        | some j => simp only [hc, selectedClockedExcursion, Bool.false_eq_true] at hstop
      have hsame : actualWalkStage pos B initial select n h.2 =
          actualWalkStage pos B initial select n ω :=
        actualWalkStage_observedPast pos B initial select n ω hprevious
      have hsel : select n (h.2 h.1) = none := by
        simpa only [choice, walkStageSelector, hsame, ite_eq_right hflag] using hnone
      obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hprevious
      have hlast : h.2 h.1 = ω k := by
        dsimp only [h]
        rw [observedHistory_of_eq (show τ ω = k from hk.symm)]
        simp only [paddedHistory, Preorder.frestrictLe_apply, min_self]
      have hout : ω k ∉ A := hlast ▸ hselect n (h.2 h.1) hsel
      exact ((exitTime_le_iff A ω k).mpr ⟨k, le_rfl, hout⟩).trans (hk.le.trans hle)

theorem trajectoryLaw_reconstructedStopped_le (N : FiniteConductanceNetwork V)
    (pos : V → Euc d) {A : Set V} (B : J → Set V) (hBA : ∀ j, B j ⊆ A)
    (hA : ∀ v ∈ A, 0 < N.totalConductance v) (haccess : N.BoundaryAccessible A)
    (initial : J) (select : ℕ → Euc d → Option J) (U : Set (Euc d))
    (hU : MeasurableSet U) (hselect : ∀ i x, select i x = none → x ∉ U)
    (v : V) (n : ℕ) (r : ℝ≥0) (hr : 0 < r)
    (hbad : N.trajectoryLaw A hA v
      {ω | (actualWalkExcursionSequence pos B initial select ω n).1 = false} ≤
        (r : ℝ≥0∞)) :
    levyProkhorovEDist
      ((N.trajectoryLaw A hA v).map (stoppedPolygonalCurve pos (pos ⁻¹' U)))
      (((N.trajectoryLaw A hA v).map (actualWalkExcursionSequence pos B initial select)).map
        (reconstructedVertexStoppedCurve U n)) ≤ r := by
  rw [Measure.map_map (measurable_reconstructedVertexStoppedCurve hU n)
    (measurable_actualWalkExcursionSequence pos B initial select)]
  apply levyProkhorov_curveLaws_le_of_ae_reconstruction (N.trajectoryLaw A hA v)
    (stoppedPolygonalCurve pos (pos ⁻¹' U))
    ((reconstructedVertexStoppedCurve U n) ∘ actualWalkExcursionSequence pos B initial select)
    (measurable_stoppedPolygonalCurve pos (pos ⁻¹' U)).aemeasurable
    ((measurable_reconstructedVertexStoppedCurve hU n).comp
      (measurable_actualWalkExcursionSequence pos B initial select)).aemeasurable
    _ r hr hbad
  filter_upwards [N.actualWalkStage_ae_all_clocks_finite pos B hBA hA haccess initial
    (fun i v => select i (pos v)) v] with ω hω
  intro hgood
  have hflag : (actualWalkStage pos B initial (fun i v => select i (pos v)) n ω).2.1 = true := by
    change (actualWalkStage pos B initial (fun i v => select i (pos v)) n ω).2.1 ≠ false at hgood
    exact Bool.eq_true_of_not_eq_false hgood
  exact (reconstructedVertexStoppedCurve_actual pos B initial select U ω n (hω n)
    (actualWalkStage_exit_le_of_stopped pos B initial (fun i v => select i (pos v))
      (pos ⁻¹' U) (fun i v hv => hselect i (pos v) hv) ω n (hω n) hflag)).symm

end BouRabeeGwynne.FiniteConductanceNetwork
