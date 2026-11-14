/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.WalkBrownianGoodEvent at commit fdb5cad; local import paths and a deprecated lemma name are adapted. -/
import LatticeProb.Bonanno.BouRabeeGwynne.WalkBrownianCoupling
import LatticeProb.Bonanno.BouRabeeGwynne.FiniteCellSelector

/-! Successful paired excursions either share a valid bounded endpoint cell,
or have both terminated and retain their earlier endpoint-distance bound.
A default off-cover label never counts as an active success. -/

open MeasureTheory ProbabilityTheory Set
open scoped unitInterval

namespace BouRabeeGwynne

variable {d : ℕ} {V ι J : Type*}

/-- A success state keeps graph support and handles absorbing padding without
requiring any later partition label at an already stopped endpoint. -/
def goodExcursionPair (pos : V → Euc d) (E : ι → Set (Euc d)) (a : ℝ) :
    Set ((Bool × ClockedWalkExcursion d) × (Bool × C(unitInterval, Euc d))) :=
  {p | (∃ i, p.1 ∈ walkEndpointCell pos (E i) ∧
      p.2 ∈ activeEndpointCell (fun c : C(unitInterval, Euc d) => c 1) (E i)) ∨
    (p.1.1 = true ∧ p.2.1 = true ∧
      ClockedWalkExcursion.endPoint p.1.2 ∈ Set.range pos ∧
      dist (ClockedWalkExcursion.endPoint p.1.2) (p.2.2 1) ≤ a)}

lemma measurableSet_goodExcursionPair [Finite V] [Countable ι]
    (pos : V → Euc d) (E : ι → Set (Euc d)) (hE : ∀ i, MeasurableSet (E i)) (a : ℝ) :
    MeasurableSet (goodExcursionPair pos E a) := by
  change MeasurableSet ({p : (Bool × ClockedWalkExcursion d) ×
      (Bool × C(unitInterval, Euc d)) | ∃ i, p.1 ∈ walkEndpointCell pos (E i) ∧
      p.2 ∈ activeEndpointCell (fun c : C(unitInterval, Euc d) => c 1) (E i)} ∪ _)
  apply MeasurableSet.union
  · simp only [Set.ofPred_exists]
    exact MeasurableSet.iUnion fun i => (measurableSet_walkEndpointCell pos (hE i)).prod
      (measurableSet_activeEndpointCell _ (ContinuousMap.measurable_eval 1) (hE i))
  · exact (measurable_fst.fst (measurableSet_singleton true)).inter
      ((measurable_snd.fst (measurableSet_singleton true)).inter
        (((ClockedWalkExcursion.measurable_endPoint.comp measurable_fst.snd)
          (Set.finite_range pos).measurableSet).inter
          (measurableSet_le
            ((ClockedWalkExcursion.measurable_endPoint.comp measurable_fst.snd).dist
              ((ContinuousMap.measurable_eval 1).comp measurable_snd.snd)) measurable_const)))

lemma goodExcursionPair_dist_le (pos : V → Euc d) (E : ι → Set (Euc d)) {a : ℝ}
    (hdiam : ∀ i, ∀ x ∈ E i, ∀ y ∈ E i, dist x y ≤ a)
    {p} (hp : p ∈ goodExcursionPair pos E a) :
    dist (ClockedWalkExcursion.endPoint p.1.2) (p.2.2 1) ≤ a := by
  rcases hp with ⟨i, hwi, hbi⟩ | hstop
  · exact hdiam i _ hwi.2.1 _ hbi.2
  · exact hstop.2.2.2

lemma goodExcursionPair_walk_in_range (pos : V → Euc d) (E : ι → Set (Euc d)) (a : ℝ)
    {p} (hp : p ∈ goodExcursionPair pos E a) :
    ClockedWalkExcursion.endPoint p.1.2 ∈ Set.range pos := by
  rcases hp with ⟨i, hwi, hbi⟩ | hstop
  · exact hwi.2.2
  · exact hstop.2.2.1

lemma goodExcursionPair_flags (pos : V → Euc d) (E : ι → Set (Euc d)) (a : ℝ)
    {p} (hp : p ∈ goodExcursionPair pos E a) : p.1.1 = p.2.1 := by
  rcases hp with ⟨i, hwi, hbi⟩ | hstop
  · exact hwi.1.trans hbi.1.symm
  · exact hstop.1.trans hstop.2.1.symm

lemma goodExcursionPair_active_cell (pos : V → Euc d) (E : ι → Set (Euc d)) (a : ℝ)
    {p} (hp : p ∈ goodExcursionPair pos E a) (hactive : p.1.1 = false) :
    ∃ i, p.1 ∈ walkEndpointCell pos (E i) ∧
      p.2 ∈ activeEndpointCell (fun c : C(unitInterval, Euc d) => c 1) (E i) := by
  rcases hp with hmatch | hstop
  · exact hmatch
  · rw [hactive] at hstop
    cases hstop.1

lemma goodExcursionPair_same_selector (pos : V → Euc d) (E : ι → Set (Euc d)) (a : ℝ)
    (hdisj : Pairwise (fun i j => Disjoint (E i) (E j))) (select : ι → Option J)
    {p} (hp : p ∈ goodExcursionPair pos E a) (hactive : p.1.1 = false) :
    cellSelector E select (ClockedWalkExcursion.endPoint p.1.2) =
      cellSelector E select (p.2.2 1) := by
  obtain ⟨i, hwi, hbi⟩ := goodExcursionPair_active_cell pos E a hp hactive
  rw [cellSelector_of_label E select ((cellLabel_eq_some_iff E hdisj _ i).mpr hwi.2.1),
    cellSelector_of_label E select ((cellLabel_eq_some_iff E hdisj _ i).mpr hbi.2)]

lemma goodExcursionPair_compl_disjoint_cell (pos : V → Euc d) (E : ι → Set (Euc d))
    (a : ℝ) (i : ι) : Disjoint (goodExcursionPair pos E a)ᶜ
      (walkEndpointCell pos (E i) ×ˢ
        activeEndpointCell (fun c : C(unitInterval, Euc d) => c 1) (E i)) := by
  exact Set.disjoint_left.mpr (fun p hp hi => hp (Or.inl ⟨i, hi.1, hi.2⟩))

/-- Both actual constant laws preserve a previously successful stopped pair,
even if neither endpoint belongs to any later cell. -/
lemma coupling_bad_goodExcursionPair_constants_zero
    (pos : V → Euc d) (E : ι → Set (Euc d)) {a : ℝ} {x y : Euc d}
    (hx : x ∈ Set.range pos) (hxy : dist x y ≤ a)
    (ρ : Measure ((Bool × ClockedWalkExcursion d) × (Bool × C(unitInterval, Euc d))))
    (hfst : ρ.fst = Measure.dirac (true, ClockedWalkExcursion.constant x))
    (hsnd : ρ.snd = Measure.dirac (true, ContinuousMap.const unitInterval y)) :
    ρ (goodExcursionPair pos E a)ᶜ = 0 := by
  apply coupling_bad_zero_of_dirac_marginals ρ hfst hsnd
  change ¬ ¬ _
  exact not_not_intro (Or.inr ⟨rfl, rfl, hx, hxy⟩)

end BouRabeeGwynne
