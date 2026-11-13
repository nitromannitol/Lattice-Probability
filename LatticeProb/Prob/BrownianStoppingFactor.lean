import LatticeProb.Prob.BrownianMarkov
import LatticeProb.Prob.BrownianPathMap
import LatticeProb.Prob.BrownianFiniteStopping

/-!
# Finitely valued stopping times factor through the path

The natural filtration of a motion with continuous paths is the pull-back of the canonical
filtration of the space of continuous paths along the path map. Consequently a stopping time of
the natural filtration that takes finitely many values is the composition of a stopping time of
the canonical filtration with the path map. For each value `v`, the event that the stopping time
equals `v` is the preimage of an event of the canonical filtration at time `v`. The canonical
stopping time is the least value whose event contains the path, or the largest value when there
is none.
-/

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

/-- The natural filtration of a motion with continuous paths is the pull-back of the canonical
filtration along the path map. -/
theorem natFiltration_eq_comap_pathMap (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hm : ∀ t, StronglyMeasurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) (t : ℝ≥0) :
    natFiltration B hm t = (brownianNaturalFiltration d t).comap (pathMap B hcont) := by
  rw [natFiltration_eq_comap, brownianNaturalFiltration_eq_comap, MeasurableSpace.comap_comp]
  rfl

/-- **A finitely valued stopping time of the natural filtration factors through the path map**
as a finitely valued stopping time of the canonical filtration of continuous paths. -/
theorem exists_pathStoppingTime_of_finite_range (B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d))
    (hm : ∀ t, StronglyMeasurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) (ρ : Ω → ℝ≥0)
    (hρ : IsStoppingTime (natFiltration B hm) (fun ω => (ρ ω : ℝ≥0∞)))
    (hfin : (Set.range ρ).Finite) :
    ∃ ρ' : BrownianPath d → ℝ≥0,
      IsStoppingTime (brownianNaturalFiltration d) (fun w => (ρ' w : ℝ≥0∞)) ∧
      (Set.range ρ').Finite ∧ ∀ ω, ρ ω = ρ' (pathMap B hcont ω) := by
  classical
  have hS : ∀ v : ℝ≥0, ∃ S : Set (BrownianPath d),
      MeasurableSet[brownianNaturalFiltration d v] S ∧
        pathMap B hcont ⁻¹' S = {ω | ρ ω = v} := by
    intro v
    have h := hρ.measurableSet_eq v
    rw [natFiltration_eq_comap_pathMap B hm hcont v] at h
    obtain ⟨S, hSm, hSeq⟩ := h
    refine ⟨S, hSm, hSeq.trans ?_⟩
    ext ω
    exact ENNReal.coe_inj
  choose S hSm hSeq using hS
  have hmemS : ∀ (v : ℝ≥0) (ω : Ω), pathMap B hcont ω ∈ S v ↔ ρ ω = v := fun v ω =>
    Set.ext_iff.1 (hSeq v) ω
  set V : Finset ℝ≥0 := hfin.toFinset with hV
  set c : ℝ≥0 := if h : V.Nonempty then V.max' h else 0 with hc
  have hle_c : ∀ v ∈ V, v ≤ c := by
    intro v hv
    have hne : V.Nonempty := ⟨v, hv⟩
    rw [hc, dite_eq_left hne]
    exact V.le_max' v hv
  obtain ⟨ρ', hρ'⟩ : ∃ ρ' : BrownianPath d → ℝ≥0, ∀ w, ρ' w =
      if h : (V.filter fun v => w ∈ S v).Nonempty then (V.filter fun v => w ∈ S v).min' h
      else c := ⟨_, fun _ => rfl⟩
  have hρ'_le : ∀ (w : BrownianPath d) (t : ℝ≥0), ρ' w ≤ t ↔
      (∃ v ∈ V, w ∈ S v ∧ v ≤ t) ∨ ((∀ v ∈ V, w ∉ S v) ∧ c ≤ t) := by
    intro w t
    by_cases h : (V.filter fun v => w ∈ S v).Nonempty
    · have hval : ρ' w = (V.filter fun v => w ∈ S v).min' h :=
        (hρ' w).trans (dite_eq_left h)
      rw [hval]
      constructor
      · intro hlt
        have hmem := Finset.mem_filter.1 ((V.filter fun v => w ∈ S v).min'_mem h)
        exact Or.inl ⟨_, hmem.1, hmem.2, hlt⟩
      · rintro (⟨v, hv, hwv, hvt⟩ | ⟨hnone, -⟩)
        · exact ((V.filter fun v => w ∈ S v).min'_le v (Finset.mem_filter.2 ⟨hv, hwv⟩)).trans hvt
        · obtain ⟨v, hv⟩ := h
          exact absurd (Finset.mem_filter.1 hv).2 (hnone v (Finset.mem_filter.1 hv).1)
    · have hval : ρ' w = c :=
        (hρ' w).trans (dite_eq_right h)
      have hnone : ∀ v ∈ V, w ∉ S v := fun v hv hwv => h ⟨v, Finset.mem_filter.2 ⟨hv, hwv⟩⟩
      rw [hval]
      constructor
      · exact fun hct => Or.inr ⟨hnone, hct⟩
      · rintro (⟨v, hv, hwv, -⟩ | ⟨-, hct⟩)
        · exact absurd hwv (hnone v hv)
        · exact hct
  refine ⟨ρ', ?_, ?_, ?_⟩
  · intro t
    have hset : {w : BrownianPath d | ((ρ' w : ℝ≥0) : ℝ≥0∞) ≤ (t : ℝ≥0∞)}
        = (⋃ v ∈ V.filter (· ≤ t), S v) ∪ ({w | ∀ v ∈ V, w ∉ S v} ∩ {_w | c ≤ t}) := by
      ext w
      have h1 : ((ρ' w : ℝ≥0) : ℝ≥0∞) ≤ (t : ℝ≥0∞) ↔ ρ' w ≤ t := ENNReal.coe_le_coe
      refine h1.trans ((hρ'_le w t).trans ?_)
      simp only [Set.mem_union, Set.mem_iUnion, Finset.mem_filter, exists_prop, Set.mem_inter_iff]
      constructor
      · rintro (⟨v, hv, hwv, hvt⟩ | ⟨hnone, hct⟩)
        · exact Or.inl ⟨v, ⟨hv, hvt⟩, hwv⟩
        · exact Or.inr ⟨hnone, hct⟩
      · rintro (⟨v, ⟨hv, hvt⟩, hwv⟩ | ⟨hnone, hct⟩)
        · exact Or.inl ⟨v, hv, hwv, hvt⟩
        · exact Or.inr ⟨hnone, hct⟩
    show MeasurableSet[brownianNaturalFiltration d t]
      {w : BrownianPath d | ((ρ' w : ℝ≥0) : ℝ≥0∞) ≤ (t : ℝ≥0∞)}
    rw [hset]
    refine MeasurableSet.union ?_ ?_
    · exact Finset.measurableSet_biUnion _ fun v hv =>
        (brownianNaturalFiltration d).mono (Finset.mem_filter.1 hv).2 _ (hSm v)
    · by_cases hct : c ≤ t
      · have heq : {w : BrownianPath d | ∀ v ∈ V, w ∉ S v} ∩ {_w | c ≤ t} = ⋂ v ∈ V, (S v)ᶜ := by
          ext w
          simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_compl_iff]
          exact ⟨fun h => h.1, fun h => ⟨h, hct⟩⟩
        rw [heq]
        exact Finset.measurableSet_biInter _ fun v hv =>
          ((brownianNaturalFiltration d).mono ((hle_c v hv).trans hct) _ (hSm v)).compl
      · have heq : {w : BrownianPath d | ∀ v ∈ V, w ∉ S v} ∩ {_w | c ≤ t} = ∅ := by
          ext w
          simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
          exact fun _ => hct
        rw [heq]
        exact @MeasurableSet.empty _ (brownianNaturalFiltration d t)
  · refine ((V.finite_toSet).union (Set.finite_singleton c)).subset ?_
    rintro _ ⟨w, rfl⟩
    by_cases h : (V.filter fun v => w ∈ S v).Nonempty
    · have hval : ρ' w = (V.filter fun v => w ∈ S v).min' h :=
        (hρ' w).trans (dite_eq_left h)
      rw [hval]
      exact Or.inl (Finset.mem_coe.2 (Finset.mem_filter.1 ((V.filter fun v => w ∈ S v).min'_mem h)).1)
    · have hval : ρ' w = c :=
        (hρ' w).trans (dite_eq_right h)
      rw [hval]
      exact Or.inr rfl
  · intro ω
    have hρV : ρ ω ∈ V := hfin.mem_toFinset.2 ⟨ω, rfl⟩
    have hne : (V.filter fun v => pathMap B hcont ω ∈ S v).Nonempty :=
      ⟨ρ ω, Finset.mem_filter.2 ⟨hρV, (hmemS (ρ ω) ω).2 rfl⟩⟩
    have hval : ρ' (pathMap B hcont ω) = (V.filter fun v => pathMap B hcont ω ∈ S v).min' hne :=
      (hρ' _).trans (dite_eq_left hne)
    rw [hval]
    exact (hmemS _ ω).1
      (Finset.mem_filter.1 ((V.filter fun v => pathMap B hcont ω ∈ S v).min'_mem hne)).2

end LatticeProb
