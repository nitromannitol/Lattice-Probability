import LatticeProb.Analysis.LadderSetReconstruction

/-!
# Monotonicity of the excursion count

For a set `K ⊆ ℝ`, the complementary intervals of `K` in `[s, t]` are the connected components of `[s, t] \ K`, and
the excursion count `excursionCount K s t ε` is the number of those of diameter larger than `ε`. For `ε > 0`:

* `finite_setOf_lt_diam`: the complementary intervals of diameter larger than `ε` are finitely many (they are
  pairwise disjoint intervals of Lebesgue measure larger than `ε` inside `[s, t]`);
* `excursionCount_mono_right`: the excursion count is nondecreasing in the right end `t` (each complementary interval
  in `[s, t]` lies in one complementary interval in `[s, u]`, `t ≤ u`, and different ones in different ones);
* `excursionCount_anti_eps`: the excursion count is nonincreasing in `ε`.

These are the deterministic monotonicity facts used to pass from first-passage levels to arbitrary times and from a
sequence of thresholds to all thresholds in Lévy's excursion-count theorem.
-/

open MeasureTheory Set Metric

namespace LatticeProb.LadderSet

variable {K : Set ℝ} {s t u ε ε' : ℝ}

theorem subset_of_mem_complementaryIntervals {C : Set ℝ} (hC : C ∈ complementaryIntervals K s t) :
    C ⊆ Icc s t \ K := by
  obtain ⟨x, -, rfl⟩ := hC
  exact connectedComponentIn_subset _ _

theorem isConnected_of_mem_complementaryIntervals {C : Set ℝ} (hC : C ∈ complementaryIntervals K s t) :
    IsConnected C := by
  obtain ⟨x, hx, rfl⟩ := hC
  exact isConnected_connectedComponentIn_iff.mpr hx

theorem isBounded_of_mem_complementaryIntervals {C : Set ℝ} (hC : C ∈ complementaryIntervals K s t) :
    Bornology.IsBounded C :=
  isBounded_Icc s t |>.subset ((subset_of_mem_complementaryIntervals hC).trans sdiff_subset)

/-- Two complementary intervals with a common point are equal. -/
theorem eq_of_mem_complementaryIntervals {C D : Set ℝ} (hC : C ∈ complementaryIntervals K s t)
    (hD : D ∈ complementaryIntervals K s t) {y : ℝ} (hyC : y ∈ C) (hyD : y ∈ D) : C = D := by
  obtain ⟨x, -, rfl⟩ := hC
  obtain ⟨x', -, rfl⟩ := hD
  rw [connectedComponentIn_eq hyC, connectedComponentIn_eq hyD]

/-- A complementary interval has Lebesgue measure at least its diameter. -/
theorem ofReal_diam_le_volume_of_mem_complementaryIntervals {C : Set ℝ}
    (hC : C ∈ complementaryIntervals K s t) : ENNReal.ofReal (diam C) ≤ volume C := by
  have hbdd := isBounded_of_mem_complementaryIntervals hC
  rw [Real.diam_eq hbdd, ← Real.volume_Ioo]
  exact measure_mono ((isConnected_of_mem_complementaryIntervals hC).Ioo_csInf_csSup_subset hbdd.bddBelow
    hbdd.bddAbove)

/-- **Finitely many long complementary intervals.** For `ε > 0` only finitely many complementary intervals of `K`
in `[s, t]` have diameter larger than `ε`. -/
theorem finite_setOf_lt_diam (K : Set ℝ) (s t : ℝ) (hε : 0 < ε) :
    {C ∈ complementaryIntervals K s t | ε < diam C}.Finite := by
  set S := {C ∈ complementaryIntervals K s t | ε < diam C}
  have hfin := Measure.finite_const_le_meas_of_disjoint_iUnion (volume : Measure ℝ) (ENNReal.ofReal_pos.mpr hε)
    (As := fun C : S => (C : Set ℝ))
    (fun C => (isConnected_of_mem_complementaryIntervals C.2.1).isPreconnected.ordConnected.measurableSet)
    (fun C D hCD => by
      rw [Function.onFun]
      exact Set.disjoint_left.mpr fun y hyC hyD =>
        hCD (Subtype.ext (eq_of_mem_complementaryIntervals C.2.1 D.2.1 hyC hyD)))
    (ne_top_of_le_ne_top (measure_Icc_lt_top (a := s) (b := t)).ne
      (measure_mono (iUnion_subset fun C => (subset_of_mem_complementaryIntervals C.2.1).trans sdiff_subset)))
  have huniv : {C : S | ENNReal.ofReal ε ≤ volume (C : Set ℝ)} = univ := by
    refine eq_univ_of_forall fun C => ?_
    show ENNReal.ofReal ε ≤ volume (C : Set ℝ)
    exact (ENNReal.ofReal_le_ofReal C.2.2.le).trans
      (ofReal_diam_le_volume_of_mem_complementaryIntervals C.2.1)
  rw [huniv] at hfin
  exact Set.finite_coe_iff.mp (Set.finite_univ_iff.mp hfin)

/-- The component of `[s, u] \ K` through a point of a complementary interval `C` of `K` in `[s, t]`, `t ≤ u`,
contains `C`. -/
theorem subset_connectedComponentIn_of_mem_complementaryIntervals {C : Set ℝ}
    (hC : C ∈ complementaryIntervals K s t) (htu : t ≤ u) {x₀ : ℝ} (hx₀ : x₀ ∈ C) :
    C ⊆ connectedComponentIn (Icc s u \ K) x₀ := by
  refine (isConnected_of_mem_complementaryIntervals hC).isPreconnected.subset_connectedComponentIn hx₀ ?_
  intro y hy
  have h := subset_of_mem_complementaryIntervals hC hy
  exact ⟨⟨h.1.1, h.1.2.trans htu⟩, h.2⟩

/-- The union of the components of `[s, u] \ K` through the points of a complementary interval `C` of `K` in
`[s, t]`, `t ≤ u`, is the component through any one point of `C`. -/
theorem biUnion_connectedComponentIn_eq {C : Set ℝ} (hC : C ∈ complementaryIntervals K s t) (htu : t ≤ u)
    {x₀ : ℝ} (hx₀ : x₀ ∈ C) :
    (⋃ x ∈ C, connectedComponentIn (Icc s u \ K) x) = connectedComponentIn (Icc s u \ K) x₀ := by
  have hCc := subset_connectedComponentIn_of_mem_complementaryIntervals hC htu hx₀
  refine subset_antisymm (iUnion₂_subset fun x hx => (connectedComponentIn_eq (hCc hx)).symm.subset) ?_
  exact subset_biUnion_of_mem (u := fun x => connectedComponentIn (Icc s u \ K) x) hx₀

/-- **The excursion count is nondecreasing in the right end.** For `ε > 0` and `t ≤ u`,
`excursionCount K s t ε ≤ excursionCount K s u ε`. -/
theorem excursionCount_mono_right (K : Set ℝ) (s : ℝ) (hε : 0 < ε) (htu : t ≤ u) :
    excursionCount K s t ε ≤ excursionCount K s u ε := by
  unfold excursionCount
  refine Set.ncard_le_ncard_of_injOn (fun C => ⋃ x ∈ C, connectedComponentIn (Icc s u \ K) x) ?_ ?_
    (finite_setOf_lt_diam K s u hε)
  · rintro C ⟨hC, hdiam⟩
    obtain ⟨x₀, hx₀C⟩ := (isConnected_of_mem_complementaryIntervals hC).nonempty
    have hx₀ : x₀ ∈ Icc s u \ K := by
      have h := subset_of_mem_complementaryIntervals hC hx₀C
      exact ⟨⟨h.1.1, h.1.2.trans htu⟩, h.2⟩
    have heq := biUnion_connectedComponentIn_eq hC htu hx₀C
    refine ⟨⟨x₀, hx₀, heq.symm⟩, ?_⟩
    rw [heq]
    refine hdiam.trans_le (diam_mono (subset_connectedComponentIn_of_mem_complementaryIntervals hC htu hx₀C) ?_)
    exact isBounded_Icc s u |>.subset ((connectedComponentIn_subset _ _).trans sdiff_subset)
  · rintro C ⟨hC, -⟩ D ⟨hD, -⟩ hCD
    obtain ⟨x₀, hx₀C⟩ := (isConnected_of_mem_complementaryIntervals hC).nonempty
    obtain ⟨y₀, hy₀D⟩ := (isConnected_of_mem_complementaryIntervals hD).nonempty
    have hCD' : connectedComponentIn (Icc s u \ K) x₀ = connectedComponentIn (Icc s u \ K) y₀ := by
      rw [← biUnion_connectedComponentIn_eq hC htu hx₀C, ← biUnion_connectedComponentIn_eq hD htu hy₀D]
      exact hCD
    have hy₀u : y₀ ∈ connectedComponentIn (Icc s u \ K) x₀ := by
      rw [hCD']
      exact subset_connectedComponentIn_of_mem_complementaryIntervals hD htu hy₀D hy₀D
    have hx₀t := subset_of_mem_complementaryIntervals hC hx₀C
    have hy₀t := subset_of_mem_complementaryIntervals hD hy₀D
    have hseg : uIcc x₀ y₀ ⊆ Icc s t \ K := by
      intro z hz
      refine ⟨ordConnected_Icc.uIcc_subset hx₀t.1 hy₀t.1 hz, fun hzK => ?_⟩
      have hzu := (isPreconnected_connectedComponentIn.ordConnected.uIcc_subset
        (subset_connectedComponentIn_of_mem_complementaryIntervals hC htu hx₀C hx₀C) hy₀u) hz
      exact (connectedComponentIn_subset _ _ hzu).2 hzK
    have hy₀C : y₀ ∈ C := by
      obtain ⟨x, -, rfl⟩ := hC
      rw [connectedComponentIn_eq hx₀C]
      exact isPreconnected_uIcc.subset_connectedComponentIn left_mem_uIcc hseg right_mem_uIcc
    exact eq_of_mem_complementaryIntervals hC hD hy₀C hy₀D

/-- **The excursion count is nonincreasing in the threshold.** For `0 < ε' ≤ ε`,
`excursionCount K s t ε ≤ excursionCount K s t ε'`. -/
theorem excursionCount_anti_eps (K : Set ℝ) (s t : ℝ) (hε' : 0 < ε') (h : ε' ≤ ε) :
    excursionCount K s t ε ≤ excursionCount K s t ε' := by
  unfold excursionCount
  exact Set.ncard_le_ncard (fun C hC => ⟨hC.1, h.trans_lt hC.2⟩) (finite_setOf_lt_diam K s t hε')

end LatticeProb.LadderSet
