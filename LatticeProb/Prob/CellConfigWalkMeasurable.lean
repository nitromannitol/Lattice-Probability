import LatticeProb.Bonanno.ReflectedGMS.GMS.WalkSRWLaw

/-!
# The rescaled walk on a recurrent cell configuration is a random path

For a cell configuration `H` on `ℂ` in the sense of Gwynne-Miller-Sheffield (Definition 1.15),
the rescaled linearly interpolated simple random walk `t ↦ ε X̃_{t/ε²}` is defined as an element
of `C([0,∞), ℂ)` only off the null set of paths whose jump times stay bounded.  Its almost sure
measurability as a random path, which is what the continuous mapping theorem needs, therefore
rests on the divergence of the jump times.  This file derives that divergence from recurrence,
which is part of the conclusion of GMS Theorem 1.16, and supplies the two structural inputs of the
measurability lemma from Definition 1.15:

* `countable_cells_of_locallyFinite`: a locally finite cell configuration has countably many
  cells;
* `finite_restrict_of_isCompact`: only finitely many cells meet a compact set;
* `area_pos`, `summable_c`, `pi_pos_of_adj`, `holding_pos_of_adj`: a cell has positive area, its
  conductances are summable, and its holding time `Area(H)/π(H)` is positive as soon as it has a
  neighbour;
* `jumpTimesUnbounded_of_infinite_visits`: infinitely many visits to one cell force the jump times
  `T_n = Σ_{k<n} Area(Y_k)/π(Y_k)` to diverge;
* `ae_jumpTimesUnbounded_of_recurrent`, `aemeasurable_interpolatedWalk_of_recurrent`: under the
  law of the walk on a recurrent configuration the jump times diverge almost surely, so the
  rescaled interpolated walk is an a.e.-measurable random element of `C([0,∞), ℂ)` for every
  scale `ε`.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace LatticeProb.CellConfigWalk

open ReflectedGMS ReflectedGMS.GMS ReflectedGMS.GMS.CellConfig

variable {H : CellConfig}

/-- **A locally finite cell configuration has countably many cells**: the plane is covered by
countably many open sets each meeting only finitely many cells, and every cell is nonempty. -/
theorem countable_cells_of_locallyFinite
    (hlf : ∀ z : Plane, ∃ U ∈ 𝓝 z, (H.restrict U).Finite) : Countable H.cells := by
  choose U hU hfin using hlf
  obtain ⟨s, hs, hcover⟩ := TopologicalSpace.countable_cover_nhds hU
  have hsub : H.cells ⊆ ⋃ z ∈ s, H.restrict (U z) := by
    intro K hK
    obtain ⟨x, hx⟩ := K.nonempty
    have hxU : x ∈ ⋃ z ∈ s, U z := hcover ▸ mem_univ x
    obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.1 hxU
    exact mem_iUnion₂.2 ⟨z, hz, hK, x, hx, hxz⟩
  exact ((hs.biUnion fun z _ => (hfin z).countable).mono hsub).to_subtype

/-- **Only finitely many cells of a locally finite configuration meet a compact set.** -/
theorem finite_restrict_of_isCompact
    (hlf : ∀ z : Plane, ∃ U ∈ 𝓝 z, (H.restrict U).Finite) {A : Set Plane} (hA : IsCompact A) :
    (H.restrict A).Finite := by
  choose U hU hfin using hlf
  obtain ⟨t, -, hcover⟩ := hA.elim_nhds_subcover U fun z _ => hU z
  refine (t.finite_toSet.biUnion fun z _ => hfin z).subset ?_
  rintro K ⟨hK, x, hxK, hxA⟩
  obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.1 (hcover hxA)
  exact mem_iUnion₂.2 ⟨z, hz, hK, x, hxK, hxz⟩

/-- **A cell has positive area**: it is compact with nonempty interior. -/
theorem area_pos (hH : H.IsCellConfiguration) (K : H.cells) : 0 < CellConfig.area (K : Cell) := by
  have hint := hH.interior_nonempty K K.2
  have hpos : 0 < volume ((K : Cell) : Set Plane) :=
    (isOpen_interior.measure_pos volume hint).trans_le (measure_mono interior_subset)
  exact ENNReal.toReal_pos hpos.ne' ((K : Cell).isCompact.measure_lt_top).ne

/-- **The conductances out of a cell are summable**: only the finitely many cells meeting it can be
adjacent to it. -/
theorem summable_c (hH : H.IsCellConfiguration) (K : Cell) :
    Summable fun K' : H.cells => H.c K K' := by
  have hfin : (Subtype.val ⁻¹' H.restrict (K : Set Plane) : Set H.cells).Finite :=
    (finite_restrict_of_isCompact hH.locallyFinite K.isCompact).preimage
      Subtype.val_injective.injOn
  refine summable_of_ne_finset_zero (s := hfin.toFinset) fun K' hK' => ?_
  by_contra hne
  have hadj : H.Adj K K' := lt_of_le_of_ne (hH.c_nonneg K K') (Ne.symm hne)
  apply hK'
  rw [Finite.mem_toFinset]
  obtain ⟨x, hx⟩ := hH.adj_inter K K' hadj
  exact ⟨K'.2, x, hx.2, hx.1⟩

/-- **A cell with a neighbour has positive total conductance** `π(H) = Σ_{H'} c(H,H')`. -/
theorem pi_pos_of_adj (hH : H.IsCellConfiguration) {K : Cell} {K' : H.cells}
    (hadj : H.Adj K K') : 0 < H.pi K :=
  hadj.trans_le ((summable_c hH K).le_tsum K' fun _ _ => hH.c_nonneg _ _)

/-- **The holding time `Area(H)/π(H)` of a cell with a neighbour is positive.** -/
theorem holding_pos_of_adj (hH : H.IsCellConfiguration) {K K' : H.cells}
    (hadj : H.Adj K K') : 0 < H.holding K :=
  div_pos (area_pos hH K) (pi_pos_of_adj hH hadj)

/-- **Every holding time is positive when every cell has a neighbour.** -/
theorem holding_pos_of_forall_exists_adj (hH : H.IsCellConfiguration)
    (hadj : ∀ K : H.cells, ∃ K' : H.cells, H.Adj K K') : ∀ K : H.cells, 0 < H.holding K :=
  fun K => (hadj K).elim fun _ h => holding_pos_of_adj hH h

/-- **Infinitely many visits to one cell force the jump times to diverge**: after `M` visits to `K₀`
the jump time is at least `M · Area(K₀)/π(K₀)`. -/
theorem jumpTimesUnbounded_of_infinite_visits (hpos : ∀ K, 0 < H.holding K)
    {ω : ℕ → H.cells} {K₀ : H.cells} (hinf : {n | ω n = K₀}.Infinite) :
    H.JumpTimesUnbounded ω := by
  intro N
  have h0 := hpos K₀
  obtain ⟨M, hM⟩ := exists_nat_gt ((N : ℝ) / H.holding K₀)
  obtain ⟨t, hts, htc⟩ := hinf.exists_subset_card_eq M
  refine ⟨t.sup id + 1, ?_⟩
  have hsub : t ⊆ Finset.range (t.sup id + 1) := fun k hk =>
    Finset.mem_range.2 (Nat.lt_succ_of_le (Finset.le_sup (f := id) hk))
  have h1 : ∑ k ∈ t, H.holding (ω k) = ∑ _k ∈ t, H.holding K₀ :=
    Finset.sum_congr rfl fun k hk => by rw [show ω k = K₀ from hts (Finset.mem_coe.2 hk)]
  rw [Finset.sum_const, htc, nsmul_eq_mul] at h1
  have h2 : ∑ k ∈ t, H.holding (ω k) ≤ ∑ k ∈ Finset.range (t.sup id + 1), H.holding (ω k) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => (hpos _).le
  have h3 : (N : ℝ) < M * H.holding K₀ := (div_lt_iff₀ h0).1 hM
  show (N : ℝ) < ∑ k ∈ Finset.range (t.sup id + 1), H.holding (ω k)
  linarith

/-- **On a recurrent configuration the jump times of the walk diverge almost surely.** -/
theorem ae_jumpTimesUnbounded_of_recurrent (hrec : H.Recurrent) (hpos : ∀ K, 0 < H.holding K)
    {K₀ : H.cells} {Q : Measure (ℕ → H.cells)} (hQ : H.IsSRWLaw K₀ Q) :
    ∀ᵐ ω ∂Q, H.JumpTimesUnbounded ω :=
  (hrec K₀ Q hQ).mono fun _ hω => jumpTimesUnbounded_of_infinite_visits hpos hω

/-- **The rescaled interpolated walk on a recurrent configuration is a random path**: under the law
of the walk it is an a.e.-measurable random element of `C([0,∞), ℂ)` for every scale `ε` and
every choice `p` of points. -/
theorem aemeasurable_interpolatedWalk_of_recurrent [Countable H.cells] (hrec : H.Recurrent)
    (hpos : ∀ K, 0 < H.holding K) {K₀ : H.cells} {Q : Measure (ℕ → H.cells)}
    (hQ : H.IsSRWLaw K₀ Q) (p : H.cells → Plane) (ε : ℝ≥0) :
    AEMeasurable (H.interpolatedWalk p ε) Q :=
  aemeasurable_interpolatedWalk hpos p ε (ae_jumpTimesUnbounded_of_recurrent hrec hpos hQ)

/-- The same for a cell configuration in the sense of GMS Definition 1.15, whose cells are
countable by local finiteness, when every cell has a neighbour. -/
theorem aemeasurable_interpolatedWalk_of_isCellConfiguration (hH : H.IsCellConfiguration)
    (hadj : ∀ K : H.cells, ∃ K' : H.cells, H.Adj K K') (hrec : H.Recurrent) {K₀ : H.cells}
    {Q : Measure (ℕ → H.cells)} (hQ : H.IsSRWLaw K₀ Q) (p : H.cells → Plane) (ε : ℝ≥0) :
    AEMeasurable (H.interpolatedWalk p ε) Q :=
  haveI := countable_cells_of_locallyFinite hH.locallyFinite
  aemeasurable_interpolatedWalk_of_recurrent hrec (holding_pos_of_forall_exists_adj hH hadj) hQ p ε

end LatticeProb.CellConfigWalk
