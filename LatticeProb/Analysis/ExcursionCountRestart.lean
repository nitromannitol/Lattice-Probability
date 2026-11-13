import LatticeProb.Analysis.ExcursionCountSandwich

/-!
# Restart of the ladder set and of the excursion count at a ladder time

Let `X : ℝ → ℝ` and let `τ` be a forward ladder time of `X` from the anchor `a`, for instance the first passage
`τ = firstPassageBelow X a b` below the level `X a - b`. This file collects the deterministic facts behind the
restart of the excursion count at `τ`:

* `forwardLadderSet_inter_Ici`: after `τ`, the forward ladder set from `a` is the forward ladder set from `τ`;
* `apply_firstPassageBelow_eq`: for continuous `X` and `b ≥ 0`, `X` is exactly at the level `X a - b` at its first
  passage below it;
* `firstPassageBelow_add`: the first passage below `X a - (b + c)` is the first passage, after `τ`, below
  `X τ - c` (`b, c ≥ 0`);
* `complementaryIntervals_eq_union` and `excursionCount_add`: if `τ ∈ K` and `a ≤ τ ≤ v`, the complementary intervals
  of `K` in `[a, v]` are those in `[a, τ]` together with those in `[τ, v]`, and the excursion count is additive:
  `N_ε(K; a, v) = N_ε(K; a, τ) + N_ε(K; τ, v)`.
-/

open Filter Set Topology

namespace LatticeProb.LadderSet

variable {X : ℝ → ℝ} {K : Set ℝ} {a b c τ v ε : ℝ}

/-- **Restart of the forward ladder set.** If `τ` is a forward ladder time of `X` from `a`, then the forward ladder
times from `a` that are at least `τ` are exactly the forward ladder times from `τ`. -/
theorem forwardLadderSet_inter_Ici (hτ : τ ∈ forwardLadderSet X a) :
    forwardLadderSet X a ∩ Ici τ = forwardLadderSet X τ := by
  ext t
  constructor
  · rintro ⟨⟨-, ht⟩, hτt⟩
    exact ⟨hτt, fun s hs => ht s ⟨hτ.1.trans hs.1, hs.2⟩⟩
  · rintro ⟨hτt, ht⟩
    refine ⟨⟨hτ.1.trans hτt, fun s hs => ?_⟩, hτt⟩
    rcases le_total s τ with hsτ | hτs
    · exact (ht τ ⟨le_rfl, hτt⟩).trans (hτ.2 s ⟨hs.1, hsτ⟩)
    · exact ht s ⟨hτs, hs.2⟩

/-- **The level at the first passage.** If `X` is continuous, goes below `X a - b` after `a`, and `b ≥ 0`, then at
the first passage below `X a - b` the value of `X` is exactly `X a - b`. -/
theorem apply_firstPassageBelow_eq (hX : Continuous X) (hne : ∃ s, a ≤ s ∧ X s < X a - b) (hb : 0 ≤ b) :
    X (firstPassageBelow X a b) = X a - b := by
  refine le_antisymm (apply_firstPassageBelow_le hX hne) ?_
  have hsub : Ico a (firstPassageBelow X a b) ⊆ {s | X a - b ≤ X s} := fun s hs =>
    le_of_not_gt fun hsb =>
      (csInf_le (s := {t | a ≤ t ∧ X t < X a - b}) ⟨a, fun _ hr => hr.1⟩ ⟨hs.1, hsb⟩).not_gt hs.2
  rcases (le_firstPassageBelow_self hne).lt_or_eq with hlt | heq
  · have hcl := closure_minimal hsub (isClosed_le continuous_const hX)
    rw [closure_Ico hlt.ne] at hcl
    exact hcl ⟨hlt.le, le_rfl⟩
  · rw [← heq]
    linarith

/-- **Restart of the first passage.** If `X` is continuous and goes below `X a - b` after `a`, with `b, c ≥ 0`, then
the first passage below `X a - (b + c)` after `a` is the first passage below `X τ - c` after the first passage `τ`
below `X a - b`. -/
theorem firstPassageBelow_add (hX : Continuous X) (hne : ∃ s, a ≤ s ∧ X s < X a - b) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    firstPassageBelow X a (b + c) = firstPassageBelow X (firstPassageBelow X a b) c := by
  have hXτ := apply_firstPassageBelow_eq hX hne hb
  show sInf _ = sInf _
  congr 1
  ext t
  constructor
  · rintro ⟨hat, ht⟩
    exact ⟨csInf_le (s := {t | a ≤ t ∧ X t < X a - b}) ⟨a, fun _ hr => hr.1⟩ ⟨hat, by linarith⟩,
      by linarith⟩
  · rintro ⟨hτt, ht⟩
    exact ⟨(le_firstPassageBelow_self hne).trans hτt, by linarith⟩

/-- If `τ ∉ U` and `x ∈ U` with `x ≤ τ`, the connected component of `x` in `U` lies in `(-∞, τ]`. -/
theorem connectedComponentIn_inter_Iic {U : Set ℝ} {x : ℝ} (hτ : τ ∉ U) (hx : x ∈ U) (hxτ : x ≤ τ) :
    connectedComponentIn (U ∩ Iic τ) x = connectedComponentIn U x := by
  refine (connectedComponentIn_mono x inter_subset_left).antisymm ?_
  have hC := isPreconnected_connectedComponentIn (x := x) (F := U)
  refine hC.subset_connectedComponentIn (mem_connectedComponentIn hx) fun y hy =>
    ⟨connectedComponentIn_subset _ _ hy, ?_⟩
  refine mem_Iic.2 (le_of_not_gt fun hyτ => hτ ?_)
  exact connectedComponentIn_subset _ _ (hC.Icc_subset (mem_connectedComponentIn hx) hy ⟨hxτ, hyτ.le⟩)

/-- If `τ ∉ U` and `x ∈ U` with `τ ≤ x`, the connected component of `x` in `U` lies in `[τ, ∞)`. -/
theorem connectedComponentIn_inter_Ici {U : Set ℝ} {x : ℝ} (hτ : τ ∉ U) (hx : x ∈ U) (hxτ : τ ≤ x) :
    connectedComponentIn (U ∩ Ici τ) x = connectedComponentIn U x := by
  refine (connectedComponentIn_mono x inter_subset_left).antisymm ?_
  have hC := isPreconnected_connectedComponentIn (x := x) (F := U)
  refine hC.subset_connectedComponentIn (mem_connectedComponentIn hx) fun y hy =>
    ⟨connectedComponentIn_subset _ _ hy, ?_⟩
  refine mem_Ici.2 (le_of_not_gt fun hyτ => hτ ?_)
  exact connectedComponentIn_subset _ _ (hC.Icc_subset hy (mem_connectedComponentIn hx) ⟨hyτ.le, hxτ⟩)

theorem Icc_diff_inter_Iic (hτv : τ ≤ v) : Icc a v \ K ∩ Iic τ = Icc a τ \ K := by
  ext t
  constructor
  · rintro ⟨⟨ht, htK⟩, htτ⟩
    exact ⟨⟨ht.1, htτ⟩, htK⟩
  · rintro ⟨ht, htK⟩
    exact ⟨⟨⟨ht.1, ht.2.trans hτv⟩, htK⟩, ht.2⟩

theorem Icc_diff_inter_Ici (haτ : a ≤ τ) : Icc a v \ K ∩ Ici τ = Icc τ v \ K := by
  ext t
  constructor
  · rintro ⟨⟨ht, htK⟩, hτt⟩
    exact ⟨⟨hτt, ht.2⟩, htK⟩
  · rintro ⟨ht, htK⟩
    exact ⟨⟨⟨haτ.trans ht.1, ht.2⟩, htK⟩, ht.1⟩

/-- **Splitting the complementary intervals at a point of `K`.** If `τ ∈ K` and `a ≤ τ ≤ v`, the complementary
intervals of `K` in `[a, v]` are those in `[a, τ]` together with those in `[τ, v]`. -/
theorem complementaryIntervals_eq_union (hτK : τ ∈ K) (haτ : a ≤ τ) (hτv : τ ≤ v) :
    complementaryIntervals K a v = complementaryIntervals K a τ ∪ complementaryIntervals K τ v := by
  have hτU : τ ∉ Icc a v \ K := fun h => h.2 hτK
  ext C
  constructor
  · rintro ⟨x, hx, rfl⟩
    rcases le_total x τ with hxτ | hτx
    · refine Or.inl ⟨x, ?_, ?_⟩
      · rw [← Icc_diff_inter_Iic hτv]
        exact ⟨hx, hxτ⟩
      · rw [← Icc_diff_inter_Iic hτv]
        exact connectedComponentIn_inter_Iic hτU hx hxτ
    · refine Or.inr ⟨x, ?_, ?_⟩
      · rw [← Icc_diff_inter_Ici haτ]
        exact ⟨hx, hτx⟩
      · rw [← Icc_diff_inter_Ici haτ]
        exact connectedComponentIn_inter_Ici hτU hx hτx
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · rw [← Icc_diff_inter_Iic hτv] at hx ⊢
      exact ⟨x, hx.1, (connectedComponentIn_inter_Iic hτU hx.1 hx.2).symm⟩
    · rw [← Icc_diff_inter_Ici haτ] at hx ⊢
      exact ⟨x, hx.1, (connectedComponentIn_inter_Ici hτU hx.1 hx.2).symm⟩

theorem disjoint_complementaryIntervals (hτK : τ ∈ K) :
    Disjoint (complementaryIntervals K a τ) (complementaryIntervals K τ v) := by
  refine Set.disjoint_left.2 fun C hC hC' => ?_
  obtain ⟨x, hx, rfl⟩ := hC
  have h₁ := subset_of_mem_complementaryIntervals hC' (mem_connectedComponentIn hx)
  exact hx.2 (le_antisymm hx.1.2 h₁.1.1 ▸ hτK)

/-- **Additivity of the excursion count at a point of `K`.** If `τ ∈ K` and `a ≤ τ ≤ v`, then for `ε > 0`,
`N_ε(K; a, v) = N_ε(K; a, τ) + N_ε(K; τ, v)`. -/
theorem excursionCount_add (hτK : τ ∈ K) (haτ : a ≤ τ) (hτv : τ ≤ v) (hε : 0 < ε) :
    excursionCount K a v ε = excursionCount K a τ ε + excursionCount K τ v ε := by
  have hsep : {C ∈ complementaryIntervals K a τ ∪ complementaryIntervals K τ v | ε < Metric.diam C} =
      {C ∈ complementaryIntervals K a τ | ε < Metric.diam C} ∪
        {C ∈ complementaryIntervals K τ v | ε < Metric.diam C} := by
    ext C
    constructor
    · rintro ⟨hC | hC, hd⟩
      · exact Or.inl ⟨hC, hd⟩
      · exact Or.inr ⟨hC, hd⟩
    · rintro (⟨hC, hd⟩ | ⟨hC, hd⟩)
      · exact ⟨Or.inl hC, hd⟩
      · exact ⟨Or.inr hC, hd⟩
  unfold excursionCount
  rw [complementaryIntervals_eq_union hτK haτ hτv, hsep]
  exact Set.ncard_union_eq
    ((disjoint_complementaryIntervals hτK).mono (fun _ h => h.1) (fun _ h => h.1))
    (finite_setOf_lt_diam K a τ hε) (finite_setOf_lt_diam K τ v hε)

end LatticeProb.LadderSet
