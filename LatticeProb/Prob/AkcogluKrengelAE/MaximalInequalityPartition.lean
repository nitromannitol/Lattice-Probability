import LatticeProb.Prob.AkcogluKrengelAE.MaximalInequalityDyadic

set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-!
# The maximal inequality: guillotine partitions (Step 4, part B, the grid dyBig)

`dyBig u J N` is the union of the level-`J` dyadic cells of offset `u` meeting the cube of side `N`;
it is tiled by those cells, so a nonnegative superadditive process summed over any pairwise disjoint
family of cells of level `≤ J` contained in `dyBig u J N` is at most `r (dyBig u J N)`. Also: for `n
≥ 1` there is a dyadic scale `j` with `n ≤ 2 ^ j < 2 n`.
-/

open MeasureTheory Filter Topology

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A box translated by `z` is the box with both corners translated by `z`. -/
theorem map_addRight_latticeBox_eq {d : ℕ} (a b z : Site d) :
    (latticeBox a b).map (Equiv.addRight z).toEmbedding = latticeBox (a + z) (b + z) := by
  simp only [latticeBox]
  have h : (Equiv.addRight z).toEmbedding = addRightEmbedding z := rfl
  rw [h, Finset.map_add_right_Icc]

/-- Translating all three boxes of an `IsBoxSplit` by `z` preserves the split. -/
theorem isBoxSplit_map_addRight {d : ℕ} {B B₁ B₂ : Finset (Site d)} (z : Site d)
    (h : IsBoxSplit B B₁ B₂) :
    IsBoxSplit (B.map (Equiv.addRight z).toEmbedding) (B₁.map (Equiv.addRight z).toEmbedding)
      (B₂.map (Equiv.addRight z).toEmbedding) := by
  obtain ⟨⟨a, b, rfl⟩, ⟨a₁, b₁, rfl⟩, ⟨a₂, b₂, rfl⟩, hdisj, hunion⟩ := h
  refine ⟨⟨a + z, b + z, map_addRight_latticeBox_eq a b z⟩,
    ⟨a₁ + z, b₁ + z, map_addRight_latticeBox_eq a₁ b₁ z⟩,
    ⟨a₂ + z, b₂ + z, map_addRight_latticeBox_eq a₂ b₂ z⟩, ?_, ?_⟩
  · rw [Finset.disjoint_map]
    exact hdisj
  · rw [← Finset.map_union, hunion, map_addRight_latticeBox_eq a b z]

/-- For a nonnegative superadditive `r`, the sum of `r` over the `k` slabs of width `m` along
coordinate `i` is at most `r` of the whole box. -/
theorem sum_latticeBox_slabs_le_apply {d : ℕ} (r : Finset (Site d) → ℝ)
    (hrnn : ∀ a b, 0 ≤ r (latticeBox a b))
    (hrsup : ∀ B B₁ B₂, IsBoxSplit B B₁ B₂ → r B₁ + r B₂ ≤ r B) (m : ℕ) (i : Fin d) (a : Site d) :
    ∀ (k : ℕ) (b : Site d), b i = a i + (k : ℤ) * m - 1 →
      ∑ j ∈ Finset.range k, r (latticeBox (Function.update a i (a i + (m : ℤ) * j))
          (Function.update b i (a i + (m : ℤ) * j + m - 1))) ≤ r (latticeBox a b) := by
  intro k
  induction k with
  | zero => intro b _; rw [Finset.sum_range_zero]; exact hrnn a b
  | succ k ih =>
    intro b hb
    have hs := isBoxSplit_latticeBox_update_of_mem a b i (a i + (m : ℤ) * k) (le_add_of_nonneg_right
        (by
        positivity))
      (by rw [hb]; push_cast; nlinarith)
    have h1 := hrsup _ _ _ hs
    have h2 := ih (Function.update b i (a i + (m : ℤ) * k - 1)) (by rw [Function.update_self]; ring)
    simp only [Function.update_idem] at h2
    have e : a i + (m : ℤ) * k + m - 1 = b i := by rw [hb]; push_cast; ring
    rw [Finset.sum_range_succ, e, Function.update_eq_self]
    linarith

/-- For a nonnegative superadditive `r`, the sum of `r` over the grid boxes obtained by refining
coordinate `i` is at most `r` of the coarser grid box. -/
theorem sum_gridBox_insert_le_apply_gridBox {d : ℕ} (r : Finset (Site d) → ℝ)
    (hrnn : ∀ a b, 0 ≤ r (latticeBox a b))
    (hrsup : ∀ B B₁ B₂, IsBoxSplit B B₁ B₂ → r B₁ + r B₂ ≤ r B)
    (m k : ℕ) (s : Finset (Fin d)) (i : Fin d) (hi : i ∉ s) (w : Fin d → ℕ)
    (hw : w ∈ gridSet d s k) :
    ∑ j ∈ Finset.range k, r (gridBox m k (insert i s) (Function.update w i j)) ≤
      r (gridBox m k s w) := by
  have hwi : w i = 0 := gridSet_apply_eq_zero_of_notMem hw hi
  have h13 := sum_latticeBox_slabs_le_apply r hrnn hrsup m i (fun l => (m : ℤ) * (w l : ℤ)) k
    (fun l => (m : ℤ) * (w l : ℤ) + (if l ∈ s then (m : ℤ) else (k : ℤ) * m) - 1)
    (by simp [hi])
  refine le_trans (le_of_eq ?_) h13
  apply Finset.sum_congr rfl
  intro j _
  rw [gridBox_update_eq_gridBox_insert m k s i hi w hwi j]

/-- For a nonnegative superadditive `r`, the sum of `r` over the grid boxes indexed by `gridSet d s
k` is at most `r` of the cube of side `k * m`. -/
theorem sum_apply_gridBox_le_apply_cube {d : ℕ} (r : Finset (Site d) → ℝ)
    (hrnn : ∀ a b, 0 ≤ r (latticeBox a b))
    (hrsup : ∀ B B₁ B₂, IsBoxSplit B B₁ B₂ → r B₁ + r B₂ ≤ r B) (m k : ℕ) (s : Finset (Fin d)) :
    ∑ w ∈ gridSet d s k, r (gridBox m k s w) ≤ r (latticeCube d (k * m)) := by
  induction s using Finset.induction with
  | empty =>
    rw [gridSet_empty, Finset.sum_singleton]
    exact le_of_eq (congrArg r (gridBox_empty_eq_latticeCube m k))
  | insert i t hi ih =>
    rw [sum_gridSet_insert t i hi k (fun w => r (gridBox m k (insert i t) w))]
    exact le_trans (Finset.sum_le_sum (fun w hw => sum_gridBox_insert_le_apply_gridBox r hrnn hrsup
        m k t i hi w hw)) ih

/-- A grid box of side `2 ^ J` translated by `u - 2 · 2 ^ J` is the level-`J` dyadic cell of offset
`u` at index `w - 2`. -/
theorem map_addRight_gridBox_eq_dyCell {d : ℕ} (u : Site d) (J k : ℕ) (w : Fin d → ℕ) :
    (gridBox (2 ^ J) k Finset.univ w).map (Equiv.addRight (u - fun _ => 2 * (2 ^ J :
        ℤ))).toEmbedding =
      dyCell u J (natToSite w - fun _ => 2) := by
  rw [gridBox, map_addRight_latticeBox_eq, dyCell]
  congr 1 <;> funext i <;>
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, natToSite,
      Finset.mem_univ, if_true] <;>
    (push_cast; ring)

/-- For a nonnegative superadditive `r`, the sum of `r` over the level-`J` dyadic cells tiling
`dyBig u J N` is at most `r (dyBig u J N)`. -/
theorem sum_apply_dyCell_grid_le_apply_dyBig {d : ℕ} (r : Finset (Site d) → ℝ)
    (hrnn : ∀ a b, 0 ≤ r (latticeBox a b))
    (hrsup : ∀ B B₁ B₂, IsBoxSplit B B₁ B₂ → r B₁ + r B₂ ≤ r B) (u : Site d) (J N : ℕ) :
    ∑ w ∈ gridSet d Finset.univ (N / 2 ^ J + 4), r (dyCell u J (natToSite w - fun _ => 2)) ≤
      r (dyBig u J N) := by
  have h := sum_apply_gridBox_le_apply_cube
    (fun B => r (B.map (Equiv.addRight (u - fun _ => 2 * (2 ^ J : ℤ))).toEmbedding))
    (fun a b => by
      show 0 ≤ r ((latticeBox a b).map (Equiv.addRight (u - fun _ => 2 * (2 ^ J : ℤ))).toEmbedding)
      rw [map_addRight_latticeBox_eq]; exact hrnn _ _)
    (fun B B₁ B₂ hs => hrsup _ _ _ (isBoxSplit_map_addRight _ hs)) (2 ^ J) (N / 2 ^ J + 4)
        Finset.univ
  simp only [map_addRight_gridBox_eq_dyCell] at h
  exact h

/-- Euclidean division bounds: for `0 ≤ t ≤ M L - 1`, the quotient `t / L` lies in `[0, M)` and `t`
lies in `[L (t / L), L (t / L) + L - 1]`. -/
theorem ediv_nonneg_lt_and_mul_ediv_le (t M L : ℤ) (hL : 0 < L) (h0 : 0 ≤ t) (h1 : t ≤ M * L
    - 1) :
    0 ≤ t / L ∧ t / L < M ∧ L * (t / L) ≤ t ∧ t ≤ L * (t / L) + L - 1 := by
  refine ⟨Int.ediv_nonneg h0 hL.le, ?_, ?_, ?_⟩
  · rw [Int.ediv_lt_iff_lt_mul hL]
    omega
  · have h := Int.mul_ediv_add_emod t L
    have h2 := Int.emod_nonneg t hL.ne'
    omega
  · have h := Int.mul_ediv_add_emod t L
    have h2 := Int.emod_lt_of_pos t hL
    omega

/-- Every site of `dyBig u J N` lies in the level-`J` dyadic cell indexed by some grid point `w - 2`
with `w ∈ gridSet d Finset.univ (N / 2 ^ J + 4)`. -/
theorem exists_mem_gridSet_mem_dyCell_of_mem_dyBig {d : ℕ} (u : Site d) (J N : ℕ) (y : Site
    d)
    (hy : y ∈ dyBig u J N) :
    ∃ w ∈ gridSet d Finset.univ (N / 2 ^ J + 4), y ∈ dyCell u J (natToSite w - fun _ => 2) := by
  have hz : dyBig u J N = latticeBox (u - fun _ => 2 * (2 ^ J : ℤ))
      (fun i => (u i - 2 * (2 ^ J : ℤ)) + (((N / 2 ^ J + 4) * 2 ^ J : ℕ) : ℤ) - 1) := by
    rw [dyBig, map_addRight_latticeCube_eq_latticeBox]
    congr 1
  rw [hz, mem_latticeBox_iff] at hy
  have hL : (0 : ℤ) < 2 ^ J := by positivity
  have hM : (0 : ℤ) ≤ ((N / 2 ^ J + 4 : ℕ) : ℤ) := by positivity
  have hbound : ∀ i, 0 ≤ y i - (u i - 2 * (2 ^ J : ℤ)) ∧
      y i - (u i - 2 * (2 ^ J : ℤ)) ≤ ((N / 2 ^ J + 4 : ℕ) : ℤ) * 2 ^ J - 1 := by
    intro i
    have h1 := (hy i).1
    have h2 := (hy i).2
    simp only [Pi.sub_apply] at h1 h2
    have h3 : ((N / 2 ^ J + 4 : ℕ) : ℤ) * 2 ^ J
        = (((N / 2 ^ J + 4) * 2 ^ J : ℕ) : ℤ) := by push_cast; ring
    constructor <;> linarith [h1, h2, h3]
  refine ⟨fun i => ((y i - (u i - 2 * (2 ^ J : ℤ))) / 2 ^ J).toNat, ?_, ?_⟩
  · rw [gridSet, Fintype.mem_piFinset]
    intro i
    simp only [Finset.mem_univ, if_true]
    have h1 := (hbound i).1
    have h2 := (hbound i).2
    have h3 := ediv_nonneg_lt_and_mul_ediv_le (y i - (u i - 2 * (2 ^ J : ℤ)))
      ((N / 2 ^ J + 4 : ℕ) : ℤ) (2 ^ J) hL h1 h2
    rw [Finset.mem_range]
    have h4 : ((y i - (u i - 2 * (2 ^ J : ℤ))) / 2 ^ J).toNat < N / 2 ^ J + 4 := by
      have h5 : (0 : ℤ) ≤ (y i - (u i - 2 * (2 ^ J : ℤ))) / 2 ^ J := h3.1
      have h6 : ((y i - (u i - 2 * (2 ^ J : ℤ))) / 2 ^ J).toNat
          < ((N / 2 ^ J + 4 : ℕ) : ℤ).toNat := by
        have h7 : (0 : ℤ) < ((N / 2 ^ J + 4 : ℕ) : ℤ) := by positivity
        rw [Int.toNat_lt_toNat h7]
        exact h3.2.1
      have h8 : ((N / 2 ^ J + 4 : ℕ) : ℤ).toNat = N / 2 ^ J + 4 := Int.toNat_natCast _
      omega
    exact h4
  · rw [dyCell, mem_latticeBox_iff]
    intro i
    have h1 := (hbound i).1
    have h3 := ediv_nonneg_lt_and_mul_ediv_le (y i - (u i - 2 * (2 ^ J : ℤ)))
      ((N / 2 ^ J + 4 : ℕ) : ℤ) (2 ^ J) hL h1 (hbound i).2
    have h4 : (((y i - (u i - 2 * (2 ^ J : ℤ))) / 2 ^ J).toNat : ℤ)
        = (y i - (u i - 2 * (2 ^ J : ℤ))) / 2 ^ J := Int.toNat_of_nonneg h3.1
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, natToSite]
    rw [h4]
    constructor <;> linarith [h3.2.2.1, h3.2.2.2]

/-- A cell of level `≤ J` contained in `dyBig u J N` is contained in some level-`J` cell indexed by
a grid point `w - 2` with `w` in the grid. -/
theorem exists_mem_gridSet_dyCell_subset_of_subset_dyBig {d : ℕ} (u : Site d) {J N : ℕ} (p :
    ℕ × Site d) (hJ : p.1 ≤ J)
    (hin : dyCell u p.1 p.2 ⊆ dyBig u J N) :
    ∃ w ∈ gridSet d Finset.univ (N / 2 ^ J + 4),
      dyCell u p.1 p.2 ⊆ dyCell u J (natToSite w - fun _ => 2) := by
  obtain ⟨y, hy⟩ := dyCell_nonempty u p.1 p.2
  obtain ⟨w, hw, hyw⟩ := exists_mem_gridSet_mem_dyCell_of_mem_dyBig u J N y (hin hy)
  refine ⟨w, hw, ?_⟩
  rcases dyCell_subset_or_disjoint u hJ p.2 (natToSite w - fun _ => 2) with h | h
  · exact h
  · exact absurd hyw (Finset.disjoint_left.1 h hy)

/-- For a pairwise disjoint family of cells of level `≤ J` contained in `dyBig u J N`, and a
nonnegative superadditive `r`, the sum of `r` over the family is at most `r (dyBig u J N)`. -/
theorem sum_apply_dyCell_family_le_apply_dyBig {d : ℕ} (hd : 1 ≤ d) (r : Finset (Site d) →
    ℝ)
    (hrnn : ∀ a b, 0 ≤ r (latticeBox a b))
    (hrsup : ∀ B B₁ B₂, IsBoxSplit B B₁ B₂ → r B₁ + r B₂ ≤ r B) (u : Site d) (J N : ℕ)
    (fam : Finset (ℕ × Site d)) (hJ : ∀ p ∈ fam, p.1 ≤ J)
    (hin : ∀ p ∈ fam, dyCell u p.1 p.2 ⊆ dyBig u J N)
    (hdisj : ∀ p ∈ fam, ∀ q ∈ fam, p ≠ q → Disjoint (dyCell u p.1 p.2) (dyCell u q.1 q.2)) :
    ∑ p ∈ fam, r (dyCell u p.1 p.2) ≤ r (dyBig u J N) := by
  have hch : ∀ p : ℕ × Site d, ∃ w : Fin d → ℕ, p ∈ fam →
      (w ∈ gridSet d Finset.univ (N / 2 ^ J + 4) ∧
        p ∈ fam.filter (fun q => dyCell u q.1 q.2 ⊆ dyCell u J (natToSite w - fun _ => 2))) := by
    intro p
    by_cases hp : p ∈ fam
    · obtain ⟨w, hw, hsub⟩ := exists_mem_gridSet_dyCell_subset_of_subset_dyBig u p (hJ p hp) (hin p
        hp)
      exact ⟨w, fun _ => ⟨hw, Finset.mem_filter.2 ⟨hp, hsub⟩⟩⟩
    · exact ⟨0, fun h => absurd h hp⟩
  choose φ hφ using hch
  calc ∑ p ∈ fam, r (dyCell u p.1 p.2)
      ≤ ∑ w ∈ gridSet d Finset.univ (N / 2 ^ J + 4), ∑ p ∈ fam.filter (fun q =>
          dyCell u q.1 q.2 ⊆ dyCell u J (natToSite w - fun _ => 2)), r (dyCell u p.1 p.2) :=
        sum_le_sum_fiberwise_of_maps_to fam _
          (fun w => fam.filter (fun q => dyCell u q.1 q.2 ⊆ dyCell u J (natToSite w - fun _ => 2)))
          (fun p => r (dyCell u p.1 p.2)) (fun p => hrnn _ _) φ hφ
    _ ≤ ∑ w ∈ gridSet d Finset.univ (N / 2 ^ J + 4), r (dyCell u J (natToSite w - fun _ => 2)) :=
        Finset.sum_le_sum fun w _ => sum_filter_dyCell_subset_le_apply hd r hrnn hrsup u fam hdisj J
            _
    _ ≤ r (dyBig u J N) := sum_apply_dyCell_grid_le_apply_dyBig r hrnn hrsup u J N

/-- Every member of a family of cells is contained in a maximal member of the family (with respect
to containment of cells). -/
theorem exists_maximal_dyCell_containing {d : ℕ} (hd : 1 ≤ d) (u : Site d) (hvy : Finset (ℕ
    × Site d))
    (p : ℕ × Site d) (hp : p ∈ hvy) :
    ∃ q ∈ hvy, dyCell u p.1 p.2 ⊆ dyCell u q.1 q.2 ∧
      ∀ q' ∈ hvy, dyCell u q.1 q.2 ⊆ dyCell u q'.1 q'.2 → q' = q := by
  classical
  let S : Finset (ℕ × Site d) := hvy.filter (fun q => dyCell u p.1 p.2 ⊆ dyCell u q.1 q.2)
  have hne : S.Nonempty := ⟨p, Finset.mem_filter.mpr ⟨hp, subset_refl _⟩⟩
  obtain ⟨q, hq, hqmax⟩ := Finset.exists_max_image S (fun q : ℕ × Site d => q.1) hne
  refine ⟨q, (Finset.mem_filter.mp hq).1, (Finset.mem_filter.mp hq).2, ?_⟩
  intro q' hq' hsub
  have hmem : q' ∈ S := Finset.mem_filter.mpr ⟨hq', (Finset.mem_filter.mp hq).2.trans hsub⟩
  have hle : q'.1 ≤ q.1 := hqmax q' hmem
  have hle' : q.1 ≤ q'.1 := by
    by_contra hlt
    push Not at hlt
    have h := level_le_of_dyCell_subset hd u hsub
    omega
  have hjeq : q'.1 = q.1 := le_antisymm hle hle'
  have hsub'' : dyCell u q.1 q.2 ⊆ dyCell u q.1 q'.2 := by
    rw [hjeq] at hsub
    exact hsub
  have h2 : q.2 = q'.2 := eq_of_dyCell_subset_same_level u hsub''
  exact Prod.ext hjeq h2.symm

/-- The maximal members of a family of cells are pairwise disjoint. -/
theorem pairwise_disjoint_of_maximal_dyCell {d : ℕ} (u : Site d) (hvy maxl : Finset (ℕ ×
    Site d))
    (hmax : ∀ p ∈ maxl, p ∈ hvy ∧ ∀ q ∈ hvy, dyCell u p.1 p.2 ⊆ dyCell u q.1 q.2 → q = p) :
    ∀ p ∈ maxl, ∀ q ∈ maxl, p ≠ q → Disjoint (dyCell u p.1 p.2) (dyCell u q.1 q.2) := by
  intro p hp q hq hne
  rcases le_total p.1 q.1 with hle | hle
  · rcases dyCell_subset_or_disjoint u hle p.2 q.2 with hsub | hdisj
    · exfalso
      have h1 : q = p := (hmax p hp).2 q (hmax q hq).1 hsub
      exact hne h1.symm
    · exact hdisj
  · rcases dyCell_subset_or_disjoint u hle q.2 p.2 with hsub | hdisj
    · exfalso
      have h1 : p = q := (hmax q hq).2 p (hmax p hp).1 hsub
      exact hne h1
    · exact hdisj.symm

/-- The cardinality of the union of a family of cells is at most the sum of the cardinalities of the
cells in any subfamily covering it. -/
theorem card_biUnion_le_sum_card_of_maximal {d : ℕ} (u : Site d) (hvy maxl : Finset (ℕ ×
    Site d))
    (hcov : ∀ p ∈ hvy, ∃ q ∈ maxl, dyCell u p.1 p.2 ⊆ dyCell u q.1 q.2) :
    ((hvy.biUnion fun p => dyCell u p.1 p.2).card : ℝ) ≤
      ∑ q ∈ maxl, ((dyCell u q.1 q.2).card : ℝ) := by
  have hsub : hvy.biUnion (fun p => dyCell u p.1 p.2) ⊆
      maxl.biUnion (fun q => dyCell u q.1 q.2) := by
    intro y hy
    rw [Finset.mem_biUnion] at hy ⊢
    obtain ⟨p, hp, hyp⟩ := hy
    obtain ⟨q, hq, hpq⟩ := hcov p hp
    exact ⟨q, hq, hpq hyp⟩
  have h1 : (hvy.biUnion fun p => dyCell u p.1 p.2).card ≤
      (maxl.biUnion fun q => dyCell u q.1 q.2).card := Finset.card_le_card hsub
  have h2 : ((maxl.biUnion fun q => dyCell u q.1 q.2).card : ℝ) ≤
      ∑ q ∈ maxl, ((dyCell u q.1 q.2).card : ℝ) := by
    have h3 : (maxl.biUnion fun q => dyCell u q.1 q.2).card ≤
        ∑ q ∈ maxl, (dyCell u q.1 q.2).card := Finset.card_biUnion_le
    exact_mod_cast h3
  exact le_trans (by exact_mod_cast h1) h2

/-- If every cell of a heavy family `hvy` is `β`-heavy, the union of the family has cardinality at
most `r (dyBig u J N) / β`, via the pairwise disjoint maximal subfamily. -/
theorem mul_card_biUnion_le_apply_dyBig_of_heavy {d : ℕ} (hd : 1 ≤ d) (r : Finset (Site d) →
    ℝ)
    (hrnn : ∀ a b, 0 ≤ r (latticeBox a b))
    (hrsup : ∀ B B₁ B₂, IsBoxSplit B B₁ B₂ → r B₁ + r B₂ ≤ r B) (u : Site d) (J N : ℕ)
    {β : ℝ} (hβ : 0 ≤ β) (hvy : Finset (ℕ × Site d)) (hJ : ∀ p ∈ hvy, p.1 ≤ J)
    (hin : ∀ p ∈ hvy, dyCell u p.1 p.2 ⊆ dyBig u J N)
    (hheavy : ∀ p ∈ hvy, β * ((dyCell u p.1 p.2).card : ℝ) ≤ r (dyCell u p.1 p.2)) :
    β * ((hvy.biUnion fun p => dyCell u p.1 p.2).card : ℝ) ≤ r (dyBig u J N) := by
  classical
  obtain ⟨maxl, hmaxl⟩ : ∃ maxl : Finset (ℕ × Site d), maxl =
      hvy.filter (fun p => ∀ q ∈ hvy, dyCell u p.1 p.2 ⊆ dyCell u q.1 q.2 → q = p) := ⟨_, rfl⟩
  have hmax : ∀ p ∈ maxl, p ∈ hvy ∧ ∀ q ∈ hvy, dyCell u p.1 p.2 ⊆ dyCell u q.1 q.2 → q = p :=
    fun p hp => Finset.mem_filter.1 (hmaxl ▸ hp)
  have hsub : ∀ q ∈ maxl, q ∈ hvy := fun q hq => (hmax q hq).1
  have hcov : ∀ p ∈ hvy, ∃ q ∈ maxl, dyCell u p.1 p.2 ⊆ dyCell u q.1 q.2 := by
    intro p hp
    obtain ⟨q, hq, hpq, hqmax⟩ := exists_maximal_dyCell_containing hd u hvy p hp
    exact ⟨q, hmaxl ▸ Finset.mem_filter.2 ⟨hq, hqmax⟩, hpq⟩
  calc β * ((hvy.biUnion fun p => dyCell u p.1 p.2).card : ℝ)
      ≤ β * ∑ q ∈ maxl, ((dyCell u q.1 q.2).card : ℝ) :=
        mul_le_mul_of_nonneg_left (card_biUnion_le_sum_card_of_maximal u hvy maxl hcov) hβ
    _ = ∑ q ∈ maxl, β * ((dyCell u q.1 q.2).card : ℝ) := by rw [Finset.mul_sum]
    _ ≤ ∑ q ∈ maxl, r (dyCell u q.1 q.2) := Finset.sum_le_sum fun q hq => hheavy q (hsub q hq)
    _ ≤ r (dyBig u J N) := sum_apply_dyCell_family_le_apply_dyBig hd r hrnn hrsup u J N maxl
        (fun q hq => hJ q (hsub q hq)) (fun q hq => hin q (hsub q hq))
        (pairwise_disjoint_of_maximal_dyCell u hvy maxl hmax)

/-- For `n ≥ 1` there is `j` with `n ≤ 2 ^ j < 2 * n`. -/
theorem exists_pow_two_le_lt_two_mul (n : ℕ) (hn : 1 ≤ n) : ∃ j, n ≤ 2 ^ j ∧ 2 ^ j < 2 * n
    := by
  refine ⟨Nat.clog 2 n, @Nat.le_pow_clog 2 (by norm_num) n, ?_⟩
  rcases eq_or_lt_of_le hn with h | h
  · subst h
    have hc : Nat.clog 2 1 = 0 := Nat.clog_of_right_le_one le_rfl 2
    rw [hc]
    norm_num
  · have hpred : 2 ^ (Nat.clog 2 n).pred < n := @Nat.pow_pred_clog_lt_self 2 (by norm_num) n h
    have hpos : 0 < Nat.clog 2 n := @Nat.clog_pos 2 n (by norm_num) h
    have hkey : 2 ^ Nat.clog 2 n = 2 ^ (Nat.clog 2 n).pred * 2 := (Nat.pow_pred_mul hpos).symm
    rw [hkey]
    have hm := Nat.mul_lt_mul_of_pos_right hpred (by norm_num : (0:ℕ) < 2)
    rw [Nat.mul_comm n 2] at hm
    exact hm

end LatticeProb
