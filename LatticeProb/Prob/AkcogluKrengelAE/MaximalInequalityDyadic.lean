import LatticeProb.Prob.AkcogluKrengelAE.Defect

set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

/-!
# The maximal inequality: dyadic cells (Step 4, part B, dyadic combinatorics)

Nesting and disjointness of the dyadic cells `dyCell u j c` of a fixed offset `u`; their
cardinalities; a cell is the guillotine union of its `2 ^ d` children; and the key counting bound:
for a pairwise disjoint family of cells and a nonnegative superadditive process `r`, the sum of `r`
over the members contained in a given cell is at most `r` of that cell.
-/

open MeasureTheory Filter Topology

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A bound `μ.real (S K) ≤ c` for all `K` in a monotone family passes to the limit `μ.real (⋃ K, S
K) ≤ c`. -/
theorem measureReal_iUnion_le_of_le {μ : Measure Ω} [IsFiniteMeasure μ] {S : ℕ → Set Ω} (hS
    : Monotone S)
    {c : ℝ} (h : ∀ K, μ.real (S K) ≤ c) : μ.real (⋃ K, S K) ≤ c := by
  have hlim : Tendsto (fun K => μ (S K)) atTop (𝓝 (μ (⋃ K, S K))) := tendsto_measure_iUnion_atTop hS
  have hne : μ (⋃ K, S K) ≠ ⊤ := measure_ne_top μ _
  have h2 : Tendsto (fun K => (μ (S K)).toReal) atTop (𝓝 ((μ (⋃ K, S K)).toReal)) :=
    (ENNReal.tendsto_toReal hne).comp hlim
  have h' : ∀ K, (μ (S K)).toReal ≤ c := fun K => by
    rw [← measureReal_def]; exact h K
  exact le_of_tendsto' h2 h'


/-- The indicator of a measurable set composed with the action `τ x` is a bounded integrable
function. -/
theorem integrable_indicator_comp_action {d : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (τ : Site d → Ω → Ω) (hτ : ∀ z, MeasurePreserving (τ z) μ μ) {E : Set Ω}
    (hE : MeasurableSet E) (x : Site d) :
    Integrable (fun ω => E.indicator (fun _ => (1 : ℝ)) (τ x ω)) μ := by
  classical
  refine Integrable.of_bound ?_ 1 ?_
  · exact ((measurable_const.indicator hE).comp (hτ x).measurable).aestronglyMeasurable
  · filter_upwards with ω
    rw [Real.norm_eq_abs, Set.indicator_apply]
    split_ifs <;> norm_num

/-- The integral of the indicator of `E` composed with `τ x` equals `μ.real E`, by
measure-preservation. -/
theorem integral_indicator_comp_action_eq_measureReal {d : ℕ} {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    (τ : Site d → Ω → Ω) (hτ : ∀ z, MeasurePreserving (τ z) μ μ) {E : Set Ω}
    (hE : MeasurableSet E) (x : Site d) :
    ∫ ω, E.indicator (fun _ => (1 : ℝ)) (τ x ω) ∂μ = μ.real E := by
  classical
  have h1 : (fun ω => E.indicator (fun _ => (1 : ℝ)) (τ x ω))
      = (τ x ⁻¹' E).indicator (fun _ => (1 : ℝ)) := by
    funext ω
    exact Set.indicator_comp_right (τ x) (g := fun _ => (1 : ℝ)) (x := ω)
  rw [h1]
  have h2 : ∫ ω, (τ x ⁻¹' E).indicator (fun _ => (1 : ℝ)) ω ∂μ = μ.real (τ x ⁻¹' E) :=
    integral_indicator_one ((hτ x).measurable hE)
  rw [h2, measureReal_def, (hτ x).measure_preimage hE.nullMeasurableSet]
  rfl

/-- Summing the indicator of `E` composed with `τ` over the cube of side `N` and integrating gives
`N ^ d * μ.real E`, by stationarity. -/
theorem integral_sum_indicator_comp_action_eq_pow_mul_measureReal {d : ℕ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (τ : Site d → Ω → Ω)
    (hτ : ∀ z, MeasurePreserving (τ z) μ μ) {E : Set Ω} (hE : MeasurableSet E) (N : ℕ) :
    ∫ ω, (∑ x ∈ latticeCube d N, E.indicator (fun _ => (1 : ℝ)) (τ x ω)) ∂μ =
      (N : ℝ) ^ d * μ.real E := by
  rw [integral_finsetSum _ (fun x _ => integrable_indicator_comp_action τ hτ hE x)]
  rw [Finset.sum_congr rfl (fun x _ => integral_indicator_comp_action_eq_measureReal τ hτ hE x),
      Finset.sum_const, card_latticeCube_eq_pow',
    nsmul_eq_mul, Nat.cast_pow]

/-- In one coordinate, if `c' = c / 2 ^ (j' - j)` then the level-`j'` interval at `c'` contains the
level-`j` interval at `c`. -/
theorem two_pow_mul_le_and_le_of_ediv_eq {j j' : ℕ} (hjj : j ≤ j') (c c' : ℤ) (h : c / 2 ^
    (j' - j) = c') :
    (2 : ℤ) ^ j' * c' ≤ 2 ^ j * c ∧ 2 ^ j * c + 2 ^ j ≤ 2 ^ j' * c' + 2 ^ j' := by
  have hq : c = 2 ^ (j' - j) * c' + c % 2 ^ (j' - j) := by
    rw [← h]; exact (Int.mul_ediv_add_emod c (2 ^ (j' - j))).symm
  have h0 : 0 ≤ c % 2 ^ (j' - j) := Int.emod_nonneg c (by positivity)
  have h1 : c % 2 ^ (j' - j) < 2 ^ (j' - j) := Int.emod_lt_of_pos c (by positivity)
  have hpow : (2 : ℤ) ^ j' = 2 ^ j * 2 ^ (j' - j) := by rw [← pow_add, Nat.add_sub_cancel' hjj]
  have hpj : (0 : ℤ) < 2 ^ j := by positivity
  constructor
  · rw [hpow]; nlinarith [hq, h0, hpj]
  · rw [hpow]; nlinarith [hq, h1, hpj]

/-- In one coordinate, if `c' ≠ c / 2 ^ (j' - j)` then the level-`j` and level-`j'` intervals are
disjoint, lying on one side or the other. -/
theorem two_pow_mul_add_le_or_le_of_ediv_ne {j j' : ℕ} (hjj : j ≤ j') (c c' : ℤ) (h : c / 2
    ^ (j' - j) ≠ c') :
    2 ^ j * c + 2 ^ j ≤ (2 : ℤ) ^ j' * c' ∨ (2 : ℤ) ^ j' * c' + 2 ^ j' ≤ 2 ^ j * c := by
  have hq : c = 2 ^ (j' - j) * (c / 2 ^ (j' - j)) + c % 2 ^ (j' - j) :=
    (Int.mul_ediv_add_emod c (2 ^ (j' - j))).symm
  have h0 : 0 ≤ c % 2 ^ (j' - j) := Int.emod_nonneg c (by positivity)
  have h1 : c % 2 ^ (j' - j) < 2 ^ (j' - j) := Int.emod_lt_of_pos c (by positivity)
  have hpow : (2 : ℤ) ^ j' = 2 ^ j * 2 ^ (j' - j) := by
    rw [← pow_add, Nat.add_sub_cancel' hjj]
  have hA : (0 : ℤ) ≤ 2 ^ j := by positivity
  have hB : (0 : ℤ) ≤ 2 ^ (j' - j) := by positivity
  rcases lt_or_gt_of_ne h with hlt | hgt
  · left
    have hQ : c / 2 ^ (j' - j) + 1 ≤ c' := by omega
    have hR : c % 2 ^ (j' - j) + 1 ≤ 2 ^ (j' - j) := by omega
    have hc1 : c + 1 ≤ 2 ^ (j' - j) * (c / 2 ^ (j' - j) + 1) := by
      nlinarith [hq, hR]
    have hc2 : 2 ^ (j' - j) * (c / 2 ^ (j' - j) + 1) ≤ 2 ^ (j' - j) * c' :=
      mul_le_mul_of_nonneg_left hQ hB
    have hc : c + 1 ≤ 2 ^ (j' - j) * c' := le_trans hc1 hc2
    calc 2 ^ j * c + 2 ^ j = 2 ^ j * (c + 1) := by ring
      _ ≤ 2 ^ j * (2 ^ (j' - j) * c') := mul_le_mul_of_nonneg_left hc hA
      _ = 2 ^ j' * c' := by rw [hpow]; ring
  · right
    have hQ : c' + 1 ≤ c / 2 ^ (j' - j) := by omega
    have hc1 : 2 ^ (j' - j) * (c' + 1) ≤ 2 ^ (j' - j) * (c / 2 ^ (j' - j)) :=
      mul_le_mul_of_nonneg_left hQ hB
    have hc2 : 2 ^ (j' - j) * (c / 2 ^ (j' - j)) ≤ c := by
      nlinarith [hq, h0]
    have hc : 2 ^ (j' - j) * (c' + 1) ≤ c := le_trans hc1 hc2
    calc 2 ^ j' * c' + 2 ^ j' = 2 ^ j' * (c' + 1) := by ring
      _ = 2 ^ j * (2 ^ (j' - j) * (c' + 1)) := by rw [hpow]; ring
      _ ≤ 2 ^ j * c := mul_le_mul_of_nonneg_left hc hA

/-- If every coordinate's level-`j` interval lies inside the level-`j'` interval, the dyadic cell of
level `j` is contained in the one of level `j'`. -/
theorem dyCell_subset_of_forall_le {d : ℕ} (u : Site d) {j j' : ℕ} (c c' : Site d)
    (h : ∀ i, (2 : ℤ) ^ j' * c' i ≤ 2 ^ j * c i ∧ 2 ^ j * c i + 2 ^ j ≤ 2 ^ j' * c' i + 2 ^ j') :
    dyCell u j c ⊆ dyCell u j' c' := by
  intro y hy
  rw [dyCell, mem_latticeBox_iff] at hy ⊢
  intro i
  have h1 := hy i
  have h2 := h i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2 ⊢
  constructor <;> linarith

/-- If some coordinate's level-`j` and level-`j'` intervals are separated, the two dyadic cells are
disjoint. -/
theorem disjoint_dyCell_of_le_or_le {d : ℕ} (u : Site d) {j j' : ℕ} (c c' : Site d) (i : Fin
    d)
    (h : 2 ^ j * c i + 2 ^ j ≤ (2 : ℤ) ^ j' * c' i ∨ (2 : ℤ) ^ j' * c' i + 2 ^ j' ≤ 2 ^ j * c i) :
    Disjoint (dyCell u j c) (dyCell u j' c') := by
  rw [Finset.disjoint_left]
  intro y hy hy'
  rw [dyCell, mem_latticeBox_iff] at hy hy'
  have h1 := hy i
  have h2 := hy' i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
  rcases h with h | h <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- Two dyadic cells of the same offset, with levels `j ≤ j'`, are either nested or disjoint. -/
theorem dyCell_subset_or_disjoint {d : ℕ} (u : Site d) {j j' : ℕ} (hjj : j ≤ j') (c c' :
    Site d) :
    dyCell u j c ⊆ dyCell u j' c' ∨ Disjoint (dyCell u j c) (dyCell u j' c') := by
  by_cases h : ∀ i, c i / 2 ^ (j' - j) = c' i
  · exact Or.inl (dyCell_subset_of_forall_le u c c' fun i => two_pow_mul_le_and_le_of_ediv_eq hjj (c
      i) (c' i) (h i))
  · push Not at h
    obtain ⟨i, hi⟩ := h
    exact Or.inr (disjoint_dyCell_of_le_or_le u c c' i (two_pow_mul_add_le_or_le_of_ediv_ne hjj (c
        i) (c' i) hi))

/-- The half-box description with no coordinate cut is the parent cell at level `j + 1`. -/
theorem latticeBox_zero_eq_dyCell_succ {d : ℕ} (u : Site d) (j : ℕ) (c : Site d) :
    latticeBox (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * (((0 : Fin d → ℕ) l : ℕ) : ℤ))
      (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * (((0 : Fin d → ℕ) l : ℕ) : ℤ) +
        (if l ∈ (∅ : Finset (Fin d)) then (2 : ℤ) ^ j else 2 ^ (j + 1)) - 1) =
      dyCell u (j + 1) c := by
  rw [dyCell]
  congr 1 <;> funext l <;>
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Finset.notMem_empty,
      if_false, Nat.cast_zero, mul_zero, add_zero] <;>
    ring

/-- Cutting coordinate `i ∉ s` of a half-box at its lower half matches the half-box description over
`insert i s` at the grid point updated to `0`. -/
theorem latticeBox_update_zero_eq_latticeBox_insert {d : ℕ} (u : Site d) (j : ℕ) (c : Site
    d) (s : Finset (Fin d))
    (i : Fin d) (hi : i ∉ s) (w : Fin d → ℕ) (hw : w i = 0) :
    latticeBox (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((w l : ℕ) : ℤ))
        (Function.update (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((w l : ℕ) : ℤ) +
          (if l ∈ s then (2 : ℤ) ^ j else 2 ^ (j + 1)) - 1) i
          ((u i + 2 ^ (j + 1) * c i + 2 ^ j * ((w i : ℕ) : ℤ) + 2 ^ j) - 1)) =
      latticeBox (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((Function.update w i 0 l : ℕ) : ℤ))
      (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((Function.update w i 0 l : ℕ) : ℤ) +
        (if l ∈ insert i s then (2 : ℤ) ^ j else 2 ^ (j + 1)) - 1) := by
  congr 1 <;> funext l <;>
    simp only [Function.update_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mem_insert] <;>
    by_cases hl : l = i <;>
      simp only [hl, ↓reduceIte, hw, hi, not_false_eq_true, true_or, false_or] <;>
      ring

/-- Cutting coordinate `i ∉ s` of a half-box at its upper half matches the half-box description over
`insert i s` at the grid point updated to `1`. -/
theorem latticeBox_update_one_eq_latticeBox_insert {d : ℕ} (u : Site d) (j : ℕ) (c : Site d)
    (s : Finset (Fin d))
    (i : Fin d) (hi : i ∉ s) (w : Fin d → ℕ) (hw : w i = 0) :
    latticeBox (Function.update (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((w l : ℕ) : ℤ)) i
        (u i + 2 ^ (j + 1) * c i + 2 ^ j * ((w i : ℕ) : ℤ) + 2 ^ j))
        (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((w l : ℕ) : ℤ) +
          (if l ∈ s then (2 : ℤ) ^ j else 2 ^ (j + 1)) - 1) =
      latticeBox (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((Function.update w i 1 l : ℕ) : ℤ))
      (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((Function.update w i 1 l : ℕ) : ℤ) +
        (if l ∈ insert i s then (2 : ℤ) ^ j else 2 ^ (j + 1)) - 1) := by
  congr 1 <;> funext l <;>
    simp only [Function.update_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mem_insert] <;>
    by_cases hl : l = i <;>
      simp only [hl, ↓reduceIte, hw, hi, not_false_eq_true, true_or, false_or] <;>
      ring

/-- Cutting coordinate `i ∉ s` of a half-box is an `IsBoxSplit` into the two half-boxes over `insert
i s`. -/
theorem isBoxSplit_latticeBox_update_insert {d : ℕ} (u : Site d) (j : ℕ) (c : Site d) (s :
    Finset (Fin d))
    (i : Fin d) (hi : i ∉ s) (w : Fin d → ℕ) (hw : w i = 0) :
    IsBoxSplit (latticeBox (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((w l : ℕ) : ℤ))
        (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((w l : ℕ) : ℤ) +
          (if l ∈ s then (2 : ℤ) ^ j else 2 ^ (j + 1)) - 1))
      (latticeBox (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((Function.update w i 0 l : ℕ) : ℤ))
        (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((Function.update w i 0 l : ℕ) : ℤ) +
          (if l ∈ insert i s then (2 : ℤ) ^ j else 2 ^ (j + 1)) - 1))
      (latticeBox (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((Function.update w i 1 l : ℕ) : ℤ))
        (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((Function.update w i 1 l : ℕ) : ℤ) +
          (if l ∈ insert i s then (2 : ℤ) ^ j else 2 ^ (j + 1)) - 1)) := by
  rw [← latticeBox_update_zero_eq_latticeBox_insert u j c s i hi w hw, ←
      latticeBox_update_one_eq_latticeBox_insert u j c s i hi w hw]
  have hp : (0 : ℤ) < 2 ^ j := by positivity
  apply isBoxSplit_latticeBox_update_of_mem
  · show u i + 2 ^ (j + 1) * c i + 2 ^ j * ((w i : ℕ) : ℤ) ≤
      u i + 2 ^ (j + 1) * c i + 2 ^ j * ((w i : ℕ) : ℤ) + 2 ^ j
    linarith
  · show u i + 2 ^ (j + 1) * c i + 2 ^ j * ((w i : ℕ) : ℤ) + 2 ^ j ≤
      u i + 2 ^ (j + 1) * c i + 2 ^ j * ((w i : ℕ) : ℤ) +
        (if i ∈ s then (2 : ℤ) ^ j else 2 ^ (j + 1)) - 1 + 1
    rw [if_neg hi, pow_succ]
    linarith

/-- For a superadditive `r`, the sum of `r` over the `2 ^ s.card` half-boxes cut along `s` is at
most `r` of the parent cell at level `j + 1`. -/
theorem sum_gridSet_two_le_apply_dyCell_succ {d : ℕ} (r : Finset (Site d) → ℝ)
    (hrsup : ∀ B B₁ B₂, IsBoxSplit B B₁ B₂ → r B₁ + r B₂ ≤ r B) (u : Site d) (j : ℕ)
    (c : Site d) (s : Finset (Fin d)) :
    ∑ w ∈ gridSet d s 2, r (latticeBox (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((w l : ℕ) : ℤ))
        (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((w l : ℕ) : ℤ) +
          (if l ∈ s then (2 : ℤ) ^ j else 2 ^ (j + 1)) - 1)) ≤
      r (dyCell u (j + 1) c) := by
  induction s using Finset.induction with
  | empty =>
    rw [gridSet_empty, Finset.sum_singleton]
    exact le_of_eq (congrArg r (latticeBox_zero_eq_dyCell_succ u j c))
  | insert i s hi ih =>
    rw [sum_gridSet_insert s i hi 2 (fun w => r (latticeBox (fun l => u l + 2 ^ (j + 1) * c l + 2 ^
        j * ((w l : ℕ) : ℤ))
        (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((w l : ℕ) : ℤ) +
          (if l ∈ insert i s then (2 : ℤ) ^ j else 2 ^ (j + 1)) - 1)))]
    refine le_trans (Finset.sum_le_sum fun w hw => ?_) ih
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    exact hrsup _ _ _ (isBoxSplit_latticeBox_update_insert u j c s i hi w
        (gridSet_apply_eq_zero_of_notMem hw hi))

/-- The dyadic cell at index `2c + e`, `e ∈ {0, 1}^d`, equals the half-box description at grid point
`e`. -/
theorem dyCell_two_smul_add_eq_latticeBox {d : ℕ} (u : Site d) (j : ℕ) (c : Site d) (e : Fin
    d → Fin 2) :
    dyCell u j ((2 : ℤ) • c + fun i => ((e i : ℕ) : ℤ)) =
      latticeBox (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((e l : ℕ) : ℤ))
        (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((e l : ℕ) : ℤ) +
          (if l ∈ (Finset.univ : Finset (Fin d)) then (2 : ℤ) ^ j else 2 ^ (j + 1)) - 1) := by
  rw [dyCell]
  congr 1 <;> funext l <;>
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mem_univ, if_true] <;>
    ring

/-- A sum over `{0, 1}^d`, viewed as `Fin d → Fin 2`, reindexes as a sum over `gridSet d Finset.univ
2`. -/
theorem sum_finTwo_eq_sum_gridSet_univ_two {d : ℕ} {M : Type*} [AddCommMonoid M] (g : (Fin d
    → ℕ) → M) :
    ∑ e : Fin d → Fin 2, g (fun i => (e i : ℕ)) = ∑ w ∈ gridSet d Finset.univ 2, g w := by
  refine Finset.sum_nbij' (fun (e : Fin d → Fin 2) => fun i => (e i : ℕ))
    (fun (w : Fin d → ℕ) => fun i => (⟨w i % 2, Nat.mod_lt _ two_pos⟩ : Fin 2)) ?_ ?_ ?_ ?_ ?_
  · intro e _
    rw [gridSet, Fintype.mem_piFinset]
    intro i
    simp only [Finset.mem_univ, if_true, Finset.mem_range]
    exact (e i).isLt
  · intro w _
    exact Finset.mem_univ _
  · intro e _
    funext i
    simp only [Fin.ext_iff]
    exact Nat.mod_eq_of_lt (e i).isLt
  · intro w hw
    funext i
    simp only []
    have h2 : w i < 2 := by
      have h3 : w ∈ Fintype.piFinset (fun i : Fin d => if i ∈ Finset.univ then Finset.range 2 else
          {0}) := by
        simpa only [gridSet] using hw
      have h4 := (Fintype.mem_piFinset.mp h3) i
      simpa using h4
    exact Nat.mod_eq_of_lt h2
  · intro e _
    rfl

/-- For a superadditive `r`, the sum of `r` over the `2 ^ d` children of a dyadic cell is at most
`r` of the cell. -/
theorem sum_apply_dyCell_children_le_apply_dyCell_succ {d : ℕ} (r : Finset (Site d) → ℝ)
    (hrsup : ∀ B B₁ B₂, IsBoxSplit B B₁ B₂ → r B₁ + r B₂ ≤ r B) (u : Site d) (j : ℕ)
    (c : Site d) :
    ∑ e : Fin d → Fin 2, r (dyCell u j ((2 : ℤ) • c + fun i => ((e i : ℕ) : ℤ))) ≤
      r (dyCell u (j + 1) c) := by
  calc ∑ e : Fin d → Fin 2, r (dyCell u j ((2 : ℤ) • c + fun i => ((e i : ℕ) : ℤ)))
      = ∑ e : Fin d → Fin 2, (fun w : Fin d → ℕ => r (latticeBox (fun l => u l + 2 ^ (j + 1) * c l +
          2 ^ j * ((w l : ℕ) : ℤ))
            (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((w l : ℕ) : ℤ) +
              (if l ∈ (Finset.univ : Finset (Fin d)) then (2 : ℤ) ^ j else 2 ^ (j + 1)) - 1))) (fun
                  i => (e i : ℕ)) :=
        Finset.sum_congr rfl fun e _ => by rw [dyCell_two_smul_add_eq_latticeBox u j c e]
    _ = ∑ w ∈ gridSet d Finset.univ 2, r (latticeBox (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((w
        l : ℕ) : ℤ))
            (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((w l : ℕ) : ℤ) +
              (if l ∈ (Finset.univ : Finset (Fin d)) then (2 : ℤ) ^ j else 2 ^ (j + 1)) - 1)) :=
        sum_finTwo_eq_sum_gridSet_univ_two (fun w : Fin d → ℕ => r (latticeBox (fun l => u l + 2 ^
            (j + 1) * c l + 2 ^ j * ((w l : ℕ) : ℤ))
            (fun l => u l + 2 ^ (j + 1) * c l + 2 ^ j * ((w l : ℕ) : ℤ) +
              (if l ∈ (Finset.univ : Finset (Fin d)) then (2 : ℤ) ^ j else 2 ^ (j + 1)) - 1)))
    _ ≤ r (dyCell u (j + 1) c) := sum_gridSet_two_le_apply_dyCell_succ r hrsup u j c Finset.univ

/-- Every dyadic cell is nonempty, containing its lower corner. -/
theorem dyCell_nonempty {d : ℕ} (u : Site d) (j : ℕ) (c : Site d) :
    (dyCell u j c).Nonempty := by
  refine ⟨fun l => u l + 2 ^ j * c l, ?_⟩
  rw [dyCell, latticeBox, Finset.mem_Icc]
  refine ⟨le_refl _, ?_⟩
  rw [Pi.le_def]
  intro l
  have h : (1 : ℤ) ≤ (2 : ℤ) ^ j := one_le_pow₀ (show (1 : ℤ) ≤ 2 by norm_num)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linarith

/-- A dyadic cell of level `j` has `(2 ^ j) ^ d` sites. -/
theorem card_dyCell_eq_pow {d : ℕ} (u : Site d) (j : ℕ) (c : Site d) :
    (dyCell u j c).card = (2 ^ j) ^ d := by
  have h : dyCell u j c = (latticeCube d (2 ^ j)).map
      (Equiv.addRight (u + (2 ^ j : ℤ) • c)).toEmbedding := by
    rw [dyCell, map_addRight_latticeCube_eq_latticeBox]
    congr 1
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [h, Finset.card_map, card_latticeCube_eq_pow']

/-- If a level-`j'` cell is contained in a level-`j` cell, then `j' ≤ j`, by comparing
cardinalities. -/
theorem level_le_of_dyCell_subset {d : ℕ} (hd : 1 ≤ d) (u : Site d) {j j' : ℕ} {c c' : Site
    d}
    (h : dyCell u j' c' ⊆ dyCell u j c) : j' ≤ j := by
  have hcard := Finset.card_le_card h
  rw [card_dyCell_eq_pow u j' c', card_dyCell_eq_pow u j c] at hcard
  have h1 : 2 ^ j' ≤ 2 ^ j :=
    (Nat.pow_le_pow_iff_left (by omega : d ≠ 0)).mp hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1

/-- Two cells of the same level, one contained in the other, have the same index. -/
theorem eq_of_dyCell_subset_same_level {d : ℕ} (u : Site d) {j : ℕ} {c c' : Site d}
    (h : dyCell u j c' ⊆ dyCell u j c) : c' = c := by
  have hcell : ∀ (c : Site d), dyCell u j c = latticeBox (fun l => u l + 2 ^ j * c l)
      (fun l => u l + 2 ^ j * c l + 2 ^ j - 1) := by
    intro c
    rw [dyCell]
    congr 1 <;> funext l <;> simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] <;> ring
  have h1 : ∀ l, u l + 2 ^ j * c l ≤ u l + 2 ^ j * c' l := by
    have hmem : (fun l => u l + 2 ^ j * c' l) ∈ dyCell u j c' := by
      rw [hcell]
      rw [mem_latticeBox_iff]
      intro l
      constructor
      · exact le_refl _
      · have h5 : (1 : ℤ) ≤ 2 ^ j := one_le_pow₀ (show (1 : ℤ) ≤ 2 by norm_num)
        linarith
    have h2 := h hmem
    rw [hcell, mem_latticeBox_iff] at h2
    intro l
    exact (h2 l).1
  have h3 : ∀ l, u l + 2 ^ j * c' l ≤ u l + 2 ^ j * c l := by
    have hmem : (fun l => u l + 2 ^ j * c' l + 2 ^ j - 1) ∈ dyCell u j c' := by
      rw [hcell]
      rw [mem_latticeBox_iff]
      intro l
      constructor
      · have h5 : (1 : ℤ) ≤ 2 ^ j := one_le_pow₀ (show (1 : ℤ) ≤ 2 by norm_num)
        linarith
      · exact le_refl _
    have h2 := h hmem
    rw [hcell, mem_latticeBox_iff] at h2
    intro l
    have h4 := (h2 l).2
    have h5 : (1 : ℤ) ≤ 2 ^ j := one_le_pow₀ (show (1 : ℤ) ≤ 2 by norm_num)
    linarith
  funext l
  have h6 := h1 l
  have h7 := h3 l
  have h8 : (0 : ℤ) < 2 ^ j := by positivity
  nlinarith [h6, h7]

/-- If a level-`j'` cell with `j ≤ j'` is contained in a level-`j` cell, the two cells coincide. -/
theorem eq_of_dyCell_subset_level_le {d : ℕ} (hd : 1 ≤ d) (u : Site d) {j j' : ℕ} {c c' :
    Site d}
    (hsub : dyCell u j' c' ⊆ dyCell u j c) (hle : j ≤ j') : (j', c') = (j, c) := by
  have hcard := Finset.card_le_card hsub
  rw [card_dyCell_eq_pow u j' c', card_dyCell_eq_pow u j c] at hcard
  have h1 : 2 ^ j' ≤ 2 ^ j := (Nat.pow_le_pow_iff_left (by omega : d ≠ 0)).mp hcard
  have h2 : j' ≤ j := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
  have h3 : j' = j := le_antisymm h2 hle
  subst h3
  have h4 : c' = c := eq_of_dyCell_subset_same_level u hsub
  rw [h4]

/-- In a pairwise disjoint family of cells, the sum of `r` over the members contained in a given
member `(j, c)` of the family is exactly `r` of that member. -/
theorem sum_filter_dyCell_subset_eq_apply {d : ℕ} (r : Finset (Site d) → ℝ) (u : Site d)
    (fam : Finset (ℕ × Site d))
    (hdisj : ∀ p ∈ fam, ∀ q ∈ fam, p ≠ q → Disjoint (dyCell u p.1 p.2) (dyCell u q.1 q.2))
    (j : ℕ) (c : Site d) (hmem : (j, c) ∈ fam) :
    ∑ p ∈ fam.filter (fun p => dyCell u p.1 p.2 ⊆ dyCell u j c), r (dyCell u p.1 p.2) =
      r (dyCell u j c) := by
  have h1 : fam.filter (fun p => dyCell u p.1 p.2 ⊆ dyCell u j c) = {(j, c)} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨Finset.mem_filter.mpr ⟨hmem, subset_refl _⟩, ?_⟩
    intro p hp
    obtain ⟨hpf, hpsub⟩ := Finset.mem_filter.mp hp
    by_contra hne
    have hdis := hdisj p hpf (j, c) hmem hne
    obtain ⟨y, hy⟩ := dyCell_nonempty u p.1 p.2
    exact Finset.disjoint_left.1 hdis hy (hpsub hy)
  rw [h1, Finset.sum_singleton]

/-- Every point of a level-`(j + 1)` cell lies in one of its `2 ^ d` level-`j` children. -/
theorem mem_dyCell_child_of_mem_dyCell_succ {d : ℕ} (u : Site d) (j : ℕ) (c y : Site d)
    (hy : y ∈ dyCell u (j + 1) c) :
    ∃ e : Fin d → Fin 2, y ∈ dyCell u j ((2 : ℤ) • c + fun i => ((e i : ℕ) : ℤ)) := by
  have hy' : ∀ i, u i + 2 ^ (j + 1) * c i ≤ y i ∧
      y i ≤ u i + 2 ^ (j + 1) * c i + 2 ^ (j + 1) - 1 := by
    have h := hy
    rw [dyCell, mem_latticeBox_iff] at h
    intro i
    have h1 := (h i).1
    have h2 := (h i).2
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
    refine ⟨h1, ?_⟩
    linarith
  refine ⟨fun i => if y i < u i + 2 ^ (j + 1) * c i + 2 ^ j then 0 else 1, ?_⟩
  rw [dyCell, mem_latticeBox_iff]
  intro i
  have h1 := hy' i
  have h2 : (2 : ℤ) ^ (j + 1) = 2 ^ j * 2 := by rw [pow_succ]
  by_cases hc : y i < u i + 2 ^ (j + 1) * c i + 2 ^ j
  · simp only [hc, ↓reduceIte, Fin.val_zero, Nat.cast_zero, add_zero, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    have h4 : 2 ^ j * (2 * c i) = 2 ^ (j + 1) * c i := by rw [h2]; ring
    constructor
    · rw [h4]; exact h1.1
    · rw [h4]; linarith [h1.2]
  · simp only [hc, ↓reduceIte, Fin.val_one, Nat.cast_one, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    push Not at hc
    have h4 : 2 ^ j * (2 * c i + 1) = 2 ^ (j + 1) * c i + 2 ^ j := by rw [h2]; ring
    constructor
    · rw [h4]; linarith [hc]
    · rw [h4]; linarith [h1.2]

/-- A cell of level `≤ j` contained in a level-`(j + 1)` cell is contained in one of its level-`j`
children. -/
theorem dyCell_subset_child_of_subset_succ {d : ℕ} (u : Site d) {j j' : ℕ} (c c' : Site d)
    (hle : j' ≤ j)
    (h : dyCell u j' c' ⊆ dyCell u (j + 1) c) :
    ∃ e : Fin d → Fin 2, dyCell u j' c' ⊆ dyCell u j ((2 : ℤ) • c + fun i => ((e i : ℕ) : ℤ)) := by
  obtain ⟨y, hy⟩ := dyCell_nonempty u j' c'
  obtain ⟨e, he⟩ := mem_dyCell_child_of_mem_dyCell_succ u j c y (h hy)
  refine ⟨e, ?_⟩
  rcases dyCell_subset_or_disjoint u hle c' ((2 : ℤ) • c + fun i => ((e i : ℕ) : ℤ)) with h1 | h1
  · exact h1
  · exact absurd he (Finset.disjoint_left.1 h1 hy)

/-- A sum over a finite set is at most the sum, over a family of fibres indexed by `I` and
containing the corresponding elements, of the sum over each fibre, for nonnegative summands. -/
theorem sum_le_sum_fiberwise_of_maps_to {α β : Type*} [DecidableEq β] (T : Finset α) (I :
    Finset β)
    (A : β → Finset α) (g : α → ℝ) (hg : ∀ p, 0 ≤ g p) (φ : α → β)
    (hφ : ∀ p ∈ T, φ p ∈ I ∧ p ∈ A (φ p)) :
    ∑ p ∈ T, g p ≤ ∑ b ∈ I, ∑ p ∈ A b, g p := by
  rw [← Finset.sum_fiberwise_of_maps_to (fun p hp => (hφ p hp).1) g]
  refine Finset.sum_le_sum fun b hb => ?_
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro p hp
    obtain ⟨hpT, hpb⟩ := Finset.mem_filter.mp hp
    subst hpb
    exact (hφ p hpT).2
  · intro p _ _
    exact hg p

/-- A member of a family, contained in a cell `(j, c)` not itself in the family, has strictly
smaller level than `j`. -/
theorem level_lt_of_dyCell_subset_of_notMem {d : ℕ} (hd : 1 ≤ d) (u : Site d) (fam : Finset
    (ℕ × Site d))
    {j : ℕ} {c : Site d} (hmem : (j, c) ∉ fam) (p : ℕ × Site d) (hp : p ∈ fam)
    (hsub : dyCell u p.1 p.2 ⊆ dyCell u j c) : p.1 < j := by
  by_contra hlt
  push Not at hlt
  have h := eq_of_dyCell_subset_level_le hd u hsub hlt
  exact hmem (by rw [← h]; exact hp)

/-- For a pairwise disjoint family of cells and a nonnegative superadditive `r`, the sum of `r` over
the members contained in a given cell is at most `r` of that cell. -/
theorem sum_filter_dyCell_subset_le_apply {d : ℕ} (hd : 1 ≤ d) (r : Finset (Site d) → ℝ)
    (hrnn : ∀ a b, 0 ≤ r (latticeBox a b))
    (hrsup : ∀ B B₁ B₂, IsBoxSplit B B₁ B₂ → r B₁ + r B₂ ≤ r B) (u : Site d)
    (fam : Finset (ℕ × Site d))
    (hdisj : ∀ p ∈ fam, ∀ q ∈ fam, p ≠ q → Disjoint (dyCell u p.1 p.2) (dyCell u q.1 q.2))
    (j : ℕ) (c : Site d) :
    ∑ p ∈ fam.filter (fun p => dyCell u p.1 p.2 ⊆ dyCell u j c), r (dyCell u p.1 p.2) ≤
      r (dyCell u j c) := by
  induction j generalizing c with
  | zero =>
    by_cases hmem : ((0 : ℕ), c) ∈ fam
    · exact le_of_eq (sum_filter_dyCell_subset_eq_apply r u fam hdisj 0 c hmem)
    · rw [Finset.sum_eq_zero fun p hp => absurd (level_lt_of_dyCell_subset_of_notMem hd u fam hmem p
        (Finset.mem_filter.1 hp).1 (Finset.mem_filter.1 hp).2) (Nat.not_lt_zero _)]
      exact hrnn _ _
  | succ j ih =>
    by_cases hmem : (j + 1, c) ∈ fam
    · exact le_of_eq (sum_filter_dyCell_subset_eq_apply r u fam hdisj (j + 1) c hmem)
    · have hch : ∀ p : ℕ × Site d, ∃ e : Fin d → Fin 2,
          p ∈ fam.filter (fun p => dyCell u p.1 p.2 ⊆ dyCell u (j + 1) c) →
            (e ∈ (Finset.univ : Finset (Fin d → Fin 2)) ∧
              p ∈ fam.filter (fun q => dyCell u q.1 q.2 ⊆
                dyCell u j ((2 : ℤ) • c + fun i => ((e i : ℕ) : ℤ)))) := by
        intro p
        by_cases hp : p ∈ fam.filter (fun p => dyCell u p.1 p.2 ⊆ dyCell u (j + 1) c)
        · obtain ⟨hpf, hps⟩ := Finset.mem_filter.1 hp
          obtain ⟨e, he⟩ := dyCell_subset_child_of_subset_succ u c p.2
            (Nat.lt_succ_iff.1 (level_lt_of_dyCell_subset_of_notMem hd u fam hmem p hpf hps)) hps
          exact ⟨e, fun _ => ⟨Finset.mem_univ _, Finset.mem_filter.2 ⟨hpf, he⟩⟩⟩
        · exact ⟨0, fun h => absurd h hp⟩
      choose φ hφ using hch
      calc _ ≤ ∑ e : Fin d → Fin 2, ∑ p ∈ fam.filter (fun q => dyCell u q.1 q.2 ⊆
              dyCell u j ((2 : ℤ) • c + fun i => ((e i : ℕ) : ℤ))), r (dyCell u p.1 p.2) :=
            sum_le_sum_fiberwise_of_maps_to (fam.filter (fun p => dyCell u p.1 p.2 ⊆ dyCell u (j +
                1) c))
              (Finset.univ : Finset (Fin d → Fin 2))
              (fun e : Fin d → Fin 2 => fam.filter (fun q => dyCell u q.1 q.2 ⊆
                dyCell u j ((2 : ℤ) • c + fun i => ((e i : ℕ) : ℤ))))
              (fun p => r (dyCell u p.1 p.2)) (fun p => hrnn _ _) φ hφ
        _ ≤ ∑ e : Fin d → Fin 2, r (dyCell u j ((2 : ℤ) • c + fun i => ((e i : ℕ) : ℤ))) :=
            Finset.sum_le_sum fun e _ => ih _
        _ ≤ r (dyCell u (j + 1) c) := sum_apply_dyCell_children_le_apply_dyCell_succ r hrsup u j c

end LatticeProb
