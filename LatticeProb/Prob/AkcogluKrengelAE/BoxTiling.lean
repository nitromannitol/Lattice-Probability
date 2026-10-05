/-
# The per-coordinate box tiling: the anchored-box theorem from the anchored-cube iteration

The library's cube theorem `LatticeProb.exists_ae_tendsto_gridAvg_univ_with_integral`
(`BoundedErgodic.lean:561`) is proved by iterating the one-parameter Birkhoff theorem over the
coordinates of `ℤ^d`, using the *same* side length `n` in every coordinate.  The frozen
`VRW.External.PointwiseErgodicCubes` needs the **anchored box** `∏ᵢ [0, ⌈N cᵢ⌉)` with
coordinate-dependent sides.

This file generalises the iteration to per-coordinate lengths: `boxGridSet s m` is the box
`∏_{i∈s}[0, mᵢ)`, and `boxAvg σ h s m` its average.  The combinatorial reindexing and the
Birkhoff identity `boxAvg_insert_eq_bAvg_boxAvg` are the exact analogues of the library's
`sum_gridSet_insert_eq_sum_range_sum_iterate` and `gridAvg_insert_eq_bAvg_gridAvg`.  No maximal
inequality is needed: the box limit is produced by the same moving-target Birkhoff argument, with
the average length running over the coordinate function `m` rather than the index.
-/
import LatticeProb.Prob.AkcogluKrengelAE.BoundedErgodic

set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

open MeasureTheory Filter Topology
open scoped BigOperators

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Coordinates in `s` range over `[0, m i)`, the others are `0`. -/
def boxGridSet {d : ℕ} (s : Finset (Fin d)) (m : Fin d → ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset fun i => if i ∈ s then Finset.range (m i) else {0}

/-- Average of `h ∘ σ z` over the box `boxGridSet s m`. -/
noncomputable def boxAvg {d : ℕ} (σ : Site d → Ω → Ω) (h : Ω → ℝ) (s : Finset (Fin d))
    (m : Fin d → ℕ) (ω : Ω) : ℝ :=
  (∑ w ∈ boxGridSet s m, h (σ (natToSite w) ω)) / ∏ i ∈ s, (m i : ℝ)

/-- The box `boxGridSet s m` has `∏_{i∈s} mᵢ` points. -/
theorem card_boxGridSet {d : ℕ} (s : Finset (Fin d)) (m : Fin d → ℕ) :
    (boxGridSet s m).card = ∏ i ∈ s, m i := by
  unfold boxGridSet
  rw [Fintype.card_piFinset]
  have hcoe : ∀ i : Fin d, (if i ∈ s then Finset.range (m i) else {0}).card
      = (if i ∈ s then m i else 1) := by
    intro i
    by_cases hi : i ∈ s <;> simp [hi]
  simp only [hcoe]
  rw [Finset.prod_ite_mem, Finset.univ_inter]

/-- A coordinate outside `s` vanishes on every point of `boxGridSet s m`. -/
theorem boxGridSet_apply_eq_zero_of_notMem {d : ℕ} {s : Finset (Fin d)} {m : Fin d → ℕ}
    {w : Fin d → ℕ} {i : Fin d} (hw : w ∈ boxGridSet s m) (hi : i ∉ s) : w i = 0 := by
  simp only [boxGridSet, Fintype.mem_piFinset] at hw
  have h := hw i
  rw [if_neg hi, Finset.mem_singleton] at h
  exact h

/-- Updating coordinate `i` of a box point in `boxGridSet s m` to a value `j` lands in
`boxGridSet (insert i s) m` iff `j < m i`. -/
theorem update_mem_boxGridSet_insert_iff {d : ℕ} {s : Finset (Fin d)} {i : Fin d}
    (_unused_hi : i ∉ s) (m : Fin d → ℕ) (w : Fin d → ℕ) (j : ℕ) (hw : w ∈ boxGridSet s m) :
    Function.update w i j ∈ boxGridSet (insert i s) m ↔ j ∈ Finset.range (m i) := by
  unfold boxGridSet at hw ⊢
  rw [Fintype.mem_piFinset] at hw ⊢
  constructor
  · intro h
    have := h i
    rw [Function.update_self, if_pos (Finset.mem_insert_self i s)] at this
    exact this
  · intro hj a
    by_cases ha : a = i
    · rw [ha, Function.update_self, if_pos (Finset.mem_insert_self i s)]
      exact hj
    · rw [Function.update_apply, if_neg ha]
      have hwa := hw a
      by_cases has : a ∈ s
      · rw [if_pos has] at hwa
        rw [if_pos (Finset.mem_insert_of_mem has)]
        exact hwa
      · rw [if_neg has] at hwa
        rw [if_neg (fun hmem => by
          rcases Finset.mem_insert.mp hmem with h' | h'
          · exact ha h'
          · exact has h')]
        exact hwa

/-- A point of `boxGridSet (insert i s) m` restricts, after zeroing coordinate `i`, to a point of
`boxGridSet s m`, with its `i`-th coordinate below `m i`. -/
theorem update_zero_mem_boxGridSet_of_mem_insert {d : ℕ} {s : Finset (Fin d)} {i : Fin d}
    (hi : i ∉ s) (m : Fin d → ℕ) (w : Fin d → ℕ) (hw : w ∈ boxGridSet (insert i s) m) :
    Function.update w i 0 ∈ boxGridSet s m ∧ w i ∈ Finset.range (m i) := by
  unfold boxGridSet at hw ⊢
  rw [Fintype.mem_piFinset] at hw ⊢
  refine ⟨?_, ?_⟩
  · intro a
    by_cases ha : a = i
    · rw [ha, Function.update_self, if_neg hi]
      exact Finset.mem_singleton.mpr rfl
    · rw [Function.update_apply, if_neg ha]
      have hwa := hw a
      by_cases has : a ∈ s
      · rw [if_pos has]
        rw [if_pos (Finset.mem_insert_of_mem has)] at hwa
        exact hwa
      · rw [if_neg has]
        have hni : ¬ a ∈ insert i s := fun hmem => by
          rcases Finset.mem_insert.mp hmem with h' | h'
          · exact ha h'
          · exact has h'
        rw [if_neg hni] at hwa
        rw [Finset.mem_singleton] at hwa ⊢
        exact hwa
  · have := hw i
    rw [if_pos (Finset.mem_insert_self i s)] at this
    exact this

/-- A sum over the box `boxGridSet (insert i s) m` splits as a sum over `boxGridSet s m` of sums
over the `m i` values of the new coordinate `i`. -/
theorem sum_boxGridSet_insert {d : ℕ} {M : Type*} [AddCommMonoid M] (s : Finset (Fin d))
    (i : Fin d) (hi : i ∉ s) (m : Fin d → ℕ) (g : (Fin d → ℕ) → M) :
    ∑ w ∈ boxGridSet (insert i s) m, g w =
      ∑ w ∈ boxGridSet s m, ∑ j ∈ Finset.range (m i), g (Function.update w i j) := by
  rw [← Finset.sum_product (boxGridSet s m) (Finset.range (m i))
        (fun p : (Fin d → ℕ) × ℕ => g (Function.update p.1 i p.2))]
  refine Finset.sum_nbij' (s := boxGridSet (insert i s) m)
    (t := boxGridSet s m ×ˢ Finset.range (m i)) (f := g)
    (g := fun p : (Fin d → ℕ) × ℕ => g (Function.update p.1 i p.2))
    (i := fun w : Fin d → ℕ => (Function.update w i 0, w i))
    (j := fun p : (Fin d → ℕ) × ℕ => Function.update p.1 i p.2) ?_ ?_ ?_ ?_ ?_
  · intro w hw
    rw [Finset.mem_product]
    exact update_zero_mem_boxGridSet_of_mem_insert hi m w hw
  · intro p hp
    rw [Finset.mem_product] at hp
    exact (update_mem_boxGridSet_insert_iff hi m p.1 p.2 hp.1).mpr hp.2
  · intro w _hw
    rw [Function.update_idem, Function.update_eq_self]
  · intro p hp
    rw [Finset.mem_product] at hp
    have h0 : p.1 i = 0 := boxGridSet_apply_eq_zero_of_notMem hp.1 hi
    apply Prod.ext
    · rw [Function.update_idem, ← h0, Function.update_eq_self]
    · rw [Function.update_self]
  · intro w _hw
    rw [Function.update_idem, Function.update_eq_self]

/-- The numerator of `boxAvg` over `insert i s` splits, via the box reindexing and the additivity
of the action, into a sum over the range of the new coordinate of sums over `boxGridSet s m`. -/
theorem sum_boxGridSet_insert_eq_sum_range_sum_iterate {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {σ : Site d → Ω → Ω}
    (hσadd : ∀ z w ω, σ (z + w) ω = σ z (σ w ω)) (h : Ω → ℝ) (s : Finset (Fin d)) (i : Fin d)
    (hi : i ∉ s) (m : Fin d → ℕ) (ω : Ω) :
    ∑ w ∈ boxGridSet (insert i s) m, h (σ (natToSite w) ω) =
      ∑ k ∈ Finset.range (m i), ∑ w ∈ boxGridSet s m,
        h (σ (natToSite w) ((σ (unit i))^[k] ω)) := by
  rw [sum_boxGridSet_insert s i hi m (fun w => h (σ (natToSite w) ω)), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _hj
  apply Finset.sum_congr rfl
  intro w hw
  rw [natToSite_update_eq_add_smul_unit w i (boxGridSet_apply_eq_zero_of_notMem hw hi) j,
      action_add_smul_unit_eq_iterate hσadd (natToSite w) i ω j,
      ← action_commute_iterate hσadd (natToSite w) (unit i) j ω]

/-- The box average over `insert i s` equals the Birkhoff average, along the action of `unit i`,
of the box average over `s`, with length `m i`. -/
theorem boxAvg_insert_eq_bAvg_boxAvg {d : ℕ} {σ : Site d → Ω → Ω}
    (hσadd : ∀ z w ω, σ (z + w) ω = σ z (σ w ω)) (h : Ω → ℝ) (s : Finset (Fin d)) (i : Fin d)
    (hi : i ∉ s) (m : Fin d → ℕ) (ω : Ω) :
    boxAvg σ h (insert i s) m ω = bAvg (σ (unit i)) (boxAvg σ h s m) (m i) ω := by
  simp only [boxAvg, bAvg, birkhoffSum]
  rw [Finset.prod_insert hi, sum_boxGridSet_insert_eq_sum_range_sum_iterate hσadd h s i hi m ω]
  rw [← Finset.sum_div, div_div, mul_comm]


end LatticeProb
