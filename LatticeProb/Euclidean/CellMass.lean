import Mathlib

/-!
# The cell mass of a set

Let `c : ι → Set E` be a family of cells (for instance the cells of a cell configuration of the
plane) and `μ` a measure. The *cell mass* of a set `S` counts the cells meeting `S`, each with the
fraction of its measure that lies in `S`:
`cellMass μ c S = ∑' i, μ (c i ∩ S) / μ (c i)`.

This is the quantity in the definition (2.1) of the capped squares `Ŝ_m^z` of Gwynne, Miller and
Sheffield, *An invariance principle for ergodic scale-free random environments* (arXiv
1807.07515): `Ŝ_m^z` is the largest dyadic square containing `z` whose cell mass is at most `m`.
Counting the fractional parts of the cells meeting the boundary makes the mass strictly increasing
along nested squares (the observation in the proof of their Lemma 2.2); this is proved here for any
chain of sets whose increments have positive measure.

Main results:
* `cellMass_mono`, `cellMass_add_diff` (additivity), `cellMass_le_card`, and `cellMass_ne_top`
  (the mass of a compact set is finite for a locally finite family of cells);
* `cellMass_pos` and `cellMass_lt_cellMass` (strict increase when the cells cover the increment
  and have finite measure, and the increment has positive measure), `strictMono_cellMass`;
* `cellMass_image`: invariance under an injective map multiplying the measure by a constant, and
  `cellMass_image_smul_add` for the similarities `z ↦ r • z + b` of a finite-dimensional real
  normed space with an additive Haar measure.
-/

open MeasureTheory Set
open scoped ENNReal Pointwise

namespace LatticeProb.CellMass

variable {E ι : Type*} [MeasurableSpace E]

/-- The cell mass of `S`: the sum over the cells of the fraction of their measure lying in `S`
(Gwynne, Miller and Sheffield, arXiv 1807.07515, (2.1)). -/
noncomputable def cellMass (μ : Measure E) (c : ι → Set E) (S : Set E) : ℝ≥0∞ :=
  ∑' i, μ (c i ∩ S) / μ (c i)

variable (μ : Measure E) (c : ι → Set E)

theorem cellMass_mono {S T : Set E} (h : S ⊆ T) : cellMass μ c S ≤ cellMass μ c T :=
  ENNReal.tsum_le_tsum fun _ =>
    ENNReal.div_le_div_right (measure_mono (inter_subset_inter_right _ h)) _

theorem cellMass_empty : cellMass μ c ∅ = 0 := by
  simp [cellMass]

/-- Each cell contributes at most `1`. -/
theorem measure_inter_div_le_one (i : ι) (S : Set E) : μ (c i ∩ S) / μ (c i) ≤ 1 :=
  ENNReal.div_le_of_le_mul (by rw [one_mul]; exact measure_mono inter_subset_left)

/-- The cell mass is at most the number of cells meeting the set. -/
theorem cellMass_le_card {S : Set E} {F : Finset ι} (hF : ∀ i, (c i ∩ S).Nonempty → i ∈ F) :
    cellMass μ c S ≤ F.card := by
  have h0 : ∀ i ∉ F, μ (c i ∩ S) / μ (c i) = 0 := fun i hi => by
    rw [not_nonempty_iff_eq_empty.mp fun h => hi (hF i h), measure_empty, ENNReal.zero_div]
  rw [cellMass, tsum_eq_sum h0]
  calc ∑ i ∈ F, μ (c i ∩ S) / μ (c i) ≤ ∑ _i ∈ F, (1 : ℝ≥0∞) :=
        Finset.sum_le_sum fun i _ => measure_inter_div_le_one μ c i S
    _ = F.card := by simp

/-- For a locally finite family of cells, the cell mass of a compact set is finite. -/
theorem cellMass_ne_top [TopologicalSpace E] (hc : LocallyFinite c) {S : Set E}
    (hS : IsCompact S) : cellMass μ c S ≠ ∞ := by
  have hfin := hc.finite_nonempty_inter_compact hS
  exact ne_top_of_le_ne_top (ENNReal.natCast_ne_top hfin.toFinset.card)
    (cellMass_le_card μ c fun i hi => hfin.mem_toFinset.mpr hi)

/-- Additivity of the cell mass over a measurable subset and its complement. -/
theorem cellMass_add_diff {S T : Set E} (hST : S ⊆ T) (hS : MeasurableSet S) :
    cellMass μ c S + cellMass μ c (T \ S) = cellMass μ c T := by
  rw [cellMass, cellMass, cellMass, ← ENNReal.tsum_add]
  refine tsum_congr fun i => ?_
  rw [← ENNReal.add_div, ← inter_sdiff_assoc, ← measure_inter_add_sdiff (c i ∩ T) hS,
    inter_assoc, inter_eq_right.mpr hST]

/-- A set of positive measure covered by countably many cells of finite measure has positive
cell mass. -/
theorem cellMass_pos [Countable ι] {A : Set E} (hcover : A ⊆ ⋃ i, c i)
    (hfin : ∀ i, μ (c i) ≠ ∞) (hA : μ A ≠ 0) : 0 < cellMass μ c A := by
  have hsum : μ A ≤ ∑' i, μ (c i ∩ A) :=
    calc μ A = μ (⋃ i, c i ∩ A) := by rw [← iUnion_inter, inter_eq_right.mpr hcover]
      _ ≤ ∑' i, μ (c i ∩ A) := measure_iUnion_le _
  obtain ⟨i, hi⟩ : ∃ i, μ (c i ∩ A) ≠ 0 := by
    by_contra h
    have h' : ∀ i, μ (c i ∩ A) = 0 := fun i => not_not.mp fun hi => h ⟨i, hi⟩
    exact hA (nonpos_iff_eq_zero.mp (hsum.trans (by simp [h'])))
  unfold cellMass
  exact (ENNReal.div_pos hi (hfin i)).trans_le
    (ENNReal.le_tsum (f := fun i => μ (c i ∩ A) / μ (c i)) i)

/-- Strict increase of the cell mass (Gwynne, Miller and Sheffield, arXiv 1807.07515, proof of
Lemma 2.2): if `S ⊆ T`, `S` is measurable with finite cell mass, and the increment `T \ S` has
positive measure and is covered by cells of finite measure, then the mass of `T` is larger. -/
theorem cellMass_lt_cellMass [Countable ι] {S T : Set E} (hST : S ⊆ T) (hS : MeasurableSet S)
    (hcover : T \ S ⊆ ⋃ i, c i) (hfin : ∀ i, μ (c i) ≠ ∞) (hpos : μ (T \ S) ≠ 0)
    (hSfin : cellMass μ c S ≠ ∞) : cellMass μ c S < cellMass μ c T := by
  rw [← cellMass_add_diff μ c hST hS]
  exact ENNReal.lt_add_right hSfin (cellMass_pos μ c hcover hfin hpos).ne'

/-- Along an increasing chain of measurable sets whose increments have positive measure, the
cell mass of a covering family of cells of finite measure is strictly increasing, provided it is
finite along the chain. -/
theorem strictMono_cellMass [Countable ι] {C : ℤ → Set E} (hmono : ∀ j, C j ⊆ C (j + 1))
    (hmeas : ∀ j, MeasurableSet (C j)) (hcover : ⋃ i, c i = univ) (hfin : ∀ i, μ (c i) ≠ ∞)
    (hpos : ∀ j, μ (C (j + 1) \ C j) ≠ 0) (hCfin : ∀ j, cellMass μ c (C j) ≠ ∞) :
    StrictMono fun j => cellMass μ c (C j) :=
  strictMono_int_of_lt_succ fun j =>
    cellMass_lt_cellMass μ c (hmono j) (hmeas j) (by rw [hcover]; exact subset_univ _) hfin
      (hpos j) (hCfin j)

/-- Invariance of the cell mass under an injective map that multiplies the measure by a constant
in `(0, ∞)`. -/
theorem cellMass_image {F : Type*} [MeasurableSpace F] (ν : Measure F) {f : E → F}
    (hf : Function.Injective f) {k : ℝ≥0∞} (hk0 : k ≠ 0) (hk : k ≠ ∞)
    (hfμ : ∀ A, ν (f '' A) = k * μ A) (S : Set E) :
    cellMass ν (fun i => f '' c i) (f '' S) = cellMass μ c S := by
  unfold cellMass
  refine tsum_congr fun i => ?_
  rw [← image_inter hf, hfμ, hfμ, ENNReal.mul_div_mul_left _ _ hk0 hk]

section Similarity

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [MeasurableSpace V] [BorelSpace V]
  [FiniteDimensional ℝ V]

/-- An additive Haar measure is multiplied by `|r ^ dim|` under the similarity `z ↦ r • z + b`. -/
theorem addHaar_image_smul_add (ν : Measure V) [ν.IsAddHaarMeasure] (r : ℝ) (b : V)
    (A : Set V) :
    ν ((fun z => r • z + b) '' A) = ENNReal.ofReal |r ^ Module.finrank ℝ V| * ν A := by
  have h : (fun z => r • z + b) '' A = (fun z => b + z) '' (r • A) := by
    rw [← image_smul, image_image]
    congr 1
    funext z
    exact add_comm _ _
  rw [h, image_add_left, measure_preimage_add, Measure.addHaar_smul]

/-- The cell mass is invariant under the similarities `z ↦ r • z + b`, `r ≠ 0`, applied to the
cells and to the set. -/
theorem cellMass_image_smul_add (ν : Measure V) [ν.IsAddHaarMeasure] (c : ι → Set V) {r : ℝ}
    (hr : r ≠ 0) (b : V) (S : Set V) :
    cellMass ν (fun i => (fun z => r • z + b) '' c i) ((fun z => r • z + b) '' S) =
      cellMass ν c S := by
  refine cellMass_image ν c ν (fun x y hxy => smul_right_injective V hr (add_right_cancel hxy))
    (ENNReal.ofReal_pos.mpr (abs_pos.mpr (pow_ne_zero _ hr))).ne' ENNReal.ofReal_ne_top
    (addHaar_image_smul_add ν r b) S

end Similarity

end LatticeProb.CellMass
