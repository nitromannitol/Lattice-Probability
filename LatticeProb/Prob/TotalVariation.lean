/-
Moved from nitromannitol/rotor-23, Apache-2.0; copyright 2026 Ahmed Bou-Rabee and
Yuval Peres.  Sources:

* `Rotor/Periodic.lean` (`tvDist`), where it is introduced, free-standing and
  with no dependence on the file's `Mechanism`/`Config`/`DoublyPeriodic`
  content, right after the doubly periodic geometry;
* `Rotor/Support/TVTools.lean` (everything: `abs_sub_le_tvDist` through
  `infinitePi_restrict_tv_le`), introduced there as "support for
  `lem:block-live-paths`, the perturbation `δ` of the one-vertex laws" of the
  rotor-routing termination paper, but stated throughout for a bare product
  of probability measures with no rotor-specific type anywhere.
-/
import Mathlib

/-!
# Total variation distance and product coupling

`tvDist μ ν` is the total variation distance between two laws on the same
measurable space, `sup_s |μ s - ν s|`.  The rest of the file bounds how much a
product measure's probability of an event can change when the one-coordinate
laws are perturbed:

* `pi_one_coord_le`: changing the law of a single coordinate of a finite
  product changes the probability of any measurable event by at most the
  total variation distance of that one coordinate;
* `pi_tv_le`: changing every coordinate changes it by at most the sum of the
  per-coordinate total variation distances (a telescoping sum of
  `pi_one_coord_le`);
* `infinitePi_restrict_tv_le`: the same bound for `Measure.infinitePi`
  (countably many coordinates), for an event determined by a finite set of
  coordinates.

This is the standard tool for comparing a perturbed product law to a
reference one, complementary to the correlation inequalities of
`LatticeProb.Prob.Harris`/`LatticeProb.Prob.HarrisVariants` (which compare two
events under one law, rather than one event under two laws).
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LatticeProb

section TV

variable {α : Type*} [MeasurableSpace α]

/-- Total variation distance between two laws on a measurable space: the
supremum, over every measurable set, of the difference of the two
probabilities. -/
noncomputable def tvDist (μ ν : Measure α) : ℝ :=
  ⨆ s : Set α, |(μ s).toReal - (ν s).toReal|

/-- Every set witnesses at most the total variation distance. -/
theorem abs_sub_le_tvDist (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (s : Set α) : |(μ s).toReal - (ν s).toReal| ≤ tvDist μ ν := by
  unfold tvDist
  refine le_ciSup (f := fun s => |(μ s).toReal - (ν s).toReal|) ⟨2, ?_⟩ s
  rintro _ ⟨t, rfl⟩
  have h1 : (μ t).toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := μ) (s := t))
    simpa using this
  have h2 : (ν t).toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one (μ := ν) (s := t))
    simpa using this
  have h3 : 0 ≤ (μ t).toReal := ENNReal.toReal_nonneg
  have h4 : 0 ≤ (ν t).toReal := ENNReal.toReal_nonneg
  show |(μ t).toReal - (ν t).toReal| ≤ 2
  rw [abs_le]
  constructor <;> linarith

/-- Total variation distance between probability measures is nonnegative. -/
theorem tvDist_nonneg (μ ν : Measure α) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    0 ≤ tvDist μ ν :=
  (abs_nonneg _).trans (abs_sub_le_tvDist μ ν ∅)

end TV

section OneCoord

variable {n : ℕ} {α : Fin (n + 1) → Type*} [∀ i, MeasurableSpace (α i)]

/-- Changing the law of one coordinate changes every probability by at most the total variation
distance of that coordinate. -/
theorem pi_one_coord_le (κ κ' : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (κ i)]
    [∀ i, IsProbabilityMeasure (κ' i)] (i : Fin (n + 1)) (h : ∀ j, j ≠ i → κ' j = κ j)
    {B : Set (∀ i, α i)} (hB : MeasurableSet B) :
    |(Measure.pi κ' B).toReal - (Measure.pi κ B).toReal| ≤ tvDist (κ' i) (κ i) := by
  set e := MeasurableEquiv.piFinSuccAbove α i with he
  have hrest : (fun j => κ' (i.succAbove j)) = fun j => κ (i.succAbove j) :=
    funext (fun j => h _ (Fin.succAbove_ne i j))
  set R := Measure.pi (fun j => κ (i.succAbove j)) with hR
  have hBe : MeasurableSet (e '' B) := e.measurableEmbedding.measurableSet_image.2 hB
  have hpre : e ⁻¹' (e '' B) = B := e.injective.preimage_image B
  have h1 : Measure.pi κ B = ((κ i).prod R) (e '' B) := by
    rw [← (measurePreserving_piFinSuccAbove κ i).measure_preimage hBe.nullMeasurableSet, hpre]
  have h2 : Measure.pi κ' B = ((κ' i).prod R) (e '' B) := by
    rw [hR, ← hrest, ← (measurePreserving_piFinSuccAbove κ' i).measure_preimage hBe.nullMeasurableSet,
      hpre]
  rw [h1, h2, Measure.prod_apply_symm hBe, Measure.prod_apply_symm hBe]
  -- the sections
  set f : (∀ j, α (i.succAbove j)) → ℝ≥0∞ := fun y => κ' i ((fun x => (x, y)) ⁻¹' (e '' B))
  set g : (∀ j, α (i.succAbove j)) → ℝ≥0∞ := fun y => κ i ((fun x => (x, y)) ⁻¹' (e '' B))
  have hf : Measurable f := measurable_measure_prodMk_right hBe
  have hg : Measurable g := measurable_measure_prodMk_right hBe
  have hf1 : ∀ y, f y ≠ ⊤ := fun y => measure_ne_top _ _
  have hg1 : ∀ y, g y ≠ ⊤ := fun y => measure_ne_top _ _
  rw [← integral_toReal hf.aemeasurable (ae_of_all _ (fun y => lt_top_iff_ne_top.2 (hf1 y))),
    ← integral_toReal hg.aemeasurable (ae_of_all _ (fun y => lt_top_iff_ne_top.2 (hg1 y)))]
  have hle1 : ∀ y, (f y).toReal ≤ 1 := fun y => by
    have h := prob_le_one (μ := κ' i) (s := (fun x => (x, y)) ⁻¹' (e '' B))
    exact (ENNReal.toReal_mono ENNReal.one_ne_top h).trans (by simp)
  have hle2 : ∀ y, (g y).toReal ≤ 1 := fun y => by
    have h := prob_le_one (μ := κ i) (s := (fun x => (x, y)) ⁻¹' (e '' B))
    exact (ENNReal.toReal_mono ENNReal.one_ne_top h).trans (by simp)
  have hfi : Integrable (fun y => (f y).toReal) R :=
    (integrable_const (1 : ℝ)).mono' hf.ennreal_toReal.aestronglyMeasurable
      (ae_of_all _ (fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
        exact hle1 y))
  have hgi : Integrable (fun y => (g y).toReal) R :=
    (integrable_const (1 : ℝ)).mono' hg.ennreal_toReal.aestronglyMeasurable
      (ae_of_all _ (fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
        exact hle2 y))
  rw [← integral_sub hfi hgi]
  calc abs (integral R (fun y => (f y).toReal - (g y).toReal))
      ≤ integral R (fun y => abs ((f y).toReal - (g y).toReal)) := abs_integral_le_integral_abs
    _ ≤ integral R (fun _ => tvDist (κ' i) (κ i)) := by
        refine integral_mono (hfi.sub hgi).abs (integrable_const _) (fun y => ?_)
        exact abs_sub_le_tvDist (κ' i) (κ i) _
    _ = tvDist (κ' i) (κ i) := by simp

end OneCoord

section Hybrid

variable {n : ℕ} {α : Fin (n + 1) → Type*} [∀ i, MeasurableSpace (α i)]

/-- The families obtained by switching the first `k` coordinates from `ν` to `ν'`. -/
def switched (ν ν' : ∀ i, Measure (α i)) (k : ℕ) : ∀ i, Measure (α i) :=
  fun i => if (i : ℕ) < k then ν' i else ν i

instance (ν ν' : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (ν i)]
    [∀ i, IsProbabilityMeasure (ν' i)] (k : ℕ) (i : Fin (n + 1)) :
    IsProbabilityMeasure (switched ν ν' k i) := by
  unfold switched
  split_ifs <;> infer_instance

/-- Changing every coordinate changes a probability by at most the sum of the total variation
distances. -/
theorem pi_tv_le (ν ν' : ∀ i, Measure (α i)) [∀ i, IsProbabilityMeasure (ν i)]
    [∀ i, IsProbabilityMeasure (ν' i)] {B : Set (∀ i, α i)} (hB : MeasurableSet B) :
    |(Measure.pi ν' B).toReal - (Measure.pi ν B).toReal| ≤ ∑ i, tvDist (ν' i) (ν i) := by
  have h0 : switched ν ν' 0 = ν := funext fun i => by simp [switched]
  have hn : switched ν ν' (n + 1) = ν' := funext fun i => by simp [switched, i.isLt]
  have step : ∀ k : ℕ, (hk : k ≤ n) →
      |(Measure.pi (switched ν ν' (k + 1)) B).toReal - (Measure.pi (switched ν ν' k) B).toReal| ≤
        tvDist (ν' ⟨k, by omega⟩) (ν ⟨k, by omega⟩) := by
    intro k hk
    have := pi_one_coord_le (switched ν ν' k) (switched ν ν' (k + 1)) ⟨k, by omega⟩
      (fun j hj => ?_) hB
    · simpa [switched] using this
    · simp only [switched]
      have hne : (j : ℕ) ≠ k := fun h => hj (Fin.ext h)
      by_cases hjk : (j : ℕ) < k
      · simp [hjk, Nat.lt_succ_of_lt hjk]
      · have : ¬ (j : ℕ) < k + 1 := by omega
        simp [hjk, this]
  have tele : ∀ k : ℕ, k ≤ n + 1 →
      |(Measure.pi (switched ν ν' k) B).toReal - (Measure.pi ν B).toReal| ≤
        ∑ i ∈ Finset.univ.filter (fun i : Fin (n + 1) => (i : ℕ) < k), tvDist (ν' i) (ν i) := by
    intro k
    induction k with
    | zero => intro _; simp [h0]
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 := step k (by omega)
      have hset : Finset.univ.filter (fun i : Fin (n + 1) => (i : ℕ) < k + 1) =
          insert ⟨k, by omega⟩ (Finset.univ.filter (fun i : Fin (n + 1) => (i : ℕ) < k)) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
        omega
      rw [hset, Finset.sum_insert (by simp)]
      calc |(Measure.pi (switched ν ν' (k + 1)) B).toReal - (Measure.pi ν B).toReal|
          ≤ |(Measure.pi (switched ν ν' (k + 1)) B).toReal -
              (Measure.pi (switched ν ν' k) B).toReal| +
            |(Measure.pi (switched ν ν' k) B).toReal - (Measure.pi ν B).toReal| :=
            abs_sub_le _ _ _
        _ ≤ _ := add_le_add h2 h1
  have := tele (n + 1) le_rfl
  rw [hn, Finset.filter_true_of_mem (fun i _ => i.isLt)] at this
  exact this

end Hybrid

section Transfer

variable {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-- Changing the one-coordinate laws of a product law changes the probability of an event
determined by the coordinates in a finite set `S` by at most the sum over `S` of the total
variation distances. -/
theorem infinitePi_restrict_tv_le (ν ν' : ∀ i, Measure (X i)) [∀ i, IsProbabilityMeasure (ν i)]
    [∀ i, IsProbabilityMeasure (ν' i)] (S : Finset ι) {B : Set (∀ i : S, X i)}
    (hB : MeasurableSet B) :
    |(Measure.infinitePi ν' (S.restrict ⁻¹' B)).toReal -
      (Measure.infinitePi ν (S.restrict ⁻¹' B)).toReal| ≤ ∑ i ∈ S, tvDist (ν' i) (ν i) := by
  rw [← Measure.map_apply (Finset.measurable_restrict S) hB,
    ← Measure.map_apply (Finset.measurable_restrict S) hB,
    Measure.infinitePi_map_restrict, Measure.infinitePi_map_restrict]
  rcases Nat.eq_zero_or_pos S.card with hS | hS
  · -- no coordinates: the index type is empty and both measures agree
    obtain rfl := Finset.card_eq_zero.1 hS
    rw [Measure.pi_of_empty, Measure.pi_of_empty]
    simp
  · obtain ⟨m, hm⟩ : ∃ m, S.card = m + 1 := ⟨S.card - 1, by omega⟩
    let f : Fin (m + 1) ≃ S := (Fin.castOrderIso hm.symm).toEquiv.trans S.equivFin.symm
    have h := measurePreserving_piCongrLeft (fun i : S => ν i) f
    have h' := measurePreserving_piCongrLeft (fun i : S => ν' i) f
    set e := MeasurableEquiv.piCongrLeft (fun i : S => X i) f
    have hpre : ∀ (μ : ∀ i : S, Measure (X i)) [∀ i, IsProbabilityMeasure (μ i)],
        Measure.pi μ B = Measure.pi (fun i' => μ (f i')) (e ⁻¹' B) := fun μ _ =>
      ((measurePreserving_piCongrLeft μ f).measure_preimage hB.nullMeasurableSet).symm
    rw [hpre (fun i : S => ν i), hpre (fun i : S => ν' i)]
    have := pi_tv_le (fun i' => ν (f i')) (fun i' => ν' (f i')) (e.measurable hB)
    refine this.trans (le_of_eq ?_)
    rw [← Finset.sum_coe_sort S]
    exact Equiv.sum_comp f (fun i : S => tvDist (ν' i) (ν i))

end Transfer

end LatticeProb
