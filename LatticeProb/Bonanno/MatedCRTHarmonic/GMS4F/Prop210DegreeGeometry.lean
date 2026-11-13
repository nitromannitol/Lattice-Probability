/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4F.Prop210DegreeGeometry at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.DegOutMeasurable
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.Lemma46
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4F.Prop210Degree

/-!
# Geometric cell counting for [18] (4.7)

A finite set of distinct mesh cells contained in the localized ball and
meeting the root window is an inner-degree family. Every remaining cell
contains a far time; ordered far times and window contacts yield an
outer-degree crossing family.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Metric

namespace MatedCRTHarmonic.GMS4F

/-- Distinct mesh cells have disjoint open time intervals. -/
theorem disjoint_mesh_cell_interior {ε : ℝ} (hε : 0 < ε)
    {x y : ℤ} (hxy : x ≠ y) :
    Disjoint (Ioo (ε * ((x : ℝ) - 1)) (ε * (x : ℝ)))
      (Ioo (ε * ((y : ℝ) - 1)) (ε * (y : ℝ))) := by
  apply Set.disjoint_left.mpr
  intro t htx hty
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · have hstep : x + 1 ≤ y := by omega
    have hcast₀ : (x : ℝ) + 1 ≤ (y : ℝ) := by exact_mod_cast hstep
    have hcast : (x : ℝ) ≤ (y : ℝ) - 1 := by linarith
    have hmul := mul_le_mul_of_nonneg_left hcast hε.le
    linarith [htx.2, hty.1]
  · have hstep : y + 1 ≤ x := by omega
    have hcast₀ : (y : ℝ) + 1 ≤ (x : ℝ) := by exact_mod_cast hstep
    have hcast : (y : ℝ) ≤ (x : ℝ) - 1 := by linarith
    have hmul := mul_le_mul_of_nonneg_left hcast hε.le
    linarith [hty.2, htx.1]

/-- Every distinct ε-cell contained in the local ball and meeting the local
window contributes one member of an inner-degree family. -/
theorem contained_window_cells_le_locDegIn
    {ε : ℝ} (hε : 0 < ε) (c : ℝ → ℂ) (t₀ : ℝ)
    (S : Finset ℤ)
    (hS : ∀ x ∈ S,
      GMS4b.cellOf ε c x ⊆ GMS4b.locBall ε c t₀ ∧
        (GMS4b.cellOf ε c x ∩ GMS4b.locWindow ε c t₀).Nonempty) :
    (S.card : ℕ∞) ≤ GMS4b.locDegIn ε c t₀ := by
  let e := S.orderIsoOfFin rfl
  let a : Fin S.card → ℝ := fun i => ε * (((e i : ℤ) : ℝ) - 1)
  have ha : GMS4b.IsDegInFamily ε c t₀ a := by
    refine ⟨?_, ?_⟩
    · intro i j hij
      have hindex : (e i : ℤ) ≠ e j := by
        intro h
        exact hij (e.injective (Subtype.ext h))
      convert disjoint_mesh_cell_interior hε hindex using 1 <;>
        simp only [a] <;> ring_nf
    · intro i
      have hi := hS (e i : ℤ) (e i).property
      convert hi using 1 <;> simp only [a, GMS4b.cellOf] <;> ring_nf
  exact GMS4b.le_locDegIn ha

/-- Times in distinct mesh cells occur in their index order. -/
theorem mesh_cell_time_le_of_lt {ε : ℝ} (hε : 0 < ε)
    {x y : ℤ} (hxy : x < y)
    {s t : ℝ}
    (hs : s ∈ Icc (ε * ((x : ℝ) - 1)) (ε * (x : ℝ)))
    (ht : t ∈ Icc (ε * ((y : ℝ) - 1)) (ε * (y : ℝ))) : s ≤ t := by
  have hstep : x + 1 ≤ y := by omega
  have hcast₀ : (x : ℝ) + 1 ≤ (y : ℝ) := by exact_mod_cast hstep
  have hcast : (x : ℝ) ≤ (y : ℝ) - 1 := by linarith
  have hmul := mul_le_mul_of_nonneg_left hcast hε.le
  exact hs.2.trans (hmul.trans ht.1)

/-- Two window contacts with far times in disjoint, ordered mesh cells obey
The pairwise crossing relation used to build an outer-degree family. -/
theorem ordered_far_contacts_crossPairOK
    {ε : ℝ} {c : ℝ → ℂ} {t₀ ti si tj sj : ℝ}
    (hfar_i : GMS4b.IsFarTime ε c t₀ si)
    (hfar_j : GMS4b.IsFarTime ε c t₀ sj)
    (horder :
      (ti ≤ tj ∧ ti ≤ sj ∧ si ≤ tj ∧ si ≤ sj) ∨
      (tj ≤ ti ∧ tj ≤ si ∧ sj ≤ ti ∧ sj ≤ si)) :
    GMS4b.CrossPairOK ε c t₀ (decide (si ≤ ti)) (decide (sj ≤ tj)) ti tj := by
  have hbetween_i (hlo : ti ≤ si) (hhi : si ≤ tj) :
      GMS4b.FarBetween ε c t₀ ti tj := by
    exact ⟨si, (min_le_left _ _).trans hlo,
      hhi.trans (le_max_right _ _), hfar_i⟩
  have hbetween_j (hlo : ti ≤ sj) (hhi : sj ≤ tj) :
      GMS4b.FarBetween ε c t₀ ti tj := by
    exact ⟨sj, (min_le_left _ _).trans hlo,
      hhi.trans (le_max_right _ _), hfar_j⟩
  have hbetween_i_rev (hlo : tj ≤ si) (hhi : si ≤ ti) :
      GMS4b.FarBetween ε c t₀ ti tj := by
    exact ⟨si, (min_le_right _ _).trans hlo,
      hhi.trans (le_max_left _ _), hfar_i⟩
  have hbetween_j_rev (hlo : tj ≤ sj) (hhi : sj ≤ ti) :
      GMS4b.FarBetween ε c t₀ ti tj := by
    exact ⟨sj, (min_le_right _ _).trans hlo,
      hhi.trans (le_max_left _ _), hfar_j⟩
  rcases horder with hord | hord
  · by_cases hi : si ≤ ti
    · by_cases hj : sj ≤ tj
      · have hb := hbetween_j hord.2.1 hj
        simp [GMS4b.CrossPairOK, hi, hj, hb]
      · simp [GMS4b.CrossPairOK, hi, hj, hord.1]
    · have hb := hbetween_i (le_of_not_ge hi) hord.2.2.1
      by_cases hj : sj ≤ tj <;> simp [GMS4b.CrossPairOK, hi, hj, hb]
  · by_cases hj : sj ≤ tj
    · by_cases hi : si ≤ ti
      · have hb := hbetween_i_rev hord.2.1 hi
        simp [GMS4b.CrossPairOK, hi, hj, hb]
      · simp [GMS4b.CrossPairOK, hi, hj, hord.1]
    · by_cases hi : si ≤ ti
      · have hb := hbetween_j_rev (le_of_not_ge hj) hord.2.2.1
        simp [GMS4b.CrossPairOK, hi, hj, hb]
      · have hb := hbetween_j_rev (le_of_not_ge hj) hord.2.2.1
        simp [GMS4b.CrossPairOK, hi, hj, hb]

/-- Distinct ε-cells with a window contact and a far point each form an
outer-degree crossing family. -/
theorem far_window_cells_le_locDegOut
    {ε : ℝ} (hε : 0 < ε) (c : ℝ → ℂ) (hc : Continuous c) (t₀ : ℝ)
    (hD : 0 < diam (GMS4b.locWindow ε c t₀)) (S : Finset ℤ)
    (hS : ∀ x ∈ S, ∃ t s : ℝ,
      t ∈ Icc (ε * ((x : ℝ) - 1)) (ε * (x : ℝ)) ∧
      s ∈ Icc (ε * ((x : ℝ) - 1)) (ε * (x : ℝ)) ∧
      c t ∈ GMS4b.locWindow ε c t₀ ∧
      GMS4b.IsFarTime ε c t₀ s) :
    (S.card : ℕ∞) ≤ GMS4b.locDegOut ε c t₀ := by
  let e := S.orderIsoOfFin rfl
  have h : ∀ i : Fin S.card, ∃ t s : ℝ,
      t ∈ Icc (ε * (((e i : ℤ) : ℝ) - 1)) (ε * ((e i : ℤ) : ℝ)) ∧
      s ∈ Icc (ε * (((e i : ℤ) : ℝ) - 1)) (ε * ((e i : ℤ) : ℝ)) ∧
      c t ∈ GMS4b.locWindow ε c t₀ ∧ GMS4b.IsFarTime ε c t₀ s :=
    fun i => hS (e i : ℤ) (e i).property
  choose t s ht hs hw hf using h
  let τ : Fin S.card → Bool := fun i => decide (s i ≤ t i)
  have hcross : GMS4b.CrossingData ε c t₀ τ t := by
    refine ⟨hw, ?_, ?_⟩
    · intro i
      constructor
      · intro hi
        have hle : s i ≤ t i := by simpa only [τ, decide_eq_true_eq] using hi
        exact ⟨s i, hle, hf i⟩
      · intro hi
        have hnot : ¬ s i ≤ t i := by simpa only [τ, decide_eq_false_iff_not] using hi
        exact ⟨s i, le_of_not_ge hnot, hf i⟩
    · intro i j hij
      have hne : (e i : ℤ) ≠ e j := fun he => hij (e.injective (Subtype.ext he))
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have horder : t i ≤ t j ∧ t i ≤ s j ∧ s i ≤ t j ∧ s i ≤ s j := by
          exact ⟨mesh_cell_time_le_of_lt hε hlt (ht i) (ht j),
            mesh_cell_time_le_of_lt hε hlt (ht i) (hs j),
            mesh_cell_time_le_of_lt hε hlt (hs i) (ht j),
            mesh_cell_time_le_of_lt hε hlt (hs i) (hs j)⟩
        exact ordered_far_contacts_crossPairOK (hf i) (hf j) (Or.inl horder)
      · have horder : t j ≤ t i ∧ t j ≤ s i ∧ s j ≤ t i ∧ s j ≤ s i := by
          exact ⟨mesh_cell_time_le_of_lt hε hgt (ht j) (ht i),
            mesh_cell_time_le_of_lt hε hgt (ht j) (hs i),
            mesh_cell_time_le_of_lt hε hgt (hs j) (ht i),
            mesh_cell_time_le_of_lt hε hgt (hs j) (hs i)⟩
        exact ordered_far_contacts_crossPairOK (hf i) (hf j) (Or.inr horder)
  obtain ⟨a, b, hab⟩ := GMS4b.exists_family_of_crossingData hc hε.le hD hcross
  exact GMS4b.le_locDegOut hab

/-- A mesh cell outside the local ball has a far time within its own
parameter interval. -/
theorem far_time_of_cell_not_subset_ball
    {ε : ℝ} {c : ℝ → ℂ} {t₀ : ℝ} {x : ℤ}
    (hnot : ¬ GMS4b.cellOf ε c x ⊆ GMS4b.locBall ε c t₀) :
    ∃ s ∈ Icc (ε * ((x : ℝ) - 1)) (ε * (x : ℝ)),
      GMS4b.IsFarTime ε c t₀ s := by
  obtain ⟨w, hw, hout⟩ := Set.not_subset.mp hnot
  obtain ⟨s, hs, hsw⟩ := hw
  refine ⟨s, hs, ?_⟩
  have hgt : 4 * diam (GMS4b.locWindow ε c t₀) < dist (c s) (c t₀) := by
    have : c s ∉ GMS4b.locBall ε c t₀ := hsw ▸ hout
    simpa [GMS4b.locBall, Metric.mem_closedBall] using this
  exact hgt.le

/-- The geometric core of (4.7): a finite collection of distinct mesh cells
meeting the root window is bounded by the sum of the inner and outer localized
degrees. -/
theorem window_contact_cells_le_local_degrees
    {ε : ℝ} (hε : 0 < ε) (c : ℝ → ℂ) (hc : Continuous c) (t₀ : ℝ)
    (hD : 0 < diam (GMS4b.locWindow ε c t₀)) (S : Finset ℤ)
    (hS : ∀ x ∈ S,
      (GMS4b.cellOf ε c x ∩ GMS4b.locWindow ε c t₀).Nonempty) :
    (S.card : ℕ∞) ≤ GMS4b.locDegIn ε c t₀ + GMS4b.locDegOut ε c t₀ := by
  classical
  let Sin : Finset ℤ := S.filter fun x => GMS4b.cellOf ε c x ⊆ GMS4b.locBall ε c t₀
  let Sout : Finset ℤ := S.filter fun x => ¬ GMS4b.cellOf ε c x ⊆ GMS4b.locBall ε c t₀
  have hcard : S.card = Sin.card + Sout.card := by
    simp only [Sin, Sout, Finset.card_filter_add_card_filter_not]
  have hin : (Sin.card : ℕ∞) ≤ GMS4b.locDegIn ε c t₀ := by
    apply contained_window_cells_le_locDegIn hε c t₀ Sin
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact ⟨hx'.2, hS x hx'.1⟩
  have hout : (Sout.card : ℕ∞) ≤ GMS4b.locDegOut ε c t₀ := by
    apply far_window_cells_le_locDegOut hε c hc t₀ hD Sout
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    obtain ⟨w, ⟨t, ht, htw⟩, hw⟩ := hS x hx'.1
    obtain ⟨s, hs, hf⟩ := far_time_of_cell_not_subset_ball hx'.2
    exact ⟨t, s, ht, hs, htw ▸ hw, hf⟩
  simpa only [hcard, Nat.cast_add] using add_le_add hin hout

/-- The ε-cell selected by the root time lies in its two-sided window. -/
theorem root_cell_subset_window
    {ε : ℝ} (hε : 0 < ε) (c : ℝ → ℂ) (t₀ : ℝ) :
    GMS4b.cellOf ε c ⌈t₀ / ε⌉ ⊆ GMS4b.locWindow ε c t₀ := by
  intro w hw
  obtain ⟨t, ht, rfl⟩ := hw
  have ht₀ := GMS4b.mem_Icc_ceil hε t₀
  apply Set.mem_image_of_mem
  change t₀ - ε ≤ t ∧ t ≤ t₀ + ε
  constructor <;> linarith [ht.1, ht.2, ht₀.1, ht₀.2]

/-- Nonempty interior of a continuous curve window gives the positive radius
needed for the outer-degree crossing construction. -/
theorem diam_locWindow_pos_of_interior_nonempty
    {ε : ℝ} {c : ℝ → ℂ} {t₀ : ℝ} (hc : Continuous c)
    (hInt : (interior (GMS4b.locWindow ε c t₀)).Nonempty) :
    0 < diam (GMS4b.locWindow ε c t₀) := by
  obtain ⟨w, hw⟩ := hInt
  have hb : Bornology.IsBounded (GMS4b.locWindow ε c t₀) := by
    exact (isCompact_Icc.image hc).isBounded
  rcases Set.eq_singleton_or_nontrivial (interior_subset hw) with heq | hnon
  · rw [heq, interior_singleton] at hw
    exact hw.elim
  · exact Metric.diam_pos hnon hb

end MatedCRTHarmonic.GMS4F

