/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cP.Excursions at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.DegMeasurable

/-!
# Rationally labelled excursions of a curve into an open set

Source: [18] Lemma 2.4 and the proof of [18] Lemma 4.3. For a curve `c` and a set `U`, the excursion of `c` into `U` labelled by a rational
point `q` is the open time interval `(e q, x q)` on which `c ∈ U`, with `c(e q), c(x q) ∉ U`; the stored
excursion segment is `u ↦ c(e q + clamp(u, 0, x q − e q))` (the frozen `MatedCRT.excursionSegment`).

* `IsExcursionFamily c U L e x`: the labels `L` give genuine maximal excursions which cover every time spent
  in `U`. (For the bundle curves this is the `ExcursionCoverage` and `isExcursion_entry_exit`.)
* `IsExcursionFamily.subset_Ioo`: an interval spent in `U` which meets an excursion lies inside it.
* `IsExcursionFamily.eq_of_mem`: two excursions through the same time coincide.
* `IsExcursionFamily.entry_eq_of_clampSeg_eq`: if `c` is parametrized by the mass of a measure, distinct
  excursions have distinct stored segments. This is what makes a local count of disjoint cells possible
  without knowing the global time order of the excursions.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4cP

/-- The excursion segment `c(e + ·)` clamped to the time interval `[0, x − e]` (as in the frozen
`MatedCRT.excursionSegment`, `[18]`). -/
def clampSeg (c : ℝ → ℂ) (e x : ℝ) : ℝ → ℂ := fun u => c (e + max 0 (min u (x - e)))

section clamp

variable {c : ℝ → ℂ} {e x u : ℝ}

theorem clampSeg_of_mem (hu : u ∈ Icc 0 (x - e)) : clampSeg c e x u = c (e + u) := by
  unfold clampSeg
  rw [min_eq_left hu.2, max_eq_right hu.1]

theorem clampSeg_of_nonpos (hu : u ≤ 0) : clampSeg c e x u = c e := by
  unfold clampSeg
  have h1 : min u (x - e) ≤ 0 := (min_le_left _ _).trans hu
  rw [max_eq_left h1, add_zero]

theorem clampSeg_of_ge (hex : e ≤ x) (hu : x - e ≤ u) : clampSeg c e x u = c x := by
  unfold clampSeg
  rw [min_eq_right hu, max_eq_right (sub_nonneg.mpr hex)]
  ring_nf

theorem continuous_clampSeg (hc : Continuous c) : Continuous (clampSeg c e x) := by
  unfold clampSeg
  fun_prop

/-- On a sub-interval of the clamping range the segment is a time shift of the curve. -/
theorem clampSeg_image_Icc {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ x - e) :
    clampSeg c e x '' Icc a b = c '' Icc (e + a) (e + b) := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨e + u, ⟨by linarith [hu.1], by linarith [hu.2]⟩, ?_⟩
    rw [clampSeg_of_mem ⟨by linarith [hu.1], by linarith [hu.2]⟩]
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t - e, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    rw [clampSeg_of_mem ⟨by linarith [ht.1], by linarith [ht.2]⟩]
    congr 1
    ring

/-- Past its length the segment adds no new points. -/
theorem clampSeg_image_Icc_zero_of_ge (hex : e ≤ x) {M : ℝ} (hM : x - e ≤ M) :
    clampSeg c e x '' Icc 0 M = c '' Icc e x := by
  ext z
  constructor
  · rintro ⟨u, hu, rfl⟩
    by_cases hux : u ≤ x - e
    · rw [clampSeg_of_mem ⟨hu.1, hux⟩]
      exact ⟨e + u, ⟨by linarith [hu.1], by linarith⟩, rfl⟩
    · rw [clampSeg_of_ge hex (le_of_not_ge hux)]
      exact ⟨x, ⟨hex, le_rfl⟩, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t - e, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    rw [clampSeg_of_mem ⟨by linarith [ht.1], by linarith [ht.2]⟩]
    congr 1
    ring

end clamp

/-- **Excursion data.** For each label `q ∈ L`, `(e q, x q)` is an excursion of `c` into `U`: a nonempty
open time interval spent in `U` whose endpoints are mapped outside `U`; every time spent in `U` lies in one
of them. -/
structure IsExcursionFamily (c : ℝ → ℂ) (U : Set ℂ) (L : Set (ℚ × ℚ))
    (e x : ℚ × ℚ → ℝ) : Prop where
  lt : ∀ q ∈ L, e q < x q
  entry_not_mem : ∀ q ∈ L, c (e q) ∉ U
  exit_not_mem : ∀ q ∈ L, c (x q) ∉ U
  mem : ∀ q ∈ L, ∀ t ∈ Ioo (e q) (x q), c t ∈ U
  cover : ∀ t, c t ∈ U → ∃ q ∈ L, t ∈ Ioo (e q) (x q)

namespace IsExcursionFamily

variable {c : ℝ → ℂ} {U : Set ℂ} {L : Set (ℚ × ℚ)} {e x : ℚ × ℚ → ℝ}

/-- **Maximality.** A time interval spent in `U` which meets an excursion lies inside it. -/
theorem subset_Ioo (hD : IsExcursionFamily c U L e x) {q : ℚ × ℚ} (hq : q ∈ L)
    {a b t : ℝ} (hab : ∀ s ∈ Icc a b, c s ∈ U) (ht : t ∈ Icc a b)
    (hte : t ∈ Ioo (e q) (x q)) : Icc a b ⊆ Ioo (e q) (x q) := by
  have hxb : b < x q := by
    by_contra h
    push Not at h
    exact hD.exit_not_mem q hq (hab _ ⟨by linarith [ht.1, hte.2], h⟩)
  have hae : e q < a := by
    by_contra h
    push Not at h
    exact hD.entry_not_mem q hq (hab _ ⟨h, by linarith [ht.2, hte.1]⟩)
  intro s hs
  exact ⟨by linarith [hs.1], by linarith [hs.2]⟩

/-- Two excursions through a common time coincide. -/
theorem eq_of_mem (hD : IsExcursionFamily c U L e x) {q q' : ℚ × ℚ} (hq : q ∈ L) (hq' : q' ∈ L)
    {t : ℝ} (ht : t ∈ Ioo (e q) (x q)) (ht' : t ∈ Ioo (e q') (x q')) :
    e q = e q' ∧ x q = x q' := by
  constructor
  · rcases lt_trichotomy (e q) (e q') with h | h | h
    · exact absurd (hD.mem q hq _ ⟨h, by linarith [ht'.1, ht.2]⟩) (hD.entry_not_mem q' hq')
    · exact h
    · exact absurd (hD.mem q' hq' _ ⟨h, by linarith [ht.1, ht'.2]⟩) (hD.entry_not_mem q hq)
  · rcases lt_trichotomy (x q) (x q') with h | h | h
    · exact absurd (hD.mem q' hq' _ ⟨by linarith [ht'.1, ht.2], h⟩) (hD.exit_not_mem q hq)
    · exact h
    · exact absurd (hD.mem q hq _ ⟨by linarith [ht.1, ht'.2], h⟩) (hD.exit_not_mem q' hq')

/-- Excursions with the same entrance time coincide. -/
theorem exit_eq_of_entry_eq (hD : IsExcursionFamily c U L e x) {q q' : ℚ × ℚ} (hq : q ∈ L)
    (hq' : q' ∈ L) (he : e q = e q') : x q = x q' := by
  have h1 := hD.lt q hq
  have h2 := hD.lt q' hq'
  set t := e q + min (x q - e q) (x q' - e q') / 2 with ht
  have hm : 0 < min (x q - e q) (x q' - e q') := lt_min (by linarith) (by linarith)
  have hm1 := min_le_left (x q - e q) (x q' - e q')
  have hm2 := min_le_right (x q - e q) (x q' - e q')
  exact (hD.eq_of_mem hq hq' (t := t) ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩).2

/-- Distinct excursions are disjoint. -/
theorem disjoint_of_entry_ne (hD : IsExcursionFamily c U L e x) {q q' : ℚ × ℚ} (hq : q ∈ L)
    (hq' : q' ∈ L) (he : e q ≠ e q') : Disjoint (Ioo (e q) (x q)) (Ioo (e q') (x q')) := by
  rw [Set.disjoint_left]
  intro t ht ht'
  exact he (hD.eq_of_mem hq hq' ht ht').1

/-- **Distinct excursions have distinct stored segments** when `c` is parametrized by the mass of a
measure (the area parametrization of space-filling SLE). -/
theorem entry_eq_of_clampSeg_eq (hD : IsExcursionFamily c U L e x) {μ : Measure ℂ}
    (hμ : ∀ s t : ℝ, s ≤ t → μ (c '' Icc s t) = ENNReal.ofReal (t - s))
    {q q' : ℚ × ℚ} (hq : q ∈ L) (hq' : q' ∈ L)
    (hseg : clampSeg c (e q) (x q) = clampSeg c (e q') (x q')) : e q = e q' := by
  by_contra hne
  -- the symmetric core: an earlier excursion cannot carry the same segment as a later one
  have key : ∀ {p p' : ℚ × ℚ}, p ∈ L → p' ∈ L →
      clampSeg c (e p) (x p) = clampSeg c (e p') (x p') → e p < e p' → False := by
    intro p p' hp hp' hs hlt
    have hpl := hD.lt p hp
    have hpl' := hD.lt p' hp'
    have hdisj := hD.disjoint_of_entry_ne hp hp' hlt.ne
    have hxe : x p ≤ e p' := by
      by_contra h
      push Not at h
      have hm : e p' < min (x p) (x p') := lt_min h hpl'
      rw [Set.disjoint_left] at hdisj
      exact hdisj (a := (e p' + min (x p) (x p')) / 2)
        ⟨by linarith [hlt], by linarith [min_le_left (x p) (x p')]⟩
        ⟨by linarith, by linarith [min_le_right (x p) (x p')]⟩
    set M := max (x p - e p) (x p' - e p')
    have himg : c '' Icc (e p) (x p) = c '' Icc (e p') (x p') := by
      rw [← clampSeg_image_Icc_zero_of_ge hpl.le (le_max_left _ _),
        ← clampSeg_image_Icc_zero_of_ge hpl'.le (le_max_right _ _), hs]
    have hlen : x p - e p = x p' - e p' := by
      have h1 := hμ _ _ hpl.le
      have h2 := hμ _ _ hpl'.le
      rw [himg, h2] at h1
      exact (ENNReal.ofReal_eq_ofReal_iff (by linarith) (by linarith)).1 h1.symm
    have hsub : c '' Icc (e p) (x p') ⊆ c '' Icc (e p) (x p) ∪ c '' Icc (x p) (e p') := by
      rintro _ ⟨t, ht, rfl⟩
      by_cases h1 : t ≤ x p
      · exact Or.inl ⟨t, ⟨ht.1, h1⟩, rfl⟩
      · by_cases h2 : t ≤ e p'
        · exact Or.inr ⟨t, ⟨(le_of_not_ge h1), h2⟩, rfl⟩
        · refine Or.inl ?_
          have : c t ∈ c '' Icc (e p') (x p') := ⟨t, ⟨le_of_not_ge h2, ht.2⟩, rfl⟩
          rwa [← himg] at this
    have hle := measure_mono (μ := μ) hsub
    have hun := measure_union_le (μ := μ) (c '' Icc (e p) (x p)) (c '' Icc (x p) (e p'))
    rw [hμ _ _ (by linarith)] at hle
    rw [hμ _ _ hpl.le, hμ _ _ hxe] at hun
    have htot := hle.trans hun
    rw [← ENNReal.ofReal_add (by linarith) (by linarith),
      ENNReal.ofReal_le_ofReal_iff (by linarith)] at htot
    linarith
  rcases lt_or_gt_of_ne hne with h | h
  · exact key hq hq' hseg h
  · exact key hq' hq hseg.symm h

end IsExcursionFamily

end MatedCRTHarmonic.GMS4cP
