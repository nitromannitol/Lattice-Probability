/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cP.LocalEvents at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cP.Excursions

/-!
# Lemma 4.3 for the inner degree: the events read from the excursion segments

Source: [18] Lemma 4.3 and the definitions of
`B̄^ε_z` (4.6) and `deg^ε_in`.

A degree ball `B̄^ε(c, t) ⊆ U` and an inner-degree family at `t` only involve times spent in `U`, but its
cells may lie in **several** excursions of `c` into `U`, whose global time order is not visible inside `U`.
The local family below therefore picks a label and a local time for each cell, asks the usual
inner-degree conditions in local coordinates, and replaces global disjointness by: cells with the same
label are disjoint, and cells with different labels have different stored segments. Distinct stored
segments mean distinct, hence disjoint, excursions (`IsExcursionFamily.entry_eq_of_clampSeg_eq`), so this is
exactly global disjointness.

Main results, for a continuous curve with excursion data `(e, x)` whose segments are `σ`:
* `escBad_iff_mem_locEsc`: escape of a degree ball from `U` at a time spent in `S ⊆ U` is read from `σ`;
* `innerAt_and_not_escBad_iff`: the all-visit inner-degree threshold `∃ t, c t ∈ S, N ≤ deg^ε_in(c, t)`
  on the non-escape event is read from `σ`, if `c` is parametrized by the mass of a measure.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4cP

open MatedCRTHarmonic.GMS4b

/-- Rationally labelled continuous segments. -/
abbrev SegSpace : Type := ℚ × ℚ → C(ℝ, ℂ)

/-- Escape of the degree ball (4.6) from `U` at some time spent in `S`. -/
def EscBad (c : ℝ → ℂ) (S U : Set ℂ) (ε : ℝ) : Prop :=
  ∃ t : ℝ, c t ∈ S ∧ ¬ locBall ε c t ⊆ U

/-- The all-visit inner-degree threshold: some time spent in `S` has `deg^ε_in ≥ N`. -/
def InnerAt (c : ℝ → ℂ) (S : Set ℂ) (ε : ℝ) (N : ℕ) : Prop :=
  ∃ t : ℝ, c t ∈ S ∧ (N : ℕ∞) ≤ locDegIn ε c t

/-- The escape event read from labelled segments. -/
def locEsc (L : Set (ℚ × ℚ)) (S U : Set ℂ) (ε : ℝ) : Set SegSpace :=
  {σ | ∃ q ∈ L, ∃ s : ℝ, σ q s ∈ S ∧ ¬ locBall ε (σ q) s ⊆ U}

/-- An inner-degree family at local time `s` of segment `q`, in local coordinates: cell `i` is
`σ (lab i) ([b i, b i + ε])`. -/
def IsLocFamily (L : Set (ℚ × ℚ)) (ε : ℝ) (σ : SegSpace) (q : ℚ × ℚ) (s : ℝ) {N : ℕ}
    (lab : Fin N → ℚ × ℚ) (b : Fin N → ℝ) : Prop :=
  (∀ i, lab i ∈ L) ∧
  (∀ i j, i ≠ j → lab i = lab j → Disjoint (Ioo (b i) (b i + ε)) (Ioo (b j) (b j + ε))) ∧
  (∀ i j, lab i ≠ lab j → σ (lab i) ≠ σ (lab j)) ∧
  ∀ i, (σ (lab i)) '' Icc (b i) (b i + ε) ⊆ locBall ε (σ q) s ∧
    ((σ (lab i)) '' Icc (b i) (b i + ε) ∩ locWindow ε (σ q) s).Nonempty

/-- The inner-degree threshold on the non-escape event, read from labelled segments. -/
def locInner (L : Set (ℚ × ℚ)) (S U : Set ℂ) (ε : ℝ) (N : ℕ) : Set SegSpace :=
  {σ | ∃ q ∈ L, ∃ s : ℝ, σ q s ∈ S ∧
    ∃ (lab : Fin N → ℚ × ℚ) (b : Fin N → ℝ), IsLocFamily L ε σ q s lab b} \ locEsc L S U ε

section transfer

variable {c : ℝ → ℂ} {U : Set ℂ} {L : Set (ℚ × ℚ)} {e x : ℚ × ℚ → ℝ}

/-- A segment value in `U` is taken at an interior local time. -/
theorem mem_Ioo_of_clampSeg_mem (hD : IsExcursionFamily c U L e x) {q : ℚ × ℚ} (hq : q ∈ L)
    {s : ℝ} (hs : clampSeg c (e q) (x q) s ∈ U) : s ∈ Ioo 0 (x q - e q) := by
  have hlt := hD.lt q hq
  constructor
  · by_contra h
    push Not at h
    rw [clampSeg_of_nonpos h] at hs
    exact hD.entry_not_mem q hq hs
  · by_contra h
    push Not at h
    rw [clampSeg_of_ge hlt.le h] at hs
    exact hD.exit_not_mem q hq hs

theorem locWindow_clampSeg {ε s e₀ x₀ : ℝ}
    (hs : Icc (s - ε) (s + ε) ⊆ Icc 0 (x₀ - e₀)) (hε : 0 ≤ ε) :
    locWindow ε (clampSeg c e₀ x₀) s = locWindow ε c (e₀ + s) := by
  have h1 := hs ⟨le_rfl, by linarith⟩
  have h2 := hs ⟨by linarith, le_rfl⟩
  unfold locWindow
  rw [clampSeg_image_Icc h1.1 h2.2]
  congr 1
  ring_nf

theorem locBall_clampSeg {ε s e₀ x₀ : ℝ}
    (hs : Icc (s - ε) (s + ε) ⊆ Icc 0 (x₀ - e₀)) (hε : 0 ≤ ε) :
    locBall ε (clampSeg c e₀ x₀) s = locBall ε c (e₀ + s) := by
  unfold locBall
  rw [locWindow_clampSeg hs hε, clampSeg_of_mem (hs ⟨by linarith, by linarith⟩)]

/-- Inside an excursion, a window either stays in it or contains one of its endpoints. -/
theorem window_cases {ε e₀ x₀ t : ℝ} :
    Icc (t - ε) (t + ε) ⊆ Icc e₀ x₀ ∨ (t - ε < e₀ ∧ e₀ ≤ t + ε) ∨ (t + ε > x₀ ∧ t - ε ≤ x₀) ∨
      (t + ε < e₀ ∨ x₀ < t - ε) := by
  by_cases h1 : e₀ ≤ t - ε
  · by_cases h2 : t + ε ≤ x₀
    · exact Or.inl fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩
    · push Not at h2
      by_cases h3 : t - ε ≤ x₀
      · exact Or.inr (Or.inr (Or.inl ⟨h2, h3⟩))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (by linarith))))
  · push Not at h1
    by_cases h3 : e₀ ≤ t + ε
    · exact Or.inr (Or.inl ⟨h1, h3⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))

/-- **Escape is local.** -/
theorem escBad_iff_mem_locEsc (hc : Continuous c) {S : Set ℂ} {ε : ℝ} (hε : 0 ≤ ε)
    (hSU : S ⊆ U) (hD : IsExcursionFamily c U L e x) {σ : SegSpace}
    (hσ : ∀ q ∈ L, ⇑(σ q) = clampSeg c (e q) (x q)) :
    EscBad c S U ε ↔ σ ∈ locEsc L S U ε := by
  constructor
  · rintro ⟨t, htS, hnot⟩
    obtain ⟨q, hq, htq⟩ := hD.cover t (hSU htS)
    have hlt := hD.lt q hq
    have hσq := hσ q hq
    have hval : σ q (t - e q) = c t := by
      rw [hσq, clampSeg_of_mem ⟨by linarith [htq.1], by linarith [htq.2]⟩]
      congr 1
      ring
    refine ⟨q, hq, t - e q, hval ▸ htS, ?_⟩
    intro hsub
    rcases window_cases (ε := ε) (e₀ := e q) (x₀ := x q) (t := t) with hA | hB | hB | hB
    · apply hnot
      have hA1 := (hA ⟨le_rfl, by linarith⟩).1
      have hA2 := (hA ⟨by linarith, le_rfl⟩).2
      have hs : Icc (t - e q - ε) (t - e q + ε) ⊆ Icc 0 (x q - e q) := fun u hu =>
        ⟨by linarith [hu.1], by linarith [hu.2]⟩
      have := locBall_clampSeg (c := c) hs hε
      rw [← hσq, show e q + (t - e q) = t by ring] at this
      rwa [← this]
    · -- the local window contains the entrance point
      have h0 : (0 : ℝ) ∈ Icc (t - e q - ε) (t - e q + ε) :=
        ⟨by linarith [hB.1], by linarith [htq.1]⟩
      have hmem : σ q 0 ∈ locBall ε (σ q) (t - e q) :=
        locWindow_subset_locBall (σ q).continuous hε (mem_image_of_mem _ h0)
      have h0v : σ q 0 = c (e q) := by
        rw [hσq, clampSeg_of_mem ⟨le_rfl, by linarith⟩, add_zero]
      exact hD.entry_not_mem q hq (h0v ▸ hsub hmem)
    · have h0 : x q - e q ∈ Icc (t - e q - ε) (t - e q + ε) :=
        ⟨by linarith [htq.2], by linarith [hB.1]⟩
      have hmem : σ q (x q - e q) ∈ locBall ε (σ q) (t - e q) :=
        locWindow_subset_locBall (σ q).continuous hε (mem_image_of_mem _ h0)
      have h0v : σ q (x q - e q) = c (x q) := by
        rw [hσq, clampSeg_of_mem ⟨by linarith, le_rfl⟩]
        congr 1
        ring
      exact hD.exit_not_mem q hq (h0v ▸ hsub hmem)
    · rcases hB with hB | hB
      · linarith [htq.1]
      · linarith [htq.2]
  · rintro ⟨q, hq, s, hsS, hnot⟩
    have hlt := hD.lt q hq
    have hσq := hσ q hq
    have hsI : s ∈ Ioo 0 (x q - e q) := by
      apply mem_Ioo_of_clampSeg_mem hD hq
      rw [← hσq]
      exact hSU hsS
    have hval : σ q s = c (e q + s) := by
      rw [hσq, clampSeg_of_mem ⟨hsI.1.le, hsI.2.le⟩]
    refine ⟨e q + s, hval ▸ hsS, ?_⟩
    intro hsub
    rcases window_cases (ε := ε) (e₀ := e q) (x₀ := x q) (t := e q + s) with hA | hB | hB | hB
    · apply hnot
      have hs : Icc (s - ε) (s + ε) ⊆ Icc 0 (x q - e q) := fun u hu =>
        ⟨by linarith [hu.1, (hA ⟨le_rfl, by linarith⟩).1],
          by linarith [hu.2, (hA ⟨by linarith, le_rfl⟩).2]⟩
      rw [hσq, locBall_clampSeg hs hε]
      exact hsub
    · have hmem : c (e q) ∈ locBall ε c (e q + s) :=
        locWindow_subset_locBall hc hε (mem_image_of_mem _ ⟨hB.1.le, by linarith [hsI.1]⟩)
      exact hD.entry_not_mem q hq (hsub hmem)
    · have hmem : c (x q) ∈ locBall ε c (e q + s) :=
        locWindow_subset_locBall hc hε (mem_image_of_mem _ ⟨by linarith [hsI.2], hB.1.le⟩)
      exact hD.exit_not_mem q hq (hsub hmem)
    · rcases hB with hB | hB
      · linarith [hsI.1]
      · linarith [hsI.2]

open Classical in
/-- A canonical label for each excursion entrance time. -/
def canonLabel (L : Set (ℚ × ℚ)) (e : ℚ × ℚ → ℝ) (r : ℝ) : ℚ × ℚ :=
  if h : ∃ q ∈ L, e q = r then Classical.choose h else 0

theorem canonLabel_spec {L : Set (ℚ × ℚ)} {e : ℚ × ℚ → ℝ} {q : ℚ × ℚ} (hq : q ∈ L) :
    canonLabel L e (e q) ∈ L ∧ e (canonLabel L e (e q)) = e q := by
  have h : ∃ q' ∈ L, e q' = e q := ⟨q, hq, rfl⟩
  classical
  unfold canonLabel
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact Classical.choose_spec h

/-- Segments of excursions with the same entrance coincide. -/
theorem seg_eq_of_entry_eq (hD : IsExcursionFamily c U L e x) {σ : SegSpace}
    (hσ : ∀ q ∈ L, ⇑(σ q) = clampSeg c (e q) (x q)) {q q' : ℚ × ℚ} (hq : q ∈ L) (hq' : q' ∈ L)
    (he : e q = e q') : σ q = σ q' := by
  apply DFunLike.coe_injective
  rw [hσ q hq, hσ q' hq', he, hD.exit_eq_of_entry_eq hq hq' he]

theorem disjoint_Ioo_shift {a a' d ε : ℝ}
    (h : Disjoint (Ioo a (a + ε)) (Ioo a' (a' + ε))) :
    Disjoint (Ioo (a + d) (a + d + ε)) (Ioo (a' + d) (a' + d + ε)) := by
  rw [Set.disjoint_left] at h ⊢
  intro u hu hu'
  exact h (a := u - d) ⟨by linarith [hu.1], by linarith [hu.2]⟩
    ⟨by linarith [hu'.1], by linarith [hu'.2]⟩

/-- **The inner degree on the non-escape event is local.** -/
theorem innerAt_and_not_escBad_iff (hc : Continuous c) {S : Set ℂ} {ε : ℝ} (hε : 0 ≤ ε)
    (hSU : S ⊆ U) (hD : IsExcursionFamily c U L e x) {μ : Measure ℂ}
    (hμ : ∀ s t : ℝ, s ≤ t → μ (c '' Icc s t) = ENNReal.ofReal (t - s)) {σ : SegSpace}
    (hσ : ∀ q ∈ L, ⇑(σ q) = clampSeg c (e q) (x q)) (N : ℕ) :
    (InnerAt c S ε N ∧ ¬ EscBad c S U ε) ↔ σ ∈ locInner L S U ε N := by
  have hesc := escBad_iff_mem_locEsc hc hε hSU hD hσ
  constructor
  · rintro ⟨⟨t, htS, hdeg⟩, hnesc⟩
    refine ⟨?_, fun h => hnesc (hesc.2 h)⟩
    have hball : locBall ε c t ⊆ U := by
      by_contra h
      exact hnesc ⟨t, htS, h⟩
    have hwin : ∀ u ∈ Icc (t - ε) (t + ε), c u ∈ U := fun u hu =>
      hball (locWindow_subset_locBall hc hε (mem_image_of_mem c hu))
    obtain ⟨q₀, hq₀, htq⟩ := hD.cover t (hSU htS)
    have hwin' := hD.subset_Ioo hq₀ hwin ⟨by linarith, by linarith⟩ htq
    have hs : Icc (t - e q₀ - ε) (t - e q₀ + ε) ⊆ Icc 0 (x q₀ - e q₀) := by
      have h1 := hwin' ⟨le_rfl, by linarith⟩
      have h2 := hwin' ⟨by linarith, le_rfl⟩
      exact fun u hu => ⟨by linarith [hu.1, h1.1], by linarith [hu.2, h2.2]⟩
    have hball₀ : locBall ε (σ q₀) (t - e q₀) = locBall ε c t := by
      rw [hσ q₀ hq₀, locBall_clampSeg hs hε, show e q₀ + (t - e q₀) = t by ring]
    have hwin₀ : locWindow ε (σ q₀) (t - e q₀) = locWindow ε c t := by
      rw [hσ q₀ hq₀, locWindow_clampSeg hs hε, show e q₀ + (t - e q₀) = t by ring]
    have hval : σ q₀ (t - e q₀) = c t := by
      rw [hσ q₀ hq₀, clampSeg_of_mem (hs ⟨by linarith, by linarith⟩)]
      congr 1
      ring
    obtain ⟨a, ha⟩ := (le_locDegIn_iff N).1 hdeg
    -- each cell lies in an excursion
    have hcell : ∀ i, ∀ u ∈ Icc (a i) (a i + ε), c u ∈ U := fun i u hu =>
      hball ((ha.2 i).1 (mem_image_of_mem c hu))
    have hex : ∀ i, ∃ q ∈ L, a i ∈ Ioo (e q) (x q) := fun i =>
      hD.cover (a i) (hcell i (a i) ⟨le_rfl, by linarith⟩)
    choose qi hqi haq using hex
    let lab : Fin N → ℚ × ℚ := fun i => canonLabel L e (e (qi i))
    have hlab : ∀ i, lab i ∈ L ∧ e (lab i) = e (qi i) := fun i => canonLabel_spec (hqi i)
    have hxlab : ∀ i, x (lab i) = x (qi i) := fun i =>
      hD.exit_eq_of_entry_eq (hlab i).1 (hqi i) (hlab i).2
    have hcellI : ∀ i, Icc (a i) (a i + ε) ⊆ Ioo (e (qi i)) (x (qi i)) := fun i =>
      hD.subset_Ioo (hqi i) (hcell i) ⟨le_rfl, by linarith⟩ (haq i)
    let b : Fin N → ℝ := fun i => a i - e (lab i)
    have himg : ∀ i, (σ (lab i)) '' Icc (b i) (b i + ε) = c '' Icc (a i) (a i + ε) := by
      intro i
      have h1 := hcellI i ⟨le_rfl, by linarith⟩
      have h2 := hcellI i ⟨by linarith, le_rfl⟩
      rw [hσ _ (hlab i).1, clampSeg_image_Icc (by simp only [b]; linarith [h1.1, (hlab i).2])
        (by simp only [b]; linarith [h2.2, (hlab i).2, hxlab i])]
      have e1 : e (lab i) + (a i - e (lab i)) = a i := by ring
      have e2 : e (lab i) + (a i - e (lab i) + ε) = a i + ε := by ring
      simp only [b, e1, e2]
    refine ⟨q₀, hq₀, t - e q₀, hval ▸ htS, lab, b, fun i => (hlab i).1, ?_, ?_, ?_⟩
    · intro i j hij hlij
      have hshift := disjoint_Ioo_shift (d := -e (lab i)) (ha.1 i j hij)
      simp only [b, hlij] at hshift ⊢
      convert hshift using 2 <;> ring_nf
    · intro i j hlij heq
      apply hlij
      have hseg : clampSeg c (e (lab i)) (x (lab i)) = clampSeg c (e (lab j)) (x (lab j)) := by
        rw [← hσ _ (hlab i).1, ← hσ _ (hlab j).1, heq]
      have hee := hD.entry_eq_of_clampSeg_eq hμ (hlab i).1 (hlab j).1 hseg
      simp only [lab]
      rw [← (hlab i).2, ← (hlab j).2]
      simp only [lab] at hee
      rw [hee]
    · intro i
      rw [himg i, hball₀, hwin₀]
      exact ha.2 i
  · rintro ⟨⟨q₀, hq₀, s, hsS, lab, b, hfam⟩, hnloc⟩
    have hnesc : ¬ EscBad c S U ε := fun h => hnloc (hesc.1 h)
    refine ⟨?_, hnesc⟩
    have hsI : s ∈ Ioo 0 (x q₀ - e q₀) := by
      apply mem_Ioo_of_clampSeg_mem hD hq₀
      rw [← hσ q₀ hq₀]
      exact hSU hsS
    set t := e q₀ + s with ht
    have hval : σ q₀ s = c t := by
      rw [hσ q₀ hq₀, clampSeg_of_mem ⟨hsI.1.le, hsI.2.le⟩]
    have htS : c t ∈ S := hval ▸ hsS
    have hball : locBall ε c t ⊆ U := by
      by_contra h
      exact hnesc ⟨t, htS, h⟩
    have hwin : ∀ u ∈ Icc (t - ε) (t + ε), c u ∈ U := fun u hu =>
      hball (locWindow_subset_locBall hc hε (mem_image_of_mem c hu))
    have hwin' := hD.subset_Ioo hq₀ hwin ⟨by linarith, by linarith⟩
      (show t ∈ Ioo (e q₀) (x q₀) from ⟨by linarith [hsI.1], by linarith [hsI.2]⟩)
    have hs : Icc (s - ε) (s + ε) ⊆ Icc 0 (x q₀ - e q₀) := by
      have h1 := hwin' ⟨le_rfl, by linarith⟩
      have h2 := hwin' ⟨by linarith, le_rfl⟩
      exact fun u hu => ⟨by linarith [hu.1, h1.1], by linarith [hu.2, h2.2]⟩
    have hball₀ : locBall ε (σ q₀) s = locBall ε c t := by
      rw [hσ q₀ hq₀, locBall_clampSeg hs hε]
    have hwin₀ : locWindow ε (σ q₀) s = locWindow ε c t := by
      rw [hσ q₀ hq₀, locWindow_clampSeg hs hε]
    obtain ⟨hL, hdisj, hsep, hcells⟩ := hfam
    -- local cells sit inside their excursions
    have hbI : ∀ i, b i ∈ Ioo 0 (x (lab i) - e (lab i)) ∧
        b i + ε ∈ Ioo 0 (x (lab i) - e (lab i)) := by
      intro i
      have hsub : (σ (lab i)) '' Icc (b i) (b i + ε) ⊆ U := by
        rw [hball₀] at hcells
        exact (hcells i).1.trans hball
      constructor
      · apply mem_Ioo_of_clampSeg_mem hD (hL i)
        rw [← hσ _ (hL i)]
        exact hsub (mem_image_of_mem _ ⟨le_rfl, by linarith⟩)
      · apply mem_Ioo_of_clampSeg_mem hD (hL i)
        rw [← hσ _ (hL i)]
        exact hsub (mem_image_of_mem _ ⟨by linarith, le_rfl⟩)
    let a : Fin N → ℝ := fun i => e (lab i) + b i
    have himg : ∀ i, (σ (lab i)) '' Icc (b i) (b i + ε) = c '' Icc (a i) (a i + ε) := by
      intro i
      rw [hσ _ (hL i), clampSeg_image_Icc (hbI i).1.1.le (hbI i).2.2.le]
      simp only [a, add_assoc]
    have hfam' : IsDegInFamily ε c t a := by
      refine ⟨?_, fun i => ?_⟩
      · intro i j hij
        by_cases hlij : lab i = lab j
        · have := disjoint_Ioo_shift (d := e (lab i)) (hdisj i j hij hlij)
          simp only [a, hlij] at this ⊢
          convert this using 2 <;> ring_nf
        · have hne : e (lab i) ≠ e (lab j) := fun he =>
            hsep i j hlij (seg_eq_of_entry_eq hD hσ (hL i) (hL j) he)
          have hex := hD.disjoint_of_entry_ne (hL i) (hL j) hne
          refine hex.mono (fun u hu => ?_) (fun u hu => ?_)
          · exact ⟨by simp only [a] at hu; linarith [hu.1, (hbI i).1.1],
              by simp only [a] at hu; linarith [hu.2, (hbI i).2.2]⟩
          · exact ⟨by simp only [a] at hu; linarith [hu.1, (hbI j).1.1],
              by simp only [a] at hu; linarith [hu.2, (hbI j).2.2]⟩
      · rw [← himg i, ← hball₀, ← hwin₀]
        exact hcells i
    exact ⟨t, htS, le_locDegIn hfam'⟩

end transfer

end MatedCRTHarmonic.GMS4cP
