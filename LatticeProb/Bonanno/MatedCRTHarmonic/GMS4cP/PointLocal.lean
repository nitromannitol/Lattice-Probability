/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cP.PointLocal at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cP.LocalEvents

/-!
# The all-visit point observables read from the excursion segments

Source: [18] Lemma 4.3 for the point observables
`DA^ε(z)`, `deg^ε_in(z)`, `deg^ε_out(z)` of (4.4)–(4.6) and `[18]`, maximized over **all** visits of the
curve to `z` (the `GMS4c.areaRatioPrime`, `degreeInPrime`, `degreeOutPrime`).

At a visit `t` of `z` whose window `c([t−ε, t+ε])` and degree ball lie in `U`, every cell of an inner-degree
family and every crossing of an outer-degree family lies in some excursion of `c` into `U`. Their local
versions (`IsLocFamily`, `IsLocOutFamily`) pick a label and local times; same labels must be disjoint and different
labels must carry different segments. This file proves the per-visit equalities (`locDA_clampSeg`,
`locFamily_iff_degInFamily`, `locOutFamily_iff_degOutFamily`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4cP

open MatedCRTHarmonic.GMS4b

/-- An outer-degree family in local coordinates: crossing `i` is `σ (lab i) ((α i, β i))`. -/
def IsLocOutFamily (L : Set (ℚ × ℚ)) (ε : ℝ) (σ : SegSpace) (q : ℚ × ℚ) (s : ℝ) {N : ℕ}
    (lab : Fin N → ℚ × ℚ) (α β : Fin N → ℝ) : Prop :=
  (∀ i, lab i ∈ L) ∧ (∀ i, α i < β i) ∧
  (∀ i j, i ≠ j → lab i = lab j → Disjoint (Ioo (α i) (β i)) (Ioo (α j) (β j))) ∧
  (∀ i j, lab i ≠ lab j → σ (lab i) ≠ σ (lab j)) ∧
  ∀ i, (σ (lab i)) '' Ioo (α i) (β i) ⊆ interior (locBall ε (σ q) s) ∧
    ((σ (lab i) (α i) ∈ frontier (locBall ε (σ q) s) ∧
        σ (lab i) (β i) ∈ locWindow ε (σ q) s) ∨
      (σ (lab i) (β i) ∈ frontier (locBall ε (σ q) s) ∧
        σ (lab i) (α i) ∈ locWindow ε (σ q) s))

section transfer

variable {c : ℝ → ℂ} {U : Set ℂ} {L : Set (ℚ × ℚ)} {e x : ℚ × ℚ → ℝ}

theorem clampSeg_image_Ioo {e₀ x₀ a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ x₀ - e₀) :
    clampSeg c e₀ x₀ '' Ioo a b = c '' Ioo (e₀ + a) (e₀ + b) := by
  ext w
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨e₀ + u, ⟨by linarith [hu.1], by linarith [hu.2]⟩, ?_⟩
    rw [clampSeg_of_mem ⟨by linarith [hu.1], by linarith [hu.2]⟩]
  · rintro ⟨t, ht, rfl⟩
    refine ⟨t - e₀, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    rw [clampSeg_of_mem ⟨by linarith [ht.1], by linarith [ht.2]⟩]
    congr 1
    ring

/-- `DA^ε` is read inside the excursion. -/
theorem locDA_clampSeg {ε s e₀ x₀ : ℝ} (hs : Icc (s - ε) (s + ε) ⊆ Icc 0 (x₀ - e₀))
    (hε : 0 ≤ ε) :
    locDA ε (clampSeg c e₀ x₀) s = locDA ε c (e₀ + s) := by
  unfold locDA
  have hh : ∀ s' ∈ Icc s (s + ε),
      segRatio (clampSeg c e₀ x₀) (s' - ε) s' = segRatio c (e₀ + s' - ε) (e₀ + s') := by
    intro s' hs'
    unfold segRatio
    have h1 := hs (show s' - ε ∈ Icc (s - ε) (s + ε) from
      ⟨by linarith [hs'.1], by linarith [hs'.2]⟩)
    have h2 := hs (show s' ∈ Icc (s - ε) (s + ε) from ⟨by linarith [hs'.1], by linarith [hs'.2]⟩)
    rw [clampSeg_image_Icc h1.1 h2.2, show e₀ + (s' - ε) = e₀ + s' - ε by ring]
  apply le_antisymm
  · refine iSup₂_le fun s' hs' => ?_
    rw [hh s' hs']
    refine le_iSup₂_of_le (f := fun r (_ : r ∈ Icc (e₀ + s) (e₀ + s + ε)) =>
      segRatio c (r - ε) r) (e₀ + s') ⟨by linarith [hs'.1], by linarith [hs'.2]⟩ le_rfl
  · refine iSup₂_le fun r hr => ?_
    refine le_iSup₂_of_le (f := fun r (_ : r ∈ Icc s (s + ε)) =>
      segRatio (clampSeg c e₀ x₀) (r - ε) r) (r - e₀) ⟨by linarith [hr.1], by linarith [hr.2]⟩ ?_
    rw [hh (r - e₀) ⟨by linarith [hr.1], by linarith [hr.2]⟩]
    apply le_of_eq
    congr 1 <;> ring

theorem disjoint_Ioo_add_left {a b a' b' : ℝ} (d : ℝ)
    (h : Disjoint (Ioo a b) (Ioo a' b')) : Disjoint (Ioo (d + a) (d + b)) (Ioo (d + a') (d + b')) := by
  rw [Set.disjoint_left] at h ⊢
  intro u hu hu'
  exact h (a := u - d) ⟨by linarith [hu.1], by linarith [hu.2]⟩
    ⟨by linarith [hu'.1], by linarith [hu'.2]⟩

theorem disjoint_Ioo_sub_right {a b a' b' : ℝ} (d : ℝ)
    (h : Disjoint (Ioo a b) (Ioo a' b')) : Disjoint (Ioo (a - d) (b - d)) (Ioo (a' - d) (b' - d)) := by
  rw [Set.disjoint_left] at h ⊢
  intro u hu hu'
  exact h (a := u + d) ⟨by linarith [hu.1], by linarith [hu.2]⟩
    ⟨by linarith [hu'.1], by linarith [hu'.2]⟩

/-- The excursion segment family attached to excursion data. -/
theorem frontier_locBall_subset (ε : ℝ) (c' : ℝ → ℂ) (t : ℝ) :
    frontier (locBall ε c' t) ⊆ locBall ε c' t :=
  frontier_subset_closure.trans isClosed_closedBall.closure_subset

/-- **Inner-degree families at one visit are local.** -/
theorem locFamily_iff_degInFamily {ε : ℝ} (hε : 0 ≤ ε)
    (hD : IsExcursionFamily c U L e x) {μ : Measure ℂ}
    (hμ : ∀ s t : ℝ, s ≤ t → μ (c '' Icc s t) = ENNReal.ofReal (t - s)) {σ : SegSpace}
    (hσ : ∀ q ∈ L, ⇑(σ q) = clampSeg c (e q) (x q)) {q₀ : ℚ × ℚ} (hq₀ : q₀ ∈ L) {s : ℝ}
    (hs : Icc (s - ε) (s + ε) ⊆ Icc 0 (x q₀ - e q₀)) (hball : locBall ε c (e q₀ + s) ⊆ U)
    (N : ℕ) :
    (∃ (lab : Fin N → ℚ × ℚ) (b : Fin N → ℝ), IsLocFamily L ε σ q₀ s lab b) ↔
      ∃ a : Fin N → ℝ, IsDegInFamily ε c (e q₀ + s) a := by
  set t := e q₀ + s
  have hball₀ : locBall ε (σ q₀) s = locBall ε c t := by
    rw [hσ q₀ hq₀, locBall_clampSeg hs hε]
  have hwin₀ : locWindow ε (σ q₀) s = locWindow ε c t := by
    rw [hσ q₀ hq₀, locWindow_clampSeg hs hε]
  constructor
  · rintro ⟨lab, b, hL, hdisj, hsep, hcells⟩
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
    refine ⟨a, ?_, fun i => ?_⟩
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
  · rintro ⟨a, ha⟩
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
    refine ⟨lab, b, fun i => (hlab i).1, ?_, ?_, ?_⟩
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

/-- **Outer-degree families at one visit are local.** -/
theorem locOutFamily_iff_degOutFamily (hc : Continuous c) {ε : ℝ} (hε : 0 ≤ ε)
    (hD : IsExcursionFamily c U L e x) {μ : Measure ℂ}
    (hμ : ∀ s t : ℝ, s ≤ t → μ (c '' Icc s t) = ENNReal.ofReal (t - s)) {σ : SegSpace}
    (hσ : ∀ q ∈ L, ⇑(σ q) = clampSeg c (e q) (x q)) {q₀ : ℚ × ℚ} (hq₀ : q₀ ∈ L) {s : ℝ}
    (hs : Icc (s - ε) (s + ε) ⊆ Icc 0 (x q₀ - e q₀)) (hball : locBall ε c (e q₀ + s) ⊆ U)
    (N : ℕ) :
    (∃ (lab : Fin N → ℚ × ℚ) (α β : Fin N → ℝ), IsLocOutFamily L ε σ q₀ s lab α β) ↔
      ∃ a b : Fin N → ℝ, IsDegOutFamily ε c (e q₀ + s) a b := by
  set t := e q₀ + s
  have hball₀ : locBall ε (σ q₀) s = locBall ε c t := by
    rw [hσ q₀ hq₀, locBall_clampSeg hs hε]
  have hwin₀ : locWindow ε (σ q₀) s = locWindow ε c t := by
    rw [hσ q₀ hq₀, locWindow_clampSeg hs hε]
  have hwinU : locWindow ε c t ⊆ U := (locWindow_subset_locBall hc hε).trans hball
  have hfrU : frontier (locBall ε c t) ⊆ U := (frontier_locBall_subset ε c t).trans hball
  have hintU : interior (locBall ε c t) ⊆ U := interior_subset.trans hball
  constructor
  · rintro ⟨lab, α, β, hL, hlt, hdisj, hsep, hcross⟩
    rw [hball₀, hwin₀] at hcross
    have hend : ∀ i, σ (lab i) (α i) ∈ U ∧ σ (lab i) (β i) ∈ U := by
      intro i
      rcases (hcross i).2 with h | h
      · exact ⟨hfrU h.1, hwinU h.2⟩
      · exact ⟨hwinU h.2, hfrU h.1⟩
    have hI : ∀ i, α i ∈ Ioo 0 (x (lab i) - e (lab i)) ∧
        β i ∈ Ioo 0 (x (lab i) - e (lab i)) := by
      intro i
      constructor
      · apply mem_Ioo_of_clampSeg_mem hD (hL i)
        rw [← hσ _ (hL i)]
        exact (hend i).1
      · apply mem_Ioo_of_clampSeg_mem hD (hL i)
        rw [← hσ _ (hL i)]
        exact (hend i).2
    let a : Fin N → ℝ := fun i => e (lab i) + α i
    let b : Fin N → ℝ := fun i => e (lab i) + β i
    have hva : ∀ i, σ (lab i) (α i) = c (a i) := fun i => by
      rw [hσ _ (hL i), clampSeg_of_mem ⟨(hI i).1.1.le, (hI i).1.2.le⟩]
    have hvb : ∀ i, σ (lab i) (β i) = c (b i) := fun i => by
      rw [hσ _ (hL i), clampSeg_of_mem ⟨(hI i).2.1.le, (hI i).2.2.le⟩]
    have himg : ∀ i, (σ (lab i)) '' Ioo (α i) (β i) = c '' Ioo (a i) (b i) := fun i => by
      rw [hσ _ (hL i), clampSeg_image_Ioo (hI i).1.1.le (hI i).2.2.le]
    refine ⟨a, b, fun i => by simp only [a, b]; linarith [hlt i], ?_, fun i => ?_⟩
    · intro i j hij
      by_cases hlij : lab i = lab j
      · have he : e (lab i) = e (lab j) := by rw [hlij]
        simp only [a, b, he]
        exact disjoint_Ioo_add_left _ (hdisj i j hij hlij)
      · have hne : e (lab i) ≠ e (lab j) := fun he =>
          hsep i j hlij (seg_eq_of_entry_eq hD hσ (hL i) (hL j) he)
        have hex := hD.disjoint_of_entry_ne (hL i) (hL j) hne
        refine hex.mono (fun u hu => ?_) (fun u hu => ?_)
        · exact ⟨by simp only [a] at hu; linarith [hu.1, (hI i).1.1],
            by simp only [b] at hu; linarith [hu.2, (hI i).2.2]⟩
        · exact ⟨by simp only [a] at hu; linarith [hu.1, (hI j).1.1],
            by simp only [b] at hu; linarith [hu.2, (hI j).2.2]⟩
    · rw [← himg i, ← hva i, ← hvb i]
      exact hcross i
  · rintro ⟨a, b, hlt, hdisj, hcross⟩
    have hseg : ∀ i, ∀ u ∈ Icc (a i) (b i), c u ∈ U := by
      intro i u hu
      rcases eq_or_lt_of_le hu.1 with h | h
      · rw [← h]
        rcases (hcross i).2 with h' | h'
        · exact hfrU h'.1
        · exact hwinU h'.2
      rcases eq_or_lt_of_le hu.2 with h2 | h2
      · rw [h2]
        rcases (hcross i).2 with h' | h'
        · exact hwinU h'.2
        · exact hfrU h'.1
      · exact hintU ((hcross i).1 (mem_image_of_mem c ⟨h, h2⟩))
    have hex : ∀ i, ∃ q ∈ L, a i ∈ Ioo (e q) (x q) := fun i =>
      hD.cover (a i) (hseg i (a i) ⟨le_rfl, (hlt i).le⟩)
    choose qi hqi haq using hex
    let lab : Fin N → ℚ × ℚ := fun i => canonLabel L e (e (qi i))
    have hlab : ∀ i, lab i ∈ L ∧ e (lab i) = e (qi i) := fun i => canonLabel_spec (hqi i)
    have hxlab : ∀ i, x (lab i) = x (qi i) := fun i =>
      hD.exit_eq_of_entry_eq (hlab i).1 (hqi i) (hlab i).2
    have hI : ∀ i, Icc (a i) (b i) ⊆ Ioo (e (qi i)) (x (qi i)) := fun i =>
      hD.subset_Ioo (hqi i) (hseg i) ⟨le_rfl, (hlt i).le⟩ (haq i)
    let α : Fin N → ℝ := fun i => a i - e (lab i)
    let β : Fin N → ℝ := fun i => b i - e (lab i)
    have hα : ∀ i, α i ∈ Icc 0 (x (lab i) - e (lab i)) := fun i => by
      have h1 := hI i ⟨le_rfl, (hlt i).le⟩
      simp only [α]
      constructor <;> linarith [h1.1, h1.2, (hlab i).2, hxlab i]
    have hβ : ∀ i, β i ∈ Icc 0 (x (lab i) - e (lab i)) := fun i => by
      have h1 := hI i ⟨(hlt i).le, le_rfl⟩
      simp only [β]
      constructor <;> linarith [h1.1, h1.2, (hlab i).2, hxlab i]
    have hva : ∀ i, σ (lab i) (α i) = c (a i) := fun i => by
      rw [hσ _ (hlab i).1, clampSeg_of_mem (hα i)]
      congr 1
      simp only [α]
      ring
    have hvb : ∀ i, σ (lab i) (β i) = c (b i) := fun i => by
      rw [hσ _ (hlab i).1, clampSeg_of_mem (hβ i)]
      congr 1
      simp only [β]
      ring
    have himg : ∀ i, (σ (lab i)) '' Ioo (α i) (β i) = c '' Ioo (a i) (b i) := fun i => by
      rw [hσ _ (hlab i).1, clampSeg_image_Ioo (hα i).1 (hβ i).2]
      congr 1
      simp only [α, β]
      congr 1 <;> ring
    refine ⟨lab, α, β, fun i => (hlab i).1, fun i => by simp only [α, β]; linarith [hlt i],
      ?_, ?_, fun i => ?_⟩
    · intro i j hij hlij
      have he : e (lab i) = e (lab j) := by rw [hlij]
      simp only [α, β, he]
      exact disjoint_Ioo_sub_right _ (hdisj i j hij)
    · intro i j hlij heq
      apply hlij
      have hseg' : clampSeg c (e (lab i)) (x (lab i)) = clampSeg c (e (lab j)) (x (lab j)) := by
        rw [← hσ _ (hlab i).1, ← hσ _ (hlab j).1, heq]
      have hee := hD.entry_eq_of_clampSeg_eq hμ (hlab i).1 (hlab j).1 hseg'
      simp only [lab]
      rw [← (hlab i).2, ← (hlab j).2]
      simp only [lab] at hee
      rw [hee]
    · rw [himg i, hva i, hvb i, hball₀, hwin₀]
      exact hcross i

end transfer

end MatedCRTHarmonic.GMS4cP
