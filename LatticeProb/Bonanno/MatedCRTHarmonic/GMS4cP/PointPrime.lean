/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cP.PointPrime at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cP.PointLocal
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.DegOutMeasurable
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.PrimedObservables

/-!
# The all-visit point observables of `z` from the excursion segments

Source: [18] Lemma 4.3 and the primed observables of
the local and global observables (`GMS4c.areaRatioPrime`, `degreeInPrime`, `degreeOutPrime`: suprema over all visits of `z`).

For a point `z ∈ U` with `B̄_{4 r₀}(z) ⊆ U`, on the event that every visit window has diameter `≤ r₀`
(the window test of (4.22)), the three all-visit maxima are the corresponding suprema over **local** visits
`(q, s)` (`σ q s = z`) of the local quantities. The window test itself is local (`winOK_iff`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4cP

open MatedCRTHarmonic.GMS4b MatedCRTHarmonic.GMS4c

/-- A visit of `z` in local coordinates. -/
def IsLocVisit (L : Set (ℚ × ℚ)) (z : ℂ) (σ : SegSpace) (q : ℚ × ℚ) (s : ℝ) : Prop :=
  q ∈ L ∧ σ q s = z

/-- The local window test: every local visit window has diameter at most `r₀`. -/
def locWinOK (L : Set (ℚ × ℚ)) (z : ℂ) (ε r₀ : ℝ) (σ : SegSpace) : Prop :=
  ∀ q s, IsLocVisit L z σ q s → diam (locWindow ε (σ q) s) ≤ r₀

/-- The local all-visit `DA^ε(z)`. -/
def locDAPrime (L : Set (ℚ × ℚ)) (z : ℂ) (ε : ℝ) (σ : SegSpace) : ℝ≥0∞ :=
  ⨆ (q : ℚ × ℚ) (s : ℝ) (_ : IsLocVisit L z σ q s), locDA ε (σ q) s

/-- The local inner degree at a local visit. -/
def locInAt (L : Set (ℚ × ℚ)) (ε : ℝ) (σ : SegSpace) (q : ℚ × ℚ) (s : ℝ) : ℕ∞ :=
  ⨆ (N : ℕ) (lab : Fin N → ℚ × ℚ) (b : Fin N → ℝ) (_ : IsLocFamily L ε σ q s lab b), (N : ℕ∞)

/-- The local outer degree at a local visit. -/
def locOutAt (L : Set (ℚ × ℚ)) (ε : ℝ) (σ : SegSpace) (q : ℚ × ℚ) (s : ℝ) : ℕ∞ :=
  ⨆ (N : ℕ) (lab : Fin N → ℚ × ℚ) (α : Fin N → ℝ) (β : Fin N → ℝ)
    (_ : IsLocOutFamily L ε σ q s lab α β), (N : ℕ∞)

/-- The local all-visit `deg^ε_in(z)`. -/
def locDegInPrime (L : Set (ℚ × ℚ)) (z : ℂ) (ε : ℝ) (σ : SegSpace) : ℕ∞ :=
  ⨆ (q : ℚ × ℚ) (s : ℝ) (_ : IsLocVisit L z σ q s), locInAt L ε σ q s

/-- The local all-visit `deg^ε_out(z)`. -/
def locDegOutPrime (L : Set (ℚ × ℚ)) (z : ℂ) (ε : ℝ) (σ : SegSpace) : ℕ∞ :=
  ⨆ (q : ℚ × ℚ) (s : ℝ) (_ : IsLocVisit L z σ q s), locOutAt L ε σ q s

section families

variable {L : Set (ℚ × ℚ)} {ε : ℝ} {σ : SegSpace} {q : ℚ × ℚ} {s : ℝ}
theorem IsLocFamily.castLE {M N : ℕ} {lab : Fin N → ℚ × ℚ} {b : Fin N → ℝ}
    (h : IsLocFamily L ε σ q s lab b) (hMN : M ≤ N) :
    IsLocFamily L ε σ q s (lab ∘ Fin.castLE hMN) (b ∘ Fin.castLE hMN) :=
  ⟨fun _ => h.1 _, fun _ _ hij hl => h.2.1 _ _ (fun he => hij (Fin.castLE_injective hMN he)) hl,
    fun _ _ hl => h.2.2.1 _ _ hl, fun _ => h.2.2.2 _⟩

theorem IsLocOutFamily.castLE {M N : ℕ} {lab : Fin N → ℚ × ℚ} {α β : Fin N → ℝ}
    (h : IsLocOutFamily L ε σ q s lab α β) (hMN : M ≤ N) :
    IsLocOutFamily L ε σ q s (lab ∘ Fin.castLE hMN) (α ∘ Fin.castLE hMN) (β ∘ Fin.castLE hMN) :=
  ⟨fun _ => h.1 _, fun _ => h.2.1 _,
    fun _ _ hij hl => h.2.2.1 _ _ (fun he => hij (Fin.castLE_injective hMN he)) hl,
    fun _ _ hl => h.2.2.2.1 _ _ hl, fun _ => h.2.2.2.2 _⟩

/-- A sup of natural numbers over families attains every value below it at the same size. -/
theorem le_iSup_families_iff {P : ℕ → Prop} (hmono : ∀ {M N : ℕ}, M ≤ N → P N → P M)
    (h0 : P 0) (k : ℕ) : (k : ℕ∞) ≤ (⨆ (N : ℕ) (_ : P N), (N : ℕ∞)) ↔ P k := by
  constructor
  · intro hk
    rcases Nat.eq_zero_or_pos k with hk0 | hpos
    · subst hk0
      exact h0
    by_contra hno
    have hle : (⨆ (N : ℕ) (_ : P N), (N : ℕ∞)) ≤ ((k - 1 : ℕ) : ℕ∞) := by
      refine iSup₂_le fun N hN => ?_
      by_contra hlt
      push Not at hlt
      have hkN : k ≤ N := by
        have : (k - 1 : ℕ) < N := Nat.cast_lt.mp hlt
        omega
      exact hno (hmono hkN hN)
    have := hk.trans hle
    have : k ≤ k - 1 := Nat.cast_le.mp this
    omega
  · intro hk
    exact le_iSup₂_of_le (f := fun (N : ℕ) (_ : P N) => (N : ℕ∞)) k hk le_rfl

theorem le_locInAt_iff (k : ℕ) :
    (k : ℕ∞) ≤ locInAt L ε σ q s ↔
      ∃ (lab : Fin k → ℚ × ℚ) (b : Fin k → ℝ), IsLocFamily L ε σ q s lab b := by
  have h : locInAt L ε σ q s = ⨆ (N : ℕ) (_ : ∃ (lab : Fin N → ℚ × ℚ) (b : Fin N → ℝ),
      IsLocFamily L ε σ q s lab b), (N : ℕ∞) := by
    unfold locInAt
    congr 1
    funext N
    apply le_antisymm
    · exact iSup_le fun lab => iSup_le fun b => iSup_le fun hf =>
        le_iSup_of_le ⟨lab, b, hf⟩ le_rfl
    · exact iSup_le fun ⟨lab, b, hf⟩ => le_iSup_of_le lab (le_iSup_of_le b (le_iSup_of_le hf le_rfl))
  rw [h]
  exact le_iSup_families_iff (fun hMN ⟨lab, b, hf⟩ => ⟨_, _, hf.castLE hMN⟩)
    ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0⟩ k

theorem le_locOutAt_iff (k : ℕ) :
    (k : ℕ∞) ≤ locOutAt L ε σ q s ↔
      ∃ (lab : Fin k → ℚ × ℚ) (α β : Fin k → ℝ), IsLocOutFamily L ε σ q s lab α β := by
  have h : locOutAt L ε σ q s = ⨆ (N : ℕ) (_ : ∃ (lab : Fin N → ℚ × ℚ) (α β : Fin N → ℝ),
      IsLocOutFamily L ε σ q s lab α β), (N : ℕ∞) := by
    unfold locOutAt
    congr 1
    funext N
    apply le_antisymm
    · exact iSup_le fun lab => iSup_le fun α => iSup_le fun β => iSup_le fun hf =>
        le_iSup_of_le ⟨lab, α, β, hf⟩ le_rfl
    · exact iSup_le fun ⟨lab, α, β, hf⟩ =>
        le_iSup_of_le lab (le_iSup_of_le α (le_iSup_of_le β (le_iSup_of_le hf le_rfl)))
  rw [h]
  exact le_iSup_families_iff (fun hMN ⟨lab, α, β, hf⟩ => ⟨_, _, _, hf.castLE hMN⟩)
    ⟨Fin.elim0, Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
      fun i => i.elim0, fun i => i.elim0⟩ k

theorem enat_eq_of_forall_le_iff {m n : ℕ∞} (h : ∀ k : ℕ, (k : ℕ∞) ≤ m ↔ (k : ℕ∞) ≤ n) :
    m = n :=
  le_antisymm (ENat.forall_natCast_le_iff_le.1 fun k hk => (h k).1 hk)
    (ENat.forall_natCast_le_iff_le.1 fun k hk => (h k).2 hk)

end families

section transfer

variable {c : ℝ → ℂ} {U : Set ℂ} {L : Set (ℚ × ℚ)} {e x : ℚ × ℚ → ℝ}

/-- A window of small diameter about a point of `U` stays in `U`. -/
theorem window_mem_of_diam_le {c' : ℝ → ℂ} (hc' : Continuous c') {ε t r₀ : ℝ}
    (hd : diam (locWindow ε c' t) ≤ r₀) (hU : closedBall (c' t) r₀ ⊆ U) :
    ∀ u ∈ Icc (t - ε) (t + ε), c' u ∈ U := by
  intro u hu
  apply hU
  rw [mem_closedBall]
  have hb : Bornology.IsBounded (locWindow ε c' t) :=
    (isCompact_Icc.image hc').isBounded
  exact (dist_le_diam_of_mem hb (mem_image_of_mem c' hu)
    (mem_image_of_mem c' ⟨by linarith [hu.1, hu.2], by linarith [hu.1, hu.2]⟩)).trans hd

/-- The local window of a local visit lies in its excursion if its diameter is small. -/
theorem localWindow_inside (hD : IsExcursionFamily c U L e x) {σ : SegSpace}
    (hσ : ∀ q ∈ L, ⇑(σ q) = clampSeg c (e q) (x q)) {q : ℚ × ℚ} (hq : q ∈ L) {z : ℂ}
    {ε s r₀ : ℝ} (hvz : σ q s = z) (hd : diam (locWindow ε (σ q) s) ≤ r₀)
    (hU : closedBall z r₀ ⊆ U) : Icc (s - ε) (s + ε) ⊆ Icc 0 (x q - e q) := by
  intro u hu
  have hmem := window_mem_of_diam_le (σ q).continuous hd (hvz ▸ hU) u hu
  rw [hσ q hq] at hmem
  exact Ioo_subset_Icc_self (mem_Ioo_of_clampSeg_mem hD hq hmem)

/-- The true window at a visit lies in its excursion if its diameter is small. -/
theorem trueWindow_inside (hc : Continuous c) (hD : IsExcursionFamily c U L e x)
    {q : ℚ × ℚ} (hq : q ∈ L) {t ε r₀ : ℝ} (ht : t ∈ Ioo (e q) (x q))
    (hd : diam (locWindow ε c t) ≤ r₀) (hU : closedBall (c t) r₀ ⊆ U) (hε : 0 ≤ ε) :
    Icc (t - e q - ε) (t - e q + ε) ⊆ Icc 0 (x q - e q) := by
  have hsub := hD.subset_Ioo hq (window_mem_of_diam_le hc hd hU)
    ⟨by linarith, by linarith⟩ ht
  have h1 := hsub ⟨le_rfl, by linarith⟩
  have h2 := hsub ⟨by linarith, le_rfl⟩
  exact fun u hu => ⟨by linarith [hu.1, h1.1], by linarith [hu.2, h2.2]⟩

/-- The local data of a visit. -/
theorem exists_locVisit (hD : IsExcursionFamily c U L e x) {σ : SegSpace}
    (hσ : ∀ q ∈ L, ⇑(σ q) = clampSeg c (e q) (x q)) {z : ℂ} (hzU : z ∈ U) {t : ℝ}
    (ht : c t = z) : ∃ q ∈ L, t ∈ Ioo (e q) (x q) ∧ IsLocVisit L z σ q (t - e q) := by
  obtain ⟨q, hq, htq⟩ := hD.cover t (ht ▸ hzU)
  refine ⟨q, hq, htq, hq, ?_⟩
  rw [hσ q hq, clampSeg_of_mem ⟨by linarith [htq.1], by linarith [htq.2]⟩,
    show e q + (t - e q) = t by ring, ht]

/-- The true visit of a local visit. -/
theorem trueVisit_of_locVisit (hD : IsExcursionFamily c U L e x) {σ : SegSpace}
    (hσ : ∀ q ∈ L, ⇑(σ q) = clampSeg c (e q) (x q)) {z : ℂ} (hzU : z ∈ U) {q : ℚ × ℚ}
    {s : ℝ} (hv : IsLocVisit L z σ q s) :
    s ∈ Ioo 0 (x q - e q) ∧ c (e q + s) = z := by
  have hs : s ∈ Ioo 0 (x q - e q) := by
    apply mem_Ioo_of_clampSeg_mem hD hv.1
    rw [← hσ q hv.1, hv.2]
    exact hzU
  refine ⟨hs, ?_⟩
  rw [← hv.2, hσ q hv.1, clampSeg_of_mem ⟨hs.1.le, hs.2.le⟩]

/-- **The window test is local.** -/
theorem winOK_iff (hc : Continuous c) {ε : ℝ} (hε : 0 ≤ ε) (hD : IsExcursionFamily c U L e x)
    {σ : SegSpace} (hσ : ∀ q ∈ L, ⇑(σ q) = clampSeg c (e q) (x q)) {z : ℂ} {r₀ : ℝ}
    (hzU : z ∈ U) (hz1 : closedBall z r₀ ⊆ U) :
    (∀ t, c t = z → diam (locWindow ε c t) ≤ r₀) ↔ locWinOK L z ε r₀ σ := by
  constructor
  · intro h q s hv
    obtain ⟨hs, hct⟩ := trueVisit_of_locVisit hD hσ hzU hv
    have hd := h _ hct
    have hin := trueWindow_inside hc hD hv.1 (t := e q + s)
      ⟨by linarith [hs.1], by linarith [hs.2]⟩ hd (hct ▸ hz1) hε
    simp only [add_sub_cancel_left] at hin
    rw [hσ q hv.1, locWindow_clampSeg hin hε]
    exact hd
  · intro h t ht
    obtain ⟨q, hq, htq, hv⟩ := exists_locVisit hD hσ hzU ht
    have hd := h q (t - e q) hv
    have hin := localWindow_inside hD hσ hq hv.2 hd hz1
    rw [hσ q hq, locWindow_clampSeg hin hε, show e q + (t - e q) = t by ring] at hd
    exact hd

/-- Per-visit identities under a small window. -/
theorem visit_identities (hc : Continuous c) {ε : ℝ} (hε : 0 ≤ ε)
    (hD : IsExcursionFamily c U L e x) {μ : Measure ℂ}
    (hμ : ∀ s t : ℝ, s ≤ t → μ (c '' Icc s t) = ENNReal.ofReal (t - s)) {σ : SegSpace}
    (hσ : ∀ q ∈ L, ⇑(σ q) = clampSeg c (e q) (x q)) {z : ℂ} {r₀ : ℝ}
    (hz4 : closedBall z (4 * r₀) ⊆ U) {q : ℚ × ℚ} (hq : q ∈ L) {s : ℝ}
    (hs : Icc (s - ε) (s + ε) ⊆ Icc 0 (x q - e q)) (hct : c (e q + s) = z)
    (hd : diam (locWindow ε c (e q + s)) ≤ r₀) :
    locDA ε (σ q) s = locDA ε c (e q + s) ∧
      locInAt L ε σ q s = locDegIn ε c (e q + s) ∧
      locOutAt L ε σ q s = locDegOut ε c (e q + s) := by
  have hball : locBall ε c (e q + s) ⊆ U := by
    refine (closedBall_subset_closedBall ?_).trans (hct ▸ hz4)
    linarith
  refine ⟨by rw [hσ q hq, locDA_clampSeg hs hε], ?_, ?_⟩
  · refine enat_eq_of_forall_le_iff fun k => ?_
    rw [le_locInAt_iff, le_locDegIn_iff]
    exact locFamily_iff_degInFamily hε hD hμ hσ hq hs hball k
  · refine enat_eq_of_forall_le_iff fun k => ?_
    rw [le_locOutAt_iff, le_locDegOut_iff]
    exact locOutFamily_iff_degOutFamily hc hε hD hμ hσ hq hs hball k

/-- **The all-visit point observables are local on the window event.** -/
theorem prime_identities (hc : Continuous c) {ε : ℝ} (hε : 0 ≤ ε)
    (hD : IsExcursionFamily c U L e x) {μ : Measure ℂ}
    (hμ : ∀ s t : ℝ, s ≤ t → μ (c '' Icc s t) = ENNReal.ofReal (t - s)) {σ : SegSpace}
    (hσ : ∀ q ∈ L, ⇑(σ q) = clampSeg c (e q) (x q)) {z : ℂ} {r₀ : ℝ} (hr₀ : 0 ≤ r₀)
    (hz4 : closedBall z (4 * r₀) ⊆ U)
    (hwin : ∀ t, c t = z → diam (locWindow ε c t) ≤ r₀) :
    locDAPrime L z ε σ = areaRatioPrime ε c z ∧
      locDegInPrime L z ε σ = degreeInPrime ε c z ∧
      locDegOutPrime L z ε σ = degreeOutPrime ε c z := by
  have hz1 : closedBall z r₀ ⊆ U := (closedBall_subset_closedBall (by linarith)).trans hz4
  have hzU : z ∈ U := hz1 (mem_closedBall_self hr₀)
  -- each local visit is a true visit with the same values
  have hloc : ∀ q s, IsLocVisit L z σ q s →
      locDA ε (σ q) s = locDA ε c (e q + s) ∧
        locInAt L ε σ q s = locDegIn ε c (e q + s) ∧
        locOutAt L ε σ q s = locDegOut ε c (e q + s) := by
    intro q s hv
    obtain ⟨hs, hct⟩ := trueVisit_of_locVisit hD hσ hzU hv
    have hd := hwin _ hct
    have hin := trueWindow_inside hc hD hv.1 (t := e q + s)
      ⟨by linarith [hs.1], by linarith [hs.2]⟩ hd (hct ▸ hz1) hε
    simp only [add_sub_cancel_left] at hin
    exact visit_identities hc hε hD hμ hσ hz4 hv.1 hin hct hd
  -- each true visit is a local visit with the same values
  have htrue : ∀ t, c t = z → ∃ q s, IsLocVisit L z σ q s ∧ e q + s = t := by
    intro t ht
    obtain ⟨q, hq, htq, hv⟩ := exists_locVisit hD hσ hzU ht
    exact ⟨q, t - e q, hv, by ring⟩
  refine ⟨?_, ?_, ?_⟩
  · apply le_antisymm
    · refine iSup_le fun q => iSup_le fun s => iSup_le fun hv => ?_
      rw [(hloc q s hv).1]
      exact le_iSup_of_le (e q + s) (le_iSup_of_le (trueVisit_of_locVisit hD hσ hzU hv).2 le_rfl)
    · refine iSup_le fun t => iSup_le fun ht => ?_
      obtain ⟨q, s, hv, hqs⟩ := htrue t ht
      rw [← hqs, ← (hloc q s hv).1]
      exact le_iSup_of_le q (le_iSup_of_le s (le_iSup_of_le hv le_rfl))
  · apply le_antisymm
    · refine iSup_le fun q => iSup_le fun s => iSup_le fun hv => ?_
      rw [(hloc q s hv).2.1]
      exact le_iSup_of_le (e q + s) (le_iSup_of_le (trueVisit_of_locVisit hD hσ hzU hv).2 le_rfl)
    · refine iSup_le fun t => iSup_le fun ht => ?_
      obtain ⟨q, s, hv, hqs⟩ := htrue t ht
      rw [← hqs, ← (hloc q s hv).2.1]
      exact le_iSup_of_le q (le_iSup_of_le s (le_iSup_of_le hv le_rfl))
  · apply le_antisymm
    · refine iSup_le fun q => iSup_le fun s => iSup_le fun hv => ?_
      rw [(hloc q s hv).2.2]
      exact le_iSup_of_le (e q + s) (le_iSup_of_le (trueVisit_of_locVisit hD hσ hzU hv).2 le_rfl)
    · refine iSup_le fun t => iSup_le fun ht => ?_
      obtain ⟨q, s, hv, hqs⟩ := htrue t ht
      rw [← hqs, ← (hloc q s hv).2.2]
      exact le_iSup_of_le q (le_iSup_of_le s (le_iSup_of_le hv le_rfl))

end transfer

end MatedCRTHarmonic.GMS4cP
