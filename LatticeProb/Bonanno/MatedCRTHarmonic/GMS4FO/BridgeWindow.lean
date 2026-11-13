/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4FO.BridgeWindow at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4FO.BridgeClock

/-!
# Local versus global area time inside an open set

Continuation of `GMS4FO/BridgeClock.lean`, under `BridgeHyp μ c ψ V`, with `ν = μ.restrict V`, a point `z ∈ V`,
its first visit `σ = τ_z(c)` and `η = c ∘ ψ` (the `μ`-area-parametrized curve, first visit `τ = ψ⁻¹ σ`).

* `relTime_eq`: the clamped inverse `relTime ν c σ s` is the first relative time at which the swept mass is `s`;
* `relTime_not_mem`: if `c(σ + u) ∉ V`, then the local curve at the swept mass `S u` is also outside `V`
  (either it is the same point, or the end of a flat stretch, or a clamped end point);
* `locCurve_eq_of_global` (global → local): if `η([a', b']) ⊆ V`, the local curve on `[a, a + b' − a']`
  (`a = S(ψ a' − σ)`) is `s ↦ η(a' + (s − a))`;
* `locCurve_eq_of_local` (local → global): if the local curve maps `[a, b]` into `V`, it is
  `s ↦ η(a' + (s − a))` there (`a' = ψ⁻¹(σ + relTime a)`), and `s ↦ ψ⁻¹(σ + relTime s)` is monotone;
* `globalWindow_subset_of_local`: if the local window `[−ε, ε]` lies in `V`, so does the global window.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4FO

open MatedCRTHarmonic

namespace BridgeHyp

variable {μ : Measure ℂ} {c : ℝ → ℂ} {ψ : ℝ ≃o ℝ} {V : Set ℂ} (H : BridgeHyp μ c ψ V)
include H

/-- The first visit time is a visit time. -/
theorem hitTime_mem (z : ℂ) : c (GMS4b.hitTime c z) = z := by
  have hcl : IsClosed (c ⁻¹' {z}) := isClosed_singleton.preimage H.cont
  have := hcl.csInf_mem (H.visits z).1 (H.visits z).2
  exact this

variable (σ : ℝ)

/-! ### The clamping values -/

theorem sweep_le_sweepTop (u : ℝ) : sweep (μ.restrict V) c σ u ≤ sweepTop (μ.restrict V) c σ := by
  obtain ⟨U₀, hU₀, hc⟩ := H.exists_sweep_const_atTop σ
  have hbdd : BddAbove (sweep (μ.restrict V) c σ '' Ici 0) := by
    refine ⟨sweep (μ.restrict V) c σ U₀, ?_⟩
    rintro _ ⟨v, -, rfl⟩
    rcases le_total v U₀ with h | h
    · exact H.sweep_mono σ h
    · exact (hc v h).le
  have hU : sweep (μ.restrict V) c σ U₀ ≤ sweepTop (μ.restrict V) c σ :=
    le_csSup hbdd ⟨U₀, hU₀, rfl⟩
  rcases le_total u U₀ with h | h
  · exact (H.sweep_mono σ h).trans hU
  · rw [hc u h]; exact hU

theorem sweepTop_mem : ∃ U₀ : ℝ, 0 ≤ U₀ ∧ sweep (μ.restrict V) c σ U₀ = sweepTop (μ.restrict V) c σ ∧
    ∀ u, U₀ ≤ u → sweep (μ.restrict V) c σ u = sweep (μ.restrict V) c σ U₀ := by
  obtain ⟨U₀, hU₀, hc⟩ := H.exists_sweep_const_atTop σ
  refine ⟨U₀, hU₀, le_antisymm (H.sweep_le_sweepTop σ U₀) ?_, hc⟩
  refine csSup_le ⟨_, ⟨U₀, hU₀, rfl⟩⟩ ?_
  rintro _ ⟨v, -, rfl⟩
  rcases le_total v U₀ with h | h
  · exact H.sweep_mono σ h
  · exact (hc v h).le

theorem sweepBot_le_sweep (u : ℝ) : sweepBot (μ.restrict V) c σ ≤ sweep (μ.restrict V) c σ u := by
  obtain ⟨U₁, hU₁, hc⟩ := H.exists_sweep_const_atBot σ
  have hbdd : BddBelow (sweep (μ.restrict V) c σ '' Iic 0) := by
    refine ⟨sweep (μ.restrict V) c σ U₁, ?_⟩
    rintro _ ⟨v, -, rfl⟩
    rcases le_total v U₁ with h | h
    · exact (hc v h).ge
    · exact H.sweep_mono σ h
  have hU : sweepBot (μ.restrict V) c σ ≤ sweep (μ.restrict V) c σ U₁ :=
    csInf_le hbdd ⟨U₁, hU₁, rfl⟩
  rcases le_total u U₁ with h | h
  · rw [hc u h]; exact hU
  · exact hU.trans (H.sweep_mono σ h)

theorem sweepBot_mem : ∃ U₁ : ℝ, U₁ ≤ 0 ∧ sweep (μ.restrict V) c σ U₁ = sweepBot (μ.restrict V) c σ := by
  obtain ⟨U₁, hU₁, hc⟩ := H.exists_sweep_const_atBot σ
  refine ⟨U₁, hU₁, le_antisymm ?_ (H.sweepBot_le_sweep σ U₁)⟩
  refine le_csInf ⟨_, ⟨U₁, hU₁, rfl⟩⟩ ?_
  rintro _ ⟨v, -, rfl⟩
  rcases le_total v U₁ with h | h
  · exact (hc v h).ge
  · exact H.sweep_mono σ h

/-- The swept mass is strictly negative before a root spent in `V`. -/
theorem sweepBot_lt_zero (hσ : c σ ∈ V) : sweepBot (μ.restrict V) c σ < 0 := by
  obtain ⟨δ, hδ, hδV⟩ := H.exists_ball_subset hσ
  have hv : c (σ + -(δ / 2)) ∈ V := hδV _ (by rw [abs_lt]; constructor <;> linarith)
  have h := H.sweep_lt_of_mem σ (u := -δ) (u' := 0) ⟨by linarith, by linarith⟩ hv
  rw [H.sweep_zero σ] at h
  exact (H.sweepBot_le_sweep σ (-δ)).trans_lt h

theorem zero_lt_sweepTop (hσ : c σ ∈ V) : 0 < sweepTop (μ.restrict V) c σ := by
  obtain ⟨δ, hδ, hδV⟩ := H.exists_ball_subset hσ
  have hv : c (σ + δ / 2) ∈ V := hδV _ (by rw [abs_lt]; constructor <;> linarith)
  have h := H.sweep_lt_of_mem σ (u := 0) (u' := δ) ⟨by linarith, by linarith⟩ hv
  rw [H.sweep_zero σ] at h
  exact h.trans_le (H.sweep_le_sweepTop σ δ)

/-- The set of times before which nothing is swept. -/
theorem sweepStart_spec (hσ : c σ ∈ V) :
    sweep (μ.restrict V) c σ (sweepStart (μ.restrict V) c σ) = sweepBot (μ.restrict V) c σ ∧
      ∀ u, sweep (μ.restrict V) c σ u ≤ sweepBot (μ.restrict V) c σ → u ≤ sweepStart (μ.restrict V) c σ := by
  set S := sweep (μ.restrict V) c σ
  set Z := {u | S u ≤ sweepBot (μ.restrict V) c σ}
  obtain ⟨U₁, -, hU₁⟩ := H.sweepBot_mem σ
  have hne : Z.Nonempty := ⟨U₁, hU₁.le⟩
  have hbdd : BddAbove Z := by
    refine ⟨0, fun u hu => ?_⟩
    by_contra h
    push Not at h
    have h1 := H.sweep_mono σ h.le
    have h2 := H.sweepBot_lt_zero σ hσ
    rw [H.sweep_zero σ] at h1
    exact absurd (h1.trans hu) (not_le.2 h2)
  have hcl : IsClosed Z := isClosed_le (H.sweep_continuous σ) continuous_const
  have hmem := hcl.csSup_mem hne hbdd
  exact ⟨le_antisymm hmem (H.sweepBot_le_sweep σ _), fun u hu => le_csSup hbdd hu⟩

/-! ### The clamped inverse -/

/-- **`relTime` is the first time the swept mass reaches `s`.** -/
theorem relTime_eq (hσ : c σ ∈ V) {s u : ℝ} (hbot : sweepBot (μ.restrict V) c σ < s)
    (htop : s ≤ sweepTop (μ.restrict V) c σ) (hS : sweep (μ.restrict V) c σ u = s)
    (hlt : ∀ v < u, sweep (μ.restrict V) c σ v < s) : relTime (μ.restrict V) c σ s = u := by
  obtain ⟨hst, hstart⟩ := H.sweepStart_spec σ hσ
  have hmin : min s (sweepTop (μ.restrict V) c σ) = s := min_eq_left htop
  unfold relTime
  rw [hmin]
  apply IsLeast.csInf_eq
  refine ⟨⟨?_, hS.ge⟩, fun v hv => ?_⟩
  · by_contra h
    push Not at h
    have := H.sweep_mono σ h.le
    rw [hst, hS] at this
    exact absurd hbot (not_lt.2 this)
  · by_contra h
    push Not at h
    exact absurd hv.2 (not_le.2 (hlt v h))

/-- Below the swept range the inverse is clamped at `sweepStart`, where `c` is not in `V`. -/
theorem relTime_of_le_bot (hσ : c σ ∈ V) {s : ℝ} (hs : s ≤ sweepBot (μ.restrict V) c σ) :
    relTime (μ.restrict V) c σ s = sweepStart (μ.restrict V) c σ := by
  unfold relTime
  have hset : {u | sweepStart (μ.restrict V) c σ ≤ u ∧
      min s (sweepTop (μ.restrict V) c σ) ≤ sweep (μ.restrict V) c σ u} =
        Ici (sweepStart (μ.restrict V) c σ) := by
    ext u
    simp only [mem_ofPred_eq, mem_Ici, and_iff_left_iff_imp]
    intro _
    exact (min_le_left _ _).trans (hs.trans (H.sweepBot_le_sweep σ u))
  rw [hset, csInf_Ici]

theorem sweepStart_not_mem (hσ : c σ ∈ V) : c (σ + sweepStart (μ.restrict V) c σ) ∉ V := by
  obtain ⟨hst, -⟩ := H.sweepStart_spec σ hσ
  apply H.not_mem_of_sweep_eq_right σ (u := sweepStart (μ.restrict V) c σ - 1) (by linarith)
  apply le_antisymm (H.sweep_mono σ (by linarith))
  rw [hst]
  exact H.sweepBot_le_sweep σ _

theorem relTime_of_top_le {s : ℝ} (hs : sweepTop (μ.restrict V) c σ ≤ s) :
    relTime (μ.restrict V) c σ s = relTime (μ.restrict V) c σ (sweepTop (μ.restrict V) c σ) := by
  unfold relTime
  rw [min_eq_right hs, min_self]

theorem relTime_top_spec (hσ : c σ ∈ V) :
    sweep (μ.restrict V) c σ (relTime (μ.restrict V) c σ (sweepTop (μ.restrict V) c σ)) =
        sweepTop (μ.restrict V) c σ ∧
      c (σ + relTime (μ.restrict V) c σ (sweepTop (μ.restrict V) c σ)) ∉ V := by
  obtain ⟨U₀, -, hU₀, hc⟩ := H.sweepTop_mem σ
  let A := {u | sweepStart (μ.restrict V) c σ ≤ u ∧
    min (sweepTop (μ.restrict V) c σ) (sweepTop (μ.restrict V) c σ) ≤ sweep (μ.restrict V) c σ u}
  have hne : A.Nonempty := by
    refine ⟨max (sweepStart (μ.restrict V) c σ) U₀, le_max_left _ _, ?_⟩
    rw [min_self, hc _ (le_max_right _ _), hU₀]
  have hbdd : BddBelow A := ⟨sweepStart (μ.restrict V) c σ, fun u hu => hu.1⟩
  have hcl : IsClosed A :=
    (isClosed_le continuous_const continuous_id).inter
      (isClosed_le continuous_const (H.sweep_continuous σ))
  have hmem : sInf A ∈ A := hcl.csInf_mem hne hbdd
  have hrel : relTime (μ.restrict V) c σ (sweepTop (μ.restrict V) c σ) = sInf A := rfl
  have hST : sweep (μ.restrict V) c σ (sInf A) = sweepTop (μ.restrict V) c σ :=
    le_antisymm (H.sweep_le_sweepTop σ _) (by have := hmem.2; rwa [min_self] at this)
  refine ⟨hrel ▸ hST, ?_⟩
  rw [hrel]
  apply H.not_mem_of_sweep_eq_left σ (u' := sInf A + 1) (by linarith)
  refine le_antisymm (H.sweep_mono σ (by linarith)) ?_
  rw [hST]
  exact H.sweep_le_sweepTop σ _

/-- **The local curve at the swept mass of an exit point is outside `V`.** -/
theorem relTime_not_mem (hσ : c σ ∈ V) {u : ℝ} (hcu : c (σ + u) ∉ V) :
    c (σ + relTime (μ.restrict V) c σ (sweep (μ.restrict V) c σ u)) ∉ V := by
  set S := sweep (μ.restrict V) c σ
  set s := S u
  rcases le_or_gt s (sweepBot (μ.restrict V) c σ) with hb | hb
  · rw [H.relTime_of_le_bot σ hσ hb]
    exact H.sweepStart_not_mem σ hσ
  rcases le_or_gt (sweepTop (μ.restrict V) c σ) s with ht | ht
  · rw [H.relTime_of_top_le σ ht]
    exact (H.relTime_top_spec σ hσ).2
  obtain ⟨hst, -⟩ := H.sweepStart_spec σ hσ
  set A := {v | sweepStart (μ.restrict V) c σ ≤ v ∧ min s (sweepTop (μ.restrict V) c σ) ≤ S v}
  have hmin : min s (sweepTop (μ.restrict V) c σ) = s := min_eq_left ht.le
  have huA : u ∈ A := by
    refine ⟨?_, by rw [hmin]⟩
    by_contra h
    push Not at h
    have := H.sweep_mono σ h.le
    rw [hst] at this
    exact absurd hb (not_lt.2 this)
  have hbdd : BddBelow A := ⟨sweepStart (μ.restrict V) c σ, fun v hv => hv.1⟩
  have hcl : IsClosed A :=
    (isClosed_le continuous_const continuous_id).inter
      (isClosed_le continuous_const (H.sweep_continuous σ))
  have hmem : sInf A ∈ A := hcl.csInf_mem ⟨u, huA⟩ hbdd
  have hle : sInf A ≤ u := csInf_le hbdd huA
  have hrel : relTime (μ.restrict V) c σ s = sInf A := rfl
  rw [hrel]
  rcases hle.lt_or_eq with hlt | heq
  · apply H.not_mem_of_sweep_eq_left σ hlt
    have h1 := hmem.2
    rw [hmin] at h1
    exact le_antisymm (H.sweep_mono σ hle) h1
  · rw [heq]; exact hcu

/-- The swept mass is bounded by the `μ`-area time. -/
theorem abs_sweep_le (u : ℝ) :
    |sweep (μ.restrict V) c σ u| ≤ |ψ.symm (σ + u) - ψ.symm σ| := by
  rcases le_total 0 u with hu | hu
  · have h1 := H.sweep_sub_le σ hu
    have h2 := H.sweep_mono σ hu
    rw [H.sweep_zero σ, add_zero] at h1
    rw [H.sweep_zero σ] at h2
    rw [abs_of_nonneg h2, abs_of_nonneg (by linarith)]
    linarith
  · have h1 := H.sweep_sub_le σ hu
    have h2 := H.sweep_mono σ hu
    rw [H.sweep_zero σ, add_zero] at h1
    rw [H.sweep_zero σ] at h2
    rw [abs_of_nonpos h2, abs_of_nonpos (by linarith)]
    linarith

/-! ### Global → local -/

/-- **A global segment inside `V` is read by the local curve.** -/
theorem relTime_of_global (hσ : c σ ∈ V) {a' b' : ℝ} (hab' : a' ≤ b')
    (hsub : (c ∘ ψ) '' Icc a' b' ⊆ V) {s : ℝ}
    (hs : s ∈ Icc (sweep (μ.restrict V) c σ (ψ a' - σ))
      (sweep (μ.restrict V) c σ (ψ a' - σ) + (b' - a'))) :
    relTime (μ.restrict V) c σ s = ψ (a' + (s - sweep (μ.restrict V) c σ (ψ a' - σ))) - σ := by
  set S := sweep (μ.restrict V) c σ
  set a := S (ψ a' - σ)
  have hsub' : ∀ x y, a' ≤ x → y ≤ b' → c '' Icc (ψ x) (ψ y) ⊆ V := by
    intro x y hx hy
    rintro _ ⟨t, ht, rfl⟩
    have h1 : x ≤ ψ.symm t := (ψ.le_symm_apply).2 ht.1
    have h2 : ψ.symm t ≤ y := (ψ.symm_apply_le).2 ht.2
    have h := hsub ⟨ψ.symm t, ⟨hx.trans h1, h2.trans hy⟩, rfl⟩
    simpa using h
  have hSeq : ∀ x, a' ≤ x → x ≤ b' → S (ψ x - σ) = a + (x - a') := by
    intro x hx hxb
    have := H.sweep_sub_of_subset σ (show ψ a' - σ ≤ ψ x - σ by linarith [ψ.monotone hx])
      (by simpa using hsub' a' x le_rfl hxb)
    simp only [add_sub_cancel, OrderIso.symm_apply_apply] at this
    linarith
  have hcV : c (ψ a') ∈ V := hsub ⟨a', ⟨le_rfl, hab'⟩, rfl⟩
  have hx : a' + (s - a) ∈ Icc a' b' := ⟨by linarith [hs.1], by linarith [hs.2]⟩
  apply H.relTime_eq σ hσ
  · obtain ⟨δ, hδ, hδV⟩ := H.exists_ball_subset hcV
    have hv : c (σ + (ψ a' - σ - δ / 2)) ∈ V := hδV _ (by rw [abs_lt]; constructor <;> linarith)
    have := H.sweep_lt_of_mem σ (u := ψ a' - σ - δ) (u' := ψ a' - σ) ⟨by linarith, by linarith⟩ hv
    exact ((H.sweepBot_le_sweep σ _).trans_lt this).trans_le hs.1
  · calc s ≤ a + (b' - a') := hs.2
      _ = S (ψ b' - σ) := (hSeq b' hab' le_rfl).symm
      _ ≤ _ := H.sweep_le_sweepTop σ _
  · change S (ψ (a' + (s - a)) - σ) = s
    rw [hSeq _ hx.1 hx.2]; ring
  · intro v hv
    rcases le_or_gt (ψ a' - σ) v with hva | hva
    · have hvx : ψ.symm (σ + v) < a' + (s - a) := by
        rw [OrderIso.symm_apply_lt]
        linarith
      have hva' : a' ≤ ψ.symm (σ + v) := by rw [OrderIso.le_symm_apply]; linarith
      have := hSeq (ψ.symm (σ + v)) hva' (hvx.le.trans hx.2)
      rw [OrderIso.apply_symm_apply, add_sub_cancel_left] at this
      change S v < s
      rw [this]
      linarith
    · obtain ⟨δ, hδ, hδV⟩ := H.exists_ball_subset hcV
      have hw1 : v ≤ max v (ψ a' - σ - δ / 2) := le_max_left _ _
      have hw3 : ψ a' - σ - δ / 2 ≤ max v (ψ a' - σ - δ / 2) := le_max_right _ _
      have hw2 : max v (ψ a' - σ - δ / 2) < ψ a' - σ := max_lt hva (by linarith)
      have hv'V : c (σ + (max v (ψ a' - σ - δ / 2) + (ψ a' - σ)) / 2) ∈ V := hδV _ (by
        rw [abs_lt]; constructor <;> linarith)
      have := H.sweep_lt_of_mem σ (u := v) (u' := ψ a' - σ)
        (v := (max v (ψ a' - σ - δ / 2) + (ψ a' - σ)) / 2) ⟨by linarith, by linarith⟩ hv'V
      exact this.trans_le hs.1

/-- **The local curve on a global segment inside `V`.** -/
theorem locCurve_eq_of_global {z : ℂ} (hz : z ∈ V) {a' b' : ℝ} (hab' : a' ≤ b')
    (hsub : (c ∘ ψ) '' Icc a' b' ⊆ V) {s : ℝ}
    (hs : s ∈ Icc (sweep (μ.restrict V) c (GMS4b.hitTime c z) (ψ a' - GMS4b.hitTime c z))
      (sweep (μ.restrict V) c (GMS4b.hitTime c z) (ψ a' - GMS4b.hitTime c z) + (b' - a'))) :
    locCurve (μ.restrict V) c z s =
      (c ∘ ψ) (a' + (s - sweep (μ.restrict V) c (GMS4b.hitTime c z) (ψ a' - GMS4b.hitTime c z))) := by
  have hσ : c (GMS4b.hitTime c z) ∈ V := by rw [H.hitTime_mem z]; exact hz
  unfold locCurve
  rw [H.relTime_of_global _ hσ hab' hsub hs, add_sub_cancel]
  rfl

end BridgeHyp

end MatedCRTHarmonic.GMS4FO
