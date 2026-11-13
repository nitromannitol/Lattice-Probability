/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4FO.BridgeFamily at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4FO.BridgeWindow

/-!
# The bridge: Lebesgue-time localized observables equal the geometric ones

Source: [18], §4.2, Lemma 4.3.

Under `BridgeHyp μ c ψ V` (`η = c ∘ ψ` parametrized by `μ`-area), for a point `z` whose degree ball
`B̄^ε_z = closedBall z (4 diam η([τ_z − ε, τ_z + ε]))` lies in `V`, the local curve of `(μ|_V, c)` at `z` agrees
with `η(τ_z + ·)` on the window, and the inner/outer degree families of the two curves correspond (each local cell
inside `V` is a global cell of the same image, and conversely), so (`locU_eq_uStar`)

  `locU (μ.restrict V) c ε z = GMS4b.uStar ε η z`.

Main result (`localGood_iff_globalGood`): if `D ⊆ R` and `closedBall z (4r) ⊆ V` for `z ∈ R`, then
`LocalGood (μ.restrict V) c ε D f A tol R r ↔ GlobalGood η ε D f A tol R r`: the regularity events coincide and on
them the integrands coincide on `D`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4FO

open MatedCRTHarmonic

/-- The first visit of a reparametrized curve is the reparametrized first visit. -/
theorem hitTime_comp_orderIso' (c : ℝ → ℂ) (ψ : ℝ ≃o ℝ) (z : ℂ)
    (hne : (c ⁻¹' {z}).Nonempty) (hbdd : BddBelow (c ⁻¹' {z})) :
    GMS4b.hitTime (c ∘ ψ) z = ψ.symm (GMS4b.hitTime c z) := by
  have hset : {t : ℝ | (c ∘ ψ) t = z} = ψ.symm '' (c ⁻¹' {z}) := by
    ext t
    simp only [mem_ofPred_eq, Function.comp_apply, mem_image, mem_preimage, mem_singleton_iff]
    constructor
    · intro ht
      exact ⟨ψ t, ht, ψ.symm_apply_apply t⟩
    · rintro ⟨s, hs, rfl⟩
      rw [ψ.apply_symm_apply]
      exact hs
  rw [GMS4b.hitTime, hset, ← ψ.symm.monotone.map_csInf_of_continuousAt
    ψ.symm.continuous.continuousAt hne hbdd]
  rfl

/-- Disjoint open intervals are ordered. -/
theorem le_or_le_of_disjoint_Ioo {a b a' b' : ℝ} (hab : a < b) (hab' : a' < b')
    (h : Disjoint (Ioo a b) (Ioo a' b')) : b ≤ a' ∨ b' ≤ a := by
  rw [Ioo_disjoint_Ioo] at h
  rcases le_total a a' with h1 | h1
  · rw [max_eq_right h1] at h
    rcases le_total b b' with h2 | h2
    · rw [min_eq_left h2] at h; exact Or.inl h
    · rw [min_eq_right h2] at h; linarith
  · rw [max_eq_left h1] at h
    rcases le_total b b' with h2 | h2
    · rw [min_eq_left h2] at h; linarith
    · rw [min_eq_right h2] at h; exact Or.inr h

theorem disjoint_Ioo_of_le {a b a' b' : ℝ} (h : b ≤ a' ∨ b' ≤ a) :
    Disjoint (Ioo a b) (Ioo a' b') := by
  rcases h with h | h
  · exact Set.disjoint_left.2 fun x hx hx' => by linarith [hx.2, hx'.1]
  · exact Set.disjoint_left.2 fun x hx hx' => by linarith [hx.1, hx'.2]

namespace BridgeHyp

variable {μ : Measure ℂ} {c : ℝ → ℂ} {ψ : ℝ ≃o ℝ} {V : Set ℂ} (H : BridgeHyp μ c ψ V)
include H

variable (σ : ℝ)

/-- The admissible sets of `relTime` are nonempty and bounded below. -/
theorem relTime_set_spec (s : ℝ) :
    let A := {u | sweepStart (μ.restrict V) c σ ≤ u ∧
      min s (sweepTop (μ.restrict V) c σ) ≤ sweep (μ.restrict V) c σ u}
    A.Nonempty ∧ BddBelow A ∧ IsClosed A := by
  intro A
  obtain ⟨U₀, -, hU₀, hc⟩ := H.sweepTop_mem σ
  refine ⟨⟨max (sweepStart (μ.restrict V) c σ) U₀, le_max_left _ _, ?_⟩,
    ⟨sweepStart (μ.restrict V) c σ, fun u hu => hu.1⟩,
    (isClosed_le continuous_const continuous_id).inter
      (isClosed_le continuous_const (H.sweep_continuous σ))⟩
  rw [hc _ (le_max_right _ _), hU₀]
  exact min_le_right _ _

/-- `relTime` is monotone. -/
theorem relTime_mono : Monotone (relTime (μ.restrict V) c σ) := by
  intro s s' hss'
  obtain ⟨hne', -, -⟩ := H.relTime_set_spec σ s'
  obtain ⟨-, hbdd, -⟩ := H.relTime_set_spec σ s
  refine csInf_le_csInf hbdd hne' fun u hu => ⟨hu.1, le_trans ?_ hu.2⟩
  exact min_le_min_right _ hss'

/-- Inside the swept range, `relTime s` is the first time at which the swept mass equals `s`. -/
theorem relTime_spec (hσ : c σ ∈ V) {s : ℝ} (hb : sweepBot (μ.restrict V) c σ < s)
    (ht : s ≤ sweepTop (μ.restrict V) c σ) :
    sweep (μ.restrict V) c σ (relTime (μ.restrict V) c σ s) = s ∧
      ∀ v < relTime (μ.restrict V) c σ s, sweep (μ.restrict V) c σ v < s := by
  obtain ⟨hne, hbdd, hcl⟩ := H.relTime_set_spec σ s
  obtain ⟨hst, -⟩ := H.sweepStart_spec σ hσ
  have hmin : min s (sweepTop (μ.restrict V) c σ) = s := min_eq_left ht
  have hmem := hcl.csInf_mem hne hbdd
  have hrel : relTime (μ.restrict V) c σ s = sInf {u | sweepStart (μ.restrict V) c σ ≤ u ∧
      min s (sweepTop (μ.restrict V) c σ) ≤ sweep (μ.restrict V) c σ u} := rfl
  rw [← hrel] at hmem
  rw [hmin] at hmem
  have hlt : ∀ v < relTime (μ.restrict V) c σ s, sweep (μ.restrict V) c σ v < s := by
    intro v hv
    by_contra hcon
    push Not at hcon
    rcases lt_or_ge v (sweepStart (μ.restrict V) c σ) with hv0 | hv0
    · have := H.sweep_mono σ hv0.le
      rw [hst] at this
      linarith
    · have hvA : v ∈ {u | sweepStart (μ.restrict V) c σ ≤ u ∧
          min s (sweepTop (μ.restrict V) c σ) ≤ sweep (μ.restrict V) c σ u} := ⟨hv0, by rwa [hmin]⟩
      have := csInf_le hbdd hvA
      rw [← hrel] at this
      linarith
  refine ⟨le_antisymm ?_ hmem.2, hlt⟩
  by_contra hcon
  push Not at hcon
  have hstart : sweepStart (μ.restrict V) c σ ≤ relTime (μ.restrict V) c σ s := hmem.1
  have hcont : ContinuousOn (sweep (μ.restrict V) c σ)
      (Icc (sweepStart (μ.restrict V) c σ) (relTime (μ.restrict V) c σ s)) :=
    (H.sweep_continuous σ).continuousOn
  obtain ⟨v, hv, hvs⟩ := intermediate_value_Icc hstart hcont ⟨by rw [hst]; exact hb.le, hcon.le⟩
  rcases hv.2.lt_or_eq with hv2 | hv2
  · exact absurd hvs (hlt v hv2).ne
  · rw [hv2] at hvs; linarith

/-- If the local curve at `s` is in `V`, then `s` is strictly inside the swept range. -/
theorem mem_range_of_mem (hσ : c σ ∈ V) {s : ℝ} (hs : c (σ + relTime (μ.restrict V) c σ s) ∈ V) :
    sweepBot (μ.restrict V) c σ < s ∧ s < sweepTop (μ.restrict V) c σ := by
  constructor
  · by_contra h
    push Not at h
    rw [H.relTime_of_le_bot σ hσ h] at hs
    exact H.sweepStart_not_mem σ hσ hs
  · by_contra h
    push Not at h
    rw [H.relTime_of_top_le σ h] at hs
    exact (H.relTime_top_spec σ hσ).2 hs

/-! ### Local → global -/

/-- **A local segment inside `V` is a global segment of the same length.** -/
theorem psi_relTime_of_local (hσ : c σ ∈ V) {a b : ℝ} (hab : a ≤ b)
    (hV : ∀ s ∈ Icc a b, c (σ + relTime (μ.restrict V) c σ s) ∈ V) {s : ℝ} (hs : s ∈ Icc a b) :
    ψ.symm (σ + relTime (μ.restrict V) c σ s) =
      ψ.symm (σ + relTime (μ.restrict V) c σ a) + (s - a) := by
  have hra := H.mem_range_of_mem σ hσ (hV a ⟨le_rfl, hab⟩)
  have hrs := H.mem_range_of_mem σ hσ (hV s hs)
  obtain ⟨hSa, -⟩ := H.relTime_spec σ hσ hra.1 hra.2.le
  obtain ⟨hSs, -⟩ := H.relTime_spec σ hσ hrs.1 hrs.2.le
  have hmono : relTime (μ.restrict V) c σ a ≤ relTime (μ.restrict V) c σ s :=
    H.relTime_mono σ hs.1
  have hsub : c '' Icc (σ + relTime (μ.restrict V) c σ a) (σ + relTime (μ.restrict V) c σ s) ⊆ V := by
    rintro _ ⟨t, ht, rfl⟩
    by_contra hct
    have hct' : c (σ + (t - σ)) ∉ V := by rwa [add_sub_cancel]
    have hle1 : a ≤ sweep (μ.restrict V) c σ (t - σ) := by
      rw [← hSa]; exact H.sweep_mono σ (by linarith [ht.1])
    have hle2 : sweep (μ.restrict V) c σ (t - σ) ≤ s := by
      rw [← hSs]; exact H.sweep_mono σ (by linarith [ht.2])
    exact H.relTime_not_mem σ hσ hct' (hV _ ⟨hle1, hle2.trans hs.2⟩)
  have := H.sweep_sub_of_subset σ hmono hsub
  rw [hSa, hSs] at this
  linarith

/-! ### The window -/

/-- If the global window lies in `V`, the local curve is the global curve on the window. -/
theorem locCurve_eq_on_window {z : ℂ} (hz : z ∈ V) {ε : ℝ} (hε : 0 ≤ ε)
    (hglob : (c ∘ ψ) '' Icc (ψ.symm (GMS4b.hitTime c z) - ε) (ψ.symm (GMS4b.hitTime c z) + ε) ⊆ V)
    {s : ℝ} (hs : s ∈ Icc (-ε) ε) :
    locCurve (μ.restrict V) c z s = (c ∘ ψ) (ψ.symm (GMS4b.hitTime c z) + s) := by
  set σ := GMS4b.hitTime c z
  have hσ : c σ ∈ V := by rw [H.hitTime_mem z]; exact hz
  have hsub' : c '' Icc (σ + (ψ (ψ.symm σ - ε) - σ)) (σ + 0) ⊆ V := by
    rintro _ ⟨t, ht, rfl⟩
    have h1 : ψ.symm σ - ε ≤ ψ.symm t := ψ.le_symm_apply.2 (by linarith [ht.1])
    have h2 : ψ.symm t ≤ ψ.symm σ + ε := ψ.symm_apply_le.2 (by
      have h3 := ht.2
      rw [add_zero] at h3
      calc t ≤ σ := h3
        _ = ψ (ψ.symm σ) := (ψ.apply_symm_apply σ).symm
        _ ≤ ψ (ψ.symm σ + ε) := ψ.monotone (by linarith))
    have := hglob ⟨ψ.symm t, ⟨h1, h2⟩, rfl⟩
    simpa using this
  have hneg : ψ (ψ.symm σ - ε) - σ ≤ 0 := by
    have : ψ (ψ.symm σ - ε) ≤ ψ (ψ.symm σ) := ψ.monotone (by linarith)
    rw [ψ.apply_symm_apply] at this
    linarith
  have ha := H.sweep_sub_of_subset σ hneg hsub'
  rw [H.sweep_zero σ, add_zero, add_sub_cancel, ψ.symm_apply_apply] at ha
  have ha' : sweep (μ.restrict V) c σ (ψ (ψ.symm σ - ε) - σ) = -ε := by linarith
  have hloc := H.locCurve_eq_of_global (a' := ψ.symm σ - ε) (b' := ψ.symm σ + ε) hz (by linarith)
    hglob (s := s) (by rw [ha']; constructor <;> linarith [hs.1, hs.2])
  rw [hloc, ha']
  congr 1
  ring

/-- If the local window lies in `V`, so does the global window. -/
theorem globalWindow_subset_of_local {z : ℂ} (hz : z ∈ V) {ε : ℝ}
    (hloc : ∀ s ∈ Icc (-ε) ε, locCurve (μ.restrict V) c z s ∈ V) :
    (c ∘ ψ) '' Icc (ψ.symm (GMS4b.hitTime c z) - ε) (ψ.symm (GMS4b.hitTime c z) + ε) ⊆ V := by
  set σ := GMS4b.hitTime c z
  have hσ : c σ ∈ V := by rw [H.hitTime_mem z]; exact hz
  rintro _ ⟨x, hx, rfl⟩
  by_contra hcx
  have hcx' : c (σ + (ψ x - σ)) ∉ V := by rw [add_sub_cancel]; exact hcx
  have hb := H.abs_sweep_le σ (ψ x - σ)
  rw [add_sub_cancel, ψ.symm_apply_apply] at hb
  have hmem : sweep (μ.restrict V) c σ (ψ x - σ) ∈ Icc (-ε) ε := by
    rw [mem_Icc, ← abs_le]
    refine hb.trans ?_
    rw [abs_le]
    constructor <;> linarith [hx.1, hx.2]
  exact H.relTime_not_mem σ hσ hcx' (hloc _ hmem)

end BridgeHyp

end MatedCRTHarmonic.GMS4FO
