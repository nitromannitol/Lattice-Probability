/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4FO.BridgeMain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4FO.BridgeFamily

/-!
# The bridge, main theorem

Under `BridgeHyp μ c ψ V` (`η = c ∘ ψ` parametrized by `μ`-area, `V` open bounded), at a point `z ∈ V` whose
global window `η([τ_z − ε, τ_z + ε])` and degree ball `B̄^ε_z` lie in `V`:

* `locWindow_eq`, `locBall_eq`, `locDA_eq`: the local window, ball and `DA^ε` are the global ones;
* `locDegIn_eq`, `locDegOut_eq`: each local inner (outer) degree family is a global family of the same images and
  conversely (cells inside `V` are translated in time, the order of disjoint cells is preserved);
* `locU_eq_uStar`: `locU (μ.restrict V) c ε z = GMS4b.uStar ε η z` ([18] Lemma 4.3, deterministic content).

`localGood_iff_globalGood`: for `D ⊆ R`, `0 ≤ r` and `closedBall z (4r) ⊆ V` (`z ∈ R`), the localized good event of
`(μ|_V, c)` is the geometric good event of `η` (regularity events coincide; on them the integrands coincide on `D`).
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

theorem image_comp_Icc (x y : ℝ) : c '' Icc (ψ x) (ψ y) = (c ∘ ψ) '' Icc x y := by
  rw [image_comp, OrderIso.image_Icc]

/-- `relTime 0 = 0` at a root spent in `V`. -/
theorem relTime_zero {σ : ℝ} (hσ : c σ ∈ V) : relTime (μ.restrict V) c σ 0 = 0 := by
  apply H.relTime_eq σ hσ (H.sweepBot_lt_zero σ hσ) (H.zero_lt_sweepTop σ hσ).le (H.sweep_zero σ)
  intro v hv
  obtain ⟨δ, hδ, hδV⟩ := H.exists_ball_subset hσ
  set w := max v (-(δ / 2))
  have hw1 : v ≤ w := le_max_left _ _
  have hw2 : -(δ / 2) ≤ w := le_max_right _ _
  have hw3 : w < 0 := max_lt hv (by linarith)
  have hvV : c (σ + w / 2) ∈ V := hδV _ (by rw [abs_lt]; constructor <;> linarith)
  have := H.sweep_lt_of_mem σ (u := v) (u' := 0) (v := w / 2) ⟨by linarith, by linarith⟩ hvV
  rwa [H.sweep_zero σ] at this

theorem locCurve_zero {z : ℂ} (hz : z ∈ V) : locCurve (μ.restrict V) c z 0 = z := by
  have hσ : c (GMS4b.hitTime c z) ∈ V := by rw [H.hitTime_mem z]; exact hz
  rw [locCurve, H.relTime_zero hσ, add_zero, H.hitTime_mem z]

/-- The local window is bounded (the local curve is `c` at monotone times). -/
theorem isBounded_locWindow (z : ℂ) (ε : ℝ) :
    Bornology.IsBounded (GMS4b.locWindow ε (locCurve (μ.restrict V) c z) 0) := by
  set σ := GMS4b.hitTime c z
  refine ((isCompact_Icc (a := σ + relTime (μ.restrict V) c σ (0 - ε))
    (b := σ + relTime (μ.restrict V) c σ (0 + ε))).image H.cont).isBounded.subset ?_
  rintro _ ⟨s, hs, rfl⟩
  exact ⟨_, ⟨by linarith [H.relTime_mono σ hs.1], by linarith [H.relTime_mono σ hs.2]⟩, rfl⟩

/-! ### Equality of the window quantities -/

section Window

variable {z : ℂ} (hz : z ∈ V) {ε : ℝ} (hε : 0 ≤ ε)
  (hglob : (c ∘ ψ) '' Icc (ψ.symm (GMS4b.hitTime c z) - ε) (ψ.symm (GMS4b.hitTime c z) + ε) ⊆ V)
include hz hε hglob

theorem locWindow_eq :
    GMS4b.locWindow ε (locCurve (μ.restrict V) c z) 0 =
      GMS4b.locWindow ε (c ∘ ψ) (ψ.symm (GMS4b.hitTime c z)) := by
  unfold GMS4b.locWindow
  ext w
  constructor
  · rintro ⟨s, hs, rfl⟩
    have hs' : s ∈ Icc (-ε) ε := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    rw [H.locCurve_eq_on_window hz hε hglob hs']
    exact ⟨_, ⟨by linarith [hs'.1], by linarith [hs'.2]⟩, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    have hs' : x - ψ.symm (GMS4b.hitTime c z) ∈ Icc (-ε) ε := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    refine ⟨x - ψ.symm (GMS4b.hitTime c z), ⟨by linarith [hs'.1], by linarith [hs'.2]⟩, ?_⟩
    rw [H.locCurve_eq_on_window hz hε hglob hs']
    congr 1
    ring

theorem locCurve_zero_eq :
    locCurve (μ.restrict V) c z 0 = (c ∘ ψ) (ψ.symm (GMS4b.hitTime c z)) := by
  rw [H.locCurve_eq_on_window hz hε hglob ⟨by linarith, hε⟩, add_zero]

theorem locBall_eq :
    GMS4b.locBall ε (locCurve (μ.restrict V) c z) 0 =
      GMS4b.locBall ε (c ∘ ψ) (ψ.symm (GMS4b.hitTime c z)) := by
  unfold GMS4b.locBall
  rw [H.locWindow_eq hz hε hglob, H.locCurve_zero_eq hz hε hglob]

theorem locDA_eq :
    GMS4b.locDA ε (locCurve (μ.restrict V) c z) 0 =
      GMS4b.locDA ε (c ∘ ψ) (ψ.symm (GMS4b.hitTime c z)) := by
  set τ := ψ.symm (GMS4b.hitTime c z)
  have hseg : ∀ s ∈ Icc (0 : ℝ) (0 + ε),
      GMS4b.segRatio (locCurve (μ.restrict V) c z) (s - ε) s =
        GMS4b.segRatio (c ∘ ψ) (τ + s - ε) (τ + s) := by
    intro s hs
    have himg : locCurve (μ.restrict V) c z '' Icc (s - ε) s = (c ∘ ψ) '' Icc (τ + s - ε) (τ + s) := by
      ext w
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [H.locCurve_eq_on_window hz hε hglob ⟨by linarith [hx.1, hs.1], by linarith [hx.2, hs.2]⟩]
        exact ⟨_, ⟨by linarith [hx.1], by linarith [hx.2]⟩, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        refine ⟨x - τ, ⟨by linarith [hx.1], by linarith [hx.2]⟩, ?_⟩
        rw [H.locCurve_eq_on_window hz hε hglob ⟨by linarith [hx.1, hs.1], by linarith [hx.2, hs.2]⟩]
        congr 1; ring
    rw [GMS4b.segRatio, GMS4b.segRatio, himg]
  unfold GMS4b.locDA
  apply le_antisymm
  · refine iSup₂_le fun s hs => ?_
    rw [hseg s hs]
    exact le_iSup₂_of_le (τ + s) ⟨by linarith [hs.1], by linarith [hs.2]⟩ le_rfl
  · refine iSup₂_le fun s hs => ?_
    have hs' : s - τ ∈ Icc (0 : ℝ) (0 + ε) := ⟨by linarith [hs.1], by linarith [hs.2]⟩
    have := hseg (s - τ) hs'
    rw [show τ + (s - τ) = s by ring] at this
    rw [← this]
    exact le_iSup₂_of_le (s - τ) hs' le_rfl

end Window

/-! ### Degree families -/

section Degrees

variable {z : ℂ} (hz : z ∈ V) {ε : ℝ} (hε : 0 < ε)
  (hglob : (c ∘ ψ) '' Icc (ψ.symm (GMS4b.hitTime c z) - ε) (ψ.symm (GMS4b.hitTime c z) + ε) ⊆ V)
  (hball : GMS4b.locBall ε (c ∘ ψ) (ψ.symm (GMS4b.hitTime c z)) ⊆ V)
include hz hε hglob hball

/-- A local segment whose image is in `V` is the global segment of the same length. -/
theorem locCurve_image_of_local {a b : ℝ} (hab : a ≤ b)
    (hV : locCurve (μ.restrict V) c z '' Icc a b ⊆ V) :
    ∀ s ∈ Icc a b, locCurve (μ.restrict V) c z s = (c ∘ ψ)
      (ψ.symm (GMS4b.hitTime c z + relTime (μ.restrict V) c (GMS4b.hitTime c z) a) + (s - a)) := by
  set σ := GMS4b.hitTime c z
  have hσ : c σ ∈ V := by rw [H.hitTime_mem z]; exact hz
  have hV' : ∀ s ∈ Icc a b, c (σ + relTime (μ.restrict V) c σ s) ∈ V :=
    fun s hs => hV ⟨s, hs, rfl⟩
  intro s hs
  rw [← H.psi_relTime_of_local σ hσ hab hV' hs]
  simp [locCurve, σ]

theorem sweep_add_of_global {a' : ℝ} (hsub : (c ∘ ψ) '' Icc a' (a' + ε) ⊆ V) :
    sweep (μ.restrict V) c (GMS4b.hitTime c z) (ψ (a' + ε) - GMS4b.hitTime c z) =
      sweep (μ.restrict V) c (GMS4b.hitTime c z) (ψ a' - GMS4b.hitTime c z) + ε := by
  have h := H.sweep_sub_of_subset (GMS4b.hitTime c z)
    (u := ψ a' - GMS4b.hitTime c z) (u' := ψ (a' + ε) - GMS4b.hitTime c z)
    (by linarith [ψ.monotone (show a' ≤ a' + ε by linarith)])
    (by rw [add_sub_cancel, add_sub_cancel, H.image_comp_Icc]; exact hsub)
  rw [add_sub_cancel, add_sub_cancel, ψ.symm_apply_apply, ψ.symm_apply_apply] at h
  linarith

theorem locDegIn_le :
    GMS4b.locDegIn ε (locCurve (μ.restrict V) c z) 0 ≤
      GMS4b.locDegIn ε (c ∘ ψ) (ψ.symm (GMS4b.hitTime c z)) := by
  set σ := GMS4b.hitTime c z
  have hσ : c σ ∈ V := by rw [H.hitTime_mem z]; exact hz
  refine GMS4b.locDegIn_le fun N a ha => ?_
  have hBV : GMS4b.locBall ε (locCurve (μ.restrict V) c z) 0 ⊆ V := by
    rw [H.locBall_eq hz hε.le hglob]; exact hball
  set a' : Fin N → ℝ := fun i => ψ.symm (σ + relTime (μ.restrict V) c σ (a i))
  have himg : ∀ i, locCurve (μ.restrict V) c z '' Icc (a i) (a i + ε) =
      (c ∘ ψ) '' Icc (a' i) (a' i + ε) := by
    intro i
    have hsub := ((ha.2 i).1).trans hBV
    have heq := H.locCurve_image_of_local hz hε hglob hball (show a i ≤ a i + ε by linarith) hsub
    ext w
    constructor
    · rintro ⟨s, hs, rfl⟩
      rw [heq s hs]
      exact ⟨_, ⟨by linarith [hs.1], by linarith [hs.2]⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨a i + (x - a' i), ⟨by linarith [hx.1], by linarith [hx.2]⟩, ?_⟩
      rw [heq _ ⟨by linarith [hx.1], by linarith [hx.2]⟩]
      congr 1; simp only [a']; ring
  have hend : ∀ i, a' i + ε = ψ.symm (σ + relTime (μ.restrict V) c σ (a i + ε)) := by
    intro i
    have hsub := ((ha.2 i).1).trans hBV
    have hV' : ∀ s ∈ Icc (a i) (a i + ε), c (σ + relTime (μ.restrict V) c σ s) ∈ V :=
      fun s hs => hsub ⟨s, hs, rfl⟩
    rw [H.psi_relTime_of_local σ hσ (by linarith) hV' ⟨by linarith, le_rfl⟩]
    ring
  have hfam : GMS4b.IsDegInFamily ε (c ∘ ψ) (ψ.symm σ) a' := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have hd := ha.1 i j hij
      rcases le_or_le_of_disjoint_Ioo (by linarith) (by linarith) hd with h | h
      · refine disjoint_Ioo_of_le (Or.inl ?_)
        rw [hend i]
        exact ψ.symm.monotone (by linarith [H.relTime_mono σ h])
      · refine disjoint_Ioo_of_le (Or.inr ?_)
        rw [hend j]
        exact ψ.symm.monotone (by linarith [H.relTime_mono σ h])
    · rw [← himg i, ← H.locBall_eq hz hε.le hglob, ← H.locWindow_eq hz hε.le hglob]
      exact ha.2 i
  exact GMS4b.le_locDegIn hfam

theorem le_locDegIn :
    GMS4b.locDegIn ε (c ∘ ψ) (ψ.symm (GMS4b.hitTime c z)) ≤
      GMS4b.locDegIn ε (locCurve (μ.restrict V) c z) 0 := by
  set σ := GMS4b.hitTime c z
  refine GMS4b.locDegIn_le fun N a' ha' => ?_
  set a : Fin N → ℝ := fun i => sweep (μ.restrict V) c σ (ψ (a' i) - σ)
  have hsub : ∀ i, (c ∘ ψ) '' Icc (a' i) (a' i + ε) ⊆ V := fun i => ((ha'.2 i).1).trans hball
  have himg : ∀ i, locCurve (μ.restrict V) c z '' Icc (a i) (a i + ε) =
      (c ∘ ψ) '' Icc (a' i) (a' i + ε) := by
    intro i
    have heq : ∀ s ∈ Icc (a i) (a i + ε), locCurve (μ.restrict V) c z s =
        (c ∘ ψ) (a' i + (s - a i)) := fun s hs =>
      H.locCurve_eq_of_global hz (show a' i ≤ a' i + ε by linarith) (hsub i)
        (by simp only [a] at hs ⊢; constructor <;> linarith [hs.1, hs.2])
    ext w
    constructor
    · rintro ⟨s, hs, rfl⟩
      rw [heq s hs]
      exact ⟨_, ⟨by linarith [hs.1], by linarith [hs.2]⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨a i + (x - a' i), ⟨by linarith [hx.1], by linarith [hx.2]⟩, ?_⟩
      rw [heq _ ⟨by linarith [hx.1], by linarith [hx.2]⟩]
      congr 1; ring
  have hfam : GMS4b.IsDegInFamily ε (locCurve (μ.restrict V) c z) 0 a := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · have hd := ha'.1 i j hij
      rcases le_or_le_of_disjoint_Ioo (by linarith) (by linarith) hd with h | h
      · refine disjoint_Ioo_of_le (Or.inl ?_)
        simp only [a]
        rw [← H.sweep_add_of_global hz hε hglob hball (hsub i)]
        exact H.sweep_mono σ (by linarith [ψ.monotone h])
      · refine disjoint_Ioo_of_le (Or.inr ?_)
        simp only [a]
        rw [← H.sweep_add_of_global hz hε hglob hball (hsub j)]
        exact H.sweep_mono σ (by linarith [ψ.monotone h])
    · rw [himg i, H.locBall_eq hz hε.le hglob, H.locWindow_eq hz hε.le hglob]
      exact ha'.2 i
  exact GMS4b.le_locDegIn hfam

theorem locDegIn_eq :
    GMS4b.locDegIn ε (locCurve (μ.restrict V) c z) 0 =
      GMS4b.locDegIn ε (c ∘ ψ) (ψ.symm (GMS4b.hitTime c z)) :=
  le_antisymm (H.locDegIn_le hz hε hglob hball) (H.le_locDegIn hz hε hglob hball)

end Degrees

end BridgeHyp

end MatedCRTHarmonic.GMS4FO
