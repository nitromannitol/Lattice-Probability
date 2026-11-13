/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4FO.BridgeOut at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4FO.BridgeMain

/-!
# The bridge: outer degrees and the good events

Continuation of `GMS4FO/BridgeMain.lean`.

* `locDegOut_eq`: outer degree families correspond (as for the inner degree, `BridgeMain.locDegIn_eq`);
* `locU_eq_uStar`: `locU (μ.restrict V) c ε z = GMS4b.uStar ε (c ∘ ψ) z` when the global window and degree ball
  of `z` lie in `V` ([18] Lemma 4.3, deterministic content);
* `window_of_globalDiam`, `window_of_localDiam`: either window diameter bound `≤ r`, with
  `closedBall z (4r) ⊆ V`, puts the window and the degree ball inside `V`;
* **`localGood_iff_globalGood`**: for `D ⊆ R`, `0 ≤ r`, `closedBall z (4r) ⊆ V` (`z ∈ R`) and measurable `D`,
  `LocalGood (μ.restrict V) c ε D f A tol R r ↔ GlobalGood (c ∘ ψ) ε D f A tol R r`.
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

/-- The swept mass along a global segment inside `V` increases by its length. -/
theorem sweep_add_of_global' (σ : ℝ) {a' L : ℝ} (hL : 0 ≤ L) (hsub : (c ∘ ψ) '' Icc a' (a' + L) ⊆ V) :
    sweep (μ.restrict V) c σ (ψ (a' + L) - σ) = sweep (μ.restrict V) c σ (ψ a' - σ) + L := by
  have h := H.sweep_sub_of_subset σ (u := ψ a' - σ) (u' := ψ (a' + L) - σ)
    (by linarith [ψ.monotone (show a' ≤ a' + L by linarith)])
    (by rw [add_sub_cancel, add_sub_cancel, H.image_comp_Icc]; exact hsub)
  rw [add_sub_cancel, add_sub_cancel, ψ.symm_apply_apply, ψ.symm_apply_apply] at h
  linarith

section Degrees

variable {z : ℂ} (hz : z ∈ V) {ε : ℝ} (hε : 0 < ε)
  (hglob : (c ∘ ψ) '' Icc (ψ.symm (GMS4b.hitTime c z) - ε) (ψ.symm (GMS4b.hitTime c z) + ε) ⊆ V)
  (hball : GMS4b.locBall ε (c ∘ ψ) (ψ.symm (GMS4b.hitTime c z)) ⊆ V)
include hz hε hglob hball

theorem window_subset_ball :
    GMS4b.locWindow ε (c ∘ ψ) (ψ.symm (GMS4b.hitTime c z)) ⊆
      GMS4b.locBall ε (c ∘ ψ) (ψ.symm (GMS4b.hitTime c z)) :=
  GMS4b.locWindow_subset_locBall (H.cont.comp ψ.continuous) hε.le

/-- The closed images of an outer-degree interval lie in the degree ball. -/
theorem image_Icc_subset_ball_of_out {c' : ℝ → ℂ} {t₀ : ℝ} {a b : ℝ} (hab : a < b)
    (hint : c' '' Ioo a b ⊆ interior (GMS4b.locBall ε c' t₀))
    (hend : (c' a ∈ frontier (GMS4b.locBall ε c' t₀) ∧ c' b ∈ GMS4b.locWindow ε c' t₀) ∨
      (c' b ∈ frontier (GMS4b.locBall ε c' t₀) ∧ c' a ∈ GMS4b.locWindow ε c' t₀))
    (hwin : GMS4b.locWindow ε c' t₀ ⊆ GMS4b.locBall ε c' t₀) :
    c' '' Icc a b ⊆ GMS4b.locBall ε c' t₀ := by
  have hcl : IsClosed (GMS4b.locBall ε c' t₀) := isClosed_closedBall
  have hfr : frontier (GMS4b.locBall ε c' t₀) ⊆ GMS4b.locBall ε c' t₀ := hcl.frontier_subset
  rintro _ ⟨s, hs, rfl⟩
  rcases hs.1.lt_or_eq with h1 | h1
  · rcases hs.2.lt_or_eq with h2 | h2
    · exact interior_subset (hint ⟨s, ⟨h1, h2⟩, rfl⟩)
    · rw [h2]
      rcases hend with h | h
      · exact hwin h.2
      · exact hfr h.1
  · rw [← h1]
    rcases hend with h | h
    · exact hfr h.1
    · exact hwin h.2

theorem locDegOut_le :
    GMS4b.locDegOut ε (locCurve (μ.restrict V) c z) 0 ≤
      GMS4b.locDegOut ε (c ∘ ψ) (ψ.symm (GMS4b.hitTime c z)) := by
  set σ := GMS4b.hitTime c z
  have hσ : c σ ∈ V := by rw [H.hitTime_mem z]; exact hz
  refine GMS4b.locDegOut_le fun N a b hab => ?_
  have hBeq := H.locBall_eq hz hε.le hglob
  have hWeq := H.locWindow_eq hz hε.le hglob
  have hBV : GMS4b.locBall ε (locCurve (μ.restrict V) c z) 0 ⊆ V := by rw [hBeq]; exact hball
  have hwin : GMS4b.locWindow ε (locCurve (μ.restrict V) c z) 0 ⊆
      GMS4b.locBall ε (locCurve (μ.restrict V) c z) 0 := by
    rw [hBeq, hWeq]; exact H.window_subset_ball hz hε hglob hball
  set a' : Fin N → ℝ := fun i => ψ.symm (σ + relTime (μ.restrict V) c σ (a i))
  set b' : Fin N → ℝ := fun i => a' i + (b i - a i)
  have hsub : ∀ i, locCurve (μ.restrict V) c z '' Icc (a i) (b i) ⊆ V := fun i =>
    (H.image_Icc_subset_ball_of_out hz hε hglob hball (hab.1 i) (hab.2.2 i).1 (hab.2.2 i).2
      hwin).trans hBV
  have heq : ∀ i, ∀ s ∈ Icc (a i) (b i), locCurve (μ.restrict V) c z s = (c ∘ ψ) (a' i + (s - a i)) :=
    fun i => H.locCurve_image_of_local hz hε hglob hball (hab.1 i).le (hsub i)
  have hend : ∀ i, b' i = ψ.symm (σ + relTime (μ.restrict V) c σ (b i)) := by
    intro i
    have hV' : ∀ s ∈ Icc (a i) (b i), c (σ + relTime (μ.restrict V) c σ s) ∈ V :=
      fun s hs => hsub i ⟨s, hs, rfl⟩
    rw [H.psi_relTime_of_local σ hσ (hab.1 i).le hV' ⟨(hab.1 i).le, le_rfl⟩]
  have hIoo : ∀ i, locCurve (μ.restrict V) c z '' Ioo (a i) (b i) = (c ∘ ψ) '' Ioo (a' i) (b' i) := by
    intro i
    ext w
    constructor
    · rintro ⟨s, hs, rfl⟩
      rw [heq i s ⟨hs.1.le, hs.2.le⟩]
      exact ⟨_, ⟨by linarith [hs.1], by simp only [b']; linarith [hs.2]⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      have hx2 : x < a' i + (b i - a i) := hx.2
      refine ⟨a i + (x - a' i), ⟨by linarith [hx.1], by linarith⟩, ?_⟩
      rw [heq i _ ⟨by linarith [hx.1], by linarith⟩]
      congr 1; ring
  have ha_eq : ∀ i, locCurve (μ.restrict V) c z (a i) = (c ∘ ψ) (a' i) := by
    intro i
    rw [heq i (a i) ⟨le_rfl, (hab.1 i).le⟩, sub_self, add_zero]
  have hb_eq : ∀ i, locCurve (μ.restrict V) c z (b i) = (c ∘ ψ) (b' i) := by
    intro i
    rw [heq i (b i) ⟨(hab.1 i).le, le_rfl⟩]
  have hfam : GMS4b.IsDegOutFamily ε (c ∘ ψ) (ψ.symm σ) a' b' := by
    refine ⟨fun i => by simp only [b']; linarith [hab.1 i], fun i j hij => ?_, fun i => ?_⟩
    · have hd := hab.2.1 i j hij
      rcases le_or_le_of_disjoint_Ioo (hab.1 i) (hab.1 j) hd with h | h
      · refine disjoint_Ioo_of_le (Or.inl ?_)
        rw [hend i]
        exact ψ.symm.monotone (by linarith [H.relTime_mono σ h])
      · refine disjoint_Ioo_of_le (Or.inr ?_)
        rw [hend j]
        exact ψ.symm.monotone (by linarith [H.relTime_mono σ h])
    · have h := hab.2.2 i
      rw [hIoo i, hBeq, hWeq, ha_eq i, hb_eq i] at h
      exact h
  exact GMS4b.le_locDegOut hfam

theorem le_locDegOut :
    GMS4b.locDegOut ε (c ∘ ψ) (ψ.symm (GMS4b.hitTime c z)) ≤
      GMS4b.locDegOut ε (locCurve (μ.restrict V) c z) 0 := by
  set σ := GMS4b.hitTime c z
  refine GMS4b.locDegOut_le fun N a' b' hab' => ?_
  have hBeq := H.locBall_eq hz hε.le hglob
  have hWeq := H.locWindow_eq hz hε.le hglob
  set a : Fin N → ℝ := fun i => sweep (μ.restrict V) c σ (ψ (a' i) - σ)
  set b : Fin N → ℝ := fun i => a i + (b' i - a' i)
  have hsub : ∀ i, (c ∘ ψ) '' Icc (a' i) (a' i + (b' i - a' i)) ⊆ V := by
    intro i
    rw [show a' i + (b' i - a' i) = b' i by ring]
    exact (H.image_Icc_subset_ball_of_out hz hε hglob hball (hab'.1 i) (hab'.2.2 i).1
      (hab'.2.2 i).2 (H.window_subset_ball hz hε hglob hball)).trans hball
  have heq : ∀ i, ∀ s ∈ Icc (a i) (b i), locCurve (μ.restrict V) c z s = (c ∘ ψ) (a' i + (s - a i)) :=
    fun i s hs => H.locCurve_eq_of_global hz (by linarith [hab'.1 i]) (hsub i)
      (by simp only [a, b] at hs ⊢; constructor <;> linarith [hs.1, hs.2])
  have hbsweep : ∀ i, b i = sweep (μ.restrict V) c σ (ψ (b' i) - σ) := by
    intro i
    have := H.sweep_add_of_global' σ (by linarith [hab'.1 i]) (hsub i)
    rw [show a' i + (b' i - a' i) = b' i by ring] at this
    simp only [b, a]
    rw [this]
  have hIoo : ∀ i, locCurve (μ.restrict V) c z '' Ioo (a i) (b i) = (c ∘ ψ) '' Ioo (a' i) (b' i) := by
    intro i
    ext w
    constructor
    · rintro ⟨s, hs, rfl⟩
      rw [heq i s ⟨hs.1.le, hs.2.le⟩]
      have hs2 : s < a i + (b' i - a' i) := hs.2
      exact ⟨_, ⟨by linarith [hs.1], by linarith⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨a i + (x - a' i), ⟨by linarith [hx.1], by simp only [b]; linarith [hx.2]⟩, ?_⟩
      rw [heq i _ ⟨by linarith [hx.1], by simp only [b]; linarith [hx.2]⟩]
      congr 1; ring
  have ha_eq : ∀ i, locCurve (μ.restrict V) c z (a i) = (c ∘ ψ) (a' i) := by
    intro i
    rw [heq i (a i) ⟨le_rfl, by simp only [b]; linarith [hab'.1 i]⟩, sub_self, add_zero]
  have hb_eq : ∀ i, locCurve (μ.restrict V) c z (b i) = (c ∘ ψ) (b' i) := by
    intro i
    rw [heq i (b i) ⟨by simp only [b]; linarith [hab'.1 i], le_rfl⟩]
    congr 1; simp only [b]; ring
  have hfam : GMS4b.IsDegOutFamily ε (locCurve (μ.restrict V) c z) 0 a b := by
    refine ⟨fun i => by simp only [b]; linarith [hab'.1 i], fun i j hij => ?_, fun i => ?_⟩
    · have hd := hab'.2.1 i j hij
      rcases le_or_le_of_disjoint_Ioo (hab'.1 i) (hab'.1 j) hd with h | h
      · refine disjoint_Ioo_of_le (Or.inl ?_)
        rw [hbsweep i]
        exact H.sweep_mono σ (by linarith [ψ.monotone h])
      · refine disjoint_Ioo_of_le (Or.inr ?_)
        rw [hbsweep j]
        exact H.sweep_mono σ (by linarith [ψ.monotone h])
    · rw [hIoo i, hBeq, hWeq, ha_eq i, hb_eq i]
      exact hab'.2.2 i
  exact GMS4b.le_locDegOut hfam

theorem locDegOut_eq :
    GMS4b.locDegOut ε (locCurve (μ.restrict V) c z) 0 =
      GMS4b.locDegOut ε (c ∘ ψ) (ψ.symm (GMS4b.hitTime c z)) :=
  le_antisymm (H.locDegOut_le hz hε hglob hball) (H.le_locDegOut hz hε hglob hball)

/-- **[18] Lemma 4.3, deterministic content.** -/
theorem locU_eq_uStar : locU (μ.restrict V) c ε z = GMS4b.uStar ε (c ∘ ψ) z := by
  rw [locU, GMS4b.uStar, hitTime_comp_orderIso' c ψ z (H.visits z).1 (H.visits z).2, GMS4b.locUStar,
    GMS4b.locUStar, H.locDA_eq hz hε.le hglob, H.locDegIn_eq hz hε hglob hball,
    H.locDegOut_eq hz hε hglob hball]

end Degrees

theorem locWinDiam_eq {z : ℂ} (hz : z ∈ V) {ε : ℝ} (hε : 0 ≤ ε)
    (hglob : (c ∘ ψ) '' Icc (ψ.symm (GMS4b.hitTime c z) - ε) (ψ.symm (GMS4b.hitTime c z) + ε) ⊆ V) :
    locWinDiam (μ.restrict V) c ε z = GMS4b.windowDiam ε (c ∘ ψ) z := by
  rw [locWinDiam, GMS4b.windowDiam, hitTime_comp_orderIso' c ψ z (H.visits z).1 (H.visits z).2,
    H.locWindow_eq hz hε hglob]

/-! ### The regularity events -/

/-- A global window diameter bound puts the window and the degree ball inside `V`. -/
theorem window_of_globalDiam {z : ℂ} {ε r : ℝ} (hε : 0 ≤ ε) (hr : closedBall z (4 * r) ⊆ V)
    (hdiam : GMS4b.windowDiam ε (c ∘ ψ) z ≤ r) :
    (c ∘ ψ) '' Icc (ψ.symm (GMS4b.hitTime c z) - ε) (ψ.symm (GMS4b.hitTime c z) + ε) ⊆ V ∧
      GMS4b.locBall ε (c ∘ ψ) (ψ.symm (GMS4b.hitTime c z)) ⊆ V := by
  set τ := ψ.symm (GMS4b.hitTime c z)
  have hτ : GMS4b.hitTime (c ∘ ψ) z = τ := hitTime_comp_orderIso' c ψ z (H.visits z).1 (H.visits z).2
  rw [GMS4b.windowDiam, hτ] at hdiam
  have hcz : (c ∘ ψ) τ = z := by simp [τ, H.hitTime_mem z]
  have hbdd : Bornology.IsBounded (GMS4b.locWindow ε (c ∘ ψ) τ) :=
    (isCompact_Icc.image (H.cont.comp ψ.continuous)).isBounded
  have hzW : z ∈ GMS4b.locWindow ε (c ∘ ψ) τ := ⟨τ, ⟨by linarith, by linarith⟩, hcz⟩
  have hr0 : 0 ≤ r := diam_nonneg.trans hdiam
  have hW : GMS4b.locWindow ε (c ∘ ψ) τ ⊆ closedBall z (4 * r) := by
    intro w hw
    rw [mem_closedBall]
    calc dist w z ≤ diam (GMS4b.locWindow ε (c ∘ ψ) τ) := dist_le_diam_of_mem hbdd hw hzW
      _ ≤ r := hdiam
      _ ≤ 4 * r := by linarith
  refine ⟨hW.trans hr, ?_⟩
  refine (closedBall_subset_closedBall' ?_).trans hr
  rw [hcz, dist_self]
  linarith

/-- A local window diameter bound puts the global window and the degree ball inside `V`. -/
theorem window_of_localDiam {z : ℂ} (hz : z ∈ V) {ε r : ℝ} (hε : 0 ≤ ε)
    (hr : closedBall z (4 * r) ⊆ V) (hdiam : locWinDiam (μ.restrict V) c ε z ≤ r) :
    (c ∘ ψ) '' Icc (ψ.symm (GMS4b.hitTime c z) - ε) (ψ.symm (GMS4b.hitTime c z) + ε) ⊆ V ∧
      GMS4b.locBall ε (c ∘ ψ) (ψ.symm (GMS4b.hitTime c z)) ⊆ V := by
  have hbdd := H.isBounded_locWindow z ε
  have hzW : z ∈ GMS4b.locWindow ε (locCurve (μ.restrict V) c z) 0 :=
    ⟨0, ⟨by linarith, by linarith⟩, H.locCurve_zero hz⟩
  have hr0 : 0 ≤ r := diam_nonneg.trans hdiam
  have hloc : ∀ s ∈ Icc (-ε) ε, locCurve (μ.restrict V) c z s ∈ V := by
    intro s hs
    apply hr
    rw [mem_closedBall]
    have hw : locCurve (μ.restrict V) c z s ∈ GMS4b.locWindow ε (locCurve (μ.restrict V) c z) 0 :=
      ⟨s, ⟨by linarith [hs.1], by linarith [hs.2]⟩, rfl⟩
    calc dist (locCurve (μ.restrict V) c z s) z ≤ diam (GMS4b.locWindow ε (locCurve (μ.restrict V) c z) 0) :=
          dist_le_diam_of_mem hbdd hw hzW
      _ ≤ r := hdiam
      _ ≤ 4 * r := by linarith
  have hglob := H.globalWindow_subset_of_local hz hloc
  refine H.window_of_globalDiam hε hr ?_
  rw [← H.locWinDiam_eq hz hε hglob]
  exact hdiam

/-- **The bridge.** The localized good event of `(μ|_V, c)` is the geometric good event of `η = c ∘ ψ`. -/
theorem localGood_iff_globalGood {ε : ℝ} (hε : 0 < ε) {D R : Set ℂ} {f : ℂ → ℝ} {A tol r : ℝ}
    (hr : 0 ≤ r) (hDR : D ⊆ R) (hRV : ∀ z ∈ R, closedBall z (4 * r) ⊆ V) (hD : MeasurableSet D) :
    LocalGood (μ.restrict V) c ε D f A tol R r ↔ GlobalGood (c ∘ ψ) ε D f A tol R r := by
  have hzV : ∀ z ∈ R, z ∈ V := fun z hz => hRV z hz (mem_closedBall_self (by linarith))
  have key : ∀ z ∈ R,
      (locWinDiam (μ.restrict V) c ε z ≤ r ∨ GMS4b.windowDiam ε (c ∘ ψ) z ≤ r) →
        locWinDiam (μ.restrict V) c ε z = GMS4b.windowDiam ε (c ∘ ψ) z ∧
          locU (μ.restrict V) c ε z = GMS4b.uStar ε (c ∘ ψ) z := by
    intro z hz hreg
    have hw : (c ∘ ψ) '' Icc (ψ.symm (GMS4b.hitTime c z) - ε) (ψ.symm (GMS4b.hitTime c z) + ε) ⊆ V ∧
        GMS4b.locBall ε (c ∘ ψ) (ψ.symm (GMS4b.hitTime c z)) ⊆ V := by
      rcases hreg with h | h
      · exact H.window_of_localDiam (hzV z hz) hε.le (hRV z hz) h
      · exact H.window_of_globalDiam hε.le (hRV z hz) h
    exact ⟨H.locWinDiam_eq (hzV z hz) hε.le hw.1, H.locU_eq_uStar (hzV z hz) hε hw.1 hw.2⟩
  have hint : ∀ hreg : ∀ z ∈ R, locWinDiam (μ.restrict V) c ε z ≤ r ∨
      GMS4b.windowDiam ε (c ∘ ψ) z ≤ r,
      (∫⁻ z in D, ENNReal.ofReal (f z) * locU (μ.restrict V) c ε z) =
        ∫⁻ z in D, ENNReal.ofReal (f z) * GMS4b.uStar ε (c ∘ ψ) z := by
    intro hreg
    refine setLIntegral_congr_fun hD fun z hz => ?_
    rw [(key z (hDR hz) (hreg z (hDR hz))).2]
  constructor
  · rintro ⟨hreg, hle⟩
    have hreg' : ∀ z ∈ R, GMS4b.windowDiam ε (c ∘ ψ) z ≤ r := fun z hz => by
      rw [← (key z hz (Or.inl (hreg z hz))).1]; exact hreg z hz
    refine ⟨hreg', ?_⟩
    rw [← hint fun z hz => Or.inl (hreg z hz)]
    exact hle
  · rintro ⟨hreg, hle⟩
    have hreg' : ∀ z ∈ R, locWinDiam (μ.restrict V) c ε z ≤ r := fun z hz => by
      rw [(key z hz (Or.inr (hreg z hz))).1]; exact hreg z hz
    refine ⟨hreg', ?_⟩
    rw [hint fun z hz => Or.inr (hreg z hz)]
    exact hle

end BridgeHyp

end MatedCRTHarmonic.GMS4FO
