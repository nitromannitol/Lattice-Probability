import Mathlib
import LatticeProb.Prob.UpcrossMeasurable
import LatticeProb.Prob.UpcrossIntervals

/-!
# Pathwise behaviour of the first up-crossing piece under stopping and time reversal

For a continuous path `w` and a level `c > 0` write `Θ_t(w)` for "exactly one up-crossing interval
from `0` to `c` ends in `[0, t]`", i.e. `d₁ w ≤ t < d₂ w`.

* `LatticeProb.theta_stop`: `Θ_t` only depends on `w` on `[0, t]`;
* `LatticeProb.theta_revStop`: `Θ_t` is invariant under reversal at `t` and reflection at `c`;
* `LatticeProb.upcrossRev c p`: the reversal `s ↦ c - p (T - s)` of an up-crossing piece `p`, with
  `T` its first hitting time of `c`; for the first up-crossing piece it is the reversal over the
  duration `d₁ - g₁` (`upcrossRev_firstUpcrossPiece`);
* `LatticeProb.firstUpcrossPiece_revStop`: on `Θ_t`, the first up-crossing piece of the reversed
  path is the reversed first piece;
* `LatticeProb.firstUpcrossPiece_stop`: on `Θ_t`, stopping at `t` keeps the first piece.
-/

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

section Pathwise

variable {w : ℝ≥0 → ℝ} {c : ℝ}

lemma continuous_revStop (hw : Continuous w) (t : ℝ≥0) : Continuous (revStop c t w) :=
  continuous_const.sub (hw.comp (continuous_const.sub (continuous_id.min continuous_const)))

lemma continuous_stop (hw : Continuous w) (t : ℝ≥0) : Continuous fun s => w (min s t) :=
  hw.comp (continuous_id.min continuous_const)

/-- `Θ_t` only depends on `w` on `[0, t]`. -/
theorem theta_stop (hw : Continuous w) (hc : 0 < c) (t : ℝ≥0) :
    (upcrossEnd₁ c (fun s => w (min s t)) ≤ t ∧
        (t : ℝ≥0∞) < upcrossEnd₂ c (fun s => w (min s t))) ↔
      (upcrossEnd₁ c w ≤ t ∧ (t : ℝ≥0∞) < upcrossEnd₂ c w) := by
  rw [← existsUnique_upcross_iff (continuous_stop hw t) hc, ← existsUnique_upcross_iff hw hc]
  refine existsUnique_congr fun p => ?_
  constructor
  · rintro ⟨hI, hd⟩
    exact ⟨hI.congr fun s hs => by
      show w (min s t) = w s
      rw [min_eq_left (hs.trans hd)], hd⟩
  · rintro ⟨hI, hd⟩
    exact ⟨hI.congr fun s hs => by
      show w s = w (min s t)
      rw [min_eq_left (hs.trans hd)], hd⟩

/-- `Θ_t` is invariant under reversal at `t` and reflection at `c`. -/
theorem theta_revStop (hw : Continuous w) (hc : 0 < c) (t : ℝ≥0) :
    (upcrossEnd₁ c (revStop c t w) ≤ t ∧ (t : ℝ≥0∞) < upcrossEnd₂ c (revStop c t w)) ↔
      (upcrossEnd₁ c w ≤ t ∧ (t : ℝ≥0∞) < upcrossEnd₂ c w) := by
  rw [← existsUnique_upcross_iff (continuous_revStop hw t) hc,
    ← existsUnique_upcross_iff hw hc]
  exact existsUnique_upcross_revStop c t w

/-- If `d₁ ≤ t`, the first up-crossing interval `[g₁, d₁]` lies in `[0, t]`. -/
lemma isUpcross_of_end₁_le (hw : Continuous w) (hc : 0 < c) {t : ℝ≥0}
    (h1 : upcrossEnd₁ c w ≤ t) :
    IsUpcross c w (upcrossStart₁ c w) (upcrossEnd₁ c w).toNNReal ∧
      (upcrossEnd₁ c w).toNNReal ≤ t := by
  have hne : upcrossEnd₁ c w ≠ ⊤ := ne_top_of_le_ne_top ENNReal.coe_ne_top h1
  obtain ⟨d, hd, hI, -⟩ := isUpcross_upcrossStart₁ hw hc hne
  rw [hd, ENNReal.toNNReal_coe]
  exact ⟨hI, by rw [hd] at h1; exact_mod_cast h1⟩

/-- On `Θ_t`, the first up-crossing interval of the reversed path is `[t - d₁, t - g₁]`. -/
lemma upcrossInterval_revStop (hw : Continuous w) (hc : 0 < c) {t : ℝ≥0}
    (h1 : upcrossEnd₁ c w ≤ t) (h2 : (t : ℝ≥0∞) < upcrossEnd₂ c w) :
    upcrossStart₁ c (revStop c t w) = t - (upcrossEnd₁ c w).toNNReal ∧
      (upcrossEnd₁ c (revStop c t w)).toNNReal = t - upcrossStart₁ c w := by
  obtain ⟨hI, hdt⟩ := isUpcross_of_end₁_le hw hc h1
  have hw' := continuous_revStop (c := c) (t := t) hw
  have hΘ' := (theta_revStop hw hc t).2 ⟨h1, h2⟩
  obtain ⟨hI', hd't⟩ := isUpcross_of_end₁_le hw' hc hΘ'.1
  have huniq := (existsUnique_upcross_iff hw' hc t).2 hΘ'
  have e : (upcrossStart₁ c (revStop c t w), (upcrossEnd₁ c (revStop c t w)).toNNReal) =
      (t - (upcrossEnd₁ c w).toNNReal, t - upcrossStart₁ c w) :=
    huniq.unique ⟨hI', hd't⟩ ⟨hI.revStop hdt, tsub_le_self⟩
  exact ⟨(Prod.mk.inj e).1, (Prod.mk.inj e).2⟩

/-- On `Θ_t`, the first up-crossing piece of the reversed path is the reversed first piece. -/
lemma firstUpcrossPiece_revStop (hw : Continuous w) (hc : 0 < c) {t : ℝ≥0}
    (h1 : upcrossEnd₁ c w ≤ t) (h2 : (t : ℝ≥0∞) < upcrossEnd₂ c w) :
    firstUpcrossPiece c (revStop c t w) =
      revLevel c ((upcrossEnd₁ c w).toNNReal - upcrossStart₁ c w) (firstUpcrossPiece c w) := by
  obtain ⟨hI, hdt⟩ := isUpcross_of_end₁_le hw hc h1
  obtain ⟨e1, e2⟩ := upcrossInterval_revStop hw hc h1 h2
  unfold firstUpcrossPiece
  rw [e1, e2]
  exact pieceAt_revStop hI.1.le hdt

/-- On `Θ_t`, the first up-crossing interval of the path stopped at `t` is `[g₁, d₁]`. -/
lemma upcrossInterval_stop (hw : Continuous w) (hc : 0 < c) {t : ℝ≥0}
    (h1 : upcrossEnd₁ c w ≤ t) (h2 : (t : ℝ≥0∞) < upcrossEnd₂ c w) :
    upcrossStart₁ c (fun s => w (min s t)) = upcrossStart₁ c w ∧
      (upcrossEnd₁ c (fun s => w (min s t))).toNNReal = (upcrossEnd₁ c w).toNNReal := by
  obtain ⟨hI, hdt⟩ := isUpcross_of_end₁_le hw hc h1
  have hw' := continuous_stop hw t
  have hΘ' := (theta_stop hw hc t).2 ⟨h1, h2⟩
  obtain ⟨hI', hd't⟩ := isUpcross_of_end₁_le hw' hc hΘ'.1
  have huniq := (existsUnique_upcross_iff hw' hc t).2 hΘ'
  have hIs : IsUpcross c (fun s => w (min s t)) (upcrossStart₁ c w)
      (upcrossEnd₁ c w).toNNReal :=
    hI.congr fun s hs => by
      show w s = w (min s t)
      rw [min_eq_left (hs.trans hdt)]
  have e : (upcrossStart₁ c (fun s => w (min s t)),
      (upcrossEnd₁ c (fun s => w (min s t))).toNNReal) =
      (upcrossStart₁ c w, (upcrossEnd₁ c w).toNNReal) :=
    huniq.unique ⟨hI', hd't⟩ ⟨hIs, hdt⟩
  exact ⟨(Prod.mk.inj e).1, (Prod.mk.inj e).2⟩

/-- On `Θ_t`, stopping at `t` keeps the first up-crossing piece. -/
lemma firstUpcrossPiece_stop (hw : Continuous w) (hc : 0 < c) {t : ℝ≥0}
    (h1 : upcrossEnd₁ c w ≤ t) (h2 : (t : ℝ≥0∞) < upcrossEnd₂ c w) :
    firstUpcrossPiece c (fun s => w (min s t)) = firstUpcrossPiece c w := by
  obtain ⟨-, hdt⟩ := isUpcross_of_end₁_le hw hc h1
  obtain ⟨e1, e2⟩ := upcrossInterval_stop hw hc h1 h2
  unfold firstUpcrossPiece
  rw [e1, e2]
  funext s
  unfold pieceAt
  have : min (upcrossStart₁ c w + s) (upcrossEnd₁ c w).toNNReal ≤ t :=
    (min_le_right _ _).trans hdt
  show w (min (min (upcrossStart₁ c w + s) (upcrossEnd₁ c w).toNNReal) t) = _
  rw [min_eq_left this]

/-- First hit of `c` by an up-crossing piece is its duration. -/
lemma hitFrom_pieceAt (hc : 0 < c) {g d : ℝ≥0} (h : IsUpcross c w g d) :
    hitFrom c 0 (pieceAt w g d) = ((d - g : ℝ≥0) : ℝ≥0∞) := by
  apply le_antisymm
  · refine hitFrom_le zero_le ?_
    show w (min (g + (d - g)) d) = c
    rw [add_tsub_cancel_of_le h.1.le, min_self]
    exact h.2.2.1
  · refine le_iInf₂ fun s hs => ?_
    have hs' : w (min (g + s) d) = c := hs.2
    by_contra hlt
    have hlt' : s < d - g := by
      have : ¬ ((d - g : ℝ≥0) : ℝ≥0∞) ≤ (s : ℝ≥0∞) := hlt
      exact not_le.1 (fun h' => this (by exact_mod_cast h'))
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ s) with h0 | h0
    · rw [← h0, add_zero, min_eq_left h.1.le, h.2.1] at hs'
      exact hc.ne hs'
    · have hg : g < g + s := lt_add_of_pos_right g h0
      have hd : g + s < d := lt_tsub_iff_left.1 hlt'
      rw [min_eq_left hd.le] at hs'
      exact (h.2.2.2 (g + s) hg hd).2.ne hs'

/-- The time reversal of an up-crossing piece `p` from `0` to `c`:
`s ↦ c - p (T - s)` with `T` the first hitting time of `c` by `p`. -/
def upcrossRev (c : ℝ) (p : ℝ≥0 → ℝ) : ℝ≥0 → ℝ := revLevel c (hitFrom c 0 p).toNNReal p

/-- For the first up-crossing piece, the reversal is over the duration `d₁ - g₁`. -/
lemma upcrossRev_firstUpcrossPiece (hw : Continuous w) (hc : 0 < c) :
    upcrossRev c (firstUpcrossPiece c w) =
      revLevel c ((upcrossEnd₁ c w).toNNReal - upcrossStart₁ c w) (firstUpcrossPiece c w) := by
  by_cases hne : upcrossEnd₁ c w = ⊤
  · have hconst : ∀ s, firstUpcrossPiece c w s = w 0 := by
      intro s
      simp [firstUpcrossPiece, pieceAt, hne]
    have hz : (hitFrom c 0 (firstUpcrossPiece c w)).toNNReal = 0 := by
      by_cases h0 : w 0 = c
      · have h1 : hitFrom c 0 (firstUpcrossPiece c w) ≤ ((0 : ℝ≥0) : ℝ≥0∞) :=
          hitFrom_le zero_le ((hconst 0).trans h0)
        have h' : hitFrom c 0 (firstUpcrossPiece c w) = 0 :=
          le_antisymm (by simpa using h1) zero_le
        rw [h']; rfl
      · have h' : hitFrom c 0 (firstUpcrossPiece c w) = ⊤ :=
          top_unique (le_iInf₂ fun s hs => absurd ((hconst s).symm.trans hs.2) h0)
        rw [h']; rfl
    unfold upcrossRev
    rw [hz, hne]
    simp
  · obtain ⟨d, hd, hI, -⟩ := isUpcross_upcrossStart₁ hw hc hne
    unfold upcrossRev firstUpcrossPiece
    rw [hd, ENNReal.toNNReal_coe, hitFrom_pieceAt hc hI, ENNReal.toNNReal_coe]

open scoped Classical in
/-- The functional `w ↦ f (first up-crossing piece of w) · 1{Θ_t w}`. -/
def upcrossOnce (c : ℝ) (t : ℝ≥0) (f : (ℝ≥0 → ℝ) → ℝ≥0∞) (w : ℝ≥0 → ℝ) : ℝ≥0∞ :=
  if upcrossEnd₁ c w ≤ t ∧ (t : ℝ≥0∞) < upcrossEnd₂ c w then f (firstUpcrossPiece c w) else 0

/-- The functional only reads `w` on `[0, t]`. -/
lemma upcrossOnce_stop (hw : Continuous w) (hc : 0 < c) (t : ℝ≥0) (f : (ℝ≥0 → ℝ) → ℝ≥0∞) :
    upcrossOnce c t f (fun s => w (min s t)) = upcrossOnce c t f w := by
  unfold upcrossOnce
  by_cases h : upcrossEnd₁ c w ≤ t ∧ (t : ℝ≥0∞) < upcrossEnd₂ c w
  · have h' := (theta_stop hw hc t).2 h
    rw [firstUpcrossPiece_stop hw hc h.1 h.2]
    simp only [h, h', and_self, ↓reduceIte]
  · have h' : ¬ (upcrossEnd₁ c (fun s => w (min s t)) ≤ t ∧
        (t : ℝ≥0∞) < upcrossEnd₂ c (fun s => w (min s t))) := fun h'' => h ((theta_stop hw hc t).1 h'')
    simp only [h, h', ↓reduceIte]

/-- Under reversal at `t` and reflection at `c`, the functional becomes the one of the reversed
piece. -/
lemma upcrossOnce_revStop (hw : Continuous w) (hc : 0 < c) (t : ℝ≥0) (f : (ℝ≥0 → ℝ) → ℝ≥0∞) :
    upcrossOnce c t f (revStop c t w) = upcrossOnce c t (fun p => f (upcrossRev c p)) w := by
  unfold upcrossOnce
  by_cases h : upcrossEnd₁ c w ≤ t ∧ (t : ℝ≥0∞) < upcrossEnd₂ c w
  · have h' := (theta_revStop hw hc t).2 h
    simp only [h, h', and_self, ↓reduceIte]
    rw [firstUpcrossPiece_revStop hw hc h.1 h.2, upcrossRev_firstUpcrossPiece hw hc]
  · have h' : ¬ (upcrossEnd₁ c (revStop c t w) ≤ t ∧
        (t : ℝ≥0∞) < upcrossEnd₂ c (revStop c t w)) := fun h'' => h ((theta_revStop hw hc t).1 h'')
    simp only [h, h', ↓reduceIte]

end Pathwise

section Measurability

variable {c : ℝ}

lemma measurable_upcrossRev_firstUpcrossPiece (hc : 0 < c) :
    Measurable fun w : C(ℝ≥0, ℝ) => upcrossRev c (firstUpcrossPiece c (w : ℝ≥0 → ℝ)) := by
  have key : (fun w : C(ℝ≥0, ℝ) => upcrossRev c (firstUpcrossPiece c (w : ℝ≥0 → ℝ))) =
      fun w : C(ℝ≥0, ℝ) => revLevel c ((upcrossEnd₁ c (w : ℝ≥0 → ℝ)).toNNReal -
        upcrossStart₁ c (w : ℝ≥0 → ℝ)) (firstUpcrossPiece c (w : ℝ≥0 → ℝ)) :=
    funext fun w => upcrossRev_firstUpcrossPiece w.continuous hc
  rw [key]
  refine Measurable.of_eval fun s => ?_
  have hD : Measurable fun w : C(ℝ≥0, ℝ) =>
      (upcrossEnd₁ c (w : ℝ≥0 → ℝ)).toNNReal - upcrossStart₁ c (w : ℝ≥0 → ℝ) :=
    (measurable_upcrossEnd₁ c).ennreal_toNNReal.sub (measurable_upcrossStart₁ c)
  have := measurable_eval_comp (τ := fun w : C(ℝ≥0, ℝ) =>
    min (upcrossStart₁ c (w : ℝ≥0 → ℝ) + ((upcrossEnd₁ c (w : ℝ≥0 → ℝ)).toNNReal -
      upcrossStart₁ c (w : ℝ≥0 → ℝ) - s)) (upcrossEnd₁ c (w : ℝ≥0 → ℝ)).toNNReal)
    (((measurable_upcrossStart₁ c).add (hD.sub measurable_const)).min
      (measurable_upcrossEnd₁ c).ennreal_toNNReal)
  exact measurable_const.sub this

/-- The functional `upcrossOnce c t f` is measurable on path space when `f ∘ piece` is. -/
lemma measurable_upcrossOnce (hc : 0 < c) (t : ℝ≥0) {f : (ℝ≥0 → ℝ) → ℝ≥0∞}
    (hf : Measurable fun w : C(ℝ≥0, ℝ) => f (firstUpcrossPiece c (w : ℝ≥0 → ℝ))) :
    Measurable fun w : C(ℝ≥0, ℝ) => upcrossOnce c t f (w : ℝ≥0 → ℝ) := by
  classical
  have hset : MeasurableSet {w : C(ℝ≥0, ℝ) |
      upcrossEnd₁ c (w : ℝ≥0 → ℝ) ≤ t ∧ (t : ℝ≥0∞) < upcrossEnd₂ c (w : ℝ≥0 → ℝ)} := by
    have := measurableSet_existsUnique_upcross c hc t
    convert this using 1
    ext w
    exact (existsUnique_upcross_iff w.continuous hc t).symm
  exact Measurable.ite hset hf measurable_const

end Measurability

end LatticeProb
