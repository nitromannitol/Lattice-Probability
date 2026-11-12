import Mathlib
import LatticeProb.Prob.UpcrossMeasurable
import LatticeProb.Prob.BrownianRestartPath

/-!
# Shifting a path to its first zero

First hits and the first up-crossing interval of a continuous path `w` after its first zero
`τ₀ = hitFrom 0 0 w` are read off the increments `shiftPath τ₀ w` of the path after `τ₀`:

* `LatticeProb.hitFrom_add_coe`: `hitFrom a (T + r) w = T + hitFrom (a - w T) r (w (T + ·) - w T)`.
* `LatticeProb.upcrossEnd₁_eq_add_shift`: `d₁ w = τ₀ + hitFrom c 0 (shiftPath τ₀ w)`.
* `LatticeProb.firstUpcrossPiece_eq_shift`: if the shifted path reaches `c`, the piece of `w` on
  its first up-crossing interval equals that of the shifted path.
* `LatticeProb.upcrossEnd₂_eq_add_shift`: `d₂ w = d₁ w + upcrossReturn c (w (d₁ + ·) - c)`, where
  `upcrossReturn c v` is the first return to `0` after the first hit of `-c`.
-/

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

section Shift

variable {w : ℝ≥0 → ℝ} {a c : ℝ}

/-- First hits after a time `T + r` are the hits of the increments after `T` after `r`. -/
theorem hitFrom_add_coe (a : ℝ) (T : ℝ≥0) (r : ℝ≥0∞) (w : ℝ≥0 → ℝ) :
    hitFrom a ((T : ℝ≥0∞) + r) w =
      (T : ℝ≥0∞) + hitFrom (a - w T) r (fun s => w (T + s) - w T) := by
  unfold hitFrom
  rw [ENNReal.add_iInf₂]
  apply le_antisymm
  · refine le_iInf₂ fun s' hs' => ?_
    have h1 : (T : ℝ≥0∞) + r ≤ ((T + s' : ℝ≥0) : ℝ≥0∞) := by
      rw [ENNReal.coe_add]; exact add_le_add_right hs'.1 _
    have h2 : w (T + s') = a := by
      have := hs'.2
      simpa using this
    have := hitFrom_le h1 h2
    rw [ENNReal.coe_add] at this
    exact this
  · refine le_iInf₂ fun s hs => ?_
    have hTs : T ≤ s := by
      have : (T : ℝ≥0∞) ≤ s := le_trans le_self_add hs.1
      exact_mod_cast this
    obtain ⟨s', rfl⟩ : ∃ s', s = T + s' := ⟨s - T, (add_tsub_cancel_of_le hTs).symm⟩
    have hr : r ≤ s' := by
      rw [ENNReal.coe_add] at hs
      exact (ENNReal.add_le_add_iff_left ENNReal.coe_ne_top).1 hs.1
    have h3 := iInf₂_le (f := fun (i : ℝ≥0) (_ : r ≤ (i : ℝ≥0∞) ∧ w (T + i) - w T = a - w T) =>
      (T : ℝ≥0∞) + (i : ℝ≥0∞)) s' ⟨hr, by rw [hs.2]⟩
    rw [ENNReal.coe_add]
    exact h3

/-- A path starting at `0` has `hitFrom 0 0 w = 0`, so `d₁ w` is its first hit of `c`. -/
lemma upcrossEnd₁_of_zero_start (h0 : w 0 = 0) : upcrossEnd₁ c w = hitFrom c 0 w := by
  have : hitFrom 0 0 w = 0 := le_antisymm (hitFrom_le (r := 0) (s := 0) le_rfl h0) zero_le
  unfold upcrossEnd₁
  rw [this]

/-- The first zero of a continuous path with a finite first zero time `τ₀` is attained and no
zero comes earlier. -/
lemma exists_firstZero (hw : Continuous w) (h : hitFrom 0 0 w ≠ ⊤) :
    ∃ T : ℝ≥0, hitFrom 0 0 w = T ∧ w T = 0 ∧ ∀ s, w s = 0 → T ≤ s := by
  obtain ⟨T, hT, -, hwT, hmin⟩ := exists_hitFrom_eq hw h
  exact ⟨T, hT, hwT, fun s hs => hmin s zero_le hs⟩

/-- The end `d₁` of the first up-crossing interval is the first zero time plus the first hit of
`c` by the increments after the first zero. -/
theorem upcrossEnd₁_eq_add_shift (hw : Continuous w) (h : hitFrom 0 0 w ≠ ⊤) :
    ∃ T : ℝ≥0, hitFrom 0 0 w = T ∧ w T = 0 ∧
      upcrossEnd₁ c w = (T : ℝ≥0∞) + hitFrom c 0 (fun s => w (T + s) - w T) := by
  obtain ⟨T, hT, hwT, -⟩ := exists_firstZero hw h
  refine ⟨T, hT, hwT, ?_⟩
  have := hitFrom_add_coe c T 0 w
  have h2 : c - w T = c := by rw [hwT, sub_zero]
  rw [add_zero, h2] at this
  unfold upcrossEnd₁
  rw [hT, this]

/-- The end `d₁` of the first up-crossing interval, from the first zero time `T`. -/
lemma upcrossEnd₁_eq_of_firstZero {T : ℝ≥0} (hT : hitFrom 0 0 w = T) (hwT : w T = 0) :
    upcrossEnd₁ c w = (T : ℝ≥0∞) + hitFrom c 0 (fun s => w (T + s) - w T) := by
  have := hitFrom_add_coe c T 0 w
  have h2 : c - w T = c := by rw [hwT, sub_zero]
  rw [add_zero, h2] at this
  unfold upcrossEnd₁
  rw [hT, this]

/-- Two up-crossing intervals with the same end have the same start. -/
lemma isUpcross_start_unique {v : ℝ≥0 → ℝ} {g g' d : ℝ≥0} (h : IsUpcross c v g d)
    (h' : IsUpcross c v g' d) : g = g' := by
  rcases lt_trichotomy g g' with hlt | heq | hgt
  · exfalso
    have := (h.2.2.2 g' hlt h'.1).1
    rw [h'.2.1] at this
    exact lt_irrefl _ this
  · exact heq
  · exfalso
    have := (h'.2.2.2 g hgt h.1).1
    rw [h.2.1] at this
    exact lt_irrefl _ this

/-- An up-crossing interval starting at or after the time `T` of a zero of `w` is an up-crossing
interval of the increments after `T`, shifted by `T`. -/
lemma IsUpcross.shift {g d T : ℝ≥0} (h : IsUpcross c w g d) (hwT : w T = 0) (hTg : T ≤ g) :
    IsUpcross c (fun s => w (T + s) - w T) (g - T) (d - T) := by
  have hTd : T ≤ d := hTg.trans h.1.le
  have hg : T + (g - T) = g := add_tsub_cancel_of_le hTg
  have hd : T + (d - T) = d := add_tsub_cancel_of_le hTd
  refine ⟨?_, ?_, ?_, fun s hgs hsd => ?_⟩
  · have : T + (g - T) < T + (d - T) := by rw [hg, hd]; exact h.1
    exact lt_of_add_lt_add_left this
  · show w (T + (g - T)) - w T = 0
    rw [hg, h.2.1, hwT, sub_zero]
  · show w (T + (d - T)) - w T = c
    rw [hd, h.2.2.1, hwT, sub_zero]
  · have h1 : g < T + s := by
      calc g = T + (g - T) := hg.symm
        _ < T + s := add_lt_add_right hgs T
    have h2 : T + s < d := by
      calc T + s < T + (d - T) := add_lt_add_right hsd T
        _ = d := hd
    have := h.2.2.2 (T + s) h1 h2
    show 0 < w (T + s) - w T ∧ w (T + s) - w T < c
    rw [hwT, sub_zero]
    exact this

/-- If the increments after the first zero reach `c`, the piece of the path on its first
up-crossing interval is the piece of the increments on their first up-crossing interval. -/
theorem firstUpcrossPiece_eq_shift (hw : Continuous w) (hc : 0 < c) {T : ℝ≥0}
    (hT : hitFrom 0 0 w = T) (hwT : w T = 0)
    (hfin : hitFrom c 0 (fun s => w (T + s) - w T) ≠ ⊤) :
    firstUpcrossPiece c w = firstUpcrossPiece c (fun s => w (T + s) - w T) := by
  set v : ℝ≥0 → ℝ := fun s => w (T + s) - w T with hvdef
  have hv : Continuous v := (hw.comp (continuous_const.add continuous_id)).sub continuous_const
  have hv0 : v 0 = 0 := by simp [hvdef]
  have hd1v : upcrossEnd₁ c v = hitFrom c 0 v := upcrossEnd₁_of_zero_start hv0
  have hd1w : upcrossEnd₁ c w = (T : ℝ≥0∞) + hitFrom c 0 v := upcrossEnd₁_eq_of_firstZero hT hwT
  obtain ⟨dv, hdv, hUv, -⟩ := isUpcross_upcrossStart₁ hv hc (by rw [hd1v]; exact hfin)
  have hdv' : hitFrom c 0 v = dv := by rw [← hd1v]; exact hdv
  have hne : upcrossEnd₁ c w ≠ ⊤ := by
    rw [hd1w]; exact ENNReal.add_ne_top.2 ⟨ENNReal.coe_ne_top, hfin⟩
  obtain ⟨d, hd, hUw, -⟩ := isUpcross_upcrossStart₁ hw hc hne
  have hdd : d = T + dv := by
    have : (d : ℝ≥0∞) = T + dv := by rw [← hd, hd1w, hdv']
    exact_mod_cast this
  have hTg : T ≤ upcrossStart₁ c w := by
    have h0 := hUw.2.1
    have : hitFrom 0 0 w ≤ (upcrossStart₁ c w : ℝ≥0) := hitFrom_le (r := 0) zero_le h0
    rw [hT] at this
    exact_mod_cast this
  have hsh := hUw.shift hwT hTg
  have hdT : d - T = dv := by rw [hdd, add_tsub_cancel_left]
  rw [hdT] at hsh
  have hg : upcrossStart₁ c w - T = upcrossStart₁ c v := isUpcross_start_unique hsh hUv
  have hg' : upcrossStart₁ c w = T + upcrossStart₁ c v := by
    rw [← hg]; exact (add_tsub_cancel_of_le hTg).symm
  have hdw : (upcrossEnd₁ c w).toNNReal = T + dv := by rw [hd, ENNReal.toNNReal_coe, hdd]
  have hdvv : (upcrossEnd₁ c v).toNNReal = dv := by rw [hdv, ENNReal.toNNReal_coe]
  funext s
  unfold firstUpcrossPiece pieceAt
  rw [hdw, hdvv, hg']
  show w (min (T + upcrossStart₁ c v + s) (T + dv)) =
    w (T + min (upcrossStart₁ c v + s) dv) - w T
  rw [hwT, sub_zero, ← min_add_add_left, add_assoc]

/-- The first return to `0` after the first hit of `-c`: if `v` starts at the level `c` then
`upcrossReturn c (v - c)` is the time to go down to `0` and come back to `c`. -/
def upcrossReturn (c : ℝ) (v : ℝ≥0 → ℝ) : ℝ≥0∞ := hitFrom 0 (hitFrom (-c) 0 v) v

/-- The end `d₂` of the second up-crossing interval is `d₁` plus the return time of the
increments after `d₁`. -/
theorem upcrossEnd₂_eq_add_shift (hw : Continuous w) (h : upcrossEnd₁ c w ≠ ⊤) :
    ∃ D : ℝ≥0, upcrossEnd₁ c w = D ∧ w D = c ∧
      upcrossEnd₂ c w = (D : ℝ≥0∞) + upcrossReturn c (fun s => w (D + s) - w D) := by
  obtain ⟨D, hD, -, hwD, -⟩ := exists_hitFrom_eq hw (show hitFrom c (hitFrom 0 0 w) w ≠ ⊤ from h)
  have hD' : upcrossEnd₁ c w = D := hD
  refine ⟨D, hD', hwD, ?_⟩
  have e1 : hitFrom 0 (D : ℝ≥0∞) w = (D : ℝ≥0∞) + hitFrom (-c) 0 (fun s => w (D + s) - w D) := by
    have := hitFrom_add_coe 0 D 0 w
    have h0 : (0 : ℝ) - w D = -c := by rw [hwD, zero_sub]
    rw [add_zero, h0] at this
    exact this
  have e2 := hitFrom_add_coe c D (hitFrom (-c) 0 (fun s => w (D + s) - w D)) w
  have h1 : c - w D = 0 := by rw [hwD, sub_self]
  rw [h1] at e2
  unfold upcrossEnd₂ upcrossReturn
  rw [hD', e1, e2]

end Shift

end LatticeProb
