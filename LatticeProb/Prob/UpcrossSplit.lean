import Mathlib
import LatticeProb.Prob.UpcrossShift
import LatticeProb.Prob.UpcrossMeasurable
import LatticeProb.Prob.StopFunctionalMin
import LatticeProb.Prob.StopFunctionalHit

/-!
# Failed attempts and the first up-crossing piece

Pathwise facts used to split the final up-crossing from `0` to `c` at an intermediate level `c'`.

* `exitFrom a b r w`: the first time at or after `r` that the path hits `a` or `b`; it is a
  measurable stopping functional when `r` is.
* `firstUpcrossPiece_eq_shift_of_zero`: if a continuous path `w` with `w 0 = 0` returns to `0` at
  time `T` without having reached the level `c`, then the first up-crossing piece of `w` equals
  that of the increments of `w` after `T`.
* `firstUpcrossPiece_eq_shift_of_fail`: the same for a failed attempt, that is a path which hits
  `c'` at `τ`, then hits `0` at `T` before hitting `c`, where `0 < c' < c`.
-/

open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

/-- The first time at or after `r` that the path hits `a` or `b`. -/
def exitFrom (a b : ℝ) (r : ℝ≥0∞) (w : ℝ≥0 → ℝ) : ℝ≥0∞ := Min.min (hitFrom a r w) (hitFrom b r w)

lemma measurable_exitFrom {r : C(ℝ≥0, ℝ) → ℝ≥0∞} (hr : Measurable r) (a b : ℝ) :
    Measurable fun w : C(ℝ≥0, ℝ) => exitFrom a b (r w) (w : ℝ≥0 → ℝ) :=
  (measurable_hitFrom hr a).min (measurable_hitFrom hr b)

lemma isStopFun_exitFrom {Ψ : C(ℝ≥0, ℝ) → ℝ≥0∞} (hΨ : IsStopFun Ψ) (a b : ℝ) :
    IsStopFun fun w : C(ℝ≥0, ℝ) => exitFrom a b (Ψ w) (w : ℝ≥0 → ℝ) :=
  (hΨ.hitFrom a).min (hΨ.hitFrom b)

variable {w : ℝ≥0 → ℝ} {c : ℝ}

/-- If the first up-crossing interval never ends, the piece is constant. -/
lemma firstUpcrossPiece_of_top (h : upcrossEnd₁ c w = ⊤) :
    firstUpcrossPiece c w = fun _ => w 0 := by
  funext s
  simp [firstUpcrossPiece, pieceAt, h]

/-- A continuous path which is `< c` at time `0` and avoids the level `c` on `[0, T]` stays `< c`
on `[0, T]`. -/
lemma forall_lt_of_forall_ne (hw : Continuous w) (h0 : w 0 < c) {T : ℝ≥0}
    (hne : ∀ s : ℝ≥0, s ≤ T → w s ≠ c) : ∀ s : ℝ≥0, s ≤ T → w s < c := by
  intro s hs
  by_contra hcon
  rw [not_lt] at hcon
  obtain ⟨s', hs'mem, hws'⟩ : ∃ s' ∈ Set.Icc (0 : ℝ≥0) s, w s' = c :=
    intermediate_value_Icc zero_le hw.continuousOn ⟨h0.le, hcon⟩
  exact hne s' (hs'mem.2.trans hs) hws'

/-- **Restart at a return to `0` before the level `c`.**  If a continuous path `w` with `w 0 = 0`
has `w T = 0` and `w < c` on `[0, T]`, then its first up-crossing piece of `0 → c` is the first
up-crossing piece of its increments after `T`. -/
theorem firstUpcrossPiece_eq_shift_of_zero (hw : Continuous w) (hc : 0 < c) {T : ℝ≥0}
    (hw0 : w 0 = 0) (hwT : w T = 0) (hlt : ∀ s : ℝ≥0, s ≤ T → w s < c) :
    firstUpcrossPiece c w = firstUpcrossPiece c (fun s => w (T + s) - w T) := by
  set v : ℝ≥0 → ℝ := fun s => w (T + s) - w T with hvdef
  have hv : Continuous v := (hw.comp (continuous_const.add continuous_id)).sub continuous_const
  have hv0 : v 0 = 0 := by simp [hvdef]
  have hd1v : upcrossEnd₁ c v = hitFrom c 0 v := upcrossEnd₁_of_zero_start hv0
  have hTs : ∀ s : ℝ≥0, w s = c → (T : ℝ≥0∞) ≤ s := fun s hs => by
    by_contra hcon
    have : s ≤ T := by exact_mod_cast (not_le.1 hcon).le
    exact (hlt s this).ne hs
  have h1 : hitFrom c 0 w = hitFrom c (T : ℝ≥0∞) w :=
    le_antisymm (le_iInf₂ fun s hs => hitFrom_le zero_le hs.2)
      (le_iInf₂ fun s hs => hitFrom_le (hTs s hs.2) hs.2)
  have hd1w : upcrossEnd₁ c w = (T : ℝ≥0∞) + hitFrom c 0 v := by
    rw [upcrossEnd₁_of_zero_start hw0, h1]
    have := hitFrom_add_coe c T 0 w
    have h2 : c - w T = c := by rw [hwT, sub_zero]
    rw [add_zero, h2] at this
    exact this
  by_cases hfin : hitFrom c 0 v = ⊤
  · have h1' : upcrossEnd₁ c w = ⊤ := by rw [hd1w, hfin]; simp
    have h2' : upcrossEnd₁ c v = ⊤ := by rw [hd1v, hfin]
    rw [firstUpcrossPiece_of_top h1', firstUpcrossPiece_of_top h2', hw0, hv0]
  · obtain ⟨dv, hdv, hUv, -⟩ := isUpcross_upcrossStart₁ hv hc (by rw [hd1v]; exact hfin)
    have hdv' : hitFrom c 0 v = dv := by rw [← hd1v]; exact hdv
    have hne : upcrossEnd₁ c w ≠ ⊤ := by
      rw [hd1w]; exact ENNReal.add_ne_top.2 ⟨ENNReal.coe_ne_top, hfin⟩
    obtain ⟨d, hd, hUw, -⟩ := isUpcross_upcrossStart₁ hw hc hne
    have hdd : d = T + dv := by
      have : (d : ℝ≥0∞) = T + dv := by rw [← hd, hd1w, hdv']
      exact_mod_cast this
    have hTg : T ≤ upcrossStart₁ c w := by
      by_contra hcon
      rw [not_le] at hcon
      have hle : T ≤ d := by rw [hdd]; exact le_self_add
      have hTd : T < d := lt_of_le_of_ne hle (fun h => by
        have := hUw.2.2.1
        rw [← h, hwT] at this
        exact hc.ne this)
      exact (hUw.2.2.2 T hcon hTd).1.ne' hwT
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

/-- **A failed attempt does not change the first up-crossing piece.**  Let `0 < c' < c` and let
`w` be a continuous path with `w 0 = 0`.  Suppose that after the first hit `τ` of `c'` the path hits
`0` (at the finite time `T`) no later than it hits `c`.  Then the first up-crossing piece of `w`
of `0 → c` is that of the increments of `w` after `T`. -/
theorem firstUpcrossPiece_eq_shift_of_fail (hw : Continuous w) (hw0 : w 0 = 0) {c' : ℝ}
    (hc' : 0 < c') (hcc : c' < c)
    (hfail : hitFrom 0 (hitFrom c' 0 w) w ≤ hitFrom c (hitFrom c' 0 w) w)
    (hfin : hitFrom 0 (hitFrom c' 0 w) w ≠ ⊤) :
    firstUpcrossPiece c w = firstUpcrossPiece c (fun s =>
      w ((hitFrom 0 (hitFrom c' 0 w) w).toNNReal + s) - w (hitFrom 0 (hitFrom c' 0 w) w).toNNReal) := by
  have hc : 0 < c := hc'.trans hcc
  obtain ⟨T, hT, -, hwT, -⟩ := exists_hitFrom_eq hw hfin
  rw [hT, ENNReal.toNNReal_coe]
  refine firstUpcrossPiece_eq_shift_of_zero hw hc hw0 hwT ?_
  refine forall_lt_of_forall_ne hw (by rw [hw0]; exact hc) fun s hs hws => ?_
  obtain ⟨s', hs'mem, hws'⟩ : ∃ s' ∈ Set.Icc (0 : ℝ≥0) s, w s' = c' :=
    intermediate_value_Icc zero_le hw.continuousOn ⟨by rw [hw0]; exact hc'.le, by rw [hws]; exact hcc.le⟩
  have hτs : hitFrom c' 0 w ≤ s :=
    (hitFrom_le (r := 0) zero_le hws').trans (by exact_mod_cast hs'mem.2)
  have h2 : hitFrom c (hitFrom c' 0 w) w ≤ s := hitFrom_le hτs hws
  have h3 : (T : ℝ≥0∞) ≤ s := by rw [← hT]; exact hfail.trans h2
  have : s = T := le_antisymm hs (by exact_mod_cast h3)
  rw [this, hwT] at hws
  exact hc.ne hws

end LatticeProb
