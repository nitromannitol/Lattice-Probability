import Mathlib
import LatticeProb.Prob.UpcrossShift
import LatticeProb.Prob.StopFunctionalHit

/-!
# Laplace weights of up-crossing times, and the pathwise decompositions

`expNeg q r = e^{-q r}` with `e^{-q ∞} = 0`, valued in `[0, ∞]`.  For a path `w` and a measurable
functional `f` of the first up-crossing piece we record the two pathwise identities behind the
two renewal steps of the Laplace transform of the last up-crossing piece:

* `LatticeProb.expNeg_upcrossEnd₁_mul_piece_eq`: at the first zero `τ₀`,
  `e^{-q d₁} f(piece w) = e^{-q τ₀} · (f(piece (w - w τ₀ after τ₀)) e^{-q d₁(w after τ₀)})`;
* `LatticeProb.expNeg_upcrossEnd₂_mul_piece_eq`: at `d₁`,
  `e^{-q d₂} f(piece w) = (e^{-q d₁} f(piece)) (stopped at d₁) · e^{-q upcrossReturn (w after d₁)}`.
-/

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

/-- `e^{-q r}` for `r ∈ [0, ∞]`, with `e^{-q ∞} = 0`. -/
def expNeg (q : ℝ) (r : ℝ≥0∞) : ℝ≥0∞ :=
  if r = ⊤ then 0 else ENNReal.ofReal (Real.exp (-q * r.toReal))

@[simp] lemma expNeg_top (q : ℝ) : expNeg q ⊤ = 0 := by simp [expNeg]

lemma expNeg_add (q : ℝ) (a b : ℝ≥0∞) : expNeg q (a + b) = expNeg q a * expNeg q b := by
  by_cases ha : a = ⊤
  · simp [ha]
  by_cases hb : b = ⊤
  · simp [hb]
  have hab : a + b ≠ ⊤ := ENNReal.add_ne_top.2 ⟨ha, hb⟩
  simp only [expNeg, ha, hb, hab, ite_false]
  rw [ENNReal.toReal_add ha hb, mul_add, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]

lemma expNeg_le_one {q : ℝ} (hq : 0 ≤ q) (r : ℝ≥0∞) : expNeg q r ≤ 1 := by
  unfold expNeg
  split_ifs with h
  · exact zero_le
  · rw [← ENNReal.ofReal_one]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_one_iff.2
    have := ENNReal.toReal_nonneg (a := r)
    nlinarith

lemma measurable_expNeg (q : ℝ) : Measurable (expNeg q) :=
  Measurable.ite (measurableSet_singleton ⊤) measurable_const
    (ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul ENNReal.measurable_toReal)))

lemma measurable_upcrossReturn (c : ℝ) :
    Measurable fun w : C(ℝ≥0, ℝ) => upcrossReturn c (w : ℝ≥0 → ℝ) :=
  measurable_hitFrom (r := fun w : C(ℝ≥0, ℝ) => hitFrom (-c) 0 (w : ℝ≥0 → ℝ))
    (measurable_hitFrom measurable_const (-c)) 0

/-- The first up-crossing piece does not change when the path is stopped at `d₁`. -/
lemma firstUpcrossPiece_stopAt (c : ℝ) (w : C(ℝ≥0, ℝ)) {D : ℝ≥0}
    (hD : upcrossEnd₁ c (w : ℝ≥0 → ℝ) = D) :
    firstUpcrossPiece c (stopAt (D : ℝ≥0∞) w : ℝ≥0 → ℝ) = firstUpcrossPiece c (w : ℝ≥0 → ℝ) := by
  have e1 : upcrossEnd₁ c (stopAt (D : ℝ≥0∞) w : ℝ≥0 → ℝ) = D := by
    have := (isStopFun_upcrossEnd₁ c w D).1 (le_of_eq hD)
    exact this.trans hD
  have e2 : lastZeroBefore (stopAt (D : ℝ≥0∞) w : ℝ≥0 → ℝ) D = lastZeroBefore (w : ℝ≥0 → ℝ) D := by
    unfold lastZeroBefore
    congr 1
    ext s
    constructor
    · rintro ⟨hs, h0⟩
      refine ⟨hs, ?_⟩
      have : stopAt (D : ℝ≥0∞) w s = 0 := h0
      rwa [stopAt_coe_of_le w hs] at this
    · rintro ⟨hs, h0⟩
      refine ⟨hs, ?_⟩
      show stopAt (D : ℝ≥0∞) w s = 0
      rwa [stopAt_coe_of_le w hs]
  funext s
  unfold firstUpcrossPiece upcrossStart₁ pieceAt
  rw [e1, hD, ENNReal.toNNReal_coe, e2]
  exact stopAt_coe_of_le w (min_le_right _ _)

/-- Pathwise decomposition at the first zero `τ₀` of the Laplace weight of `d₁` times a
functional of the first up-crossing piece. -/
theorem expNeg_upcrossEnd₁_mul_piece_eq {c : ℝ} (hc : 0 < c) (q : ℝ) (w : C(ℝ≥0, ℝ))
    (f : (ℝ≥0 → ℝ) → ℝ≥0∞) :
    expNeg q (upcrossEnd₁ c (w : ℝ≥0 → ℝ)) * f (firstUpcrossPiece c (w : ℝ≥0 → ℝ)) =
      expNeg q (hitFrom 0 0 (w : ℝ≥0 → ℝ)) *
        (f (firstUpcrossPiece c (shiftPath (hitFrom 0 0 (w : ℝ≥0 → ℝ)).toNNReal w : ℝ≥0 → ℝ)) *
          expNeg q (upcrossEnd₁ c (shiftPath (hitFrom 0 0 (w : ℝ≥0 → ℝ)).toNNReal w : ℝ≥0 → ℝ))) := by
  by_cases h0 : hitFrom 0 0 (w : ℝ≥0 → ℝ) = ⊤
  · have : upcrossEnd₁ c (w : ℝ≥0 → ℝ) = ⊤ := by
      unfold upcrossEnd₁; rw [h0, hitFrom_top]
    rw [this, h0]
    simp
  · obtain ⟨T, hT, hwT, hd1⟩ := upcrossEnd₁_eq_add_shift (c := c) w.continuous h0
    have hTnn : (hitFrom 0 0 (w : ℝ≥0 → ℝ)).toNNReal = T := by rw [hT, ENNReal.toNNReal_coe]
    rw [hTnn]
    have hv : (shiftPath T w : ℝ≥0 → ℝ) = fun s => w (T + s) - w T := rfl
    have hv0 : (shiftPath T w : ℝ≥0 → ℝ) 0 = 0 := by simp
    rw [upcrossEnd₁_of_zero_start hv0, hv]
    by_cases hfin : hitFrom c 0 (fun s => w (T + s) - w T) = ⊤
    · rw [hd1, hfin]
      simp
    · rw [firstUpcrossPiece_eq_shift w.continuous hc hT hwT hfin, hd1, expNeg_add, hT]
      ring

/-- Pathwise decomposition at `d₁` of the Laplace weight of `d₂` times a functional of the first
up-crossing piece. -/
theorem expNeg_upcrossEnd₂_mul_piece_eq (c q : ℝ) (w : C(ℝ≥0, ℝ)) (f : (ℝ≥0 → ℝ) → ℝ≥0∞) :
    expNeg q (upcrossEnd₂ c (w : ℝ≥0 → ℝ)) * f (firstUpcrossPiece c (w : ℝ≥0 → ℝ)) =
      (expNeg q (upcrossEnd₁ c (stopAt (upcrossEnd₁ c (w : ℝ≥0 → ℝ)) w : ℝ≥0 → ℝ)) *
        f (firstUpcrossPiece c (stopAt (upcrossEnd₁ c (w : ℝ≥0 → ℝ)) w : ℝ≥0 → ℝ))) *
        expNeg q (upcrossReturn c
          (shiftPath (upcrossEnd₁ c (w : ℝ≥0 → ℝ)).toNNReal w : ℝ≥0 → ℝ)) := by
  by_cases hd : upcrossEnd₁ c (w : ℝ≥0 → ℝ) = ⊤
  · have h2 : upcrossEnd₂ c (w : ℝ≥0 → ℝ) = ⊤ := by
      unfold upcrossEnd₂; rw [hd, hitFrom_top, hitFrom_top]
    rw [h2, hd, stopAt_top, hd]
    simp
  · obtain ⟨D, hD, hwD, hd2⟩ := upcrossEnd₂_eq_add_shift w.continuous hd
    have e1 : upcrossEnd₁ c (stopAt (D : ℝ≥0∞) w : ℝ≥0 → ℝ) = D :=
      ((isStopFun_upcrossEnd₁ c w D).1 hD.le).trans hD
    have hsh : (shiftPath D w : ℝ≥0 → ℝ) = fun s => w (D + s) - w D := rfl
    rw [hD, ENNReal.toNNReal_coe, hd2, e1, firstUpcrossPiece_stopAt c w hD, hsh, expNeg_add]
    ring

end LatticeProb
