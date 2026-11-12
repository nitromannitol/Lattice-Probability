import Mathlib
import LatticeProb.Prob.UpcrossReversalPathwise
import LatticeProb.Prob.UpcrossConcat

/-!
# Time reversal of a concatenation of two up-crossing pieces

If `p` is a continuous path from `0` that first hits `c'` at time `L` and stays at `c'` afterwards,
and `q` is a continuous path from `0` that first hits `a` at time `e`, then the concatenation of `p`
followed by `q` first hits `c' + a` at time `L + e`, and its reversal (read at level `c' + a`) is the
reversal of `q` (read at level `a`, over the duration `e`) followed by the reversal of `p`.
-/

open Set
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

/-- The concatenation of `p` and `q` first hits `c' + a` at time `L + e`. -/
lemma hitFrom_concatAt_of_hit {c' a : ℝ} (hc' : 0 < c') (ha : 0 < a) {L e : ℝ≥0}
    {p q : ℝ≥0 → ℝ} (hp : Continuous p) (hp0 : p 0 = 0) (hphit : hitFrom c' 0 p = L)
    (hpconst : ∀ t, L ≤ t → p t = c') (hq : Continuous q) (hq0 : q 0 = 0)
    (hqhit : hitFrom a 0 q = e) :
    hitFrom (c' + a) 0 (concatAt L p q) = ((L + e : ℝ≥0) : ℝ≥0∞) := by
  have hqe : q e = a := by
    obtain ⟨s, hs, -, hqs, -⟩ := exists_hitFrom_eq hq (by rw [hqhit]; exact ENNReal.coe_ne_top)
    have : (e : ℝ≥0∞) = s := hqhit.symm.trans hs
    rw [ENNReal.coe_inj.1 this]; exact hqs
  have hpL : p L = c' := hpconst L le_rfl
  have hup : hitFrom (c' + a) 0 (concatAt L p q) ≤ ((L + e : ℝ≥0) : ℝ≥0∞) := by
    refine hitFrom_le (zero_le) ?_
    simp only [concatAt, hpconst (L + e) le_self_add, add_tsub_cancel_left, hqe]
  have hlow : ∀ s : ℝ≥0, concatAt L p q s = c' + a → L + e ≤ s := by
    intro s hs
    by_contra hlt
    rw [not_le] at hlt
    rcases lt_or_ge s L with h1 | h1
    · have hsL : s - L = 0 := tsub_eq_zero_of_le h1.le
      simp only [concatAt, hsL, hq0, add_zero] at hs
      obtain ⟨s', hs'mem, hps'⟩ : ∃ s' ∈ Icc (0 : ℝ≥0) s, p s' = c' :=
        intermediate_value_Icc zero_le hp.continuousOn
          ⟨by rw [hp0]; exact hc'.le, by rw [hs]; linarith⟩
      have := (hitFrom_le (r := 0) zero_le hps').trans (ENNReal.coe_le_coe.2 hs'mem.2)
      rw [hphit] at this
      exact absurd (lt_of_le_of_lt (ENNReal.coe_le_coe.1 this) h1) (lt_irrefl _)
    · have hps := hpconst s h1
      simp only [concatAt, hps] at hs
      have hqs : q (s - L) = a := by linarith
      have := hitFrom_le (r := 0) zero_le hqs
      rw [hqhit] at this
      have h2 : e ≤ s - L := ENNReal.coe_le_coe.1 this
      exact absurd ((le_tsub_iff_left h1).1 h2) (not_le.2 hlt)
  have hlo : ((L + e : ℝ≥0) : ℝ≥0∞) ≤ hitFrom (c' + a) 0 (concatAt L p q) :=
    le_iInf₂ fun s hs => ENNReal.coe_le_coe.2 (hlow s hs.2)
  exact le_antisymm hup hlo

/-- **Reversal of a concatenation.**  The reversal of the concatenation of `p` and `q` is the
reversal of `q` followed by the reversal of `p`. -/
theorem upcrossRev_concatAt_of_hit {c' a : ℝ} (hc' : 0 < c') (ha : 0 < a) {L e : ℝ≥0}
    {p q : ℝ≥0 → ℝ} (hp : Continuous p) (hp0 : p 0 = 0) (hphit : hitFrom c' 0 p = L)
    (hpconst : ∀ t, L ≤ t → p t = c') (hq : Continuous q) (hq0 : q 0 = 0)
    (hqhit : hitFrom a 0 q = e) :
    upcrossRev (c' + a) (concatAt L p q) = concatAt e (revLevel a e q) (upcrossRev c' p) := by
  have hG := hitFrom_concatAt_of_hit hc' ha hp hp0 hphit hpconst hq hq0 hqhit
  have hpL : p L = c' := hpconst L le_rfl
  funext s
  simp only [upcrossRev, hG, hphit, ENNReal.toNNReal_coe, concatAt, revLevel]
  rcases le_total s e with hse | hes
  · have h1 : L ≤ L + e - s := by
      rw [add_tsub_assoc_of_le hse]; exact le_self_add
    have h2 : L + e - s - L = e - s := by
      rw [add_tsub_assoc_of_le hse, add_tsub_cancel_left]
    rw [hpconst _ h1, h2, tsub_eq_zero_of_le hse, tsub_zero, hpL]
    ring
  · have h1 : L + e - s ≤ L := by
      rw [tsub_le_iff_right]; exact add_le_add le_rfl hes
    have h2 : L + e - s - L = 0 := tsub_eq_zero_of_le h1
    have h3 : L + e - s = L - (s - e) := by
      have := tsub_tsub_tsub_cancel_right (a := L + e) hes
      rw [add_tsub_cancel_right] at this
      exact this.symm
    rw [h2, hq0, tsub_eq_zero_of_le hes, hq0, h3]
    ring

end LatticeProb
