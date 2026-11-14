import LatticeProb.Prob.ConeVectorDirectPairCover
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Dimension of direct-excursion pairs

A common dimension bound for the forward and backward cone vectors of a path
and its time reversal transfers to pairs of distinct excursion partners.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped ENNReal
open MatedCRTHarmonic.MatedCRT (DirectRel lrCoord Path2 IsCorrelatedBM2)

namespace LatticeProb

/-- Four cone-vector dimension bounds and countability of the exceptional
pairs imply the same dimension bound for the direct-excursion pairs. -/
theorem dimH_direct_excursion_pairs_le_of_coneVectors (X Y : ℝ → ℝ) {d : ℝ≥0∞}
    (he : {p : ℝ × ℝ | ∃ a b,
      ((DirectRel X p.1 a ∧ DirectRel Y p.1 b) ∨
       (DirectRel X a p.1 ∧ DirectRel Y b p.1)) ∧
      (IsLocalMin X a ∨ IsLocalMin Y b) ∧
      (p.2 = p.1 ∨ p.2 = a ∨ p.2 = b)}.Countable)
    (hf : dimH (forwardConeVectors X Y) ≤ d)
    (hb : dimH (backwardConeVectors X Y) ≤ d)
    (hfr : dimH (forwardConeVectors (fun t => X (-t)) (fun t => Y (-t))) ≤ d)
    (hbr : dimH (backwardConeVectors (fun t => X (-t)) (fun t => Y (-t))) ≤ d) :
    dimH {p : ℝ × ℝ | ∃ a b, a ≠ b ∧
      ((DirectRel X p.1 a ∧ DirectRel Y p.1 b) ∨
       (DirectRel X a p.1 ∧ DirectRel Y b p.1)) ∧
      (p.2 = a ∨ p.2 = b)} ≤ d := by
  have hs : LipschitzWith 1 (fun p : ℝ × ℝ => (p.2, p.1)) := by
    simpa only [max_self] using
      (LipschitzWith.prod_snd.prodMk LipschitzWith.prod_fst :
        LipschitzWith (max 1 1) (fun p : ℝ × ℝ => (p.2, p.1)))
  have hn : LipschitzWith 1 (fun p : ℝ × ℝ => (-p.2, -p.1)) := by
    simpa only [max_self, Pi.neg_apply] using
      (LipschitzWith.prod_snd.neg.prodMk LipschitzWith.prod_fst.neg :
        LipschitzWith (max 1 1) (fun p : ℝ × ℝ => (-p.2, -p.1)))
  apply (dimH_mono (direct_excursion_pairs_subset_coneVectors X Y)).trans
  rw [dimH_union, dimH_union, dimH_union, dimH_union]
  exact max_le (max_le (max_le (max_le (he.dimH_zero ▸ bot_le)
    ((hs.dimH_image_le _).trans hf)) ((hs.dimH_image_le _).trans hb))
    ((hn.dimH_image_le _).trans hfr)) ((hn.dimH_image_le _).trans hbr)

/-- Under four almost-sure cone-vector bounds, correlated Brownian direct
excursion pairs satisfy the same almost-sure dimension bound. -/
theorem CorrelatedBM.ae_dimH_direct_excursion_pairs_le_of_coneVectors
    {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) {d : ℝ≥0∞}
    (hf : ∀ᵐ ω ∂μ, dimH (forwardConeVectors (lrCoord 0 · ω) (lrCoord 1 · ω)) ≤ d)
    (hb : ∀ᵐ ω ∂μ, dimH (backwardConeVectors (lrCoord 0 · ω) (lrCoord 1 · ω)) ≤ d)
    (hfr : ∀ᵐ ω ∂μ, dimH (forwardConeVectors
      (fun t => lrCoord 0 (-t) ω) (fun t => lrCoord 1 (-t) ω)) ≤ d)
    (hbr : ∀ᵐ ω ∂μ, dimH (backwardConeVectors
      (fun t => lrCoord 0 (-t) ω) (fun t => lrCoord 1 (-t) ω)) ≤ d) :
    ∀ᵐ ω ∂μ, dimH {p : ℝ × ℝ | ∃ a b, a ≠ b ∧
      ((DirectRel (lrCoord 0 · ω) p.1 a ∧ DirectRel (lrCoord 1 · ω) p.1 b) ∨
       (DirectRel (lrCoord 0 · ω) a p.1 ∧ DirectRel (lrCoord 1 · ω) b p.1)) ∧
      (p.2 = a ∨ p.2 = b)} ≤ d := by
  filter_upwards [CorrelatedBM.ae_countable_localMin_direct_pairs hμ, hf, hb, hfr, hbr] with
    ω he hf hb hfr hbr
  exact dimH_direct_excursion_pairs_le_of_coneVectors _ _ he hf hb hfr hbr

end LatticeProb
