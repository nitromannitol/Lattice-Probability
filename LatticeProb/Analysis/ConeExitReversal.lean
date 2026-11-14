import LatticeProb.Analysis.FirstDropAfterExcursion

/-!
# Time reversal of cone exit times

Negating time exchanges a first strict exit after a base time with the last
strict exit before it. The same identity holds for the joint exit at which
both coordinates have dropped, possibly at different times.
-/

open Set

namespace LatticeProb

/-- The first strict exit of either reversed coordinate is the negative of the
last strict exit of either original coordinate. -/
theorem firstEitherDrop_rev (X Y : ℝ → ℝ) (s : ℝ) :
    sInf {t : ℝ | -s < t ∧ (X (-t) < X s ∨ Y (-t) < Y s)} =
      -sSup {t : ℝ | t < s ∧ (X t < X s ∨ Y t < Y s)} := by
  rw [Real.sInf_def]
  apply congrArg Neg.neg
  apply congrArg sSup
  ext t
  simp only [mem_ofPred_eq, mem_neg, neg_neg, neg_lt_neg_iff]

/-- The first joint strict exit of the reversed coordinates is the negative of
the last joint strict exit of the original coordinates. -/
theorem jointDrop_rev (X Y : ℝ → ℝ) (s : ℝ) :
    sInf {t : ℝ | -s < t ∧ (∃ r ∈ Icc (-s) t, X (-r) < X s) ∧
      (∃ r ∈ Icc (-s) t, Y (-r) < Y s)} =
    -sSup {t : ℝ | t < s ∧ (∃ r ∈ Icc t s, X r < X s) ∧
      (∃ r ∈ Icc t s, Y r < Y s)} := by
  rw [Real.sInf_def]
  apply congrArg Neg.neg
  apply congrArg sSup
  ext t
  simp only [mem_ofPred_eq, mem_neg, neg_lt_neg_iff]
  constructor
  · rintro ⟨ht, ⟨r, hr, hx⟩, q, hq, hy⟩
    refine ⟨ht, ⟨-r, ?_, by simpa using hx⟩, -q, ?_, by simpa using hy⟩
    · exact ⟨by linarith [hr.2], by linarith [hr.1]⟩
    · exact ⟨by linarith [hq.2], by linarith [hq.1]⟩
  · rintro ⟨ht, ⟨r, hr, hx⟩, q, hq, hy⟩
    refine ⟨ht, ⟨-r, ?_, by simpa using hx⟩, -q, ?_, by simpa using hy⟩
    · exact ⟨by linarith [hr.2], by linarith [hr.1]⟩
    · exact ⟨by linarith [hq.2], by linarith [hq.1]⟩

end LatticeProb
