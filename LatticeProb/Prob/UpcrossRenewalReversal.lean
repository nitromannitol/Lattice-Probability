import Mathlib
import LatticeProb.Prob.UpcrossReversalConcat
import LatticeProb.Prob.UpcrossGlueMeasure
import LatticeProb.Prob.UpcrossDriftLawNeg

/-!
# Reversing a concatenation of a first up-crossing piece and a successful second leg

For levels `0 < c'`, `0 < a` and a path `u` from `0` hitting `c'` and a path `v` from `0` that hits
`a` before `-c'`, the reversal at level `c' + a` of the first up-crossing piece to `c'` of `u`
followed by the second leg of `v` is the reversal of `v` (from its first hit of `a`) followed by the
reversal of the first up-crossing piece of `u`.  We also record the measurable dependence of this
reversed path on the pair `(u, v)`.
-/

open MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

section Pieces

variable {w : ℝ≥0 → ℝ}

lemma continuous_firstUpcrossPiece (hw : Continuous w) (c : ℝ) :
    Continuous (firstUpcrossPiece c w) := by
  unfold firstUpcrossPiece pieceAt
  exact hw.comp ((continuous_const.add continuous_id).min continuous_const)

lemma continuous_upcrossRev {p : ℝ≥0 → ℝ} (hp : Continuous p) (c : ℝ) :
    Continuous (upcrossRev c p) := by
  unfold upcrossRev revLevel
  exact continuous_const.sub (hp.comp (continuous_const.sub continuous_id))

/-- The time reversal of the first up-crossing piece to `c`, as a continuous path. -/
def revPieceC (c : ℝ) (w : C(ℝ≥0, ℝ)) : C(ℝ≥0, ℝ) :=
  ⟨upcrossRev c (firstUpcrossPiece c (w : ℝ≥0 → ℝ)),
    continuous_upcrossRev (continuous_firstUpcrossPiece w.continuous c) c⟩

lemma measurable_revPieceC {c : ℝ} (hc : 0 < c) : Measurable (revPieceC c) := by
  rw [ContinuousMap.measurable_iff_eval]
  intro s
  exact (measurable_pi_apply s).comp (measurable_upcrossRev_firstUpcrossPiece hc)

end Pieces

section Stopped

/-- Stopping a path at its first hit of a level that it reaches does not change that first hit. -/
lemma hitFrom_stopAt_hit {a : ℝ} {v : C(ℝ≥0, ℝ)} (hT : hitFrom a 0 (v : ℝ≥0 → ℝ) ≠ ⊤) :
    hitFrom a 0 (stopAt (hitFrom a 0 (v : ℝ≥0 → ℝ)) v : ℝ≥0 → ℝ) = hitFrom a 0 (v : ℝ≥0 → ℝ) := by
  obtain ⟨e, he, -, hve, hmin⟩ := exists_hitFrom_eq v.continuous hT
  rw [he]
  apply le_antisymm
  · refine hitFrom_le (r := 0) zero_le ?_
    rw [stopAt_apply_of_le le_rfl v le_rfl]; exact hve
  · refine le_iInf₂ fun s hs => ENNReal.coe_le_coe.2 ?_
    by_contra hlt
    rw [not_le] at hlt
    have h1 : stopAt (e : ℝ≥0∞) v s = v s := stopAt_apply_of_le le_rfl v hlt.le
    exact absurd (hmin s zero_le (h1 ▸ hs.2)) (not_le.2 hlt)

/-- On the success event the second leg is the second leg stopped at its first hit of `a`. -/
lemma legStop_eq_stopAt_hit {c' a : ℝ} {v : C(ℝ≥0, ℝ)} (hv : v ∈ legSuccess c' (c' + a)) :
    legStop c' (c' + a) v = stopAt (hitFrom a 0 (v : ℝ≥0 → ℝ)) v := by
  have hv' : hitFrom a 0 (v : ℝ≥0 → ℝ) < hitFrom (-c') 0 (v : ℝ≥0 → ℝ) := by
    have := hv
    simp only [legSuccess, Set.mem_ofPred_eq, add_sub_cancel_left] at this
    exact this
  unfold legStop exitFrom
  rw [add_sub_cancel_left, min_eq_right hv'.le]

end Stopped

/-- **Reversal of the concatenation of a first up-crossing piece and a successful leg.** -/
theorem upcrossRev_concat_legStop {c' a : ℝ} (hc' : 0 < c') (ha : 0 < a) {u v : C(ℝ≥0, ℝ)}
    (hE : upcrossEnd₁ c' (u : ℝ≥0 → ℝ) ≠ ⊤) (hv0 : v 0 = 0)
    (hv : v ∈ legSuccess c' (c' + a)) :
    upcrossRev (c' + a) (concatAt (upcrossLen c' (u : ℝ≥0 → ℝ))
        (firstUpcrossPiece c' (u : ℝ≥0 → ℝ)) (legStop c' (c' + a) v : ℝ≥0 → ℝ)) =
      glueFun a (-(v : ℝ≥0 → ℝ)) (upcrossRev c' (firstUpcrossPiece c' (u : ℝ≥0 → ℝ))) := by
  have hv' : hitFrom a 0 (v : ℝ≥0 → ℝ) < hitFrom (-c') 0 (v : ℝ≥0 → ℝ) := by
    have := hv
    simp only [legSuccess, Set.mem_ofPred_eq, add_sub_cancel_left] at this
    exact this
  have hT : hitFrom a 0 (v : ℝ≥0 → ℝ) ≠ ⊤ := ne_top_of_lt hv'
  have hleg := legStop_eq_stopAt_hit hv
  obtain ⟨e, he, -, -, -⟩ := exists_hitFrom_eq v.continuous hT
  obtain ⟨d, hd, hup, -⟩ := isUpcross_upcrossStart₁ u.continuous hc' hE
  obtain ⟨hgd, hg0, hdc, -⟩ := hup
  set g := upcrossStart₁ c' (u : ℝ≥0 → ℝ) with hg
  have hdd : (upcrossEnd₁ c' (u : ℝ≥0 → ℝ)).toNNReal = d := by rw [hd]; rfl
  have hpiece : firstUpcrossPiece c' (u : ℝ≥0 → ℝ) = pieceAt u g d := by
    unfold firstUpcrossPiece; rw [hdd]
  have hlen : upcrossLen c' (u : ℝ≥0 → ℝ) = d - g := by unfold upcrossLen; rw [hdd]
  have hp := continuous_firstUpcrossPiece u.continuous c'
  have hp0 : firstUpcrossPiece c' (u : ℝ≥0 → ℝ) 0 = 0 := by
    rw [hpiece]; simp only [pieceAt, add_zero, min_eq_left hgd.le]; exact hg0
  have hpconst : ∀ t, upcrossLen c' (u : ℝ≥0 → ℝ) ≤ t →
      firstUpcrossPiece c' (u : ℝ≥0 → ℝ) t = c' := by
    intro t ht
    rw [hlen] at ht
    have h1 : d ≤ g + t := by
      have := add_le_add le_rfl ht (a := g)
      rwa [add_tsub_cancel_of_le hgd.le] at this
    rw [hpiece]; simp only [pieceAt, min_eq_right h1]; exact hdc
  have hphit := hitFrom_firstUpcrossPiece u.continuous hc' hE
  have hqhit : hitFrom a 0 (legStop c' (c' + a) v : ℝ≥0 → ℝ) = (e : ℝ≥0∞) := by
    rw [hleg]; exact (hitFrom_stopAt_hit hT).trans he
  have hq0 : (legStop c' (c' + a) v : ℝ≥0 → ℝ) 0 = 0 := by
    rw [hleg, stopAt_apply]; simpa using hv0
  rw [upcrossRev_concatAt_of_hit hc' ha hp hp0 hphit hpconst (legStop c' (c' + a) v).continuous hq0
    hqhit]
  have hrev : revLevel a e (legStop c' (c' + a) v : ℝ≥0 → ℝ) = revLevel a e (-(-(v : ℝ≥0 → ℝ))) := by
    funext s
    simp only [revLevel, neg_neg]
    rw [hleg, he, stopAt_apply_of_le (s₀ := e) le_rfl v tsub_le_self]
  simp only [glueFun, glueTime, hitFrom_neg, he, ENNReal.toNNReal_coe]
  rw [hrev]

lemma coe_glueC_neg_revPieceC (a c' : ℝ) (u v : C(ℝ≥0, ℝ)) :
    (glueC a (-v) (revPieceC c' u) : ℝ≥0 → ℝ) =
      glueFun a (-(v : ℝ≥0 → ℝ)) (upcrossRev c' (firstUpcrossPiece c' (u : ℝ≥0 → ℝ))) := rfl

/-- The functional of `(u, v)`: `F` of the reversed path glued from `v` and the reversed first
up-crossing piece of `u`, on the event that the second leg `v` succeeds. -/
def reflGlueFunctional (c' a : ℝ) (F : (ℝ≥0 → ℝ) → ℝ≥0∞) (x : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) : ℝ≥0∞ :=
  open scoped Classical in
  if x.2 ∈ legSuccess c' (c' + a) then F (glueC a (-x.2) (revPieceC c' x.1) : ℝ≥0 → ℝ) else 0

theorem measurable_reflGlueFunctional {c' : ℝ} (hc' : 0 < c') (a : ℝ) {F : (ℝ≥0 → ℝ) → ℝ≥0∞}
    (hF : Measurable F) : Measurable (reflGlueFunctional c' a F) := by
  have hcoe : Measurable fun f : C(ℝ≥0, ℝ) => (f : ℝ≥0 → ℝ) :=
    measurable_pi_iff.2 fun s => (continuous_eval_const s).measurable
  have h1 : Measurable fun x : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) => -x.2 :=
    measurable_neg_pathSpace.comp measurable_snd
  have h2 : Measurable fun x : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) => revPieceC c' x.1 :=
    (measurable_revPieceC hc').comp measurable_fst
  have h3 := (measurable_glueC a).comp (h1.prodMk h2)
  have h4 : Measurable fun x : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) =>
      F (glueC a (-x.2) (revPieceC c' x.1) : ℝ≥0 → ℝ) := hF.comp (hcoe.comp h3)
  have h5 : MeasurableSet {x : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) | x.2 ∈ legSuccess c' (c' + a)} :=
    measurable_snd (measurableSet_legSuccess c' (c' + a))
  unfold reflGlueFunctional
  exact Measurable.ite h5 h4 measurable_const

/-- Away from the exceptional paths, the glued functional is the concatenation functional of the
reversal at level `c' + a`. -/
theorem reflGlueFunctional_eq_concatFunctional {c' a : ℝ} (hc' : 0 < c') (ha : 0 < a)
    (F : (ℝ≥0 → ℝ) → ℝ≥0∞) {x : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)}
    (hE : upcrossEnd₁ c' (x.1 : ℝ≥0 → ℝ) ≠ ⊤) (hv0 : x.2 0 = 0) :
    reflGlueFunctional c' a F x =
      concatFunctional c' (c' + a) (fun p => F (upcrossRev (c' + a) p)) x := by
  unfold reflGlueFunctional concatFunctional
  by_cases hv : x.2 ∈ legSuccess c' (c' + a)
  · simp only [hv, ite_true]
    rw [upcrossRev_concat_legStop hc' ha hE hv0 hv, coe_glueC_neg_revPieceC]
  · simp only [hv, ite_false]

end LatticeProb
