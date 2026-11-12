import Mathlib
import LatticeProb.Prob.UpcrossAttempt
import LatticeProb.Prob.UpcrossLaplace

/-!
# Concatenation of the up-crossing pieces to two levels

For levels `0 < c' < c` and a continuous path `w` started at `0`, the first up-crossing piece to
`c` is, on the event that after the first hit `τ` of `c'` the path reaches `c` before `0`, the
first up-crossing piece to `c'` followed by the increments after `τ` stopped at their exit of
`(-c', c - c')`.  This file records the pathwise identity and the measurability of the
corresponding functional of the pair (path stopped at `τ`, increments after `τ`).

* `LatticeProb.concatAt`: the concatenation `s ↦ p s + q (s - T)`;
* `LatticeProb.upcrossLen`: length of the first up-crossing interval;
* `LatticeProb.legSuccess`, `LatticeProb.legStop`: the second leg;
* `LatticeProb.firstUpcrossPiece_eq_concatAt`: the pathwise decomposition;
* `LatticeProb.concatFunctional_stopAt_shift`: `Φ (w stopped at τ, w after τ)` is the indicator of
  the success event times `f (piece_c w)`;
* `LatticeProb.measurable_concatFunctional`: measurability on `C × C`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

/-- The path `p` followed by the path `q`, which starts at time `T`: `s ↦ p s + q (s - T)`. -/
def concatAt (T : ℝ≥0) (p q : ℝ≥0 → ℝ) : ℝ≥0 → ℝ := fun s => p s + q (s - T)

/-- The length `d₁ - g₁` of the first up-crossing interval. -/
def upcrossLen (c : ℝ) (w : ℝ≥0 → ℝ) : ℝ≥0 := (upcrossEnd₁ c w).toNNReal - upcrossStart₁ c w

/-- The second leg succeeds: the increments hit `c - c'` before `-c'`. -/
def legSuccess (c' c : ℝ) : Set C(ℝ≥0, ℝ) :=
  {v | hitFrom (c - c') 0 (v : ℝ≥0 → ℝ) < hitFrom (-c') 0 (v : ℝ≥0 → ℝ)}

/-- The second leg stopped at its exit of `(-c', c - c')`. -/
def legStop (c' c : ℝ) (v : C(ℝ≥0, ℝ)) : C(ℝ≥0, ℝ) :=
  stopAt (exitFrom (-c') (c - c') 0 (v : ℝ≥0 → ℝ)) v

section Pathwise

variable {w : ℝ≥0 → ℝ} {c c' : ℝ}

/-- The first hit of `c` by the first up-crossing piece to `c` is its length. -/
lemma hitFrom_firstUpcrossPiece (hw : Continuous w) (hc : 0 < c) (h : upcrossEnd₁ c w ≠ ⊤) :
    hitFrom c 0 (firstUpcrossPiece c w) = (upcrossLen c w : ℝ≥0∞) := by
  obtain ⟨d, hd, hup, -⟩ := isUpcross_upcrossStart₁ hw hc h
  have hdd : (upcrossEnd₁ c w).toNNReal = d := by rw [hd]; rfl
  set g := upcrossStart₁ c w with hg
  have hpiece : firstUpcrossPiece c w = pieceAt w g d := by
    unfold firstUpcrossPiece; rw [hdd]
  have hlen : upcrossLen c w = d - g := by unfold upcrossLen; rw [hdd]
  rw [hpiece, hlen]
  obtain ⟨hgd, hg0, hdc, hmid⟩ := hup
  apply le_antisymm
  · refine hitFrom_le (r := 0) zero_le ?_
    simp only [pieceAt]
    rw [add_tsub_cancel_of_le hgd.le, min_self, hdc]
  · refine le_iInf₂ fun s hs => ?_
    refine ENNReal.coe_le_coe.2 ?_
    by_contra hlt
    rw [not_le] at hlt
    have hgs : g + s < d := by
      calc g + s < g + (d - g) := by gcongr
        _ = d := add_tsub_cancel_of_le hgd.le
    have hsc : w (g + s) = c := by
      have := hs.2
      simpa [pieceAt, min_eq_left hgs.le] using this
    rcases eq_or_ne s 0 with rfl | hs0
    · rw [add_zero, hg0] at hsc
      exact hc.ne hsc
    · have hgs' : g < g + s := by
        exact lt_add_of_pos_right g (pos_iff_ne_zero.2 hs0)
      exact (hmid _ hgs' hgs).2.ne hsc

/-- Stopping a path at the end `d₁` of its first up-crossing interval keeps `d₁` and the start
`g₁` of that interval. -/
lemma upcross_stopAt (hc : 0 < c) {w : C(ℝ≥0, ℝ)} {D : ℝ≥0}
    (hD : upcrossEnd₁ c (w : ℝ≥0 → ℝ) = D) :
    upcrossEnd₁ c (stopAt (D : ℝ≥0∞) w : ℝ≥0 → ℝ) = D ∧
      upcrossStart₁ c (stopAt (D : ℝ≥0∞) w : ℝ≥0 → ℝ) = upcrossStart₁ c (w : ℝ≥0 → ℝ) := by
  have e1 : upcrossEnd₁ c (stopAt (D : ℝ≥0∞) w : ℝ≥0 → ℝ) = D :=
    ((isStopFun_upcrossEnd₁ c w D).1 hD.le).trans hD
  refine ⟨e1, ?_⟩
  obtain ⟨d, hd, hup, -⟩ := isUpcross_upcrossStart₁ w.continuous hc
    (by rw [hD]; exact ENNReal.coe_ne_top)
  have hdD : d = D := by rw [hD] at hd; exact_mod_cast hd.symm
  rw [hdD] at hup
  have hup' : IsUpcross c (stopAt (D : ℝ≥0∞) w : ℝ≥0 → ℝ) (upcrossStart₁ c (w : ℝ≥0 → ℝ)) D :=
    hup.congr fun s hs => (stopAt_coe_of_le w hs).symm
  obtain ⟨d', hd', hup'', -⟩ := isUpcross_upcrossStart₁ (stopAt (D : ℝ≥0∞) w).continuous hc
    (by rw [e1]; exact ENNReal.coe_ne_top)
  have hdD' : d' = D := by rw [e1] at hd'; exact_mod_cast hd'.symm
  rw [hdD'] at hup''
  exact isUpcross_start_unique hup'' hup'

/-- First hits after the first hit time `T` of `c'`, read on the increments after `T`. -/
lemma hitFrom_at_first_hit {w : C(ℝ≥0, ℝ)} {T : ℝ≥0} {c' : ℝ} (hwT : w T = c') (a : ℝ) :
    hitFrom a (T : ℝ≥0∞) (w : ℝ≥0 → ℝ) =
      T + hitFrom (a - c') 0 (shiftPath T w : ℝ≥0 → ℝ) := by
  have h := hitFrom_add_coe a T 0 (w : ℝ≥0 → ℝ)
  rw [add_zero] at h
  have e : a - w T = a - c' := by rw [hwT]
  rw [e] at h
  exact h

/-- Success of the attempt, read on the increments after the first hit of `c'`. -/
lemma mem_attemptSuccess_iff_shift {w : C(ℝ≥0, ℝ)}
    (hτ : hitFrom c' 0 (w : ℝ≥0 → ℝ) ≠ ⊤) :
    w ∈ attemptSuccess c' c ↔
      shiftPath (hitFrom c' 0 (w : ℝ≥0 → ℝ)).toNNReal w ∈ legSuccess c' c := by
  obtain ⟨T, hτT, -, hwT, -⟩ := exists_hitFrom_eq w.continuous hτ
  simp only [attemptSuccess, legSuccess, Set.mem_ofPred_eq, hτT, ENNReal.toNNReal_coe]
  rw [hitFrom_at_first_hit hwT c, hitFrom_at_first_hit hwT 0, zero_sub]
  exact ENNReal.add_lt_add_iff_left ENNReal.coe_ne_top

/-- **Pathwise decomposition at the first hit of `c'`.**  For `0 < c' < c` and a continuous path
`w` started at `0` which, after its first hit of `c'`, hits `c` before `0`, the first up-crossing
piece to `c` is the first up-crossing piece to `c'` followed by the increments after the first
hit of `c'`, stopped at their exit of `(-c', c - c')`. -/
theorem firstUpcrossPiece_eq_concatAt {w : C(ℝ≥0, ℝ)} (hw0 : w 0 = 0) (hc' : 0 < c')
    (hcc : c' < c) (hS : w ∈ attemptSuccess c' c) :
    firstUpcrossPiece c (w : ℝ≥0 → ℝ) =
      concatAt (upcrossLen c' (w : ℝ≥0 → ℝ)) (firstUpcrossPiece c' (w : ℝ≥0 → ℝ))
        (legStop c' c (shiftPath (hitFrom c' 0 (w : ℝ≥0 → ℝ)).toNNReal w) : ℝ≥0 → ℝ) := by
  have hw := w.continuous
  have hc : 0 < c := hc'.trans hcc
  have hτ : hitFrom c' 0 (w : ℝ≥0 → ℝ) ≠ ⊤ := by
    intro h
    have : hitFrom c (hitFrom c' 0 (w : ℝ≥0 → ℝ)) (w : ℝ≥0 → ℝ) <
        hitFrom 0 (hitFrom c' 0 (w : ℝ≥0 → ℝ)) (w : ℝ≥0 → ℝ) := hS
    rw [h, hitFrom_top, hitFrom_top] at this
    exact lt_irrefl _ this
  have hSshift := (mem_attemptSuccess_iff_shift hτ).1 hS
  obtain ⟨T, hτT, -, hwT, hminT⟩ := exists_hitFrom_eq hw hτ
  have hS' : hitFrom c (T : ℝ≥0∞) (w : ℝ≥0 → ℝ) < hitFrom 0 (T : ℝ≥0∞) (w : ℝ≥0 → ℝ) := by
    have : hitFrom c (hitFrom c' 0 (w : ℝ≥0 → ℝ)) (w : ℝ≥0 → ℝ) <
        hitFrom 0 (hitFrom c' 0 (w : ℝ≥0 → ℝ)) (w : ℝ≥0 → ℝ) := hS
    rwa [hτT] at this
  obtain ⟨R, hρR, hTR, hwR, hminR⟩ := exists_hitFrom_eq hw hS'.ne_top
  have hTR' : T ≤ R := by exact_mod_cast hTR
  rw [hρR] at hS'
  have hTle : ∀ s : ℝ≥0, w s = c → T ≤ s := fun s hs => by
    have := hitFrom_mid_le hw hw0 hc' hcc hs
    rw [hτT] at this
    exact_mod_cast this
  have hc0 : hitFrom c 0 (w : ℝ≥0 → ℝ) = R := by
    apply le_antisymm
    · exact hitFrom_le (r := 0) zero_le hwR
    · refine le_iInf₂ fun s hs => ?_
      exact_mod_cast hminR s (by exact_mod_cast hTle s hs.2) hs.2
  have hnozero : ∀ s : ℝ≥0, T ≤ s → s ≤ R → w s ≠ 0 := by
    intro s hTs hsR hws
    have h1 : hitFrom 0 (T : ℝ≥0∞) (w : ℝ≥0 → ℝ) ≤ s := hitFrom_le (by exact_mod_cast hTs) hws
    have h2 : (s : ℝ≥0∞) ≤ R := by exact_mod_cast hsR
    exact absurd h2 (not_le.2 (lt_of_lt_of_le hS' h1))
  have hend : upcrossEnd₁ c (w : ℝ≥0 → ℝ) = R := by
    rw [upcrossEnd₁_of_zero_start hw0]; exact hc0
  have hend' : upcrossEnd₁ c' (w : ℝ≥0 → ℝ) = T := by
    rw [upcrossEnd₁_of_zero_start hw0]; exact hτT
  have hupc : IsUpcross c (w : ℝ≥0 → ℝ) (lastZeroBefore w R) R :=
    isUpcross_lastZeroBefore hw hc hw0 hwR zero_le fun s _ hs => hminR s
      (by exact_mod_cast hTle s hs) hs
  set g := lastZeroBefore (w : ℝ≥0 → ℝ) R with hg
  have hgT : g < T := by
    by_contra hTg
    rw [not_lt] at hTg
    exact hnozero g hTg hupc.1.le hupc.2.1
  have hupc' : IsUpcross c' (w : ℝ≥0 → ℝ) g T := by
    refine ⟨hgT, hupc.2.1, hwT, fun s hgs hsT => ⟨(hupc.2.2.2 s hgs (hsT.trans_le hTR')).1, ?_⟩⟩
    refine forall_lt_of_forall_ne hw (by rw [hw0]; exact hc') (T := s) (fun s'' hs'' hws'' => ?_)
      s le_rfl
    exact absurd (hminT s'' zero_le hws'') (by
      rw [not_le]; exact lt_of_le_of_lt hs'' hsT)
  have hstart' : upcrossStart₁ c' (w : ℝ≥0 → ℝ) = g := by
    obtain ⟨d, hd, hupT, -⟩ := isUpcross_upcrossStart₁ hw hc' (by rw [hend']; exact ENNReal.coe_ne_top)
    have hdT : d = T := by rw [hend'] at hd; exact_mod_cast hd.symm
    rw [hdT] at hupT
    exact isUpcross_start_unique hupT hupc'
  have hstart : upcrossStart₁ c (w : ℝ≥0 → ℝ) = g := by
    unfold upcrossStart₁; rw [hend]; rfl
  have hpc : firstUpcrossPiece c (w : ℝ≥0 → ℝ) = pieceAt w g R := by
    unfold firstUpcrossPiece; rw [hend, hstart, ENNReal.toNNReal_coe]
  have hpc' : firstUpcrossPiece c' (w : ℝ≥0 → ℝ) = pieceAt w g T := by
    unfold firstUpcrossPiece; rw [hend', hstart', ENNReal.toNNReal_coe]
  have hlen : upcrossLen c' (w : ℝ≥0 → ℝ) = T - g := by
    unfold upcrossLen; rw [hend', hstart', ENNReal.toNNReal_coe]
  -- the second leg
  rw [hτT, ENNReal.toNNReal_coe] at hSshift ⊢
  have h1 := hitFrom_at_first_hit hwT c
  rw [hρR] at h1
  have hlt : hitFrom (c - c') 0 (shiftPath T w : ℝ≥0 → ℝ) <
      hitFrom (-c') 0 (shiftPath T w : ℝ≥0 → ℝ) := hSshift
  have hexit : exitFrom (-c') (c - c') 0 (shiftPath T w : ℝ≥0 → ℝ) =
      hitFrom (c - c') 0 (shiftPath T w : ℝ≥0 → ℝ) := by
    unfold exitFrom; exact min_eq_right hlt.le
  obtain ⟨e, he⟩ : ∃ e : ℝ≥0, hitFrom (c - c') 0 (shiftPath T w : ℝ≥0 → ℝ) = e :=
    ⟨_, (ENNReal.coe_toNNReal hlt.ne_top).symm⟩
  have hRe : R = T + e := by
    have : ((R : ℝ≥0) : ℝ≥0∞) = ((T + e : ℝ≥0) : ℝ≥0∞) := by
      rw [ENNReal.coe_add, ← he]; exact h1
    exact_mod_cast this
  have hleg : (legStop c' c (shiftPath T w) : ℝ≥0 → ℝ) = fun u => w (T + min u e) - w T := by
    funext u
    unfold legStop
    rw [hexit, he, stopAt_coe]
    rfl
  subst hRe
  rw [hpc, hpc']
  funext s
  simp only [concatAt, pieceAt, hleg, hlen, hwT]
  by_cases hs : s ≤ T - g
  · have h0 : s - (T - g) = 0 := tsub_eq_zero_of_le hs
    have hgs : g + s ≤ T := by
      calc g + s ≤ g + (T - g) := by gcongr
        _ = T := add_tsub_cancel_of_le hgT.le
    rw [h0, min_eq_left (hgs.trans le_self_add), min_eq_left hgs, min_eq_left (by simp : (0 : ℝ≥0) ≤ e),
      add_zero, hwT, sub_self, add_zero]
  · rw [not_le] at hs
    obtain ⟨k, rfl⟩ : ∃ k, s = (T - g) + k :=
      ⟨s - (T - g), (add_tsub_cancel_of_le hs.le).symm⟩
    have hgs : g + (T - g + k) = T + k := by
      rw [← add_assoc, add_tsub_cancel_of_le hgT.le]
    rw [hgs, add_tsub_cancel_left, min_add_add_left, min_eq_right (le_self_add : T ≤ T + k), hwT]
    ring

end Pathwise

section Functional

variable {c c' : ℝ}

/-- The functional of the pair (path stopped at the first hit of `c'`, increments after it) which
evaluates `f` on the concatenation of the first up-crossing piece to `c'` with the second leg,
on the event that the second leg succeeds. -/
def concatFunctional (c' c : ℝ) (f : (ℝ≥0 → ℝ) → ℝ≥0∞) (x : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ)) : ℝ≥0∞ :=
  open scoped Classical in
  if x.2 ∈ legSuccess c' c then
    f (concatAt (upcrossLen c' (x.1 : ℝ≥0 → ℝ)) (firstUpcrossPiece c' (x.1 : ℝ≥0 → ℝ))
      (legStop c' c x.2 : ℝ≥0 → ℝ))
  else 0

/-- **Pathwise identity at the first hit of `c'`.**  For a continuous path started at `0` with a
finite first hit `τ` of `c'`, the functional of (the path stopped at `τ`, its increments after
`τ`) is the indicator of the success event times `f` of the first up-crossing piece to `c`. -/
theorem concatFunctional_stopAt_shift (f : (ℝ≥0 → ℝ) → ℝ≥0∞) {w : C(ℝ≥0, ℝ)} (hw0 : w 0 = 0)
    (hc' : 0 < c') (hcc : c' < c) (hτ : hitFrom c' 0 (w : ℝ≥0 → ℝ) ≠ ⊤) :
    concatFunctional c' c f (stopAt (hitFrom c' 0 (w : ℝ≥0 → ℝ)) w,
        shiftPath (hitFrom c' 0 (w : ℝ≥0 → ℝ)).toNNReal w) =
      (attemptSuccess c' c).indicator
        (fun w : C(ℝ≥0, ℝ) => f (firstUpcrossPiece c (w : ℝ≥0 → ℝ))) w := by
  obtain ⟨T, hτT, -, hwT, -⟩ := exists_hitFrom_eq w.continuous hτ
  have hend' : upcrossEnd₁ c' (w : ℝ≥0 → ℝ) = T := by
    rw [upcrossEnd₁_of_zero_start hw0]; exact hτT
  obtain ⟨hE, hSt⟩ := upcross_stopAt hc' hend'
  have hpiece := firstUpcrossPiece_stopAt c' w hend'
  have hlen : upcrossLen c' (stopAt (T : ℝ≥0∞) w : ℝ≥0 → ℝ) = upcrossLen c' (w : ℝ≥0 → ℝ) := by
    unfold upcrossLen; rw [hE, hSt, hend']
  have hmem : shiftPath T w ∈ legSuccess c' c ↔ w ∈ attemptSuccess c' c := by
    have := (mem_attemptSuccess_iff_shift (c := c) hτ).symm
    rwa [hτT, ENNReal.toNNReal_coe] at this
  rw [hτT, ENNReal.toNNReal_coe]
  unfold concatFunctional
  by_cases hS : w ∈ attemptSuccess c' c
  · rw [Set.indicator_of_mem hS]
    have key := firstUpcrossPiece_eq_concatAt hw0 hc' hcc hS
    rw [hτT, ENNReal.toNNReal_coe] at key
    simp only [hmem.2 hS, ite_true]
    rw [hlen, hpiece, key]
  · rw [Set.indicator_of_notMem hS]
    simp only [mt hmem.1 hS, ite_false]

lemma measurableSet_legSuccess (c' c : ℝ) : MeasurableSet (legSuccess c' c) :=
  measurableSet_lt (measurable_hitFrom (r := fun _ => 0) measurable_const (c - c'))
    (measurable_hitFrom (r := fun _ => 0) measurable_const (-c'))

lemma measurable_legStop (c' c : ℝ) : Measurable (legStop c' c) := by
  refine measurable_pathValued_of_eval fun s => ?_
  have hρ : Measurable fun v : C(ℝ≥0, ℝ) => exitFrom (-c') (c - c') 0 (v : ℝ≥0 → ℝ) :=
    measurable_exitFrom (r := fun _ => 0) measurable_const _ _
  exact measurable_eval_comp (τ := fun v => (min (s : ℝ≥0∞)
    (exitFrom (-c') (c - c') 0 (v : ℝ≥0 → ℝ))).toNNReal) (measurable_const.min hρ).ennreal_toNNReal

lemma measurable_upcrossLen (c : ℝ) :
    Measurable fun w : C(ℝ≥0, ℝ) => upcrossLen c (w : ℝ≥0 → ℝ) :=
  (measurable_upcrossEnd₁ c).ennreal_toNNReal.sub (measurable_upcrossStart₁ c)

/-- The functional is measurable on `C × C` for measurable `f`. -/
theorem measurable_concatFunctional (c' c : ℝ) {f : (ℝ≥0 → ℝ) → ℝ≥0∞} (hf : Measurable f) :
    Measurable (concatFunctional c' c f) := by
  unfold concatFunctional
  refine Measurable.ite (measurable_snd (measurableSet_legSuccess c' c)) ?_ measurable_const
  refine hf.comp (measurable_pi_iff.2 fun s => ?_)
  have h1 : Measurable fun x : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) => firstUpcrossPiece c' (x.1 : ℝ≥0 → ℝ) s :=
    ((measurable_pi_apply s).comp (measurable_firstUpcrossPiece c')).comp measurable_fst
  have h2 : Measurable fun x : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) => (legStop c' c x.2 : ℝ≥0 → ℝ)
      (s - upcrossLen c' (x.1 : ℝ≥0 → ℝ)) :=
    (continuous_eval : Continuous fun p : C(ℝ≥0, ℝ) × ℝ≥0 => p.1 p.2).measurable.comp
      (((measurable_legStop c' c).comp measurable_snd).prodMk
        (measurable_const.sub ((measurable_upcrossLen c').comp measurable_fst)))
  exact h1.add h2

end Functional

end LatticeProb
