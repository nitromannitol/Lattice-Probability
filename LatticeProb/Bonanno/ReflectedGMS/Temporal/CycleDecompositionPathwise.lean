/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.CycleDecompositionPathwise at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.FirstCycleLaw

/-!
# The cycle decomposition of the re-rooted two-sided path, pathwise (milestone 2(c), part 1)

For a two-sided regular pair `p = (x⁺, x⁻)` whose two halves both start at `v` and are the
concatenations of their successive complete cycles `cP k`, `cM k`
(`cP k = firstCycle v (nx^[k] x⁺)`, `nx` = shift to the first complete return), the re-rooted
pair `ρ p` is the splice of the two-sided cycle sequence

  `assemble cP cM j = cP (j + 1)`                                     (`j ≥ 0`),
  `assemble cP cM (-1) = withHold (h(cP 0) + h(cM 0)) (cP 0)`           (the straddling holding),
  `assemble cP cM (-(k+2)) = cycRev (withHold (h(cM (k+1))) (cM k))`     (reversed backward loops),

where `h c = holdTime c` and `withHold h c` is `c` with its holding at `v` replaced by `h`
(`splice_decomp`).  Everything here is deterministic.

* §1 left limits under shifts; the **double reversal** `leftLim (revPiece x T) (T − u) = x u` on
  regular paths with left limits (`leftLim_revPiece_sub`).
* §2 cycle surgery: `excPath`, `withHold` (measurable, `measurable_withHold`), the reversal of a
  cycle (`revPiece_holdExc`) and of a reversed cycle (`revPiece_cycRevPath`).
* §3 generic glue algebra and the chain lemma `concat_eq_of_chain`.
* §4 `nx`, the forward chain (`concat_cycles_eq`) and the backward loop chain.
* §5 `assemble`, `decomp` (measurable) and **`splice_decomp : splice (decomp v p) = rho p`**.
-/

set_option autoImplicit false

open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.CycleDecomposition

open ReflectedWalk ReflectedWalk.Theorem16
open ReflectedGMS.CadlagRegeneration
open ReflectedGMS.TwoSidedCycleSplice
open ReflectedGMS.FirstCycleLaw

/-! ### 1. Left limits under shifts; double reversal -/

theorem option_eq_of_some_iff {o o' : Option ℕ} (h : ∀ y, o = some y ↔ o' = some y) :
    o = o' := by
  cases o with
  | none =>
    cases o' with
    | none => rfl
    | some y => exact absurd ((h y).2 rfl) (by simp)
  | some y => exact ((h y).1 rfl).symm

theorem leftLim_shiftBy (x : Trajectory ℕ) (H : ℝ≥0) {t : ℝ≥0} (ht : 0 < t) :
    leftLim (shiftBy H x) t = leftLim x (t + H) := by
  refine option_eq_of_some_iff fun y => ?_
  rw [leftLim_eq_some_iff, leftLim_eq_some_iff]
  constructor
  · rintro ⟨a, hat, ha⟩
    refine ⟨a + H, (add_lt_add_iff_right H).2 hat, fun s hs => ?_⟩
    have hHs : H ≤ s := le_trans le_add_self hs.1.le
    have h1 : s - H ∈ Ioo a t :=
      ⟨lt_tsub_iff_right.2 hs.1, (tsub_lt_iff_right hHs).2 hs.2⟩
    have h2 : x (s - H + H) = some y := ha (s - H) h1
    rwa [tsub_add_cancel_of_le hHs] at h2
  · rintro ⟨a, hat, ha⟩
    refine ⟨a - H, ?_, fun s hs =>
      ha (s + H) ⟨lt_add_of_tsub_lt_right hs.1, (add_lt_add_iff_right H).2 hs.2⟩⟩
    by_cases hHa : H ≤ a
    · exact (tsub_lt_iff_right hHa).2 hat
    · rw [tsub_eq_zero_of_le (not_le.1 hHa).le]
      exact ht

/-- **Double reversal**: on a regular path with left limits, the left limit of the reversal at
`T − u` is the value at `u`. -/
theorem leftLim_revPiece_sub {x : Trajectory ℕ} (hx : IsRegLL x) {T u : ℝ≥0} (hu : u < T) :
    leftLim (revPiece x T) (T - u) = x u := by
  cases hxu : x u with
  | some w =>
    obtain ⟨b, hub, hb⟩ := rr_some hx.regular hxu
    have hub' : u < min b T := lt_min hub hu
    have hb'T : min b T ≤ T := min_le_right _ _
    refine leftLim_eq_some_iff.2 ⟨T - min b T, tsub_lt_tsub_left_of_le hb'T hub', fun s hs => ?_⟩
    have hsT : s < T := lt_of_lt_of_le hs.2 tsub_le_self
    rw [revPiece_of_lt hsT]
    have h1 : T - s < min b T :=
      (tsub_lt_iff_left hsT.le).2 ((tsub_lt_iff_right hb'T).1 hs.1)
    refine leftLim_eq_some_iff.2 ⟨u, lt_tsub_comm.1 hs.2, fun r hr => hb r hr.1.le ?_⟩
    exact lt_of_lt_of_le (hr.2.trans h1) (min_le_left _ _)
  | none =>
    refine option_eq_of_some_iff fun y => ⟨fun h => ?_, fun h => absurd h (by simp)⟩
    exfalso
    obtain ⟨a, hat, ha⟩ := leftLim_eq_some_iff.1 h
    obtain ⟨b, hub, hb⟩ := rr_none hx.regular hxu y
    have hb'T : min b T ≤ T := min_le_right _ _
    have hlo : max a (T - min b T) < T - u :=
      max_lt hat (tsub_lt_tsub_left_of_le hb'T (lt_min hub hu))
    obtain ⟨s, hs1, hs2⟩ := exists_between hlo
    have hsT : s < T := lt_of_lt_of_le hs2 tsub_le_self
    have hrev := ha s ⟨lt_of_le_of_lt (le_max_left _ _) hs1, hs2⟩
    rw [revPiece_of_lt hsT] at hrev
    have h1 : T - min b T < s := lt_of_le_of_lt (le_max_right _ _) hs1
    have h2 : T - s < min b T := (tsub_lt_iff_left hsT.le).2 ((tsub_lt_iff_right hb'T).1 h1)
    exact leftLim_ne_some_of (lt_tsub_comm.1 hs2)
      (fun r hr => hb r hr.1 (lt_of_lt_of_le (hr.2.trans h2) (min_le_left _ _))) hrev

/-! ### 2. Cycle surgery -/

variable {v : ℕ}

theorem cyc_hold (c : Cyc v) : 0 < holdTime c ∧ holdTime c < c.1.2 ∧
    (∀ t, t < holdTime c → c.1.1 t = some v) ∧
    ∀ t, holdTime c ≤ t → t < c.1.2 → c.1.1 t ≠ some v := by
  obtain ⟨h, h0, hL, hbef, haft⟩ := c.2.hold
  rw [holdTime_eq c hL hbef haft]
  exact ⟨h0, hL, hbef, haft⟩

/-- The excursion part of a cycle (the path after its holding at `v`). -/
noncomputable def excPath (c : Cyc v) : Trajectory ℕ := shiftBy (holdTime c) c.1.1

theorem isRegLL_excPath (c : Cyc v) : IsRegLL (excPath c) := isRegLL_shiftBy c.2.regLL _

/-- Hold `h` at `v`, then the excursion of `c`. -/
noncomputable def withHoldPath (h : ℝ≥0) (c : Cyc v) : Trajectory ℕ :=
  glue (constPath v) h (excPath c)

theorem withHoldPath_of_lt {h t : ℝ≥0} (c : Cyc v) (ht : t < h) :
    withHoldPath h c t = some v := by
  rw [withHoldPath, glue_of_lt ht]
  rfl

theorem withHoldPath_ne {h t : ℝ≥0} (c : Cyc v) (h1 : h ≤ t)
    (h2 : t < h + (c.1.2 - holdTime c)) : withHoldPath h c t ≠ some v := by
  obtain ⟨-, hHL, -, haft⟩ := cyc_hold c
  rw [withHoldPath, glue_of_le h1]
  show c.1.1 (t - h + holdTime c) ≠ some v
  refine haft _ le_add_self ?_
  have h3 : t - h < c.1.2 - holdTime c := (tsub_lt_iff_left h1).2 h2
  calc t - h + holdTime c < (c.1.2 - holdTime c) + holdTime c :=
      add_lt_add_of_lt_of_le h3 le_rfl
    _ = c.1.2 := tsub_add_cancel_of_le hHL.le

theorem isCycle_withHoldPath {h : ℝ≥0} (hh : 0 < h) (c : Cyc v) :
    IsCycle v (withHoldPath h c) (h + (c.1.2 - holdTime c)) := by
  obtain ⟨-, hHL, -, -⟩ := cyc_hold c
  have hE : 0 < c.1.2 - holdTime c := tsub_pos_of_lt hHL
  refine ⟨withHoldPath_of_lt c hh, isRegLL_glue (isRegLL_constPath v) (isRegLL_excPath c) h,
    fun t ht => ?_, ⟨h, hh, lt_add_of_pos_right h hE, fun t ht => withHoldPath_of_lt c ht,
    fun t h1 h2 => withHoldPath_ne c h1 h2⟩⟩
  have hht : h ≤ t := le_trans le_self_add ht
  rw [withHoldPath, glue_of_le hht]
  show c.1.1 (t - h + holdTime c) = none
  apply c.2.killed
  have h3 : c.1.2 - holdTime c ≤ t - h := le_tsub_of_add_le_left ht
  calc c.1.2 = (c.1.2 - holdTime c) + holdTime c := (tsub_add_cancel_of_le hHL.le).symm
    _ ≤ t - h + holdTime c := add_le_add h3 le_rfl

open Classical in
/-- The raw pair of `withHold`. -/
noncomputable def withHoldRaw (h : ℝ≥0) (c : Cyc v) : Trajectory ℕ × ℝ≥0 :=
  if 0 < h then (withHoldPath h c, h + (c.1.2 - holdTime c)) else c.1

theorem isCycle_withHoldRaw (h : ℝ≥0) (c : Cyc v) :
    IsCycle v (withHoldRaw h c).1 (withHoldRaw h c).2 := by
  unfold withHoldRaw
  split_ifs with hh
  · exact isCycle_withHoldPath hh c
  · exact c.2

/-- **The cycle `c` with its holding at `v` replaced by `h`** (`c` itself if `h = 0`). -/
noncomputable def withHold (h : ℝ≥0) (c : Cyc v) : Cyc v :=
  ⟨withHoldRaw h c, isCycle_withHoldRaw h c⟩

theorem withHold_val {h : ℝ≥0} (hh : 0 < h) (c : Cyc v) :
    (withHold h c).1 = (withHoldPath h c, h + (c.1.2 - holdTime c)) := by
  show withHoldRaw h c = _
  unfold withHoldRaw
  rw [if_pos hh]

theorem len_withHold {h : ℝ≥0} (hh : 0 < h) (c : Cyc v) :
    (withHold h c).1.2 = h + (c.1.2 - holdTime c) := by
  rw [withHold_val hh]

theorem holdTime_withHold {h : ℝ≥0} (hh : 0 < h) (c : Cyc v) : holdTime (withHold h c) = h := by
  obtain ⟨-, hHL, -, -⟩ := cyc_hold c
  have hv := withHold_val hh c
  refine holdTime_eq _ ?_ (fun t ht => ?_) (fun t h1 h2 => ?_)
  · rw [hv]
    exact lt_add_of_pos_right h (tsub_pos_of_lt hHL)
  · rw [hv]
    exact withHoldPath_of_lt c ht
  · rw [hv] at h2 ⊢
    exact withHoldPath_ne c h1 h2

theorem excPath_withHold {h : ℝ≥0} (hh : 0 < h) (c : Cyc v) :
    excPath (withHold h c) = excPath c := by
  funext s
  show (withHold h c).1.1 (s + holdTime (withHold h c)) = excPath c s
  rw [holdTime_withHold hh, withHold_val hh]
  show glue (constPath v) h (excPath c) (s + h) = excPath c s
  rw [glue_of_le le_add_self, add_tsub_cancel_right]

theorem withHold_holdTime (c : Cyc v) : withHold (holdTime c) c = c := by
  obtain ⟨hH0, hHL, hbef, -⟩ := cyc_hold c
  apply Subtype.ext
  rw [withHold_val hH0]
  refine Prod.ext ?_ (add_tsub_cancel_of_le hHL.le)
  funext t
  show glue (constPath v) (holdTime c) (excPath c) t = c.1.1 t
  by_cases ht : t < holdTime c
  · rw [glue_of_lt ht, hbef t ht]
    rfl
  · rw [glue_of_le (not_lt.1 ht)]
    show c.1.1 (t - holdTime c + holdTime c) = c.1.1 t
    rw [tsub_add_cancel_of_le (not_lt.1 ht)]

theorem withHold_withHold {h h' : ℝ≥0} (hh : 0 < h) (hh' : 0 < h') (c : Cyc v) :
    withHold h (withHold h' c) = withHold h c := by
  apply Subtype.ext
  rw [withHold_val hh, withHold_val hh]
  show (glue (constPath v) h (excPath (withHold h' c)),
      h + ((withHold h' c).1.2 - holdTime (withHold h' c))) =
    (glue (constPath v) h (excPath c), h + (c.1.2 - holdTime c))
  rw [excPath_withHold hh', holdTime_withHold hh', len_withHold hh', add_tsub_cancel_left]

theorem measurable_withHold : Measurable fun p : ℝ≥0 × Cyc v => withHold p.1 p.2 := by
  classical
  have hx : Measurable fun p : ℝ≥0 × Cyc v => p.2.1.1 :=
    measurable_fst.comp (measurable_subtype_coe.comp measurable_snd)
  have hL : Measurable fun p : ℝ≥0 × Cyc v => p.2.1.2 :=
    measurable_snd.comp (measurable_subtype_coe.comp measurable_snd)
  have hH : Measurable fun p : ℝ≥0 × Cyc v => holdTime p.2 :=
    measurable_holdTime.comp measurable_snd
  have hpath : Measurable fun p : ℝ≥0 × Cyc v => withHoldPath p.1 p.2 := by
    refine measurable_pi_iff.2 fun s => ?_
    show Measurable fun p : ℝ≥0 × Cyc v =>
      if s < p.1 then some v else p.2.1.1 (s - p.1 + holdTime p.2)
    exact Measurable.ite (measurableSet_lt measurable_const measurable_fst) measurable_const
      (measurable_eval_at hx (fun p => p.2.2.regLL.regular)
        ((measurable_nnreal_sub measurable_const measurable_fst).add hH))
  have h1 : Measurable fun p : ℝ≥0 × Cyc v =>
      if p ∈ {p : ℝ≥0 × Cyc v | 0 < p.1} then
        (withHoldPath p.1 p.2, p.1 + (p.2.1.2 - holdTime p.2)) else p.2.1 :=
    Measurable.ite (measurableSet_lt measurable_const measurable_fst)
      (hpath.prodMk (measurable_fst.add (measurable_nnreal_sub hL hH)))
      (measurable_subtype_coe.comp measurable_snd)
  have heq : (fun p : ℝ≥0 × Cyc v => withHoldRaw p.1 p.2) = fun p =>
      if p ∈ {p : ℝ≥0 × Cyc v | 0 < p.1} then
        (withHoldPath p.1 p.2, p.1 + (p.2.1.2 - holdTime p.2)) else p.2.1 := by
    funext p
    unfold withHoldRaw
    by_cases hp : 0 < p.1
    · rw [if_pos hp, if_pos (show p ∈ {p : ℝ≥0 × Cyc v | 0 < p.1} from hp)]
    · rw [if_neg hp, if_neg (show p ∉ {p : ℝ≥0 × Cyc v | 0 < p.1} from hp)]
  have hraw : Measurable fun p : ℝ≥0 × Cyc v => withHoldRaw p.1 p.2 := by
    rw [heq]
    exact h1
  exact hraw.subtype_mk

/-- **The reversal of a cycle path**: reversed excursion, then the holding. -/
theorem revPiece_holdExc {x : Trajectory ℕ} {H L : ℝ≥0} (hHL : H < L)
    (hbef : ∀ t, t < H → x t = some v) :
    revPiece x L = glue (revPiece (shiftBy H x) (L - H)) (L - H) (glue (constPath v) H cem) := by
  funext u
  by_cases hu : u < L - H
  · have huL : u < L := lt_of_lt_of_le hu tsub_le_self
    have hpos : 0 < L - H - u := tsub_pos_of_lt hu
    rw [glue_of_lt hu, revPiece_of_lt hu, revPiece_of_lt huL, leftLim_shiftBy _ _ hpos]
    have huH : u + H < L := lt_tsub_iff_right.1 hu
    have key : L - H - u + H = L - u := by
      rw [tsub_right_comm, tsub_add_cancel_of_le (le_tsub_of_add_le_left huH.le)]
    rw [key]
  · have hEu : L - H ≤ u := not_lt.1 hu
    rw [glue_of_le hEu]
    by_cases huL : u < L
    · have hLu : L ≤ u + H := tsub_le_iff_right.1 hEu
      have h1 : u - (L - H) < H := by
        rw [tsub_lt_iff_left hEu, tsub_add_cancel_of_le hHL.le]
        exact huL
      rw [revPiece_of_lt huL, glue_of_lt h1]
      refine leftLim_eq_some_iff.2 ⟨0, tsub_pos_of_lt huL, fun s hs => hbef s ?_⟩
      exact lt_of_lt_of_le hs.2 (tsub_le_iff_left.2 hLu)
    · have hLu : L ≤ u := not_lt.1 huL
      have h1 : H ≤ u - (L - H) := by
        rw [le_tsub_iff_left hEu, tsub_add_cancel_of_le hHL.le]
        exact hLu
      rw [revPiece_of_le hLu, glue_of_le h1]
      rfl

/-- **The reversal of a reversed cycle** is the excursion, then the holding. -/
theorem revPiece_cycRevPath {x : Trajectory ℕ} (hx : IsRegLL x) {H L : ℝ≥0} (hHL : H < L) :
    revPiece (cycRevPath x v H L) L = glue (shiftBy H x) (L - H) (glue (constPath v) H cem) := by
  funext u
  by_cases hu : u < L - H
  · have huL : u < L := lt_of_lt_of_le hu tsub_le_self
    have huH : u + H < L := lt_tsub_iff_right.1 hu
    have hpos : 0 < L - u - H := tsub_pos_of_lt (lt_tsub_iff_left.2 huH)
    have hshift : shiftBy H (cycRevPath x v H L) = glue (revPiece x L) (L - H) cem := by
      funext s
      show glue (constPath v) H (glue (revPiece x L) (L - H) cem) (s + H) = _
      rw [glue_of_le le_add_self, add_tsub_cancel_right]
    have e1 : leftLim (cycRevPath x v H L) (L - u) =
        leftLim (glue (revPiece x L) (L - H) cem) (L - u - H) := by
      rw [← hshift, leftLim_shiftBy _ _ hpos, tsub_add_cancel_of_le (le_tsub_of_add_le_left huH.le)]
    have e2 : leftLim (glue (revPiece x L) (L - H) cem) (L - u - H) =
        leftLim (revPiece x L) (L - u - H) := by
      refine leftLim_congr hpos fun s hs => glue_of_lt ?_
      exact lt_of_lt_of_le hs.2 (tsub_le_tsub_right tsub_le_self H)
    rw [revPiece_of_lt huL, e1, e2, tsub_tsub, leftLim_revPiece_sub hx huH, glue_of_lt hu]
    rfl
  · have hEu : L - H ≤ u := not_lt.1 hu
    rw [glue_of_le hEu]
    by_cases huL : u < L
    · have hLu : L ≤ u + H := tsub_le_iff_right.1 hEu
      have h1 : u - (L - H) < H := by
        rw [tsub_lt_iff_left hEu, tsub_add_cancel_of_le hHL.le]
        exact huL
      rw [revPiece_of_lt huL, glue_of_lt h1]
      refine leftLim_eq_some_iff.2 ⟨0, tsub_pos_of_lt huL, fun s hs => ?_⟩
      have hsH : s < H := lt_of_lt_of_le hs.2 (tsub_le_iff_left.2 hLu)
      show glue (constPath v) H _ s = some v
      rw [glue_of_lt hsH]
      rfl
    · have hLu : L ≤ u := not_lt.1 huL
      have h1 : H ≤ u - (L - H) := by
        rw [le_tsub_iff_left hEu, tsub_add_cancel_of_le hHL.le]
        exact hLu
      rw [revPiece_of_le hLu, glue_of_le h1]
      rfl

theorem revPiece_cyc (c : Cyc v) :
    revPiece c.1.1 c.1.2 = glue (revPiece (excPath c) (c.1.2 - holdTime c)) (c.1.2 - holdTime c)
      (glue (constPath v) (holdTime c) cem) :=
  revPiece_holdExc (cyc_hold c).2.1 (cyc_hold c).2.2.1

theorem revPiece_cycRev (c : Cyc v) :
    revPiece (cycRev c).1.1 (cycRev c).1.2 =
      glue (excPath c) (c.1.2 - holdTime c) (glue (constPath v) (holdTime c) cem) :=
  revPiece_cycRevPath c.2.regLL (cyc_hold c).2.1

/-- The reversal of the cycle with holding `h`: reversed excursion, then `h` at `v`. -/
theorem revPiece_withHold {h : ℝ≥0} (hh : 0 < h) (c : Cyc v) :
    revPiece (withHold h c).1.1 (withHold h c).1.2 =
      glue (revPiece (excPath c) (c.1.2 - holdTime c)) (c.1.2 - holdTime c)
        (glue (constPath v) h cem) := by
  rw [revPiece_cyc, excPath_withHold hh, holdTime_withHold hh, len_withHold hh,
    add_tsub_cancel_left]

/-- The reversal of the reversed cycle with holding `h`: the excursion, then `h` at `v`. -/
theorem revPiece_cycRev_withHold {h : ℝ≥0} (hh : 0 < h) (c : Cyc v) :
    revPiece (cycRev (withHold h c)).1.1 (cycRev (withHold h c)).1.2 =
      glue (excPath c) (c.1.2 - holdTime c) (glue (constPath v) h cem) := by
  rw [revPiece_cycRev, excPath_withHold hh, holdTime_withHold hh, len_withHold hh,
    add_tsub_cancel_left]

/-! ### 3. Glue algebra and the chain lemma -/

theorem glue_glue (p q r : Trajectory ℕ) (A B : ℝ≥0) :
    glue p A (glue q B r) = glue (glue p A (glue q B cem)) (A + B) r := by
  funext s
  by_cases hA : s < A
  · rw [glue_of_lt hA, glue_of_lt (lt_of_lt_of_le hA le_self_add), glue_of_lt hA]
  · have hAs : A ≤ s := not_lt.1 hA
    by_cases hB : s < A + B
    · have hsB : s - A < B := (tsub_lt_iff_left hAs).2 hB
      rw [glue_of_le hAs, glue_of_lt hsB, glue_of_lt hB, glue_of_le hAs, glue_of_lt hsB]
    · have hABs : A + B ≤ s := not_lt.1 hB
      have hsB : B ≤ s - A := le_tsub_of_add_le_left hABs
      rw [glue_of_le hAs, glue_of_le hsB, glue_of_le hABs, tsub_tsub]

theorem glue_const_const (w : ℕ) (a b : ℝ≥0) (z : Trajectory ℕ) :
    glue (constPath w) a (glue (constPath w) b z) = glue (constPath w) (a + b) z := by
  funext s
  by_cases ha : s < a
  · rw [glue_of_lt ha, glue_of_lt (lt_of_lt_of_le ha le_self_add)]
  · have has : a ≤ s := not_lt.1 ha
    rw [glue_of_le has]
    by_cases hb : s < a + b
    · have hsb : s - a < b := (tsub_lt_iff_left has).2 hb
      rw [glue_of_lt hsb, glue_of_lt hb]
      rfl
    · have habs : a + b ≤ s := not_lt.1 hb
      rw [glue_of_le (le_tsub_of_add_le_left habs), glue_of_le habs, tsub_tsub]

theorem shiftBy_glue_le (p q : Trajectory ℕ) {a T : ℝ≥0} (h : a ≤ T) :
    shiftBy a (glue p T q) = glue (shiftBy a p) (T - a) q := by
  funext s
  show glue p T q (s + a) = _
  by_cases hs : s < T - a
  · rw [glue_of_lt (lt_tsub_iff_right.1 hs), glue_of_lt hs]
    rfl
  · have hTs : T - a ≤ s := not_lt.1 hs
    have hTsa : T ≤ s + a := tsub_le_iff_right.1 hTs
    rw [glue_of_le hTsa, glue_of_le hTs]
    congr 1
    apply NNReal.eq
    rw [NNReal.coe_sub hTsa, NNReal.coe_sub hTs, NNReal.coe_sub h, NNReal.coe_add]
    ring

theorem glue_eq_self_of_hold {y : Trajectory ℕ} {H : ℝ≥0} (hy : ∀ t, t < H → y t = some v) :
    y = glue (constPath v) H (shiftBy H y) := by
  funext s
  by_cases hs : s < H
  · rw [glue_of_lt hs, hy s hs]
    rfl
  · rw [glue_of_le (not_lt.1 hs)]
    show y s = y (s - H + H)
    rw [tsub_add_cancel_of_le (not_lt.1 hs)]

/-- `revPiece` only reads the path below the reversal length. -/
theorem revPiece_glue (p q : Trajectory ℕ) (T : ℝ≥0) : revPiece (glue p T q) T = revPiece p T := by
  funext u
  by_cases hu : u < T
  · rw [revPiece_of_lt hu, revPiece_of_lt hu]
    exact leftLim_congr (tsub_pos_of_lt hu) fun s hs =>
      glue_of_lt (lt_of_lt_of_le hs.2 tsub_le_self)
  · rw [revPiece_of_le (not_lt.1 hu), revPiece_of_le (not_lt.1 hu)]

/-- **The chain lemma**: if `z k = piece k ⊕_{len k} z (k+1)` for every `k` and the lengths sum
to `∞`, the concatenation of the pieces is `z 0`. -/
theorem concat_eq_of_chain {piece : ℕ → Trajectory ℕ} {len : ℕ → ℝ≥0} {z : ℕ → Trajectory ℕ}
    (hz : ∀ k, z k = glue (piece k) (len k) (z (k + 1))) (hu : Unbounded len) :
    concat piece len = z 0 := by
  have key : ∀ (n : ℕ) (piece : ℕ → Trajectory ℕ) (len : ℕ → ℝ≥0) (z : ℕ → Trajectory ℕ),
      (∀ k, z k = glue (piece k) (len k) (z (k + 1))) →
        ∀ t, t < psum len n → concat piece len t = z 0 t := by
    intro n
    induction n with
    | zero =>
      intro piece len z _ t ht
      rw [psum_zero] at ht
      exact absurd ht (not_lt.2 bot_le)
    | succ n ih =>
      intro piece len z hz t ht
      rw [concat_cons, hz 0]
      by_cases h0 : t < len 0
      · rw [glue_of_lt h0, glue_of_lt h0]
      · rw [glue_of_le (not_lt.1 h0), glue_of_le (not_lt.1 h0)]
        refine ih (fun k => piece (k + 1)) (fun k => len (k + 1)) (fun k => z (k + 1))
          (fun k => hz (k + 1)) _ ?_
        rw [psum_succ'] at ht
        exact (tsub_lt_iff_left (not_lt.1 h0)).2 ht
  funext t
  obtain ⟨n, hn⟩ := hu.exists_gt t
  exact key n piece len z hz t hn

/-! ### 4. The shift to the next return; forward and backward chains -/

/-- **The path after its first complete return.** -/
noncomputable def nx (x : RegLL) : RegLL := ⟨shiftBy (retLen x.1) x.1, isRegLL_shiftBy x.2 _⟩

theorem measurable_nx : Measurable nx := by
  have h : Measurable fun x : RegLL => shiftBy (retLen x.1) x.1 := by
    refine measurable_pi_iff.2 fun s => ?_
    show Measurable fun x : RegLL => x.1 (s + retLen x.1)
    exact measurable_eval_at measurable_subtype_coe (fun x => x.2.regular)
      (measurable_const.add measurable_retLen_reg)
  exact h.subtype_mk

/-- A path that starts at `v` and returns. -/
def Good (v : ℕ) (x : RegLL) : Prop := x.1 0 = some v ∧ fwdReturn x.1 ≠ ⊤

theorem measurableSet_good (v : ℕ) : MeasurableSet {x : RegLL | Good v x} :=
  measurableSet_goodStart v

theorem firstCycle_len_of_good {x : RegLL} (h : Good v x) :
    (firstCycle v x).1.2 = retLen x.1 := by
  rw [firstCycle_of_good h.1 h.2]

theorem path_eq_glue_of_good {x : RegLL} (h : Good v x) :
    x.1 = glue (firstCycle v x).1.1 (firstCycle v x).1.2 (nx x).1 := by
  rw [firstCycle_of_good h.1 h.2]
  funext s
  show x.1 s = glue (glue x.1 (retLen x.1) cem) (retLen x.1) (shiftBy (retLen x.1) x.1) s
  by_cases hs : s < retLen x.1
  · rw [glue_of_lt hs, glue_of_lt hs]
  · rw [glue_of_le (not_lt.1 hs)]
    show x.1 s = x.1 (s - retLen x.1 + retLen x.1)
    rw [tsub_add_cancel_of_le (not_lt.1 hs)]

theorem path_of_lt_hold {x : RegLL} (h : Good v x) {t : ℝ≥0}
    (ht : t < holdTime (firstCycle v x)) : x.1 t = some v := by
  obtain ⟨-, hHL, hbef, -⟩ := cyc_hold (firstCycle v x)
  rw [path_eq_glue_of_good h, glue_of_lt (ht.trans hHL)]
  exact hbef t ht

/-- **The forward chain**: a path all of whose cycles are complete, with cycle lengths summing to
`∞`, is the concatenation of its cycles. -/
theorem concat_cycles_eq {x : RegLL} (hg : ∀ k, Good v (nx^[k] x))
    (hu : Unbounded fun k => (firstCycle v (nx^[k] x)).1.2) :
    concat (fun k => (firstCycle v (nx^[k] x)).1.1) (fun k => (firstCycle v (nx^[k] x)).1.2) =
      x.1 :=
  concat_eq_of_chain (z := fun k => (nx^[k] x).1) (fun k => by
    show (nx^[k] x).1 = glue _ _ (nx^[k + 1] x).1
    rw [Function.iterate_succ_apply']
    exact path_eq_glue_of_good (hg k)) hu

/-- The `k`-th post-exit path: the `k`-th cycle's excursion, and everything after it. -/
noncomputable def postExit (v : ℕ) (x : RegLL) (k : ℕ) : Trajectory ℕ :=
  shiftBy (holdTime (firstCycle v (nx^[k] x))) (nx^[k] x).1

/-- The `k`-th backward loop: the `k`-th excursion, then the `(k+1)`-st holding. -/
noncomputable def loop (v : ℕ) (x : RegLL) (k : ℕ) : Trajectory ℕ :=
  glue (excPath (firstCycle v (nx^[k] x)))
    ((firstCycle v (nx^[k] x)).1.2 - holdTime (firstCycle v (nx^[k] x)))
    (glue (constPath v) (holdTime (firstCycle v (nx^[k + 1] x))) cem)

/-- The length of the `k`-th backward loop. -/
noncomputable def loopLen (v : ℕ) (x : RegLL) (k : ℕ) : ℝ≥0 :=
  ((firstCycle v (nx^[k] x)).1.2 - holdTime (firstCycle v (nx^[k] x))) +
    holdTime (firstCycle v (nx^[k + 1] x))

theorem postExit_chain {x : RegLL} (hg : ∀ k, Good v (nx^[k] x)) (k : ℕ) :
    postExit v x k = glue (loop v x k) (loopLen v x k) (postExit v x (k + 1)) := by
  set c := firstCycle v (nx^[k] x) with hc
  obtain ⟨-, hHL, -, -⟩ := cyc_hold c
  have h1 : (nx^[k] x).1 = glue c.1.1 c.1.2 (nx^[k + 1] x).1 := by
    rw [Function.iterate_succ_apply']
    exact path_eq_glue_of_good (hg k)
  have h2 : (nx^[k + 1] x).1 = glue (constPath v) (holdTime (firstCycle v (nx^[k + 1] x)))
      (postExit v x (k + 1)) :=
    glue_eq_self_of_hold fun t ht => path_of_lt_hold (hg (k + 1)) ht
  show shiftBy (holdTime c) (nx^[k] x).1 =
    glue (glue (excPath c) (c.1.2 - holdTime c)
      (glue (constPath v) (holdTime (firstCycle v (nx^[k + 1] x))) cem))
      ((c.1.2 - holdTime c) + holdTime (firstCycle v (nx^[k + 1] x))) (postExit v x (k + 1))
  rw [h1, shiftBy_glue_le _ _ hHL.le, h2,
    glue_glue (shiftBy (holdTime c) c.1.1) (constPath v) (postExit v x (k + 1))
      (c.1.2 - holdTime c) (holdTime (firstCycle v (nx^[k + 1] x)))]
  rfl

/-- The loop lengths sum to `∞` when the cycle lengths do. -/
theorem psum_loopLen (v : ℕ) (x : RegLL) (n : ℕ) :
    psum (loopLen v x) n + holdTime (firstCycle v x) =
      psum (fun k => (firstCycle v (nx^[k] x)).1.2) n + holdTime (firstCycle v (nx^[n] x)) := by
  induction n with
  | zero => simp [psum_zero]
  | succ n ih =>
    obtain ⟨-, hHL, -, -⟩ := cyc_hold (firstCycle v (nx^[n] x))
    rw [psum_succ, psum_succ, add_right_comm (psum (loopLen v x) n), ih, loopLen]
    have e : (firstCycle v (nx^[n] x)).1.2 =
        ((firstCycle v (nx^[n] x)).1.2 - holdTime (firstCycle v (nx^[n] x))) +
          holdTime (firstCycle v (nx^[n] x)) := (tsub_add_cancel_of_le hHL.le).symm
    conv_rhs => rw [e]
    ring

theorem unbounded_loopLen {x : RegLL} (hu : Unbounded fun k => (firstCycle v (nx^[k] x)).1.2) :
    Unbounded (loopLen v x) := by
  intro n
  obtain ⟨k, hk⟩ := hu.exists_gt ((n : ℝ≥0) + holdTime (firstCycle v x))
  refine ⟨k, ?_⟩
  have h := psum_loopLen v x k
  have h4 : psum (fun k => (firstCycle v (nx^[k] x)).1.2) k ≤
      psum (loopLen v x) k + holdTime (firstCycle v x) := by
    rw [h]
    exact le_self_add
  exact lt_of_add_lt_add_right (lt_of_lt_of_le hk h4)

/-- **The backward chain**: the path after the first exit is the concatenation of the loops. -/
theorem concat_loops_eq {x : RegLL} (hg : ∀ k, Good v (nx^[k] x))
    (hu : Unbounded fun k => (firstCycle v (nx^[k] x)).1.2) :
    concat (loop v x) (loopLen v x) = postExit v x 0 :=
  concat_eq_of_chain (postExit_chain hg) (unbounded_loopLen hu)

/-! ### 5. The two-sided cycle sequence of a pair, and `splice ∘ decomp = ρ` -/

/-- The backward half of a two-sided regular pair. -/
def bwdReg (p : TwoSidedReg) : RegLL := ⟨p.1.2, p.2.bwd⟩

theorem measurable_bwdReg : Measurable bwdReg :=
  (measurable_snd.comp measurable_subtype_coe).subtype_mk

/-- The cycle sequence of `nx^[k] x`. -/
noncomputable def cycSeq (v : ℕ) (x : RegLL) : ℕ → Cyc v := fun k => firstCycle v (nx^[k] x)

theorem measurable_cycSeq (v : ℕ) : Measurable (cycSeq v) :=
  measurable_pi_iff.2 fun k => (measurable_firstCycle v).comp (measurable_nx.iterate k)

/-- **The two-sided cycle sequence assembled from the forward cycles `a` and backward cycles `b`**
of a vertex-rooted pair, after re-rooting at the first forward return. -/
noncomputable def assemble (a b : ℕ → Cyc v) : ℤ → Cyc v
  | Int.ofNat k => a (k + 1)
  | Int.negSucc 0 => withHold (holdTime (a 0) + holdTime (b 0)) (a 0)
  | Int.negSucc (k + 1) => cycRev (withHold (holdTime (b (k + 1))) (b k))

theorem measurable_withHold_of {α : Type*} [MeasurableSpace α] {f : α → ℝ≥0} {g : α → Cyc v}
    (hf : Measurable f) (hg : Measurable g) : Measurable fun a => withHold (f a) (g a) :=
  measurable_withHold.comp (hf.prodMk hg)

theorem measurable_seq_fst (k : ℕ) :
    Measurable fun x : (ℕ → Cyc v) × (ℕ → Cyc v) => x.1 k :=
  (measurable_pi_apply k).comp measurable_fst

theorem measurable_seq_snd (k : ℕ) :
    Measurable fun x : (ℕ → Cyc v) × (ℕ → Cyc v) => x.2 k :=
  (measurable_pi_apply k).comp measurable_snd

theorem measurable_assemble :
    Measurable fun ab : (ℕ → Cyc v) × (ℕ → Cyc v) => assemble ab.1 ab.2 := by
  refine measurable_pi_iff.2 fun j => ?_
  rcases j with k | (_ | k)
  · show Measurable fun x : (ℕ → Cyc v) × (ℕ → Cyc v) => x.1 (k + 1)
    exact measurable_seq_fst (k + 1)
  · show Measurable fun x : (ℕ → Cyc v) × (ℕ → Cyc v) =>
      withHold (holdTime (x.1 0) + holdTime (x.2 0)) (x.1 0)
    exact measurable_withHold_of ((measurable_holdTime.comp (measurable_seq_fst 0)).add
      (measurable_holdTime.comp (measurable_seq_snd 0))) (measurable_seq_fst 0)
  · show Measurable fun x : (ℕ → Cyc v) × (ℕ → Cyc v) =>
      cycRev (withHold (holdTime (x.2 (k + 1))) (x.2 k))
    exact measurable_cycRev.comp (measurable_withHold_of
      (measurable_holdTime.comp (measurable_seq_snd (k + 1))) (measurable_seq_snd k))

/-- **The cycle decomposition of a two-sided pair.** -/
noncomputable def decomp (v : ℕ) (p : TwoSidedReg) : ℤ → Cyc v :=
  assemble (cycSeq v (fwdReg p)) (cycSeq v (bwdReg p))

theorem measurable_decomp (v : ℕ) : Measurable (decomp v) :=
  measurable_assemble.comp (((measurable_cycSeq v).comp measurable_fwdReg).prodMk
    ((measurable_cycSeq v).comp measurable_bwdReg))

theorem bwdIdx_eq_negSucc (k : ℕ) : bwdIdx k = Int.negSucc k := by
  rw [bwdIdx, Int.negSucc_eq]

/-- **Pathwise cycle decomposition of the re-rooted pair**: if both halves have all their cycles
complete with lengths summing to `∞`, the re-rooting `ρ p` is the splice of `decomp v p`. -/
theorem splice_decomp {p : TwoSidedReg} (hP : ∀ k, Good v (nx^[k] (fwdReg p)))
    (hM : ∀ k, Good v (nx^[k] (bwdReg p)))
    (uP : Unbounded fun k => (firstCycle v (nx^[k] (fwdReg p))).1.2)
    (uM : Unbounded fun k => (firstCycle v (nx^[k] (bwdReg p))).1.2) :
    splice (decomp v p) = rho p := by
  set a := cycSeq v (fwdReg p) with ha
  set b := cycSeq v (bwdReg p) with hb
  obtain ⟨hHa0, hHLa, -, -⟩ := cyc_hold (a 0)
  obtain ⟨hHb0, -, -, -⟩ := cyc_hold (b 0)
  -- the lengths
  have hfl : fwdLens (decomp v p) = fun k => (a (k + 1)).1.2 := rfl
  have hfp : fwdPieces (decomp v p) = fun k => (a (k + 1)).1.1 := rfl
  have hbl0 : bwdLens (decomp v p) 0 = (a 0).1.2 + holdTime (b 0) := by
    show (decomp v p (bwdIdx 0)).1.2 = _
    rw [bwdIdx_eq_negSucc]
    show (withHold (holdTime (a 0) + holdTime (b 0)) (a 0)).1.2 = _
    rw [len_withHold (add_pos hHa0 hHb0)]
    rw [add_comm (holdTime (a 0)) (holdTime (b 0)), add_assoc,
      add_tsub_cancel_of_le hHLa.le, add_comm]
  have hblS : (fun k => bwdLens (decomp v p) (k + 1)) = loopLen v (bwdReg p) := by
    funext k
    obtain ⟨hHk, -, -, -⟩ := cyc_hold (b (k + 1))
    show (decomp v p (bwdIdx (k + 1))).1.2 = _
    rw [bwdIdx_eq_negSucc]
    show (cycRev (withHold (holdTime (b (k + 1))) (b k))).1.2 = _
    show (withHold (holdTime (b (k + 1))) (b k)).1.2 = _
    rw [len_withHold hHk, add_comm]
    rfl
  have hbp0 : bwdPieces (decomp v p) 0 =
      glue (revPiece (excPath (a 0)) ((a 0).1.2 - holdTime (a 0))) ((a 0).1.2 - holdTime (a 0))
        (glue (constPath v) (holdTime (a 0) + holdTime (b 0)) cem) := by
    show revPiece (decomp v p (bwdIdx 0)).1.1 (decomp v p (bwdIdx 0)).1.2 = _
    rw [bwdIdx_eq_negSucc]
    exact revPiece_withHold (add_pos hHa0 hHb0) (a 0)
  have hbpS : (fun k => bwdPieces (decomp v p) (k + 1)) = loop v (bwdReg p) := by
    funext k
    obtain ⟨hHk, -, -, -⟩ := cyc_hold (b (k + 1))
    show revPiece (decomp v p (bwdIdx (k + 1))).1.1 (decomp v p (bwdIdx (k + 1))).1.2 = _
    rw [bwdIdx_eq_negSucc]
    exact revPiece_cycRev_withHold hHk (b k)
  -- unboundedness
  have uPs : Unbounded (fwdLens (decomp v p)) := by
    rw [hfl]
    exact unbounded_succ_iff.2 uP
  have uMs : Unbounded (bwdLens (decomp v p)) := by
    refine unbounded_succ_iff.1 ?_
    rw [hblS]
    exact unbounded_loopLen uM
  have hgood : GoodSeq (decomp v p) := ⟨uPs, uMs⟩
  -- the forward half
  have hgP1 : ∀ k, Good v (nx^[k] (nx (fwdReg p))) := fun k => hP (k + 1)
  have uP1 : Unbounded fun k => (firstCycle v (nx^[k] (nx (fwdReg p)))).1.2 :=
    unbounded_succ_iff.2 uP
  have hfwd : fwdPath (decomp v p) = shiftBy (retLen p.1.1) p.1.1 := by
    rw [fwdPath, hfp, hfl]
    exact concat_cycles_eq hgP1 uP1
  -- the backward half
  have hL0 : retLen p.1.1 = (a 0).1.2 := (firstCycle_len_of_good (hP 0)).symm
  have hxm : p.1.2 = glue (constPath v) (holdTime (b 0)) (postExit v (bwdReg p) 0) :=
    glue_eq_self_of_hold (y := p.1.2) fun t ht => path_of_lt_hold (x := bwdReg p) (hM 0) ht
  have hrevp : revPiece p.1.1 (a 0).1.2 = revPiece (a 0).1.1 (a 0).1.2 := by
    have h := path_eq_glue_of_good (hP 0)
    have h' : p.1.1 = glue (a 0).1.1 (a 0).1.2 (nx (fwdReg p)).1 := h
    rw [h', revPiece_glue]
  have hbwd : bwdPath (decomp v p) =
      glue (revPiece p.1.1 (retLen p.1.1)) (retLen p.1.1) p.1.2 := by
    rw [bwdPath, concat_cons, hbp0, hbl0, hbpS, hblS, concat_loops_eq hM uM, hL0, hrevp,
      revPiece_cyc, hxm]
    have e1 := glue_glue (revPiece (excPath (a 0)) ((a 0).1.2 - holdTime (a 0))) (constPath v)
      (postExit v (bwdReg p) 0) ((a 0).1.2 - holdTime (a 0)) (holdTime (a 0) + holdTime (b 0))
    have e2 := glue_glue (revPiece (excPath (a 0)) ((a 0).1.2 - holdTime (a 0))) (constPath v)
      (glue (constPath v) (holdTime (b 0)) (postExit v (bwdReg p) 0))
      ((a 0).1.2 - holdTime (a 0)) (holdTime (a 0))
    have hLE : (a 0).1.2 - holdTime (a 0) + holdTime (a 0) = (a 0).1.2 :=
      tsub_add_cancel_of_le hHLa.le
    have hLE' : (a 0).1.2 - holdTime (a 0) + (holdTime (a 0) + holdTime (b 0)) =
        (a 0).1.2 + holdTime (b 0) := by
      rw [← add_assoc, hLE]
    rw [hLE'] at e1
    rw [hLE] at e2
    rw [← e1, ← e2, glue_const_const]
  -- assemble
  apply Subtype.ext
  show spliceRaw (decomp v p) = rhoRaw p.1
  rw [spliceRaw, if_pos hgood]
  unfold rhoRaw
  rw [if_neg (show ¬ fwdReturn p.1.1 = ⊤ from (hP 0).2), hfwd, hbwd]

end ReflectedGMS.CycleDecomposition
