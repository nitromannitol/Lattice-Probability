/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Temporal.RatShiftBridgeProof at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Temporal.RatShiftBridgePathwise
import LatticeProb.Bonanno.ReflectedGMS.Temporal.CellRootedRegenAllStarts

/-!
# `hbr` PROVED: the rational-shift bridge at every live gate environment

`CellRootedRegenAllStarts.RatShiftBridgeOn z G hG hwalk` (B1 of the final-route review) is the last
named input of `InvarianceMainTheoremProof.reflectedInvarianceMainTheorem`.  It
is proved here for every field `z` and every measurable admissible gate `G` carrying the extension
input `ExtensionGate z G` (`ratShiftBridgeOn_of_extensionGate`), hence at the interior
representative and the similarity-closed gate (`ratShiftBridgeOn_interiorField`).

By `RatShiftBridgePathwise.ratShiftBridge_of_ae` it suffices that, under the rooted regularity
kernel `μ = rootedRegKernel … e` at a live environment `e`,

1. a.s. the rational position readings satisfy the càdlàg criterion and the label event `Lab`
   holds at `w` (`ae_ratCadlag_lab`: on the sample-space good set the readings are those of the
   built configuration, `FlowCodingKernel.ratRead_build_of_mem`; `Lab` is fixed-time local
   constancy, property (ii));
2. a.s. `Lab (ρ^{k+1} w)` for every `k` (`ae_lab_iterate`).  Here the PROVED cycle decomposition
   `μ.map ρ ≪ entranceLaw ν` (clauses (b), (c): `CompleteCycleReversal`, `RootedCycleDecomposition`)
   and the exact `ρ`-invariance of the i.i.d.-cycle law reduce everything to `Lab` under
   `entranceLaw ν` (`ae_lab_splice`):
   * the forward half is the walk from the root (`CycleDecomposition.map_cycSeq`,
     `concat_cycles_eq`), locally constant at fixed times;
   * the backward half is a concatenation of left-limit reversed i.i.d. cycles; at a rational time
     the cycle containing it is independent of the partial sum before it (`iid_fubini`), and a
     reversed cycle is locally constant at a fixed time `u` a.s. (`measure_bad_rev`): by the
     complete-cycle reversal `ν.map cycRev = ν` this is local constancy at the fixed time `u`
     AFTER THE FIRST EXIT, which is the strong Markov property at the exit time
     (`CycleHolding.measure_exit_future`) plus fixed-time local constancy of the walk from the
     exit vertex (`ae_goodAtQ_hold_add`); partial sums avoid rational times because a return time
     is a jump time (`not_goodAt_fwdN_psum`).

This is the handoff's first route (strong Markov at the return times via forward regeneration,
continuity at the reversed side), organized through the PROVED cycle decomposition so that only
the first exit and one reversed cycle ever enter.  The handoff's "cleaner alternative" (an exact
measurable intertwining `Φ`) was not taken: it needs the same measurable càdlàg criterion to even
define `Φ` (see `RatShiftBridgeCadlag`), and a new consumer.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal NNReal

namespace ReflectedGMS.RatShiftBridgeProof

open Code EnvironmentFields EnvironmentLaws AreaClocks RootDensities
open ReflectedWalk ReflectedWalk.Theorem16
open ReflectedGMS.TrajectoryCoding ReflectedGMS.TwoSidedRegenerationFlow
open ReflectedGMS.TwoSidedRegenerationCoding ReflectedGMS.RegenerationKernel
open ReflectedGMS.EnvironmentWalkDataProducer
open ReflectedGMS.CadlagRegeneration
open ReflectedGMS.FlowCodingKernel
open ReflectedGMS.TwoSidedCycleSplice ReflectedGMS.FirstCycleLaw ReflectedGMS.CycleDecomposition
open ReflectedGMS.CycleHolding
open ReflectedGMS.CellRootedRegenerativeInvariance
open ReflectedGMS.RatShiftBridgeCadlag ReflectedGMS.RatShiftBridgePathwise

/-! ### 1. Local constancy: interval form and transfer lemmas -/

theorem goodAt_mk {x : Trajectory ℕ} {t : ℝ≥0} (w : ℕ) (ε : ℝ) (hε : 0 < ε)
    (h : ∀ s : ℝ≥0, (t : ℝ) - ε < s → (s : ℝ) < t + ε → x s = some w) : GoodAt x t := by
  refine ⟨w, ε, hε, fun s hs => ?_⟩
  rw [NNReal.dist_eq, abs_lt] at hs
  exact h s (by linarith [hs.1]) (by linarith [hs.2])

theorem goodAt_dest {x : Trajectory ℕ} {t : ℝ≥0} (h : GoodAt x t) :
    ∃ w : ℕ, ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ≥0, (t : ℝ) - ε < s → (s : ℝ) < t + ε → x s = some w := by
  obtain ⟨w, ε, hε, hx⟩ := h
  refine ⟨w, ε, hε, fun s h1 h2 => hx s ?_⟩
  rw [NNReal.dist_eq, abs_lt]
  constructor <;> linarith

/-- Local constancy only reads a neighbourhood: two paths agreeing below `L` agree on it. -/
theorem goodAt_of_agree {x y : Trajectory ℕ} {L t : ℝ≥0} (ht : t < L)
    (hxy : ∀ s, s < L → x s = y s) (h : GoodAt y t) : GoodAt x t := by
  obtain ⟨w, ε, hε, hy⟩ := goodAt_dest h
  have htL : (t : ℝ) < L := ht
  have hm1 := min_le_left ε ((L : ℝ) - t)
  have hm2 := min_le_right ε ((L : ℝ) - t)
  refine goodAt_mk w (min ε ((L : ℝ) - t)) (lt_min hε (by linarith)) fun s h1 h2 => ?_
  have hsL : s < L := by
    have : (s : ℝ) < L := by linarith
    exact_mod_cast this
  rw [hxy s hsL]
  exact hy s (by linarith) (by linarith)

theorem goodAt_glue_right {p q : Trajectory ℕ} {T t : ℝ≥0} (hTt : T < t)
    (h : GoodAt q (t - T)) : GoodAt (TwoSidedCycleSplice.glue p T q) t := by
  obtain ⟨w, ε, hε, hw⟩ := goodAt_dest h
  have hTt' : (T : ℝ) < t := hTt
  have hc : ((t - T : ℝ≥0) : ℝ) = t - T := NNReal.coe_sub hTt.le
  have hm1 := min_le_left ε ((t : ℝ) - T)
  have hm2 := min_le_right ε ((t : ℝ) - T)
  refine goodAt_mk w (min ε ((t : ℝ) - T)) (lt_min hε (by linarith)) fun s h1 h2 => ?_
  have hTs : T ≤ s := by
    have : (T : ℝ) ≤ s := by linarith
    exact_mod_cast this
  rw [TwoSidedCycleSplice.glue_of_le hTs]
  exact hw (s - T) (by rw [NNReal.coe_sub hTs, hc]; linarith)
    (by rw [NNReal.coe_sub hTs, hc]; linarith)

theorem goodAt_glue_left {p q : Trajectory ℕ} {T t : ℝ≥0} (htT : t < T) (h : GoodAt p t) :
    GoodAt (TwoSidedCycleSplice.glue p T q) t :=
  goodAt_of_agree htT (fun _ hs => TwoSidedCycleSplice.glue_of_lt hs) h

theorem leftLim_eq_of_near {x : Trajectory ℕ} {r : ℝ≥0} {w : ℕ} {δ : ℝ} (hr : (0 : ℝ) < r)
    (hδ : 0 < δ) (h : ∀ s : ℝ≥0, (r : ℝ) - δ < s → s < r → x s = some w) :
    leftLim x r = some w := by
  refine leftLim_eq_some_iff.2 ⟨((r : ℝ) - δ).toNNReal, ?_, fun s hs => h s ?_ hs.2⟩
  · have := (Real.toNNReal_lt_toNNReal_iff hr).2 (show (r : ℝ) - δ < r by linarith)
    rwa [Real.toNNReal_coe] at this
  · have h1 : ((((r : ℝ) - δ).toNNReal : ℝ≥0) : ℝ) < s := hs.1
    rw [Real.coe_toNNReal'] at h1
    linarith [le_max_left ((r : ℝ) - δ) 0]

/-- **Local constancy survives the left-limit reversal.** -/
theorem goodAt_revPiece {x : Trajectory ℕ} {L u : ℝ≥0} (hu0 : 0 < u) (huL : u < L)
    (h : GoodAt x (L - u)) : GoodAt (revPiece x L) u := by
  obtain ⟨w, ε, hε, hw⟩ := goodAt_dest h
  have hc : ((L - u : ℝ≥0) : ℝ) = L - u := NNReal.coe_sub huL.le
  have hu : (0 : ℝ) < u := by exact_mod_cast hu0
  have huL' : (u : ℝ) < L := huL
  have hm1 := min_le_left (ε / 2) (min (u : ℝ) ((L : ℝ) - u))
  have hm2 := min_le_right (ε / 2) (min (u : ℝ) ((L : ℝ) - u))
  have hm3 := min_le_left (u : ℝ) ((L : ℝ) - u)
  have hm4 := min_le_right (u : ℝ) ((L : ℝ) - u)
  have hpos : 0 < min (ε / 2) (min (u : ℝ) ((L : ℝ) - u)) :=
    lt_min (by linarith) (lt_min hu (by linarith))
  refine goodAt_mk w (min (ε / 2) (min (u : ℝ) ((L : ℝ) - u))) hpos fun s h1 h2 => ?_
  have hsL' : (s : ℝ) < L := by linarith
  have hsL : s < L := by exact_mod_cast hsL'
  rw [revPiece_of_lt hsL]
  have hcs : ((L - s : ℝ≥0) : ℝ) = L - s := NNReal.coe_sub hsL.le
  refine leftLim_eq_of_near (δ := ε / 2) (by rw [hcs]; linarith) (by linarith)
    fun s' h3 h4 => hw s' ?_ ?_
  · rw [hcs] at h3
    rw [hc]
    linarith
  · have h4' : (s' : ℝ) < ((L - s : ℝ≥0) : ℝ) := h4
    rw [hcs] at h4'
    rw [hc]
    linarith

theorem goodAt_of_shiftBy {x : Trajectory ℕ} {H u : ℝ≥0} (hu : 0 < u)
    (h : GoodAt (shiftBy H x) u) : GoodAt x (u + H) := by
  obtain ⟨w, ε, hε, hw⟩ := goodAt_dest h
  have hu' : (0 : ℝ) < u := by exact_mod_cast hu
  have hm1 := min_le_left ε (u : ℝ)
  have hm2 := min_le_right ε (u : ℝ)
  refine goodAt_mk w (min ε (u : ℝ)) (lt_min hε hu') fun s h1 h2 => ?_
  push_cast at h1 h2
  have hHs : H ≤ s := by
    have : (H : ℝ) ≤ s := by linarith
    exact_mod_cast this
  have h := hw (s - H) (by rw [NNReal.coe_sub hHs]; linarith) (by rw [NNReal.coe_sub hHs]; linarith)
  have e : shiftBy H x (s - H) = x s := by
    show x (s - H + H) = x s
    rw [tsub_add_cancel_of_le hHs]
  rw [← e]
  exact h

theorem goodAt_concat {piece : ℕ → Trajectory ℕ} {len : ℕ → ℝ≥0} {k : ℕ} {t : ℝ≥0}
    (hb : Bracket len k t) (hlt : psum len k < t) (h : GoodAt (piece k) (t - psum len k)) :
    GoodAt (concat piece len) t := by
  obtain ⟨w, ε, hε, hw⟩ := goodAt_dest h
  have ha : (psum len k : ℝ) < t := hlt
  have hb' : (t : ℝ) < psum len (k + 1) := hb.2
  have hc : ((t - psum len k : ℝ≥0) : ℝ) = t - psum len k := NNReal.coe_sub hlt.le
  have hm1 := min_le_left ε (min ((t : ℝ) - psum len k) ((psum len (k + 1) : ℝ) - t))
  have hm2 := min_le_right ε (min ((t : ℝ) - psum len k) ((psum len (k + 1) : ℝ) - t))
  have hm3 := min_le_left ((t : ℝ) - psum len k) ((psum len (k + 1) : ℝ) - t)
  have hm4 := min_le_right ((t : ℝ) - psum len k) ((psum len (k + 1) : ℝ) - t)
  refine goodAt_mk w (min ε (min ((t : ℝ) - psum len k) ((psum len (k + 1) : ℝ) - t)))
    (lt_min hε (lt_min (by linarith) (by linarith))) fun s h1 h2 => ?_
  have has : psum len k ≤ s := by
    have : (psum len k : ℝ) ≤ s := by linarith
    exact_mod_cast this
  have hsb : s < psum len (k + 1) := by
    have : (s : ℝ) < psum len (k + 1) := by linarith
    exact_mod_cast this
  rw [concat_of_bracket ⟨has, hsb⟩]
  exact hw (s - psum len k) (by rw [NNReal.coe_sub has, hc]; linarith)
    (by rw [NNReal.coe_sub has, hc]; linarith)

theorem exists_nnreal_between {lo : ℝ} {t : ℝ≥0} (h : lo < t) (ht : (0 : ℝ) < t) :
    ∃ s : ℝ≥0, lo < s ∧ (s : ℝ) < t := by
  obtain ⟨y, h1, h2⟩ := exists_between (max_lt h ht)
  have hy0 : 0 ≤ y := le_of_lt (lt_of_le_of_lt (le_max_right _ _) h1)
  refine ⟨y.toNNReal, ?_, ?_⟩
  · rw [Real.coe_toNNReal _ hy0]
    exact lt_of_le_of_lt (le_max_left _ _) h1
  · rw [Real.coe_toNNReal _ hy0]
    exact h2

/-- **A return time is a jump time**: the path is not locally constant there. -/
theorem not_goodAt_retLen {v : ℕ} {x : RegLL} (h1 : Good v x) (h2 : Good v (nx x)) :
    ¬ GoodAt x.1 (retLen x.1) := by
  intro hg
  obtain ⟨w, ε, hε, hw⟩ := goodAt_dest hg
  obtain ⟨hH0, hHL, -, haft⟩ := cyc_hold (firstCycle v x)
  have hL : (firstCycle v x).1.2 = retLen x.1 := firstCycle_len_of_good h1
  have hret : x.1 (retLen x.1) = some v := by
    have e : (nx x).1 0 = x.1 (0 + retLen x.1) := rfl
    rw [zero_add] at e
    rw [← e]
    exact h2.1
  have hwv : w = v := by
    have := hw (retLen x.1) (by linarith) (by linarith)
    rw [hret] at this
    exact (Option.some_inj.1 this).symm
  have hHL' : (holdTime (firstCycle v x) : ℝ) < retLen x.1 := by
    rw [← hL]; exact_mod_cast hHL
  have hLpos : (0 : ℝ) < retLen x.1 := lt_of_le_of_lt (NNReal.coe_nonneg _) hHL'
  obtain ⟨s, hs1, hs2⟩ := exists_nnreal_between
    (lo := max (holdTime (firstCycle v x) : ℝ) ((retLen x.1 : ℝ) - ε))
    (max_lt hHL' (by linarith)) hLpos
  have hsL : s < (firstCycle v x).1.2 := by
    rw [hL]
    exact_mod_cast hs2
  have hHs : holdTime (firstCycle v x) ≤ s := by
    have : (holdTime (firstCycle v x) : ℝ) ≤ s := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hs1)
    exact_mod_cast this
  have hne := haft s hHs hsL
  rw [firstCycle_apply_of_lt h1.1 h1.2 hsL] at hne
  apply hne
  rw [← hwv]
  exact hw s (by linarith [le_max_right (holdTime (firstCycle v x) : ℝ) ((retLen x.1 : ℝ) - ε)])
    (by linarith)

/-- **Local constancy of the reversed cycle** at `L − u` from local constancy of the cycle at
`h + u` (`h` the holding time), off the single time `L − u = h`. -/
theorem goodAt_cycRev {v : ℕ} (c : Cyc v) {u : ℝ≥0} (hu0 : 0 < u) (huL : u < c.1.2)
    (hne : c.1.2 - u ≠ holdTime c)
    (hG : holdTime c < c.1.2 - u → GoodAt c.1.1 (holdTime c + u)) :
    GoodAt (cycRev c).1.1 (c.1.2 - u) := by
  obtain ⟨hH0, hHL, -, -⟩ := cyc_hold c
  show GoodAt (cycRevPath c.1.1 v (holdTime c) c.1.2) (c.1.2 - u)
  unfold cycRevPath
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact goodAt_glue_left hlt ⟨v, 1, one_pos, fun _ _ => rfl⟩
  · refine goodAt_glue_right hgt ?_
    have hLu : ((c.1.2 - u : ℝ≥0) : ℝ) = c.1.2 - u := NNReal.coe_sub huL.le
    have hgt' : (holdTime c : ℝ) < c.1.2 - u := by rw [← hLu]; exact_mod_cast hgt
    have h1 : ((c.1.2 - u - holdTime c : ℝ≥0) : ℝ) = c.1.2 - u - holdTime c := by
      rw [NNReal.coe_sub hgt.le, hLu]
    have h2 : ((c.1.2 - holdTime c : ℝ≥0) : ℝ) = c.1.2 - holdTime c := NNReal.coe_sub hHL.le
    have hu' : (0 : ℝ) < u := by exact_mod_cast hu0
    have hlt2 : c.1.2 - u - holdTime c < c.1.2 - holdTime c := by
      have : ((c.1.2 - u - holdTime c : ℝ≥0) : ℝ) < ((c.1.2 - holdTime c : ℝ≥0) : ℝ) := by
        rw [h1, h2]; linarith
      exact_mod_cast this
    refine goodAt_glue_left hlt2 ?_
    have hpos : 0 < c.1.2 - u - holdTime c := by
      have : (0 : ℝ) < ((c.1.2 - u - holdTime c : ℝ≥0) : ℝ) := by rw [h1]; linarith
      exact_mod_cast this
    have hlt3 : c.1.2 - u - holdTime c < c.1.2 := by
      have : ((c.1.2 - u - holdTime c : ℝ≥0) : ℝ) < c.1.2 := by
        rw [h1]; linarith [NNReal.coe_nonneg (holdTime c)]
      exact_mod_cast this
    have key : c.1.2 - (c.1.2 - u - holdTime c) = holdTime c + u := by
      apply NNReal.eq
      rw [NNReal.coe_sub hlt3.le, h1, NNReal.coe_add]
      ring
    refine goodAt_revPiece hpos hlt3 ?_
    rw [key]
    exact hG hgt

/-! ### 2. The i.i.d. concatenations -/

section Seq

variable {v : ℕ}

/-- The lengths of a cycle sequence. -/
def lens (a : ℕ → Cyc v) : ℕ → ℝ≥0 := fun k => (a k).1.2

/-- The forward concatenation of a cycle sequence. -/
noncomputable def fwdN (a : ℕ → Cyc v) : Trajectory ℕ := concat (fun k => (a k).1.1) (lens a)

/-- The concatenation of the left-limit reversals of a cycle sequence (the backward half of the
splice). -/
noncomputable def bwdN (a : ℕ → Cyc v) : Trajectory ℕ :=
  concat (fun k => revPiece (a k).1.1 (a k).1.2) (lens a)

theorem measurable_lens (k : ℕ) : Measurable fun a : ℕ → Cyc v => lens a k :=
  (measurable_snd.comp measurable_subtype_coe).comp (measurable_pi_apply k)

theorem measurable_psum_lens (k : ℕ) : Measurable fun a : ℕ → Cyc v => psum (lens a) k :=
  Finset.measurable_sum _ fun j _ => measurable_lens j

theorem measurable_cycPath (k : ℕ) : Measurable fun a : ℕ → Cyc v => (a k).1.1 :=
  (measurable_fst.comp measurable_subtype_coe).comp (measurable_pi_apply k)

theorem measurable_cycPath_eval (k : ℕ) {T : (ℕ → Cyc v) → ℝ≥0} (hT : Measurable T) :
    Measurable fun a : ℕ → Cyc v => (a k).1.1 (T a) :=
  measurable_eval_at (measurable_cycPath k) (fun a => (a k).2.regLL.regular) hT

theorem measurable_fwdN : Measurable (fwdN (v := v)) := by
  refine measurable_pi_iff.2 fun t => ?_
  exact measurable_concat_apply (piece := fun a k => (a k).1.1) (len := lens) measurable_lens t
    (fun k => (measurable_cycPath_eval k (T := fun a => t - psum (lens a) k)
      (measurable_nnreal_sub measurable_const (measurable_psum_lens k)) :
        Measurable fun a : ℕ → Cyc v => (a k).1.1 (t - psum (lens a) k)))

/-- **The forward event** of a cycle sequence: unbounded lengths and local constancy of the
concatenation at every rational time `q ≥ 0`. -/
def FG (a : ℕ → Cyc v) : Prop :=
  Unbounded (lens a) ∧ ∀ q : ℚ, 0 ≤ q → GoodAtQ (fwdN a) (q : ℝ).toNNReal

theorem measurableSet_FG : MeasurableSet {a : ℕ → Cyc v | FG a} :=
  (measurableSet_unbounded measurable_lens).inter (measurableSet_setOfPred.2
    (Measurable.forall fun _ => Measurable.imp measurable_const
      (measurable_goodAtQ.comp (measurable_fwdN.prodMk measurable_const))))

/-- **The start of every later cycle is a jump time of the forward concatenation.** -/
theorem not_goodAt_fwdN_psum (a : ℕ → Cyc v) (j : ℕ) :
    ¬ GoodAt (fwdN a) (psum (lens a) (j + 1)) := by
  intro hg
  obtain ⟨w, ε, hε, hw⟩ := goodAt_dest hg
  have hLj := Cyc.len_pos (a j)
  have hLj1 := Cyc.len_pos (a (j + 1))
  have hsucc : psum (lens a) (j + 1) = psum (lens a) j + (a j).1.2 := psum_succ _ _
  have hbr : Bracket (lens a) (j + 1) (psum (lens a) (j + 1)) :=
    ⟨le_rfl, by rw [psum_succ (lens a) (j + 1)]; exact lt_add_of_pos_right _ hLj1⟩
  have hval : fwdN a (psum (lens a) (j + 1)) = some v := by
    unfold fwdN
    rw [concat_of_bracket hbr, tsub_self]
    exact (a (j + 1)).2.start
  have hwv : w = v := by
    have := hw (psum (lens a) (j + 1)) (by linarith) (by linarith)
    rw [hval] at this
    exact (Option.some_inj.1 this).symm
  obtain ⟨hH0, hHL, -, haft⟩ := cyc_hold (a j)
  have hsucc' : (psum (lens a) (j + 1) : ℝ) = psum (lens a) j + (a j).1.2 := by
    rw [hsucc, NNReal.coe_add]
  have hHL' : (holdTime (a j) : ℝ) < (a j).1.2 := by exact_mod_cast hHL
  have hpos : (0 : ℝ) < psum (lens a) (j + 1) := by
    rw [hsucc']; linarith [NNReal.coe_nonneg (psum (lens a) j), NNReal.coe_nonneg (holdTime (a j))]
  obtain ⟨s, hs1, hs2⟩ := exists_nnreal_between
    (lo := max ((psum (lens a) j : ℝ) + holdTime (a j)) ((psum (lens a) (j + 1) : ℝ) - ε))
    (max_lt (by rw [hsucc']; linarith) (by linarith)) hpos
  have hm1 := le_max_left ((psum (lens a) j : ℝ) + holdTime (a j))
    ((psum (lens a) (j + 1) : ℝ) - ε)
  have hm2 := le_max_right ((psum (lens a) j : ℝ) + holdTime (a j))
    ((psum (lens a) (j + 1) : ℝ) - ε)
  have hjs : psum (lens a) j ≤ s := by
    have : (psum (lens a) j : ℝ) ≤ s := by linarith [NNReal.coe_nonneg (holdTime (a j))]
    exact_mod_cast this
  have hs3 : s < psum (lens a) (j + 1) := by exact_mod_cast hs2
  have hcs : ((s - psum (lens a) j : ℝ≥0) : ℝ) = s - psum (lens a) j := NNReal.coe_sub hjs
  have h := hw s (by linarith) (by linarith)
  unfold fwdN at h
  rw [concat_of_bracket ⟨hjs, hs3⟩] at h
  refine haft (s - psum (lens a) j) ?_ ?_ (hwv ▸ h)
  · have : (holdTime (a j) : ℝ) ≤ ((s - psum (lens a) j : ℝ≥0) : ℝ) := by rw [hcs]; linarith
    exact_mod_cast this
  · have : ((s - psum (lens a) j : ℝ≥0) : ℝ) < (a j).1.2 := by rw [hcs]; linarith
    exact_mod_cast this

end Seq

/-! ### 3. Independence along an i.i.d. sequence -/

/-- **Fubini along an i.i.d. sequence**: the `k`-th coordinate is independent of the partial sum
of the lengths before it. -/
theorem iid_fubini {X : Type*} [MeasurableSpace X] (ν : Measure X) [IsProbabilityMeasure ν]
    {len : X → ℝ≥0} (hlen : Measurable len) (k : ℕ) {A : Set (ℝ≥0 × X)} (hA : MeasurableSet A)
    (hsec : ∀ s : ℝ≥0, ν (Prod.mk s ⁻¹' A) = 0) :
    Measure.infinitePi (fun _ : ℕ => ν) {a | (psum (fun j => len (a j)) k, a k) ∈ A} = 0 := by
  set μ := Measure.infinitePi (fun _ : ℕ => ν) with hμ
  have hI : iIndepFun (fun (i : ℕ) (a : ℕ → X) => a i) μ :=
    iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id)
  have hind := hI.indepFun_finset (Finset.range k) {k} (by simp) (fun i => measurable_pi_apply i)
  let F : (Finset.range k → X) → ℝ≥0 := fun b => ∑ i, len (b i)
  have hF : Measurable F := Finset.measurable_sum _ fun i _ => hlen.comp (measurable_pi_apply i)
  let E : (({k} : Finset ℕ) → X) → X := fun b => b ⟨k, Finset.mem_singleton_self k⟩
  have hE : Measurable E := measurable_pi_apply _
  have e1 : (fun a : ℕ → X => psum (fun j => len (a j)) k) =
      F ∘ (fun a (i : Finset.range k) => a i) := by
    funext a
    exact (Finset.sum_coe_sort (Finset.range k) (fun j => len (a j))).symm
  have e2 : (fun a : ℕ → X => a k) = E ∘ (fun a (i : ({k} : Finset ℕ)) => a i) := rfl
  have hS : Measurable fun a : ℕ → X => psum (fun j => len (a j)) k :=
    Finset.measurable_sum _ fun j _ => hlen.comp (measurable_pi_apply j)
  have hind2 : IndepFun (fun a : ℕ → X => psum (fun j => len (a j)) k) (fun a => a k) μ := by
    rw [e1, e2]
    exact hind.comp hF hE
  have hjoint := (indepFun_iff_map_prod_eq_prod_map_map hS.aemeasurable
    (measurable_pi_apply k).aemeasurable).1 hind2
  have hk : μ.map (fun a : ℕ → X => a k) = ν := Measure.infinitePi_map_eval _ k
  have hmeas : Measurable fun a : ℕ → X => (psum (fun j => len (a j)) k, a k) :=
    hS.prodMk (measurable_pi_apply k)
  have : μ {a | (psum (fun j => len (a j)) k, a k) ∈ A} =
      (μ.map fun a : ℕ → X => (psum (fun j => len (a j)) k, a k)) A := by
    rw [Measure.map_apply hmeas hA]
    rfl
  rw [this, hjoint, hk, Measure.prod_apply hA]
  simp [hsec]

/-! ### 4. The walk from a slot: fixed times and the first exit -/

section Walk

variable {G : Set Env} (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e) {e : Env}
  (he : e ∈ G) {n : ℕ} (hn : (e.val.1 n).isSome)

theorem goodAtQ_label_of_fixed {ω : (areaFamily e).Ω} {t : ℝ≥0}
    (h : (∃ x, (areaFamily e).X t ω = some x) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Metric.ball t ε, (areaFamily e).X s ω = (areaFamily e).X t ω) :
    GoodAtQ (labelTraj ((areaFamily e).trajectory ω)) t := by
  obtain ⟨⟨u, hu⟩, ε, hε, hball⟩ := h
  refine goodAtQ_of_goodAt ⟨u.1, ε, hε, fun s hs => ?_⟩
  show ((areaFamily e).X s ω).map Subtype.val = some u.1
  rw [hball s hs, hu]
  rfl

include he hn in
/-- **Fixed-time local constancy of the walk from a slot**, on the regularity subtype. -/
theorem ae_goodAtQ_regSlotLaw (t : ℝ≥0) : ∀ᵐ f ∂regSlotLaw G hwalk n e, GoodAtQ f.1 t := by
  have hw := isReflectedWalk_areaFamily e (hwalk e he)
  obtain ⟨g, hgm, hg, hμ, -⟩ := CycleDecomposition.exists_sample_lift G hwalk he hn
  have hS : MeasurableSet {f : RegLL | GoodAtQ f.1 t} :=
    measurableSet_setOfPred.2 (measurable_goodAtQ.comp (measurable_subtype_coe.prodMk
      measurable_const))
  rw [hμ, ae_map_iff hgm.aemeasurable hS]
  filter_upwards [hg, (hw ⟨n, hn⟩).2.1 t] with ω h1 h2
  show GoodAtQ (g ω).1 t
  rw [h1]
  exact goodAtQ_label_of_fixed h2

include he hn in
/-- **Local constancy at a fixed time after the first exit** (strong Markov property at the exit
time, `CycleHolding.measure_exit_future`, and fixed-time local constancy from the exit vertex). -/
theorem ae_goodAtQ_hold_add (u : ℝ≥0) (hu : 0 < u) :
    ∀ᵐ f ∂regSlotLaw G hwalk n e, GoodAtQ f.1 (u + holdTime (firstCycle n f)) := by
  have := nontrivial_vertex e
  have hw := isReflectedWalk_areaFamily e (hwalk e he)
  have hconn := decode_connected e
  obtain ⟨g, hgm, hg, hμ, -⟩ := CycleDecomposition.exists_sample_lift G hwalk he hn
  have hgood := ae_good_pair_of_lift G hwalk he hn hgm hμ
  have hhold := ae_exitTime_eq_holdTime hn hg (hgood.mono fun _ h => h.1)
  have hD : MeasurableSet {y : Trajectory (Vertex e.val) | ¬ GoodAtQ (labelTraj y) u} :=
    measurableSet_setOfPred.2 (Measurable.not (measurable_goodAtQ.comp
      (measurable_labelTraj.prodMk measurable_const)))
  have hzero : ∀ v : Vertex e.val,
      (areaFamily e).law v {y : Trajectory (Vertex e.val) | ¬ GoodAtQ (labelTraj y) u} = 0 := by
    intro v
    rw [ProcessFamily.law, Measure.map_apply (areaFamily e).measurable_trajectory hD]
    have hae : ∀ᵐ ω ∂(areaFamily e).P v, GoodAtQ (labelTraj ((areaFamily e).trajectory ω)) u := by
      filter_upwards [(hw v).2.1 u] with ω hω
      exact goodAtQ_label_of_fixed hω
    exact ae_iff.1 hae
  have hfut : ∀ᵐ ω ∂(areaFamily e).P ⟨n, hn⟩, GoodAtQ (labelTraj (futureAt (areaFamily e).X
      (exitTime (areaFamily e).X ⟨n, hn⟩) ω)) u := by
    have h0 := measure_exit_future hw hconn (⟨n, hn⟩ : Vertex e.val) MeasurableSet.univ hD
    simp only [hzero, mul_zero, tsum_zero, preimage_univ, univ_inter] at h0
    exact ae_iff.2 h0
  have hreg := TwoSidedCycleSplice.ae_isRegLL_label e (hwalk e he) ⟨n, hn⟩
  have hS : MeasurableSet {f : RegLL | GoodAtQ f.1 (u + holdTime (firstCycle n f))} :=
    measurableSet_setOfPred.2 (measurable_goodAtQ.comp (measurable_subtype_coe.prodMk
      (measurable_const.add (measurable_holdTime.comp (measurable_firstCycle n)))))
  rw [hμ, ae_map_iff hgm.aemeasurable hS]
  filter_upwards [hg, hhold, hfut, hreg] with ω h1 h2 h3 h4
  show GoodAtQ (g ω).1 (u + holdTime (firstCycle n (g ω)))
  have hsh : labelTraj (futureAt (areaFamily e).X (exitTime (areaFamily e).X ⟨n, hn⟩) ω) =
      shiftBy (holdTime (firstCycle n (g ω))) (labelTraj ((areaFamily e).trajectory ω)) := by
    funext s
    show ((areaFamily e).X (s + (exitTime (areaFamily e).X ⟨n, hn⟩ ω).untopA) ω).map
        Subtype.val = ((areaFamily e).X (s + holdTime (firstCycle n (g ω))) ω).map Subtype.val
    rw [h2]
    rfl
  rw [hsh] at h3
  rw [h1]
  exact goodAtQ_of_goodAt (goodAt_of_shiftBy hu (goodAt_of_goodAtQ (isRegLL_shiftBy h4 _) h3))

include he hn in
/-- **(RS) A reversed cycle is locally constant at every fixed positive time**, a.s. under the
first-cycle law: by `ν.map cycRev = ν` this is local constancy a fixed time after the first exit. -/
theorem measure_bad_rev (u : ℝ≥0) (hu : 0 < u) :
    firstCycleLaw G hwalk n e {c | u < c.1.2 ∧ ¬ GoodAtQ c.1.1 (c.1.2 - u)} = 0 := by
  have hreg := forwardRegeneration_regSlotLaw G hwalk he hn
  have hL : Measurable fun c : Cyc n => c.1.2 := measurable_snd.comp measurable_subtype_coe
  have hP : Measurable fun c : Cyc n => c.1.1 := measurable_fst.comp measurable_subtype_coe
  have hA : MeasurableSet {c : Cyc n | u < c.1.2 ∧ ¬ GoodAtQ c.1.1 (c.1.2 - u)} :=
    (measurableSet_lt measurable_const hL).inter (measurableSet_setOfPred.2 (Measurable.not
      (measurable_goodAtQ.comp (hP.prodMk (measurable_nnreal_sub hL measurable_const)))))
  have hB : MeasurableSet ({c : Cyc n | c.1.2 - u = holdTime c} ∪
      {c : Cyc n | holdTime c + u < c.1.2 ∧ ¬ GoodAtQ c.1.1 (holdTime c + u)}) := by
    refine (measurableSet_eq_fun (measurable_nnreal_sub hL measurable_const) measurable_holdTime).union
      ((measurableSet_lt (measurable_holdTime.add measurable_const) hL).inter
        (measurableSet_setOfPred.2 (Measurable.not (measurable_goodAtQ.comp
          (hP.prodMk (measurable_holdTime.add measurable_const))))))
  have hb : (firstCycleLaw G hwalk n e).map cycRev = firstCycleLaw G hwalk n e :=
    CycleReversalProof.completeCycleReversal_firstCycleLaw G hwalk n e
  rw [← hb, Measure.map_apply measurable_cycRev hA]
  -- the reversed event is contained in the bad event at the first exit
  have hsub : cycRev ⁻¹' {c : Cyc n | u < c.1.2 ∧ ¬ GoodAtQ c.1.1 (c.1.2 - u)} ⊆
      {c : Cyc n | c.1.2 - u = holdTime c} ∪
        {c : Cyc n | holdTime c + u < c.1.2 ∧ ¬ GoodAtQ c.1.1 (holdTime c + u)} := by
    intro c hc
    obtain ⟨huL, hbad⟩ := hc
    by_contra hnot
    simp only [mem_union, mem_setOf_eq, not_or, not_and, not_not] at hnot
    refine hbad (goodAtQ_of_goodAt (goodAt_cycRev c hu huL hnot.1 fun hlt => ?_))
    exact goodAt_of_goodAtQ c.2.regLL (hnot.2 (lt_tsub_iff_right.1 hlt))
  refine measure_mono_null hsub ?_
  -- the bad event at the first exit is null
  have hnull : ∀ᵐ f ∂regSlotLaw G hwalk n e, Good n f ∧ Good n (nx f) ∧
      GoodAtQ f.1 (u + holdTime (firstCycle n f)) := by
    filter_upwards [ae_all_good hreg, ae_goodAtQ_hold_add hwalk he hn u hu] with f h1 h2
    exact ⟨h1 0, h1 1, h2⟩
  rw [firstCycleLaw, Measure.map_apply (measurable_firstCycle n) hB]
  refine measure_mono_null (fun f hf => ?_) (ae_iff.1 hnull)
  intro hgood
  obtain ⟨h1, h2, h3⟩ := hgood
  set c := firstCycle n f with hc
  have hLc : c.1.2 = retLen f.1 := firstCycle_len_of_good h1
  have hfreg : IsRegLL f.1 := f.2
  rcases hf with hf | hf
  · -- the excursion returns exactly `u` after the exit: a jump time
    have hf' : c.1.2 - u = holdTime c := hf
    have huL : u < c.1.2 := by
      by_contra hle
      rw [tsub_eq_zero_of_le (not_lt.1 hle)] at hf'
      exact absurd hf'.symm (cyc_hold c).1.ne'
    have hLeq : retLen f.1 = u + holdTime c := by
      rw [← hLc, ← hf', add_tsub_cancel_of_le huL.le]
    have := not_goodAt_retLen h1 h2
    rw [hLeq] at this
    exact this (goodAt_of_goodAtQ hfreg h3)
  · -- local constancy of the path gives that of its first cycle
    obtain ⟨hlt, hbad⟩ := hf
    apply hbad
    refine goodAtQ_of_goodAt (goodAt_of_agree hlt (fun s hs => firstCycle_apply_of_lt h1.1 h1.2 hs) ?_)
    rw [add_comm]
    exact goodAt_of_goodAtQ hfreg h3

include he hn in
/-- The i.i.d. cycle law is the law of the cycle sequence of the walk from the slot. -/
theorem iid_eq_map_cycSeq :
    Measure.infinitePi (fun _ : ℕ => firstCycleLaw G hwalk n e) =
      (regSlotLaw G hwalk n e).map (cycSeq n) := by
  have hreg := forwardRegeneration_regSlotLaw G hwalk he hn
  rw [map_cycSeq _ hreg.shift hreg.indep]
  rfl

include he hn in
/-- **The forward event is almost sure** for the i.i.d. cycle law. -/
theorem ae_FG : ∀ᵐ a ∂Measure.infinitePi (fun _ : ℕ => firstCycleLaw G hwalk n e), FG a := by
  have hreg := forwardRegeneration_regSlotLaw G hwalk he hn
  rw [iid_eq_map_cycSeq hwalk he hn, ae_map_iff (measurable_cycSeq n).aemeasurable measurableSet_FG]
  filter_upwards [ae_all_good hreg, ae_unbounded hreg,
    ae_all_iff.2 fun q : ℚ => ae_goodAtQ_regSlotLaw hwalk he hn (q : ℝ).toNNReal] with f h1 h2 h3
  have hc : fwdN (cycSeq n f) = f.1 := concat_cycles_eq h1 h2
  exact ⟨h2, fun q _ => by rw [hc]; exact h3 q⟩

include he hn in
/-- **The backward event is almost sure** for the i.i.d. cycle law. -/
theorem ae_bwdLab : ∀ᵐ a ∂Measure.infinitePi (fun _ : ℕ => firstCycleLaw G hwalk n e),
    ∀ q : ℚ, 0 < q → GoodAtQ (bwdN a) (q : ℝ).toNNReal := by
  have hLm : Measurable fun c : Cyc n => c.1.2 := measurable_snd.comp measurable_subtype_coe
  have hPm : Measurable fun c : Cyc n => c.1.1 := measurable_fst.comp measurable_subtype_coe
  have hbad : ∀ (q : ℚ) (k : ℕ), ∀ᵐ a ∂Measure.infinitePi (fun _ : ℕ => firstCycleLaw G hwalk n e),
      ¬ (psum (lens a) k < (q : ℝ).toNNReal ∧ (q : ℝ).toNNReal - psum (lens a) k < (a k).1.2 ∧
        ¬ GoodAtQ (a k).1.1 ((a k).1.2 - ((q : ℝ).toNNReal - psum (lens a) k))) := by
    intro q k
    rw [ae_iff]
    simp only [not_not]
    set q' := (q : ℝ).toNNReal
    have hA : MeasurableSet {p : ℝ≥0 × Cyc n | p.1 < q' ∧ q' - p.1 < p.2.1.2 ∧
        ¬ GoodAtQ p.2.1.1 (p.2.1.2 - (q' - p.1))} := by
      have h1 : Measurable fun p : ℝ≥0 × Cyc n => p.2.1.2 := hLm.comp measurable_snd
      have h2 : Measurable fun p : ℝ≥0 × Cyc n => q' - p.1 :=
        measurable_nnreal_sub measurable_const measurable_fst
      exact (measurableSet_lt measurable_fst measurable_const).inter
        ((measurableSet_lt h2 h1).inter (measurableSet_setOfPred.2 (Measurable.not
          (measurable_goodAtQ.comp ((hPm.comp measurable_snd).prodMk
            (measurable_nnreal_sub h1 h2))))))
    refine iid_fubini (firstCycleLaw G hwalk n e) hLm k hA fun s => ?_
    by_cases hs : s < q'
    · refine measure_mono_null (fun c hc => ?_) (measure_bad_rev hwalk he hn (q' - s)
        (tsub_pos_of_lt hs))
      exact ⟨hc.2.1, hc.2.2⟩
    · refine measure_mono_null (fun c hc => ?_) measure_empty
      exact hs hc.1
  filter_upwards [ae_FG hwalk he hn, ae_all_iff.2 fun q => ae_all_iff.2 fun k => hbad q k]
    with a hFG hk
  intro q hq
  set q' := (q : ℝ).toNNReal with hq'def
  have hq' : 0 < q' := Real.toNNReal_pos.2 (by exact_mod_cast hq)
  obtain ⟨k, hkb⟩ := exists_bracket (hFG.1.exists_gt q')
  rcases eq_or_lt_of_le hkb.1 with heq | hlt
  · exfalso
    cases k with
    | zero =>
      rw [psum_zero] at heq
      exact hq'.ne heq
    | succ j =>
      have hg := goodAt_of_goodAtQ (isRegLL_concat (fun k => (a k).2.regLL) hFG.1)
        (hFG.2 q hq.le)
      rw [← hq'def, ← heq] at hg
      exact not_goodAt_fwdN_psum a j hg
  · have hLk : q' - psum (lens a) k < (a k).1.2 := by
      have h2 := hkb.2
      rw [psum_succ] at h2
      exact (tsub_lt_iff_left hkb.1).2 h2
    have hgood : GoodAtQ (a k).1.1 ((a k).1.2 - (q' - psum (lens a) k)) := by
      by_contra hc
      exact hk q k ⟨hlt, hLk, hc⟩
    exact goodAtQ_of_goodAt (goodAt_concat hkb hlt (goodAt_revPiece (tsub_pos_of_lt hlt) hLk
      (goodAt_of_goodAtQ (a k).2.regLL hgood)))

include he hn in
/-- **The label event under the entrance-rooted i.i.d.-cycle law.** -/
theorem ae_lab_splice :
    ∀ᵐ ω ∂Temporal.iidCycleLaw (firstCycleLaw G hwalk n e), Lab (splice ω).1 := by
  set ν := firstCycleLaw G hwalk n e
  have hbinj : Function.Injective bwdIdx := fun a b h => by
    unfold bwdIdx at h
    omega
  have hF : (Temporal.iidCycleLaw ν).map (fun (ω : ℤ → Cyc n) (k : ℕ) => ω k) =
      Measure.infinitePi (fun _ : ℕ => ν) := by
    unfold Temporal.iidCycleLaw
    exact Measure.map_infinitePi_infinitePi_of_inj Nat.cast_injective
  have hBw : (Temporal.iidCycleLaw ν).map (fun (ω : ℤ → Cyc n) (k : ℕ) => ω (bwdIdx k)) =
      Measure.infinitePi (fun _ : ℕ => ν) := by
    unfold Temporal.iidCycleLaw
    exact Measure.map_infinitePi_infinitePi_of_inj hbinj
  have hFm : Measurable fun (ω : ℤ → Cyc n) (k : ℕ) => ω k :=
    measurable_pi_iff.2 fun k => measurable_pi_apply _
  have hBm : Measurable fun (ω : ℤ → Cyc n) (k : ℕ) => ω (bwdIdx k) :=
    measurable_pi_iff.2 fun k => measurable_pi_apply _
  have h1 : ∀ᵐ ω ∂Temporal.iidCycleLaw ν, FG (fun k : ℕ => ω k) := by
    have h := ae_FG hwalk he hn
    rw [← hF] at h
    exact ae_of_ae_map hFm.aemeasurable h
  have h2 : ∀ᵐ ω ∂Temporal.iidCycleLaw ν, FG (fun k : ℕ => ω (bwdIdx k)) ∧
      ∀ q : ℚ, 0 < q → GoodAtQ (bwdN (fun k : ℕ => ω (bwdIdx k))) (q : ℝ).toNNReal := by
    have h := (ae_FG hwalk he hn).and (ae_bwdLab hwalk he hn)
    rw [← hBw] at h
    exact ae_of_ae_map hBm.aemeasurable h
  filter_upwards [h1, h2] with ω hf hb
  have hgs : GoodSeq ω := ⟨hf.1, hb.1.1⟩
  have hsp : (splice ω).1 = (fwdPath ω, bwdPath ω) := by
    show spliceRaw ω = _
    unfold spliceRaw
    rw [if_pos hgs]
  rw [hsp]
  exact ⟨hf.2, hb.2⟩

end Walk

/-! ### 5. The two almost-sure events under the rooted kernel -/

theorem entranceLaw_map_rho {v : ℕ} (ν : Measure (Cyc v)) [IsProbabilityMeasure ν] :
    (entranceLaw ν).map rho = entranceLaw ν := by
  unfold entranceLaw
  rw [Measure.map_map measurable_rho measurable_splice]
  have hcomp : rho ∘ splice = splice ∘ Temporal.cycleShift (Cyc := Cyc v) := funext rho_splice
  rw [hcomp, ← Measure.map_map measurable_splice Temporal.measurable_cycleShift,
    (Temporal.measurePreserving_cycleShift ν).map_eq]

/-- **(P2) `Lab` along the whole orbit after one re-rooting**, from the PROVED cycle
decomposition. -/
theorem ae_lab_iterate {G : Set Env} (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e) {e : Env} (h : Live G e) :
    ∀ᵐ w ∂rootedRegKernel G hG hwalk
      (RegenerationKernelMeasurability.measurable_slotTransition G hG hwalk) e,
      ∀ k : ℕ, Lab (rho^[k + 1] w).1 := by
  set ν := firstCycleLaw G hwalk (rootLabel e) e
  have hb : CompleteCycleReversal ν :=
    CycleReversalProof.completeCycleReversal_firstCycleLaw G hwalk (rootLabel e) e
  have hc := rootedCycleDecomposition_rootedRegKernel_of G hG hwalk h.1 h.2
    (holdExcIndep_firstCycleLaw G hwalk h.1 h.2) (straddleAbsCont_firstCycleLaw G hwalk h.1 h.2)
  have hac := entranceAbsCont_of_reversal hb hc
  have hQ : ∀ᵐ u ∂entranceLaw ν, ∀ k : ℕ, Lab (rho^[k] u).1 := by
    refine ae_all_iff.2 fun k => ?_
    have hlab : ∀ᵐ u ∂entranceLaw ν, Lab u.1 := by
      have hms : MeasurableSet {u : TwoSidedReg | Lab u.1} :=
        measurableSet_setOfPred.2 (measurable_lab.comp measurable_subtype_coe)
      unfold entranceLaw
      rw [ae_map_iff measurable_splice.aemeasurable hms]
      exact ae_lab_splice hwalk h.1 h.2
    rw [← map_iterate_eq measurable_rho (entranceLaw_map_rho ν) k] at hlab
    exact ae_of_ae_map (measurable_rho.iterate k).aemeasurable hlab
  have h2 := ae_of_ae_map measurable_rho.aemeasurable (hac.ae_le hQ)
  filter_upwards [h2] with w hw k
  rw [Function.iterate_succ_apply]
  exact hw k

/-- **(P1) the càdlàg criterion and `Lab` at the root**, from the sample-space good set. -/
theorem ae_ratCadlag_lab {z : CellField} {G : Set Env} (hG : MeasurableSet G)
    (hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e) (hext : ExtensionGate z G) {e : Env}
    (h : Live G e) :
    ∀ᵐ w ∂rootedRegKernel G hG hwalk
      (RegenerationKernelMeasurability.measurable_slotTransition G hG hwalk) e,
      RatCadlag (ratCode z (e, w.1)).2 ∧ Lab w.1 := by
  set P := (areaFamily e).P (rootVertex h) with hPdef
  have hlaw : rootedLaw G e = (P.prod P).map fun ω =>
      ((labelTraj ((areaFamily e).trajectory ω.1),
        labelTraj ((areaFamily e).trajectory ω.2)) : TwoSidedCoding) := by
    have hsl : slotLaw G (rootLabel e) e = P.map fun ω =>
        labelTraj ((areaFamily e).trajectory ω) := by
      rw [slotLaw_of_mem h.1 h.2, ProcessFamily.law,
        Measure.map_map measurable_labelTraj (areaFamily e).measurable_trajectory]
      rfl
    show (slotLaw G (rootLabel e) e).prod (slotLaw G (rootLabel e) e) = _
    rw [hsl, Measure.map_prod_map _ _ measurable_labelTraj_trajectory
      measurable_labelTraj_trajectory]
    rfl
  have hpm : Measurable fun ω : (areaFamily e).Ω × (areaFamily e).Ω =>
      ((labelTraj ((areaFamily e).trajectory ω.1),
        labelTraj ((areaFamily e).trajectory ω.2)) : TwoSidedCoding) :=
    (measurable_labelTraj_trajectory.comp measurable_fst).prodMk
      (measurable_labelTraj_trajectory.comp measurable_snd)
  have hS : MeasurableSet {p : TwoSidedCoding | RatCadlag (ratCode z (e, p)).2 ∧ Lab p} :=
    (measurableSet_ratCadlag.preimage (measurable_snd.comp ((measurable_ratCode z).comp
      measurable_prodMk_left))).inter (measurableSet_setOfPred.2 measurable_lab)
  have hae : ∀ᵐ p ∂rootedLaw G e, RatCadlag (ratCode z (e, p)).2 ∧ Lab p := by
    rw [hlaw, ae_map_iff hpm.aemeasurable hS]
    filter_upwards [ae_mem_goodSet hwalk hext h] with ω hω
    have hg := halfGood_of_mem_goodSet z e (rootVertex h) hω
    refine ⟨?_, fun q _ => goodAtQ_label_of_fixed (hg.1.fixed q),
      fun q _ => goodAtQ_label_of_fixed (hg.2.fixed q)⟩
    show RatCadlag (ratCode z (e, _)).2
    rw [← ratRead_build_of_mem hω]
    exact ratCadlag_ratRead _
  rw [← rootedRegKernel_map_val G hG hwalk
    (RegenerationKernelMeasurability.measurable_slotTransition G hG hwalk) e] at hae
  exact ae_of_ae_map measurable_subtype_coe.aemeasurable hae

/-! ### 6. `hbr` -/

/-- **The rational-shift bridge at every live gate environment**, for every field with the
extension input on a measurable admissible gate. -/
theorem ratShiftBridgeOn_of_extensionGate {z : CellField} {G : Set Env} {hG : MeasurableSet G}
    {hwalk : ∀ e ∈ G, EnvironmentAreaClockAdmissible e} (hext : ExtensionGate z G) :
    CellRootedRegenAllStarts.RatShiftBridgeOn z G hG hwalk := by
  intro e he
  refine ratShiftBridge_of_ae z e ?_
  filter_upwards [ae_ratCadlag_lab hG hwalk hext he, ae_lab_iterate hG hwalk he] with w h1 h2
  refine ⟨h1.1, fun k => ?_⟩
  cases k with
  | zero => exact h1.2
  | succ k => exact h2 k

/-- **`hbr` at the interior representative and the similarity-closed gate** — the last named
input of `InvarianceMainTheoremProof.reflectedInvarianceMainTheorem`. -/
theorem ratShiftBridgeOn_interiorField :
    CellRootedRegenAllStarts.RatShiftBridgeOn InteriorRepresentative.interiorField
      SimilarityClosedGate.similarityClosedGate SimilarityClosedGate.measurableSet_similarityClosedGate
      (fun _ he => SimilarityClosedGate.environmentAreaClockAdmissible_of_mem he) :=
  ratShiftBridgeOn_of_extensionGate
    ExtensionGateAllStarts.extensionGate_interiorField_similarityClosedGate

end ReflectedGMS.RatShiftBridgeProof
