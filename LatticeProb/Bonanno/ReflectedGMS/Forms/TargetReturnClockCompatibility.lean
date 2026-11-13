/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.TargetReturnClockCompatibility at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.TargetReturnPairProcessLaw
import LatticeProb.Bonanno.ReflectedGMS.Forms.TargetOccupationClock
import LatticeProb.Bonanno.ReflectedWalk.TimeChange

/-!
# Compatibility of the target-return path and the occupation clock

Deterministic bookkeeping for the trace of a path on a finite target.  The
probabilistic inputs used later are only finiteness of all return times and
divergence of the retained holding-time clock.
-/

set_option autoImplicit false

open MeasureTheory Filter Set
open scoped NNReal ENNReal

namespace ReflectedGMS.TargetReturnClockCompatibility

open ReflectedWalk ReflectedWalk.Theorem16
open TargetOccupationClock TargetReturnRecursion
open TargetReturnPairProcessLaw

universe u

variable {V : Type u} {Ω : Type u}

/-- Adding an interval on which the path lies in the target increases the
occupation clock by the length of that interval.  The right endpoint is
irrelevant, as it is Lebesgue-null. -/
theorem occupationClock_eq_add_of_mem_Ico (A : Set V)
    (X : ℝ≥0 → Ω → Option V) (ω : Ω) {a b : ℝ≥0} (hab : a ≤ b)
    (hmem : ∀ s ∈ Ico a b, X s ω ∈ some '' A) :
    occupationClock A X b ω = occupationClock A X a ω + ((b - a : ℝ≥0) : ℝ≥0∞) := by
  let S : Set ℝ :=
    {s : ℝ | s ∈ Icc (0 : ℝ) (a : ℝ) ∧ X (Real.toNNReal s) ω ∈ some '' A}
  let T : Set ℝ := Ioc (a : ℝ) (b : ℝ)
  have hdisj : Disjoint S T := by
    refine Set.disjoint_left.2 ?_
    intro s hs ht
    exact (not_lt_of_ge hs.1.2) ht.1
  have hae :
      {s : ℝ | s ∈ Icc (0 : ℝ) (b : ℝ) ∧
          X (Real.toNNReal s) ω ∈ some '' A} =ᵐ[volume] S ∪ T := by
    filter_upwards [volume.ae_ne (b : ℝ)] with s hsb
    simp only [S, T, Set.mem_union, Set.mem_ofPred_eq, Set.mem_Icc, Set.mem_Ioc]
    apply propext
    constructor
    · intro hs
      by_cases hsa : s ≤ (a : ℝ)
      · exact Or.inl ⟨⟨hs.1.1, hsa⟩, hs.2⟩
      · exact Or.inr ⟨lt_of_not_ge hsa, hs.1.2⟩
    · rintro (hs | hs)
      · exact ⟨⟨hs.1.1, hs.1.2.trans (NNReal.coe_le_coe.2 hab)⟩, hs.2⟩
      · have hs0 : 0 ≤ s := (show (0 : ℝ) ≤ (a : ℝ) from a.property).trans hs.1.le
        have hsa' : a ≤ Real.toNNReal s := by
          apply NNReal.coe_le_coe.1
          simpa [Real.coe_toNNReal s hs0] using hs.1.le
        have hsb' : Real.toNNReal s < b := by
          apply NNReal.coe_lt_coe.1
          simpa [Real.coe_toNNReal s hs0] using lt_of_le_of_ne hs.2 hsb
        exact ⟨⟨hs0, hs.2⟩, hmem _ ⟨hsa', hsb'⟩⟩
  change volume
    {s : ℝ | s ∈ Icc (0 : ℝ) (b : ℝ) ∧ X (Real.toNNReal s) ω ∈ some '' A} =
      volume S + ((b - a : ℝ≥0) : ℝ≥0∞)
  rw [measure_congr hae, measure_union hdisj measurableSet_Ioc, Real.volume_Ioc]
  congr 1

/-- Adding an interval on which the path avoids the target leaves the
occupation clock unchanged. -/
theorem occupationClock_eq_of_notMem_Ioo (A : Set V)
    (X : ℝ≥0 → Ω → Option V) (ω : Ω) {a b : ℝ≥0} (hab : a ≤ b)
    (hnot : ∀ s ∈ Ioo a b, X s ω ∉ some '' A) :
    occupationClock A X b ω = occupationClock A X a ω := by
  apply measure_congr
  filter_upwards [volume.ae_ne (b : ℝ)] with s hsb
  simp only [Set.mem_ofPred_eq, Set.mem_Icc]
  apply propext
  constructor
  · intro hs
    refine ⟨⟨hs.1.1, ?_⟩, hs.2⟩
    by_contra hsa
    have hs0 : 0 ≤ s := hs.1.1
    have hu : Real.toNNReal s ∈ Ioo a b := by
      constructor
      · apply NNReal.coe_lt_coe.1
        simpa [Real.coe_toNNReal s hs0] using lt_of_not_ge hsa
      · apply NNReal.coe_lt_coe.1
        simpa [Real.coe_toNNReal s hs0] using lt_of_le_of_ne hs.1.2 hsb
    exact hnot _ hu hs.2
  · intro hs
    exact ⟨⟨hs.1.1, hs.1.2.trans (NNReal.coe_le_coe.2 hab)⟩, hs.2⟩

section Returns

variable [MeasurableSpace Ω] [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V]

noncomputable def targetReturnAt (X : ℝ≥0 → Ω → Option V)
    (A : Finset V) (n : ℕ) (ω : Ω) : ℝ≥0 :=
  (targetReturnTime X A n ω).untopA

noncomputable def targetExitAt (X : ℝ≥0 → Ω → Option V)
    (A : Finset V) (n : ℕ) (ω : Ω) : ℝ≥0 :=
  (exitAfter X (targetReturnTime X A n) ω).untopA

lemma coe_targetReturnAt {X : ℝ≥0 → Ω → Option V} {A : Finset V} {n : ℕ} {ω : Ω}
    (hfin : targetReturnTime X A n ω ≠ ⊤) :
    ((targetReturnAt X A n ω : ℝ≥0) : WithTop ℝ≥0) = targetReturnTime X A n ω := by
  exact ReflectedWalk.Theorem16.TimeChange.coe_untopA hfin

lemma targetExit_ne_top {X : ℝ≥0 → Ω → Option V} {A : Finset V} {n : ℕ} {ω : Ω}
    (hfin : targetReturnTime X A (n + 1) ω ≠ ⊤) :
    exitAfter X (targetReturnTime X A n) ω ≠ ⊤ :=
  ne_top_of_le_ne_top hfin (exitAfter_targetReturnTime_le_succ X A n ω)

lemma coe_targetExitAt {X : ℝ≥0 → Ω → Option V} {A : Finset V} {n : ℕ} {ω : Ω}
    (hfin : exitAfter X (targetReturnTime X A n) ω ≠ ⊤) :
    ((targetExitAt X A n ω : ℝ≥0) : WithTop ℝ≥0) =
      exitAfter X (targetReturnTime X A n) ω := by
  exact ReflectedWalk.Theorem16.TimeChange.coe_untopA hfin

lemma targetReturnAt_le_exitAt {X : ℝ≥0 → Ω → Option V} {A : Finset V}
    {n : ℕ} {ω : Ω} (hfin : ∀ j, targetReturnTime X A j ω ≠ ⊤) :
    targetReturnAt X A n ω ≤ targetExitAt X A n ω := by
  rw [← WithTop.coe_le_coe, coe_targetReturnAt (hfin n),
    coe_targetExitAt (targetExit_ne_top (hfin (n + 1)))]
  exact le_hitAfter ω

lemma targetExitAt_le_succ {X : ℝ≥0 → Ω → Option V} {A : Finset V}
    {n : ℕ} {ω : Ω} (hfin : ∀ j, targetReturnTime X A j ω ≠ ⊤) :
    targetExitAt X A n ω ≤ targetReturnAt X A (n + 1) ω := by
  rw [← WithTop.coe_le_coe, coe_targetExitAt (targetExit_ne_top (hfin (n + 1))),
    coe_targetReturnAt (hfin (n + 1))]
  exact exitAfter_targetReturnTime_le_succ X A n ω

lemma targetReturnAt_zero {X : ℝ≥0 → Ω → Option V} {A : Finset V} {ω : Ω} :
    targetReturnAt X A 0 ω = 0 := rfl

lemma targetReturnAt_le_succ {X : ℝ≥0 → Ω → Option V} {A : Finset V}
    {n : ℕ} {ω : Ω} (hfin : ∀ j, targetReturnTime X A j ω ≠ ⊤) :
    targetReturnAt X A n ω ≤ targetReturnAt X A (n + 1) ω :=
  (targetReturnAt_le_exitAt hfin).trans (targetExitAt_le_succ hfin)

lemma targetReturnAt_mono {X : ℝ≥0 → Ω → Option V} {A : Finset V}
    {j k : ℕ} {ω : Ω} (hfin : ∀ n, targetReturnTime X A n ω ≠ ⊤) (hjk : j ≤ k) :
    targetReturnAt X A j ω ≤ targetReturnAt X A k ω := by
  induction k with
  | zero => rw [Nat.le_zero.1 hjk]
  | succ k ih =>
      rcases Nat.lt_or_ge j (k + 1) with h | h
      · exact (ih (Nat.lt_succ_iff.1 h)).trans (targetReturnAt_le_succ hfin)
      · rw [Nat.le_antisymm hjk h]

lemma eq_stoppedValue_of_mem_target_hold {X : ℝ≥0 → Ω → Option V} {A : Finset V}
    {n : ℕ} {ω : Ω} (hfin : ∀ j, targetReturnTime X A j ω ≠ ⊤)
    {s : ℝ≥0} (h1 : targetReturnAt X A n ω ≤ s) (h2 : s < targetExitAt X A n ω) :
    X s ω = stoppedValue X (targetReturnTime X A n) ω := by
  have he : exitAfter X (targetReturnTime X A n) ω =
      hittingAfter X {o : Option V | o ≠ stoppedValue X (targetReturnTime X A n) ω}
        (targetReturnAt X A n ω) ω :=
    hitAfter_coe (coe_targetReturnAt (hfin n)).symm
  have h2' : (s : WithTop ℝ≥0) < exitAfter X (targetReturnTime X A n) ω := by
    rw [← coe_targetExitAt (targetExit_ne_top (hfin (n + 1)))]
    exact WithTop.coe_lt_coe.2 h2
  rw [he] at h2'
  simpa using notMem_of_lt_hittingAfter
    (u := X) (s := {o : Option V | o ≠ stoppedValue X (targetReturnTime X A n) ω}) h2' h1

lemma notMem_target_of_between_exit_return {X : ℝ≥0 → Ω → Option V} {A : Finset V}
    {n : ℕ} {ω : Ω} (hfin : ∀ j, targetReturnTime X A j ω ≠ ⊤)
    {s : ℝ≥0} (h1 : targetExitAt X A n ω ≤ s)
    (h2 : s < targetReturnAt X A (n + 1) ω) :
    X s ω ∉ some '' (A : Set V) := by
  have he : targetReturnTime X A (n + 1) ω =
      hittingAfter X (some '' (A : Set V)) (targetExitAt X A n ω) ω := by
    rw [targetReturnTime, hitAfter_coe
      (coe_targetExitAt (targetExit_ne_top (hfin (n + 1)))).symm]
  have h2' : (s : WithTop ℝ≥0) < targetReturnTime X A (n + 1) ω := by
    rw [← coe_targetReturnAt (hfin (n + 1))]
    exact WithTop.coe_lt_coe.2 h2
  rw [he] at h2'
  exact notMem_of_lt_hittingAfter h2' h1

lemma targetHolding_eq_coe {X : ℝ≥0 → Ω → Option V} {A : Finset V}
    {n : ℕ} {ω : Ω} (hfin : ∀ j, targetReturnTime X A j ω ≠ ⊤) :
    targetReturnHolding X A n ω =
      ((targetExitAt X A n ω - targetReturnAt X A n ω : ℝ≥0) : ℝ≥0∞) := by
  have h1 : exitAfter X (targetReturnTime X A n) ω =
      ((targetExitAt X A n ω : ℝ≥0) : ℝ≥0∞) :=
    (coe_targetExitAt (targetExit_ne_top (hfin (n + 1)))).symm
  have h2 : targetReturnTime X A n ω =
      ((targetReturnAt X A n ω : ℝ≥0) : ℝ≥0∞) :=
    (coe_targetReturnAt (hfin n)).symm
  rw [targetReturnHolding, h1, h2, ENNReal.coe_sub]
  rfl

lemma ofReal_targetHoldingSeq_eq_coe {X : ℝ≥0 → Ω → Option V} {A : Finset V}
    {n : ℕ} {ω : Ω} (hfin : ∀ j, targetReturnTime X A j ω ≠ ⊤) :
    ENNReal.ofReal (targetReturnHoldingSeq X A ω n) =
      ((targetExitAt X A n ω - targetReturnAt X A n ω : ℝ≥0) : ℝ≥0∞) := by
  rw [targetReturnHoldingSeq, targetHolding_eq_coe hfin]
  simp

lemma jumpClock_targetReturnPair_succ {X : ℝ≥0 → Ω → Option V} {A : Finset V}
    {default : V} {n : ℕ} {ω : Ω} (hfin : ∀ j, targetReturnTime X A j ω ≠ ⊤) :
    ContinuousTimeChain.jumpClock (targetReturnPair X A default ω).2 (n + 1) =
      ContinuousTimeChain.jumpClock (targetReturnPair X A default ω).2 n +
        ((targetExitAt X A n ω - targetReturnAt X A n ω : ℝ≥0) : ℝ≥0∞) := by
  rw [ContinuousTimeChain.jumpClock, ContinuousTimeChain.jumpClock,
    Finset.sum_range_succ]
  simp only [targetReturnPair]
  rw [ofReal_targetHoldingSeq_eq_coe hfin]

/-- At each original return time, the true occupation clock equals the sum of
the retained target holding times. -/
theorem occupationClock_targetReturnAt {X : ℝ≥0 → Ω → Option V} {A : Finset V}
    {default : V} {ω : Ω} (hfin : ∀ j, targetReturnTime X A j ω ≠ ⊤)
    (hreturn : ∀ j, stoppedValue X (targetReturnTime X A j) ω ∈ some '' (A : Set V))
    (n : ℕ) :
    occupationClock (A : Set V) X (targetReturnAt X A n ω) ω =
      ContinuousTimeChain.jumpClock (targetReturnPair X A default ω).2 n := by
  induction n with
  | zero =>
      rw [targetReturnAt_zero]
      change volume {s : ℝ | s ∈ Icc (0 : ℝ) 0 ∧
        X (Real.toNNReal s) ω ∈ some '' (A : Set V)} = 0
      refine measure_mono_null (t := {(0 : ℝ)}) ?_ Real.volume_singleton
      intro s hs
      simpa using hs.1
  | succ n ih =>
      have hae : targetReturnAt X A n ω ≤ targetExitAt X A n ω :=
        targetReturnAt_le_exitAt hfin
      have heb : targetExitAt X A n ω ≤ targetReturnAt X A (n + 1) ω :=
        targetExitAt_le_succ hfin
      have hstay : ∀ s ∈ Ico (targetReturnAt X A n ω) (targetExitAt X A n ω),
          X s ω ∈ some '' (A : Set V) := by
        intro s hs
        rw [eq_stoppedValue_of_mem_target_hold hfin hs.1 hs.2]
        exact hreturn n
      have hout : ∀ s ∈ Ioo (targetExitAt X A n ω) (targetReturnAt X A (n + 1) ω),
          X s ω ∉ some '' (A : Set V) := by
        intro s hs
        exact notMem_target_of_between_exit_return hfin hs.1.le hs.2
      rw [occupationClock_eq_of_notMem_Ioo (A : Set V) X ω heb hout,
        occupationClock_eq_add_of_mem_Ico (A : Set V) X ω hae hstay, ih,
        jumpClock_targetReturnPair_succ hfin]

/-- The original return times cover every finite time once the retained
holding-time sum diverges. -/
theorem exists_targetReturn_interval {X : ℝ≥0 → Ω → Option V} {A : Finset V}
    {default : V} {ω : Ω} (hfin : ∀ j, targetReturnTime X A j ω ≠ ⊤)
    (hreturn : ∀ j, stoppedValue X (targetReturnTime X A j) ω ∈ some '' (A : Set V))
    (hdiv : ∑' j, ENNReal.ofReal ((targetReturnPair X A default ω).2 j) = ⊤)
    (u : ℝ≥0) :
    ∃ n, targetReturnAt X A n ω ≤ u ∧ u < targetReturnAt X A (n + 1) ω := by
  have hsup :
      (⨆ n, ContinuousTimeChain.jumpClock (targetReturnPair X A default ω).2 n) = ⊤ := by
    calc
      (⨆ n, ContinuousTimeChain.jumpClock (targetReturnPair X A default ω).2 n) =
          ⨆ n, ∑ j ∈ Finset.range n,
            ENNReal.ofReal ((targetReturnPair X A default ω).2 j) := rfl
      _ = ∑' j, ENNReal.ofReal ((targetReturnPair X A default ω).2 j) :=
        ENNReal.tsum_eq_iSup_nat.symm
      _ = ⊤ := hdiv
  have hexClock : ∃ n,
      (u : ℝ≥0∞) < ContinuousTimeChain.jumpClock (targetReturnPair X A default ω).2 n := by
    refine lt_iSup_iff.mp ?_
    rw [hsup]
    exact ENNReal.coe_lt_top
  have hex : ∃ n, u < targetReturnAt X A n ω := by
    obtain ⟨n, hn⟩ := hexClock
    refine ⟨n, ?_⟩
    apply ENNReal.coe_lt_coe.1
    exact hn.trans_le ((occupationClock_targetReturnAt (default := default) hfin hreturn n).symm ▸
      occupationClock_le (A : Set V) X (targetReturnAt X A n ω) ω)
  have hspec : u < targetReturnAt X A (Nat.find hex) ω := Nat.find_spec hex
  have hpos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with hzero | hpos
    · rw [hzero, targetReturnAt_zero] at hspec
      exact absurd hspec (not_lt.2 zero_le)
    · exact hpos
  refine ⟨Nat.find hex - 1, not_lt.1 (Nat.find_min hex (by omega)), ?_⟩
  rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega]
  exact hspec

/-- The target-return jump path, read at the true target occupation clock,
recovers the original path whenever the latter is in the target. -/
theorem targetTrace_at_occupationClock {X : ℝ≥0 → Ω → Option V} {A : Finset V}
    {default : V} {ω : Ω} (hfin : ∀ j, targetReturnTime X A j ω ≠ ⊤)
    (hreturn : ∀ j, stoppedValue X (targetReturnTime X A j) ω ∈ some '' (A : Set V))
    (hdiv : ∑' j, ENNReal.ofReal ((targetReturnPair X A default ω).2 j) = ⊤)
    (u : ℝ≥0) (hu : X u ω ∈ some '' (A : Set V)) :
    ContinuousTimeChain.jumpPath (targetReturnPair X A default ω)
        (occupationClock (A : Set V) X u ω).toNNReal = X u ω := by
  obtain ⟨n, hτu, huτ⟩ := exists_targetReturn_interval hfin hreturn hdiv u
  have huExit : u < targetExitAt X A n ω := by
    by_contra h
    exact (notMem_target_of_between_exit_return hfin (not_lt.1 h) huτ) hu
  have hXu : X u ω = stoppedValue X (targetReturnTime X A n) ω :=
    eq_stoppedValue_of_mem_target_hold hfin hτu huExit
  have hclock : occupationClock (A : Set V) X u ω =
      occupationClock (A : Set V) X (targetReturnAt X A n ω) ω +
        ((u - targetReturnAt X A n ω : ℝ≥0) : ℝ≥0∞) :=
    occupationClock_eq_add_of_mem_Ico (A : Set V) X ω hτu fun s hs => by
      rw [eq_stoppedValue_of_mem_target_hold hfin hs.1 (hs.2.trans huExit)]
      exact hreturn n
  have hclockTop : occupationClock (A : Set V) X u ω ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top (occupationClock_le (A : Set V) X u ω)
  have hin : ContinuousTimeChain.InJump (targetReturnPair X A default ω).2 n
      (((occupationClock (A : Set V) X u ω).toNNReal : ℝ≥0) : ℝ≥0∞) := by
    rw [ENNReal.coe_toNNReal hclockTop, hclock,
      occupationClock_targetReturnAt (default := default) hfin hreturn n]
    change ContinuousTimeChain.jumpClock (targetReturnPair X A default ω).2 n ≤
        ContinuousTimeChain.jumpClock (targetReturnPair X A default ω).2 n +
          ((u - targetReturnAt X A n ω : ℝ≥0) : ℝ≥0∞) ∧
      ContinuousTimeChain.jumpClock (targetReturnPair X A default ω).2 n +
          ((u - targetReturnAt X A n ω : ℝ≥0) : ℝ≥0∞) <
        ContinuousTimeChain.jumpClock (targetReturnPair X A default ω).2 (n + 1)
    constructor
    · exact le_add_right le_rfl
    · rw [jumpClock_targetReturnPair_succ (default := default) hfin]
      apply ENNReal.add_lt_add_left
      · simp [ContinuousTimeChain.jumpClock]
      · have hsub : u - targetReturnAt X A n ω <
            targetExitAt X A n ω - targetReturnAt X A n ω :=
          tsub_lt_tsub_right_of_le hτu huExit
        have hsub' : ((u - targetReturnAt X A n ω : ℝ≥0) : ℝ≥0∞) <
            ((targetExitAt X A n ω - targetReturnAt X A n ω : ℝ≥0) : ℝ≥0∞) := by
          exact_mod_cast hsub
        simpa only [ENNReal.coe_sub] using hsub'
  rw [ContinuousTimeChain.jumpPath_eq_of_inJump hin]
  change some ((stoppedValue X (targetReturnTime X A n) ω).getD default) = X u ω
  obtain ⟨y, -, hy⟩ := hreturn n
  calc
    some ((stoppedValue X (targetReturnTime X A n) ω).getD default) = some y := by
      rw [← hy]
      simp
    _ = X u ω := hy.trans hXu.symm

end Returns

end ReflectedGMS.TargetReturnClockCompatibility
