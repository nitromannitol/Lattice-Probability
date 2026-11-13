/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedWalk.TimeChange at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.UniquenessLimit
import LatticeProb.Bonanno.ReflectedWalk.ContinuousTimeChain

/-!
# The time change (3.32) and the covering lemma (Gwynne–Sung, arXiv:2506.18827, Section 3.4)

`UniquenessSkeleton.lean` builds the stopping times `tⁿ_j` of (3.31) out of an arbitrary
process `X̃` satisfying the properties (i)–(vi) of Theorem 1.6 (`stepTime`, `exitAfter`,
`nextStep`) and proves that they are stopping times and random variables.  This file supplies
the **pathwise** half of Step 1 and Step 2 of the uniqueness proof, which the skeleton does not:

1. the time change **(3.32)**, `X̃ⁿ_t := X̃_{tⁿ_k}` for the unique `k` with
   `t ∈ [∑_{j<k} Tⁿ_j, ∑_{j≤k} Tⁿ_j)` (`processN`), expressed through the *same* measurable
   functional `ContinuousTimeChain.jumpPath` that reads the constructed chain `Xⁿ` of (3.15)
   off its embedded chain and holding times, so that the law identification of Step 1 is a
   pushforward along one fixed map (`processN_eq_jumpPath`);
2. the **covering lemma**: every time lies in `[tⁿ_j, tⁿ_{j+1})` for some `j`
   (`exists_mem_Ico`), with the sharpening at the times the paper cares about: if
   `X̃_t ∈ VG_n` then the `j` with `t ∈ [tⁿ_j, tⁿ_{j+1})` has `X̃_{tⁿ_j} = X̃_t ∈ VG_n` and
   `Tⁿ_j = tⁿ_{j+1} − tⁿ_j` (`posAt_eq_of_mem_Ico`);
3. the **rewind bound (3.33)–(3.34)**: the lag `Rⁿ = tⁿ_j − ∑_{i<j} Tⁿ_i` between the real and
   the compressed clock is at most the sojourn `∫₀ᵗ 1(X̃_s ∉ G_n) ds` (`lag_le_sojourn`), and
   consequently `X̃ⁿ_{t − Rⁿ} = X̃_t` (`processN_sub_lag_eq`), which with property (i) upgrades
   to `X̃ⁿ_t = X̃_t` for all `n` with `∫₀ᵗ 1(X̃_s ∉ G_n) ds` below the constancy radius of the
   path at `t` (`processN_eq_of_sojourn_lt`) and hence to Step 2 itself
   (`approximatedAtFixedTimes_processN`).  `RewindBound`/`rewindBound_processN` record
   (3.33)–(3.34) in the shape of `UniquenessLimit.ShiftBound`.

## The orientation of (3.33), and why `ShiftBound` is not what is proved

The paper's (3.33) reads `X̃ⁿ_t = X̃_{t−Rⁿ}`, and `UniquenessLimit.ShiftBound` transcribes it
literally.  That orientation is a slip: the compressed clock `Sⁿ_k := ∑_{j<k} Tⁿ_j` runs
*behind* the real clock, `Sⁿ_k ≤ tⁿ_k` (`stepSum_le_stepAt`, because
`Tⁿ_j ≤ tⁿ_{j+1} − tⁿ_j` with equality only while `X̃_{tⁿ_j} ∈ G_n`), so `X̃ⁿ` at clock value
`t` reports the position of `X̃` at the *later* real time `tⁿ_k ≥ t`.  What is true — and what
(3.34) bounds, since the lag accumulated before `tⁿ_j ≤ t` is a union of excursion intervals
inside `{s ≤ t : X̃_s ∉ G_n}` — is the transpose,

  `X̃ⁿ_{t − Rⁿ} = X̃_t`,  `0 ≤ Rⁿ ≤ ∫₀ᵗ 1(X̃_s ∉ G_n) ds`,

which is `processN_sub_lag_eq` together with `lag_le_sojourn`.  `ShiftBound` as literally
stated is false: for a fixed `n` and a path with a long excursion outside `G_n` just after `t`,
`X̃ⁿ_t` is the position of `X̃` at a time beyond that excursion, and no rewind of `t` by at most
`∫₀ᵗ 1(X̃_s ∉ G_n) ds` reaches it.  Nothing downstream is lost: `ShiftBound` is only an
intermediate step towards `ApproximatedAtFixedTimes`, which is what `ApproximatedBy` — and
hence `uniqueness_half` — actually consumes, and which `approximatedAtFixedTimes_processN`
proves directly.  The extra ingredient that the transposed form needs, and that the paper
glosses, is that `X̃ⁿ` is constant on `[Sⁿ_j, Sⁿ_{j+1})` and that `t` lies in that interval
together with `t − Rⁿ` as soon as `Rⁿ` is below the constancy radius of `X̃` at `t`.

## Hypotheses carried, and who discharges them

Two facts about the recursion (3.31) are *distributional* and are therefore taken as pathwise
hypotheses on the outcome, each named after the result on the law side that discharges it:

* `StepTimesFinite X Gn ω` — every `tⁿ_j` is finite.  Almost sure by
  `UniquenessGeneralSide.ae_forall_definedAt` (whose `definedAt` is `tⁿ_j < ∞` together with
  `X̃_{tⁿ_j} ∈ VG`), through `mem_definedAt_iff`.
* `∑' j, stepHolding X Gn j ω = ⊤` — the level-`n` holding times diverge, the paper's "By
  Property (v), a.s. `X̃` returns to its starting point infinitely many times … a.s.
  `lim_k ∑_{j≤k} Tⁿ_j = ∞`" (p. 26).  `stepHolding` is *definitionally*
  `UniquenessGeneralSide.holdingTime`, so that file's divergence statement applies verbatim.

## What is not here

Nothing about *laws*: the identification of the law of `embeddedPair` — the pair
`((X̃_{tⁿ_j})_j, (Tⁿ_j)_j)` — with `E.chainLaw hG n z ⊗ₘ holdingKernel w`, which is the rest of
Step 1, lives in `UniquenessGeneralSide.lean`; `processN_eq_jumpPath_embeddedPair` is the point
where the two meet, and `ContinuousTimeChain.measure_processN_eq` is the template for reading the
one-time marginals off that law.  Nor measurability: `UniquenessLimit.ApproximatedBy` asks for
`Measurable (Xn n s)` while the times `tⁿ_j` of (3.31) are only a.e.-measurable
(`UniquenessSkeleton.stepTime_isAEStoppingTime_aemeasurable`), so (3.32) has to be replaced by a
measurable version; `approximatedAtFixedTimes_congr` transports Step 2 to any such version.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

universe u

namespace ReflectedWalk
namespace Theorem16
namespace TimeChange

variable {V : Type u} {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {X : ℝ≥0 → Ω → Option V} {P : Measure Ω} {Gn : Finset V} {j : ℕ} {ω : Ω}

/-! ### Hitting times: monotonicity in the target, and what lies before them -/

omit mΩ in
/-- A larger target is hit no later: `hittingAfter` is antitone in the target set. -/
lemma hittingAfter_mono_target {S S' : Set (Option V)} (hSS' : S' ⊆ S) (a : ℝ≥0) (ω : Ω) :
    hittingAfter X S a ω ≤ hittingAfter X S' a ω := by
  classical
  by_cases h' : ∃ b : ℝ≥0, a ≤ b ∧ X b ω ∈ S'
  · have h : ∃ b : ℝ≥0, a ≤ b ∧ X b ω ∈ S := by
      obtain ⟨b, hb, hbS⟩ := h'
      exact ⟨b, hb, hSS' hbS⟩
    simp only [hittingAfter]
    rw [ite_eq_left h, ite_eq_left h']
    refine WithTop.coe_le_coe.2 (csInf_le_csInf ?_ ?_ ?_)
    · exact ⟨a, fun b hb => hb.1⟩
    · obtain ⟨b, hb, hbS⟩ := h'
      exact ⟨b, hb, hbS⟩
    · exact fun b hb => ⟨hb.1, hSS' hb.2⟩
  · simp only [hittingAfter]
    rw [ite_eq_right h']
    exact le_top

omit mΩ in
/-- `hitAfter` is antitone in the target set. -/
lemma hitAfter_mono_target {S S' : Set (Option V)} (hSS' : S' ⊆ S) (σ : Ω → WithTop ℝ≥0)
    (ω : Ω) : hitAfter X S σ ω ≤ hitAfter X S' σ ω := by
  cases h : σ ω with
  | top => rw [hitAfter_top h]; exact le_of_eq (hitAfter_top h).symm
  | coe a => rw [hitAfter_coe h, hitAfter_coe h]; exact hittingAfter_mono_target hSS' a ω

/-! ### The times and positions of (3.31), as data in `[0,∞)` -/

/-- `tⁿ_j` of (3.31) as an element of `[0,∞)` (junk value on `{tⁿ_j = ∞}`). -/
noncomputable def stepAt (X : ℝ≥0 → Ω → Option V) (Gn : Finset V) (j : ℕ) (ω : Ω) : ℝ≥0 :=
  (stepTime X Gn j ω).untopA

/-- `min{t ≥ tⁿ_j : X̃_t ≠ X̃_{tⁿ_j}}` of (3.31) as an element of `[0,∞)`. -/
noncomputable def exitAt (X : ℝ≥0 → Ω → Option V) (Gn : Finset V) (j : ℕ) (ω : Ω) : ℝ≥0 :=
  (exitAfter X (stepTime X Gn j) ω).untopA

/-- The position `X̃_{tⁿ_j}` of the embedded chain. -/
noncomputable def posAt (X : ℝ≥0 → Ω → Option V) (Gn : Finset V) (j : ℕ) (ω : Ω) : Option V :=
  stoppedValue X (stepTime X Gn j) ω

omit mΩ in
lemma posAt_eq_apply (X : ℝ≥0 → Ω → Option V) (Gn : Finset V) (j : ℕ) (ω : Ω) :
    posAt X Gn j ω = X (stepAt X Gn j ω) ω := rfl

/-- The holding time `Tⁿ_j` of (3.31), `min{t ≥ tⁿ_j : X̃_t ≠ X̃_{tⁿ_j}} − tⁿ_j`.  This is
*definitionally* `UniquenessGeneralSide.holdingTime`. -/
noncomputable def stepHolding (X : ℝ≥0 → Ω → Option V) (Gn : Finset V) (j : ℕ) (ω : Ω) : ℝ≥0∞ :=
  exitAfter X (stepTime X Gn j) ω - stepTime X Gn j ω

/-- **The recursion (3.31) does not get stuck at `ω`**: every `tⁿ_j` is finite.  Almost sure by
`UniquenessGeneralSide.ae_forall_definedAt`. -/
def StepTimesFinite (X : ℝ≥0 → Ω → Option V) (Gn : Finset V) (ω : Ω) : Prop :=
  ∀ j : ℕ, stepTime X Gn j ω ≠ ⊤

omit mΩ in
lemma coe_untopA {x : WithTop ℝ≥0} (hx : x ≠ ⊤) : ((x.untopA : ℝ≥0) : WithTop ℝ≥0) = x := by
  cases x with
  | top => exact absurd rfl hx
  | coe a => rfl

omit mΩ in
lemma coe_stepAt (h : stepTime X Gn j ω ≠ ⊤) :
    ((stepAt X Gn j ω : ℝ≥0) : WithTop ℝ≥0) = stepTime X Gn j ω := coe_untopA h

omit mΩ in
/-- `tⁿ_j ≤ min{t ≥ tⁿ_j : X̃_t ≠ X̃_{tⁿ_j}}`. -/
lemma stepTime_le_exitAfter (j : ℕ) (ω : Ω) :
    stepTime X Gn j ω ≤ exitAfter X (stepTime X Gn j) ω := le_hitAfter ω

omit mΩ in
/-- **The exit time comes no later than the next step time** (p. 26, first sentence): with
equality when `X̃_{tⁿ_j} ∈ G_n`, and possibly strictly when `X̃_{tⁿ_j} ∈ B₁G_n \ G_n`. -/
lemma exitAfter_le_stepTime_succ (j : ℕ) (ω : Ω) :
    exitAfter X (stepTime X Gn j) ω ≤ stepTime X Gn (j + 1) ω := by
  rw [show stepTime X Gn (j + 1) = nextStep X Gn (stepTime X Gn j) from rfl, nextStep, exitAfter]
  split_ifs with hv
  · exact le_rfl
  · refine hitAfter_mono_target ?_ _ _
    intro o ho hc
    rw [← hc] at hv
    exact hv ho

omit mΩ in
lemma stepTime_le_succ (j : ℕ) (ω : Ω) :
    stepTime X Gn j ω ≤ stepTime X Gn (j + 1) ω :=
  (stepTime_le_exitAfter j ω).trans (exitAfter_le_stepTime_succ j ω)

omit mΩ in
lemma stepTime_mono {j k : ℕ} (hjk : j ≤ k) (ω : Ω) :
    stepTime X Gn j ω ≤ stepTime X Gn k ω := by
  induction k with
  | zero => rw [Nat.le_zero.1 hjk]
  | succ k ih =>
    rcases Nat.lt_or_ge j (k + 1) with h | h
    · exact (ih (Nat.lt_succ_iff.1 h)).trans (stepTime_le_succ k ω)
    · rw [Nat.le_antisymm hjk h]

omit mΩ in
/-- **The path is constant on `[tⁿ_j, tⁿ_j + Tⁿ_j)`** — the meaning of the exit time. -/
lemma eq_posAt_of_lt_exitAfter (hfin : stepTime X Gn j ω ≠ ⊤) {s : ℝ≥0}
    (h1 : stepAt X Gn j ω ≤ s) (h2 : (s : WithTop ℝ≥0) < exitAfter X (stepTime X Gn j) ω) :
    X s ω = posAt X Gn j ω := by
  have he : exitAfter X (stepTime X Gn j) ω =
      hittingAfter X {o : Option V | o ≠ posAt X Gn j ω} (stepAt X Gn j ω) ω :=
    hitAfter_coe (coe_stepAt hfin).symm
  rw [he] at h2
  have := notMem_of_lt_hittingAfter (u := X) (s := {o : Option V | o ≠ posAt X Gn j ω}) h2 h1
  simpa using this

omit mΩ in
/-- **On an excursion the path stays outside `G_n`**: if `X̃_{tⁿ_j} ∉ G_n`, then `tⁿ_{j+1}` is
the first visit to `G_n` after `tⁿ_j`, so `X̃_s ∉ G_n` for `s ∈ [tⁿ_j, tⁿ_{j+1})`. -/
lemma notMem_of_lt_stepTime_succ (hfin : stepTime X Gn j ω ≠ ⊤)
    (hv : posAt X Gn j ω ∉ some '' (Gn : Set V)) {s : ℝ≥0} (h1 : stepAt X Gn j ω ≤ s)
    (h2 : (s : WithTop ℝ≥0) < stepTime X Gn (j + 1) ω) :
    X s ω ∉ some '' (Gn : Set V) := by
  have he : stepTime X Gn (j + 1) ω = hittingAfter X (some '' (Gn : Set V)) (stepAt X Gn j ω) ω := by
    rw [show stepTime X Gn (j + 1) = nextStep X Gn (stepTime X Gn j) from rfl,
      nextStep_eq_of_notMem hv]
    exact hitAfter_coe (coe_stepAt hfin).symm
  rw [he] at h2
  exact notMem_of_lt_hittingAfter h2 h1

/-! ### The compressed clock `Sⁿ_k = ∑_{j<k} Tⁿ_j` of (3.32)

All of the bookkeeping of (3.31)–(3.32) happens on the event `StepTimesFinite`, where it can be
carried out in `[0,∞)`. -/

omit mΩ in
lemma exitAfter_ne_top (hfin : StepTimesFinite X Gn ω) (j : ℕ) :
    exitAfter X (stepTime X Gn j) ω ≠ ⊤ :=
  ne_top_of_le_ne_top (hfin (j + 1)) (exitAfter_le_stepTime_succ j ω)

omit mΩ in
lemma coe_exitAt (h : exitAfter X (stepTime X Gn j) ω ≠ ⊤) :
    ((exitAt X Gn j ω : ℝ≥0) : WithTop ℝ≥0) = exitAfter X (stepTime X Gn j) ω := coe_untopA h

omit mΩ in
lemma stepAt_zero : stepAt X Gn 0 ω = 0 := rfl

omit mΩ in
lemma stepAt_le_exitAt (hfin : StepTimesFinite X Gn ω) (j : ℕ) :
    stepAt X Gn j ω ≤ exitAt X Gn j ω := by
  rw [← WithTop.coe_le_coe, coe_stepAt (hfin j), coe_exitAt (exitAfter_ne_top hfin j)]
  exact stepTime_le_exitAfter j ω

omit mΩ in
lemma exitAt_le_stepAt_succ (hfin : StepTimesFinite X Gn ω) (j : ℕ) :
    exitAt X Gn j ω ≤ stepAt X Gn (j + 1) ω := by
  rw [← WithTop.coe_le_coe, coe_exitAt (exitAfter_ne_top hfin j), coe_stepAt (hfin (j + 1))]
  exact exitAfter_le_stepTime_succ j ω

omit mΩ in
lemma stepAt_le_succ (hfin : StepTimesFinite X Gn ω) (j : ℕ) :
    stepAt X Gn j ω ≤ stepAt X Gn (j + 1) ω :=
  (stepAt_le_exitAt hfin j).trans (exitAt_le_stepAt_succ hfin j)

omit mΩ in
lemma stepAt_mono (hfin : StepTimesFinite X Gn ω) {j k : ℕ} (hjk : j ≤ k) :
    stepAt X Gn j ω ≤ stepAt X Gn k ω := by
  rw [← WithTop.coe_le_coe, coe_stepAt (hfin j), coe_stepAt (hfin k)]
  exact stepTime_mono hjk ω

/-- The holding time `Tⁿ_j` of (3.31) as an element of `[0,∞)`. -/
noncomputable def holdAt (X : ℝ≥0 → Ω → Option V) (Gn : Finset V) (j : ℕ) (ω : Ω) : ℝ≥0 :=
  exitAt X Gn j ω - stepAt X Gn j ω

omit mΩ in
/-- `tⁿ_j + Tⁿ_j = min{t ≥ tⁿ_j : X̃_t ≠ X̃_{tⁿ_j}}`. -/
lemma stepAt_add_holdAt (hfin : StepTimesFinite X Gn ω) (j : ℕ) :
    stepAt X Gn j ω + holdAt X Gn j ω = exitAt X Gn j ω :=
  add_tsub_cancel_of_le (stepAt_le_exitAt hfin j)

omit mΩ in
/-- `Tⁿ_j` in `[0,∞]` is the `ℝ≥0∞`-valued holding time of `UniquenessGeneralSide`. -/
lemma stepHolding_eq_coe (hfin : StepTimesFinite X Gn ω) (j : ℕ) :
    stepHolding X Gn j ω = ((holdAt X Gn j ω : ℝ≥0) : ℝ≥0∞) := by
  have h1 : exitAfter X (stepTime X Gn j) ω = ((exitAt X Gn j ω : ℝ≥0) : ℝ≥0∞) :=
    (coe_exitAt (exitAfter_ne_top hfin j)).symm
  have h2 : stepTime X Gn j ω = ((stepAt X Gn j ω : ℝ≥0) : ℝ≥0∞) := (coe_stepAt (hfin j)).symm
  rw [stepHolding, h1, h2, holdAt, ENNReal.coe_sub]
  rfl

/-- The compressed clock `Sⁿ_k := ∑_{j<k} Tⁿ_j` of (3.32). -/
noncomputable def stepSum (X : ℝ≥0 → Ω → Option V) (Gn : Finset V) (k : ℕ) (ω : Ω) : ℝ≥0 :=
  ∑ j ∈ Finset.range k, holdAt X Gn j ω

omit mΩ in
@[simp] lemma stepSum_zero : stepSum X Gn 0 ω = 0 := by simp [stepSum]

omit mΩ in
lemma stepSum_succ (k : ℕ) :
    stepSum X Gn (k + 1) ω = stepSum X Gn k ω + holdAt X Gn k ω := Finset.sum_range_succ _ _

omit mΩ in
lemma stepSum_mono {k k' : ℕ} (hkk' : k ≤ k') : stepSum X Gn k ω ≤ stepSum X Gn k' ω := by
  refine Finset.sum_le_sum_of_subset ?_
  intro i hi
  simp only [Finset.mem_range] at hi ⊢
  omega

omit mΩ in
/-- **The compressed clock runs behind the real clock**, `Sⁿ_k ≤ tⁿ_k`, because
`Tⁿ_j ≤ tⁿ_{j+1} − tⁿ_j`.  This is the inequality that settles the orientation of (3.33). -/
lemma stepSum_le_stepAt (hfin : StepTimesFinite X Gn ω) (k : ℕ) :
    stepSum X Gn k ω ≤ stepAt X Gn k ω := by
  induction k with
  | zero => simp [stepAt_zero]
  | succ k ih =>
    rw [stepSum_succ]
    calc stepSum X Gn k ω + holdAt X Gn k ω
        ≤ stepAt X Gn k ω + holdAt X Gn k ω := add_le_add ih le_rfl
      _ = exitAt X Gn k ω := stepAt_add_holdAt hfin k
      _ ≤ stepAt X Gn (k + 1) ω := exitAt_le_stepAt_succ hfin k

/-! ### The covering lemma -/

omit mΩ in
/-- **The real clock is unbounded** once the holding times diverge — the paper's "a.s.
`lim_k ∑_{j≤k} Tⁿ_j = ∞`" transported to the times `tⁿ_k` through `stepSum_le_stepAt`. -/
lemma exists_lt_stepAt (hfin : StepTimesFinite X Gn ω)
    (hdiv : ∑' j, stepHolding X Gn j ω = ⊤) (t : ℝ≥0) : ∃ k, t < stepAt X Gn k ω := by
  have hcoe : ∀ k, ∑ j ∈ Finset.range k, stepHolding X Gn j ω
      = ((stepSum X Gn k ω : ℝ≥0) : ℝ≥0∞) := by
    intro k
    rw [stepSum, ENNReal.ofNNReal_finsetSum]
    exact Finset.sum_congr rfl fun j _ => stepHolding_eq_coe hfin j
  have hsup : (⨆ k, ((stepSum X Gn k ω : ℝ≥0) : ℝ≥0∞)) = ⊤ := by
    rw [← hdiv, ENNReal.tsum_eq_iSup_nat]
    exact (iSup_congr hcoe).symm
  have hex : ∃ k, (t : ℝ≥0∞) < ((stepSum X Gn k ω : ℝ≥0) : ℝ≥0∞) := by
    refine lt_iSup_iff.mp ?_
    rw [hsup]
    exact ENNReal.coe_lt_top
  obtain ⟨k, hk⟩ := hex
  exact ⟨k, lt_of_lt_of_le (ENNReal.coe_lt_coe.1 hk) (stepSum_le_stepAt hfin k)⟩

omit mΩ in
/-- **The covering lemma** (Gwynne–Sung, p. 26, first sentence of Step 2).  Every time `t ≥ 0`
lies in `[tⁿ_j, tⁿ_{j+1})` for some `j ≥ 0`: the intervals of (3.31) tile `[0, sup_j tⁿ_j)`, and
the holding times diverge, so the supremum is `∞`.  (The paper states it only for the times with
`X̃_t ∈ VG_n`, which is where it is used; the restriction is not needed.) -/
theorem exists_mem_Ico (hfin : StepTimesFinite X Gn ω)
    (hdiv : ∑' j, stepHolding X Gn j ω = ⊤) (t : ℝ≥0) :
    ∃ j, stepAt X Gn j ω ≤ t ∧ t < stepAt X Gn (j + 1) ω := by
  classical
  have hex : ∃ k, t < stepAt X Gn k ω := exists_lt_stepAt hfin hdiv t
  have hspec : t < stepAt X Gn (Nat.find hex) ω := Nat.find_spec hex
  have hpos : 0 < Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0, stepAt_zero] at hspec
      exact absurd hspec (not_lt.2 zero_le)
    · exact hpos
  refine ⟨Nat.find hex - 1, not_lt.1 (Nat.find_min hex (by omega)), ?_⟩
  rw [show Nat.find hex - 1 + 1 = Nat.find hex by omega]
  exact hspec

omit mΩ in
/-- **The `j` of the covering lemma is unique**: the intervals `[tⁿ_j, tⁿ_{j+1})` are disjoint. -/
theorem mem_Ico_unique (hfin : StepTimesFinite X Gn ω) {j k : ℕ} {t : ℝ≥0}
    (hj : stepAt X Gn j ω ≤ t ∧ t < stepAt X Gn (j + 1) ω)
    (hk : stepAt X Gn k ω ≤ t ∧ t < stepAt X Gn (k + 1) ω) : j = k := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact absurd (lt_of_lt_of_le hj.2 (le_trans (stepAt_mono hfin h) hk.1)) (lt_irrefl _)
  · exact absurd (lt_of_lt_of_le hk.2 (le_trans (stepAt_mono hfin h) hj.1)) (lt_irrefl _)

/-! ### The time change (3.32)

`X̃ⁿ_t := X̃_{tⁿ_k}` for the unique `k` with `t ∈ [Sⁿ_k, Sⁿ_{k+1})`.  It is written through
`ContinuousTimeChain.jumpPath`, the same fixed measurable functional that reads the constructed
chain `Xⁿ` of (3.15) off its embedded chain and holding times, so that the identity in law of
Step 1 is an identity of pushforwards along one map. -/

/-- The embedded chain `Ỹⁿ_j := X̃_{tⁿ_j}` as a `V`-valued sequence; `z` is the junk value where
the position is `∞` (a null event, by `UniquenessGeneralSide.ae_forall_definedAt`). -/
noncomputable def embeddedSeq (X : ℝ≥0 → Ω → Option V) (Gn : Finset V) (z : V) (ω : Ω) : ℕ → V :=
  fun j => (posAt X Gn j ω).getD z

/-- The holding times `(Tⁿ_j)_{j ≥ 0}` of (3.31) as a real sequence. -/
noncomputable def holdingSeq (X : ℝ≥0 → Ω → Option V) (Gn : Finset V) (ω : Ω) : ℕ → ℝ :=
  fun j => (holdAt X Gn j ω : ℝ)

/-- **(3.32)**: the time change `X̃ⁿ` of an arbitrary process satisfying (i)–(vi), the process on
the compressed clock that holds at `X̃_{tⁿ_k}` for the time `Tⁿ_k`. -/
noncomputable def processN (X : ℝ≥0 → Ω → Option V) (Gn : Finset V) (z : V) (t : ℝ≥0) (ω : Ω) :
    Option V :=
  ContinuousTimeChain.jumpPath (embeddedSeq X Gn z ω, holdingSeq X Gn ω) t

omit mΩ in
/-- (3.32) is the functional `jumpPath` of the embedded chain and the holding times — the form
in which Step 1 identifies its law with that of `Xⁿ` (3.15). -/
lemma processN_eq_jumpPath (X : ℝ≥0 → Ω → Option V) (Gn : Finset V) (z : V) (t : ℝ≥0) (ω : Ω) :
    processN X Gn z t ω =
      ContinuousTimeChain.jumpPath (embeddedSeq X Gn z ω, holdingSeq X Gn ω) t := rfl

omit mΩ in
lemma jumpClock_holdingSeq (k : ℕ) :
    ContinuousTimeChain.jumpClock (holdingSeq X Gn ω) k = ((stepSum X Gn k ω : ℝ≥0) : ℝ≥0∞) := by
  rw [ContinuousTimeChain.jumpClock, stepSum, ENNReal.ofNNReal_finsetSum]
  exact Finset.sum_congr rfl fun j _ => by
    rw [holdingSeq, ENNReal.ofReal_coe_nnreal]

omit mΩ in
/-- **(3.32), read off**: on `[Sⁿ_k, Sⁿ_{k+1})` the time change is at `X̃_{tⁿ_k}`. -/
lemma processN_eq_of_mem_Ico {z : V} {k : ℕ} {t : ℝ≥0} (h1 : stepSum X Gn k ω ≤ t)
    (h2 : t < stepSum X Gn (k + 1) ω) :
    processN X Gn z t ω = some (embeddedSeq X Gn z ω k) := by
  refine ContinuousTimeChain.jumpPath_eq_of_inJump (p := (embeddedSeq X Gn z ω, holdingSeq X Gn ω))
    (k := k) ⟨?_, ?_⟩
  · rw [show ((embeddedSeq X Gn z ω, holdingSeq X Gn ω) : (ℕ → V) × (ℕ → ℝ)).2
        = holdingSeq X Gn ω from rfl, jumpClock_holdingSeq]
    exact ENNReal.coe_le_coe.2 h1
  · rw [show ((embeddedSeq X Gn z ω, holdingSeq X Gn ω) : (ℕ → V) × (ℕ → ℝ)).2
        = holdingSeq X Gn ω from rfl, jumpClock_holdingSeq]
    exact ENNReal.coe_lt_coe.2 h2

omit mΩ in
/-- **(3.32) at a vertex**: if `X̃_{tⁿ_k}` is the vertex `y`, then `X̃ⁿ = y` on `[Sⁿ_k, Sⁿ_{k+1})`. -/
lemma processN_eq_posAt {z y : V} {k : ℕ} {t : ℝ≥0} (h1 : stepSum X Gn k ω ≤ t)
    (h2 : t < stepSum X Gn (k + 1) ω) (hy : posAt X Gn k ω = some y) :
    processN X Gn z t ω = posAt X Gn k ω := by
  rw [processN_eq_of_mem_Ico h1 h2, embeddedSeq, hy, Option.getD_some]

/-! ### The exit time is an infimum, and the two branches of (3.31) -/

omit mΩ in
/-- **When the position at `tⁿ_j` lies in `G_n`, `tⁿ_{j+1}` *is* the exit time**, so
`Tⁿ_j = tⁿ_{j+1} − tⁿ_j` (p. 26, first sentence). -/
lemma exitAfter_eq_stepTime_succ (hv : posAt X Gn j ω ∈ some '' (Gn : Set V)) :
    exitAfter X (stepTime X Gn j) ω = stepTime X Gn (j + 1) ω := by
  obtain ⟨x, hx, hxv⟩ := hv
  have h1 : stoppedValue X (stepTime X Gn j) ω = some x := hxv.symm
  rw [show stepTime X Gn (j + 1) = nextStep X Gn (stepTime X Gn j) from rfl,
    nextStep_eq_of_eq (Finset.mem_coe.1 hx) h1, exitAfter, h1]

omit mΩ in
lemma exitAt_eq_stepAt_succ (hv : posAt X Gn j ω ∈ some '' (Gn : Set V)) :
    exitAt X Gn j ω = stepAt X Gn (j + 1) ω :=
  congrArg WithTop.untopA (exitAfter_eq_stepTime_succ hv)

omit mΩ in
/-- **The converse**: the real clock overshoots the compressed clock at step `j` only across an
excursion, i.e. only when `X̃_{tⁿ_j} ∈ B₁G_n \ G_n`. -/
lemma posAt_notMem_of_exitAt_lt (h : exitAt X Gn j ω < stepAt X Gn (j + 1) ω) :
    posAt X Gn j ω ∉ some '' (Gn : Set V) :=
  fun hv => absurd (exitAt_eq_stepAt_succ hv) (ne_of_lt h)

omit mΩ in
/-- **The exit time is an infimum, not a minimum**: arbitrarily soon after it the path differs
from `X̃_{tⁿ_j}`.  (The infimum need not be attained, so this — not `X̃_{exit} ≠ X̃_{tⁿ_j}` — is
what the definition gives.) -/
lemma exists_ne_posAt_lt (hfin : StepTimesFinite X Gn ω) {j : ℕ} {u : ℝ≥0}
    (hu : exitAt X Gn j ω < u) :
    ∃ s : ℝ≥0, exitAt X Gn j ω ≤ s ∧ s < u ∧ X s ω ≠ posAt X Gn j ω := by
  classical
  set S : Set (Option V) := {o : Option V | o ≠ posAt X Gn j ω} with hS
  set A : Set ℝ≥0 := {i : ℝ≥0 | stepAt X Gn j ω ≤ i ∧ X i ω ∈ S} with hA
  have he : exitAfter X (stepTime X Gn j) ω = hittingAfter X S (stepAt X Gn j ω) ω :=
    hitAfter_coe (coe_stepAt (hfin j)).symm
  have hne : hittingAfter X S (stepAt X Gn j ω) ω ≠ ⊤ := by
    rw [← he]; exact exitAfter_ne_top hfin j
  have hAne : A.Nonempty := by
    rw [ne_eq, hittingAfter_eq_top_iff] at hne
    simp only [not_forall, not_not] at hne
    obtain ⟨i, hi1, hi2⟩ := hne
    exact ⟨i, hi1, hi2⟩
  have hAb : BddBelow A := ⟨stepAt X Gn j ω, fun i hi => hi.1⟩
  have hex : ∃ i : ℝ≥0, stepAt X Gn j ω ≤ i ∧ X i ω ∈ S := hAne
  have hinf : exitAt X Gn j ω = sInf A := by
    rw [exitAt, he]
    simp only [hittingAfter]
    rw [ite_eq_left hex]
    rfl
  rw [hinf] at hu ⊢
  obtain ⟨s, hsA, hsu⟩ := exists_lt_of_csInf_lt hAne hu
  exact ⟨s, csInf_le hAb hsA, hsu, hsA.2⟩

/-! ### The lag between the two clocks, and the bound (3.34) -/

/-- The lag `Rⁿ := tⁿ_j − Sⁿ_j` of (3.33): how far the real clock has run ahead of the
compressed clock by the `j`-th step of (3.31). -/
noncomputable def lag (X : ℝ≥0 → Ω → Option V) (Gn : Finset V) (j : ℕ) (ω : Ω) : ℝ≥0 :=
  stepAt X Gn j ω - stepSum X Gn j ω

omit mΩ in
@[simp] lemma lag_zero : lag X Gn 0 ω = 0 := by simp [lag, stepAt_zero]

omit mΩ in
lemma lag_le_stepAt (j : ℕ) : lag X Gn j ω ≤ stepAt X Gn j ω := tsub_le_self

omit mΩ in
lemma stepSum_add_lag (hfin : StepTimesFinite X Gn ω) (j : ℕ) :
    stepSum X Gn j ω + lag X Gn j ω = stepAt X Gn j ω :=
  add_tsub_cancel_of_le (stepSum_le_stepAt hfin j)

omit mΩ in
lemma stepSum_succ_add_lag (hfin : StepTimesFinite X Gn ω) (j : ℕ) :
    stepSum X Gn (j + 1) ω + lag X Gn j ω = exitAt X Gn j ω := by
  rw [stepSum_succ, add_right_comm, stepSum_add_lag hfin j, stepAt_add_holdAt hfin j]

omit mΩ in
/-- **The lag grows only by the excursion overshoot** `tⁿ_{j+1} − (tⁿ_j + Tⁿ_j)`. -/
lemma lag_succ (hfin : StepTimesFinite X Gn ω) (j : ℕ) :
    lag X Gn (j + 1) ω = lag X Gn j ω + (stepAt X Gn (j + 1) ω - exitAt X Gn j ω) := by
  have hab : stepSum X Gn j ω ≤ stepAt X Gn j ω := stepSum_le_stepAt hfin j
  have hbc : stepAt X Gn j ω ≤ exitAt X Gn j ω := stepAt_le_exitAt hfin j
  have hcd : exitAt X Gn j ω ≤ stepAt X Gn (j + 1) ω := exitAt_le_stepAt_succ hfin j
  have hs1 : stepSum X Gn (j + 1) ω
      = stepSum X Gn j ω + (exitAt X Gn j ω - stepAt X Gn j ω) := by
    rw [stepSum_succ, holdAt]
  have hs2 : stepSum X Gn j ω + (exitAt X Gn j ω - stepAt X Gn j ω)
      ≤ stepAt X Gn (j + 1) ω :=
    le_trans (le_trans (add_le_add hab le_rfl) (le_of_eq (add_tsub_cancel_of_le hbc))) hcd
  rw [lag, lag, hs1, ← NNReal.coe_inj]
  simp only [NNReal.coe_add, NNReal.coe_sub hs2, NNReal.coe_sub hab, NNReal.coe_sub hbc,
    NNReal.coe_sub hcd]
  ring

/-- The times in `[0, u)` at which the process is outside `A` — the integrand of (3.34), cut off
at `u`. -/
def outsideBelow (X : ℝ≥0 → Ω → Option V) (A : Set V) (u : ℝ≥0) (ω : Ω) : Set ℝ :=
  {s : ℝ | s ∈ Set.Ico (0 : ℝ) (u : ℝ) ∧ X (Real.toNNReal s) ω ∉ some '' A}

omit mΩ in
lemma outsideBelow_mono {A : Set V} {u u' : ℝ≥0} (h : u ≤ u') (ω : Ω) :
    outsideBelow X A u ω ⊆ outsideBelow X A u' ω := fun _ hs =>
  ⟨⟨hs.1.1, lt_of_lt_of_le hs.1.2 (NNReal.coe_le_coe.2 h)⟩, hs.2⟩

omit mΩ in
/-- The sojourn of (3.34) dominates the time spent outside `G_n` before any `u ≤ t`. -/
lemma volume_outsideBelow_le_sojourn {Gs : ℕ → Set V} {n : ℕ} {u t : ℝ≥0}
    (hGn : Gs n = (Gn : Set V)) (hu : u ≤ t) :
    volume (outsideBelow X (Gn : Set V) u ω) ≤ sojourn Gs X n t ω := by
  rw [sojourn]
  refine measure_mono fun _ hs => ⟨⟨hs.1.1, ?_⟩, ?_⟩
  · exact le_of_lt (lt_of_lt_of_le hs.1.2 (NNReal.coe_le_coe.2 hu))
  · rw [hGn]; exact hs.2

/-- **Carathéodory splitting off an interval.**  No measurability of `A` or `B` is needed: only
the interval has to be measurable.  This is what lets the lag bound (3.34) be proved for a
process with no joint measurability. -/
lemma add_volume_Ico_le {A B : Set ℝ} {a b : ℝ} (hIA : Set.Ico a b ⊆ A)
    (hB : B ⊆ A \ Set.Ico a b) : volume B + volume (Set.Ico a b) ≤ volume A := by
  have h := measure_inter_add_sdiff (μ := volume) A
    (measurableSet_Ico : MeasurableSet (Set.Ico a b))
  rw [Set.inter_eq_right.2 hIA] at h
  calc volume B + volume (Set.Ico a b)
      ≤ volume (A \ Set.Ico a b) + volume (Set.Ico a b) := add_le_add (measure_mono hB) le_rfl
    _ = volume (Set.Ico a b) + volume (A \ Set.Ico a b) := add_comm _ _
    _ = volume A := h

omit mΩ in
/-- **(3.34)**: the lag accumulated by the `j`-th step of (3.31) is at most the time spent
outside `G_n` before `tⁿ_j`.

The lag grows only across excursions (`lag_succ` together with `posAt_notMem_of_exitAt_lt`), and
on an excursion the path stays outside `G_n` (`notMem_of_lt_stepTime_succ`); the overshoot
intervals `[min{t ≥ tⁿ_j : X̃_t ≠ X̃_{tⁿ_j}}, tⁿ_{j+1})` are disjoint, and they are added up by
the Carathéodory identity, which needs no measurability of the path. -/
theorem coe_lag_le_volume_outsideBelow (hfin : StepTimesFinite X Gn ω) (j : ℕ) :
    ((lag X Gn j ω : ℝ≥0) : ℝ≥0∞)
      ≤ volume (outsideBelow X (Gn : Set V) (stepAt X Gn j ω) ω) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hbc : stepAt X Gn j ω ≤ exitAt X Gn j ω := stepAt_le_exitAt hfin j
    have hcd : exitAt X Gn j ω ≤ stepAt X Gn (j + 1) ω := exitAt_le_stepAt_succ hfin j
    have hIA : Set.Ico ((exitAt X Gn j ω : ℝ≥0) : ℝ) ((stepAt X Gn (j + 1) ω : ℝ≥0) : ℝ)
        ⊆ outsideBelow X (Gn : Set V) (stepAt X Gn (j + 1) ω) ω := by
      intro s hs
      have hs0 : (0 : ℝ) ≤ s := le_trans (exitAt X Gn j ω).coe_nonneg hs.1
      have hlt : exitAt X Gn j ω < stepAt X Gn (j + 1) ω :=
        NNReal.coe_lt_coe.1 (lt_of_le_of_lt hs.1 hs.2)
      refine ⟨⟨hs0, hs.2⟩, ?_⟩
      refine notMem_of_lt_stepTime_succ (hfin j) (posAt_notMem_of_exitAt_lt hlt) ?_ ?_
      · rw [← NNReal.coe_le_coe, Real.coe_toNNReal s hs0]
        exact le_trans (NNReal.coe_le_coe.2 hbc) hs.1
      · rw [← coe_stepAt (hfin (j + 1))]
        refine WithTop.coe_lt_coe.2 ?_
        rw [← NNReal.coe_lt_coe, Real.coe_toNNReal s hs0]
        exact hs.2
    have hprev : outsideBelow X (Gn : Set V) (stepAt X Gn j ω) ω
        ⊆ outsideBelow X (Gn : Set V) (stepAt X Gn (j + 1) ω) ω
            \ Set.Ico ((exitAt X Gn j ω : ℝ≥0) : ℝ) ((stepAt X Gn (j + 1) ω : ℝ≥0) : ℝ) := by
      intro s hs
      refine ⟨outsideBelow_mono (stepAt_le_succ hfin j) ω hs, ?_⟩
      intro hmem
      exact absurd (lt_of_lt_of_le hs.1.2 (NNReal.coe_le_coe.2 hbc)) (not_lt.2 hmem.1)
    have hvol : volume (Set.Ico ((exitAt X Gn j ω : ℝ≥0) : ℝ)
        ((stepAt X Gn (j + 1) ω : ℝ≥0) : ℝ))
        = ((stepAt X Gn (j + 1) ω - exitAt X Gn j ω : ℝ≥0) : ℝ≥0∞) := by
      rw [Real.volume_Ico, ← NNReal.coe_sub hcd, ENNReal.ofReal_coe_nnreal]
    calc ((lag X Gn (j + 1) ω : ℝ≥0) : ℝ≥0∞)
        = ((lag X Gn j ω : ℝ≥0) : ℝ≥0∞)
            + ((stepAt X Gn (j + 1) ω - exitAt X Gn j ω : ℝ≥0) : ℝ≥0∞) := by
          rw [lag_succ hfin j, ENNReal.coe_add]
      _ ≤ volume (outsideBelow X (Gn : Set V) (stepAt X Gn j ω) ω)
            + volume (Set.Ico ((exitAt X Gn j ω : ℝ≥0) : ℝ)
              ((stepAt X Gn (j + 1) ω : ℝ≥0) : ℝ)) := by
          rw [hvol]; exact add_le_add ih le_rfl
      _ ≤ volume (outsideBelow X (Gn : Set V) (stepAt X Gn (j + 1) ω) ω) :=
          add_volume_Ico_le hIA hprev

omit mΩ in
/-- **(3.34)**: `0 ≤ Rⁿ ≤ ∫₀ᵗ 1(X̃_s ∉ G_n) ds` for the lag `Rⁿ` at any step `tⁿ_j ≤ t`. -/
theorem lag_le_sojourn (hfin : StepTimesFinite X Gn ω) {Gs : ℕ → Set V} {n : ℕ}
    (hGn : Gs n = (Gn : Set V)) {j : ℕ} {t : ℝ≥0} (ht : stepAt X Gn j ω ≤ t) :
    ((lag X Gn j ω : ℝ≥0) : ℝ≥0∞) ≤ sojourn Gs X n t ω :=
  (coe_lag_le_volume_outsideBelow hfin j).trans (volume_outsideBelow_le_sojourn hGn ht)

/-! ### (3.33): the rewind -/

omit mΩ in
/-- **The sharpened covering lemma.**  At a time `t` where the process sits at a vertex of `G_n`,
the `j` of the covering lemma is an `X̃_{tⁿ_j} ∈ G_n` step and not an excursion, so
`X̃_{tⁿ_j} = X̃_t` and `Tⁿ_j = tⁿ_{j+1} − tⁿ_j`.  This is where the paper's restriction to "each
time `t` for which `X̃_t ∈ VG_n`" is used, and all it is used for. -/
theorem posAt_eq_of_mem_Ico (hfin : StepTimesFinite X Gn ω) {j : ℕ} {t : ℝ≥0} {y : V}
    (h1 : stepAt X Gn j ω ≤ t) (h2 : t < stepAt X Gn (j + 1) ω)
    (hy : X t ω = some y) (hyG : y ∈ Gn) :
    posAt X Gn j ω = X t ω ∧ exitAt X Gn j ω = stepAt X Gn (j + 1) ω := by
  have hlt : (t : WithTop ℝ≥0) < stepTime X Gn (j + 1) ω := by
    rw [← coe_stepAt (hfin (j + 1))]; exact WithTop.coe_lt_coe.2 h2
  have hv : posAt X Gn j ω ∈ some '' (Gn : Set V) := by
    by_contra hv
    have hns := notMem_of_lt_stepTime_succ (hfin j) hv h1 hlt
    rw [hy] at hns
    exact hns ⟨y, Finset.mem_coe.2 hyG, rfl⟩
  have hex : exitAt X Gn j ω = stepAt X Gn (j + 1) ω := exitAt_eq_stepAt_succ hv
  refine ⟨(eq_posAt_of_lt_exitAfter (hfin j) h1 ?_).symm, hex⟩
  rw [exitAfter_eq_stepTime_succ hv]
  exact hlt

omit mΩ in
/-- **(3.33)**, in the orientation in which it holds (see the module docstring): at a time `t`
where `X̃_t` is a vertex of `G_n`, the time change (3.32) at the rewound time `t − Rⁿ` is `X̃_t`,
where `Rⁿ = tⁿ_j − Sⁿ_j` is the lag of the `j`-th step of (3.31).  With `lag_le_sojourn` this is
the pair (3.33)–(3.34). -/
theorem processN_sub_lag_eq (hfin : StepTimesFinite X Gn ω) {z y : V} {j : ℕ} {t : ℝ≥0}
    (h1 : stepAt X Gn j ω ≤ t) (h2 : t < stepAt X Gn (j + 1) ω)
    (hy : X t ω = some y) (hyG : y ∈ Gn) :
    processN X Gn z (t - lag X Gn j ω) ω = X t ω := by
  obtain ⟨hpos, hex⟩ := posAt_eq_of_mem_Ico hfin h1 h2 hy hyG
  have hlb : stepSum X Gn j ω ≤ t - lag X Gn j ω := by
    refine le_tsub_of_add_le_right ?_
    rw [stepSum_add_lag hfin j]; exact h1
  have hub : t - lag X Gn j ω < stepSum X Gn (j + 1) ω := by
    rw [tsub_lt_iff_right (le_trans (lag_le_stepAt j) h1), stepSum_succ_add_lag hfin j, hex]
    exact h2
  rw [processN_eq_posAt hlb hub (hpos.trans hy), hpos]

omit mΩ in
/-- **`X̃ⁿ_t = X̃_t` at one outcome and one level**: as soon as the sojourn outside `G_n` up to `t`
is below the constancy radius `ε` of the path at `t` (property (i)), the lag is so small that `t`
itself lies in the compressed interval `[Sⁿ_j, Sⁿ_{j+1})` on which (3.32) holds at
`X̃_{tⁿ_j} = X̃_t`.  This is the step the paper glosses when it passes from (3.33) to
"`X̃ⁿ_t = X̃_t` for each sufficiently large `n`". -/
theorem processN_eq_of_sojourn_lt (hfin : StepTimesFinite X Gn ω)
    (hdiv : ∑' j, stepHolding X Gn j ω = ⊤) {Gs : ℕ → Set V} {n : ℕ}
    (hGn : Gs n = (Gn : Set V)) {z y : V} {t : ℝ≥0} {ε : ℝ} (hε : 0 < ε)
    (hball : ∀ s ∈ Metric.ball t ε, X s ω = X t ω) (hy : X t ω = some y) (hyG : y ∈ Gn)
    (hsoj : sojourn Gs X n t ω < ENNReal.ofReal ε) :
    processN X Gn z t ω = X t ω := by
  obtain ⟨j, h1, h2⟩ := exists_mem_Ico hfin hdiv t
  obtain ⟨hpos, hex⟩ := posAt_eq_of_mem_Ico hfin h1 h2 hy hyG
  -- the lag is smaller than `ε`
  have hlagε : ((lag X Gn j ω : ℝ≥0) : ℝ) < ε := by
    have h := lt_of_le_of_lt (lag_le_sojourn hfin hGn h1) hsoj
    rw [ENNReal.ofReal, ENNReal.coe_lt_coe] at h
    calc ((lag X Gn j ω : ℝ≥0) : ℝ) < ((ε.toNNReal : ℝ≥0) : ℝ) := NNReal.coe_lt_coe.2 h
      _ = ε := Real.coe_toNNReal ε hε.le
  -- the next step time is at least `t + ε`, because the path is constant on `(t − ε, t + ε)`
  have hfar : (t : ℝ) + ε ≤ ((stepAt X Gn (j + 1) ω : ℝ≥0) : ℝ) := by
    by_contra hc
    rw [not_le] at hc
    have hpos' : (0 : ℝ) ≤ (t : ℝ) + ε := add_nonneg t.coe_nonneg hε.le
    have hu : exitAt X Gn j ω < ((t : ℝ) + ε).toNNReal := by
      rw [hex, ← NNReal.coe_lt_coe, Real.coe_toNNReal _ hpos']
      exact hc
    obtain ⟨s, hs1, hs2, hs3⟩ := exists_ne_posAt_lt hfin hu
    have hts : t < s := lt_of_lt_of_le h2 (hex ▸ hs1)
    have hsε : (s : ℝ) < (t : ℝ) + ε := by
      rw [← Real.coe_toNNReal _ hpos']
      exact NNReal.coe_lt_coe.2 hs2
    have hball' : X s ω = X t ω := by
      refine hball s ?_
      rw [Metric.mem_ball, NNReal.dist_eq, abs_of_nonneg (by linarith [NNReal.coe_lt_coe.2 hts])]
      linarith
    exact hs3 (hball'.trans hpos.symm)
  -- so `t` lies in `[Sⁿ_j, Sⁿ_{j+1})`
  have hlb : stepSum X Gn j ω ≤ t := le_trans (stepSum_le_stepAt hfin j) h1
  have hub : t < stepSum X Gn (j + 1) ω := by
    have hlt : t + lag X Gn j ω < stepSum X Gn (j + 1) ω + lag X Gn j ω := by
      rw [stepSum_succ_add_lag hfin j, hex, ← NNReal.coe_lt_coe, NNReal.coe_add]
      linarith
    exact lt_of_add_lt_add_right hlt
  rw [processN_eq_posAt hlb hub (hpos.trans hy), hpos]

/-! ### Step 2 for the time change (3.32) -/

/-- **Step 2** (Gwynne–Sung, p. 26) for the time changes (3.32) of an arbitrary process
satisfying (i)–(vi): for each fixed `t`, almost surely `X̃ⁿ_t = X̃_t` for all sufficiently large
`n`.  This is `ApproximatedAtFixedTimes`, the hypothesis that `UniquenessLimit.ApproximatedBy`
— and hence `uniqueness_half` — consumes.

The two distributional inputs are hypotheses, named after the results on the law side that
discharge them: `h_ae_forall_definedAt` (`UniquenessGeneralSide.ae_forall_definedAt`) and
`h_tsum_holdingTime_eq_top` (the divergence of the level-`n` holding times). -/
theorem approximatedAtFixedTimes_processN [Countable V] [SFinite P] {Gn : ℕ → Finset V} {z : V}
    (hGmono : Monotone fun n => ((Gn n : Finset V) : Set V)) (hcov : ∀ x : V, ∃ n, x ∈ Gn n)
    (hX : ∀ s, Measurable (X s)) (hi : AlmostEverywhereDefined P X) (hii : RightContinuous P X)
    (hR : RightContinuousAtInfty P X)
    (h_ae_forall_definedAt : ∀ n, ∀ᵐ ω ∂P, StepTimesFinite X (Gn n) ω)
    (h_tsum_holdingTime_eq_top : ∀ n, ∀ᵐ ω ∂P, ∑' j, stepHolding X (Gn n) j ω = ⊤) :
    ApproximatedAtFixedTimes P X (fun n => processN X (Gn n) z) := by
  have hcov' : ∀ x : V, ∃ n, x ∈ ((Gn n : Finset V) : Set V) :=
    fun x => (hcov x).imp fun _ h => Finset.mem_coe.2 h
  intro t
  filter_upwards [hi t, ae_tendsto_sojourn hGmono hcov' hX hi hii hR t,
    ae_all_iff.2 h_ae_forall_definedAt, ae_all_iff.2 h_tsum_holdingTime_eq_top]
    with ω h1 h2 h3 h4
  obtain ⟨⟨x, hx⟩, ε, hε, hball⟩ := h1
  obtain ⟨n₀, hn₀⟩ := hcov x
  have hεpos : (0 : ℝ≥0∞) < ENNReal.ofReal ε := ENNReal.ofReal_pos.2 hε
  have hlt : ∀ᶠ n in atTop,
      sojourn (fun n => ((Gn n : Finset V) : Set V)) X n t ω < ENNReal.ofReal ε :=
    h2 (gt_mem_nhds hεpos)
  filter_upwards [hlt, eventually_ge_atTop n₀] with n hn hnn
  exact processN_eq_of_sojourn_lt (h3 n) (h4 n) rfl hε hball hx
    (Finset.mem_coe.1 (hGmono hnn (Finset.mem_coe.2 hn₀))) hn

/-! ### The interface for the law side

The law side of Step 1 identifies the joint law of the embedded chain and the holding times; these
are the two statements that turn that identification into statements about (3.32). -/

/-- The pair `(Ỹⁿ, T̃ⁿ) = ((X̃_{tⁿ_j})_j, (Tⁿ_j)_j)` of (3.31), as one random element of
`(ℕ → V) × (ℕ → ℝ)`.  This is the random variable whose law Step 1 identifies with
`E.chainLaw hG n z ⊗ₘ holdingKernel w` — the same pair as
`ContinuousTimeChain.embeddedPair` for the constructed chain (3.15). -/
noncomputable def embeddedPair (X : ℝ≥0 → Ω → Option V) (Gn : Finset V) (z : V) (ω : Ω) :
    (ℕ → V) × (ℕ → ℝ) :=
  (embeddedSeq X Gn z ω, holdingSeq X Gn ω)

omit mΩ in
/-- (3.32) is `ContinuousTimeChain.jumpPath` of `embeddedPair`.  Since `jumpPath` is a fixed
measurable map (`ContinuousTimeChain.measurable_jumpPath`) and `ContinuousTimeChain.Xn_eq_jumpPath`
says the same for the constructed chain (3.15), the law of the whole path of `X̃ⁿ` is the
pushforward of the law of `embeddedPair` along `jumpPath`: this is the sense in which Step 1
concludes that `X̃ⁿ` has the same law as `Xⁿ`. -/
lemma processN_eq_jumpPath_embeddedPair (X : ℝ≥0 → Ω → Option V) (Gn : Finset V) (z : V)
    (t : ℝ≥0) (ω : Ω) :
    processN X Gn z t ω = ContinuousTimeChain.jumpPath (embeddedPair X Gn z ω) t := rfl

/-- **(3.33)–(3.34) as a hypothesis on a family of time changes**, in the orientation in which
they hold: almost surely, for every `n` at which `X̃_t` is a vertex of `G_n`, there is a rewind
`r ≤ ∫₀ᵗ 1(X̃_s ∉ G_n) ds` with `X̃ⁿ_{t − r} = X̃_t`.

This is `UniquenessLimit.ShiftBound` with the two sides of (3.33) exchanged; see the module
docstring for why that exchange is forced. -/
def RewindBound (Gs : ℕ → Set V) (P : Measure Ω) (X : ℝ≥0 → Ω → Option V)
    (Xn : ℕ → ℝ≥0 → Ω → Option V) (t : ℝ≥0) : Prop :=
  ∀ᵐ ω ∂P, ∀ n : ℕ, (∃ x ∈ Gs n, X t ω = some x) →
    ∃ r : ℝ≥0, (r : ℝ≥0∞) ≤ sojourn Gs X n t ω ∧ Xn n (t - r) ω = X t ω

/-- **(3.33)–(3.34) for the time change (3.32)**: the output of Step 1 that Step 2 consumes.
No regularity of the path is used — only the covering lemma and the lag bound. -/
theorem rewindBound_processN {Gn : ℕ → Finset V} {z : V}
    (h_ae_forall_definedAt : ∀ n, ∀ᵐ ω ∂P, StepTimesFinite X (Gn n) ω)
    (h_tsum_holdingTime_eq_top : ∀ n, ∀ᵐ ω ∂P, ∑' j, stepHolding X (Gn n) j ω = ⊤) (t : ℝ≥0) :
    RewindBound (fun n => ((Gn n : Finset V) : Set V)) P X (fun n => processN X (Gn n) z) t := by
  filter_upwards [ae_all_iff.2 h_ae_forall_definedAt, ae_all_iff.2 h_tsum_holdingTime_eq_top]
    with ω h3 h4
  intro n hn
  obtain ⟨x, hxG, hx⟩ := hn
  obtain ⟨j, h1, h2⟩ := exists_mem_Ico (h3 n) (h4 n) t
  exact ⟨lag X (Gn n) j ω, lag_le_sojourn (h3 n) rfl h1,
    processN_sub_lag_eq (h3 n) h1 h2 hx (Finset.mem_coe.1 hxG)⟩

/-- Step 2 is insensitive to modifying the approximating processes on a null set for each `n`, so
it transfers from (3.32) to any version of it — in particular to the *measurable* version that
`UniquenessLimit.ApproximatedBy` requires (the times `tⁿ_j` of (3.31) are only a.e.-measurable,
by `UniquenessSkeleton.stepTime_isAEStoppingTime_aemeasurable`, so (3.32) itself is only
a.e.-measurable). -/
theorem approximatedAtFixedTimes_congr {Y Xn : ℕ → ℝ≥0 → Ω → Option V}
    (hYX : ∀ n, ∀ᵐ ω ∂P, ∀ t, Y n t ω = Xn n t ω)
    (h : ApproximatedAtFixedTimes P X Xn) : ApproximatedAtFixedTimes P X Y := by
  intro t
  filter_upwards [h t, ae_all_iff.2 hYX] with ω hω hYXω
  filter_upwards [hω] with n hn
  rw [hYXω n t, hn]

end TimeChange
end Theorem16
end ReflectedWalk
