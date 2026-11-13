/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.GMS.WalkStepPath at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.UniquenessGeneralSide
import LatticeProb.Bonanno.ReflectedGMS.Process.SpatialEnds
import Mathlib.Util.AssertNoSorry

/-!
# Step paths and their jump chains (deterministic part of the GMS walk identification)

A path `f : ℝ≥0 → Option V` is a **step path** with jump chain `J` and jump times `s`
(`IsStepPath f J s`) when `s 0 = 0`, `s` is strictly increasing, consecutive states differ, `f`
equals `J k` on `[s k, s (k+1))`, and these intervals cover the whole half-line (no explosion).
This is exactly the shape of GMS's continuous-time simple random walk
(`GMS.CellConfig.walk`).

This file proves, for a fixed outcome and without any probability:

* `exitSeq` — the exit-time recursion `T₀ = 0`, `T_{j+1} = exitAfter T_j` (reusing
  `ReflectedWalk.Theorem16.exitAfter` of the uniqueness skeleton), and `jumpChainOf`, the value of
  the path at these times;
* `exitSeq_of_isStepPath` — on a step path the exit times are the jump times and the values are the
  jump chain;
* `IsStepPath.comp_symm` — a homeomorphic time change of a step path is a step path with the same
  jump chain;
* `stepTime_eq_exitSeq`, `mem_embeddedCyl_iff_exitSeq` — as long as the path stays in a finite set
  `Gn`, the level-`Gn` recursion (3.31) of the uniqueness skeleton (`stepTime`) *is* the exit-time
  recursion; so the cylinder events of the jump chain are the skeleton's `embeddedCyl`;
* `exists_isStepPath_of_holdingIntervals` — a vertex-valued path with complete holding intervals of
  positive lengths `L v`, visiting only finitely many vertices on every bounded time interval, is a
  step path with holding lengths `L`;
* `finite_visited_of_spatialExtension` — that finiteness follows from a locally bounded spatial
  extension through in-cell representatives when the cells are spatially locally finite.
-/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace ReflectedGMS.GMS.WalkStepPath

open ReflectedWalk ReflectedWalk.Theorem16 SpatialEnds

universe u

/-! ## Hitting times of a path that leaves a set exactly at a given time -/

/-- If `u` avoids `S` on `[a, b)` and is in `S` at `b ≥ a`, the hitting time of `S` after `a` is
`b`. -/
theorem hittingAfter_eq_of_forall_notMem {Ω β : Type*} {u : ℝ≥0 → Ω → β} {S : Set β}
    {a b : ℝ≥0} {ω : Ω} (hab : a ≤ b) (hlt : ∀ t, a ≤ t → t < b → u t ω ∉ S)
    (hb : u b ω ∈ S) : hittingAfter u S a ω = (b : WithTop ℝ≥0) := by
  refine le_antisymm (hittingAfter_le_of_mem hab hb) (le_of_not_gt fun h => ?_)
  obtain ⟨j, hj, hjS⟩ := hittingAfter_lt_iff.mp h
  exact hlt j hj.1 hj.2 hjS

/-! ## The exit-time recursion -/

section Exit

variable {V Ω : Type u}

/-- The exit-time recursion: `T₀ = 0` and `T_{j+1}` is the first time `≥ T_j` at which the path
differs from its value at `T_j` (`ReflectedWalk.Theorem16.exitAfter`). -/
noncomputable def exitSeq (X : ℝ≥0 → Ω → Option V) : ℕ → Ω → WithTop ℝ≥0
  | 0 => fun _ => ((0 : ℝ≥0) : WithTop ℝ≥0)
  | j + 1 => exitAfter X (exitSeq X j)

/-- **The jump chain** of a path: its value at the successive exit times (the default `v₀` is used
only if that value is not a vertex, which does not happen on a step path). -/
noncomputable def jumpChainOf (X : ℝ≥0 → Ω → Option V) (v₀ : V) (ω : Ω) (j : ℕ) : V :=
  (stoppedValue X (exitSeq X j) ω).getD v₀

theorem exitSeq_zero (X : ℝ≥0 → Ω → Option V) (ω : Ω) :
    exitSeq X 0 ω = ((0 : ℝ≥0) : WithTop ℝ≥0) := rfl

theorem exitSeq_succ (X : ℝ≥0 → Ω → Option V) (j : ℕ) (ω : Ω) :
    exitSeq X (j + 1) ω = exitAfter X (exitSeq X j) ω := rfl

/-- `stoppedValue` only reads the stopping time at the outcome. -/
theorem stoppedValue_congr {X : ℝ≥0 → Ω → Option V} {τ τ' : Ω → WithTop ℝ≥0} {ω : Ω}
    (h : τ ω = τ' ω) : stoppedValue X τ ω = stoppedValue X τ' ω := by
  simp only [stoppedValue, h]

/-- `hitAfter` only reads the starting time at the outcome. -/
theorem hitAfter_congr {X : ℝ≥0 → Ω → Option V} {S : Set (Option V)} {σ σ' : Ω → WithTop ℝ≥0}
    {ω : Ω} (h : σ ω = σ' ω) : hitAfter X S σ ω = hitAfter X S σ' ω := by
  unfold hitAfter
  rw [h]

theorem mem_stopEvent_congr {X : ℝ≥0 → Ω → Option V} {τ τ' : Ω → WithTop ℝ≥0} {ω : Ω}
    (h : τ ω = τ' ω) (x : V) : ω ∈ stopEvent X τ x ↔ ω ∈ stopEvent X τ' x := by
  show (τ ω ≠ ⊤ ∧ stoppedValue X τ ω = some x) ↔ (τ' ω ≠ ⊤ ∧ stoppedValue X τ' ω = some x)
  rw [h, stoppedValue_congr (X := X) h]

end Exit

/-! ## Step paths -/

section StepPath

variable {V : Type*}

/-- **A step path**: `f` equals `J k` on `[s k, s (k+1))`, with `s 0 = 0`, `s` strictly
increasing, consecutive states distinct, and the intervals covering `[0, ∞)`. -/
structure IsStepPath (f : ℝ≥0 → Option V) (J : ℕ → V) (s : ℕ → ℝ≥0) : Prop where
  zero : s 0 = 0
  strictMono : StrictMono s
  succ_ne : ∀ k, J (k + 1) ≠ J k
  eq_of_mem : ∀ k t, t ∈ Ico (s k) (s (k + 1)) → f t = some (J k)
  exists_mem : ∀ t, ∃ k, t ∈ Ico (s k) (s (k + 1))

namespace IsStepPath

variable {f g : ℝ≥0 → Option V} {J : ℕ → V} {s : ℕ → ℝ≥0}

theorem apply_self (hs : IsStepPath f J s) (k : ℕ) : f (s k) = some (J k) :=
  hs.eq_of_mem k (s k) ⟨le_rfl, hs.strictMono (Nat.lt_succ_self k)⟩

/-- The index of the interval containing a time is unique. -/
theorem index_eq (hs : IsStepPath f J s) {t : ℝ≥0} {k m : ℕ}
    (hk : t ∈ Ico (s k) (s (k + 1))) (hm : t ∈ Ico (s m) (s (m + 1))) : k = m := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have h1 : s (k + 1) ≤ s m := hs.strictMono.monotone h
    exact absurd (lt_of_lt_of_le hk.2 h1) (not_lt.2 hm.1)
  · have h1 : s (m + 1) ≤ s k := hs.strictMono.monotone h
    exact absurd (lt_of_lt_of_le hm.2 h1) (not_lt.2 hk.1)

/-- The jump times are unbounded. -/
theorem exists_lt (hs : IsStepPath f J s) (t : ℝ≥0) : ∃ n, t < s n := by
  obtain ⟨k, hk⟩ := hs.exists_mem t
  exact ⟨k + 1, hk.2⟩

/-- **A homeomorphic time change of a step path is a step path with the same jump chain.**  If
`f t = g (h t)` for an increasing homeomorphism `h` with `h 0 = 0`, then `g` is a step path with
jump times `h ∘ s`. -/
theorem comp_symm (hs : IsStepPath f J s) (h : ℝ≥0 ≃ₜ ℝ≥0) (hmono : StrictMono h)
    (h0 : h 0 = 0) (hfg : ∀ t, f t = g (h t)) : IsStepPath g J (fun k => h (s k)) where
  zero := by simp only [hs.zero, h0]
  strictMono := hmono.comp hs.strictMono
  succ_ne := hs.succ_ne
  eq_of_mem k u hu := by
    have hu' : h.symm u ∈ Ico (s k) (s (k + 1)) := by
      constructor
      · rw [← hmono.le_iff_le, h.apply_symm_apply]
        exact hu.1
      · rw [← hmono.lt_iff_lt, h.apply_symm_apply]
        exact hu.2
    have hg := hfg (h.symm u)
    rw [h.apply_symm_apply] at hg
    rw [← hg]
    exact hs.eq_of_mem k _ hu'
  exists_mem u := by
    obtain ⟨k, hk⟩ := hs.exists_mem (h.symm u)
    refine ⟨k, ?_, ?_⟩
    · have := hmono.monotone hk.1
      rwa [h.apply_symm_apply] at this
    · have := hmono hk.2
      rwa [h.apply_symm_apply] at this

end IsStepPath

end StepPath

/-! ## Exit times of a step path -/

section ExitStep

variable {V Ω : Type u}

/-- **On a step path the exit times are the jump times and the values there are the jump chain.** -/
theorem exitSeq_of_isStepPath {X : ℝ≥0 → Ω → Option V} {ω : Ω} {J : ℕ → V} {s : ℕ → ℝ≥0}
    (hs : IsStepPath (fun t => X t ω) J s) (j : ℕ) :
    exitSeq X j ω = (s j : WithTop ℝ≥0) ∧ stoppedValue X (exitSeq X j) ω = some (J j) := by
  induction j with
  | zero =>
    have h0 : exitSeq X 0 ω = ((s 0 : ℝ≥0) : WithTop ℝ≥0) := by
      rw [exitSeq_zero, hs.zero]
    exact ⟨h0, by rw [stoppedValue_of_eq h0]; exact hs.apply_self 0⟩
  | succ j ih =>
    have hhit : exitSeq X (j + 1) ω = hittingAfter X {x | x ≠ some (J j)} (s j) ω := by
      rw [exitSeq_succ, exitAfter, ih.2, hitAfter_coe ih.1]
    have heq : exitSeq X (j + 1) ω = (s (j + 1) : WithTop ℝ≥0) := by
      rw [hhit]
      refine hittingAfter_eq_of_forall_notMem (hs.strictMono (Nat.lt_succ_self j)).le ?_ ?_
      · intro t ht1 ht2 hmem
        have hval : X t ω = some (J j) := hs.eq_of_mem j t ⟨ht1, ht2⟩
        exact hmem hval
      · show X (s (j + 1)) ω ≠ some (J j)
        rw [show X (s (j + 1)) ω = some (J (j + 1)) from hs.apply_self (j + 1)]
        exact fun hc => hs.succ_ne j (Option.some_injective _ hc)
    exact ⟨heq, by rw [stoppedValue_of_eq heq]; exact hs.apply_self (j + 1)⟩

/-- On a step path the jump chain of `jumpChainOf` is the step path's chain. -/
theorem jumpChainOf_of_isStepPath {X : ℝ≥0 → Ω → Option V} {ω : Ω} {J : ℕ → V} {s : ℕ → ℝ≥0}
    (hs : IsStepPath (fun t => X t ω) J s) (v₀ : V) : jumpChainOf X v₀ ω = J := by
  funext j
  rw [jumpChainOf, (exitSeq_of_isStepPath hs j).2]
  rfl

/-- On a step path, the jump chain equals `g j` exactly when the path is at `g j` at the finite
`j`-th exit time. -/
theorem mem_stopEvent_exitSeq_iff {X : ℝ≥0 → Ω → Option V} {ω : Ω} {J : ℕ → V}
    {s : ℕ → ℝ≥0} (hs : IsStepPath (fun t => X t ω) J s) (j : ℕ) (x : V) :
    ω ∈ stopEvent X (exitSeq X j) x ↔ J j = x := by
  show (exitSeq X j ω ≠ ⊤ ∧ stoppedValue X (exitSeq X j) ω = some x) ↔ J j = x
  rw [(exitSeq_of_isStepPath hs j).1, (exitSeq_of_isStepPath hs j).2]
  exact ⟨fun h => Option.some_injective _ h.2, fun h => ⟨WithTop.coe_ne_top, by rw [h]⟩⟩

/-! ## The skeleton recursion (3.31) inside a finite set is the exit recursion -/

/-- **As long as the path stays in `Gn`, the level-`Gn` recursion is the exit recursion.** -/
theorem stepTime_eq_exitSeq {X : ℝ≥0 → Ω → Option V} {Gn : Finset V} {ω : Ω} {n : ℕ}
    (h : ∀ i < n, stepTime X Gn i ω = exitSeq X i ω →
      stoppedValue X (exitSeq X i) ω ∈ some '' (Gn : Set V)) :
    ∀ i ≤ n, stepTime X Gn i ω = exitSeq X i ω := by
  intro i hi
  induction i with
  | zero => rfl
  | succ i ih =>
    have ih' : stepTime X Gn i ω = exitSeq X i ω := ih (Nat.le_of_succ_le hi)
    have hmem := h i (Nat.lt_of_succ_le hi) ih'
    have hsv : stoppedValue X (stepTime X Gn i) ω = stoppedValue X (exitSeq X i) ω :=
      stoppedValue_congr ih'
    show nextStep X Gn (stepTime X Gn i) ω = exitAfter X (exitSeq X i) ω
    unfold nextStep exitAfter
    rw [if_pos (by rw [hsv]; exact hmem), hsv]
    exact hitAfter_congr ih'

/-- **The cylinder events of the jump chain are the skeleton's cylinder events** when the finite set
`Gn` contains the first `n` prescribed states. -/
theorem mem_embeddedCyl_iff_exitSeq {X : ℝ≥0 → Ω → Option V} {Gn : Finset V} {g : ℕ → V}
    {n : ℕ} (hg : ∀ i < n, g i ∈ Gn) (ω : Ω) :
    ω ∈ embeddedCyl X Gn g n ↔ ∀ j ≤ n, ω ∈ stopEvent X (exitSeq X j) (g j) := by
  rw [mem_embeddedCyl_iff]
  constructor
  · intro hω
    have heq : ∀ i ≤ n, stepTime X Gn i ω = exitSeq X i ω := by
      refine stepTime_eq_exitSeq fun i hi hi' => ?_
      have hv : stoppedValue X (stepTime X Gn i) ω = some (g i) := (hω i hi.le).2
      rw [← stoppedValue_congr hi', hv]
      exact ⟨g i, hg i hi, rfl⟩
    intro j hj
    exact (mem_stopEvent_congr (heq j hj) (g j)).1 (hω j hj)
  · intro hω
    have heq : ∀ i ≤ n, stepTime X Gn i ω = exitSeq X i ω := by
      refine stepTime_eq_exitSeq fun i hi _ => ?_
      rw [(hω i hi.le).2]
      exact ⟨g i, hg i hi, rfl⟩
    intro j hj
    exact (mem_stopEvent_congr (heq j hj) (g j)).2 (hω j hj)

end ExitStep

/-! ## Step paths from complete holding intervals -/

section Holding

variable {V : Type*} {F : IndexedCells V}

/-- **A vertex-valued path with complete holding intervals of positive lengths, visiting finitely
many vertices on every bounded time interval, is a step path.**  Its jump chain moves along
edges, and the holding time at `J k` is `L (J k)`. -/
theorem exists_isStepPath_of_holdingIntervals {g : ℝ≥0 → State F} {L : V → ℝ}
    (hvert : ∀ t, ∃ v, g t = Sum.inl v)
    (hcomp : HasCompleteHoldingIntervals F g)
    (hlen : ∀ v w a b, IsHoldingInterval F g v w a b → (b : ℝ) - a = L v)
    (hL : ∀ v, 0 < L v)
    (hfin : ∀ T : ℝ≥0, {v | ∃ t ≤ T, g t = Sum.inl v}.Finite) :
    ∃ (J : ℕ → V) (s : ℕ → ℝ≥0), IsStepPath (fun t => collapse (g t)) J s ∧
      (∀ k, (s (k + 1) : ℝ) - s k = L (J k)) ∧
      ∀ k, F.graph.toSimpleGraph.Adj (J k) (J (k + 1)) := by
  classical
  choose vtx hvtx using hvert
  choose a b wn hab using fun r => hcomp r (vtx r) (hvtx r)
  obtain ⟨s, hs0, hsucc⟩ : ∃ s : ℕ → ℝ≥0, s 0 = 0 ∧ ∀ k, s (k + 1) = b (s k) :=
    ⟨fun k => b^[k] 0, rfl, fun k => Function.iterate_succ_apply' b k 0⟩
  -- the value at the end of the interval chosen at `r` is the next vertex
  have hnext : ∀ r, vtx (b r) = wn r := by
    intro r
    have h1 : g (b r) = Sum.inl (wn r) := (hab r).1.2.2.1
    have h2 := hvtx (b r)
    rw [h1] at h2
    exact (Sum.inl_injective h2).symm
  -- the interval chosen at `s k` starts at `s k`
  have hstart : ∀ k, a (s k) = s k := by
    intro k
    induction k with
    | zero =>
      rw [hs0]
      have h1 : a 0 ≤ 0 := by
        have := (hab 0).2.1
        exact this
      exact le_antisymm h1 zero_le
    | succ k ih =>
      have hr : s k < s (k + 1) := by
        rw [hsucc k]
        have := (hab (s k)).1.1
        rwa [ih] at this
      by_contra hne
      have hlt : a (s (k + 1)) < s (k + 1) := lt_of_le_of_ne (hab (s (k + 1))).2.1 hne
      have hqlt : max (a (s (k + 1))) (s k) < s (k + 1) := max_lt hlt hr
      have hq1 : max (a (s (k + 1))) (s k) ∈ Ico (a (s (k + 1))) (b (s (k + 1))) :=
        ⟨le_max_left _ _, lt_trans hqlt (hab (s (k + 1))).2.2⟩
      have hq2 : max (a (s (k + 1))) (s k) ∈ Ico (a (s k)) (b (s k)) := by
        refine ⟨?_, ?_⟩
        · rw [ih]
          exact le_max_right _ _
        · rw [← hsucc k]
          exact hqlt
      have e1 := (hab (s (k + 1))).1.2.1 _ hq1
      have e2 := (hab (s k)).1.2.1 _ hq2
      rw [e1] at e2
      have hveq : vtx (s (k + 1)) = vtx (s k) := Sum.inl_injective e2
      have hadj := (hab (s k)).1.2.2.2.1
      rw [← hnext (s k), ← hsucc k, hveq] at hadj
      exact SimpleGraph.irrefl _ hadj
  have hJsucc : ∀ k, vtx (s (k + 1)) = wn (s k) := fun k => by rw [hsucc k, hnext]
  have hsmono : ∀ k, s k < s (k + 1) := fun k => by
    rw [hsucc k]
    have := (hab (s k)).1.1
    rwa [hstart k] at this
  have hIco : ∀ k, Ico (s k) (s (k + 1)) = Ico (a (s k)) (b (s k)) := fun k => by
    rw [hstart k, hsucc k]
  have hhold : ∀ k, (s (k + 1) : ℝ) - s k = L (vtx (s k)) := fun k => by
    have := hlen _ _ _ _ (hab (s k)).1
    rwa [hstart k, ← hsucc k] at this
  -- the jump times are unbounded
  have hunb : ∀ t : ℝ≥0, ∃ n, t < s n := by
    intro t
    by_contra hcon
    push Not at hcon
    have hmemS : ∀ k, vtx (s k) ∈ {v | ∃ t' ≤ t, g t' = Sum.inl v} :=
      fun k => ⟨s k, hcon k, hvtx (s k)⟩
    obtain ⟨v₀, -, hv₀min⟩ := Set.exists_min_image _ L (hfin t) ⟨_, hmemS 0⟩
    have hgrow : ∀ k : ℕ, (k : ℝ) * L v₀ ≤ s k := by
      intro k
      induction k with
      | zero => simp [hs0]
      | succ k ih =>
        have h1 := hhold k
        have h2 := hv₀min _ (hmemS k)
        have h3 : ((k : ℝ) + 1) * L v₀ = k * L v₀ + L v₀ := by ring
        push_cast
        linarith
    obtain ⟨k, hk⟩ := exists_nat_gt ((t : ℝ) / L v₀)
    rw [div_lt_iff₀ (hL v₀)] at hk
    have h4 : (s k : ℝ) ≤ t := NNReal.coe_le_coe.mpr (hcon k)
    linarith [hgrow k]
  refine ⟨fun k => vtx (s k), s, ⟨hs0, strictMono_nat_of_lt_succ hsmono, ?_, ?_, ?_⟩,
    hhold, ?_⟩
  · intro k
    show vtx (s (k + 1)) ≠ vtx (s k)
    rw [hJsucc k]
    exact ((hab (s k)).1.2.2.2.1.ne).symm
  · intro k t ht
    rw [hIco k] at ht
    show collapse (g t) = some (vtx (s k))
    rw [(hab (s k)).1.2.1 t ht]
    rfl
  · intro t
    obtain ⟨n, hn, hmin⟩ : ∃ n, t < s n ∧ ∀ m < n, ¬ t < s m :=
      ⟨Nat.find (hunb t), Nat.find_spec (hunb t), fun m hm => Nat.find_min (hunb t) hm⟩
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [hs0] at hn
      exact absurd hn (by simp)
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
    exact ⟨k, not_lt.1 (hmin k (Nat.lt_succ_self k)), hn⟩
  · intro k
    show F.graph.toSimpleGraph.Adj (vtx (s k)) (vtx (s (k + 1)))
    rw [hJsucc k]
    exact (hab (s k)).1.2.2.2.1

/-- **Finitely many vertices on bounded time intervals**, from a locally bounded spatial extension
through in-cell representatives, when the cells are spatially locally finite. -/
theorem finite_visited_of_spatialExtension {z : V → Plane} {g : ℝ≥0 → State F}
    {Z : ℝ≥0 → Plane} (hZ : IsSpatialExtension F z g Z) (hbdd : LocallySpatiallyBounded Z)
    (hz : ∀ v, z v ∈ (F.cell v : Set Plane))
    (hlf : LocallyFinite (fun v => (F.cell v : Set Plane))) (T : ℝ≥0) :
    {v | ∃ t ≤ T, g t = Sum.inl v}.Finite := by
  obtain ⟨R, hR⟩ := (hbdd T).subset_closedBall (0 : Plane)
  refine (hlf.finite_nonempty_inter_compact (isCompact_closedBall (0 : Plane) R)).subset ?_
  rintro v ⟨t, htT, hgt⟩
  refine ⟨z v, hz v, ?_⟩
  have hZt : Z t = z v := hZ.2.1 t v hgt
  rw [← hZt]
  exact hR ⟨t, ⟨zero_le, htT⟩, rfl⟩

end Holding

end ReflectedGMS.GMS.WalkStepPath

open ReflectedGMS.GMS.WalkStepPath in
assert_no_sorry exitSeq_of_isStepPath
open ReflectedGMS.GMS.WalkStepPath in
assert_no_sorry IsStepPath.comp_symm
open ReflectedGMS.GMS.WalkStepPath in
assert_no_sorry mem_embeddedCyl_iff_exitSeq
open ReflectedGMS.GMS.WalkStepPath in
assert_no_sorry exists_isStepPath_of_holdingIntervals
open ReflectedGMS.GMS.WalkStepPath in
assert_no_sorry finite_visited_of_spatialExtension

#print axioms ReflectedGMS.GMS.WalkStepPath.exitSeq_of_isStepPath
#print axioms ReflectedGMS.GMS.WalkStepPath.jumpChainOf_of_isStepPath
#print axioms ReflectedGMS.GMS.WalkStepPath.IsStepPath.comp_symm
#print axioms ReflectedGMS.GMS.WalkStepPath.mem_embeddedCyl_iff_exitSeq
#print axioms ReflectedGMS.GMS.WalkStepPath.exists_isStepPath_of_holdingIntervals
#print axioms ReflectedGMS.GMS.WalkStepPath.finite_visited_of_spatialExtension
