/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.GMS.WalkSRWLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.GMS.Theorem116Statement
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.MeasureTheory.Constructions.Projective
import Mathlib.Topology.Order.LeftRight
import Mathlib.Util.AssertNoSorry

/-!
# GMS's simple random walk: uniqueness of its law, measurability, and the interpolated path

Facts about GMS's own objects (`GMS.CellConfig.IsSRWLaw`, `jumpTime`, `jumpCount`, `walk`,
`interpolatedPath`, `interpolatedWalk`), for a cell configuration with countably many cells.

* `CellConfig.IsSRWLaw.unique` — the finite-dimensional distributions required by `IsSRWLaw`
  determine the law on `ℕ → H.cells`.  The proof reuses mathlib's projective-limit uniqueness
  (`IsProjectiveLimit.unique`): the marginals on `Finset.Iic N` are measures on a countable type,
  determined by their singleton masses, which are exactly the cylinder probabilities.
* `measurable_jumpTime`, `measurable_jumpCount`, `measurable_interpolatedPath` — measurability in
  the jump sequence (the `sSup` convention of `jumpCount` is handled exactly, `nat_sSup_eq_iff`).
* When every holding time is positive and the jump times are unbounded (`JumpTimesUnbounded`):
  `jumpCount_eq_of_mem` / `walk_eq_of_mem` (the walk is `ω n` on `[T_n, T_{n+1})`),
  `interpolatedPath_eq_lineMap` (on `[T_n, T_{n+1}]` the interpolated path is the affine
  interpolation from `p(ω n)` to `p(ω (n+1))`), `continuous_interpolatedPath`, and
  `coe_interpolatedWalk` (the placeholder branch of `interpolatedWalk` is not taken).
* `aemeasurable_interpolatedWalk` — the rescaled interpolated walk is an a.e.-measurable random
  element of `C(ℝ≥0, ℂ)` under any law giving full mass to unbounded jump times.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace ReflectedGMS.GMS

/-! ## `sSup` on `ℕ` -/

/-- The value of `sSup` of a set of naturals, including mathlib's conventions for the empty and
the unbounded set. -/
theorem nat_sSup_eq_iff (S : Set ℕ) (m : ℕ) :
    sSup S = m ↔ (m ∈ S ∧ ∀ n, m < n → n ∉ S) ∨
      (m = 0 ∧ ((∀ N, ∃ n, N < n ∧ n ∈ S) ∨ ∀ n, n ∉ S)) := by
  by_cases hb : BddAbove S
  · rcases S.eq_empty_or_nonempty with rfl | hne
    · have h0 : sSup (∅ : Set ℕ) = 0 := by simp
      rw [h0]
      constructor
      · rintro rfl
        exact Or.inr ⟨rfl, Or.inr fun n => Set.notMem_empty n⟩
      · rintro (⟨hm, -⟩ | ⟨rfl, -⟩)
        · exact absurd hm (Set.notMem_empty m)
        · rfl
    · have hmem := Nat.sSup_mem hne hb
      have hle : ∀ n ∈ S, n ≤ sSup S := fun n hn => le_csSup hb hn
      constructor
      · rintro rfl
        exact Or.inl ⟨hmem, fun n hn hnS => absurd (hle n hnS) (not_le.2 hn)⟩
      · rintro (⟨hm, hmax⟩ | ⟨rfl, hunb | hemp⟩)
        · refine le_antisymm ?_ (hle m hm)
          by_contra hlt
          exact hmax _ (not_le.1 hlt) hmem
        · obtain ⟨B, hB⟩ := hb
          obtain ⟨n, hn, hnS⟩ := hunb B
          exact absurd (hB hnS) (not_le.2 hn)
        · obtain ⟨n, hn⟩ := hne
          exact absurd hn (hemp n)
  · rw [Nat.sSup_of_not_bddAbove hb]
    constructor
    · rintro rfl
      refine Or.inr ⟨rfl, Or.inl fun N => ?_⟩
      rw [not_bddAbove_iff] at hb
      obtain ⟨n, hnS, hn⟩ := hb N
      exact ⟨n, hn, hnS⟩
    · rintro (⟨hm, hmax⟩ | ⟨rfl, -⟩)
      · exfalso
        refine hb ⟨m, fun n hn => ?_⟩
        by_contra hlt
        exact hmax n (not_le.1 hlt) hn
      · rfl

/-- Evaluating a measurable family at a measurable index is measurable. -/
theorem measurable_comp_nat {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β] {N : Ω → ℕ}
    (hN : Measurable N) {F : ℕ → Ω → β} (hF : ∀ m, Measurable (F m)) :
    Measurable fun ω => F (N ω) ω := by
  have h : Measurable fun q : Ω × ℕ => F q.2 q.1 :=
    measurable_from_prod_countable_left fun m => hF m
  exact h.comp (measurable_id.prodMk hN)

namespace CellConfig

variable {H : CellConfig}

/-! ## Uniqueness of the simple-random-walk law -/

section Unique

variable [Countable H.cells]

/-- **The law of GMS's simple random walk is unique**: two laws on `ℕ → H.cells` with the
finite-dimensional distributions of `IsSRWLaw` from the same start coincide. -/
theorem IsSRWLaw.unique {K₀ : H.cells} {Q Q' : Measure (ℕ → H.cells)}
    (hQ : H.IsSRWLaw K₀ Q) (hQ' : H.IsSRWLaw K₀ Q') : Q = Q' := by
  have := hQ.1
  have := hQ'.1
  have hN : ∀ N : ℕ, Q.map (Finset.Iic N).restrict = Q'.map (Finset.Iic N).restrict := by
    intro N
    refine Measure.ext_iff_singleton.2 fun x => ?_
    rw [Measure.map_apply (Finset.measurable_restrict _) (measurableSet_singleton x),
      Measure.map_apply (Finset.measurable_restrict _) (measurableSet_singleton x)]
    have hset : Finset.restrict (π := fun _ : ℕ => H.cells) (Finset.Iic N) ⁻¹' {x} =
        {ω : ℕ → H.cells | ∀ i : Fin (N + 1),
          ω i = x ⟨i, Finset.mem_Iic.2 (Nat.lt_succ_iff.1 i.2)⟩} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
      constructor
      · intro h i
        exact congrFun h ⟨i, Finset.mem_Iic.2 (Nat.lt_succ_iff.1 i.2)⟩
      · intro h
        funext i
        exact h ⟨i, Nat.lt_succ_iff.2 (Finset.mem_Iic.1 i.2)⟩
    rw [hset, hQ.2 N (fun i => x ⟨i, Finset.mem_Iic.2 (Nat.lt_succ_iff.1 i.2)⟩),
      hQ'.2 N (fun i => x ⟨i, Finset.mem_Iic.2 (Nat.lt_succ_iff.1 i.2)⟩)]
  have hproj : ∀ I : Finset ℕ, Q.map I.restrict = Q'.map I.restrict := by
    intro I
    rw [← Finset.restrict₂_comp_restrict I.subset_Iic_sup_id,
      ← Measure.map_map (Finset.measurable_restrict₂ _) (Finset.measurable_restrict _),
      ← Measure.map_map (Finset.measurable_restrict₂ _) (Finset.measurable_restrict _), hN]
  exact IsProjectiveLimit.unique (P := fun I => Q'.map I.restrict) hproj (fun _ => rfl)

end Unique

/-! ## Measurability in the jump sequence -/

section Measurability

variable [Countable H.cells]

theorem measurable_jumpTime (n : ℕ) : Measurable fun ω : ℕ → H.cells => H.jumpTime ω n := by
  unfold jumpTime
  exact Finset.measurable_sum _ fun k _ =>
    (measurable_of_countable H.holding).comp (measurable_pi_apply k)

theorem measurable_jumpCount (t : ℝ) : Measurable fun ω : ℕ → H.cells => H.jumpCount ω t := by
  have hB : ∀ n, Measurable fun ω : ℕ → H.cells => H.jumpTime ω n ≤ t := fun n =>
    measurableSet_setOfPred.1 (measurableSet_le (H.measurable_jumpTime n) measurable_const)
  refine measurable_to_countable' fun m => ?_
  have hset : (fun ω : ℕ → H.cells => H.jumpCount ω t) ⁻¹' {m} =
      {ω | (H.jumpTime ω m ≤ t ∧ ∀ n, m < n → ¬ H.jumpTime ω n ≤ t) ∨
        (m = 0 ∧ ((∀ N, ∃ n, N < n ∧ H.jumpTime ω n ≤ t) ∨ ∀ n, ¬ H.jumpTime ω n ≤ t))} := by
    ext ω
    exact nat_sSup_eq_iff {n | H.jumpTime ω n ≤ t} m
  rw [hset]
  refine measurableSet_setOfPred.2 ?_
  exact ((hB m).and (Measurable.forall fun n => measurable_const.imp (hB n).not)).or
    (measurable_const.and ((Measurable.forall fun N => Measurable.exists fun n =>
      measurable_const.and (hB n)).or (Measurable.forall fun n => (hB n).not)))

theorem measurable_interpolatedPath (p : H.cells → Plane) (s : ℝ) :
    Measurable fun ω : ℕ → H.cells => H.interpolatedPath p ω s := by
  have hp : ∀ m, Measurable fun ω : ℕ → H.cells => p (ω m) := fun m =>
    (measurable_of_countable p).comp (measurable_pi_apply m)
  have hh : ∀ m, Measurable fun ω : ℕ → H.cells => H.holding (ω m) := fun m =>
    (measurable_of_countable H.holding).comp (measurable_pi_apply m)
  exact measurable_comp_nat (H.measurable_jumpCount s)
    (F := fun m ω => p (ω m) + ((s - H.jumpTime ω m) / H.holding (ω m)) •
      (p (ω (m + 1)) - p (ω m)))
    fun m => (hp m).add (((measurable_const.sub (H.measurable_jumpTime m)).div (hh m)).smul
      ((hp (m + 1)).sub (hp m)))

end Measurability

/-! ## The walk and its interpolation between jump times -/

/-- The jump times are unbounded (no explosion). -/
def JumpTimesUnbounded (ω : ℕ → H.cells) : Prop := ∀ N : ℕ, ∃ n, (N : ℝ) < H.jumpTime ω n

theorem measurableSet_jumpTimesUnbounded [Countable H.cells] :
    MeasurableSet {ω : ℕ → H.cells | H.JumpTimesUnbounded ω} :=
  measurableSet_setOfPred.2 (Measurable.forall fun _ => Measurable.exists fun n =>
    measurableSet_setOfPred.1 (measurableSet_lt measurable_const (H.measurable_jumpTime n)))

section Deterministic

variable (p : H.cells → Plane) (ω : ℕ → H.cells)

/-- The affine piece of the interpolation on the `n`-th holding interval. -/
noncomputable def affinePiece (n : ℕ) (s : ℝ) : Plane :=
  p (ω n) + ((s - H.jumpTime ω n) / H.holding (ω n)) • (p (ω (n + 1)) - p (ω n))

theorem interpolatedPath_eq_affinePiece (s : ℝ) :
    H.interpolatedPath p ω s = H.affinePiece p ω (H.jumpCount ω s) s := rfl

theorem continuous_affinePiece (n : ℕ) : Continuous (H.affinePiece p ω n) := by
  unfold affinePiece
  exact continuous_const.add
    (((continuous_id.sub continuous_const).div_const _).smul continuous_const)

theorem jumpTime_zero : H.jumpTime ω 0 = 0 := by simp [jumpTime]

theorem jumpTime_succ (n : ℕ) : H.jumpTime ω (n + 1) = H.jumpTime ω n + H.holding (ω n) := by
  simp [jumpTime, Finset.sum_range_succ]

variable {p ω}

theorem affinePiece_self (n : ℕ) : H.affinePiece p ω n (H.jumpTime ω n) = p (ω n) := by
  simp [affinePiece]

theorem affinePiece_jumpTime_succ (hpos : ∀ K, 0 < H.holding K) (n : ℕ) :
    H.affinePiece p ω n (H.jumpTime ω (n + 1)) = p (ω (n + 1)) := by
  simp [affinePiece, jumpTime_succ, div_self (hpos (ω n)).ne']

theorem jumpTime_strictMono (hpos : ∀ K, 0 < H.holding K) : StrictMono (H.jumpTime ω) :=
  strictMono_nat_of_lt_succ fun n => by
    rw [jumpTime_succ]
    linarith [hpos (ω n)]

theorem jumpTime_nonneg (hpos : ∀ K, 0 < H.holding K) (n : ℕ) : 0 ≤ H.jumpTime ω n := by
  rw [← H.jumpTime_zero ω]
  exact (H.jumpTime_strictMono hpos).monotone (Nat.zero_le n)

theorem jumpCount_eq_of_mem (hpos : ∀ K, 0 < H.holding K) {n : ℕ} {s : ℝ}
    (h1 : H.jumpTime ω n ≤ s) (h2 : s < H.jumpTime ω (n + 1)) : H.jumpCount ω s = n := by
  have hmono := H.jumpTime_strictMono (ω := ω) hpos
  have hset : {m | H.jumpTime ω m ≤ s} = Set.Iic n := by
    ext m
    simp only [Set.mem_ofPred_eq, Set.mem_Iic]
    constructor
    · intro hm
      by_contra hlt
      have := hmono.monotone (Nat.succ_le_of_lt (not_le.1 hlt))
      linarith
    · intro hm
      exact (hmono.monotone hm).trans h1
  unfold jumpCount
  rw [hset, csSup_Iic]

theorem jumpCount_eq_zero_of_lt (hpos : ∀ K, 0 < H.holding K) {s : ℝ}
    (hs : s < H.jumpTime ω 1) : H.jumpCount ω s = 0 := by
  by_cases h0 : 0 ≤ s
  · exact H.jumpCount_eq_of_mem (n := 0) hpos (by rw [jumpTime_zero]; exact h0) hs
  · have hset : {m | H.jumpTime ω m ≤ s} = ∅ := by
      ext m
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      linarith [H.jumpTime_nonneg (ω := ω) hpos m]
    unfold jumpCount
    rw [hset]
    simp

/-- **GMS's walk is `ω n` on `[T_n, T_{n+1})`.** -/
theorem walk_eq_of_mem (hpos : ∀ K, 0 < H.holding K) {n : ℕ} {s : ℝ}
    (h1 : H.jumpTime ω n ≤ s) (h2 : s < H.jumpTime ω (n + 1)) : H.walk ω s = ω n := by
  rw [walk, H.jumpCount_eq_of_mem hpos h1 h2]

theorem interpolatedPath_eq_of_mem (hpos : ∀ K, 0 < H.holding K) {n : ℕ} {s : ℝ}
    (h1 : H.jumpTime ω n ≤ s) (h2 : s < H.jumpTime ω (n + 1)) :
    H.interpolatedPath p ω s = H.affinePiece p ω n s := by
  rw [interpolatedPath_eq_affinePiece, H.jumpCount_eq_of_mem hpos h1 h2]

theorem exists_mem_Ico (hpos : ∀ K, 0 < H.holding K) (hunb : H.JumpTimesUnbounded ω) {s : ℝ}
    (hs : 0 ≤ s) : ∃ n, H.jumpTime ω n ≤ s ∧ s < H.jumpTime ω (n + 1) := by
  classical
  have hex : ∃ n, s < H.jumpTime ω n := by
    obtain ⟨N, hN⟩ := exists_nat_gt s
    obtain ⟨n, hn⟩ := hunb N
    exact ⟨n, hN.trans hn⟩
  obtain ⟨n, hn, hmin⟩ : ∃ n, s < H.jumpTime ω n ∧ ∀ m < n, ¬ s < H.jumpTime ω m :=
    ⟨Nat.find hex, Nat.find_spec hex, fun m hm => Nat.find_min hex hm⟩
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [jumpTime_zero] at hn
    linarith
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
  exact ⟨k, not_lt.1 (hmin k (Nat.lt_succ_self k)), hn⟩

/-- On the closed interval `[T_n, T_{n+1}]` the interpolated path is the affine interpolation from
`p(ω n)` to `p(ω (n+1))`. -/
theorem interpolatedPath_eq_affinePiece_of_mem_Icc (hpos : ∀ K, 0 < H.holding K) {n : ℕ}
    {s : ℝ} (h1 : H.jumpTime ω n ≤ s) (h2 : s ≤ H.jumpTime ω (n + 1)) :
    H.interpolatedPath p ω s = H.affinePiece p ω n s := by
  rcases h2.lt_or_eq with h2 | h2
  · exact H.interpolatedPath_eq_of_mem hpos h1 h2
  · subst h2
    have hmono := H.jumpTime_strictMono (ω := ω) hpos
    rw [H.interpolatedPath_eq_of_mem hpos le_rfl (hmono (Nat.lt_succ_self (n + 1))),
      affinePiece_self, affinePiece_jumpTime_succ hpos]

/-- The interpolated path in `lineMap` form on `[T_n, T_{n+1}]`. -/
theorem interpolatedPath_eq_lineMap (hpos : ∀ K, 0 < H.holding K) {n : ℕ} {s : ℝ}
    (h1 : H.jumpTime ω n ≤ s) (h2 : s ≤ H.jumpTime ω (n + 1)) :
    H.interpolatedPath p ω s = AffineMap.lineMap (p (ω n)) (p (ω (n + 1)))
      ((s - H.jumpTime ω n) / (H.jumpTime ω (n + 1) - H.jumpTime ω n)) := by
  rw [H.interpolatedPath_eq_affinePiece_of_mem_Icc hpos h1 h2, AffineMap.lineMap_apply,
    jumpTime_succ, add_sub_cancel_left, affinePiece]
  simp only [vsub_eq_sub, vadd_eq_add]
  abel

/-- **The interpolated path is continuous** when every holding time is positive and the jump
times are unbounded. -/
theorem continuous_interpolatedPath (hpos : ∀ K, 0 < H.holding K)
    (hunb : H.JumpTimesUnbounded ω) : Continuous (H.interpolatedPath p ω) := by
  have hmono := H.jumpTime_strictMono (ω := ω) hpos
  have hT1 : 0 < H.jumpTime ω 1 := by
    rw [← H.jumpTime_zero ω]
    exact hmono Nat.zero_lt_one
  refine continuous_iff_continuousAt.2 fun s₀ =>
    continuousAt_iff_continuous_left_right.2 ⟨?_, ?_⟩
  · -- from the left
    by_cases hs₀ : s₀ ≤ 0
    · have hev : H.interpolatedPath p ω =ᶠ[𝓝[≤] s₀] H.affinePiece p ω 0 := by
        filter_upwards [self_mem_nhdsWithin] with s hs
        rw [interpolatedPath_eq_affinePiece,
          H.jumpCount_eq_zero_of_lt hpos (lt_of_le_of_lt (le_trans hs hs₀) hT1)]
      exact (H.continuous_affinePiece p ω 0).continuousWithinAt.congr_of_eventuallyEq hev
        (hev.eq_of_nhdsWithin Set.self_mem_Iic)
    · obtain ⟨n, h1, h2⟩ := H.exists_mem_Ico hpos hunb (le_of_lt (not_le.1 hs₀))
      rcases h1.lt_or_eq with hlt | heq
      · have hev : H.interpolatedPath p ω =ᶠ[𝓝[≤] s₀] H.affinePiece p ω n := by
          filter_upwards [Ioc_mem_nhdsLE hlt] with s hs
          exact H.interpolatedPath_eq_of_mem hpos hs.1.le (lt_of_le_of_lt hs.2 h2)
        exact (H.continuous_affinePiece p ω n).continuousWithinAt.congr_of_eventuallyEq hev
          (hev.eq_of_nhdsWithin Set.self_mem_Iic)
      · have hn0 : n ≠ 0 := by
          rintro rfl
          rw [jumpTime_zero] at heq
          exact hs₀ heq.symm.le
        obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
        have hev : H.interpolatedPath p ω =ᶠ[𝓝[≤] s₀] H.affinePiece p ω k := by
          have hk : H.jumpTime ω k < s₀ := by
            rw [← heq]
            exact hmono (Nat.lt_succ_self k)
          filter_upwards [Icc_mem_nhdsLE hk] with s hs
          exact H.interpolatedPath_eq_affinePiece_of_mem_Icc hpos hs.1 (by rw [heq]; exact hs.2)
        exact (H.continuous_affinePiece p ω k).continuousWithinAt.congr_of_eventuallyEq hev
          (hev.eq_of_nhdsWithin Set.self_mem_Iic)
  · -- from the right
    obtain ⟨n, hn2, hn⟩ : ∃ n, s₀ < H.jumpTime ω (n + 1) ∧
        ∀ s, s₀ ≤ s → s < H.jumpTime ω (n + 1) →
          H.interpolatedPath p ω s = H.affinePiece p ω n s := by
      by_cases hs₀ : 0 ≤ s₀
      · obtain ⟨n, h1, h2⟩ := H.exists_mem_Ico hpos hunb hs₀
        exact ⟨n, h2, fun s hs hs' => H.interpolatedPath_eq_of_mem hpos (h1.trans hs) hs'⟩
      · refine ⟨0, lt_trans (not_le.1 hs₀) hT1, fun s _ hs' => ?_⟩
        rw [interpolatedPath_eq_affinePiece, H.jumpCount_eq_zero_of_lt hpos hs']
    have hev : H.interpolatedPath p ω =ᶠ[𝓝[≥] s₀] H.affinePiece p ω n := by
      filter_upwards [Ico_mem_nhdsGE hn2] with s hs
      exact hn s hs.1 hs.2
    exact (H.continuous_affinePiece p ω n).continuousWithinAt.congr_of_eventuallyEq hev
      (hev.eq_of_nhdsWithin Set.self_mem_Ici)

/-- **Without explosion, `interpolatedWalk` is the rescaled interpolated path** (its placeholder
branch is not taken). -/
theorem coe_interpolatedWalk (hpos : ∀ K, 0 < H.holding K) (hunb : H.JumpTimesUnbounded ω)
    (ε : ℝ≥0) :
    (H.interpolatedWalk p ε ω : ℝ≥0 → Plane) =
      fun t : ℝ≥0 => (ε : ℝ) • H.interpolatedPath p ω ((t : ℝ) / (ε : ℝ) ^ 2) := by
  have hc : Continuous
      (fun t : ℝ≥0 => (ε : ℝ) • H.interpolatedPath p ω ((t : ℝ) / (ε : ℝ) ^ 2)) :=
    ((H.continuous_interpolatedPath hpos hunb).comp
      (NNReal.continuous_coe.div_const ((ε : ℝ) ^ 2))).const_smul (ε : ℝ)
  unfold interpolatedWalk
  rw [dif_pos hc]
  rfl

end Deterministic

/-- **The rescaled interpolated walk is an a.e.-measurable random element of `C(ℝ≥0, ℂ)`** under
any law giving full mass to unbounded jump times. -/
theorem aemeasurable_interpolatedWalk [Countable H.cells] (hpos : ∀ K, 0 < H.holding K)
    (p : H.cells → Plane) (ε : ℝ≥0) {Q : Measure (ℕ → H.cells)}
    (hQ : ∀ᵐ ω ∂Q, H.JumpTimesUnbounded ω) : AEMeasurable (H.interpolatedWalk p ε) Q := by
  classical
  refine ⟨{ω | H.JumpTimesUnbounded ω}.piecewise (H.interpolatedWalk p ε) (fun _ => 0), ?_, ?_⟩
  · refine ContinuousMap.measurable_iff_eval.2 fun t => ?_
    have hfun : (fun ω => ({ω | H.JumpTimesUnbounded ω}.piecewise (H.interpolatedWalk p ε)
        (fun _ => 0) ω) t) = {ω | H.JumpTimesUnbounded ω}.piecewise
          (fun ω => (ε : ℝ) • H.interpolatedPath p ω ((t : ℝ) / (ε : ℝ) ^ 2)) (fun _ => 0) := by
      funext ω
      by_cases hω : ω ∈ {ω | H.JumpTimesUnbounded ω}
      · rw [Set.piecewise_eq_of_mem _ _ _ hω, Set.piecewise_eq_of_mem _ _ _ hω,
          H.coe_interpolatedWalk hpos hω]
      · rw [Set.piecewise_eq_of_notMem _ _ _ hω, Set.piecewise_eq_of_notMem _ _ _ hω]
        simp
    rw [hfun]
    exact Measurable.piecewise measurableSet_jumpTimesUnbounded
      ((H.measurable_interpolatedPath p _).const_smul (ε : ℝ)) measurable_const
  · filter_upwards [hQ] with ω hω
    exact (Set.piecewise_eq_of_mem _ _ _ hω).symm

end CellConfig

end ReflectedGMS.GMS

open ReflectedGMS.GMS.CellConfig in
assert_no_sorry IsSRWLaw.unique
open ReflectedGMS.GMS.CellConfig in
assert_no_sorry continuous_interpolatedPath
open ReflectedGMS.GMS.CellConfig in
assert_no_sorry aemeasurable_interpolatedWalk

#print axioms ReflectedGMS.GMS.CellConfig.IsSRWLaw.unique
#print axioms ReflectedGMS.GMS.CellConfig.measurable_jumpCount
#print axioms ReflectedGMS.GMS.CellConfig.walk_eq_of_mem
#print axioms ReflectedGMS.GMS.CellConfig.interpolatedPath_eq_lineMap
#print axioms ReflectedGMS.GMS.CellConfig.continuous_interpolatedPath
#print axioms ReflectedGMS.GMS.CellConfig.coe_interpolatedWalk
#print axioms ReflectedGMS.GMS.CellConfig.aemeasurable_interpolatedWalk
