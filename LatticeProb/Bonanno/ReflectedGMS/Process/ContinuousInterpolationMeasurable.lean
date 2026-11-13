/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Process.ContinuousInterpolationMeasurable at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Process.ContinuousInterpolation
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-!
# Evaluation-measurability of the continuous interpolation

The interpolation of `Process/ContinuousInterpolation` is defined pathwise, through a choice of
holding interval and a choice of càdlàg extension.  This file shows that it is nevertheless a
measurable function of the sample at every fixed time, by exhibiting it as a pointwise limit of
explicit measurable **dyadic approximations** (`approx`):

* the exit time of the sojourn through `r` is approximated by the first level-`n` dyadic time
  after `r` at which the path differs from its value at `r` (`exitIndex`, a hitting index over
  countably many measurable events);
* the entry time by the last level-`n` dyadic time before `r` with a different value
  (`entryTime`, a countable supremum);
* the following vertex by the value of the path at the approximate exit time.

`tendsto_approx` proves the convergence at every time, pathwise, from `PathInputs` alone: right
regularity and density of vertex times put level-`n` dyadic times inside every right
neighbourhood of the exit time, and inside every right neighbourhood of a time just before the
entry time; at end-valued times the approximation is the extension at the approximate exit
times, which converge to `r` from the right.

`exists_measurable_interpolation` then produces, from `PathInputs` almost surely, a map into
`C(ℝ≥0, Plane)` with measurable evaluations that is almost surely the interpolation: off a
measurable null set containing every bad sample it is set to `0`.

Nothing here is specific to the reflected walk beyond the measurability of each `X t`.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace ReflectedGMS.ContinuousInterpolation

open AreaClocks SpatialEnds InvarianceMainStatement StatementIngredients
open ReflectedGMS.PathwiseClockClauseLift ReflectedGMS.SpatialExtensionConstruction

variable {V : Type*}

/-! ## Dyadic times -/

/-- The level-`n` dyadic time `k / 2^n`. -/
noncomputable def dyadic (n k : ℕ) : ℝ≥0 := (k : ℝ≥0) / 2 ^ n

theorem coe_dyadic (n k : ℕ) : (dyadic n k : ℝ) = (k : ℝ) / 2 ^ n := by
  simp [dyadic]

theorem dyadic_mono (n : ℕ) {k l : ℕ} (h : k ≤ l) : dyadic n k ≤ dyadic n l := by
  rw [← NNReal.coe_le_coe, coe_dyadic, coe_dyadic]
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  exact div_le_div_of_nonneg_right (by exact_mod_cast h) h2.le

/-- Eventually in `n`, every nonempty open interval contains a level-`n` dyadic time. -/
theorem eventually_exists_dyadic_mem {a b : ℝ≥0} (hab : a < b) :
    ∀ᶠ n in atTop, ∃ k, a < dyadic n k ∧ dyadic n k < b := by
  have hd : (0 : ℝ) < (b : ℝ) - a := sub_pos.2 (NNReal.coe_lt_coe.2 hab)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hd (by norm_num : (1 / 2 : ℝ) < 1)
  filter_upwards [eventually_ge_atTop N] with n hn
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have hpow : (1 / 2 : ℝ) ^ n ≤ (1 / 2) ^ N :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
  have ha0 : (0 : ℝ) ≤ (a : ℝ) * 2 ^ n := by positivity
  refine ⟨⌊(a : ℝ) * 2 ^ n⌋₊ + 1, ?_, ?_⟩
  · rw [← NNReal.coe_lt_coe, coe_dyadic, lt_div_iff₀ h2]
    push_cast
    exact Nat.lt_floor_add_one _
  · rw [← NNReal.coe_lt_coe, coe_dyadic, div_lt_iff₀ h2]
    push_cast
    have hfl := Nat.floor_le ha0
    have hone : (1 / 2 : ℝ) ^ n * 2 ^ n = 1 := by
      rw [← mul_pow]
      norm_num
    have h3 : 1 < (b : ℝ) * 2 ^ n - (a : ℝ) * 2 ^ n := by
      have h4 := mul_lt_mul_of_pos_right (lt_of_le_of_lt hpow hN) h2
      rw [hone, sub_mul] at h4
      exact h4
    linarith

/-! ## The approximations -/

/-- The index of the first level-`n` dyadic time after `r` at which the path differs from its
value at `r` (`0` if there is none). -/
noncomputable def exitIndex (X : ℝ≥0 → Option V) (n : ℕ) (r : ℝ≥0) : ℕ :=
  sInf {k | r < dyadic n k ∧ X (dyadic n k) ≠ X r}

open Classical in
/-- The `k`-th candidate for the approximate entry time. -/
noncomputable def entryTerm (X : ℝ≥0 → Option V) (n : ℕ) (r : ℝ≥0) (k : ℕ) : ℝ≥0 :=
  if dyadic n k ≤ r ∧ X (dyadic n k) ≠ X r then dyadic n k else 0

/-- The last level-`n` dyadic time at or before `r` at which the path differs from its value at
`r` (`0` if there is none). -/
noncomputable def entryTime (X : ℝ≥0 → Option V) (n : ℕ) (r : ℝ≥0) : ℝ≥0 :=
  ⨆ k : ℕ, entryTerm X n r k

/-- The field at an optional vertex, `0` at the nonvertex state. -/
def fieldAt (z : V → Plane) (o : Option V) : Plane := o.elim 0 z

@[simp] theorem fieldAt_some (z : V → Plane) (v : V) : fieldAt z (some v) = z v := rfl

/-- **The level-`n` approximation of the interpolation at time `r`.** -/
noncomputable def approx (z : V → Plane) (X : ℝ≥0 → Option V) (n : ℕ) (r : ℝ≥0) : Plane :=
  if (X r).isSome then
    affinePiece (fieldAt z (X r)) (fieldAt z (X (dyadic n (exitIndex X n r))))
      (entryTime X n r) (dyadic n (exitIndex X n r)) r
  else fieldAt z (X (dyadic n (exitIndex X n r)))

theorem entryTerm_le (X : ℝ≥0 → Option V) (n : ℕ) (r : ℝ≥0) (k : ℕ) :
    entryTerm X n r k ≤ r := by
  rw [entryTerm]
  split_ifs with hk
  · exact hk.1
  · exact zero_le

theorem bddAbove_entryTerm (X : ℝ≥0 → Option V) (n : ℕ) (r : ℝ≥0) :
    BddAbove (range (entryTerm X n r)) := by
  refine ⟨r, ?_⟩
  rintro _ ⟨k, rfl⟩
  exact entryTerm_le X n r k

/-! ## Pathwise convergence -/

/-- **The dyadic approximations converge to the interpolation at every time**, under
`PathInputs`. -/
theorem tendsto_approx {F : IndexedCells V} {z : V → Plane} {X : ℝ≥0 → Option V}
    (h : PathInputs F z X) (r : ℝ≥0) :
    Tendsto (fun n => approx z X n r) atTop
      (𝓝 (interpolation F z X (pathExtension z X) r)) := by
  rcases hXr : X r with _ | v
  · -- an end-valued time: approximate exit times are vertex times converging to `r⁺`
    rw [interpolation_eq_of_none F z X (pathExtension z X) hXr]
    have hexit : ∀ η : ℝ≥0, 0 < η → ∀ᶠ n in atTop,
        r < dyadic n (exitIndex X n r) ∧ dyadic n (exitIndex X n r) < r + η ∧
        ∃ u, X (dyadic n (exitIndex X n r)) = some u := by
      intro η hη
      obtain ⟨p, ⟨u, hpu⟩, hp⟩ := h.dense.exists_between (lt_add_of_pos_right r hη)
      obtain ⟨ε, hε, hεX⟩ := h.rightRegular.1 p ⟨u, hpu⟩
      have hlt : p < min (p + ε) (r + η) := lt_min (lt_add_of_pos_right p hε) hp.2
      filter_upwards [eventually_exists_dyadic_mem hlt] with n hn
      obtain ⟨k, hk1, hk2⟩ := hn
      have hkX : X (dyadic n k) = some u :=
        (hεX _ ⟨hk1.le, hk2.trans_le (min_le_left _ _)⟩).trans hpu
      have hkS : k ∈ {k | r < dyadic n k ∧ X (dyadic n k) ≠ X r} := by
        refine ⟨hp.1.trans hk1, ?_⟩
        rw [hkX, hXr]
        exact Option.some_ne_none u
      have hmem := Nat.sInf_mem ⟨k, hkS⟩
      have hle := Nat.sInf_le hkS
      refine ⟨hmem.1, (dyadic_mono n hle).trans_lt (hk2.trans_le (min_le_right _ _)), ?_⟩
      have hne : X (dyadic n (exitIndex X n r)) ≠ none := fun hc => hmem.2 (hc.trans hXr.symm)
      exact Option.ne_none_iff_exists'.1 hne
    have hconv : Tendsto (fun n => dyadic n (exitIndex X n r)) atTop (𝓝[>] r) := by
      refine tendsto_nhdsWithin_iff.2 ⟨tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩, ?_⟩
      · exact (hexit 1 one_pos).mono fun n hn => ha.trans hn.1
      · refine (hexit (b - r) (tsub_pos_of_lt hb)).mono fun n hn => ?_
        have h2 := hn.2.1
        rwa [add_tsub_cancel_of_le hb.le] at h2
      · exact (hexit 1 one_pos).mono fun n hn => hn.1
    have hZ := h.pathExtension_spec
    have hlim := ((hZ.1.isRightContinuous r).tendsto).comp hconv
    refine hlim.congr' ?_
    filter_upwards [hexit 1 one_pos] with n hn
    obtain ⟨-, -, u, hu⟩ := hn
    have h1 : approx z X n r = fieldAt z (X (dyadic n (exitIndex X n r))) := by
      simp [approx, hXr]
    rw [Function.comp_apply, h1, hu, fieldAt_some, hZ.2 _ u hu]
  · -- a vertex time in the holding interval `[s, t)` at `v`, followed by `w`
    obtain ⟨s, t, w, hI, hmem⟩ := h.hasCompleteCollapsedHoldingIntervals r v hXr
    rw [interpolation_eq_of_mem F z X (pathExtension z X) hI hmem]
    obtain ⟨ε, hε, hεX⟩ := h.rightRegular.1 t ⟨w, hI.2.2.1⟩
    have hwv : some w ≠ some v := fun hwv => hI.2.2.2.1.ne (Option.some_injective _ hwv).symm
    -- the approximate exit times converge to `t`, where the path is at `w`
    have hexit : ∀ η : ℝ≥0, 0 < η → ∀ᶠ n in atTop,
        t ≤ dyadic n (exitIndex X n r) ∧ dyadic n (exitIndex X n r) < t + η ∧
        X (dyadic n (exitIndex X n r)) = some w := by
      intro η hη
      have hlt : t < min (t + ε) (t + η) :=
        lt_min (lt_add_of_pos_right t hε) (lt_add_of_pos_right t hη)
      filter_upwards [eventually_exists_dyadic_mem hlt] with n hn
      obtain ⟨k, hk1, hk2⟩ := hn
      have hkX : X (dyadic n k) = some w :=
        (hεX _ ⟨hk1.le, hk2.trans_le (min_le_left _ _)⟩).trans hI.2.2.1
      have hkS : k ∈ {k | r < dyadic n k ∧ X (dyadic n k) ≠ X r} := by
        refine ⟨hmem.2.trans hk1, ?_⟩
        rw [hkX, hXr]
        exact hwv
      have hmemS := Nat.sInf_mem ⟨k, hkS⟩
      have hle : dyadic n (exitIndex X n r) ≤ dyadic n k := dyadic_mono n (Nat.sInf_le hkS)
      have htle : t ≤ dyadic n (exitIndex X n r) := by
        by_contra hlt'
        push_neg at hlt'
        apply hmemS.2
        exact (hI.2.1 _ ⟨hmem.1.trans hmemS.1.le, hlt'⟩).trans hXr.symm
      refine ⟨htle, hle.trans_lt (hk2.trans_le (min_le_right _ _)), ?_⟩
      exact (hεX _ ⟨htle, hle.trans_lt (hk2.trans_le (min_le_left _ _))⟩).trans hI.2.2.1
    have hT : Tendsto (fun n => dyadic n (exitIndex X n r)) atTop (𝓝 t) := by
      refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
      · exact (hexit 1 one_pos).mono fun n hn => ha.trans_le hn.1
      · refine (hexit (b - t) (tsub_pos_of_lt hb)).mono fun n hn => ?_
        have h2 := hn.2.1
        rwa [add_tsub_cancel_of_le hb.le] at h2
    -- the approximate entry times converge to `s` from below
    have hentry_le : ∀ n, entryTime X n r ≤ s := by
      intro n
      refine ciSup_le fun k => ?_
      rw [entryTerm]
      split_ifs with hk
      · by_contra hlt
        push_neg at hlt
        exact hk.2 (by rw [hXr]; exact hI.2.1 _ ⟨hlt.le, hk.1.trans_lt hmem.2⟩)
      · exact zero_le
    have hentry_lower : ∀ a < s, ∀ᶠ n in atTop, a < entryTime X n r := by
      intro a has
      rcases hI.2.2.2.2 with h0 | hmax
      · rw [h0] at has
        exact absurd has (not_lt.2 zero_le)
      · obtain ⟨p, hp, hpv⟩ := hmax a has
        obtain ⟨ε', hε', hε'X⟩ : ∃ ε' : ℝ≥0, 0 < ε' ∧ ∀ q ∈ Ioo p (p + ε'), X q ≠ some v := by
          rcases hXp : X p with _ | u
          · exact h.rightRegular.2 p hXp v
          · obtain ⟨ε', hε', hε'X⟩ := h.rightRegular.1 p ⟨u, hXp⟩
            refine ⟨ε', hε', fun q hq => ?_⟩
            rw [hε'X q ⟨hq.1.le, hq.2⟩, hXp]
            intro huv
            exact hpv (by rw [hXp, huv])
        have hlt : p < min (p + ε') s := lt_min (lt_add_of_pos_right p hε') hp.2
        filter_upwards [eventually_exists_dyadic_mem hlt] with n hn
        obtain ⟨k, hk1, hk2⟩ := hn
        have hks : dyadic n k < s := hk2.trans_le (min_le_right _ _)
        have hcond : dyadic n k ≤ r ∧ X (dyadic n k) ≠ X r := by
          refine ⟨hks.le.trans hmem.1, ?_⟩
          rw [hXr]
          exact hε'X _ ⟨hk1, hk2.trans_le (min_le_left _ _)⟩
        have h1 : dyadic n k ≤ entryTime X n r := by
          calc dyadic n k = entryTerm X n r k := by rw [entryTerm, if_pos hcond]
            _ ≤ entryTime X n r := le_ciSup (bddAbove_entryTerm X n r) k
        exact hp.1.trans (hk1.trans_le h1)
    have hE : Tendsto (fun n => entryTime X n r) atTop (𝓝 s) :=
      tendsto_order.2 ⟨fun a ha => hentry_lower a ha,
        fun b hb => Eventually.of_forall fun n => (hentry_le n).trans_lt hb⟩
    have hEr : Tendsto (fun n => (entryTime X n r : ℝ)) atTop (𝓝 (s : ℝ)) :=
      NNReal.tendsto_coe.2 hE
    have hTr : Tendsto (fun n => (dyadic n (exitIndex X n r) : ℝ)) atTop (𝓝 (t : ℝ)) :=
      NNReal.tendsto_coe.2 hT
    have hne : (t : ℝ) - s ≠ 0 := sub_ne_zero.2 (NNReal.coe_lt_coe.2 hI.1).ne'
    have hθ : Tendsto (fun n => ((r : ℝ) - entryTime X n r) /
        ((dyadic n (exitIndex X n r) : ℝ) - entryTime X n r)) atTop
        (𝓝 (((r : ℝ) - s) / ((t : ℝ) - s))) :=
      (tendsto_const_nhds.sub hEr).div (hTr.sub hEr) hne
    have hlim := ((AffineMap.lineMap_continuous (R := ℝ) (p := z v) (q := z w)).tendsto _).comp hθ
    refine hlim.congr' ?_
    filter_upwards [hexit 1 one_pos] with n hn
    have h1 : approx z X n r = affinePiece (z v) (z w) (entryTime X n r)
        (dyadic n (exitIndex X n r)) r := by
      simp [approx, hXr, hn.2.2]
    rw [h1]
    rfl

/-! ## Measurability of the approximations -/

section Measurability

open ReflectedWalk

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Every subset of the (discrete) state space is measurable. -/
theorem measurableSet_option (S : Set (Option V)) : MeasurableSet S :=
  MeasurableSpace.measurableSet_top

theorem measurableSet_eq_option [Countable V] {f g : Ω → Option V} (hf : Measurable f)
    (hg : Measurable g) : MeasurableSet {ω | f ω = g ω} := by
  have hset : {ω | f ω = g ω} = ⋃ o : Option V, f ⁻¹' {o} ∩ g ⁻¹' {o} := by
    ext ω
    simp only [mem_setOf_eq, mem_iUnion, mem_inter_iff, mem_preimage, mem_singleton_iff]
    exact ⟨fun h => ⟨f ω, rfl, h.symm⟩, fun ⟨o, h1, h2⟩ => h1.trans h2.symm⟩
  rw [hset]
  exact MeasurableSet.iUnion fun o =>
    (hf (measurableSet_option {o})).inter (hg (measurableSet_option {o}))

/-- A hitting index over countably many measurable events is measurable. -/
theorem measurable_sInf_nat {p : ℕ → Set Ω} (hp : ∀ k, MeasurableSet (p k)) :
    Measurable fun ω => sInf {k | ω ∈ p k} := by
  refine measurable_to_countable' fun m => ?_
  have hset : (fun ω => sInf {k | ω ∈ p k}) ⁻¹' {m} =
      (p m ∩ ⋂ k : Fin m, (p k)ᶜ) ∪ ({_ω | m = 0} ∩ ⋂ k, (p k)ᶜ) := by
    ext ω
    simp only [mem_preimage, mem_singleton_iff, mem_union, mem_inter_iff, mem_iInter,
      mem_compl_iff, mem_setOf_eq]
    constructor
    · intro h
      by_cases hne : {k | ω ∈ p k}.Nonempty
      · left
        have hm := Nat.sInf_mem hne
        rw [h] at hm
        refine ⟨hm, fun k => ?_⟩
        have hk : (k : ℕ) < sInf {k | ω ∈ p k} := by
          rw [h]
          exact k.isLt
        exact Nat.notMem_of_lt_sInf hk
      · right
        rw [Set.not_nonempty_iff_eq_empty] at hne
        rw [hne, Nat.sInf_empty] at h
        refine ⟨h.symm, fun k hk => ?_⟩
        have hk' : k ∈ {k | ω ∈ p k} := hk
        rw [hne] at hk'
        simp at hk'
    · rintro (⟨hm, hlt⟩ | ⟨h0, hnone⟩)
      · refine le_antisymm (Nat.sInf_le hm) ?_
        by_contra hlt'
        push_neg at hlt'
        have hmem : sInf {k | ω ∈ p k} ∈ {k | ω ∈ p k} := Nat.sInf_mem ⟨m, hm⟩
        exact hlt ⟨_, hlt'⟩ hmem
      · have hS : {k | ω ∈ p k} = ∅ := Set.eq_empty_of_forall_notMem fun k hk => hnone k hk
        rw [hS, Nat.sInf_empty, h0]
  rw [hset]
  exact ((hp m).inter (MeasurableSet.iInter fun k : Fin m => (hp k).compl)).union
    ((MeasurableSet.const (m = 0)).inter (MeasurableSet.iInter fun k : ℕ => (hp k).compl))

variable [Countable V] (X : ℝ≥0 → Ω → Option V) (hX : ∀ t, Measurable (X t))
include hX

theorem measurable_exitIndex (n : ℕ) (r : ℝ≥0) :
    Measurable fun ω => exitIndex (fun t => X t ω) n r := by
  have h := measurable_sInf_nat (p := fun k => {ω | r < dyadic n k ∧ X (dyadic n k) ω ≠ X r ω})
    fun k => by
      show MeasurableSet {ω | r < dyadic n k ∧ X (dyadic n k) ω ≠ X r ω}
      rw [Set.setOf_and]
      exact (MeasurableSet.const _).inter (measurableSet_eq_option (hX _) (hX r)).compl
  exact h

theorem measurable_entryTime (n : ℕ) (r : ℝ≥0) :
    Measurable fun ω => entryTime (fun t => X t ω) n r := by
  show Measurable fun ω => ⨆ k, entryTerm (fun t => X t ω) n r k
  refine Measurable.iSup fun k => ?_
  have hset : MeasurableSet {ω | dyadic n k ≤ r ∧ X (dyadic n k) ω ≠ X r ω} := by
    rw [Set.setOf_and]
    exact (MeasurableSet.const _).inter (measurableSet_eq_option (hX _) (hX r)).compl
  simp only [entryTerm]
  exact Measurable.ite hset measurable_const measurable_const

theorem measurable_exitValue (n : ℕ) (r : ℝ≥0) :
    Measurable fun ω => X (dyadic n (exitIndex (fun t => X t ω) n r)) ω := by
  have hF : Measurable fun q : Ω × ℕ => X (dyadic n q.2) q.1 :=
    measurable_from_prod_countable_left fun k => hX (dyadic n k)
  exact hF.comp (measurable_id.prodMk (measurable_exitIndex X hX n r))

omit [Countable V] hX in
theorem measurable_fieldAt (z : V → Plane) : Measurable (fieldAt z) :=
  measurable_from_top

omit [Countable V] hX in
theorem measurable_affinePiece {A B : Ω → Plane} {S T : Ω → ℝ≥0} (hA : Measurable A)
    (hB : Measurable B) (hS : Measurable S) (hT : Measurable T) (r : ℝ≥0) :
    Measurable fun ω => affinePiece (A ω) (B ω) (S ω) (T ω) r := by
  have hθ : Measurable fun ω => ((r : ℝ) - S ω) / ((T ω : ℝ) - S ω) :=
    (measurable_const.sub hS.coe_nnreal_real).div (hT.coe_nnreal_real.sub hS.coe_nnreal_real)
  simp only [affinePiece, AffineMap.lineMap_apply_module']
  exact (hθ.smul (hB.sub hA)).add hA

/-- **Each dyadic approximation is a measurable function of the sample.** -/
theorem measurable_approx (z : V → Plane) (n : ℕ) (r : ℝ≥0) :
    Measurable fun ω => approx z (fun t => X t ω) n r := by
  have hsome : MeasurableSet {ω | (X r ω).isSome = true} :=
    hX r (measurableSet_option {o : Option V | o.isSome = true})
  have hval := (measurable_fieldAt z).comp (measurable_exitValue X hX n r)
  simp only [approx]
  refine Measurable.ite hsome ?_ hval
  exact measurable_affinePiece ((measurable_fieldAt z).comp (hX r)) hval
    (measurable_entryTime X hX n r)
    ((measurable_from_nat (f := fun k : ℕ => dyadic n k)).comp (measurable_exitIndex X hX n r)) r

end Measurability

/-! ## The measurable interpolation -/

open ReflectedWalk in
/-- **A measurable continuous interpolation.**  If the pathwise inputs hold almost surely, there
is a map into `C(ℝ≥0, Plane)` whose time evaluations are measurable and which is, almost surely,
the interpolation of the path. -/
theorem exists_measurable_interpolation {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [Countable V] {F : IndexedCells V} (hF : Geometry F) (hL : LargeCellsFinite F)
    {z : V → Plane} (hz : CellRepresentatives F z) (X : ℝ≥0 → Ω → Option V)
    (hX : ∀ t, Measurable (X t)) (hin : ∀ᵐ ω ∂P, PathInputs F z (fun t => X t ω)) :
    ∃ I : Ω → C(ℝ≥0, Plane), (∀ r, Measurable fun ω => I ω r) ∧
      ∀ᵐ ω ∂P, ⇑(I ω) =
        interpolation F z (fun t => X t ω) (pathExtension z (fun t => X t ω)) := by
  classical
  set G : Set Ω := (toMeasurable P {ω | ¬ PathInputs F z (fun t => X t ω)})ᶜ with hGdef
  have hGm : MeasurableSet G := (measurableSet_toMeasurable _ _).compl
  have hGsub : ∀ ω ∈ G, PathInputs F z (fun t => X t ω) := by
    intro ω hω
    by_contra hbad
    exact hω (subset_toMeasurable _ _ hbad)
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := by
    rw [ae_iff]
    have hset : {ω | ¬ ω ∈ G} = toMeasurable P {ω | ¬ PathInputs F z (fun t => X t ω)} := by
      ext ω
      simp [hGdef]
    rw [hset, measure_toMeasurable]
    exact ae_iff.1 hin
  let J : Ω → ℝ≥0 → Plane := fun ω =>
    if ω ∈ G then interpolation F z (fun t => X t ω) (pathExtension z (fun t => X t ω)) else 0
  have hJ : ∀ ω, Continuous (J ω) := by
    intro ω
    by_cases hω : ω ∈ G
    · simp only [J, if_pos hω]
      exact (hGsub ω hω).continuous_interpolation hF hL hz
    · simp only [J, if_neg hω]
      exact continuous_const
  refine ⟨fun ω => ⟨J ω, hJ ω⟩, fun r => ?_, ?_⟩
  · show Measurable fun ω => J ω r
    have hJr : (fun ω => J ω r) = fun ω =>
        if ω ∈ G then interpolation F z (fun t => X t ω) (pathExtension z (fun t => X t ω)) r
        else 0 := by
      funext ω
      by_cases hω : ω ∈ G
      · simp only [J, if_pos hω]
      · simp only [J, if_neg hω, Pi.zero_apply]
    rw [hJr]
    refine measurable_of_tendsto_metrizable
      (f := fun n ω => if ω ∈ G then approx z (fun t => X t ω) n r else 0)
      (fun n => Measurable.ite hGm (measurable_approx X hX z n r) measurable_const) ?_
    refine tendsto_pi_nhds.2 fun ω => ?_
    by_cases hω : ω ∈ G
    · simp only [if_pos hω]
      exact tendsto_approx (hGsub ω hω) r
    · simp only [if_neg hω]
      exact tendsto_const_nhds
  · filter_upwards [hGae] with ω hω
    show J ω = _
    simp only [J, if_pos hω]

end ReflectedGMS.ContinuousInterpolation
