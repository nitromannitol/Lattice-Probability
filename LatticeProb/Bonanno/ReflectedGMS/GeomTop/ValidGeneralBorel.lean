/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.GeomTop.ValidGeneralBorel at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.GeomTop.ValidGeneralBorelLocal
import LatticeProb.Bonanno.ReflectedGMS.GeomTop.ValidGeneralBorelHausdorff
import Mathlib.Util.AssertNoSorry

/-!
# The valid codes of the general-cell manuscript form a Borel set

`GeomTop.measurableSet_validGeneral`: `{r : Code.RawCode | Code.ValidGeneral r}` is Borel.

`Code.ValidGeneral r` is admissibility, canonical labels and `GeneralGeometry (rawConfig r h)`
(Definition 1.1 + (LCS)).  All clauses but one are Borel coordinate conditions already handled for
the GMS codes (`GMS/ValidCodeSet.lean`).  The remaining clause is the existential over the singular
witness, `∃ S : SingularSet C, C.LineConnectedOff S.sing`, which is reduced in three steps:

1. it is equivalent to `μH[1] (starSet C) = 0` for the canonical singular set
   `starSet C = closure (accSet C ∪ uncSet C ∪ badSet C)` (`ValidBorel.exists_singularSet_iff`,
   `GeomTop/ValidGeneralBorelStar.lean`);
2. `H¹`-nullity of a closure is: for all `N, k` some finite family of closed rational balls of total
   radius `< 1/(k+1)` leaves no point of `accSet ∪ uncSet ∪ badSet` in the open window
   `B(0, N+1) \ ⋃ B̄` (`ValidBorel.hausdorff_closure_eq_zero_iff`,
   `GeomTop/ValidGeneralBorelHausdorff.lean`);
3. on an open window, the absence of such points is the Borel condition `ValidBorel.GoodOn`
   (`ValidBorel.goodOn_iff`, `ValidBorel.measurable_goodOn`, `GeomTop/ValidGeneralBorelLocal.lean`).

Hence `ValidGeneral r ↔ IsValidGeneralCode r` (`ValidBorel.validGeneral_iff`), a countable Boolean
combination of Borel conditions on the slot and conductance coordinates.
-/

set_option autoImplicit false

open MeasureTheory Set

namespace ReflectedGMS.GeomTop.ValidBorel

open Code GMS GMS.ValidCodeSet

/-- **Borel coordinate form of `Code.ValidGeneral`**: admissible conductances, canonical labels,
connected cells, null intersections, intersecting adjacent cells, and — for the singular witness —
for all `N, k` a finite rational ball family of total radius `< 1/(k+1)` outside which no point of
`B(0, N+1)` is an accumulation, uncovered or bad point. -/
structure IsValidGeneralCode (r : RawCode) : Prop where
  admissible : RawAdmissible r
  canonical : ∀ n, (r.1 n).isSome → LeastInteriorLabel (slotCell r n) n
  connected : ∀ n, (r.1 n).isSome → IsConnected (slotCell r n : Set Plane)
  nullInter : ∀ n m, n ≠ m → (r.1 n).isSome → (r.1 m).isSome →
    volume ((slotCell r n : Set Plane) ∩ slotCell r m) = 0
  adjInter : ∀ n m, 0 < r.2 n m → (r.1 n).isSome → (r.1 m).isSome →
    ((slotCell r n : Set Plane) ∩ slotCell r m).Nonempty
  singular : ∀ N k : ℕ, ∃ s : Finset (ℕ × ℚ), ratRadiusSum s < 1 / ((k : ℝ) + 1) ∧
    GoodOn r (windowSet N s)

/-- **The singular-witness clause of an admissible code in Borel coordinate form.** -/
theorem exists_singularSet_rawConfig_iff {r : RawCode} (h : RawAdmissible r) :
    (∃ S : CellConfiguration.SingularSet (rawConfig r h),
        (rawConfig r h).LineConnectedOff S.sing) ↔
      ∀ N k : ℕ, ∃ s : Finset (ℕ × ℚ), ratRadiusSum s < 1 / ((k : ℝ) + 1) ∧
        GoodOn r (windowSet N s) := by
  rw [exists_singularSet_iff, starSet, hausdorff_closure_eq_zero_iff]
  refine forall_congr' fun N => forall_congr' fun k => exists_congr fun s => and_congr Iff.rfl ?_
  exact (goodOn_iff h (isOpen_windowSet N s)).symm

/-- **`ValidGeneral` in Borel coordinate form.** -/
theorem validGeneral_iff (r : RawCode) : ValidGeneral r ↔ IsValidGeneralCode r := by
  constructor
  · rintro ⟨h, hG, hcan⟩
    refine ⟨h, fun n hn => ?_, fun n hn => ?_, fun n m hnm hn hm => ?_, fun n m hpos hn hm => ?_,
      (exists_singularSet_rawConfig_iff h).1 hG.exists_singularSet⟩
    · rw [slotCell_eq_cell r hn]
      exact hcan ⟨n, hn⟩
    · rw [slotCell_eq_cell r hn]
      exact hG.isConnected ⟨n, hn⟩
    · rw [slotCell_eq_cell r hn, slotCell_eq_cell r hm]
      exact hG.volume_inter (v := ⟨n, hn⟩) (w := ⟨m, hm⟩)
        fun heq => hnm (congrArg Subtype.val heq)
    · rw [slotCell_eq_cell r hn, slotCell_eq_cell r hm]
      exact hG.adj_inter_nonempty (v := ⟨n, hn⟩) (w := ⟨m, hm⟩) hpos
  · intro hr
    refine ⟨hr.admissible, ⟨fun v => ?_, fun v => ?_, fun ⦃v w⦄ hvw => ?_,
      (exists_singularSet_rawConfig_iff hr.admissible).2 hr.singular, fun ⦃v w⦄ hadj => ?_⟩,
      fun v => ?_⟩
    · have h1 := hr.connected v.val v.property
      rw [slotCell_val] at h1
      exact h1
    · have h1 := hr.canonical v.val v.property
      rw [slotCell_val] at h1
      exact ⟨rationalPoint v.val, h1.1⟩
    · have h1 := hr.nullInter v.val w.val (fun heq => hvw (Subtype.ext heq)) v.property w.property
      rw [slotCell_val, slotCell_val] at h1
      exact h1
    · have h1 := hr.adjInter v.val w.val hadj v.property w.property
      rw [slotCell_val, slotCell_val] at h1
      exact h1
    · have h1 := hr.canonical v.val v.property
      rw [slotCell_val] at h1
      exact h1

/-- **The Borel coordinate form is a Borel condition.** -/
theorem measurable_isValidGeneralCode : Measurable fun r : RawCode => IsValidGeneralCode r := by
  have h : (fun r : RawCode => IsValidGeneralCode r) = fun r =>
      RawAdmissible r ∧ (∀ n, (r.1 n).isSome → LeastInteriorLabel (slotCell r n) n) ∧
        (∀ n, (r.1 n).isSome → IsConnected (slotCell r n : Set Plane)) ∧
        (∀ n m, n ≠ m → (r.1 n).isSome → (r.1 m).isSome →
          volume ((slotCell r n : Set Plane) ∩ slotCell r m) = 0) ∧
        (∀ n m, 0 < r.2 n m → (r.1 n).isSome → (r.1 m).isSome →
          ((slotCell r n : Set Plane) ∩ slotCell r m).Nonempty) ∧
        ∀ N k : ℕ, ∃ s : Finset (ℕ × ℚ), ratRadiusSum s < 1 / ((k : ℝ) + 1) ∧
          GoodOn r (windowSet N s) := by
    funext r
    exact propext ⟨fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6⟩,
      fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩⟩
  have hpos : ∀ n m : ℕ, Measurable fun r : RawCode => 0 < r.2 n m := fun n m =>
    measurableSet_setOfPred.1 (measurableSet_lt measurable_const (measurable_rawCond n m))
  rw [h]
  refine measurable_rawAdmissible.and ?_
  refine (Measurable.forall fun n =>
    (measurable_isSome n).imp (measurable_leastInteriorLabel_slotCell n)).and ?_
  refine (Measurable.forall fun n =>
    (measurable_isSome n).imp (measurable_isConnected_slotCell n)).and ?_
  refine (Measurable.forall fun n => Measurable.forall fun m => measurable_const.imp
    ((measurable_isSome n).imp ((measurable_isSome m).imp
      (measurable_volume_slotCell_inter_eq_zero n m)))).and ?_
  refine (Measurable.forall fun n => Measurable.forall fun m => (hpos n m).imp
    ((measurable_isSome n).imp ((measurable_isSome m).imp
      (measurable_inter_nonempty_slotCell n m)))).and ?_
  exact Measurable.forall fun N => Measurable.forall fun _ => Measurable.exists fun s =>
    measurable_const.and (measurable_goodOn (windowSet N s))

/-- The valid general codes are the codes in Borel coordinate form. -/
theorem setOf_validGeneral_eq : {r : RawCode | ValidGeneral r} = {r | IsValidGeneralCode r} :=
  Set.ext fun r => validGeneral_iff r

end ReflectedGMS.GeomTop.ValidBorel

namespace ReflectedGMS.GeomTop

open Code

/-- **The valid codes of the general-cell manuscript form a Borel set.** -/
theorem measurableSet_validGeneral : MeasurableSet {r : RawCode | ValidGeneral r} := by
  rw [ValidBorel.setOf_validGeneral_eq]
  exact measurableSet_setOfPred.2 ValidBorel.measurable_isValidGeneralCode

end ReflectedGMS.GeomTop

assert_no_sorry ReflectedGMS.GeomTop.ValidBorel.exists_singularSet_rawConfig_iff
assert_no_sorry ReflectedGMS.GeomTop.ValidBorel.validGeneral_iff
assert_no_sorry ReflectedGMS.GeomTop.ValidBorel.measurable_isValidGeneralCode
assert_no_sorry ReflectedGMS.GeomTop.ValidBorel.setOf_validGeneral_eq
assert_no_sorry ReflectedGMS.GeomTop.measurableSet_validGeneral

#print axioms ReflectedGMS.GeomTop.ValidBorel.exists_singularSet_rawConfig_iff
#print axioms ReflectedGMS.GeomTop.ValidBorel.validGeneral_iff
#print axioms ReflectedGMS.GeomTop.measurableSet_validGeneral
