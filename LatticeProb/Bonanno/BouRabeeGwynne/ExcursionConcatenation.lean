/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module BouRabeeGwynne.ExcursionConcatenation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.BouRabeeGwynne.SkeletonCurveComparison
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.ContinuousOn
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-! Actual concatenation of a finite sequence of continuous excursions.
Matching endpoints are the only compatibility condition. Fixed-partition
concatenation is a contraction, hence a measurable operation on the excursions. -/

open Set
open scoped unitInterval ENNReal

namespace BouRabeeGwynne

/-- A finite family of genuine excursions with adjacent endpoints identified. -/
abbrev ExcursionChain (n d : ℕ) :=
  {c : Fin (n + 1) → C(unitInterval, EuclideanSpace ℝ (Fin d)) //
    ∀ i j, i.succ = j.castSucc → c i 1 = c j 0}

namespace TimePartition

variable {n d : ℕ} (P Q : TimePartition n)

/-- A fixed canonical partition for concatenating any prescribed finite
number of excursions; no random duration or arbitrary partition choice enters
its measurable concatenation map. -/
noncomputable def uniform (n : ℕ) : TimePartition n where
  knots i := ⟨(i.val : ℝ) / ((n + 1 : ℕ) : ℝ), by
    have hd : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    refine ⟨div_nonneg (Nat.cast_nonneg _) hd.le, (div_le_one hd).mpr ?_⟩
    have hi : i.val ≤ n + 1 := by omega
    exact_mod_cast hi⟩
  strictMono_knots := by
    intro i j hij
    change (i.val : ℝ) / ((n + 1 : ℕ) : ℝ) < (j.val : ℝ) / ((n + 1 : ℕ) : ℝ)
    apply div_lt_div_of_pos_right _ (by positivity)
    exact_mod_cast hij
  first := by apply Subtype.ext; simp
  last := by
    apply Subtype.ext
    change (((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) = 1
    exact div_self (by positivity)

/-- Local normalized time, clamped outside the selected interval. -/
noncomputable def localTime (i : Fin (n + 1)) (t : unitInterval) : unitInterval :=
  projIcc 0 1 zero_le_one (((t : ℝ) - P.left i) / (P.right i - P.left i))

lemma continuous_localTime (i : Fin (n + 1)) : Continuous (P.localTime i) := by
  unfold localTime
  fun_prop

@[simp] lemma localTime_left (i : Fin (n + 1)) : P.localTime i (P.left i) = 0 := by
  simp [localTime, projIcc_left]

@[simp] lemma localTime_right (i : Fin (n + 1)) : P.localTime i (P.right i) = 1 := by
  simp [localTime, div_self (P.gap_pos i).ne', projIcc_right]

private lemma excursion_eq_on_overlap_le (c : ExcursionChain n d)
    (i j : Fin (n + 1)) (hij : i ≤ j) {t : unitInterval}
    (hi : P.left i ≤ t ∧ t ≤ P.right i)
    (hj : P.left j ≤ t ∧ t ≤ P.right j) :
    c.val i (P.localTime i t) = c.val j (P.localTime j t) := by
  by_cases heq : i = j
  · rw [heq]
  have hgap := P.right_le_left (lt_of_le_of_ne hij heq)
  have hti : t = P.right i := le_antisymm hi.2 (hgap.trans hj.1)
  have htj : t = P.left j := le_antisymm (hi.2.trans hgap) hj.1
  have hindex : i.succ = j.castSucc := P.strictMono_knots.injective (hti.symm.trans htj)
  rw [hti, P.localTime_right]
  rw [← hti, htj, P.localTime_left]
  exact c.property i j hindex

lemma excursion_eq_on_overlap (c : ExcursionChain n d)
    (i j : Fin (n + 1)) {t : unitInterval}
    (hi : P.left i ≤ t ∧ t ≤ P.right i)
    (hj : P.left j ≤ t ∧ t ≤ P.right j) :
    c.val i (P.localTime i t) = c.val j (P.localTime j t) := by
  rcases le_total i j with hij | hji
  · exact P.excursion_eq_on_overlap_le c i j hij hi hj
  · exact (P.excursion_eq_on_overlap_le c j i hji hj hi).symm

/-- The actual pasted function. Agreement at a shared knot makes the interval
selection immaterial. -/
noncomputable def excursionConcatFun (c : ExcursionChain n d) (t : unitInterval) :
    EuclideanSpace ℝ (Fin d) := c.val (P.interval t) (P.localTime (P.interval t) t)

lemma excursionConcatFun_eq (c : ExcursionChain n d) (i : Fin (n + 1))
    {t : unitInterval} (ht : P.left i ≤ t ∧ t ≤ P.right i) :
    P.excursionConcatFun c t = c.val i (P.localTime i t) :=
  P.excursion_eq_on_overlap c (P.interval t) i (P.interval_spec t) ht

lemma continuous_excursionConcatFun (c : ExcursionChain n d) :
    Continuous (P.excursionConcatFun c) := by
  have hpiece (i : Fin (n + 1)) :
      ContinuousOn (P.excursionConcatFun c) (Icc (P.left i) (P.right i)) := by
    apply ((c.val i).continuous.comp (P.continuous_localTime i)).continuousOn.congr
    intro t ht
    exact P.excursionConcatFun_eq c i ht
  have hfinite (s : Finset (Fin (n + 1))) :
      ContinuousOn (P.excursionConcatFun c) (⋃ i ∈ s, Icc (P.left i) (P.right i)) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      simp only [Finset.mem_insert, Set.iUnion_iUnion_eq_or_left]
      exact (hpiece i).union_of_isClosed ih isClosed_Icc
        (isClosed_biUnion_finset fun _ _ => isClosed_Icc)
  have hcover : (⋃ i ∈ (Finset.univ : Finset (Fin (n + 1))),
      Icc (P.left i) (P.right i)) = univ := by
    ext t
    simp only [Finset.mem_univ, iUnion_true, mem_iUnion, mem_Icc, mem_univ, iff_true]
    exact P.exists_interval t
  rw [← continuousOn_univ, ← hcover]
  exact hfinite Finset.univ

/-- The concatenated continuous excursion path, with an explicit duration
partition and no arbitrary representative choice. -/
noncomputable def concatenate (c : ExcursionChain n d) :
    C(unitInterval, EuclideanSpace ℝ (Fin d)) :=
  ⟨P.excursionConcatFun c, P.continuous_excursionConcatFun c⟩

lemma concatenate_apply (c : ExcursionChain n d) (i : Fin (n + 1))
    {t : unitInterval} (ht : P.left i ≤ t ∧ t ≤ P.right i) :
    P.concatenate c t = c.val i (P.localTime i t) := P.excursionConcatFun_eq c i ht

@[simp] lemma concatenate_left (c : ExcursionChain n d) (i : Fin (n + 1)) :
    P.concatenate c (P.left i) = c.val i 0 := by
  rw [P.concatenate_apply c i ⟨le_rfl, (P.left_lt_right i).le⟩, P.localTime_left]

@[simp] lemma concatenate_right (c : ExcursionChain n d) (i : Fin (n + 1)) :
    P.concatenate c (P.right i) = c.val i 1 := by
  rw [P.concatenate_apply c i ⟨(P.left_lt_right i).le, le_rfl⟩, P.localTime_right]

/-- Concatenating with fixed time intervals does not amplify uniform errors
in any of the input excursions. -/
lemma dist_concatenate_le (c e : ExcursionChain n d) :
    dist (P.concatenate c) (P.concatenate e) ≤ dist c e := by
  apply ContinuousMap.dist_le_iff_of_nonempty.mpr
  intro t
  change dist (c.val (P.interval t) (P.localTime (P.interval t) t))
      (e.val (P.interval t) (P.localTime (P.interval t) t)) ≤ dist c e
  exact (ContinuousMap.dist_apply_le_dist _).trans
    ((dist_pi_le_iff' (f := c.val) (g := e.val)).mp le_rfl (P.interval t))

lemma concatenate_lipschitz : LipschitzWith 1 (P.concatenate (d := d)) := by
  apply LipschitzWith.of_dist_le_mul
  intro c e
  simpa only [NNReal.coe_one, one_mul] using P.dist_concatenate_le c e

lemma continuous_concatenate : Continuous (P.concatenate (d := d)) :=
  P.concatenate_lipschitz.continuous

lemma measurable_concatenate : Measurable (P.concatenate (d := d)) :=
  P.continuous_concatenate.measurable

/-- Corresponding excursions need only remain close to their own starting
vertices; their physical time durations may differ arbitrarily. -/
theorem concatenate_curveSpace_edist_le (c e : ExcursionChain n d) {α β γ : ℝ}
    (hc : ∀ i t, dist (c.val i t) (c.val i 0) ≤ α)
    (hstarts : ∀ i, dist (c.val i 0) (e.val i 0) ≤ β)
    (he : ∀ i t, dist (e.val i t) (e.val i 0) ≤ γ) :
    edist (CurveSpace.project (P.concatenate c)) (CurveSpace.project (Q.concatenate e)) ≤
      ENNReal.ofReal (α + β + γ) := by
  apply P.curveSpace_edist_le_of_segment_bounds Q
    ⟨P.concatenate c⟩ ⟨Q.concatenate e⟩
  · intro i t ht
    change dist (P.concatenate c t) (P.concatenate c (P.left i)) ≤ α
    rw [P.concatenate_apply c i ht, P.concatenate_left]
    exact hc i _
  · intro i
    change dist (P.concatenate c (P.left i)) (Q.concatenate e (Q.left i)) ≤ β
    simpa only [P.concatenate_left, Q.concatenate_left] using hstarts i
  · intro i t ht
    change dist (Q.concatenate e t) (Q.concatenate e (Q.left i)) ≤ γ
    rw [Q.concatenate_apply e i ht, Q.concatenate_left]
    exact he i _

/-- The forward affine parametrization of one actual partition interval. -/
noncomputable def intervalParam (i : Fin (n + 1)) (u : unitInterval) : unitInterval :=
  ⟨P.left i + (u : ℝ) * (P.right i - P.left i),
    ⟨add_nonneg (P.left i).property.1 (mul_nonneg u.property.1 (P.gap_pos i).le), by
      have hm := mul_le_mul_of_nonneg_right u.property.2 (P.gap_pos i).le
      have hb := (P.right i).property.2
      nlinarith⟩⟩

lemma continuous_intervalParam (i : Fin (n + 1)) : Continuous (P.intervalParam i) := by
  unfold intervalParam
  fun_prop

@[simp] lemma intervalParam_zero (i : Fin (n + 1)) : P.intervalParam i 0 = P.left i := by
  apply Subtype.ext
  simp [intervalParam]

@[simp] lemma intervalParam_one (i : Fin (n + 1)) : P.intervalParam i 1 = P.right i := by
  apply Subtype.ext
  simp [intervalParam]

lemma intervalParam_localTime (i : Fin (n + 1)) {t : unitInterval}
    (ht : P.left i ≤ t ∧ t ≤ P.right i) :
    P.intervalParam i (P.localTime i t) = t := by
  have hratio : ((t : ℝ) - P.left i) / (P.right i - P.left i) ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr ht.1) (P.gap_pos i).le
    · apply (div_le_one (P.gap_pos i)).mpr
      exact sub_le_sub_right (show (t : ℝ) ≤ (P.right i : ℝ) from ht.2) _
  apply Subtype.ext
  simp only [intervalParam, localTime, projIcc_of_mem zero_le_one hratio, Subtype.coe_mk]
  field_simp [(P.gap_pos i).ne']
  ring

/-- Restrict an actual normalized continuous path to its consecutive time
intervals. The adjacent excursion endpoints agree by construction. -/
noncomputable def restrictChain (f : C(unitInterval, EuclideanSpace ℝ (Fin d))) :
    ExcursionChain n d :=
  ⟨fun i => ⟨fun u => f (P.intervalParam i u),
      f.continuous.comp (P.continuous_intervalParam i)⟩, by
    intro i j hij
    change f (P.intervalParam i 1) = f (P.intervalParam j 0)
    rw [P.intervalParam_one, P.intervalParam_zero]
    exact congrArg f (congrArg P.knots hij)⟩

/-- Pasting the actual restrictions recovers the original path exactly, not
just an endpoint-equivalent or arbitrarily chosen curve representation. -/
@[simp] theorem concatenate_restrictChain
    (f : C(unitInterval, EuclideanSpace ℝ (Fin d))) :
    P.concatenate (P.restrictChain f) = f := by
  apply ContinuousMap.ext
  intro t
  rw [P.concatenate_apply (P.restrictChain f) (P.interval t) (P.interval_spec t)]
  change f (P.intervalParam (P.interval t) (P.localTime (P.interval t) t)) = f t
  rw [P.intervalParam_localTime _ (P.interval_spec t)]

lemma restrictChain_lipschitz : LipschitzWith 1 (P.restrictChain (d := d)) := by
  apply LipschitzWith.of_dist_le_mul
  intro f g
  change dist (P.restrictChain f).val (P.restrictChain g).val ≤ (1 : ℝ) * dist f g
  rw [one_mul]
  apply dist_pi_le_iff'.mpr
  intro i
  apply ContinuousMap.dist_le_iff_of_nonempty.mpr
  intro t
  exact ContinuousMap.dist_apply_le_dist (P.intervalParam i t)

lemma measurable_restrictChain : Measurable (P.restrictChain (d := d)) :=
  P.restrictChain_lipschitz.continuous.measurable

end TimePartition
end BouRabeeGwynne
