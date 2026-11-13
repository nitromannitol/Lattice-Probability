/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.DyadicGridLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Geometry.DyadicApproximation
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! Explicit construction of a candidate random dyadic grid.

The consumer `HarmonicMainStatement.IsHarmonicCoordinate` requires a measure on
`DyadicApproximation.Grid` satisfying `DyadicApproximation.UniformGridLaw`, whose
grid has a phase, origins at every integer level and binary parent digits.

Here the whole two-sided grid is produced from five uniform coordinates by the
binary-digit recursion `U (k+1) = (U k + digit k) / 2` for the relative origin
`U k i = -origin k i / side k`: the digits at levels `< 0` are the binary digits
of the level-zero relative origin, the digits at levels `≥ 0` are the binary
digits of a second independent coordinate. Writing the relative origins with
`Int.fract` makes the construction total, so no exceptional all-ones event has to
be removed: the compatibility relation holds at every level for every source
point. The remaining obligation for `UniformGridLaw` is the law computation,
isolated here as the pushforward identity `map_gridCylinder_gridMeasure`. -/

set_option autoImplicit false

open MeasureTheory Set

namespace ReflectedGMS.DyadicGridLaw

open ReflectedGMS.DyadicApproximation

/-! ### Binary digits of a real number -/

/-- The binary digit `⌊2y⌋ - 2⌊y⌋` of a real number. -/
noncomputable def bitInt (y : ℝ) : ℤ := ⌊2 * y⌋ - 2 * ⌊y⌋

theorem bitInt_nonneg (y : ℝ) : 0 ≤ bitInt y := by
  have h : 2 * ⌊y⌋ ≤ ⌊2 * y⌋ := by
    rw [Int.le_floor]
    push_cast
    linarith [Int.floor_le y]
  simp only [bitInt]
  omega

theorem bitInt_lt_two (y : ℝ) : bitInt y < 2 := by
  have h : ⌊2 * y⌋ < 2 * ⌊y⌋ + 2 := by
    rw [Int.floor_lt]
    push_cast
    linarith [Int.lt_floor_add_one y]
  simp only [bitInt]
  omega

/-- The defining halving relation of the binary digit. -/
theorem fract_eq_half (y : ℝ) :
    Int.fract y = (Int.fract (2 * y) + (bitInt y : ℝ)) / 2 := by
  simp only [← Int.self_sub_floor, bitInt]
  push_cast
  ring

theorem measurable_bitInt : Measurable bitInt := by
  have h : Measurable fun y : ℝ => (⌊2 * y⌋, ⌊y⌋) :=
    (Int.measurable_floor.comp (measurable_const.mul measurable_id)).prodMk
      Int.measurable_floor
  exact (measurable_of_countable fun q : ℤ × ℤ => q.1 - 2 * q.2).comp h

/-- The two element type of digits, from an integer that is `0` or `1`. -/
def intToFin2 (n : ℤ) : Fin 2 := if n = 1 then 1 else 0

/-! ### The grid data attached to a source point -/

/-- The source space: the phase coordinate, the level-zero relative origin
coordinates, and the coordinates carrying the digits at nonnegative levels. -/
abbrev Source := ℝ × (Fin 2 → ℝ) × (Fin 2 → ℝ)

/-- The parent digit at level `k`. At negative levels it is a binary digit of
the level-zero relative origin, at nonnegative levels of the second source. -/
noncomputable def digitInt (u w : Fin 2 → ℝ) (k : ℤ) (i : Fin 2) : ℤ :=
  if k < 0 then bitInt ((2 : ℝ) ^ (-(k + 1)) * Int.fract (u i))
  else bitInt ((2 : ℝ) ^ k * Int.fract (w i))

theorem digitInt_nonneg (u w : Fin 2 → ℝ) (k : ℤ) (i : Fin 2) :
    0 ≤ digitInt u w k i := by
  unfold digitInt
  split_ifs <;> exact bitInt_nonneg _

theorem digitInt_lt_two (u w : Fin 2 → ℝ) (k : ℤ) (i : Fin 2) :
    digitInt u w k i < 2 := by
  unfold digitInt
  split_ifs <;> exact bitInt_lt_two _

noncomputable def digitFin (u w : Fin 2 → ℝ) (k : ℤ) (i : Fin 2) : Fin 2 :=
  intToFin2 (digitInt u w k i)

theorem digitFin_val (u w : Fin 2 → ℝ) (k : ℤ) (i : Fin 2) :
    ((digitFin u w k i).val : ℝ) = (digitInt u w k i : ℝ) := by
  have h0 := digitInt_nonneg u w k i
  have h2 := digitInt_lt_two u w k i
  have h : digitInt u w k i = 0 ∨ digitInt u w k i = 1 := by omega
  rcases h with h | h <;> simp [digitFin, intToFin2, h]

/-- The integer accumulated from the digits at levels `0, …, k - 1`. -/
noncomputable def futureNum (u w : Fin 2 → ℝ) (k : ℤ) (i : Fin 2) : ℝ :=
  ∑ j ∈ Finset.range k.toNat, (2 : ℝ) ^ j * (digitInt u w (j : ℤ) i : ℝ)

theorem futureNum_nonneg (u w : Fin 2 → ℝ) (k : ℤ) (i : Fin 2) :
    0 ≤ futureNum u w k i := by
  refine Finset.sum_nonneg fun j _ => ?_
  have h := digitInt_nonneg u w (j : ℤ) i
  have h' : (0 : ℝ) ≤ (digitInt u w (j : ℤ) i : ℝ) := by exact_mod_cast h
  positivity

theorem sum_digits_le (u w : Fin 2 → ℝ) (i : Fin 2) (m : ℕ) :
    (∑ j ∈ Finset.range m, (2 : ℝ) ^ j * (digitInt u w (j : ℤ) i : ℝ)) ≤ 2 ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, pow_succ]
    have hd : ((digitInt u w (m : ℤ) i : ℤ) : ℝ) ≤ 1 := by
      have := digitInt_lt_two u w (m : ℤ) i
      have h1 : digitInt u w (m : ℤ) i ≤ 1 := by omega
      exact_mod_cast h1
    have h2 : (0 : ℝ) < 2 ^ m := by positivity
    have h3 := mul_le_mul_of_nonneg_left hd (le_of_lt h2)
    linarith

theorem futureNum_le (u w : Fin 2 → ℝ) (k : ℤ) (i : Fin 2) :
    futureNum u w k i ≤ 2 ^ k.toNat - 1 :=
  sum_digits_le u w i k.toNat

/-- The relative origin at level `k`: the position of the grid origin inside its
own cell, measured in units of the side length. -/
noncomputable def rel (u w : Fin 2 → ℝ) (k : ℤ) (i : Fin 2) : ℝ :=
  Int.fract ((2 : ℝ) ^ (-k) * (Int.fract (u i) + futureNum u w k i))

theorem rel_nonneg (u w : Fin 2 → ℝ) (k : ℤ) (i : Fin 2) : 0 ≤ rel u w k i :=
  Int.fract_nonneg _

theorem rel_lt_one (u w : Fin 2 → ℝ) (k : ℤ) (i : Fin 2) : rel u w k i < 1 :=
  Int.fract_lt_one _

theorem rel_of_nonneg (u w : Fin 2 → ℝ) {k : ℤ} (hk : 0 ≤ k) (i : Fin 2) :
    rel u w k i = (2 : ℝ) ^ (-k) * (Int.fract (u i) + futureNum u w k i) := by
  unfold rel
  refine Int.fract_eq_self.2 ⟨?_, ?_⟩
  · have h1 := futureNum_nonneg u w k i
    have h2 := Int.fract_nonneg (u i)
    have h3 : (0 : ℝ) < (2 : ℝ) ^ (-k) := by positivity
    have : (0 : ℝ) ≤ Int.fract (u i) + futureNum u w k i := by linarith
    exact mul_nonneg (le_of_lt h3) this
  · have hx : Int.fract (u i) + futureNum u w k i < 2 ^ k.toNat := by
      have h1 := Int.fract_lt_one (u i)
      have h2 := futureNum_le u w k i
      linarith
    have hk2 : ((2 : ℝ) ^ k.toNat) = (2 : ℝ) ^ (k : ℤ) := by
      rw [← zpow_natCast (2 : ℝ) k.toNat, Int.toNat_of_nonneg hk]
    have hpos : (0 : ℝ) < (2 : ℝ) ^ (k : ℤ) := by positivity
    rw [hk2] at hx
    rw [zpow_neg, inv_mul_eq_div, div_lt_one hpos]
    exact hx

/-- The exact compatibility relation between successive relative origins. -/
theorem rel_succ (u w : Fin 2 → ℝ) (k : ℤ) (i : Fin 2) :
    rel u w (k + 1) i = (rel u w k i + (digitInt u w k i : ℝ)) / 2 := by
  by_cases hk : 0 ≤ k
  · have hk1 : (0 : ℤ) ≤ k + 1 := by omega
    have hF : futureNum u w (k + 1) i
        = futureNum u w k i + (2 : ℝ) ^ k.toNat * (digitInt u w k i : ℝ) := by
      have h1 : (k + 1).toNat = k.toNat + 1 := by omega
      simp only [futureNum, h1, Finset.sum_range_succ, Int.toNat_of_nonneg hk]
    rw [rel_of_nonneg u w hk1 i, rel_of_nonneg u w hk i, hF]
    have h2 : (2 : ℝ) ^ (-(k + 1)) = (2 : ℝ) ^ (-k) / 2 := by
      rw [show -(k + 1) = -k - 1 by ring, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
    have h3 : (2 : ℝ) ^ k.toNat = ((2 : ℝ) ^ (-k))⁻¹ := by
      rw [zpow_neg, inv_inv, ← zpow_natCast (2 : ℝ) k.toNat, Int.toNat_of_nonneg hk]
    have h4 : (2 : ℝ) ^ (-k) ≠ 0 := by positivity
    rw [h2, h3]
    field_simp
    ring
  · have hk' : k < 0 := by omega
    have hk0 : k.toNat = 0 := by omega
    have hk1 : (k + 1).toNat = 0 := by omega
    have hFk : futureNum u w k i = 0 := by simp [futureNum, hk0]
    have hFk1 : futureNum u w (k + 1) i = 0 := by simp [futureNum, hk1]
    have hd : digitInt u w k i = bitInt ((2 : ℝ) ^ (-(k + 1)) * Int.fract (u i)) := by
      simp only [digitInt, if_pos hk']
    have h2 : (2 : ℝ) ^ (-k) * Int.fract (u i)
        = 2 * ((2 : ℝ) ^ (-(k + 1)) * Int.fract (u i)) := by
      rw [show -(k + 1) = -k - 1 by ring, zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
      ring
    unfold rel
    simp only [hFk, hFk1, hd, add_zero]
    rw [h2]
    exact fract_eq_half _

/-! ### The grid attached to a source point -/

/-- The grid origin at level `k`, at relative position `rel` inside its cell. -/
noncomputable def originOf (p : ℝ) (u w : Fin 2 → ℝ) (k : ℤ) (i : Fin 2) : ℝ :=
  -((2 : ℝ) ^ (Int.fract p + (k : ℝ)) * rel u w k i)

theorem originOf_position (p : ℝ) (u w : Fin 2 → ℝ) (k : ℤ) (i : Fin 2) :
    -(2 : ℝ) ^ (Int.fract p + (k : ℝ)) < originOf p u w k i ∧ originOf p u w k i ≤ 0 := by
  have hS : (0 : ℝ) < (2 : ℝ) ^ (Int.fract p + (k : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have h0 := rel_nonneg u w k i
  have h1 := rel_lt_one u w k i
  constructor
  · simp only [originOf]
    nlinarith [mul_pos hS (sub_pos.2 h1)]
  · simp only [originOf]
    have : 0 ≤ (2 : ℝ) ^ (Int.fract p + (k : ℝ)) * rel u w k i :=
      mul_nonneg (le_of_lt hS) h0
    linarith

theorem originOf_compatible (p : ℝ) (u w : Fin 2 → ℝ) (k : ℤ) (i : Fin 2) :
    originOf p u w k i = originOf p u w (k + 1) i +
      (2 : ℝ) ^ (Int.fract p + (k : ℝ)) * ((digitFin u w k i).val : ℝ) := by
  have hs : (2 : ℝ) ^ (Int.fract p + ((k + 1 : ℤ) : ℝ))
      = (2 : ℝ) ^ (Int.fract p + (k : ℝ)) * 2 := by
    rw [show Int.fract p + ((k + 1 : ℤ) : ℝ) = (Int.fract p + (k : ℝ)) + 1 by push_cast; ring,
      Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one]
  have hr := rel_succ u w k i
  simp only [originOf, hs, hr, digitFin_val]
  ring

/-- The grid produced by the five uniform source coordinates. -/
noncomputable def gridOf (ω : Source) : Grid where
  phase := Int.fract ω.1
  phase_mem := ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
  origin := originOf ω.1 ω.2.1 ω.2.2
  digit := digitFin ω.2.1 ω.2.2
  origin_position := originOf_position ω.1 ω.2.1 ω.2.2
  compatible := originOf_compatible ω.1 ω.2.1 ω.2.2

@[simp] theorem gridOf_phase (ω : Source) : (gridOf ω).phase = Int.fract ω.1 := rfl

@[simp] theorem gridOf_origin (ω : Source) :
    (gridOf ω).origin = originOf ω.1 ω.2.1 ω.2.2 := rfl

@[simp] theorem gridOf_digit (ω : Source) :
    (gridOf ω).digit = digitFin ω.2.1 ω.2.2 := rfl

theorem side_gridOf (ω : Source) (k : ℤ) :
    side (gridOf ω) k = (2 : ℝ) ^ (Int.fract ω.1 + (k : ℝ)) := rfl

/-- The relative origin is exactly the coordinate recorded by `gridCylinder`. -/
theorem neg_originOf_div (p : ℝ) (u w : Fin 2 → ℝ) (k : ℤ) (i : Fin 2) :
    -originOf p u w k i / (2 : ℝ) ^ (Int.fract p + (k : ℝ)) = rel u w k i := by
  have hS : (0 : ℝ) < (2 : ℝ) ^ (Int.fract p + (k : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  simp only [originOf]
  field_simp

theorem gridCylinder_gridOf (k : ℤ) (n : ℕ) (ω : Source) :
    gridCylinder k n (gridOf ω) =
      (Int.fract ω.1, (fun i => rel ω.2.1 ω.2.2 k i,
        fun (j : Fin n) (i : Fin 2) => digitFin ω.2.1 ω.2.2 (k + (j.val : ℤ)) i)) := by
  simp only [gridCylinder, gridOf_phase, gridOf_origin, gridOf_digit, side_gridOf,
    Prod.mk.injEq, true_and]
  exact ⟨funext fun i => neg_originOf_div _ _ _ _ _, trivial⟩

/-! ### Measurability -/

theorem measurable_digitInt (k : ℤ) (i : Fin 2) :
    Measurable fun ω : Source => digitInt ω.2.1 ω.2.2 k i := by
  by_cases hk : k < 0
  · simp only [digitInt, if_pos hk]
    exact measurable_bitInt.comp (measurable_const.mul
      (measurable_fract.comp ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))))
  · simp only [digitInt, if_neg hk]
    exact measurable_bitInt.comp (measurable_const.mul
      (measurable_fract.comp ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd))))

theorem measurable_digitFin (k : ℤ) (i : Fin 2) :
    Measurable fun ω : Source => digitFin ω.2.1 ω.2.2 k i :=
  (measurable_of_countable intToFin2).comp (measurable_digitInt k i)

theorem measurable_futureNum (k : ℤ) (i : Fin 2) :
    Measurable fun ω : Source => futureNum ω.2.1 ω.2.2 k i := by
  simp only [futureNum]
  exact Finset.measurable_sum _ fun j _ => measurable_const.mul
    ((measurable_of_countable fun n : ℤ => (n : ℝ)).comp (measurable_digitInt (j : ℤ) i))

theorem measurable_rel (k : ℤ) (i : Fin 2) :
    Measurable fun ω : Source => rel ω.2.1 ω.2.2 k i := by
  simp only [rel]
  exact measurable_fract.comp (measurable_const.mul
    ((measurable_fract.comp
      ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))).add
      (measurable_futureNum k i)))

theorem measurable_two_rpow (c : ℝ) : Measurable fun x : ℝ => (2 : ℝ) ^ (x + c) :=
  (continuous_const.rpow (continuous_id.add continuous_const)
    fun _ => Or.inl (by norm_num)).measurable

theorem measurable_originOf (k : ℤ) (i : Fin 2) :
    Measurable fun ω : Source => originOf ω.1 ω.2.1 ω.2.2 k i := by
  simp only [originOf]
  exact (((measurable_two_rpow (k : ℝ)).comp (measurable_fract.comp measurable_fst)).mul
    (measurable_rel k i)).neg

theorem measurable_gridCoords :
    Measurable fun D : Grid => (D.phase, D.origin, D.digit) := fun _ hs => ⟨_, hs, rfl⟩

theorem measurable_gridOf : Measurable gridOf := by
  have hcomp : Measurable fun ω : Source =>
      ((gridOf ω).phase, (gridOf ω).origin, (gridOf ω).digit) := by
    refine (measurable_fract.comp measurable_fst).prodMk (Measurable.prodMk ?_ ?_)
    · exact Measurable.of_eval fun k => Measurable.of_eval fun i => measurable_originOf k i
    · exact Measurable.of_eval fun k => Measurable.of_eval fun i => measurable_digitFin k i
  intro s hs
  obtain ⟨t, ht, rfl⟩ := hs
  exact hcomp ht

theorem measurable_gridCylinder (k : ℤ) (n : ℕ) : Measurable (gridCylinder k n) := by
  have h := measurable_gridCoords
  have hphase : Measurable fun D : Grid => D.phase := measurable_fst.comp h
  have horigin : Measurable fun D : Grid => D.origin :=
    measurable_fst.comp (measurable_snd.comp h)
  have hdigit : Measurable fun D : Grid => D.digit :=
    measurable_snd.comp (measurable_snd.comp h)
  refine hphase.prodMk (Measurable.prodMk ?_ ?_)
  · refine Measurable.of_eval fun i => ?_
    exact (((measurable_pi_apply i).comp
      ((measurable_pi_apply k).comp horigin)).neg).div
      ((measurable_two_rpow (k : ℝ)).comp hphase)
  · refine Measurable.of_eval fun j => Measurable.of_eval fun i => ?_
    exact (measurable_pi_apply i).comp ((measurable_pi_apply (k + (j.val : ℤ))).comp hdigit)

/-! ### The candidate law -/

/-- Lebesgue measure on the unit interval, in each of the five coordinates. -/
noncomputable def unitMeasure : Measure ℝ := volume.restrict (Set.Ico (0 : ℝ) 1)

theorem isProbabilityMeasure_unitMeasure : IsProbabilityMeasure unitMeasure := by
  refine ⟨?_⟩
  rw [unitMeasure, Measure.restrict_apply_univ, Real.volume_Ico]
  norm_num

noncomputable def sourceMeasure : Measure Source :=
  unitMeasure.prod ((Measure.pi fun _ : Fin 2 => unitMeasure).prod
    (Measure.pi fun _ : Fin 2 => unitMeasure))

theorem isProbabilityMeasure_sourceMeasure : IsProbabilityMeasure sourceMeasure := by
  have := isProbabilityMeasure_unitMeasure
  rw [sourceMeasure]
  infer_instance

/-- The candidate grid law: the image of the uniform source measure. -/
noncomputable def gridMeasure : Measure Grid := sourceMeasure.map gridOf

theorem isProbabilityMeasure_gridMeasure : IsProbabilityMeasure gridMeasure := by
  have := isProbabilityMeasure_sourceMeasure
  refine ⟨?_⟩
  rw [gridMeasure, Measure.map_apply measurable_gridOf MeasurableSet.univ,
    Set.preimage_univ, measure_univ]

/-- The cylinder law of the constructed grid, reduced to an explicit statement
about the five uniform coordinates. This is exactly the remaining input of
`DyadicApproximation.UniformGridLaw` for `gridMeasure`: it remains to identify
the right hand side with the uniform phase, uniform relative origin and
independent fair parent digits. -/
theorem map_gridCylinder_gridMeasure (k : ℤ) (n : ℕ) :
    gridMeasure.map (gridCylinder k n) =
      sourceMeasure.map (fun ω : Source => (Int.fract ω.1,
        (fun i => rel ω.2.1 ω.2.2 k i,
          fun (j : Fin n) (i : Fin 2) => digitFin ω.2.1 ω.2.2 (k + (j.val : ℤ)) i))) := by
  rw [gridMeasure, Measure.map_map (measurable_gridCylinder k n) measurable_gridOf]
  congr 1
  funext ω
  exact gridCylinder_gridOf k n ω

end ReflectedGMS.DyadicGridLaw
