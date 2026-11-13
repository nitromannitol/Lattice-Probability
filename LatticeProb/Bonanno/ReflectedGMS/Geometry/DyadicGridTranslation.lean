/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Geometry.DyadicGridTranslation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.DyadicGridLawUniqueness

/-! # The translation (re-rooting) action on dyadic grids

The consumer `Spatial.MarkedBlockAveraging.MarkedReRooting` needs a re-rooting
action `ω ↦ ω - z` on marked configurations whose grid component is an actual
`DyadicApproximation.Grid`, jointly measurable in the configuration and the
shift, and geometrically correct: the squares of the translated grid are exactly
the translates of the squares of the original grid.

This file constructs that action on the grid component and proves precisely
those facts.

* `relativeOrigin D k i = -D.origin k i / side D k` is the position of the grid
  origin inside its own level-`k` cell, the coordinate already read by
  `DyadicApproximation.gridCylinder`.  `Grid.origin_position` puts it in `[0,1)`
  and `Grid.compatible` gives `2 * relativeOrigin D (k+1) i = relativeOrigin D k i
  + digit` (`two_mul_relativeOrigin_succ`).
* Re-rooting at `u` subtracts `u`, so the new relative origin is
  `shiftedRelativeOrigin D u k i = Int.fract (relativeOrigin D k i + u i / side D k)`
  and the new origin is `-(side D k * shiftedRelativeOrigin D u k i)`, keeping the
  exact `(-side, 0]` convention of `Grid.origin_position`.
* The new parent digits are read off by the *existing* binary-digit map
  `DyadicGridLaw.bitInt` of the shifted parent relative origin, so the whole carry
  theory is the already checked `DyadicGridLaw.fract_eq_half`; no new carry
  argument is written here.
* `translate u D` assembles these into a `Grid`, `translate_zero` and
  `translate_translate` make it an action, `measurable_translate` is the joint
  measurability required by `MarkedReRooting.measurable_shift`, and
  `square_carrier_translate` / `square_carrier_translate_symm` identify the
  squares of `translate u D` with the `u`-translates of the squares of `D`, up to
  the explicit integer lattice reindexing `latticeShift`.

No law statement is made here: invariance of `DyadicApproximation.UniformGridLaw`
under this action does **not** follow from the geometry alone and is a separate
obligation.
-/

set_option autoImplicit false

open MeasureTheory Set

namespace ReflectedGMS.DyadicGridTranslation

open ReflectedGMS.DyadicApproximation ReflectedGMS.DyadicGridLaw
open ReflectedGMS.StatementIngredients

/-! ### Relative origins of a grid -/

/-- The position of the grid origin inside its own level-`k` cell, in units of the
side length.  This is the coordinate read by `gridCylinder`. -/
noncomputable def relativeOrigin (D : Grid) (k : ℤ) (i : Fin 2) : ℝ :=
  -D.origin k i / side D k

theorem relativeOrigin_nonneg (D : Grid) (k : ℤ) (i : Fin 2) : 0 ≤ relativeOrigin D k i :=
  div_nonneg (neg_nonneg.2 (D.origin_position k i).2) (side_pos D k).le

theorem relativeOrigin_lt_one (D : Grid) (k : ℤ) (i : Fin 2) : relativeOrigin D k i < 1 := by
  have h := (D.origin_position k i).1
  have hside : side D k = (2 : ℝ) ^ (D.phase + (k : ℝ)) := rfl
  rw [relativeOrigin, div_lt_one (side_pos D k), hside]
  linarith

theorem origin_eq_relativeOrigin (D : Grid) (k : ℤ) (i : Fin 2) :
    D.origin k i = -(side D k * relativeOrigin D k i) := by
  have hne : side D k ≠ 0 := (side_pos D k).ne'
  rw [relativeOrigin]
  field_simp

/-- Successive levels of one grid differ by a factor two. -/
theorem side_succ (D : Grid) (k : ℤ) : side D (k + 1) = 2 * side D k := by
  have h : ((k + 1 : ℤ) : ℝ) - (k : ℝ) = 1 := by push_cast; ring
  rw [DyadicGridLawUniqueness.side_eq_rpow_mul D (k + 1) k, h, Real.rpow_one]

/-- `Grid.compatible` read through the relative origins. -/
theorem two_mul_relativeOrigin_succ (D : Grid) (k : ℤ) (i : Fin 2) :
    2 * relativeOrigin D (k + 1) i = relativeOrigin D k i + ((D.digit k i).val : ℝ) := by
  have hne : side D k ≠ 0 := (side_pos D k).ne'
  have hstep := DyadicGridLawUniqueness.origin_succ D k i
  simp only [relativeOrigin, side_succ, hstep]
  field_simp
  ring

/-! ### The translated coordinates -/

/-- Re-rooting at `u` subtracts `u`, so the relative origin moves by `u / side`.
The exact `(-side, 0]` convention is restored by `Int.fract`. -/
noncomputable def shiftedRelativeOrigin (D : Grid) (u : Plane) (k : ℤ) (i : Fin 2) : ℝ :=
  Int.fract (relativeOrigin D k i + u i / side D k)

theorem shiftedRelativeOrigin_nonneg (D : Grid) (u : Plane) (k : ℤ) (i : Fin 2) :
    0 ≤ shiftedRelativeOrigin D u k i := Int.fract_nonneg _

theorem shiftedRelativeOrigin_lt_one (D : Grid) (u : Plane) (k : ℤ) (i : Fin 2) :
    shiftedRelativeOrigin D u k i < 1 := Int.fract_lt_one _

theorem fract_two_mul_fract (x : ℝ) : Int.fract (2 * Int.fract x) = Int.fract (2 * x) := by
  have h : 2 * Int.fract x = 2 * x - ((2 * ⌊x⌋ : ℤ) : ℝ) := by
    rw [Int.fract]; push_cast; ring
  rw [h, Int.fract_sub_intCast]

/-- The translated relative origins satisfy the same halving recursion as the
untranslated ones: the shift is compatible with passing to the parent level. -/
theorem fract_two_mul_shifted (D : Grid) (u : Plane) (k : ℤ) (i : Fin 2) :
    Int.fract (2 * shiftedRelativeOrigin D u (k + 1) i) = shiftedRelativeOrigin D u k i := by
  have hne : side D k ≠ 0 := (side_pos D k).ne'
  have hu : (2 : ℝ) * (u i / (2 * side D k)) = u i / side D k := by field_simp
  have hr := two_mul_relativeOrigin_succ D k i
  have hkey : 2 * (relativeOrigin D (k + 1) i + u i / side D (k + 1))
      = (relativeOrigin D k i + u i / side D k) + ((D.digit k i).val : ℝ) := by
    rw [side_succ]
    calc 2 * (relativeOrigin D (k + 1) i + u i / (2 * side D k))
        = 2 * relativeOrigin D (k + 1) i + 2 * (u i / (2 * side D k)) := by ring
      _ = (relativeOrigin D k i + ((D.digit k i).val : ℝ)) + u i / side D k := by rw [hr, hu]
      _ = (relativeOrigin D k i + u i / side D k) + ((D.digit k i).val : ℝ) := by ring
  rw [shiftedRelativeOrigin, fract_two_mul_fract, hkey, Int.fract_add_natCast,
    shiftedRelativeOrigin]

/-- The parent digit of the translated grid, read by the existing binary-digit map
`DyadicGridLaw.bitInt` at the shifted parent relative origin. -/
noncomputable def translatedDigit (D : Grid) (u : Plane) (k : ℤ) (i : Fin 2) : Fin 2 :=
  intToFin2 (bitInt (shiftedRelativeOrigin D u (k + 1) i))

theorem intToFin2_val_cast {n : ℤ} (h0 : 0 ≤ n) (h2 : n < 2) :
    (((intToFin2 n).val : ℕ) : ℝ) = (n : ℝ) := by
  have h : n = 0 ∨ n = 1 := by omega
  rcases h with h | h <;> simp [intToFin2, h]

theorem intToFin2_val (d : Fin 2) : intToFin2 ((d.val : ℤ)) = d := by
  fin_cases d <;> rfl

theorem translatedDigit_val (D : Grid) (u : Plane) (k : ℤ) (i : Fin 2) :
    (((translatedDigit D u k i).val : ℕ) : ℝ)
      = (bitInt (shiftedRelativeOrigin D u (k + 1) i) : ℝ) :=
  intToFin2_val_cast (bitInt_nonneg _) (bitInt_lt_two _)

/-- The origin of the translated grid, in the exact `(-side, 0]` convention. -/
noncomputable def translatedOrigin (D : Grid) (u : Plane) (k : ℤ) (i : Fin 2) : ℝ :=
  -(side D k * shiftedRelativeOrigin D u k i)

theorem translatedOrigin_position (D : Grid) (u : Plane) (k : ℤ) (i : Fin 2) :
    -(2 : ℝ) ^ (D.phase + (k : ℝ)) < translatedOrigin D u k i ∧
      translatedOrigin D u k i ≤ 0 := by
  have hs := side_pos D k
  have h0 := shiftedRelativeOrigin_nonneg D u k i
  have h1 := shiftedRelativeOrigin_lt_one D u k i
  have hside : (2 : ℝ) ^ (D.phase + (k : ℝ)) = side D k := rfl
  rw [hside, translatedOrigin]
  constructor
  · nlinarith
  · nlinarith

theorem translatedOrigin_compatible (D : Grid) (u : Plane) (k : ℤ) (i : Fin 2) :
    translatedOrigin D u k i = translatedOrigin D u (k + 1) i +
      (2 : ℝ) ^ (D.phase + (k : ℝ)) * ((translatedDigit D u k i).val : ℝ) := by
  have hside : (2 : ℝ) ^ (D.phase + (k : ℝ)) = side D k := rfl
  have hy : Int.fract (shiftedRelativeOrigin D u (k + 1) i)
      = shiftedRelativeOrigin D u (k + 1) i :=
    Int.fract_eq_self.2 ⟨shiftedRelativeOrigin_nonneg D u (k + 1) i,
      shiftedRelativeOrigin_lt_one D u (k + 1) i⟩
  have hhalf := fract_eq_half (shiftedRelativeOrigin D u (k + 1) i)
  have hstep := fract_two_mul_shifted D u k i
  rw [hy] at hhalf
  have hsub : shiftedRelativeOrigin D u k i
      = 2 * shiftedRelativeOrigin D u (k + 1) i
        - (bitInt (shiftedRelativeOrigin D u (k + 1) i) : ℝ) := by
    rw [← hstep]
    linarith
  rw [hside, translatedOrigin, translatedOrigin, translatedDigit_val, side_succ, hsub]
  ring

/-! ### The translated grid -/

/-- The grid seen from `u`: every square of `D` is translated by `-u`. -/
noncomputable def translate (u : Plane) (D : Grid) : Grid where
  phase := D.phase
  phase_mem := D.phase_mem
  origin := translatedOrigin D u
  digit := translatedDigit D u
  origin_position := translatedOrigin_position D u
  compatible := translatedOrigin_compatible D u

@[simp] theorem translate_phase (u : Plane) (D : Grid) : (translate u D).phase = D.phase := rfl

@[simp] theorem translate_origin (u : Plane) (D : Grid) :
    (translate u D).origin = translatedOrigin D u := rfl

@[simp] theorem translate_digit (u : Plane) (D : Grid) :
    (translate u D).digit = translatedDigit D u := rfl

@[simp] theorem side_translate (u : Plane) (D : Grid) (k : ℤ) :
    side (translate u D) k = side D k := rfl

theorem relativeOrigin_translate (u : Plane) (D : Grid) (k : ℤ) (i : Fin 2) :
    relativeOrigin (translate u D) k i = shiftedRelativeOrigin D u k i := by
  have hne : side D k ≠ 0 := (side_pos D k).ne'
  simp only [relativeOrigin, side_translate, translate_origin, translatedOrigin]
  field_simp

/-- A grid is determined by its coordinate code. -/
theorem grid_ext {D E : Grid} (hp : D.phase = E.phase) (ho : D.origin = E.origin)
    (hd : D.digit = E.digit) : D = E := by
  cases D with
  | mk p hpm o dg hpos hcomp =>
    cases E with
    | mk q hqm o' dg' hpos' hcomp' =>
      dsimp only at hp ho hd
      subst hp
      subst ho
      subst hd
      rfl

@[simp] theorem translate_zero (D : Grid) : translate 0 D = D := by
  have hrel : ∀ (k : ℤ) (i : Fin 2),
      shiftedRelativeOrigin D (0 : Plane) k i = relativeOrigin D k i := by
    intro k i
    have h : ((0 : Plane) i) = 0 := rfl
    simp only [shiftedRelativeOrigin, h, zero_div, add_zero]
    exact Int.fract_eq_self.2 ⟨relativeOrigin_nonneg D k i, relativeOrigin_lt_one D k i⟩
  refine grid_ext rfl (funext fun k => funext fun i => ?_) (funext fun k => funext fun i => ?_)
  · show translatedOrigin D 0 k i = D.origin k i
    rw [translatedOrigin, hrel, ← origin_eq_relativeOrigin]
  · show translatedDigit D 0 k i = D.digit k i
    have hfl : ⌊relativeOrigin D (k + 1) i⌋ = 0 :=
      Int.floor_eq_zero_iff.2 ⟨relativeOrigin_nonneg D (k + 1) i,
        relativeOrigin_lt_one D (k + 1) i⟩
    have hfl2 : ⌊(2 : ℝ) * relativeOrigin D (k + 1) i⌋ = ((D.digit k i).val : ℤ) := by
      rw [two_mul_relativeOrigin_succ, Int.floor_add_natCast,
        Int.floor_eq_zero_iff.2 ⟨relativeOrigin_nonneg D k i, relativeOrigin_lt_one D k i⟩,
        zero_add]
    have hb : bitInt (shiftedRelativeOrigin D (0 : Plane) (k + 1) i) = ((D.digit k i).val : ℤ) := by
      rw [hrel]
      simp only [bitInt, hfl, hfl2]
      ring
    rw [translatedDigit, hb, intToFin2_val]

theorem translate_translate (u v : Plane) (D : Grid) :
    translate v (translate u D) = translate (u + v) D := by
  have hshift : ∀ (k : ℤ) (i : Fin 2),
      shiftedRelativeOrigin (translate u D) v k i = shiftedRelativeOrigin D (u + v) k i := by
    intro k i
    have huv : ((u + v) i) = u i + v i := rfl
    simp only [shiftedRelativeOrigin, relativeOrigin_translate, side_translate, huv]
    rw [Int.fract_fract_add]
    congr 1
    rw [add_div]
    ring
  refine grid_ext rfl (funext fun k => funext fun i => ?_) (funext fun k => funext fun i => ?_)
  · show translatedOrigin (translate u D) v k i = translatedOrigin D (u + v) k i
    simp only [translatedOrigin, side_translate, hshift]
  · show translatedDigit (translate u D) v k i = translatedDigit D (u + v) k i
    simp only [translatedDigit, hshift]

/-! ### The geometric reindexing of the squares -/

/-- The integer lattice translation induced on the level-`k` squares. -/
noncomputable def latticeShift (D : Grid) (u : Plane) (k : ℤ) (i : Fin 2) : ℤ :=
  ⌊relativeOrigin D k i + u i / side D k⌋

/-- The translated origin is the translate of the original origin, corrected by an
integer number of cells. -/
theorem translatedOrigin_eq (D : Grid) (u : Plane) (k : ℤ) (i : Fin 2) :
    translatedOrigin D u k i
      = D.origin k i - u i + side D k * (latticeShift D u k i : ℝ) := by
  have hne : side D k ≠ 0 := (side_pos D k).ne'
  have hfr : Int.fract (relativeOrigin D k i + u i / side D k)
      = (relativeOrigin D k i + u i / side D k) - (latticeShift D u k i : ℝ) :=
    (Int.self_sub_floor _).symm
  have horig := origin_eq_relativeOrigin D k i
  rw [translatedOrigin, shiftedRelativeOrigin, hfr, horig]
  field_simp
  ring

theorem square_lower_translate (D : Grid) (u : Plane) (s : SquareIndex) (i : Fin 2) :
    (square (translate u D) s).lower i
      = (square D (s.1, fun j => s.2 j + latticeShift D u s.1 j)).lower i - u i := by
  simp only [square, side_translate, translate_origin]
  rw [translatedOrigin_eq]
  push_cast
  ring

theorem square_upper_translate (D : Grid) (u : Plane) (s : SquareIndex) (i : Fin 2) :
    (square (translate u D) s).upper i
      = (square D (s.1, fun j => s.2 j + latticeShift D u s.1 j)).upper i - u i := by
  simp only [square, side_translate, translate_origin]
  rw [translatedOrigin_eq]
  push_cast
  ring

/-- Every square of the translated grid is the `u`-translate of a square of the
original grid, with the explicit integer lattice reindexing. -/
theorem square_carrier_translate (D : Grid) (u : Plane) (s : SquareIndex) :
    (square (translate u D) s).carrier
      = (fun z : Plane => z + u) ⁻¹'
          (square D (s.1, fun j => s.2 j + latticeShift D u s.1 j)).carrier := by
  ext z
  have hzu : ∀ i, ((z + u) i) = z i + u i := fun _ => rfl
  simp only [Rectangle.carrier, mem_setOf_eq, mem_preimage, hzu,
    square_lower_translate, square_upper_translate]
  constructor
  · intro h i
    exact ⟨by linarith [(h i).1], by linarith [(h i).2]⟩
  · intro h i
    exact ⟨by linarith [(h i).1], by linarith [(h i).2]⟩

/-! ### Joint measurability -/

theorem measurable_gridPhase : Measurable fun D : Grid => D.phase :=
  measurable_fst.comp measurable_gridCoords

theorem measurable_gridOrigin (k : ℤ) (i : Fin 2) : Measurable fun D : Grid => D.origin k i :=
  (measurable_pi_apply i).comp
    ((measurable_pi_apply k).comp (measurable_fst.comp (measurable_snd.comp measurable_gridCoords)))

theorem measurable_side (k : ℤ) : Measurable fun D : Grid => side D k :=
  (measurable_two_rpow (k : ℝ)).comp measurable_gridPhase

theorem measurable_plane_apply (i : Fin 2) : Measurable fun u : Plane => u i :=
  (measurable_pi_apply i).comp (WithLp.measurable_ofLp 2 (Fin 2 → ℝ))

theorem measurable_relativeOrigin (k : ℤ) (i : Fin 2) :
    Measurable fun D : Grid => relativeOrigin D k i :=
  (measurable_gridOrigin k i).neg.div (measurable_side k)

theorem measurable_shiftedRelativeOrigin (k : ℤ) (i : Fin 2) :
    Measurable fun p : Grid × Plane => shiftedRelativeOrigin p.1 p.2 k i :=
  measurable_fract.comp
    (((measurable_relativeOrigin k i).comp measurable_fst).add
      (((measurable_plane_apply i).comp measurable_snd).div
        ((measurable_side k).comp measurable_fst)))

theorem measurable_translatedOrigin (k : ℤ) (i : Fin 2) :
    Measurable fun p : Grid × Plane => translatedOrigin p.1 p.2 k i :=
  (((measurable_side k).comp measurable_fst).mul
    (measurable_shiftedRelativeOrigin k i)).neg

theorem measurable_translatedDigit (k : ℤ) (i : Fin 2) :
    Measurable fun p : Grid × Plane => translatedDigit p.1 p.2 k i :=
  (measurable_of_countable intToFin2).comp
    (measurable_bitInt.comp (measurable_shiftedRelativeOrigin (k + 1) i))

/-- The re-rooting action on grids is jointly measurable in the grid and the
shift.  This is the measurability datum required by
`MarkedBlockAveraging.MarkedReRooting.measurable_shift`. -/
theorem measurable_translate : Measurable fun p : Grid × Plane => translate p.2 p.1 := by
  have hcomp : Measurable fun p : Grid × Plane =>
      ((translate p.2 p.1).phase, (translate p.2 p.1).origin, (translate p.2 p.1).digit) := by
    refine (measurable_gridPhase.comp measurable_fst).prodMk (Measurable.prodMk ?_ ?_)
    · exact Measurable.of_eval fun k => Measurable.of_eval fun i => measurable_translatedOrigin k i
    · exact Measurable.of_eval fun k => Measurable.of_eval fun i => measurable_translatedDigit k i
  intro s hs
  obtain ⟨t, ht, rfl⟩ := hs
  exact hcomp ht

theorem measurable_translate_left (u : Plane) : Measurable (translate u) :=
  measurable_translate.comp (measurable_id.prodMk measurable_const)

end ReflectedGMS.DyadicGridTranslation
