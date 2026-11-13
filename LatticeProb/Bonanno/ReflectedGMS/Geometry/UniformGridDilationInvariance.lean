/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Geometry.UniformGridDilationInvariance at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Geometry.UniformGridTranslationInvariance
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # The dilation action on dyadic grids and invariance of the uniform grid law

`Spatial.ActualMarkedBlockTransport` needs
`MarkedReRooting.MarkedBlockTransport` for the actual marked configuration space
under `ν.prod gridMeasure`.  The manuscript route feeds the marked block
transport into `EnvironmentLaws.MassTransport`, whose `MassTransportKernel`
covariance field must hold at **every** positive scale, not only for
translations.  Averaging over the grid marks therefore needs invariance of
`DyadicGridLaw.gridMeasure` under a dilation action on
`DyadicApproximation.Grid`, alongside the already checked
`UniformGridTranslationInvariance.map_translate_gridMeasure`.

This file constructs that action and proves exactly those facts.

The geometry.  A `Grid` has side lengths `side D k = 2 ^ (D.phase + k)` with
`D.phase ∈ [0,1)`.  Scaling the whole picture by `s > 0` sends this to
`2 ^ (logb 2 s + D.phase + k)`, which is again of the prescribed form only after
splitting `D.phase + logb 2 s` into its fractional and integer parts.  So a
dilation is **not** a phase rotation alone: it is a phase rotation

  `dilatedPhase s D = Int.fract (D.phase + logb 2 s)`

*together with* the integer level reindexing by

  `levelShift s D = ⌊D.phase + logb 2 s⌋`,

and the reindexing genuinely depends on the grid, through its phase.  The level
`k` data of `dilate s hs D` is the scaled level `k - levelShift s D` data of `D`
(`dilate`, `side_dilate`, `square_carrier_dilate`), so every dyadic square of the
dilated grid is the `s`-dilate of a square of the original grid.

The law.  Because only the phase moves and the origin/digit data is merely
reindexed, the level-`k` depth-`n` cylinder of `dilate s hs D` is the level
`k - levelShift s D` cylinder of `D` with its phase rotated by `logb 2 s` modulo
one (`gridCylinder_dilate`).  Since `D.phase ∈ [0,1)`, `levelShift s D` takes only
the two values `⌊logb 2 s⌋` and `⌊logb 2 s⌋ + 1` (`levelShift_eq_ite`), split by
the measurable set `{D | D.phase + Int.fract (logb 2 s) < 1}`.  On each of the two
pieces the dilated cylinder is a *fixed* level cylinder of `D` composed with the
circle rotation `dilateCyl`, whose law invariance is the already checked
`UniformGridTranslationInvariance.map_fract_add_unitMeasure`.  Adding the two
pieces back up gives `uniformGridLaw_map_dilate` and hence
`map_dilate_gridMeasure`.

No invariant mark law is assumed anywhere: invariance is derived from the actual
cylinder law of the construction, exactly as in the translation file.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open MeasureTheory Set

namespace ReflectedGMS.UniformGridDilationInvariance

open ReflectedGMS.DyadicApproximation ReflectedGMS.DyadicGridLaw
open ReflectedGMS.DyadicGridLawUniqueness ReflectedGMS.DyadicGridTranslation
open ReflectedGMS.UniformGridTranslationInvariance ReflectedGMS.StatementIngredients

/-! ### The phase rotation and the integer level reindexing -/

/-- The phase of the grid dilated by `s`: the old phase rotated by `logb 2 s`
modulo one. -/
noncomputable def dilatedPhase (s : ℝ) (D : Grid) : ℝ :=
  Int.fract (D.phase + Real.logb 2 s)

/-- The integer level reindexing caused by dilating by `s`.  It depends on the
grid through its phase, and is *not* constant in `D`: this is the part of a
dilation that a phase rotation alone cannot produce. -/
noncomputable def levelShift (s : ℝ) (D : Grid) : ℤ :=
  ⌊D.phase + Real.logb 2 s⌋

theorem dilatedPhase_nonneg (s : ℝ) (D : Grid) : 0 ≤ dilatedPhase s D :=
  Int.fract_nonneg _

theorem dilatedPhase_lt_one (s : ℝ) (D : Grid) : dilatedPhase s D < 1 :=
  Int.fract_lt_one _

/-- The scaled side lengths are again of the form prescribed by `Grid`, at the
reindexed level.  This is the single computation behind the whole construction. -/
theorem mul_side {s : ℝ} (hs : 0 < s) (D : Grid) (l : ℤ) :
    s * side D l = (2 : ℝ) ^ (dilatedPhase s D + ((l + levelShift s D : ℤ) : ℝ)) := by
  have h2 : (2 : ℝ) ^ Real.logb 2 s = s :=
    Real.rpow_logb (by norm_num) (by norm_num) hs
  have hfl : ((⌊D.phase + Real.logb 2 s⌋ : ℤ) : ℝ) + Int.fract (D.phase + Real.logb 2 s)
      = D.phase + Real.logb 2 s := Int.floor_add_fract _
  have hside : side D l = (2 : ℝ) ^ (D.phase + (l : ℝ)) := rfl
  have hexp : Real.logb 2 s + (D.phase + (l : ℝ))
      = dilatedPhase s D + ((l + levelShift s D : ℤ) : ℝ) := by
    simp only [dilatedPhase, levelShift]
    push_cast
    linarith
  calc s * side D l = (2 : ℝ) ^ Real.logb 2 s * (2 : ℝ) ^ (D.phase + (l : ℝ)) := by
        rw [h2, hside]
    _ = (2 : ℝ) ^ (Real.logb 2 s + (D.phase + (l : ℝ))) :=
        (Real.rpow_add (by norm_num : (0 : ℝ) < 2) _ _).symm
    _ = (2 : ℝ) ^ (dilatedPhase s D + ((l + levelShift s D : ℤ) : ℝ)) := by rw [hexp]

/-- The scaled side length at the reindexed level is the side length of the
dilated grid at level `k`. -/
theorem mul_side_sub {s : ℝ} (hs : 0 < s) (D : Grid) (k : ℤ) :
    s * side D (k - levelShift s D) = (2 : ℝ) ^ (dilatedPhase s D + (k : ℝ)) := by
  rw [mul_side hs D (k - levelShift s D)]
  congr 1
  push_cast
  ring

/-! ### The dilated coordinates -/

/-- The origin of the dilated grid at level `k`: the scaled origin of the
original grid at the reindexed level. -/
noncomputable def dilatedOrigin (s : ℝ) (D : Grid) (k : ℤ) (i : Fin 2) : ℝ :=
  s * D.origin (k - levelShift s D) i

/-- The parent digits are merely reindexed: dilating does not change which parent
half a square sits in. -/
noncomputable def dilatedDigit (s : ℝ) (D : Grid) (k : ℤ) (i : Fin 2) : Fin 2 :=
  D.digit (k - levelShift s D) i

theorem dilatedOrigin_position {s : ℝ} (hs : 0 < s) (D : Grid) (k : ℤ) (i : Fin 2) :
    -(2 : ℝ) ^ (dilatedPhase s D + (k : ℝ)) < dilatedOrigin s D k i
      ∧ dilatedOrigin s D k i ≤ 0 := by
  obtain ⟨h1, h2⟩ := D.origin_position (k - levelShift s D) i
  have hside : side D (k - levelShift s D)
      = (2 : ℝ) ^ (D.phase + ((k - levelShift s D : ℤ) : ℝ)) := rfl
  have hmul := mul_side_sub hs D k
  rw [hside] at hmul
  constructor
  · have hlt := mul_lt_mul_of_pos_left h1 hs
    rw [← hmul]
    show -(s * (2 : ℝ) ^ (D.phase + ((k - levelShift s D : ℤ) : ℝ)))
      < s * D.origin (k - levelShift s D) i
    linarith
  · have := mul_le_mul_of_nonneg_left h2 hs.le
    simpa [dilatedOrigin] using this

theorem dilatedOrigin_compatible {s : ℝ} (hs : 0 < s) (D : Grid) (k : ℤ) (i : Fin 2) :
    dilatedOrigin s D k i = dilatedOrigin s D (k + 1) i
      + (2 : ℝ) ^ (dilatedPhase s D + (k : ℝ)) * ((dilatedDigit s D k i).val : ℝ) := by
  have hcomp := D.compatible (k - levelShift s D) i
  have hidx : k + 1 - levelShift s D = (k - levelShift s D) + 1 := by ring
  have hmul := mul_side_sub hs D k
  have hside : side D (k - levelShift s D)
      = (2 : ℝ) ^ (D.phase + ((k - levelShift s D : ℤ) : ℝ)) := rfl
  show s * D.origin (k - levelShift s D) i
      = s * D.origin (k + 1 - levelShift s D) i
        + (2 : ℝ) ^ (dilatedPhase s D + (k : ℝ)) * ((D.digit (k - levelShift s D) i).val : ℝ)
  rw [hidx, hcomp, ← hmul, hside]
  ring

/-! ### The dilated grid -/

/-- The grid scaled by the positive factor `s`: every square of `D` is dilated by
`s`, which rotates the phase and reindexes the levels by `levelShift s D`. -/
noncomputable def dilate (s : ℝ) (hs : 0 < s) (D : Grid) : Grid where
  phase := dilatedPhase s D
  phase_mem := Set.mem_Ico.2 ⟨dilatedPhase_nonneg s D, dilatedPhase_lt_one s D⟩
  origin := dilatedOrigin s D
  digit := dilatedDigit s D
  origin_position := dilatedOrigin_position hs D
  compatible := dilatedOrigin_compatible hs D

@[simp] theorem dilate_phase (s : ℝ) (hs : 0 < s) (D : Grid) :
    (dilate s hs D).phase = dilatedPhase s D := rfl

@[simp] theorem dilate_origin (s : ℝ) (hs : 0 < s) (D : Grid) :
    (dilate s hs D).origin = dilatedOrigin s D := rfl

@[simp] theorem dilate_digit (s : ℝ) (hs : 0 < s) (D : Grid) :
    (dilate s hs D).digit = dilatedDigit s D := rfl

/-- **The side lengths scale exactly.**  The level-`k` side of the dilated grid is
`s` times the side of the original grid at the reindexed level. -/
theorem side_dilate {s : ℝ} (hs : 0 < s) (D : Grid) (k : ℤ) :
    side (dilate s hs D) k = s * side D (k - levelShift s D) :=
  (mul_side_sub hs D k).symm

/-- Dilating by `1` is the identity. -/
theorem dilate_one (D : Grid) : dilate 1 one_pos D = D := by
  have hlog : Real.logb 2 (1 : ℝ) = 0 := Real.logb_one
  have hlev : levelShift 1 D = 0 := by
    simp only [levelShift, hlog, add_zero]
    exact Int.floor_eq_zero_iff.2 D.phase_mem
  refine grid_ext ?_ (funext fun k => funext fun i => ?_) (funext fun k => funext fun i => ?_)
  · show Int.fract (D.phase + Real.logb 2 1) = D.phase
    rw [hlog, add_zero]
    exact Int.fract_eq_self.2 D.phase_mem
  · show (1 : ℝ) * D.origin (k - levelShift 1 D) i = D.origin k i
    rw [hlev, one_mul, sub_zero]
  · show D.digit (k - levelShift 1 D) i = D.digit k i
    rw [hlev, sub_zero]

/-! ### Dyadic square compatibility -/

theorem square_lower_dilate {s : ℝ} (hs : 0 < s) (D : Grid) (c : SquareIndex) (i : Fin 2) :
    (square (dilate s hs D) c).lower i
      = s * (square D (c.1 - levelShift s D, c.2)).lower i := by
  have horig : (dilate s hs D).origin c.1 i = s * D.origin (c.1 - levelShift s D) i := rfl
  show (dilate s hs D).origin c.1 i + side (dilate s hs D) c.1 * ((c.2 i : ℤ) : ℝ)
      = s * (D.origin (c.1 - levelShift s D) i
          + side D (c.1 - levelShift s D) * ((c.2 i : ℤ) : ℝ))
  rw [horig, side_dilate hs D c.1]
  ring

theorem square_upper_dilate {s : ℝ} (hs : 0 < s) (D : Grid) (c : SquareIndex) (i : Fin 2) :
    (square (dilate s hs D) c).upper i
      = s * (square D (c.1 - levelShift s D, c.2)).upper i := by
  have horig : (dilate s hs D).origin c.1 i = s * D.origin (c.1 - levelShift s D) i := rfl
  show (dilate s hs D).origin c.1 i + side (dilate s hs D) c.1 * ((c.2 i : ℤ) : ℝ)
        + side (dilate s hs D) c.1
      = s * (D.origin (c.1 - levelShift s D) i
          + side D (c.1 - levelShift s D) * ((c.2 i : ℤ) : ℝ)
          + side D (c.1 - levelShift s D))
  rw [horig, side_dilate hs D c.1]
  ring

/-- **Exact dyadic square compatibility.**  A point lies in a square of the
original grid exactly when its `s`-dilate lies in the correspondingly reindexed
square of the dilated grid. -/
theorem smul_preimage_square_carrier_dilate {s : ℝ} (hs : 0 < s) (D : Grid) (c : SquareIndex) :
    (fun z : Plane => s • z) ⁻¹' (square (dilate s hs D) c).carrier
      = (square D (c.1 - levelShift s D, c.2)).carrier := by
  ext z
  have hz : ∀ i, ((s • z) i) = s * z i := fun _ => rfl
  simp only [Set.mem_preimage, Rectangle.carrier, Set.mem_setOf_eq, hz,
    square_lower_dilate hs D c, square_upper_dilate hs D c]
  constructor
  · intro h i
    exact ⟨le_of_mul_le_mul_left (h i).1 hs, le_of_mul_le_mul_left (h i).2 hs⟩
  · intro h i
    exact ⟨mul_le_mul_of_nonneg_left (h i).1 hs.le,
      mul_le_mul_of_nonneg_left (h i).2 hs.le⟩

/-- Every square of the dilated grid is the `s`-dilate of a square of the original
grid, with the explicit level reindexing.  This is the dilation analogue of
`DyadicGridTranslation.square_carrier_translate`. -/
theorem square_carrier_dilate {s : ℝ} (hs : 0 < s) (D : Grid) (c : SquareIndex) :
    (square (dilate s hs D) c).carrier
      = (fun z : Plane => s⁻¹ • z) ⁻¹' (square D (c.1 - levelShift s D, c.2)).carrier := by
  rw [← smul_preimage_square_carrier_dilate hs D c]
  ext z
  simp only [Set.mem_preimage]
  rw [smul_inv_smul₀ hs.ne']

/-! ### Cylinder compatibility -/

theorem relativeOrigin_dilate {s : ℝ} (hs : 0 < s) (D : Grid) (k : ℤ) (i : Fin 2) :
    relativeOrigin (dilate s hs D) k i = relativeOrigin D (k - levelShift s D) i := by
  have horig : (dilate s hs D).origin k i = s * D.origin (k - levelShift s D) i := rfl
  show -(dilate s hs D).origin k i / side (dilate s hs D) k
      = -D.origin (k - levelShift s D) i / side D (k - levelShift s D)
  rw [horig, side_dilate hs D k,
    show -(s * D.origin (k - levelShift s D) i)
        = s * -D.origin (k - levelShift s D) i by ring,
    mul_div_mul_left _ _ hs.ne']

/-- The circle rotation induced on cylinder data by a dilation: only the phase
coordinate moves. -/
noncomputable def dilateCyl (s : ℝ) (n : ℕ) (c : Cyl n) : Cyl n :=
  (Int.fract (c.1 + Real.logb 2 s), c.2)

theorem measurable_dilateCyl (s : ℝ) (n : ℕ) : Measurable (dilateCyl s n) :=
  (measurable_fract.comp (measurable_fst.add_const _)).prodMk measurable_snd

/-- **The cylinder of a dilated grid.**  The level-`k` depth-`n` cylinder of
`dilate s hs D` is the level `k - levelShift s D` depth-`n` cylinder of `D` with
its phase rotated by `logb 2 s` modulo one.  Both the reindexing and the rotation
are genuinely present. -/
theorem gridCylinder_dilate {s : ℝ} (hs : 0 < s) (k : ℤ) (n : ℕ) (D : Grid) :
    gridCylinder k n (dilate s hs D)
      = dilateCyl s n (gridCylinder (k - levelShift s D) n D) := by
  have hA : (fun i : Fin 2 => relativeOrigin (dilate s hs D) k i)
      = fun i : Fin 2 => relativeOrigin D (k - levelShift s D) i :=
    funext fun i => relativeOrigin_dilate hs D k i
  have hB : (fun (j : Fin n) (i : Fin 2) => (dilate s hs D).digit (k + (j.val : ℤ)) i)
      = fun (j : Fin n) (i : Fin 2) =>
          D.digit ((k - levelShift s D) + (j.val : ℤ)) i := by
    funext j i
    show D.digit (k + (j.val : ℤ) - levelShift s D) i
      = D.digit ((k - levelShift s D) + (j.val : ℤ)) i
    congr 1
    ring
  show ((dilate s hs D).phase,
      (fun i : Fin 2 => relativeOrigin (dilate s hs D) k i,
        fun (j : Fin n) (i : Fin 2) => (dilate s hs D).digit (k + (j.val : ℤ)) i))
    = dilateCyl s n (gridCylinder (k - levelShift s D) n D)
  rw [hA, hB]
  rfl

/-! ### Measurability of the dilation -/

theorem measurable_gridDigit (k : ℤ) (i : Fin 2) : Measurable fun D : Grid => D.digit k i :=
  (measurable_pi_apply i).comp
    ((measurable_pi_apply k).comp (measurable_snd.comp (measurable_snd.comp measurable_gridCoords)))

theorem measurableSet_phaseLow (s : ℝ) :
    MeasurableSet {D : Grid | D.phase + Int.fract (Real.logb 2 s) < 1} :=
  measurableSet_lt (measurable_gridPhase.add_const _) measurable_const

/-- Since `D.phase ∈ [0,1)`, the level reindexing takes exactly two values, split
by a measurable set of grids.  This is what makes the dilation measurable and what
reduces its law to two fixed-level cylinder laws. -/
theorem levelShift_eq_ite (s : ℝ) (D : Grid) :
    levelShift s D
      = if D.phase + Int.fract (Real.logb 2 s) < 1 then ⌊Real.logb 2 s⌋
        else ⌊Real.logb 2 s⌋ + 1 := by
  have hp0 : 0 ≤ D.phase := (Set.mem_Ico.1 D.phase_mem).1
  have hp1 : D.phase < 1 := (Set.mem_Ico.1 D.phase_mem).2
  have hf0 : 0 ≤ Int.fract (Real.logb 2 s) := Int.fract_nonneg _
  have hf1 : Int.fract (Real.logb 2 s) < 1 := Int.fract_lt_one _
  have hsplit : D.phase + Real.logb 2 s
      = (D.phase + Int.fract (Real.logb 2 s)) + ((⌊Real.logb 2 s⌋ : ℤ) : ℝ) := by
    have := Int.floor_add_fract (Real.logb 2 s)
    linarith
  rw [levelShift, hsplit, Int.floor_add_intCast]
  by_cases hc : D.phase + Int.fract (Real.logb 2 s) < 1
  · rw [if_pos hc, Int.floor_eq_zero_iff.2 (Set.mem_Ico.2 ⟨by linarith, hc⟩), zero_add]
  · rw [if_neg hc]
    have h1 : ((1 : ℤ) : ℝ) ≤ D.phase + Int.fract (Real.logb 2 s) := by
      push_cast
      linarith [not_lt.1 hc]
    have h2 : D.phase + Int.fract (Real.logb 2 s) < ((1 : ℤ) : ℝ) + 1 := by
      push_cast
      linarith
    rw [Int.floor_eq_iff.2 ⟨h1, h2⟩]
    ring

theorem measurable_dilatedPhase (s : ℝ) : Measurable fun D : Grid => dilatedPhase s D :=
  measurable_fract.comp (measurable_gridPhase.add_const _)

theorem measurable_dilatedOrigin (s : ℝ) (k : ℤ) (i : Fin 2) :
    Measurable fun D : Grid => dilatedOrigin s D k i := by
  have h : (fun D : Grid => dilatedOrigin s D k i)
      = fun D : Grid => if D.phase + Int.fract (Real.logb 2 s) < 1
          then s * D.origin (k - ⌊Real.logb 2 s⌋) i
          else s * D.origin (k - (⌊Real.logb 2 s⌋ + 1)) i := by
    funext D
    rw [dilatedOrigin, levelShift_eq_ite]
    by_cases hc : D.phase + Int.fract (Real.logb 2 s) < 1 <;> simp [hc]
  rw [h]
  exact Measurable.ite (measurableSet_phaseLow s)
    (measurable_const.mul (measurable_gridOrigin _ i))
    (measurable_const.mul (measurable_gridOrigin _ i))

theorem measurable_dilatedDigit (s : ℝ) (k : ℤ) (i : Fin 2) :
    Measurable fun D : Grid => dilatedDigit s D k i := by
  have h : (fun D : Grid => dilatedDigit s D k i)
      = fun D : Grid => if D.phase + Int.fract (Real.logb 2 s) < 1
          then D.digit (k - ⌊Real.logb 2 s⌋) i
          else D.digit (k - (⌊Real.logb 2 s⌋ + 1)) i := by
    funext D
    rw [dilatedDigit, levelShift_eq_ite]
    by_cases hc : D.phase + Int.fract (Real.logb 2 s) < 1 <;> simp [hc]
  rw [h]
  exact Measurable.ite (measurableSet_phaseLow s)
    (measurable_gridDigit _ i) (measurable_gridDigit _ i)

/-- The dilation action is measurable on grids. -/
theorem measurable_dilate (s : ℝ) (hs : 0 < s) : Measurable (dilate s hs) := by
  have hcomp : Measurable fun D : Grid =>
      ((dilate s hs D).phase, (dilate s hs D).origin, (dilate s hs D).digit) := by
    refine (measurable_dilatedPhase s).prodMk (Measurable.prodMk ?_ ?_)
    · exact Measurable.of_eval fun k => Measurable.of_eval fun i => measurable_dilatedOrigin s k i
    · exact Measurable.of_eval fun k => Measurable.of_eval fun i => measurable_dilatedDigit s k i
  intro u hu
  obtain ⟨t, ht, rfl⟩ := hu
  exact hcomp ht

/-! ### The cylinder rotation preserves the cylinder law -/

/-- The cylinder-level dilation map is the circle rotation of the phase, with the
origin/digit data untouched, so it preserves the prescribed cylinder law by the
already checked `map_fract_add_unitMeasure`. -/
theorem measurePreserving_dilateCyl (s : ℝ) (n : ℕ) :
    MeasurePreserving (dilateCyl s n) (cylinderTarget n) (cylinderTarget n) := by
  have := isProbabilityMeasure_unitMeasure
  have h1 : MeasurePreserving (fun x : ℝ => Int.fract (x + Real.logb 2 s))
      unitMeasure unitMeasure :=
    ⟨measurable_fract.comp (measurable_id.add_const _), map_fract_add_unitMeasure _⟩
  have h2 := h1.prod (MeasurePreserving.id (innerTarget n))
  have hfun : dilateCyl s n
      = Prod.map (fun x : ℝ => Int.fract (x + Real.logb 2 s)) (id : _ → _) := rfl
  rw [cylinderTarget, hfun]
  exact h2

/-! ### The two-piece decomposition of the dilated cylinder -/

theorem preimage_inter_phaseLow {s : ℝ} (hs : 0 < s) (k : ℤ) (n : ℕ) (S : Set (Cyl n)) :
    ((gridCylinder k n ∘ dilate s hs) ⁻¹' S)
        ∩ {D : Grid | D.phase + Int.fract (Real.logb 2 s) < 1}
      = (gridCylinder (k - ⌊Real.logb 2 s⌋) n) ⁻¹'
          ((dilateCyl s n ⁻¹' S) ∩ {q : Cyl n | q.1 + Int.fract (Real.logb 2 s) < 1}) := by
  ext D
  constructor
  · intro hD
    obtain ⟨h1, h2⟩ := hD
    have h2' : D.phase + Int.fract (Real.logb 2 s) < 1 := h2
    have hlev : levelShift s D = ⌊Real.logb 2 s⌋ := by
      rw [levelShift_eq_ite, if_pos h2']
    refine ⟨?_, h2⟩
    show dilateCyl s n (gridCylinder (k - ⌊Real.logb 2 s⌋) n D) ∈ S
    rw [← hlev, ← gridCylinder_dilate hs k n D]
    exact h1
  · intro hD
    obtain ⟨h1, h2⟩ := hD
    have h2' : D.phase + Int.fract (Real.logb 2 s) < 1 := h2
    have hlev : levelShift s D = ⌊Real.logb 2 s⌋ := by
      rw [levelShift_eq_ite, if_pos h2']
    refine ⟨?_, h2'⟩
    show gridCylinder k n (dilate s hs D) ∈ S
    rw [gridCylinder_dilate hs k n D, hlev]
    exact h1

theorem preimage_sdiff_phaseLow {s : ℝ} (hs : 0 < s) (k : ℤ) (n : ℕ) (S : Set (Cyl n)) :
    ((gridCylinder k n ∘ dilate s hs) ⁻¹' S)
        \ {D : Grid | D.phase + Int.fract (Real.logb 2 s) < 1}
      = (gridCylinder (k - (⌊Real.logb 2 s⌋ + 1)) n) ⁻¹'
          ((dilateCyl s n ⁻¹' S) \ {q : Cyl n | q.1 + Int.fract (Real.logb 2 s) < 1}) := by
  ext D
  constructor
  · intro hD
    obtain ⟨h1, h2⟩ := hD
    have h2' : ¬ (D.phase + Int.fract (Real.logb 2 s) < 1) := h2
    have hlev : levelShift s D = ⌊Real.logb 2 s⌋ + 1 := by
      rw [levelShift_eq_ite, if_neg h2']
    refine ⟨?_, h2⟩
    show dilateCyl s n (gridCylinder (k - (⌊Real.logb 2 s⌋ + 1)) n D) ∈ S
    rw [← hlev, ← gridCylinder_dilate hs k n D]
    exact h1
  · intro hD
    obtain ⟨h1, h2⟩ := hD
    have h2' : ¬ (D.phase + Int.fract (Real.logb 2 s) < 1) := h2
    have hlev : levelShift s D = ⌊Real.logb 2 s⌋ + 1 := by
      rw [levelShift_eq_ite, if_neg h2']
    refine ⟨?_, h2'⟩
    show gridCylinder k n (dilate s hs D) ∈ S
    rw [gridCylinder_dilate hs k n D, hlev]
    exact h1

/-! ### Dilation invariance of the law -/

/-- Dilating a uniform random dyadic grid gives a uniform random dyadic grid.
Every finite cylinder law is preserved; the grid-dependent level reindexing is
handled by splitting along the two values it takes. -/
theorem uniformGridLaw_map_dilate {ν : Measure Grid} (h : UniformGridLaw ν)
    {s : ℝ} (hs : 0 < s) : UniformGridLaw (Measure.map (dilate s hs) ν) := by
  have hprob := h.1
  refine ⟨inferInstance, fun k n => ?_⟩
  have hmm : Measure.map (gridCylinder k n) (Measure.map (dilate s hs) ν)
      = Measure.map (gridCylinder k n ∘ dilate s hs) ν :=
    Measure.map_map (ReflectedGMS.DyadicGridLaw.measurable_gridCylinder k n)
      (measurable_dilate s hs)
  rw [hmm, ← cylinderTarget_eq]
  refine Measure.ext fun S hS => ?_
  have hAmeas : MeasurableSet {q : Cyl n | q.1 + Int.fract (Real.logb 2 s) < 1} :=
    measurableSet_lt (measurable_fst.add_const _) measurable_const
  have hTmeas : MeasurableSet (dilateCyl s n ⁻¹' S) := measurable_dilateCyl s n hS
  have hcompmeas : Measurable (gridCylinder k n ∘ dilate s hs) :=
    (ReflectedGMS.DyadicGridLaw.measurable_gridCylinder k n).comp (measurable_dilate s hs)
  have hlaw : ∀ (l : ℤ) (U : Set (Cyl n)), MeasurableSet U →
      ν ((gridCylinder l n) ⁻¹' U) = cylinderTarget n U := by
    intro l U hU
    rw [← Measure.map_apply (ReflectedGMS.DyadicGridLaw.measurable_gridCylinder l n) hU,
      h.2 l n, ← cylinderTarget_eq]
  calc Measure.map (gridCylinder k n ∘ dilate s hs) ν S
      = ν ((gridCylinder k n ∘ dilate s hs) ⁻¹' S) := Measure.map_apply hcompmeas hS
    _ = ν (((gridCylinder k n ∘ dilate s hs) ⁻¹' S)
            ∩ {D : Grid | D.phase + Int.fract (Real.logb 2 s) < 1})
        + ν (((gridCylinder k n ∘ dilate s hs) ⁻¹' S)
            \ {D : Grid | D.phase + Int.fract (Real.logb 2 s) < 1}) :=
        (measure_inter_add_sdiff _ (measurableSet_phaseLow s)).symm
    _ = cylinderTarget n ((dilateCyl s n ⁻¹' S)
            ∩ {q : Cyl n | q.1 + Int.fract (Real.logb 2 s) < 1})
        + cylinderTarget n ((dilateCyl s n ⁻¹' S)
            \ {q : Cyl n | q.1 + Int.fract (Real.logb 2 s) < 1}) := by
        rw [preimage_inter_phaseLow hs k n S, preimage_sdiff_phaseLow hs k n S,
          hlaw _ _ (hTmeas.inter hAmeas), hlaw _ _ (hTmeas.diff hAmeas)]
    _ = cylinderTarget n (dilateCyl s n ⁻¹' S) := measure_inter_add_sdiff _ hAmeas
    _ = cylinderTarget n S := by
        rw [← Measure.map_apply (measurable_dilateCyl s n) hS,
          (measurePreserving_dilateCyl s n).map_eq]

/-- **Dilation invariance of the uniform dyadic grid law.**  Any measure realising
`DyadicApproximation.UniformGridLaw` is invariant under the dilation action. -/
theorem map_dilate_of_uniformGridLaw {ν : Measure Grid} (h : UniformGridLaw ν)
    {s : ℝ} (hs : 0 < s) : Measure.map (dilate s hs) ν = ν :=
  DyadicGridLawUniqueness.eq_of_uniformGridLaw (uniformGridLaw_map_dilate h hs) h

/-- **The mark-law input at every positive scale.**  The constructed independent
grid law `DyadicGridLaw.gridMeasure` is invariant under dilation by every positive
factor.  Together with
`UniformGridTranslationInvariance.map_translate_gridMeasure` this is the mark-law
covariance needed by `MassTransportKernel`. -/
theorem map_dilate_gridMeasure {s : ℝ} (hs : 0 < s) :
    Measure.map (dilate s hs) gridMeasure = gridMeasure :=
  map_dilate_of_uniformGridLaw DyadicCylinderLaw.uniformGridLaw_gridMeasure hs

end ReflectedGMS.UniformGridDilationInvariance
