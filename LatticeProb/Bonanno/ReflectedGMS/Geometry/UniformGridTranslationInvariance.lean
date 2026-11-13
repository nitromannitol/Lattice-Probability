/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Geometry.UniformGridTranslationInvariance at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Geometry.DyadicGridTranslation
import LatticeProb.Bonanno.ReflectedGMS.Forms.DyadicCylinderLaw
import Mathlib.MeasureTheory.Group.Measure

/-! # Translation invariance of the uniform random dyadic grid law

`DyadicGridTranslation.translate` re-roots a `DyadicApproximation.Grid` at a point
`u` of the plane.  The mark-law input needed by the manuscript lemmas
`s:lem:conditional` and `s:lem:redistribution` is that the *actual* independent
grid law is invariant under this action: re-rooting a uniform random dyadic grid
gives again a uniform random dyadic grid.  Nothing here assumes an invariant mark
law, and no independence of the translated digits is assumed; it is proved.

The route is the already checked cylinder theory.

* By `DyadicGridLawUniqueness.eq_of_uniformGridLaw` it suffices to show that
  `Measure.map (translate u) ν` again satisfies
  `DyadicApproximation.UniformGridLaw` whenever `ν` does, i.e. to prove the
  invariance of every *finite* cylinder law.
* The level-`k` depth-`n` cylinder of `translate u D` is an explicit measurable
  function `translateCyl u k n` of the level-`k` depth-`n` cylinder of `D`
  (`gridCylinder_translate`); no deeper data is needed, because the translated
  relative origins satisfy the same halving recursion
  (`DyadicGridTranslation.fract_two_mul_shifted`).
* The key to the law is the *coarser relative-origin coordinate*: gluing the
  level-`k` relative origin with the `n` digits above it, via the existing
  `DyadicCylinderLaw.glueDigits`, produces the relative origin at the coarse level
  `k + n` (`glueDigits_relativeOrigin`).  In that single coordinate re-rooting is
  the rotation `x ↦ Int.fract (x + c)` of the circle, which preserves the uniform
  law on `[0, 1)` (`map_fract_add_unitMeasure`).  Re-expanding by
  `DyadicFiniteBitLaw.shiftBits` returns a uniform remainder together with
  independent fair digits, so the translated origin and the translated digits are
  *jointly* uniform rather than assumed so.
* The phase is untouched by re-rooting but enters the rotation amount, so the
  cylinder map is a skew product over the phase; `MeasurePreserving.skew_product`
  assembles it.

The resulting `map_translate_gridMeasure` is the exact mark-law statement
`Measure.map (translate u) gridMeasure = gridMeasure` for the constructed law
`DyadicGridLaw.gridMeasure`.  Positive dilations are a separate obligation and are
not claimed here.
-/

set_option autoImplicit false

open MeasureTheory Set

namespace ReflectedGMS.UniformGridTranslationInvariance

open ReflectedGMS.DyadicApproximation ReflectedGMS.DyadicGridLaw ReflectedGMS.DyadicDigitLaw
open ReflectedGMS.DyadicFiniteBitLaw ReflectedGMS.DyadicCylinderLaw
open ReflectedGMS.DyadicGridLawUniqueness ReflectedGMS.DyadicGridTranslation

/-! ### Rotation invariance of the uniform law on the unit interval -/

theorem fract_add_eq_fract_add_fract (x c : ℝ) :
    Int.fract (x + c) = Int.fract (x + Int.fract c) := by
  have h : x + c = (x + Int.fract c) + ((⌊c⌋ : ℤ) : ℝ) := by
    rw [Int.fract]; ring
  rw [h, Int.fract_add_intCast]

/-- Rotation by an amount in `[0, 1)` preserves the uniform law on `[0, 1)`.  The map
is the identity translation on `[0, 1 - a)` and the translation by `a - 1` on
`[1 - a, 1)`, and the two images tile `[0, 1)`. -/
theorem map_fract_add_unitMeasure_of_mem_Ico {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) :
    Measure.map (fun x : ℝ => Int.fract (x + a)) unitMeasure = unitMeasure := by
  have hmeas : Measurable fun x : ℝ => Int.fract (x + a) :=
    measurable_fract.comp (measurable_id.add_const a)
  have hadd : Measurable fun x : ℝ => x + a := measurable_id.add_const a
  have hadd' : Measurable fun x : ℝ => x + (a - 1) := measurable_id.add_const (a - 1)
  have hsplit : unitMeasure = volume.restrict (Set.Ico (0 : ℝ) (1 - a))
      + volume.restrict (Set.Ico (1 - a) 1) := by
    rw [unitMeasure, ← Measure.restrict_union Set.Ico_disjoint_Ico_same measurableSet_Ico,
      Set.Ico_union_Ico_eq_Ico (by linarith) (by linarith)]
  have h1 : Measure.map (fun x : ℝ => Int.fract (x + a))
        (volume.restrict (Set.Ico (0 : ℝ) (1 - a)))
      = volume.restrict (Set.Ico a 1) := by
    have hcong : Measure.map (fun x : ℝ => Int.fract (x + a))
          (volume.restrict (Set.Ico (0 : ℝ) (1 - a)))
        = Measure.map (fun x : ℝ => x + a) (volume.restrict (Set.Ico (0 : ℝ) (1 - a))) := by
      refine Measure.map_congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
      exact Int.fract_eq_self.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hpre : Set.Ico (0 : ℝ) (1 - a) = (fun x : ℝ => x + a) ⁻¹' Set.Ico a 1 := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Ico]
      constructor
      · intro h; exact ⟨by linarith [h.1], by linarith [h.2]⟩
      · intro h; exact ⟨by linarith [h.1], by linarith [h.2]⟩
    rw [hcong, hpre, ← Measure.restrict_map hadd measurableSet_Ico, map_add_right_eq_self]
  have h2 : Measure.map (fun x : ℝ => Int.fract (x + a))
        (volume.restrict (Set.Ico (1 - a) 1))
      = volume.restrict (Set.Ico (0 : ℝ) a) := by
    have hcong : Measure.map (fun x : ℝ => Int.fract (x + a))
          (volume.restrict (Set.Ico (1 - a) 1))
        = Measure.map (fun x : ℝ => x + (a - 1)) (volume.restrict (Set.Ico (1 - a) 1)) := by
      refine Measure.map_congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
      have hfl : ⌊x + a⌋ = 1 := by
        rw [Int.floor_eq_iff]
        push_cast
        exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
      rw [Int.fract, hfl]
      push_cast
      ring
    have hpre : Set.Ico (1 - a) 1 = (fun x : ℝ => x + (a - 1)) ⁻¹' Set.Ico (0 : ℝ) a := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Ico]
      constructor
      · intro h; exact ⟨by linarith [h.1], by linarith [h.2]⟩
      · intro h; exact ⟨by linarith [h.1], by linarith [h.2]⟩
    rw [hcong, hpre, ← Measure.restrict_map hadd' measurableSet_Ico, map_add_right_eq_self]
  calc Measure.map (fun x : ℝ => Int.fract (x + a)) unitMeasure
      = Measure.map (fun x : ℝ => Int.fract (x + a))
          (volume.restrict (Set.Ico (0 : ℝ) (1 - a)) + volume.restrict (Set.Ico (1 - a) 1)) := by
        rw [← hsplit]
    _ = volume.restrict (Set.Ico a 1) + volume.restrict (Set.Ico (0 : ℝ) a) := by
        rw [Measure.map_add _ _ hmeas, h1, h2]
    _ = unitMeasure := by
        rw [add_comm, unitMeasure,
          ← Measure.restrict_union Set.Ico_disjoint_Ico_same measurableSet_Ico,
          Set.Ico_union_Ico_eq_Ico ha0 ha1.le]

/-- **Circle rotation invariance.**  Adding an arbitrary real number modulo one
preserves the uniform law on `[0, 1)`.  This is the only new probabilistic input of
the translation invariance. -/
theorem map_fract_add_unitMeasure (c : ℝ) :
    Measure.map (fun x : ℝ => Int.fract (x + c)) unitMeasure = unitMeasure := by
  have hfun : (fun x : ℝ => Int.fract (x + c)) = fun x : ℝ => Int.fract (x + Int.fract c) :=
    funext fun x => fract_add_eq_fract_add_fract x c
  rw [hfun]
  exact map_fract_add_unitMeasure_of_mem_Ico (Int.fract_nonneg c) (Int.fract_lt_one c)

/-! ### Re-rooting on the cylinder data of one planar coordinate -/

/-- Re-rooting read on one planar coordinate of a cylinder: glue the relative origin
with the digits above it into the coarse relative origin, rotate that single
coordinate by `c` modulo one, and expand again.  The digit order is reversed because
`DyadicCylinderLaw.digitValue` weights slot `j` by `2 ^ j` while
`DyadicFiniteBitLaw.bitsUpTo` reads the most significant digit first. -/
noncomputable def coordShiftCyl (n : ℕ) (c : ℝ) (p : ℝ × (Fin n → Fin 2)) :
    ℝ × (Fin n → Fin 2) :=
  ((shiftBits n (Int.fract (glueDigits n p + c))).1,
    (shiftBits n (Int.fract (glueDigits n p + c))).2 ∘ Fin.rev)

/-- **The one coordinate law.**  Gluing, rotating modulo one and re-expanding
preserves the exact joint law "uniform remainder, independent fair digits". -/
theorem measurePreserving_coordShiftCyl (n : ℕ) (c : ℝ) :
    MeasurePreserving (coordShiftCyl n c) (unitMeasure.prod (digitMeasure n))
      (unitMeasure.prod (digitMeasure n)) := by
  have := isProbabilityMeasure_unitMeasure
  have h1 : MeasurePreserving (glueDigits n) (unitMeasure.prod (digitMeasure n)) unitMeasure :=
    ⟨measurable_glueDigits n, map_glueDigits n⟩
  have h2 : MeasurePreserving (fun x : ℝ => Int.fract (x + c)) unitMeasure unitMeasure :=
    ⟨measurable_fract.comp (measurable_id.add_const c), map_fract_add_unitMeasure c⟩
  have h3 : MeasurePreserving (shiftBits n) unitMeasure (unitMeasure.prod (digitMeasure n)) :=
    ⟨measurable_shiftBits n, map_shiftBits_unitMeasure n⟩
  have h4 : MeasurePreserving
      (Prod.map (id : ℝ → ℝ) (fun d : Fin n → Fin 2 => d ∘ Fin.rev))
      (unitMeasure.prod (digitMeasure n)) (unitMeasure.prod (digitMeasure n)) :=
    (MeasurePreserving.id unitMeasure).prod
      ⟨measurable_of_countable _, map_rev_digitMeasure n⟩
  exact ((h4.comp h3).comp h2).comp h1

/-! ### Regrouping the two planar coordinates -/

/-- The inverse of `DyadicCylinderLaw.planarAssemble`: read the cylinder data one
planar coordinate at a time. -/
def planarSplit (n : ℕ) (c : (Fin 2 → ℝ) × (Fin n → Fin 2 → Fin 2)) :
    Fin 2 → ℝ × (Fin n → Fin 2) :=
  fun i => (c.1 i, fun j => c.2 j i)

theorem planarSplit_planarAssemble (n : ℕ) (g : Fin 2 → ℝ × (Fin n → Fin 2)) :
    planarSplit n (planarAssemble n g) = g := rfl

theorem measurable_planarSplit (n : ℕ) : Measurable (planarSplit n) :=
  Measurable.of_eval fun i =>
    ((measurable_pi_apply i).comp measurable_fst).prodMk
      (Measurable.of_eval fun j => (measurable_pi_apply i).comp
        ((measurable_pi_apply j).comp measurable_snd))

/-- The law of the two independent planar coordinate cylinders. -/
noncomputable def innerTarget (n : ℕ) : Measure ((Fin 2 → ℝ) × (Fin n → Fin 2 → Fin 2)) :=
  (Measure.pi fun _ : Fin 2 => unitMeasure).prod
    (PMF.uniformOfFintype (Fin n → Fin 2 → Fin 2)).toMeasure

instance isProbabilityMeasure_innerTarget (n : ℕ) : IsProbabilityMeasure (innerTarget n) := by
  have := isProbabilityMeasure_unitMeasure
  unfold innerTarget
  infer_instance

/-- The full level-`k` depth-`n` cylinder law prescribed by
`DyadicApproximation.UniformGridLaw`. -/
noncomputable def cylinderTarget (n : ℕ) : Measure (Cyl n) :=
  unitMeasure.prod (innerTarget n)

theorem cylinderTarget_eq (n : ℕ) :
    cylinderTarget n
      = (volume.restrict (Set.Ico (0 : ℝ) 1)).prod
          ((Measure.pi fun _ : Fin 2 => volume.restrict (Set.Ico (0 : ℝ) 1)).prod
            (PMF.uniformOfFintype (Fin n → Fin 2 → Fin 2)).toMeasure) := rfl

theorem measurePreserving_planarAssemble (n : ℕ) :
    MeasurePreserving (planarAssemble n)
      (Measure.pi fun _ : Fin 2 => unitMeasure.prod (digitMeasure n)) (innerTarget n) :=
  ⟨measurable_planarAssemble n, map_planarAssemble n⟩

theorem measurePreserving_planarSplit (n : ℕ) :
    MeasurePreserving (planarSplit n) (innerTarget n)
      (Measure.pi fun _ : Fin 2 => unitMeasure.prod (digitMeasure n)) := by
  refine ⟨measurable_planarSplit n, ?_⟩
  have hid : planarSplit n ∘ planarAssemble n = id :=
    funext fun g => planarSplit_planarAssemble n g
  rw [innerTarget, ← map_planarAssemble n,
    Measure.map_map (measurable_planarSplit n) (measurable_planarAssemble n), hid, Measure.map_id]

/-! ### The induced map on the grid cylinder -/

/-- The rotation amount read by the coarse level `k + n` coordinate `i`: the shift `u`
measured in units of the side length at that level.  It depends on the grid only
through the phase. -/
noncomputable def phaseShiftConst (u : Plane) (k : ℤ) (n : ℕ) (p : ℝ) (i : Fin 2) : ℝ :=
  u i / (2 : ℝ) ^ (p + ((k + (n : ℤ) : ℤ) : ℝ))

theorem measurable_phaseShiftConst (u : Plane) (k : ℤ) (n : ℕ) (i : Fin 2) :
    Measurable fun p : ℝ => phaseShiftConst u k n p i :=
  measurable_const.div (measurable_two_rpow _)

/-- The action of re-rooting on the origin/digit part of a cylinder, at a fixed
phase. -/
noncomputable def translateCylInner (u : Plane) (k : ℤ) (n : ℕ) (p : ℝ)
    (c : (Fin 2 → ℝ) × (Fin n → Fin 2 → Fin 2)) : (Fin 2 → ℝ) × (Fin n → Fin 2 → Fin 2) :=
  planarAssemble n fun i => coordShiftCyl n (phaseShiftConst u k n p i) (planarSplit n c i)

/-- The action of re-rooting at `u` on the level-`k` depth-`n` grid cylinder. -/
noncomputable def translateCyl (u : Plane) (k : ℤ) (n : ℕ) (c : Cyl n) : Cyl n :=
  (c.1, translateCylInner u k n c.1 c.2)

theorem translateCylInner_eq_comp (u : Plane) (k : ℤ) (n : ℕ) (p : ℝ) :
    translateCylInner u k n p
      = planarAssemble n ∘ ((fun a : Fin 2 → ℝ × (Fin n → Fin 2) => fun i =>
          coordShiftCyl n (phaseShiftConst u k n p i) (a i)) ∘ planarSplit n) := by
  funext c
  rfl

theorem translateCyl_eq_skew (u : Plane) (k : ℤ) (n : ℕ) :
    translateCyl u k n
      = fun q : Cyl n => ((id : ℝ → ℝ) q.1, translateCylInner u k n q.1 q.2) := by
  funext q
  rfl

theorem translateCylInner_uncurry_eq_comp (u : Plane) (k : ℤ) (n : ℕ) :
    (fun q : ℝ × ((Fin 2 → ℝ) × (Fin n → Fin 2 → Fin 2)) => translateCylInner u k n q.1 q.2)
      = planarAssemble n ∘ (fun q : ℝ × ((Fin 2 → ℝ) × (Fin n → Fin 2 → Fin 2)) =>
          fun i => coordShiftCyl n (phaseShiftConst u k n q.1 i) (planarSplit n q.2 i)) := by
  funext q
  rfl

/-- Joint measurability of one planar slot of the re-rooting map, in the phase and the
cylinder data.  Built directly from the definition of `coordShiftCyl`, so that no
higher order unification against the uncurried map is needed. -/
theorem measurable_coordShiftCylSlot (u : Plane) (k : ℤ) (n : ℕ) (i : Fin 2) :
    Measurable fun q : ℝ × ((Fin 2 → ℝ) × (Fin n → Fin 2 → Fin 2)) =>
      coordShiftCyl n (phaseShiftConst u k n q.1 i) (planarSplit n q.2 i) := by
  have hc : Measurable fun q : ℝ × ((Fin 2 → ℝ) × (Fin n → Fin 2 → Fin 2)) =>
      phaseShiftConst u k n q.1 i :=
    (measurable_phaseShiftConst u k n i).comp measurable_fst
  have hp : Measurable fun q : ℝ × ((Fin 2 → ℝ) × (Fin n → Fin 2 → Fin 2)) =>
      planarSplit n q.2 i :=
    (measurable_pi_apply i).comp ((measurable_planarSplit n).comp measurable_snd)
  have hS : Measurable fun q : ℝ × ((Fin 2 → ℝ) × (Fin n → Fin 2 → Fin 2)) =>
      shiftBits n (Int.fract (glueDigits n (planarSplit n q.2 i)
        + phaseShiftConst u k n q.1 i)) :=
    (measurable_shiftBits n).comp
      (measurable_fract.comp (((measurable_glueDigits n).comp hp).add hc))
  show Measurable fun q : ℝ × ((Fin 2 → ℝ) × (Fin n → Fin 2 → Fin 2)) =>
      ((shiftBits n (Int.fract (glueDigits n (planarSplit n q.2 i)
          + phaseShiftConst u k n q.1 i))).1,
        (shiftBits n (Int.fract (glueDigits n (planarSplit n q.2 i)
          + phaseShiftConst u k n q.1 i))).2 ∘ Fin.rev)
  exact (measurable_fst.comp hS).prodMk
    ((measurable_of_countable fun d : Fin n → Fin 2 => d ∘ Fin.rev).comp
      (measurable_snd.comp hS))

theorem measurable_translateCylInner_uncurry (u : Plane) (k : ℤ) (n : ℕ) :
    Measurable fun q : ℝ × ((Fin 2 → ℝ) × (Fin n → Fin 2 → Fin 2)) =>
      translateCylInner u k n q.1 q.2 := by
  rw [translateCylInner_uncurry_eq_comp]
  exact (measurable_planarAssemble n).comp
    (Measurable.of_eval fun i => measurable_coordShiftCylSlot u k n i)

theorem measurePreserving_translateCylInner (u : Plane) (k : ℤ) (n : ℕ) (p : ℝ) :
    MeasurePreserving (translateCylInner u k n p) (innerTarget n) (innerTarget n) := by
  have := isProbabilityMeasure_unitMeasure
  have hmid : MeasurePreserving
      (fun a : Fin 2 → ℝ × (Fin n → Fin 2) => fun i =>
        coordShiftCyl n (phaseShiftConst u k n p i) (a i))
      (Measure.pi fun _ : Fin 2 => unitMeasure.prod (digitMeasure n))
      (Measure.pi fun _ : Fin 2 => unitMeasure.prod (digitMeasure n)) :=
    measurePreserving_pi _ _ fun i => measurePreserving_coordShiftCyl n _
  rw [translateCylInner_eq_comp]
  exact (measurePreserving_planarAssemble n).comp
    (hmid.comp (measurePreserving_planarSplit n))

/-- **The finite cylinder law is translation invariant.**  The phase is unchanged and
the origin/digit part is transported by a measure preserving map, so the whole
cylinder law is preserved.  This is the skew product structure of re-rooting. -/
theorem measurePreserving_translateCyl (u : Plane) (k : ℤ) (n : ℕ) :
    MeasurePreserving (translateCyl u k n) (cylinderTarget n) (cylinderTarget n) := by
  have := isProbabilityMeasure_unitMeasure
  rw [translateCyl_eq_skew, cylinderTarget]
  exact MeasurePreserving.skew_product (MeasurePreserving.id unitMeasure)
    (measurable_translateCylInner_uncurry u k n)
    (ae_of_all _ fun p => (measurePreserving_translateCylInner u k n p).map_eq)

theorem measurable_translateCyl (u : Plane) (k : ℤ) (n : ℕ) :
    Measurable (translateCyl u k n) :=
  (measurePreserving_translateCyl u k n).measurable

/-! ### The cylinder of a re-rooted grid -/

/-- The coarse relative origin: gluing the level-`k` relative origin with the `n`
parent digits above it returns the relative origin at level `k + n`.  This is
`DyadicGridLawUniqueness.relOrigin_add_nat` read through
`DyadicCylinderLaw.glueDigits`. -/
theorem glueDigits_relativeOrigin (D : Grid) (k : ℤ) (n : ℕ) (i : Fin 2) :
    glueDigits n (relativeOrigin D k i, fun j : Fin n => D.digit (k + (j.val : ℤ)) i)
      = relativeOrigin D (k + (n : ℤ)) i := by
  have h : relativeOrigin D (k + (n : ℤ)) i
      = (2 : ℝ) ^ (-(n : ℝ)) * (relativeOrigin D k i
        + ∑ j : Fin n, (2 : ℝ) ^ (((j : ℕ) : ℝ)) *
            ((D.digit (k + ((j : ℕ) : ℤ)) i).val : ℝ)) :=
    DyadicGridLawUniqueness.relOrigin_add_nat D k n i
  have hpow : (2 : ℝ) ^ (-(n : ℝ)) = ((2 : ℝ) ^ n)⁻¹ := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  have hsum : ∑ j : Fin n, (2 : ℝ) ^ (((j : ℕ) : ℝ)) * ((D.digit (k + ((j : ℕ) : ℤ)) i).val : ℝ)
      = digitValue (fun j : Fin n => D.digit (k + (j.val : ℤ)) i) := by
    rw [digitValue]
    exact Finset.sum_congr rfl fun j _ => by rw [Real.rpow_natCast]
  show ((2 : ℝ) ^ n)⁻¹ * (relativeOrigin D k i
      + digitValue (fun j : Fin n => D.digit (k + (j.val : ℤ)) i))
    = relativeOrigin D (k + (n : ℤ)) i
  rw [h, hpow, hsum]

/-- The translated relative origins of all levels between `k` and `k + m` are the
successive binary shifts of the translated relative origin at the coarse level
`k + m`.  Iterated `DyadicGridTranslation.fract_two_mul_shifted`. -/
theorem fract_pow_mul_shiftedRelativeOrigin (D : Grid) (u : Plane) (i : Fin 2) (m : ℕ) :
    ∀ k : ℤ, Int.fract ((2 : ℝ) ^ m * shiftedRelativeOrigin D u (k + (m : ℤ)) i)
      = shiftedRelativeOrigin D u k i := by
  induction m with
  | zero =>
    intro k
    have h : k + ((0 : ℕ) : ℤ) = k := by push_cast; ring
    rw [h, pow_zero, one_mul]
    exact Int.fract_eq_self.2
      ⟨shiftedRelativeOrigin_nonneg D u k i, shiftedRelativeOrigin_lt_one D u k i⟩
  | succ m ih =>
    intro k
    have hidx : k + ((m + 1 : ℕ) : ℤ) = (k + (m : ℤ)) + 1 := by push_cast; ring
    have hstep := fract_two_mul_shifted D u (k + (m : ℤ)) i
    calc Int.fract ((2 : ℝ) ^ (m + 1) * shiftedRelativeOrigin D u (k + ((m + 1 : ℕ) : ℤ)) i)
        = Int.fract ((2 : ℝ) ^ m *
            (2 * shiftedRelativeOrigin D u ((k + (m : ℤ)) + 1) i)) := by
          rw [hidx]
          congr 1
          ring
      _ = Int.fract ((2 : ℝ) ^ m *
            Int.fract (2 * shiftedRelativeOrigin D u ((k + (m : ℤ)) + 1) i)) :=
          (DyadicCylinderLaw.fract_pow_mul_fract m _).symm
      _ = Int.fract ((2 : ℝ) ^ m * shiftedRelativeOrigin D u (k + (m : ℤ)) i) := by
          rw [hstep]
      _ = shiftedRelativeOrigin D u k i := ih k

/-- The coordinatewise geometric identity: the translated cylinder data of one planar
coordinate is exactly the glue–rotate–expand map `coordShiftCyl`. -/
theorem coordShiftCyl_gridCylinder (u : Plane) (k : ℤ) (n : ℕ) (D : Grid) (i : Fin 2) :
    coordShiftCyl n (phaseShiftConst u k n D.phase i)
        (relativeOrigin D k i, fun j : Fin n => D.digit (k + (j.val : ℤ)) i)
      = (shiftedRelativeOrigin D u k i,
          fun j : Fin n => translatedDigit D u (k + (j.val : ℤ)) i) := by
  have hconst : phaseShiftConst u k n D.phase i = u i / side D (k + (n : ℤ)) := rfl
  have hglue : Int.fract (glueDigits n
        (relativeOrigin D k i, fun j : Fin n => D.digit (k + (j.val : ℤ)) i)
        + phaseShiftConst u k n D.phase i)
      = shiftedRelativeOrigin D u (k + (n : ℤ)) i := by
    rw [glueDigits_relativeOrigin D k n i, hconst]
    rfl
  have hset : coordShiftCyl n (phaseShiftConst u k n D.phase i)
        (relativeOrigin D k i, fun j : Fin n => D.digit (k + (j.val : ℤ)) i)
      = ((shiftBits n (shiftedRelativeOrigin D u (k + (n : ℤ)) i)).1,
          (shiftBits n (shiftedRelativeOrigin D u (k + (n : ℤ)) i)).2 ∘ Fin.rev) := by
    simp only [coordShiftCyl, hglue]
  have hfst : (shiftBits n (shiftedRelativeOrigin D u (k + (n : ℤ)) i)).1
      = shiftedRelativeOrigin D u k i :=
    fract_pow_mul_shiftedRelativeOrigin D u i n k
  have hsnd : (shiftBits n (shiftedRelativeOrigin D u (k + (n : ℤ)) i)).2 ∘ Fin.rev
      = fun j : Fin n => translatedDigit D u (k + (j.val : ℤ)) i := by
    funext j
    have hj : (j : ℕ) < n := j.isLt
    have hrev : ((Fin.rev j : Fin n) : ℕ) = n - 1 - (j : ℕ) := by
      rw [Fin.val_rev]
      omega
    have hidx : (k + (j.val : ℤ) + 1) + ((n - 1 - (j : ℕ) : ℕ) : ℤ) = k + (n : ℤ) := by
      omega
    have hstep := fract_pow_mul_shiftedRelativeOrigin D u i (n - 1 - (j : ℕ))
      (k + (j.val : ℤ) + 1)
    rw [hidx] at hstep
    show bitFin ((2 : ℝ) ^ (((Fin.rev j : Fin n)) : ℕ) *
        shiftedRelativeOrigin D u (k + (n : ℤ)) i) = translatedDigit D u (k + (j.val : ℤ)) i
    rw [hrev, translatedDigit, ← hstep, bitFin, bitInt_fract]
  rw [hset, hfst, hsnd]

/-- **The cylinder of a re-rooted grid.**  The level-`k` depth-`n` cylinder of
`translate u D` is the explicit measurable function `translateCyl u k n` of the
level-`k` depth-`n` cylinder of `D`: no deeper data of `D` is needed. -/
theorem gridCylinder_translate (u : Plane) (k : ℤ) (n : ℕ) (D : Grid) :
    gridCylinder k n (translate u D) = translateCyl u k n (gridCylinder k n D) := by
  have hL : gridCylinder k n (translate u D)
      = (D.phase, (fun i => shiftedRelativeOrigin D u k i,
          fun (j : Fin n) (i : Fin 2) => translatedDigit D u (k + (j.val : ℤ)) i)) := by
    have h2 : (fun i => -(translate u D).origin k i / side (translate u D) k)
        = fun i => shiftedRelativeOrigin D u k i :=
      funext fun i => relativeOrigin_translate u D k i
    show ((translate u D).phase,
        (fun i => -(translate u D).origin k i / side (translate u D) k,
          fun (j : Fin n) (i : Fin 2) => (translate u D).digit (k + (j.val : ℤ)) i)) = _
    rw [h2]
    rfl
  have hR : translateCyl u k n (gridCylinder k n D)
      = (D.phase, ((fun i => (coordShiftCyl n (phaseShiftConst u k n D.phase i)
            (relativeOrigin D k i, fun j : Fin n => D.digit (k + (j.val : ℤ)) i)).1),
          fun (j : Fin n) (i : Fin 2) => (coordShiftCyl n (phaseShiftConst u k n D.phase i)
            (relativeOrigin D k i, fun j : Fin n => D.digit (k + (j.val : ℤ)) i)).2 j)) := rfl
  have hA : (fun i => shiftedRelativeOrigin D u k i)
      = fun i => (coordShiftCyl n (phaseShiftConst u k n D.phase i)
          (relativeOrigin D k i, fun j : Fin n => D.digit (k + (j.val : ℤ)) i)).1 :=
    funext fun i => by rw [coordShiftCyl_gridCylinder u k n D i]
  have hB : (fun (j : Fin n) (i : Fin 2) => translatedDigit D u (k + (j.val : ℤ)) i)
      = fun (j : Fin n) (i : Fin 2) => (coordShiftCyl n (phaseShiftConst u k n D.phase i)
          (relativeOrigin D k i, fun j : Fin n => D.digit (k + (j.val : ℤ)) i)).2 j :=
    funext fun j => funext fun i => by rw [coordShiftCyl_gridCylinder u k n D i]
  rw [hL, hR, hA, hB]

/-! ### Translation invariance of the law -/

/-- Re-rooting a uniform random dyadic grid gives a uniform random dyadic grid: every
finite cylinder law is preserved.  In particular the translated parent digits are
*proved* to be independent fair coins, independent of the translated relative
origin. -/
theorem uniformGridLaw_map_translate {ν : Measure Grid} (h : UniformGridLaw ν) (u : Plane) :
    UniformGridLaw (Measure.map (translate u) ν) := by
  have := h.1
  refine ⟨inferInstance, fun k n => ?_⟩
  have hfun : gridCylinder k n ∘ translate u = translateCyl u k n ∘ gridCylinder k n :=
    funext fun D => gridCylinder_translate u k n D
  rw [Measure.map_map (ReflectedGMS.DyadicGridLaw.measurable_gridCylinder k n)
      (measurable_translate_left u), hfun,
    ← Measure.map_map (measurable_translateCyl u k n)
      (ReflectedGMS.DyadicGridLaw.measurable_gridCylinder k n),
    h.2 k n, ← cylinderTarget_eq]
  exact (measurePreserving_translateCyl u k n).map_eq

/-- **Translation invariance of the uniform dyadic grid law.**  Any measure realising
`DyadicApproximation.UniformGridLaw` is invariant under the re-rooting action
`DyadicGridTranslation.translate`. -/
theorem map_translate_of_uniformGridLaw {ν : Measure Grid} (h : UniformGridLaw ν) (u : Plane) :
    Measure.map (translate u) ν = ν :=
  DyadicGridLawUniqueness.eq_of_uniformGridLaw (uniformGridLaw_map_translate h u) h

/-- **The mark-law input.**  The constructed independent grid law
`DyadicGridLaw.gridMeasure` is invariant under re-rooting at every point of the
plane.  No invariant mark law is assumed: invariance is derived from the actual
cylinder law of the construction. -/
theorem map_translate_gridMeasure (u : Plane) :
    Measure.map (translate u) gridMeasure = gridMeasure :=
  map_translate_of_uniformGridLaw DyadicCylinderLaw.uniformGridLaw_gridMeasure u

end ReflectedGMS.UniformGridTranslationInvariance
