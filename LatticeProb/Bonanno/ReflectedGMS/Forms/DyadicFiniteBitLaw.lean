/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.DyadicFiniteBitLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.DyadicDigitLaw
import Mathlib.MeasureTheory.Constructions.Pi

/-! The exact joint law of the remainder and the first `m` binary digits.

`DyadicDigitLaw.map_shiftBit_unitMeasure` is the one step identity: under the
uniform law on `[0, 1)` the pair `x ↦ (Int.fract (2 * x), bitFin x)` has law
`unitMeasure.prod (fair coin)`.  The cylinder law of
`DyadicGridLaw.map_gridCylinder_gridMeasure` needs the same statement for
finitely many successive digits at once, because `DyadicGridLaw.digitInt` reads
the digits of a single uniform coordinate at the levels `k, …, k + n - 1`.

The `m` step map is here the closed form

  `shiftBits m x = (Int.fract (2 ^ m * x), fun j : Fin m => bitFin (2 ^ (j : ℕ) * x))`

built from the source level `DyadicGridLaw.bitInt` and `DyadicGridLaw.intToFin2`
through `DyadicDigitLaw.bitFin`, with no new binary expansion machinery.  The
proof first identifies this closed form with the one step iteration
(`shiftBits_succ`, using that `bitInt` is unchanged by an integer translation)
and then transports the one step product law along `Measure.map_prod_map`,
`Measure.prodAssoc_prod` and the measure preserving `Fin.snoc` equivalence
`MeasureTheory.measurePreserving_piFinSuccAbove` at `Fin.last`.

The conclusion is exact, with the half-open endpoints of the source statement:
the remainder `Int.fract (2 ^ m * x)` is again exactly uniform on `[0, 1)` and is
exactly independent of the first `m` digits, which are independent fair coins.
This is only the finite digit input; it does not by itself give the law of a grid
cylinder whose levels have mixed signs. -/

set_option autoImplicit false

open MeasureTheory Set

open scoped ENNReal

namespace ReflectedGMS.DyadicFiniteBitLaw

open ReflectedGMS.DyadicGridLaw ReflectedGMS.DyadicDigitLaw

/-! ### Integer translation invariance of the binary digit -/

/-- The binary digit `DyadicGridLaw.bitInt` is invariant under integer translation. -/
theorem bitInt_add_intCast (y : ℝ) (n : ℤ) : bitInt (y + (n : ℝ)) = bitInt y := by
  have h : 2 * (y + (n : ℝ)) = 2 * y + ((2 * n : ℤ) : ℝ) := by push_cast; ring
  simp only [bitInt, h, Int.floor_add_intCast]
  ring

theorem fract_eq_add_intCast (y : ℝ) : Int.fract y = y + ((-⌊y⌋ : ℤ) : ℝ) := by
  rw [← Int.self_sub_floor]
  push_cast
  ring

theorem bitInt_fract (y : ℝ) : bitInt (Int.fract y) = bitInt y := by
  rw [fract_eq_add_intCast y, bitInt_add_intCast]

theorem bitFin_fract (y : ℝ) : bitFin (Int.fract y) = bitFin y := by
  rw [bitFin, bitFin, bitInt_fract]

theorem fract_two_mul_fract (y : ℝ) : Int.fract (2 * Int.fract y) = Int.fract (2 * y) := by
  have h : 2 * Int.fract y = 2 * y + ((-(2 * ⌊y⌋) : ℤ) : ℝ) := by
    rw [fract_eq_add_intCast y]
    push_cast
    ring
  rw [h, Int.fract_add_intCast]

/-! ### The `m` step shift and its digits -/

/-- The first `m` binary digits of a real number, in the source level form
`DyadicGridLaw.intToFin2 (DyadicGridLaw.bitInt (2 ^ j * x))`. -/
noncomputable def bitsUpTo (m : ℕ) (x : ℝ) : Fin m → Fin 2 :=
  fun j => bitFin ((2 : ℝ) ^ (j : ℕ) * x)

/-- The remainder after `m` shifts together with the first `m` binary digits. -/
noncomputable def shiftBits (m : ℕ) (x : ℝ) : ℝ × (Fin m → Fin 2) :=
  (Int.fract ((2 : ℝ) ^ m * x), bitsUpTo m x)

theorem shiftBits_fst (m : ℕ) (x : ℝ) :
    (shiftBits m x).1 = Int.fract ((2 : ℝ) ^ m * x) := rfl

theorem shiftBits_snd (m : ℕ) (x : ℝ) : (shiftBits m x).2 = bitsUpTo m x := rfl

/-- **Exact iteration.**  The closed form of the `m + 1` step map is one further
application of the one step map `DyadicDigitLaw.shiftBit` to the remainder, with
the new digit appended. -/
theorem shiftBits_succ (m : ℕ) (x : ℝ) :
    shiftBits (m + 1) x
      = (Int.fract (2 * (shiftBits m x).1),
          Fin.snoc (shiftBits m x).2 (bitFin (shiftBits m x).1)) := by
  have hpow : (2 : ℝ) ^ (m + 1) * x = 2 * ((2 : ℝ) ^ m * x) := by ring
  have hfst : Int.fract ((2 : ℝ) ^ (m + 1) * x)
      = Int.fract (2 * Int.fract ((2 : ℝ) ^ m * x)) := by
    rw [fract_two_mul_fract, hpow]
  have hsnd : bitsUpTo (m + 1) x
      = Fin.snoc (bitsUpTo m x) (bitFin (Int.fract ((2 : ℝ) ^ m * x))) := by
    funext j
    induction j using Fin.lastCases with
    | last => simp [bitsUpTo, bitFin_fract]
    | cast i => simp [bitsUpTo]
  simp only [shiftBits, hfst, hsnd]

/-! ### Measurability -/

theorem measurable_bitsUpTo (m : ℕ) : Measurable (bitsUpTo m) :=
  Measurable.of_eval fun _ => measurable_bitFin.comp (measurable_const.mul measurable_id)

theorem measurable_shiftBits (m : ℕ) : Measurable (shiftBits m) :=
  (measurable_fract.comp (measurable_const.mul measurable_id)).prodMk (measurable_bitsUpTo m)

/-- Appending a digit to a finite digit tuple. -/
def snocDigit (m : ℕ) (p : Fin 2 × (Fin m → Fin 2)) : Fin (m + 1) → Fin 2 :=
  Fin.snoc p.2 p.1

theorem measurable_snocDigit (m : ℕ) : Measurable (snocDigit m) :=
  measurable_of_countable _

/-- Appending the digit produced together with the new remainder. -/
def snocRemainder (m : ℕ) (p : (ℝ × Fin 2) × (Fin m → Fin 2)) : ℝ × (Fin (m + 1) → Fin 2) :=
  (p.1.1, Fin.snoc p.2 p.1.2)

theorem measurable_snocRemainder (m : ℕ) : Measurable (snocRemainder m) :=
  (measurable_fst.comp measurable_fst).prodMk
    ((measurable_snocDigit m).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

/-! ### The uniform law on finite digit tuples -/

/-- Independent fair coins in each of `m` digit slots. -/
noncomputable def digitMeasure (m : ℕ) : Measure (Fin m → Fin 2) :=
  Measure.pi fun _ => (PMF.uniformOfFintype (Fin 2)).toMeasure

instance isProbabilityMeasure_digitMeasure (m : ℕ) : IsProbabilityMeasure (digitMeasure m) := by
  rw [digitMeasure]
  infer_instance

/-- Independent fair digits are exactly the uniform law on the finite tuple type,
the shape required by `DyadicApproximation.UniformGridLaw`. -/
theorem digitMeasure_eq_uniformOfFintype (m : ℕ) :
    digitMeasure m = (PMF.uniformOfFintype (Fin m → Fin 2)).toMeasure := by
  refine Measure.ext_of_singleton fun f => ?_
  have hcoin : ∀ i : Fin m,
      (PMF.uniformOfFintype (Fin 2)).toMeasure {f i} = (2 : ℝ≥0∞)⁻¹ := by
    intro i
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton (f i)),
      PMF.uniformOfFintype_apply]
    simp
  have hcard : (Fintype.card (Fin m → Fin 2) : ℝ≥0∞) = 2 ^ m := by
    simp
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton f),
    PMF.uniformOfFintype_apply, digitMeasure, Measure.pi_singleton,
    Finset.prod_congr rfl fun i _ => hcoin i, Finset.prod_const, hcard, ENNReal.inv_pow]
  simp

/-- Appending one fair coin to `m` independent fair coins gives `m + 1`
independent fair coins. -/
theorem map_snocDigit_digitMeasure (m : ℕ) :
    Measure.map (snocDigit m)
        (((PMF.uniformOfFintype (Fin 2)).toMeasure).prod (digitMeasure m))
      = digitMeasure (m + 1) := by
  have hfun : ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => Fin 2) (Fin.last m)).symm
      = snocDigit m := by
    funext p
    simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.insertNth_last', snocDigit]
  have h := (MeasureTheory.measurePreserving_piFinSuccAbove
    (fun _ : Fin (m + 1) => (PMF.uniformOfFintype (Fin 2)).toMeasure) (Fin.last m)).symm.map_eq
  rw [hfun] at h
  simp only [digitMeasure]
  exact h

/-! ### The finite bit product law -/

/-- The three factor rearrangement behind the induction step: the new remainder,
the new digit and the old digits recombine into a remainder and a digit tuple. -/
theorem map_snocRemainder_prod (μ : Measure ℝ) [SFinite μ] (m : ℕ) :
    Measure.map (snocRemainder m)
        ((μ.prod ((PMF.uniformOfFintype (Fin 2)).toMeasure)).prod (digitMeasure m))
      = μ.prod (digitMeasure (m + 1)) := by
  have hfun : snocRemainder m
      = (Prod.map id (snocDigit m)) ∘
        (MeasurableEquiv.prodAssoc :
          (ℝ × Fin 2) × (Fin m → Fin 2) ≃ᵐ ℝ × (Fin 2 × (Fin m → Fin 2))) := by
    funext p
    rfl
  rw [hfun, ← Measure.map_map (measurable_id.prodMap (measurable_snocDigit m))
      (MeasurableEquiv.prodAssoc).measurable, Measure.prodAssoc_prod,
    ← Measure.map_prod_map μ _ measurable_id (measurable_snocDigit m),
    Measure.map_id, map_snocDigit_digitMeasure]

/-- **Exact finite bit product law.**  Under the uniform law on the half-open
unit interval the remainder `Int.fract (2 ^ m * x)` is again exactly uniform on
`[0, 1)` and is exactly independent of the first `m` binary digits, which are
independent fair coins. -/
theorem map_shiftBits_unitMeasure (m : ℕ) :
    Measure.map (shiftBits m) unitMeasure = unitMeasure.prod (digitMeasure m) := by
  have := isProbabilityMeasure_unitMeasure
  induction m with
  | zero =>
    have hdirac : digitMeasure 0 = Measure.dirac (Fin.elim0 : Fin 0 → Fin 2) := by
      rw [digitMeasure]
      exact Measure.pi_of_empty _ _
    have hmem : ∀ᵐ x ∂unitMeasure, x ∈ Set.Ico (0 : ℝ) 1 := by
      rw [unitMeasure]
      exact ae_restrict_mem measurableSet_Ico
    rw [hdirac, Measure.prod_dirac]
    refine Measure.map_congr ?_
    filter_upwards [hmem] with x hx
    have hx' : Int.fract ((2 : ℝ) ^ (0 : ℕ) * x) = x := by
      rw [pow_zero, one_mul]
      exact Int.fract_eq_self.2 ⟨hx.1, hx.2⟩
    have hfun : bitsUpTo 0 x = (Fin.elim0 : Fin 0 → Fin 2) := by
      funext j
      exact j.elim0
    simp only [shiftBits, hx', hfun]
  | succ m ih =>
    have hcomp : shiftBits (m + 1)
        = snocRemainder m ∘ (Prod.map shiftBit id ∘ shiftBits m) := by
      funext x
      rw [shiftBits_succ]
      rfl
    rw [hcomp, ← Measure.map_map (measurable_snocRemainder m)
        ((measurable_shiftBit.prodMap measurable_id).comp (measurable_shiftBits m)),
      ← Measure.map_map (measurable_shiftBit.prodMap measurable_id) (measurable_shiftBits m),
      ih, ← Measure.map_prod_map unitMeasure (digitMeasure m) measurable_shiftBit measurable_id,
      map_shiftBit_unitMeasure, Measure.map_id, map_snocRemainder_prod]

end ReflectedGMS.DyadicFiniteBitLaw
