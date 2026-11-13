/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.DyadicDigitLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.DyadicGridLaw
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Measure.WithDensity

/-! Fairness and independence of the first binary digit of a uniform real.

`DyadicGridLaw.map_gridCylinder_gridMeasure` reduces `DyadicApproximation.UniformGridLaw`
for `DyadicGridLaw.gridMeasure` to a statement about the uniform source coordinates:
the relative origins must stay uniform while the parent digits are fair and
independent of them.  The single missing probabilistic input is the one step
identity proved here: under Lebesgue measure on `[0, 1)` the pair

  `x ↦ (Int.fract (2 * x), first binary digit of x)`

is distributed as the product of the uniform law on `[0, 1)` with the fair coin
on `Fin 2`.  Both halves of the statement matter for the consumer: the shifted
fractional part is again exactly uniform on the half-open unit interval, and it
is exactly independent of the digit, not merely uniform in the margin.

The proof is the two affine changes of variable `x ↦ 2 * x` on `[0, 1/2)` and
`x ↦ 2 * x - 1` on `[1/2, 1)`, each of which halves Lebesgue measure, combined
with the dirac decomposition of the fair coin.  The digit is
`DyadicGridLaw.bitInt` read through `DyadicGridLaw.intToFin2`, so no new binary
expansion machinery is introduced. -/

set_option autoImplicit false

open MeasureTheory Set

open scoped ENNReal

namespace ReflectedGMS.DyadicDigitLaw

open ReflectedGMS.DyadicGridLaw

/-! ### The fair coin on `Fin 2` -/

/-- The uniform law on `Fin 2`, the shape used by `DyadicApproximation.UniformGridLaw`,
written as a combination of point masses. -/
theorem toMeasure_uniformOfFintype_finTwo :
    (PMF.uniformOfFintype (Fin 2)).toMeasure
      = (2 : ℝ≥0∞)⁻¹ • Measure.dirac (0 : Fin 2)
        + (2 : ℝ≥0∞)⁻¹ • Measure.dirac (1 : Fin 2) := by
  refine Measure.ext_of_singleton fun b => ?_
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton b),
    PMF.uniformOfFintype_apply]
  fin_cases b <;> simp [Measure.dirac_apply]

/-! ### The one step binary expansion map -/

/-- The first binary digit of a real number, as an element of `Fin 2`. -/
noncomputable def bitFin (x : ℝ) : Fin 2 := intToFin2 (bitInt x)

/-- The shifted fractional part together with the first binary digit. -/
noncomputable def shiftBit (x : ℝ) : ℝ × Fin 2 := (Int.fract (2 * x), bitFin x)

theorem measurable_bitFin : Measurable bitFin :=
  (measurable_of_countable intToFin2).comp measurable_bitInt

theorem measurable_shiftBit : Measurable shiftBit :=
  (measurable_fract.comp (measurable_const.mul measurable_id)).prodMk measurable_bitFin

/-! ### The two affine branches -/

theorem measurable_two_mul_sub (c : ℝ) : Measurable fun x : ℝ => 2 * x - c :=
  (measurable_const.mul measurable_id).sub measurable_const

theorem preimage_two_mul_sub_Ico (c : ℝ) :
    (fun x : ℝ => 2 * x - c) ⁻¹' Set.Ico (0 : ℝ) 1 = Set.Ico (c / 2) ((c + 1) / 2) := by
  ext x
  simp only [Set.mem_preimage, Set.mem_Ico]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    constructor <;> linarith

/-- The affine branch halves Lebesgue measure on the whole line. -/
theorem map_volume_two_mul_sub (c : ℝ) :
    Measure.map (fun x : ℝ => 2 * x - c) volume = (2 : ℝ≥0∞)⁻¹ • volume := by
  have hmul : Measurable fun x : ℝ => 2 * x := measurable_const.mul measurable_id
  have hadd : Measurable fun y : ℝ => y + -c := measurable_id.add_const _
  have hfun : (fun x : ℝ => 2 * x - c) = (fun y : ℝ => y + -c) ∘ fun x : ℝ => 2 * x := by
    funext x
    simp [sub_eq_add_neg]
  have habs : ENNReal.ofReal |(2 : ℝ)⁻¹| = (2 : ℝ≥0∞)⁻¹ := by
    rw [abs_of_pos (by norm_num : (0 : ℝ) < (2 : ℝ)⁻¹),
      ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hscale : Measure.map (fun x : ℝ => 2 * x) volume = (2 : ℝ≥0∞)⁻¹ • volume := by
    have h := Real.map_volume_mul_left (a := 2) (by norm_num)
    rw [habs] at h
    exact h
  rw [hfun, ← Measure.map_map hadd hmul, hscale, Measure.map_smul _ hadd.aemeasurable,
    map_add_right_eq_self volume (-c)]

/-- The affine branch sends the corresponding half of the unit interval onto a
half copy of the uniform law on `[0, 1)`. -/
theorem map_halfInterval (c : ℝ) :
    Measure.map (fun x : ℝ => 2 * x - c) (volume.restrict (Set.Ico (c / 2) ((c + 1) / 2)))
      = (2 : ℝ≥0∞)⁻¹ • unitMeasure := by
  have h := Measure.restrict_map (μ := (volume : Measure ℝ)) (measurable_two_mul_sub c)
    (measurableSet_Ico (a := (0 : ℝ)) (b := 1))
  rw [preimage_two_mul_sub_Ico c] at h
  rw [← h, map_volume_two_mul_sub c, Measure.restrict_smul]
  rfl

/-- The same computation with the digit value recorded in the second coordinate. -/
theorem map_halfInterval_pair (c : ℝ) (b : Fin 2) :
    Measure.map (fun x : ℝ => (2 * x - c, b))
        (volume.restrict (Set.Ico (c / 2) ((c + 1) / 2)))
      = (2 : ℝ≥0∞)⁻¹ • Measure.map (fun y : ℝ => (y, b)) unitMeasure := by
  have hpair : Measurable fun y : ℝ => (y, b) := measurable_id.prodMk measurable_const
  have hfun : (fun x : ℝ => (2 * x - c, b))
      = (fun y : ℝ => (y, b)) ∘ fun x : ℝ => 2 * x - c := by
    funext x
    rfl
  rw [hfun, ← Measure.map_map hpair (measurable_two_mul_sub c), map_halfInterval c,
    Measure.map_smul _ hpair.aemeasurable]

/-! ### Identification of the two branches -/

theorem shiftBit_of_mem_Ico_zero_half {x : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) (1 / 2)) :
    shiftBit x = (2 * x - 0, (0 : Fin 2)) := by
  obtain ⟨h0, h1⟩ := hx
  have hfx : ⌊x⌋ = 0 := Int.floor_eq_iff.2 (by push_cast; constructor <;> linarith)
  have hf2 : ⌊2 * x⌋ = 0 := Int.floor_eq_iff.2 (by push_cast; constructor <;> linarith)
  have hb : bitInt x = 0 := by simp [bitInt, hfx, hf2]
  simp [shiftBit, bitFin, hb, intToFin2, Int.fract, hf2]

theorem shiftBit_of_mem_Ico_half_one {x : ℝ} (hx : x ∈ Set.Ico (1 / 2 : ℝ) 1) :
    shiftBit x = (2 * x - 1, (1 : Fin 2)) := by
  obtain ⟨h0, h1⟩ := hx
  have hfx : ⌊x⌋ = 0 := Int.floor_eq_iff.2 (by push_cast; constructor <;> linarith)
  have hf2 : ⌊2 * x⌋ = 1 := Int.floor_eq_iff.2 (by push_cast; constructor <;> linarith)
  have hb : bitInt x = 1 := by simp [bitInt, hfx, hf2]
  simp [shiftBit, bitFin, hb, intToFin2, Int.fract, hf2]

/-- The half-open unit interval splits at `1/2` into the two digit branches. -/
theorem unitMeasure_eq_add_halves :
    unitMeasure = volume.restrict (Set.Ico (0 : ℝ) (1 / 2))
      + volume.restrict (Set.Ico (1 / 2 : ℝ) 1) := by
  have hdisj : Disjoint (Set.Ico (0 : ℝ) (1 / 2)) (Set.Ico (1 / 2 : ℝ) 1) := by
    rw [Set.disjoint_left]
    rintro x ⟨-, hx2⟩ ⟨hx3, -⟩
    linarith
  rw [← Measure.restrict_union hdisj measurableSet_Ico,
    Set.Ico_union_Ico_eq_Ico (by norm_num) (by norm_num)]
  rfl

theorem map_shiftBit_lower :
    Measure.map shiftBit (volume.restrict (Set.Ico (0 : ℝ) (1 / 2)))
      = (2 : ℝ≥0∞)⁻¹ • Measure.map (fun y : ℝ => (y, (0 : Fin 2))) unitMeasure := by
  have hae : shiftBit =ᵐ[volume.restrict (Set.Ico (0 : ℝ) (1 / 2))]
      fun x : ℝ => (2 * x - 0, (0 : Fin 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
      using shiftBit_of_mem_Ico_zero_half hx
  have hset : Set.Ico (0 : ℝ) (1 / 2) = Set.Ico ((0 : ℝ) / 2) (((0 : ℝ) + 1) / 2) := by
    norm_num
  rw [Measure.map_congr hae, hset, map_halfInterval_pair 0 0]

theorem map_shiftBit_upper :
    Measure.map shiftBit (volume.restrict (Set.Ico (1 / 2 : ℝ) 1))
      = (2 : ℝ≥0∞)⁻¹ • Measure.map (fun y : ℝ => (y, (1 : Fin 2))) unitMeasure := by
  have hae : shiftBit =ᵐ[volume.restrict (Set.Ico (1 / 2 : ℝ) 1)]
      fun x : ℝ => (2 * x - 1, (1 : Fin 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
      using shiftBit_of_mem_Ico_half_one hx
  have hset : Set.Ico (1 / 2 : ℝ) 1 = Set.Ico ((1 : ℝ) / 2) (((1 : ℝ) + 1) / 2) := by
    norm_num
  rw [Measure.map_congr hae, hset, map_halfInterval_pair 1 1]

/-! ### The one bit uniform law -/

/-- **Fairness and independence of the first binary digit.**  Under the uniform
law on the half-open unit interval, the shifted fractional part `Int.fract (2 * x)`
is again uniform on `[0, 1)` and is independent of the first binary digit, which
is a fair coin.  This is the missing probabilistic hypothesis of
`DyadicGridLaw.map_gridCylinder_gridMeasure`. -/
theorem map_shiftBit_unitMeasure :
    Measure.map shiftBit unitMeasure
      = unitMeasure.prod (PMF.uniformOfFintype (Fin 2)).toMeasure := by
  haveI := isProbabilityMeasure_unitMeasure
  have hLHS : Measure.map shiftBit unitMeasure
      = (2 : ℝ≥0∞)⁻¹ • Measure.map (fun y : ℝ => (y, (0 : Fin 2))) unitMeasure
        + (2 : ℝ≥0∞)⁻¹ • Measure.map (fun y : ℝ => (y, (1 : Fin 2))) unitMeasure := by
    conv_lhs => rw [unitMeasure_eq_add_halves]
    rw [Measure.map_add _ _ measurable_shiftBit, map_shiftBit_lower, map_shiftBit_upper]
  rw [hLHS, toMeasure_uniformOfFintype_finTwo, Measure.prod_add, Measure.prod_smul_right,
    Measure.prod_smul_right, Measure.prod_dirac, Measure.prod_dirac]

end ReflectedGMS.DyadicDigitLaw
