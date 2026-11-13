/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4F.RealObservable at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.JointMeasurable

/-!
# Real representatives of the geometric localized observables

The source uses finite real-valued area ratios and degrees. Lean's geometric
definitions retain infinity until finiteness is established. These total real
representatives agree with the geometric values exactly on their finite event.
-/

set_option autoImplicit false

noncomputable section

namespace MatedCRTHarmonic.GMS4F

/-- The real representative of the area ratio. -/
def realAreaRatio (ε : ℝ) (c : ℝ → ℂ) (z : ℂ) : ℝ :=
  (GMS4b.areaRatio ε c z).toReal

/-- The natural representatives of the two geometric degrees. -/
def natDegreeIn (ε : ℝ) (c : ℝ → ℂ) (z : ℂ) : ℕ :=
  (GMS4b.degreeIn ε c z).toNat

def natDegreeOut (ε : ℝ) (c : ℝ → ℂ) (z : ℂ) : ℕ :=
  (GMS4b.degreeOut ε c z).toNat

/-- The real source density, using the same product formula as
`L27CellModelProp48Data.uStar_formula`. -/
def realUStar (ε : ℝ) (c : ℝ → ℂ) (z : ℂ) : ℝ :=
  realAreaRatio ε c z * ((natDegreeIn ε c z + natDegreeOut ε c z : ℕ) : ℝ)

theorem realUStar_nonneg (ε : ℝ) (c : ℝ → ℂ) (z : ℂ) :
    0 ≤ realUStar ε c z := by
  exact mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _)

/-- Exact identification with (4.19) whenever all three geometric factors
are finite. No assertion is made on the source-excluded infinite event. -/
theorem ofReal_realUStar_eq_geometric
    {ε : ℝ} {c : ℝ → ℂ} {z : ℂ}
    (hDA : GMS4b.areaRatio ε c z ≠ ⊤)
    (hIn : GMS4b.degreeIn ε c z ≠ ⊤)
    (hOut : GMS4b.degreeOut ε c z ≠ ⊤) :
    ENNReal.ofReal (realUStar ε c z) = GMS4b.uStar ε c z := by
  have hIn' : ((natDegreeIn ε c z : ℕ) : ℕ∞) = GMS4b.degreeIn ε c z := by
    exact ENat.natCast_toNat_eq_self.mpr hIn
  have hOut' : ((natDegreeOut ε c z : ℕ) : ℕ∞) = GMS4b.degreeOut ε c z := by
    exact ENat.natCast_toNat_eq_self.mpr hOut
  rw [realUStar, realAreaRatio,
    ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hDA]
  rw [ENNReal.ofReal_natCast]
  have hInR : ((natDegreeIn ε c z : ℕ) : ENNReal) =
      ((GMS4b.degreeIn ε c z : ℕ∞) : ENNReal) :=
    congrArg (fun n : ℕ∞ => (n : ENNReal)) hIn'
  have hOutR : ((natDegreeOut ε c z : ℕ) : ENNReal) =
      ((GMS4b.degreeOut ε c z : ℕ∞) : ENNReal) :=
    congrArg (fun n : ℕ∞ => (n : ENNReal)) hOut'
  change GMS4b.areaRatio ε c z *
      ((natDegreeIn ε c z + natDegreeOut ε c z : ℕ) : ENNReal) =
    GMS4b.areaRatio ε c z *
      (((GMS4b.degreeIn ε c z + GMS4b.degreeOut ε c z : ℕ∞)) : ENNReal)
  rw [Nat.cast_add, ENat.toENNReal_add, hInR, hOutR]

/-- The total real representative never exceeds the extended geometric
density, including on the infinite event. -/
theorem ofReal_realUStar_le_geometric
    (ε : ℝ) (c : ℝ → ℂ) (z : ℂ) :
    ENNReal.ofReal (realUStar ε c z) ≤ GMS4b.uStar ε c z := by
  have hDA := ENNReal.ofReal_toReal_le (a := GMS4b.areaRatio ε c z)
  have hIn : ((natDegreeIn ε c z : ℕ) : ENNReal) ≤
      ((GMS4b.degreeIn ε c z : ℕ∞) : ENNReal) := by
    exact ENat.toENNReal_mono (ENat.natCast_toNat_le_self _)
  have hOut : ((natDegreeOut ε c z : ℕ) : ENNReal) ≤
      ((GMS4b.degreeOut ε c z : ℕ∞) : ENNReal) := by
    exact ENat.toENNReal_mono (ENat.natCast_toNat_le_self _)
  change ENNReal.ofReal (realAreaRatio ε c z *
      ((natDegreeIn ε c z + natDegreeOut ε c z : ℕ) : ℝ)) ≤ _
  rw [realAreaRatio, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_natCast]
  change ENNReal.ofReal (GMS4b.areaRatio ε c z).toReal *
    ((natDegreeIn ε c z + natDegreeOut ε c z : ℕ) : ENNReal) ≤
      GMS4b.areaRatio ε c z *
        (((GMS4b.degreeIn ε c z + GMS4b.degreeOut ε c z : ℕ∞)) : ENNReal)
  simpa only [Nat.cast_add, ENat.toENNReal_add] using
    mul_le_mul' hDA (add_le_add hIn hOut)

/-- Joint measurability of the record-compatible real density. -/
theorem measurable_realUStar {ε : ℝ} (hε : 0 ≤ ε) :
    Measurable fun p : C(ℝ, ℂ) × ℂ => realUStar ε p.1 p.2 := by
  have hDA : Measurable fun p : C(ℝ, ℂ) × ℂ =>
      realAreaRatio ε p.1 p.2 :=
    ENNReal.measurable_toReal.comp (GMS4b.measurable_areaRatio ε)
  have hNat : Measurable fun n : ℕ∞ => n.toNat := measurable_of_countable _
  have hIn : Measurable fun p : C(ℝ, ℂ) × ℂ =>
      natDegreeIn ε p.1 p.2 :=
    hNat.comp (GMS4b.measurable_degreeIn ε)
  have hOut : Measurable fun p : C(ℝ, ℂ) × ℂ =>
      natDegreeOut ε p.1 p.2 :=
    hNat.comp (GMS4b.measurable_degreeOut hε)
  have hCast : Measurable fun n : ℕ => (n : ℝ) := measurable_of_countable _
  exact hDA.mul (hCast.comp (hIn.add hOut))

end MatedCRTHarmonic.GMS4F

