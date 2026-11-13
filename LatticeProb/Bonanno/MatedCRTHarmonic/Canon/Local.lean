/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Canon.Local at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.Canon.Data
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.JointMeasurable
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.Lemma46
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4F.Prop210Degree47
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.CurveAdapters

/-!
# Canonical localized objects of [18] §4.2

All local objects are defined from the actual area-parametrized curve. Degrees
retain their extended natural values; this is essential before finiteness is
proved. The graph is the Brownian multigraph where it is locally finite.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.Canon

open MatedCRTHarmonic.MatedCRT

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ}
  {U : Ω → ℝ} {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The selected mesh cell contains the first visit time of `z`. -/
def selectedIndex (ε : ℝ) (c : C(ℝ, ℂ)) (z : ℂ) : ℤ :=
  ⌈GMS4b.hitTime c z / ε⌉

/-- A quantum-time cell, exactly [18]'s `H^ε_x`. -/
def cell (ε : ℝ) (c : C(ℝ, ℂ)) (x : ℤ) : Set ℂ :=
  GMS4b.cellOf ε c x

/-- All six point observables are direct views of `GMS4b`'s §4.2 definitions. -/
structure LocalPoint where
  firstHit : ℝ
  selected : ℤ
  DA : ℝ≥0∞
  degreeIn : ℕ∞
  degreeOut : ℕ∞
  uStar : ℝ≥0∞

def localPoint (ε : ℝ) (c : C(ℝ, ℂ)) (z : ℂ) : LocalPoint :=
  { firstHit := GMS4b.hitTime c z
    selected := selectedIndex ε c z
    DA := GMS4b.areaRatio ε c z
    degreeIn := GMS4b.degreeIn ε c z
    degreeOut := GMS4b.degreeOut ε c z
    uStar := GMS4b.uStar ε c z }

def referenceLocalPoint
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (ε : ℝ) (ω : Ω) (z : ℂ) : LocalPoint :=
  localPoint ε (referenceSample D hγ ω).areaCurve z

/-- The Brownian structure graph at a mesh where it is locally finite. -/
def structureGraph (ε : ℝ) (w : Path2) (hlf : IsLocallyFinite ε w) :
    LFMultigraph ℤ (MatedCRT.Edge ε w) :=
  MatedCRT.graph ε w hlf

/-- The first-hit time lies in the half-open interval of the selected cell. -/
theorem firstHit_mem_selectedCellTime {ε : ℝ} (hε : 0 < ε)
    (c : C(ℝ, ℂ)) (z : ℂ) :
    GMS4b.hitTime c z ∈ Ioc
      (ε * ((selectedIndex ε c z : ℝ) - 1))
      (ε * (selectedIndex ε c z : ℝ)) := by
  have hlt := Int.ceil_lt_add_one (GMS4b.hitTime c z / ε)
  have hle := Int.le_ceil (GMS4b.hitTime c z / ε)
  have hlt' : ((selectedIndex ε c z : ℝ) - 1) < GMS4b.hitTime c z / ε := by
    dsimp [selectedIndex]
    linarith
  have hle' : GMS4b.hitTime c z / ε ≤ (selectedIndex ε c z : ℝ) := by
    simpa only [selectedIndex] using hle
  constructor
  · calc
      ε * ((selectedIndex ε c z : ℝ) - 1) < ε * (GMS4b.hitTime c z / ε) :=
        mul_lt_mul_of_pos_left hlt' hε
      _ = GMS4b.hitTime c z := mul_div_cancel₀ _ hε.ne'
  · calc
      GMS4b.hitTime c z = ε * (GMS4b.hitTime c z / ε) := (mul_div_cancel₀ _ hε.ne').symm
      _ ≤ ε * (selectedIndex ε c z : ℝ) := mul_le_mul_of_nonneg_left hle' hε.le

end MatedCRTHarmonic.Canon
