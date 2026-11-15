import LatticeProb.Prob.CorrelatedBMOpenWedgeBridge
import LatticeProb.Prob.BrownianOpenExitStopping

/-! # Exit time from a symmetric open wedge -/

set_option autoImplicit false

open Set
open scoped ENNReal NNReal
open MatedCRTHarmonic.MatedCRT

namespace LatticeProb.CorrelatedBM

/-- The open wedge bounded by the lines `b y = ± a x`. -/
def openSymmetricWedge (a b : ℝ) : Set (ℝ × ℝ) :=
  {z | |b * z.2| < a * z.1}

/-- The symmetric wedge is open, for arbitrary real coefficients. -/
theorem isOpen_openSymmetricWedge (a b : ℝ) : IsOpen (openSymmetricWedge a b) := by
  apply isOpen_lt <;> fun_prop

/-- The path started at the point on the symmetry axis corresponding to `q`. -/
noncomputable def wedgeStartedPath (a q : ℝ) (t : ℝ≥0) (ω : Path2) : ℝ × ℝ :=
  (q / a + coneIncr 0 t 0 ω, coneIncr 1 t 0 ω)

/-- The strict wedge barrier is survival of the started path in the open wedge. -/
theorem mem_openSymmetricWedge_iff (a b q : ℝ) (ha : a ≠ 0)
    (t : ℝ≥0) (ω : Path2) :
    wedgeStartedPath a q t ω ∈ openSymmetricWedge a b ↔
      |b * coneIncr 1 t 0 ω| < q + a * coneIncr 0 t 0 ω := by
  change |b * coneIncr 1 t 0 ω| < a * (q / a + coneIncr 0 t 0 ω) ↔ _
  have h : a * (q / a + coneIncr 0 t 0 ω) = q + a * coneIncr 0 t 0 ω := by
    field_simp
  rw [h]

/-- A strict barrier through time `T` is equivalent to the open-wedge exit
 time being strictly larger than `T`. -/
theorem mem_openSymmetricWedgeBarrier_iff_lt_openExitTime (a b q : ℝ) (ha : a ≠ 0)
    (T : ℝ≥0) (ω : Path2) :
    ω ∈ openSymmetricWedgeBarrier a b q T ↔
      (T : ℝ≥0∞) < openExitTime (wedgeStartedPath a q) (openSymmetricWedge a b) ω := by
  have hcont : Continuous (fun t : ℝ≥0 => wedgeStartedPath a q t ω) := by
    simp only [wedgeStartedPath, coneIncr, lrCoord, ↓reduceIte, Fin.isValue, one_ne_zero]
    fun_prop
  rw [lt_iff_not_ge, openExitTime_le_iff_not_mapsTo (isOpen_openSymmetricWedge a b) hcont]
  rw [not_not]
  constructor
  · intro hω t ht
    apply (mem_openSymmetricWedge_iff a b q ha t ω).2
    exact hω t ⟨NNReal.coe_nonneg _, by exact_mod_cast ht.2⟩
  · intro hω t ht
    let s : ℝ≥0 := ⟨t, ht.1⟩
    exact (mem_openSymmetricWedge_iff a b q ha s ω).1 (hω ⟨bot_le, by exact_mod_cast ht.2⟩)

end LatticeProb.CorrelatedBM
