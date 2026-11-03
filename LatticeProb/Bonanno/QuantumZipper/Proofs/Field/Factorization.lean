/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Field.Factorization at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.LQG.Surfaces
import Mathlib.Logic.Equiv.List

/-!
# Blueprint A4: factorization of field operations through countably many coordinates

Every field operation is built from `avgReg`, which reads a field sample `x` only at the
countably many measures `foldedCircle q (radius k)` with `q` on a dyadic grid. We enumerate these
(`dyadicIndex`), record the raw values (`coords`), and build a measurable reconstruction map
`reconstruct : (ℕ → ℝ) → FieldSample` with `avgReg (reconstruct (coords x)) = avgReg x`.
Consequently every operation `Φ` that depends on `x` only through `avgReg x` satisfies
`Φ x = (Φ ∘ reconstruct) (coords x)`, and `Φ ∘ reconstruct` is measurable whenever `Φ` is.
-/

noncomputable section

open MeasureTheory Filter

namespace QuantumZipper

namespace Factorization

/-- Enumeration of the pairs `(q, k)`, `q = (a + b i)/2^n` dyadic, `k ∈ ℕ`. Surjects onto
every pair `(dyadicRoundC n z, k)` (all `z ∈ ℂ`, in particular all `z ∈ Hbar`). -/
def dyadicIndex (i : ℕ) : ℂ × ℕ :=
  let p := Denumerable.ofNat (ℤ × ℤ × ℕ × ℕ) i
  (⟨(p.1 : ℝ) / (2 : ℝ) ^ p.2.2.1, (p.2.1 : ℝ) / (2 : ℝ) ^ p.2.2.1⟩, p.2.2.2)

theorem dyadicIndex_surj (n k : ℕ) (z : ℂ) : ∃ i, dyadicIndex i = (dyadicRoundC n z, k) := by
  refine ⟨Encodable.encode ((⌊(2 : ℝ) ^ n * z.re⌋, ⌊(2 : ℝ) ^ n * z.im⌋, n, k) :
    ℤ × ℤ × ℕ × ℕ), ?_⟩
  simp only [dyadicIndex, Denumerable.ofNat_encode]
  rfl

/-- The raw coordinates read by `avgReg`. -/
def coords (x : FieldSample) : ℕ → ℝ := fun i =>
  x (foldedCircle (dyadicIndex i).1 (radius (dyadicIndex i).2))

theorem measurable_coords : Measurable coords :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

open Classical in
/-- Measurable reconstruction of a field sample from its coordinates (junk `0` off the family). -/
def reconstruct (y : ℕ → ℝ) : FieldSample := fun μ =>
  if h : ∃ i, foldedCircle (dyadicIndex i).1 (radius (dyadicIndex i).2) = μ
  then y (Nat.find h) else 0

theorem measurable_reconstruct : Measurable reconstruct := by
  refine measurable_pi_iff.2 fun μ => ?_
  unfold reconstruct
  by_cases h : ∃ i, foldedCircle (dyadicIndex i).1 (radius (dyadicIndex i).2) = μ
  · simp only [dif_pos h]; exact measurable_pi_apply _
  · simp only [dif_neg h]; exact measurable_const

open Classical in
theorem reconstruct_coords_apply (x : FieldSample) (i : ℕ) :
    reconstruct (coords x) (foldedCircle (dyadicIndex i).1 (radius (dyadicIndex i).2)) =
      x (foldedCircle (dyadicIndex i).1 (radius (dyadicIndex i).2)) := by
  have h : ∃ j, foldedCircle (dyadicIndex j).1 (radius (dyadicIndex j).2) =
      foldedCircle (dyadicIndex i).1 (radius (dyadicIndex i).2) := ⟨i, rfl⟩
  unfold reconstruct
  rw [dif_pos h]
  exact congrArg x (Nat.find_spec h)

/-- The key identity: `avgReg` only sees the recorded coordinates. -/
theorem avgReg_reconstruct_coords (x : FieldSample) :
    avgReg (reconstruct (coords x)) = avgReg x := by
  funext k z
  unfold avgReg
  congr 1
  funext n
  obtain ⟨i, hi⟩ := dyadicIndex_surj n k z
  have := reconstruct_coords_apply x i
  rw [hi] at this
  exact this

/-! ## Operations determined by `avgReg` -/

theorem evalReg_congr {x x' : FieldSample} (h : avgReg x = avgReg x') :
    evalReg x = evalReg x' := by
  funext ν; unfold evalReg; rw [h]

theorem pairTest_congr {x x' : FieldSample} (h : avgReg x = avgReg x') :
    pairTest x = pairTest x' := by
  funext ρ; unfold pairTest; rw [evalReg_congr h]

theorem coordChange_congr {x x' : FieldSample} (h : avgReg x = avgReg x') (ψ : ℂ → ℂ) (Q : ℝ) :
    coordChange x ψ Q = coordChange x' ψ Q := by
  funext μ; unfold coordChange; rw [evalReg_congr h]

theorem translate_congr {x x' : FieldSample} (h : avgReg x = avgReg x') (a : ℂ) :
    translate x a = translate x' a := by
  funext μ; unfold translate; rw [evalReg_congr h]

theorem bdryApprox_congr {x x' : FieldSample} (h : avgReg x = avgReg x') (γ : ℝ) :
    bdryApprox γ x = bdryApprox γ x' := by
  funext k; unfold bdryApprox; rw [h]

theorem areaApprox_congr {x x' : FieldSample} (h : avgReg x = avgReg x') (γ : ℝ) :
    areaApprox γ x = areaApprox γ x' := by
  funext k; unfold areaApprox; rw [h]

theorem qBoundaryMeasure_congr {x x' : FieldSample} (h : avgReg x = avgReg x') (γ : ℝ) :
    qBoundaryMeasure γ x = qBoundaryMeasure γ x' := by
  unfold qBoundaryMeasure; rw [bdryApprox_congr h]

theorem qAreaMeasure_congr {x x' : FieldSample} (h : avgReg x = avgReg x') (γ : ℝ) :
    qAreaMeasure γ x = qAreaMeasure γ x' := by
  unfold qAreaMeasure; rw [areaApprox_congr h]

theorem scaleParam_congr {x x' : FieldSample} (h : avgReg x = avgReg x') (γ : ℝ) :
    scaleParam γ x = scaleParam γ x' := by
  unfold scaleParam; rw [qAreaMeasure_congr h]

theorem canonical_congr {x x' : FieldSample} (h : avgReg x = avgReg x') (γ : ℝ) :
    canonical γ x = canonical γ x' := by
  rw [canonical_eq_coordChange, canonical_eq_coordChange, scaleParam_congr h,
    coordChange_congr h]

/-! ## Measurable factorizations -/

end Factorization

end QuantumZipper
