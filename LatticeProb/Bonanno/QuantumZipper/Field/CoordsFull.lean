/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Field.CoordsFull at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Field.Factorization
import LatticeProb.Bonanno.QuantumZipper.Field.Law
import LatticeProb.Bonanno.QuantumZipper.LQG.WedgeProcess

/-!
# Full circle coordinates of a field sample (STATEMENT_SPEC A16)

Laws of wedge-type fields must be compared through circle coordinates jointly with test
pairings, since test pairings alone (supported in the open half-plane) do not determine the LQG
measures, which read circle averages centred on `ℝ`.

We enumerate all pairs (dyadic centre `(a + b i)/2^n`, positive dyadic radius `m/2^j`,
`m ≥ 1`), covering the
circles read by `avgReg` (radius `2^{-k}`) and by `radAvgReg` (radii
`dyadicRound n r + 2^{-n}` at centre `0`, `r ≥ 0`), record the raw values `coordsFull`, and show that
`avgReg`, `radAvgReg` (at `r ≥ 0`), `evalReg`, `pairTest` and `lateralPart` depend only on `coordsFull`. Radius `0` (point masses, whose raw values are junk and could
leak non-intrinsic data such as the canonicalization scale) and negative radii are excluded.
-/

noncomputable section

open MeasureTheory

namespace QuantumZipper

namespace CoordsFull

/-- Enumeration of pairs (dyadic centre, positive dyadic radius `(m+1)/2^j`, `m : ℕ`).
Non-positive radii are deliberately excluded: `foldedCircle z 0` is a point mass, and the raw
value of a field sample at a point mass is junk (it may leak e.g. the canonicalization scale),
while negative radii are meaningless. Only positive radii are read by `avgReg` and `radAvgReg`
(at `r ≥ 0`). -/
def fullIndex (i : ℕ) : ℂ × ℝ :=
  let p := Denumerable.ofNat (ℤ × ℤ × ℕ × ℕ × ℕ) i
  (⟨(p.1 : ℝ) / (2 : ℝ) ^ p.2.2.1, (p.2.1 : ℝ) / (2 : ℝ) ^ p.2.2.1⟩,
    ((p.2.2.2.1 : ℝ) + 1) / (2 : ℝ) ^ p.2.2.2.2)

/-- Raw values of the field at all enumerated folded circles (positive radii only). -/
def coordsFull (x : FieldSample) : ℕ → ℝ := fun i =>
  x (foldedCircle (fullIndex i).1 (fullIndex i).2)

theorem measurable_coordsFull : Measurable coordsFull :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

theorem fullIndex_surj (n : ℕ) (z : ℂ) (m : ℤ) (hm : 0 < m) (j : ℕ) :
    ∃ i, fullIndex i = (dyadicRoundC n z, (m : ℝ) / (2 : ℝ) ^ j) := by
  refine ⟨Encodable.encode ((⌊(2 : ℝ) ^ n * z.re⌋, ⌊(2 : ℝ) ^ n * z.im⌋, n, m.toNat - 1, j) :
    ℤ × ℤ × ℕ × ℕ × ℕ), ?_⟩
  have hc : (((m.toNat - 1 : ℕ) : ℤ) : ℝ) + 1 = (m : ℝ) := by
    have : ((m.toNat - 1 : ℕ) : ℤ) + 1 = m := by omega
    exact_mod_cast this
  simp only [fullIndex, Denumerable.ofNat_encode]
  rw [← hc]
  push_cast
  rfl

theorem coordsFull_apply_eq {x x' : FieldSample} (h : coordsFull x = coordsFull x')
    (n : ℕ) (z : ℂ) (m : ℤ) (hm : 0 < m) (j : ℕ) :
    x (foldedCircle (dyadicRoundC n z) ((m : ℝ) / (2 : ℝ) ^ j)) =
      x' (foldedCircle (dyadicRoundC n z) ((m : ℝ) / (2 : ℝ) ^ j)) := by
  obtain ⟨i, hi⟩ := fullIndex_surj n z m hm j
  have := congrFun h i
  simp only [coordsFull, hi] at this
  exact this

theorem radius_eq_div (k : ℕ) : radius k = ((1 : ℤ) : ℝ) / (2 : ℝ) ^ k := by
  simp [radius, inv_pow]

theorem radAvg_radius_eq_div (n : ℕ) (r : ℝ) :
    dyadicRound n r + radius n = ((⌊(2 : ℝ) ^ n * r⌋ + 1 : ℤ) : ℝ) / (2 : ℝ) ^ n := by
  simp only [dyadicRound, radius, inv_pow]
  push_cast
  field_simp

theorem dyadicRoundC_zero (n : ℕ) : dyadicRoundC n 0 = 0 := by
  simp [dyadicRoundC, dyadicRound]; rfl

theorem avgReg_congr_full {x x' : FieldSample} (h : coordsFull x = coordsFull x') :
    avgReg x = avgReg x' := by
  funext k z
  unfold avgReg
  congr 1
  funext n
  rw [radius_eq_div]
  exact coordsFull_apply_eq h n z 1 one_pos k

/-- `radAvgReg x r` depends only on `coordsFull x` for `r ≥ 0` (the radii read are then
positive; for `r < 0` they may be non-positive, which `coordsFull` does not record). -/
theorem radAvgReg_congr_full {x x' : FieldSample} (h : coordsFull x = coordsFull x')
    {r : ℝ} (hr : 0 ≤ r) : radAvgReg x r = radAvgReg x' r := by
  unfold radAvgReg
  congr 1
  funext n
  rw [radAvg_radius_eq_div, ← dyadicRoundC_zero n]
  have h0 : 0 ≤ ⌊(2 : ℝ) ^ n * r⌋ := Int.floor_nonneg.2 (by positivity)
  exact coordsFull_apply_eq h n 0 _ (by omega) n

theorem evalReg_congr_full {x x' : FieldSample} (h : coordsFull x = coordsFull x') :
    evalReg x = evalReg x' :=
  Factorization.evalReg_congr (avgReg_congr_full h)

theorem pairTest_congr_full {x x' : FieldSample} (h : coordsFull x = coordsFull x') :
    pairTest x = pairTest x' :=
  Factorization.pairTest_congr (avgReg_congr_full h)

theorem lateralPart_congr_full {x x' : FieldSample} (h : coordsFull x = coordsFull x') :
    lateralPart x = lateralPart x' := by
  funext μ
  unfold lateralPart
  rw [evalReg_congr_full h]
  simp only [radAvgReg_congr_full h (norm_nonneg _)]

/-- Generic factorization through `coordsFull`. -/
theorem factor_of_coordsFull {β : Type*} (Φ : FieldSample → β)
    (hΦ : ∀ x x', coordsFull x = coordsFull x' → Φ x = Φ x') :
    ∃ F : (ℕ → ℝ) → β, ∀ x, Φ x = F (coordsFull x) := by
  classical
  refine ⟨fun y => if h : ∃ x, coordsFull x = y then Φ h.choose else Φ 0, fun x => ?_⟩
  have h : ∃ x', coordsFull x' = coordsFull x := ⟨x, rfl⟩
  simp only [h, ↓reduceDIte]
  exact hΦ _ _ h.choose_spec.symm

end CoordsFull

open CoordsFull

variable {Ω : Type*} [MeasurableSpace Ω]

/-- STATEMENT_SPEC A16: the law of a random field through its full circle coordinates jointly
with its raw test pairings on `U`. Laws of wedge-type fields must be compared this way, since
test pairings alone do not determine the LQG measures. -/
def fieldLawFull (U : Set ℂ) (X : Ω → FieldSample) (P : Measure Ω) :
    Measure ((ℕ → ℝ) × (TestFun U → ℝ)) :=
  P.map fun ω => (coordsFull (X ω), fun ρ => pairRaw (X ω) ρ.1)

theorem measurable_fieldLawFull_map {U : Set ℂ} {X : Ω → FieldSample}
    (hX : ∀ μ : Measure ℂ, Measurable fun ω => X ω μ) :
    Measurable fun ω => (coordsFull (X ω), fun ρ : TestFun U => pairRaw (X ω) ρ.1) :=
  (measurable_coordsFull.comp (measurable_pi_iff.mpr hX)).prodMk
    (measurable_pi_iff.mpr fun ρ => measurable_pairRaw_comp hX ρ.1)

end QuantumZipper
