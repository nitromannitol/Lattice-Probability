/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Statement.Dimension at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs
import LatticeProb.Bonanno.QuantumZipper.LQG.Local
import Mathlib.Topology.Path
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Statement layer, part 4: the LQG dimension `d_γ` and `ξ = γ/d_γ`

`FOUNDATIONS.md` §8 (block copied verbatim). Sources:
* GM (arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`) l. 202–209: "It is
  shown in [DG19] … that for each γ ∈ (0,2), there is an exponent d_γ > 2 …", (1.1)
  `ξ = ξ_γ := γ/d_γ`.
* Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex` l. 214: "We set d_γ := 2/χ", χ the
  exponent of Ding–Zeitouni–Zhang, arXiv:1807.00422, Thm 1.1 (Liouville graph distance, DZZ
  l. 121–124: least number of Euclidean balls with rational centres of LQG mass ≤ δ² whose union
  contains a path from u to v).
The zero-boundary GFF on the open unit square and its LQG area measure are reused verbatim from
QuantumZipper (`QuantumZipper.IsZeroBoundaryGFFOn`, `QuantumZipper.qAreaMeasureOn`). Decision
D9; deviation F11.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric

/-- the open unit square `(0,1)²` -/
def openSquare : Set ℂ := {z | 0 < z.re ∧ z.re < 1 ∧ 0 < z.im ∧ z.im < 1}
/-- the point of `ℂ` with rational coordinates `c` -/
def ratPt (c : ℚ × ℚ) : ℂ := ⟨(c.1 : ℝ), (c.2 : ℝ)⟩

/-- DZZ's Liouville graph distance (DZZ l. 121–124): least number of open Euclidean balls with
rational centres, each of `μ`-mass ≤ δ², whose union contains a path from `u` to `v`. -/
def lgdDZZ (μ : Measure ℂ) (δ : ℝ) (u v : ℂ) : ℕ∞ :=
  ⨅ (N : ℕ) (_ : ∃ (c : Fin N → ℚ × ℚ) (ρ : Fin N → ℝ) (P : Path u v),
      (∀ i, 0 < ρ i ∧ μ (Metric.ball (ratPt (c i)) (ρ i)) ≤ ENNReal.ofReal (δ ^ 2)) ∧
      ∀ t, ∃ i, P t ∈ Metric.ball (ratPt (c i)) (ρ i)), (N : ℕ∞)

/-- DZZ Thm 1.1 in limit form: for every zero-boundary GFF on the open unit square and fixed
`u ≠ v` inside, a.s. `log D_{γ,δ}(u,v) / log δ⁻¹ → χ` as `δ → 0`. -/
def IsLGDExponent (γ χ : ℝ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → Measure ℂ → ℝ), QuantumZipper.IsZeroBoundaryGFFOn openSquare X P →
    ∀ u ∈ openSquare, ∀ v ∈ openSquare, u ≠ v → ∀ᵐ ω ∂P,
      Tendsto (fun δ : ℝ => Real.log
          (lgdDZZ (QuantumZipper.qAreaMeasureOn γ (X ω) openSquare) δ u v).toNat
        / Real.log δ⁻¹) (𝓝[>] 0) (𝓝 χ)

open Classical in
/-- `χ` of DZZ Thm 1.1; junk `1/2` (d = 4) if no exponent exists -/
def chiDZZ (γ : ℝ) : ℝ := if hχ : ∃ χ : ℝ, 0 < χ ∧ IsLGDExponent γ χ then hχ.choose else 1 / 2
/-- `d_γ := 2/χ` (DG l. 214) -/
def dGamma (γ : ℝ) : ℝ := 2 / chiDZZ γ
/-- `ξ = γ/d_γ` (GM (1.1)) -/
def xiGamma (γ : ℝ) : ℝ := γ / dGamma γ

end LQGMetric
