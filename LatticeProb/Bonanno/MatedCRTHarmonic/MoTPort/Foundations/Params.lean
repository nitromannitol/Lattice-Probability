/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTPort.Foundations.Params at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.QuantumZipper.Field.CoordsFull
import LatticeProb.Bonanno.QuantumZipper.LQG.Measures
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Wedge, cone and zipping parameters (DMS Tables 1.1–1.3)

Duplantier–Miller–Sheffield (arXiv:1409.7055v4), L428–471 and L629–660.
For `γ ∈ (0,2)`, `Q = 2/γ + γ/2` (QuantumZipper's `Qc`) and `χ = 2/γ − γ/2` (QuantumZipper's
`chiC` at `κ = γ²`), every parameter of a quantum wedge or cone is an affine function of its
weight `W`. We take `W` as the primary coordinate and define the other parameters from it; each
table entry is then a lemma (`Foundations/ParamsWedge.lean`, `ParamsCone.lean`, `ParamsZip.lean`).

Here: the definitions, `chi`, the thick/thin thresholds, and the bridge to QuantumZipper's
α-wedge (`QuantumZipper.IsQuantumWedge γ α` is parameterized by `α`, the same convention as DMS
(1.4): `W = γ(γ + 2/γ − α)`, so the weight-2 wedge is the γ-wedge).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace MatedCRTHarmonic.MoTPort

open QuantumZipper Real

/-- `χ = 2/γ − γ/2` as QuantumZipper's `chiC κ` at `κ = γ²`. -/
abbrev chi (γ : ℝ) : ℝ := chiC (γ ^ 2)

theorem chi_eq {γ : ℝ} (hγ : 0 < γ) : chi γ = 2 / γ - γ / 2 := by
  simp [chi, chiC, Real.sqrt_sq hγ.le]

theorem chi_eq' {γ : ℝ} (hγ : 0 < γ) : chi γ = (4 - γ ^ 2) / (2 * γ) := by
  rw [chi_eq hγ]; field_simp; ring

/-! ## Table 1.1: wedge parameters as functions of the weight `W` (DMS (1.4), Table 1.1) -/

/-- `α = γ/2 + Q − W/γ` (DMS (1.4): `W = γ(γ/2 + Q − α)`). -/
def wedgeAlpha (γ W : ℝ) : ℝ := γ / 2 + Qc γ - W / γ
/-! ## Table 1.2: cone parameters as functions of the weight `W` (DMS (1.5), Table 1.2) -/

/-- `α = Q − W/(2γ)` (DMS (1.5): `W = 2γ(Q − α)`). -/
def coneAlpha (γ W : ℝ) : ℝ := Qc γ - W / (2 * γ)
/-! ## Table 1.3: zipping -/

set_option hygiene false in
/-- Normalization tactic for the table identities. -/
macro "params_tac" : tactic => `(tactic| (
  have hγ0 : (γ : ℝ) ≠ 0 := ne_of_gt ‹0 < γ›
  have hχ4 : (4 : ℝ) - γ ^ 2 ≠ 0 := by nlinarith
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  simp only [wedgeAlpha, wedgeTheta, wedgeDelta, wedgeA, wedgeDeltaExp, coneAlpha, coneTheta,
    coneDelta, coneA, coneDeltaExp, zipRho, chi_eq' ‹0 < γ›, Qc] <;> (try field_simp) <;> ring))

variable {γ W : ℝ}

/-! ## Thick/thin thresholds (DMS L397–418, Table 1.1 caption) -/

/-! ## Bridge to QuantumZipper's α-wedge -/

end MatedCRTHarmonic.MoTPort
