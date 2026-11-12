/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.CellScaling.ConeDefs at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import Mathlib
import LatticeProb.Bonanno.LQGMetric.Statement.GFF
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTPath2

/-!
These SLE-free definitions describe the cone field, its scale and its rescaling.
They are definitionally equal to the corresponding `MatedCRT` definitions.
The field is written as `LQGMetric.DistC`.

See the joint-scaling identity and DMS [14] Definition 4.10 and Remark 4.4 for the
quantum-cone and circle-average conventions.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.CellScaling

open MatedCRTHarmonic

/-- `Q = 2/γ + γ/2`. -/
def lqgQ (γ : ℝ) : ℝ := 2 / γ + γ / 2

/-- The distribution `φ ↦ ∫ f φ` of a function (junk `0` if `f` is not locally integrable; mathlib `ofFun`). -/
def ofFunC (f : ℂ → ℝ) : LQGMetric.DistC := Distribution.ofFun ⊤ f volume ⊤

/-- The radial profile `z ↦ h_{|z|}(0)` (circle averages about `0`, LQGMetric `circleAvg`). -/
def radialAvg (h : LQGMetric.DistC) : ℂ → ℝ := fun z => LQGMetric.circleAvg h ‖z‖ 0

/-- The lateral part `h − h_{|·|}(0)` (DMS Def 4.10). -/
def lateralPart (h : LQGMetric.DistC) : LQGMetric.DistC := h - ofFunC (radialAvg h)

/-- Last zero on `[0, ∞)` of a path (QuantumZipper `lastZero`): `sup {s ≥ 0 | c s = 0}`. -/
def lastZeroR (c : ℝ → ℝ) : ℝ := sSup {s : ℝ | 0 ≤ s ∧ c s = 0}

/-- **The radial process of the α-quantum cone** (DMS Def 4.10 with Rem 4.4): `A_t = h_{e^{-t}}(0)`;
`A_t = B_t + αt` for `t ≥ 0`; for `t < 0`, `A_t = B̂_{−t} + αt` where `B̂_s + (Q − α)s = c(ℓ + s)` is the part after
its last zero `ℓ` of `c(u) = B'_u + (Q − α)u` (Brownian motion with drift `Q − α` conditioned to stay positive,
DMS Rem 4.4). -/
def coneRadial (γ α : ℝ) (b b' : ℝ≥0 → ℝ) (t : ℝ) : ℝ :=
  if 0 ≤ t then b t.toNNReal + α * t
  else
    (fun c : ℝ → ℝ => c (lastZeroR c - t) + lqgQ γ * t)
      (fun u => b' u.toNNReal + (lqgQ γ - α) * u)

/-- **The circle-average embedding of a quantum cone** : lateral part of the whole-plane GFF `X` plus the
radial function `z ↦ A_{−log|z|}`. -/
def coneField (X : LQGMetric.DistC) (A : ℝ → ℝ) : LQGMetric.DistC :=
  lateralPart X + ofFunC (fun z => A (-Real.log ‖z‖))

/-- Dyadic scale `2^{-k}`. -/
def dyadicScale (k : ℕ) : ℝ := (2 : ℝ) ^ (-(k : ℤ))

/-- The area approximation `2^{-kγ²/2} e^{γ h_{2^{-k}}(z)} dz`. -/
def lqgAreaApprox (γ : ℝ) (h : LQGMetric.DistC) (k : ℕ) : Measure ℂ :=
  volume.withDensity fun z : ℂ =>
    ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * LQGMetric.circleAvg h (dyadicScale k) z))

/-- Vague convergence on `ℂ` (locally finite limit; integrals of compactly supported continuous functions). -/
def IsVagueLimitC (μs : ℕ → Measure ℂ) (μ : Measure ℂ) : Prop :=
  (∀ K : Set ℂ, IsCompact K → μ K < ⊤) ∧
    ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f →
      Tendsto (fun k => ∫ z, f z ∂(μs k)) atTop (𝓝 (∫ z, f z ∂μ))

open Classical in
/-- **The γ-LQG area measure** `A^γ_h` : the vague limit of `lqgAreaApprox γ h` along dyadic scales,
junk `0` if none exists. -/
def lqgArea (γ : ℝ) (h : LQGMetric.DistC) : Measure ℂ :=
  if hx : ∃ μ, IsVagueLimitC (lqgAreaApprox γ h) μ then hx.choose else 0

/-- The radial path `s ↦ A_{−s} + Q s` of the cone (`= h_{e^s}(0) + Q s`). -/
def coneLogRadial (γ α : ℝ) (b b' : ℝ≥0 → ℝ) (s : ℝ) : ℝ := coneRadial γ α b b' (-s) + lqgQ γ * s

/-- **`R_b`** : `R_b = sup {r > 0 | h_r(0) + Q log r = γ⁻¹ log b}`, read off the radial process:
`R_b = exp (sup {s | A_{−s} + Q s = γ⁻¹ log b})`. -/
def coneScale (γ α : ℝ) (b b' : ℝ≥0 → ℝ) (b₀ : ℝ) : ℝ :=
  Real.exp (sSup {s : ℝ | coneLogRadial γ α b b' s = γ⁻¹ * Real.log b₀})

/-- **`h_b`** : `h_b = h(R_b ·) + Q log R_b − γ⁻¹ log b`. -/
def coneRescaleField (γ R b₀ : ℝ) (h : LQGMetric.DistC) : LQGMetric.DistC :=
  LQGMetric.addConst (LQGMetric.affineComp R 0 h) (lqgQ γ * Real.log R - γ⁻¹ * Real.log b₀)

/-- The γ-quantum cone field `h` of the cell model, built from the whole-plane GFF `X` and the two radial Brownian
motions `B, B'` ( with `α = γ`). -/
def coneFieldOf (γ : ℝ) (X : LQGMetric.DistC) (b b' : ℝ≥0 → ℝ) : LQGMetric.DistC :=
  coneField X (coneRadial γ γ b b')

/-- The mesh-`ε` cells `H^ε_x = η([ε(x − 1), εx])`, indexed by `x ∈ ℤ ≅ εℤ`. -/
def meshCells (ε : ℝ) (η : C(ℝ, ℂ)) (x : ℤ) : Set ℂ := η '' Icc (ε * ((x : ℝ) - 1)) (ε * x)

end MatedCRTHarmonic.CellScaling
