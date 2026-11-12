/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Blueprint.DFGPSInputs at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSExistence
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenObs
import LatticeProb.Bonanno.LQGMetric.Field.ZeroBoundaryExt

/-!
# Blueprint: the DDDF results DFGPS §2 cites (task P2-BP-DF)

Source: DDDF = Ding–Dubédat–Dunlap–Falconet, *Tightness of Liouville first passage percolation
for γ ∈ (0,2)*, arXiv:1904.08021, `literature/src/1904.08021/tightness.tex` (cited `DD:`).
Consumers: DFGPS (arXiv:1905.00380, `lqg-metric-estimates-final.tex`, cited `T:`) Lemma 2.8
(T:872–898: "[DDDF, Theorem 1]" + "see also [DDDF, Section 6.1]", T:883) and Lemma 2.14
(T:1097: "immediate from [DDDF, Theorem 1, Equation (1.3)]"; the inventory finding
`blueprint/DDDF.md` l. 37: the ratio bound needs the quasi-multiplicativity (6.99) = `DDDFEq6_99`).

* `DDDFThm1_1` — DDDF Theorem 1 (1) (DD:155–160).
* `DDDFThm1_2` — DDDF Theorem 1 (2) (DD:160–161).
* `DDDFEq1_3` — DDDF (1.3) (DD:162–166).
* `DDDFProp28` — DDDF Proposition 28 (`Prop:Holder`, DD:1385–1393).
* `DDDFProp29` — DDDF Proposition 29 (`Prop:GffHT`, DD:1500–1506).
* `DDDFEq6_99` — DDDF (6.99) (`eq:MulCont`, DD:1617–1621).

Objects (all built): `φ_{a,b}` = `WhiteNoise.phi` with continuous version `DDDF.phiVer` (DD:289;
DDDF's `φ_δ = φ_{δ,1}`, `φ_{0,n} = φ_{2^{-n},1}` = `DDDF.phiMN W P 0 n`); `λ_δ` = lower median
`DDDF.lambdaDelta` (DD:153), `λ_n` = `DDDF.lambdaN`; the length metric `e^{ξf}ds` restricted to
`S` (internal: paths in `S`) = `DDDF.crossLenIn ξ f S {x} {y}` (DD:457–460); the zero-boundary
GFF on `D` "extended to zero outside of `D`" (DD:160) = the process `X : BddOn D → Ω → ℝ`
(`IsZBGFFProcessExt`) with `p_{t/2} * h (x) = X (p_{t/2}(x − ·) 1_D)` (`heatBdd`).

Readings (proposed DEVIATIONS entries BP-DF-1…4, see the P2-BP-DF report):
* "tight in the uniform topology on `C(K × K, ℝ₊)`": the random functions are continuous on
  `K × K` (asserted) and the set of their laws on `C(K × K, ℝ)` is `IsTightMeasureSet`;
  "any subsequential limit": limits in law along `δ_n → 0`; "bi-Hölder": `∃ c, C, α, β > 0`,
  `c|x−y|^α ≤ d(x,y) ≤ C|x−y|^β` on `K` (DD:155–160, cf. DD:1386–1393).
* `λ_δ` is a deterministic number; it is computed from any white noise `(W', P')` (the law of
  `φ_δ` does not depend on the space; `DDDF.lambdaDelta` takes it as parameter).
* (1.3) "`λ_δ = δ^{1−ξQ} e^{O(√|log δ|)}`" is read as δ → 0: `∃ C, δ₀ > 0` with the two-sided
  bound on `(0, δ₀)`.
* Prop 29's "domain `D`" is read as a bounded open set (as in Theorem 1 (2), DD:160; the
  extension `IsZBGFFProcessExt` is defined for bounded `D`) and "`U ⊂⊂ D`" as `cl U` compact in `D`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.Blueprint

open WhiteNoise DDDF

/-! ## Small definitions -/

/-- the internal length metric of `e^{ξ f} ds` on `S` (DDDF DD:153, 457–460), real-valued
(`toReal`; junk `0` if infinite) -/
def lenMetricOn (ξ : ℝ) (f : ℂ → ℝ) (S : Set ℂ) (x y : ℂ) : ℝ :=
  (crossLenIn ξ f S {x} {y}).toReal

open Classical in
/-- a function viewed as a continuous map (junk `0` if it is not continuous) -/
def toCMap {X : Type*} [TopologicalSpace X] (g : X → ℝ) : C(X, ℝ) :=
  if hg : Continuous g then ⟨g, hg⟩ else 0

/-- `Y` is a continuous (every `ω`), measurable (every `x`) modification of the process `X` -/
def IsContVersion {Ω : Type*} [MeasurableSpace Ω] (X Y : ℂ → Ω → ℝ) (P : Measure Ω) : Prop :=
  (∀ ω, Continuous fun x => Y x ω) ∧ (∀ x, Measurable (Y x)) ∧ ∀ x, Y x =ᵐ[P] X x

open Classical in
/-- the density `p_s(x − ·) 1_U` as an element of `BddOn U` (junk `0` if it is not one, e.g.
for `s ≤ 0`); `p_{t/2} * h̊ (x) = X (heatBdd U (t/2) x)` for the zero-extended zero-boundary GFF
(DD:160, 1498) -/
def heatBdd (U : Set ℂ) (s : ℝ) (x : ℂ) : BddOn U :=
  if hρ : Measurable (U.indicator fun w => heatKernel s x w) ∧
      (∃ C : ℝ, ∀ z, |U.indicator (fun w => heatKernel s x w) z| ≤ C) ∧
      ∀ z ∉ U, U.indicator (fun w => heatKernel s x w) z = 0 then ⟨_, hρ⟩
  else ⟨0, measurable_const, ⟨0, fun z => by simp⟩, fun _ _ => rfl⟩

/-- the random function `(x, y) ↦ a⁻¹ d_f(x, y)` on `[0,1]² × [0,1]²` as a continuous map, where
`d_f` is the internal length metric of `e^{ξ f} ds` on `[0,1]²` -/
def sqMetricC (ξ a : ℝ) (f : ℂ → ℝ) : C(closedUnitSquare × closedUnitSquare, ℝ) :=
  toCMap fun p => a⁻¹ * lenMetricOn ξ f closedUnitSquare p.1 p.2

/-- `d` is bi-Hölder w.r.t. the Euclidean metric on `[0,1]²` -/
def IsBiHolderSq (d : C(closedUnitSquare × closedUnitSquare, ℝ)) : Prop :=
  ∃ c C α β : ℝ, 0 < c ∧ 0 < C ∧ 0 < α ∧ 0 < β ∧ ∀ x y : closedUnitSquare,
    c * ‖(x : ℂ) - y‖ ^ α ≤ d (x, y) ∧ d (x, y) ≤ C * ‖(x : ℂ) - y‖ ^ β

/-! ## DDDF results -/

/-- **DDDF Theorem 1 (1)** (`thm:MainTheorem`, DD:155–160): "If `γ ∈ (0,2)`, then
`(λ_δ⁻¹ e^{ξφ_δ} ds)_{δ∈(0,1)}` is tight with respect to the uniform topology on the space of
continuous functions `[0,1]² × [0,1]² → ℝ⁺`. Furthermore, any subsequential limit is almost
surely bi-Hölder with respect to the Euclidean metric on `[0,1]²`." (`ξ = γ/d_γ`, DD:149;
the metric is restricted to the unit square, DD:153.) -/
def DDDFThm1_1 : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (W : WNSpace → Ω → ℝ), IsWhiteNoise P W →
      let X : ℝ → Ω → C(closedUnitSquare × closedUnitSquare, ℝ) := fun δ ω =>
        sqMetricC (xiGamma γ) (lambdaDelta (xiGamma γ) W P δ) (fun x => phiVer W P δ 1 x ω)
      (∀ δ ∈ Ioo (0 : ℝ) 1, ∀ ω, Continuous fun p : closedUnitSquare × closedUnitSquare =>
        (lambdaDelta (xiGamma γ) W P δ)⁻¹ *
          lenMetricOn (xiGamma γ) (fun x => phiVer W P δ 1 x ω) closedUnitSquare p.1 p.2) ∧
      IsTightMeasureSet {μ | ∃ δ ∈ Ioo (0 : ℝ) 1, μ = P.map (X δ)} ∧
      ∀ (δn : ℕ → ℝ) (ν : ℕ → ProbabilityMeasure C(closedUnitSquare × closedUnitSquare, ℝ))
        (μ : ProbabilityMeasure C(closedUnitSquare × closedUnitSquare, ℝ)),
        (∀ n, δn n ∈ Ioo (0 : ℝ) 1 ∧ (ν n : Measure _) = P.map (X (δn n))) →
        Tendsto δn atTop (𝓝 0) → Tendsto ν atTop (𝓝 μ) →
        ∀ᵐ d ∂(μ : Measure C(closedUnitSquare × closedUnitSquare, ℝ)), IsBiHolderSq d

/-- **DDDF (1.3)** (`eq:BornesExpo`, DD:162–166): "the normalizing constants `(λ_δ)_{δ∈(0,1)}`
satisfy `λ_δ = δ^{1−ξQ} e^{O(√|log δ|)}` where `Q = 2/γ + γ/2`" (read as `δ → 0`). -/
def DDDFEq1_3 : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (W : WNSpace → Ω → ℝ), IsWhiteNoise P W →
      ∃ C δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
        δ ^ (1 - xiGamma γ * Q γ) * Real.exp (-C * Real.sqrt |Real.log δ|) ≤
            lambdaDelta (xiGamma γ) W P δ ∧
          lambdaDelta (xiGamma γ) W P δ ≤
            δ ^ (1 - xiGamma γ * Q γ) * Real.exp (C * Real.sqrt |Real.log δ|)

/-- **DDDF (6.99)** (`eq:MulCont`, DD:1615–1621): "there exists `C > 0` such that for
`δ, δ' ∈ (0,1)` we have `C⁻¹ e^{−C√|log δ ∨ δ'|} λ_δ λ_{δ'} ≤ λ_{δδ'} ≤ C e^{C√|log δ ∨ δ'|}
λ_δ λ_{δ'}`." (`γ ∈ (0,2)`, `ξ = γ/d_γ`, standing assumptions of DDDF §6.) -/
def DDDFEq6_99 : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (W : WNSpace → Ω → ℝ), IsWhiteNoise P W →
      ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Ioo (0 : ℝ) 1, ∀ δ' ∈ Ioo (0 : ℝ) 1,
        C⁻¹ * Real.exp (-C * Real.sqrt |Real.log (max δ δ')|) *
            (lambdaDelta (xiGamma γ) W P δ * lambdaDelta (xiGamma γ) W P δ') ≤
          lambdaDelta (xiGamma γ) W P (δ * δ') ∧
        lambdaDelta (xiGamma γ) W P (δ * δ') ≤
          C * Real.exp (C * Real.sqrt |Real.log (max δ δ')|) *
            (lambdaDelta (xiGamma γ) W P δ * lambdaDelta (xiGamma γ) W P δ')

/-- **DDDF Proposition 29** (`Prop:GffHT`, DD:1498–1506): "Let `h` be a GFF with Dirichlet
boundary condition on a domain `D` and `U ⊂⊂ D` … There exist constants `C, c > 0` such that for
all `t ∈ (0,1/2)`, there is a coupling of `h` and `φ_t =ᵈ φ_{√t}` such that for all `x ≥ 0`,
`P(‖φ_t − p_{t/2} * h‖_U ≥ x) ≤ C e^{−cx²}`." The coupling is a probability space carrying the
zero-boundary GFF `Xh` on `D` (extended by zero), a continuous version `Y` of `p_{t/2} * h` and a
white noise `W` with `φ_t := φ_{√t,1}` built from `W`. -/
def DDDFProp29Coupling (D : TopologicalSpace.Opens ℂ) (U : Set ℂ) (C c t : ℝ) : Prop :=
  ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (Xh : BddOn (D : Set ℂ) → Ω → ℝ)
    (W : WNSpace → Ω → ℝ) (Y : ℂ → Ω → ℝ),
    IsProbabilityMeasure P ∧ IsZBGFFProcessExt D Xh P ∧ IsWhiteNoise P W ∧
    IsContVersion (fun x => Xh (heatBdd D (t / 2) x)) Y P ∧
    ∀ x : ℝ, 0 ≤ x →
      P {ω | ENNReal.ofReal x ≤ ⨆ z ∈ U, ENNReal.ofReal |phiVer W P (Real.sqrt t) 1 z ω - Y z ω|}
        ≤ ENNReal.ofReal (C * Real.exp (-c * x ^ 2))

end LQGMetric.Blueprint
