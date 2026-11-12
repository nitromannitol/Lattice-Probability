/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6Defs at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenObs

/-!
# DDDF §§5.4–6: statements of the scale relations of `λ` (task P2-DDDF6)

DDDF = Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021, `literature/src/1904.08021/tightness.tex`.
Status map: `blueprint/DDDF6-STATUS.md`. Open nodes, stated verbatim from DDDF:

* `S6Eq5_54` — (5.54) = `eq:DGlowerBound` (l. 1004–1010; DG Prop 3.17 + DGo Prop 3.3).
* `S6Eq5_78` — (5.78) = `eq:DGupperQuantile` (l. 1276–1281; "follows the same lines").
* `S6Eq5_76` — (5.76) = `eq:WeakMul` (Prop 26, l. 1262–1267).
* `S6Eq5_77` — (5.77) = `eq:ExpoError` (Prop 26, l. 1268–1272), with `O(√n)` written out.
* `S6Eq6_98` — (6.98) = `eq:AprioriMul` (l. 1608–1612), with `λ_{n+r} := λ_{2^{-(n+r)}}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace LQGMetric
namespace DDDF

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **DDDF (5.54)** (`eq:DGlowerBound`, l. 1004–1010): for fixed `p` and `ε ∈ (0, Q − 2)`, for
`K` large, `ℓ^{(K)}_{1,1}(φ, p) ≥ 2^{-K(1 − ξQ + ξε)}`; written with `ζ = ξε > 0` and
`p ∈ (0, 1/2]`. Here `q` stands for `Q = 2/γ + γ/2`. Open (DG chain). -/
def S6Eq5_54 (ξ q : ℝ) (W : WNSpace → Ω → ℝ) (P : Measure Ω) : Prop :=
  ∀ p : ℝ, 0 < p → p ≤ 1 / 2 → ∀ ζ : ℝ, 0 < ζ → ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K →
    (2 : ℝ) ^ (-((K : ℝ) * (1 - ξ * q + ζ))) ≤ ellN ξ W P K (ENNReal.ofReal p)

/-- **DDDF (5.78)** (`eq:DGupperQuantile`, l. 1276–1281): for each fixed small `ζ > 0`, for `k`
large, `λ_k ≤ 2^{-k(1 − ξQ − ζ)}`. Open (DG chain). -/
def S6Eq5_78 (ξ q : ℝ) (W : WNSpace → Ω → ℝ) (P : Measure Ω) : Prop :=
  ∀ ζ : ℝ, 0 < ζ → ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K →
    lambdaN ξ W P K ≤ (2 : ℝ) ^ (-((K : ℝ) * (1 - ξ * q - ζ)))

/-- **DDDF (5.76)** (`eq:WeakMul`, Prop 26, l. 1262–1267): there is `C` with
`e^{-C√k} λ_n λ_k ≤ λ_{n+k} ≤ e^{C√k} λ_n λ_k` for all `n, k ≥ 1`. Open. -/
def S6Eq5_76 (ξ : ℝ) (W : WNSpace → Ω → ℝ) (P : Measure Ω) : Prop :=
  ∃ C : ℝ, ∀ n k : ℕ, 1 ≤ n → 1 ≤ k →
    Real.exp (-(C * √(k : ℝ))) * lambdaN ξ W P n * lambdaN ξ W P k ≤ lambdaN ξ W P (n + k) ∧
      lambdaN ξ W P (n + k) ≤ Real.exp (C * √(k : ℝ)) * lambdaN ξ W P n * lambdaN ξ W P k

/-- **DDDF (5.77)** (`eq:ExpoError`, Prop 26, l. 1268–1272): `λ_n = 2^{-n(1−ξQ) + O(√n)}`, i.e.
`|log λ_n + n(1 − ξQ) log 2| ≤ C √n` for `n ≥ 1`. -/
def S6Eq5_77 (ξ q : ℝ) (W : WNSpace → Ω → ℝ) (P : Measure Ω) : Prop :=
  ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
    |Real.log (lambdaN ξ W P n) + n * (1 - ξ * q) * Real.log 2| ≤ C * √(n : ℝ)

/-- **DDDF (6.98)** (`eq:AprioriMul`, l. 1608–1612): there is `C` with
`e^{-C} λ_n ≤ λ_{n+r} ≤ e^{C} λ_n` for `n ≥ 0`, `r ∈ [0,1]`, where `λ_{n+r} = λ_{2^{-(n+r)}}`.
Open. -/
def S6Eq6_98 (ξ : ℝ) (W : WNSpace → Ω → ℝ) (P : Measure Ω) : Prop :=
  ∃ C : ℝ, ∀ (n : ℕ) (r : ℝ), 0 ≤ r → r ≤ 1 →
    Real.exp (-C) * lambdaN ξ W P n ≤ lambdaDelta ξ W P ((2 : ℝ) ^ (-((n : ℝ) + r))) ∧
      lambdaDelta ξ W P ((2 : ℝ) ^ (-((n : ℝ) + r))) ≤ Real.exp C * lambdaN ξ W P n

end DDDF
end LQGMetric
