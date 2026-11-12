/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.P10Node at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenObs

/-!
# DDDF Proposition 10 (statement): quantile transfer under a conformal map

Task P2-DDDFRSW; blueprint row DDDF.P10. DDDF = Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021,
`tightness.tex` l. 725–736 (`Prop:RSWconf`), after Dubédat–Falconet arXiv:1809.02607
Props. 4.5–4.6 (DF:534–608). DDDF give no proof; the proof (DF's) combines DDDF Lemma 6
(`l6_*`: `φ̃_{0,n} ∘ F = φ_{0,n} + φ_L + φ_H`, `φ_H` independent of `(φ_{0,n}, φ_L)`, Gaussian
tail for `‖φ_L‖_K`, bounded variance of `φ_H`) with DDDF Lemma 9 (`lemma9_tail`).

Setting (DDDF l. 725–729): `K` compact, `A, B ⊆ K` (compact boundary arcs), `F` conformal on an
open `U ⊇ K` with `|F'| ≥ 1`; `L` is the `e^{ξ φ_{0,n}} ds` distance from `A` to `B` in `K`, and
`L'` the `e^{ξ φ̃_{0,n}} ds` distance from `F(A)` to `F(B)` in `F(K)`. Statement:
∃ `C > 0`, ∀ `l > 0`, `ε < 1/2`:
(1) `P(L ≤ l) ≥ ε ⇒ P(L' ≤ l') ≥ ε/4`; (2) `P(L ≤ l) ≥ 1 − ε ⇒ P(L' ≤ l') ≥ 1 − 3ε`,
`l' = C l ‖F'‖_K e^{C √|log(ε/2C)|}`.

Formalization choices (see DEVIATIONS, proposed D-DDDF-6 and D-DDDF-18):
* `l' = C l ‖F'‖_K e^{C√|log(ε/2C)|}`: DDDF print `‖F'‖_K e^{C√…}` without the factor `l`
  (typo, D-DDDF-6; DF Prop 4.5 has it).
* The conformal maps are those produced by DDDF Lemma 12′ (`L12.lemma12'`): `U` open and
  bounded, `F` holomorphic and injective on `U`, `1 ≤ |F'| ≤ M`, `|F''| ≤ M` on `U`. No convexity
  (DDDF l. 539 assume `U, V` convex; the Lemma 6 kernel bounds do not need it, see
  handoff/P2-DDDFL6C.md).
* `C` is uniform in `n` (DDDF's `C` does not depend on the scale; DF Prop 4.5 is uniform in `δ`).
* Law form: `φ̃_{0,n}` has the law of `φ_{0,n}` (DDDF l. 541–543: `W̃` is a white noise), and the
  two statements only involve the laws of `L` and `L'`, so `L'` is computed with the field
  `φ_{0,n} = phiMN W P 0 n` of the same white noise (D-DDDF-18). The proof builds `φ̃` from the
  coupled noise `coupledNoise h W W'` on an extension carrying an independent `W'` and
  transfers the law of `L'`.
* Probabilities are outer measures `P {…}` of `[0,∞]`-valued lengths (`crossLenIn`), so no
  measurability or finiteness side conditions enter the statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DDDF

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω]

/-- the conformal maps of DDDF Prop 10 as supplied by Lemma 12′ (`L12.lemma12'`):
`F` holomorphic and injective on the bounded open `U ⊇ K`, `1 ≤ |F'| ≤ M`, `|F''| ≤ M` -/
structure P10Map (K U : Set ℂ) (F : ℂ → ℂ) : Prop where
  isOpen : IsOpen U
  bdd : Bornology.IsBounded U
  sub : K ⊆ U
  diff : DifferentiableOn ℂ F U
  inj : InjOn F U
  deriv_bd : ∃ M : ℝ, ∀ z ∈ U, 1 ≤ ‖deriv F z‖ ∧ ‖deriv F z‖ ≤ M ∧ ‖deriv (deriv F) z‖ ≤ M

/-- `‖F'‖_K = sup_K |F'|` -/
def derivSup (F : ℂ → ℂ) (K : Set ℂ) : ℝ := sSup ((fun z => ‖deriv F z‖) '' K)

/-- DDDF's `l' = C l ‖F'‖_K e^{C √|log(ε/2C)|}` (with the factor `l`, D-DDDF-6) -/
def p10Len (C l ε S : ℝ) : ℝ := C * l * S * Real.exp (C * Real.sqrt |Real.log (ε / (2 * C))|)

/-- **DDDF Proposition 10** (`Prop:RSWconf`, l. 725–736) for the field `φ_{0,n}` of the white
noise `W` (statement; law form D-DDDF-18). -/
def Prop10 (ξ : ℝ) (P : Measure Ω) (W : WNSpace → Ω → ℝ) : Prop :=
  ∀ (K A B U : Set ℂ) (F : ℂ → ℂ), IsCompact K → IsCompact A → IsCompact B → A ⊆ K → B ⊆ K →
    P10Map K U F →
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (l ε : ℝ), 0 < l → 0 < ε → ε < 1 / 2 →
      (ENNReal.ofReal ε ≤
          P {ω | crossLenIn ξ (fun x => phiMN W P 0 n x ω) K A B ≤ ENNReal.ofReal l} →
        ENNReal.ofReal (ε / 4) ≤
          P {ω | crossLenIn ξ (fun x => phiMN W P 0 n x ω) (F '' K) (F '' A) (F '' B) ≤
            ENNReal.ofReal (p10Len C l ε (derivSup F K))}) ∧
      (ENNReal.ofReal (1 - ε) ≤
          P {ω | crossLenIn ξ (fun x => phiMN W P 0 n x ω) K A B ≤ ENNReal.ofReal l} →
        ENNReal.ofReal (1 - 3 * ε) ≤
          P {ω | crossLenIn ξ (fun x => phiMN W P 0 n x ω) (F '' K) (F '' A) (F '' B) ≤
            ENNReal.ofReal (p10Len C l ε (derivSup F K))})

end DDDF
end LQGMetric
