/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.D5T at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.PsiField
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenBasic

/-!
# DDDF Condition (T) (blueprint node DDDF.D5.T)

DDDF = Ding–Dubédat–Dunlap–Falconet, arXiv:1904.08021, `literature/src/1904.08021/tightness.tex`
l. 950–960 (`DefCoarseGraining`, `eq:AssA`). DDDF: let `π_n(ψ)` be the left–right geodesic of
`[0,1]²` for `e^{ξ ψ_{0,n}} ds`, "chosen among them in some measurable way", and
`π_n^K(ψ) := {P ∈ 𝒫_K : P ∩ π_n(ψ) ≠ ∅}` with `𝒫_K = {2^{-K}([i,i+1] × [j,j+1]) : i, j ∈ ℤ}`
(`Pndef`, l. 322). Condition (T): there are `α > 1`, `c > 0` such that for `K` large

  `sup_{n ≥ K} E[(Σ_{P ∈ π_n^K} e^{2ξψ_{0,K}(P)} / (Σ_{P ∈ π_n^K} e^{ξψ_{0,K}(P)})²)^α]^{1/α}
     ≤ e^{-cK}`,

`ψ_{0,K}(P)` the value at the centre of `P`.

Formalization (deviation D-DDDF-5 / decision D31: measurably selected near-geodesics instead of
"the uppermost geodesic"):

* `T20.blkIdx K`: the indices `(i, j) ∈ [-1, 2^K]²`; every block of `𝒫_K` meeting `[0,1]²` has
  such an index, so `coarseBlocks K γ` (blocks meeting `γ([0,1])`) is DDDF's `π^K` for a path
  `γ` in `[0,1]²`.
* `IsNearGeodSel ξ Q W P η γ`: `γ n ω` is an admissible left–right crossing of `[0,1]²` whose
  `e^{ξψ_{0,n}}`-length is at most `(1+η)` times the crossing length `L^{(n)}_{1,1}(ψ)`, and the
  events `{P ∈ π_n^K}` are measurable ("chosen in some measurable way").
* `ConditionT`: `∃ α > 1, c > 0, K₀` such that for every `η > 0` some measurable
  `(1+η)`-near-geodesic selection satisfies the bound for all `K ≥ K₀`, `n ≥ K`; the moment is a
  lower Lebesgue integral (the ratio is `≤ 1`, so this is DDDF's expectation).
  An exact measurable geodesic is a `(1+η)`-near-geodesic for every `η`, so DDDF's condition
  implies `ConditionT`; DDDF's own verification (Prop 21, l. 972–1018) bounds the ratio for every
  crossing, so it gives `ConditionT` as well.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Real
open scoped ENNReal

namespace LQGMetric
namespace DDDF
open WhiteNoise

namespace T20

/-- indices `(i, j) ∈ [-1, 2^K]²` of the blocks of `𝒫_K` that can meet `[0,1]²` -/
def blkIdx (K : ℕ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-1 : ℤ) (2 ^ K) ×ˢ Finset.Icc (-1 : ℤ) (2 ^ K)

/-- the block `2^{-K}([i, i+1] × [j, j+1])` of `𝒫_K` (DDDF (`Pndef`), l. 322) -/
def dyBlock (K : ℕ) (b : ℤ × ℤ) : Set ℂ :=
  Icc ((b.1 : ℝ) * (2 : ℝ)⁻¹ ^ K) (((b.1 : ℝ) + 1) * (2 : ℝ)⁻¹ ^ K) ×ℂ
    Icc ((b.2 : ℝ) * (2 : ℝ)⁻¹ ^ K) (((b.2 : ℝ) + 1) * (2 : ℝ)⁻¹ ^ K)

/-- the centre of `dyBlock K b` -/
def dyCenter (K : ℕ) (b : ℤ × ℤ) : ℂ :=
  ⟨((b.1 : ℝ) + 1 / 2) * (2 : ℝ)⁻¹ ^ K, ((b.2 : ℝ) + 1 / 2) * (2 : ℝ)⁻¹ ^ K⟩

open Classical in
/-- DDDF's `K`-coarse graining `π^K = {P ∈ 𝒫_K : P ∩ γ ≠ ∅}` of a path `γ : [0,1] → [0,1]²`
(`DefCoarseGraining`, l. 951–954) -/
def coarseBlocks (K : ℕ) (γ : ℝ → ℂ) : Finset (ℤ × ℤ) :=
  (blkIdx K).filter fun b => ∃ t ∈ Icc (0 : ℝ) 1, γ t ∈ dyBlock K b

/-- the Condition (T) ratio `Σ_{P ∈ π^K} e^{2ξ f(P)} / (Σ_{P ∈ π^K} e^{ξ f(P)})²`, `f(P)` the
value at the centre of `P` (l. 957) -/
def condTRatio (ξ : ℝ) (K : ℕ) (f : ℂ → ℝ) (γ : ℝ → ℂ) : ℝ :=
  (∑ b ∈ coarseBlocks K γ, exp (2 * ξ * f (dyCenter K b))) /
    (∑ b ∈ coarseBlocks K γ, exp (ξ * f (dyCenter K b))) ^ 2

variable {Ω : Type*} [MeasurableSpace Ω]

/-- a measurable selection of `(1+η)`-near-geodesics for `L^{(n)}_{1,1}(ψ)` (D-DDDF-5) -/
structure IsNearGeodSel (ξ : ℝ) (Q : PsiParams) (W : WNSpace → Ω → ℝ) (P : Measure Ω) (η : ℝ)
    (γ : ℕ → Ω → ℝ → ℂ) : Prop where
  adm : ∀ n ω, AdmPath (rectAB 1 1).toSet (rectAB 1 1).side₁ (rectAB 1 1).side₂ (γ n ω)
  near : ∀ n ω, lfppLen ξ (fun x => psiMN Q W P 0 n x ω) (γ n ω) ≤
    ENNReal.ofReal (1 + η) * rectLen ξ (fun x => psiMN Q W P 0 n x ω) (rectAB 1 1)
  meas : ∀ n K : ℕ, ∀ b : ℤ × ℤ, MeasurableSet {ω | b ∈ coarseBlocks K (γ n ω)}

end T20

open T20

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **DDDF Condition (T)** (`eq:AssA`, l. 956–960; blueprint DDDF.D5.T), with measurably selected
near-geodesics (D-DDDF-5). -/
def ConditionT (ξ : ℝ) (Q : PsiParams) (W : WNSpace → Ω → ℝ) (P : Measure Ω) : Prop :=
  ∃ α : ℝ, 1 < α ∧ ∃ c : ℝ, 0 < c ∧ ∃ K₀ : ℕ, ∀ η : ℝ, 0 < η →
    ∃ γ : ℕ → Ω → ℝ → ℂ, IsNearGeodSel ξ Q W P η γ ∧
      ∀ K : ℕ, K₀ ≤ K → ∀ n : ℕ, K ≤ n →
        (∫⁻ ω, ENNReal.ofReal
            (condTRatio ξ K (fun x => psiMN Q W P 0 K x ω) (γ n ω) ^ α) ∂P) ^ (1 / α) ≤
          ENNReal.ofReal (exp (-(c * K)))

end DDDF
end LQGMetric
