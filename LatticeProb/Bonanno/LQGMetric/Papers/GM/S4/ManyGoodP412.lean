/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.ManyGoodP412 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.ManyGood
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.RegularityDet
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.Defs
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_3Tail

/-!
# GM Proposition 4.12: the statement (for WP-M2k)

Source: GM = `literature/src/1905.00383/uniqueness-final.tex`, §4.4, (4.35) (l. 2004–2008),
(4.18) (`eqn-good-annulus-set`, l. 1723–1726), (4.10) (`eqn-good-annulus-set0`, l. 1679–1684),
(4.11) (`eqn-ball-stab-event`, l. 1692–1694), Proposition 4.12 (`prop-stab`, l. 2022–2024).

* `p4K R a ε β = K = ⌊(a/c₂)ε^{-β}⌋ − 1` (GM (4.35) as changed by D-B1 / DV-B12, GM.Eq4.35′:
  `c₂ = regC2const R a = (ℓ/a + 1)e^{ξ/a}`).
* `p4Rads R 𝕣 ε = {r^ε_1, …, r^ε_{⌊μ log₈ ε⁻¹⌋}}` (the radii of T4.2 (1), `R.rr 𝕣 ε k`, D59).
* `zkE … k ω = 𝒵^E_k` (GM (4.18)): pairs `(z,r) ∈ 𝒵_k` (`candSet` of `𝓑^•_{t_k}`, GM (4.10))
  with `E_r(z)`, `Stab_{k,r}(z)` (`stabCond` with `s = s_k`, `t = t_k`, GM (4.11)) and
  `P ∩ B_{λ₂r}(z) ≠ ∅`, `P = sel 𝕫 𝕨 (h ω)` (the geodesic selector of T4.2, D31).
  Indexing: `R.lam 0, …, R.lam 4 = λ₁, …, λ₅` (as in `GeoIterateHyp`).
* `p412Bad = ℰ_𝕣 ∩ {#{k ∈ [0,K] : 𝒵^E_k ≠ ∅} < (1 − ε^θ)K}`.
* `GMP4_12At` — the conclusion of Proposition 4.12: there are `β, θ ∈ (0,1)` (depending only on
  the metric data: `γ, D, c`, the CONF parameters and `χ, χ'`; GM: "depending only on the
  choice of metric `D`", with `χ, χ'` fixed by `D`) with `β < χ/χ'` (GM (4.37)) such that for
  every `a`, every `M > 0` there are `C, ε₀` with `P[p412Bad] ≤ C ε^M` for all dyadic
  `ε = 2^{-n} < ε₀`, uniformly in `𝕣 > 0` and `𝕫, 𝕨 ∈ 𝕣U` with `|𝕫 − 𝕨| ≥ 4ℓ𝕣` (GM l. 1613),
  the field (D57 convention), and (D75) the events `E_r(z)` and the radii `r^ε_k` (the fields
  `E`, `rr` of `RegPar`, quantified after `C, ε₀`): GM's rate depends only on the parameters
  (Thm 4.2: "at a rate depending only on `U, q, ℓ, μ, ν, {λ_i}, ε₀, Λ`").

  Hypotheses on the parameters: GM's `0 < λ₁ < λ₂ ≤ λ₃ ≤ λ₄ < λ₅`, `0 < μ < ν`, the radii of
  T4.2 (1), `ℓ ∈ (0,1)`, `U ⊆ V` bounded (GM L4.11), `a ≤ ℓ` (D-B1: `a` replaced by `min{a, ℓ}`),
  and `λ₄ > 1` (GM l. 2555: "since `λ₄ ≥ 1`", used in the proof of Lemma 4.22 but not among the
  hypotheses of Theorem 4.2; its only application, Prop 4.3, has `λ₄ = 4`).

  Reading (proposed DEVIATIONS entry): `ε` ranges over dyadic values `2^{-n}`, because
  condition 5 of `ℰ_𝕣` (GM l. 1968, `regC5`) — the only source of the balls `B_{λ₂r}(z)` with
  `E_r(z)` in the proof of Prop 4.12 (l. 2231) — is imposed only for `ε ∈ {2^{-n}}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- `K = ⌊(a/c₂)ε^{-β}⌋ − 1` (GM (4.35), D-B1 / DV-B12: GM.Eq4.35′) -/
def p4K (R : RegPar) (a ε β : ℝ) : ℕ := ⌊a / regC2const R a * ε ^ (-β)⌋₊ - 1

/-- the radii `{r^ε_1, …, r^ε_{⌊μ log₈ ε⁻¹⌋}}` of T4.2 (1) at scale `𝕣` (D59) -/
def p4Rads (R : RegPar) (𝕣 ε : ℝ) : Set ℝ :=
  R.rr 𝕣 ε '' Iio ⌊R.μ * Real.logb 8 ε⁻¹⌋₊

section Defs
variable {Ω : Type} [MeasurableSpace Ω]

/-- `𝒵^E_k` (GM (4.18)) -/
def zkE (D : DistC → ContMetric) (sel : ℂ → ℂ → DistC → C(unitInterval, ℂ)) (h : Ω → DistC)
    (R : RegPar) (𝕫 𝕨 : ℂ) (𝕣 ε β : ℝ) (k : ℕ) (ω : Ω) : Set (ℂ × ℝ) :=
  {p | p ∈ candSet (filledBall (D (h ω)) 𝕫 (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω)) (R.lam 0) (R.lam 3) ε
        R.ν 𝕣 (p4Rads R 𝕣 ε) ∧
    h ω ∈ R.E p.2 p.1 ∧
    stabCond (D (h ω)) 𝕫 (s4S D h 𝕫 R.ℓ 𝕣 ε β k ω) (s4T D h 𝕫 R.ℓ 𝕣 ε β k ω) p.1 p.2 ∧
    (range (sel 𝕫 𝕨 (h ω)) ∩ Metric.ball p.1 (R.lam 1 * p.2)).Nonempty}

open scoped Classical in
/-- the exceptional event of Proposition 4.12: `ℰ_𝕣` and fewer than `(1 − ε^θ)K` values
`k ∈ [0,K]` with `𝒵^E_k ≠ ∅` -/
def p412Bad (D : DistC → ContMetric) (sel : ℂ → ℂ → DistC → C(unitInterval, ℂ)) (P : Measure Ω)
    (h : Ω → DistC) (H : ℝ → ℂ → Ω → ℝ) (R : RegPar) (𝕫 𝕨 : ℂ) (𝕣 a ε β θ : ℝ) : Set Ω :=
  regEvent D P h H R 𝕣 a ∩
    {ω | ((((Finset.range (p4K R a ε β + 1)).filter
        (fun k => (zkE D sel h R 𝕫 𝕨 𝕣 ε β k ω).Nonempty)).card : ℕ) : ℝ) <
      (1 - ε ^ θ) * (p4K R a ε β : ℝ)}

end Defs

/-- **GM Proposition 4.12** (`prop-stab`, l. 2022–2024), conclusion, for the metric data
`γ, D, c`, the CONF parameters `cp`, the Hölder exponents `χ < χ'` and the geodesic selector
`sel`. -/
def GMP4_12At (γ : ℝ) (D : DistC → ContMetric) (c : ℝ → ℝ) (cp : CONFParams) (χ χ' : ℝ)
    (sel : ℂ → ℂ → DistC → C(unitInterval, ℂ)) : Prop :=
  ∃ β θ : ℝ, β ∈ Ioo (0 : ℝ) 1 ∧ θ ∈ Ioo (0 : ℝ) 1 ∧ β < χ / χ' ∧
  ∀ R : RegPar, R.ξ = xiGamma γ → R.c = c → R.p = cp → R.χ = χ → R.χ' = χ' →
  0 < R.lam 0 → R.lam 0 < R.lam 1 → R.lam 1 ≤ R.lam 2 → R.lam 2 ≤ R.lam 3 → 1 < R.lam 3 →
  R.lam 3 < R.lam 4 → 0 < R.μ → R.μ < R.ν → R.ℓ ∈ Ioo (0 : ℝ) 1 → R.U ⊆ R.V →
  Bornology.IsBounded R.V →
  ∀ a ∈ Ioo (0 : ℝ) 1, a ≤ R.ℓ → ∀ M : ℝ, 0 < M → ∃ C ε₀ : ℝ, 0 < ε₀ ∧
  ∀ (E : ℝ → ℂ → Set DistC) (rr : ℝ → ℝ → ℕ → ℝ),
  (∀ 𝕣 > 0, ∀ ε ∈ Ioo (0 : ℝ) 1, ∀ k < ⌊R.μ * Real.logb 8 ε⁻¹⌋₊,
    rr 𝕣 ε k ∈ Icc (ε ^ (1 + R.ν) * 𝕣) (ε * 𝕣)) →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P →
    (∀ x y : ℂ, x ≠ y → ∀ᵐ ω ∂P, IsGeod01 (D (h ω)) x y (sel x y (h ω))) →
    ∀ H : ℝ → ℂ → Ω → ℝ, DFGPS.IsCircleAvgVersion h P H →
    ∀ 𝕣 : ℝ, 0 < 𝕣 → ∀ 𝕫 ∈ rScale 𝕣 R.U, ∀ 𝕨 ∈ rScale 𝕣 R.U, 4 * (R.ℓ * 𝕣) ≤ ‖𝕫 - 𝕨‖ →
    ∀ n : ℕ, (2 : ℝ)⁻¹ ^ n < ε₀ →
      P (p412Bad D sel P h H { R with E := E, rr := rr } 𝕫 𝕨 𝕣 a ((2 : ℝ)⁻¹ ^ n) β θ) ≤
        ENNReal.ofReal (C * ((2 : ℝ)⁻¹ ^ n) ^ M)

end LQGMetric.GM
