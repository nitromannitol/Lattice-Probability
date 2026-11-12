/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.EventStmts at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.EventDefs

/-!
# GM §5.4–§5.5: statements of Lemmas 5.9, 5.10, 5.11 and Proposition 5.2

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex` (task P2-M2M,
row 16 of `blueprint/M2.md`). Definitions of `E_r`, `𝓖_r` in `EventDefs.lean`.

* `EData.Ranges`: the parameter ranges of GM l. 3183–3186 as sharpened in the proof of Lemma 5.10
  (l. 3322–3326): `δ, Δ ∈ (0,1)`; `b, ρ ∈ (0,1/100)`, `ε₀ ∈ (0, b/100)` (Lemma 5.8);
  `ζ ∈ (0, ε₀/100)`, `a ∈ (0,1)`, `θ ∈ (0, ζ/100)`; `A, M, Λ₀ > 1`; `ζ < δ/100` (D83).
* `L5_9` (`lem-geo-event-msrble`, l. 3293), `L5_10` (`lem-geo-event-prob`, l. 3304),
  `L5_11` (`lem-internal-geo`, l. 3360, deterministic given `E_r`: the a.s. inputs — Weyl scaling for
  the bump function `φ` and the bi-Lipschitz bounds `c_* D ≤ D̃ ≤ C_* D` at `h` and `h − φ` — are
  hypotheses), `P5_2` (`prop-geo-event0`, l. 2731).
* In `P5_2` (C) the random `φ` is `phiChoice` at any pair of hitting points (GM chooses them
  measurably, footnote l. 3344; any choice works); since `𝓖_r` is finite the a.s. quantifier is
  outside the choice of hitting points.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

namespace LQGMetric.GM
open Blueprint

/-- the parameter ranges of GM §5.4 (l. 3183–3186, 3322–3326) -/
def EData.Ranges (S : EData) : Prop :=
  0 < S.ξ ∧ S.δ ∈ Ioo (0 : ℝ) 1 ∧ S.b ∈ Ioo (0 : ℝ) (1 / 100) ∧ S.ρ ∈ Ioo (0 : ℝ) (1 / 100) ∧
  S.ε₀ ∈ Ioo (0 : ℝ) (S.b / 100) ∧ S.Δ ∈ Ioo (0 : ℝ) 1 ∧ S.ζ ∈ Ioo (0 : ℝ) (S.ε₀ / 100) ∧
  S.a ∈ Ioo (0 : ℝ) 1 ∧ S.θ ∈ Ioo (0 : ℝ) (S.ζ / 100) ∧ 1 < S.A ∧ 1 < S.M ∧ 1 < S.Λ₀ ∧
  -- D83: `ζ` is chosen after `δ` (GM l. 3322–3326); GM's own parameters have `ε₀ < δ/500`
  S.ζ < S.δ / 100

/-- the bi-Lipschitz bounds `c_* D ≤ D̃ ≤ C_* D` at a field `g` -/
def BilipAt (D D' : DistC → ContMetric) (cs Cs : ℝ) (g : DistC) : Prop :=
  ∀ x y : ℂ, cs * (D g).1 (x, y) ≤ (D' g).1 (x, y) ∧ (D' g).1 (x, y) ≤ Cs * (D g).1 (x, y)

/-- **GM Lemma 5.9** (`lem-geo-event-msrble`, l. 3293–3302): `E_r` is a.s. determined by
`(h − h_{5r}(0))|_{𝔸_{r/4,4r}(0)}`. -/
def L5_9 : Prop := ∀ {γ : ℝ} {D D' : DistC → ContMetric} {c : ℝ → ℝ} {cs Cs : ℝ},
  PairSetting γ D D' c → RatiosAre D D' cs Cs → 0 < cs → cs ≤ Cs →
  ∀ (S : EData), S.ξ = xiGamma γ → S.c = c → S.cs = cs → S.Cs = Cs → S.Ranges →
  ∀ (r : ℝ), 0 < r → ∀ (U : ℂ → ℂ → Set ℂ) (fb gb : Set ℂ → TestC),
    IsTubeFam S U r → IsBumpChoice S U fb gb r →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P →
    AEEventIn P (fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) (5 * r) 0))
      (annulus 0 (r / 4) (4 * r))) (h ⁻¹' eventE D D' S U fb gb r)

/-- **GM Lemma 5.10** (`lem-geo-event-prob`, l. 3304–3335): the parameters can be chosen depending
only on `𝕡, μ, ν, c_1', c_2'` (here: on `𝕡`, `α`, `p₀`, `c₁`, `c₂`, `η`) so that `P[E_r] ≥ 𝕡` for
`r ∈ ρ⁻¹𝓡_0`; the tubes `U` are those of Lemma 5.8 and the bump functions are chosen as in GM §5.4.1
(deterministic, before the probability space: D79 (3)). -/
def L5_10 : Prop := ∀ {γ : ℝ} {D D' : DistC → ContMetric} {c : ℝ → ℝ} {cs Cs : ℝ},
  PairSetting γ D D' c → RatiosAre D D' cs Cs → 0 < cs → cs < Cs →
  ∀ {α p₀ : ℝ}, 3 / 4 ≤ α → α < 1 → 0 < p₀ → p₀ < 1 → EndpointProp D D' cs Cs α p₀ →
  ∀ {c₁ c₂ η : ℝ}, cs < c₁ → c₁ < c₂ → c₂ < Cs → EtaChoice cs Cs c₁ c₂ η →
  ∀ 𝕡 ∈ Ioo (0 : ℝ) 1, ∃ S : EData, S.ξ = xiGamma γ ∧ S.c = c ∧ S.cs = cs ∧ S.Cs = Cs ∧
    S.c₁ = c₁ ∧ S.η = η ∧ S.Ranges ∧
  ∀ r : ℝ, S.ρ * r ∈ goodRadii D D' α c₁ p₀ →
  ∃ (U : ℂ → ℂ → Set ℂ) (fb gb : Set ℂ → TestC), IsTubeFam S U r ∧ IsBumpChoice S U fb gb r ∧
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ENNReal.ofReal 𝕡 ≤ P (h ⁻¹' eventE D D' S U fb gb r)

/-- **GM Lemma 5.11** (`lem-internal-geo`, l. 3360–3373), deterministic form at a field `g ∈ E_r`:
with `𝕩', 𝕪'` hitting points of `∂B_{3r}(0)` from `𝕫, 𝕨`, `φ` as in (5.35), `Q` a `D_g`-geodesic
from `𝕫` to `𝕨` which enters `B_{2r}(0)`, and `Qφ` a `D_{g−φ}`-geodesic from `𝕫` to `𝕨`, the
shortcut conclusion (5.36) holds with `b₀ = b − 40ε₀`. The a.s. inputs at `g` and `g − φ` are
hypotheses: length spaces, Weyl scaling `D_{g−φ} = e^{−ξφ}·D_g`, `D̃_{g−φ} = e^{−ξφ}·D̃_g`, the
bi-Lipschitz bounds. `0 < 𝔠_r` (Lemma 5.12; D83). -/
def L5_11 : Prop := ∀ {D D' : DistC → ContMetric} {c₂ : ℝ} (S : EData),
  S.Ranges → 0 < S.cs → S.cs < S.c₁ → S.c₁ < c₂ → c₂ < S.Cs → EtaChoice S.cs S.Cs S.c₁ c₂ S.η →
  ∀ (r : ℝ), 0 < r → 0 < S.c r → ∀ (U : ℂ → ℂ → Set ℂ) (fb gb : Set ℂ → TestC),
    IsTubeFam S U r → IsBumpChoice S U fb gb r →
  ∀ (g : DistC) (z w x' y' : ℂ) (Q Qφ : C(unitInterval, ℂ)),
    z ∉ Metric.ball (0 : ℂ) (4 * r) → w ∉ Metric.ball (0 : ℂ) (4 * r) →
    IsHitPt (D g) z x' r → IsHitPt (D g) w y' r →
    let φ := phiChoice S U fb gb r x' y'
    (D g).IsLength → (D' g).IsLength →
    (∀ x y : ℂ, ENNReal.ofReal ((D (subTest g φ)).1 (x, y)) =
      weylScale S.ξ (-testCont φ) (D g) x y) →
    (∀ x y : ℂ, ENNReal.ofReal ((D' (subTest g φ)).1 (x, y)) =
      weylScale S.ξ (-testCont φ) (D' g) x y) →
    BilipAt D D' S.cs S.Cs g → BilipAt D D' S.cs S.Cs (subTest g φ) →
    IsGeod01 (D g) z w Q → (range Q ∩ Metric.ball (0 : ℂ) (2 * r)).Nonempty →
    g ∈ eventE D D' S U fb gb r →
    IsGeod01 (D (subTest g φ)) z w Qφ →
    ShortcutConcl D D' S.cs S.Cs c₂ (S.b - 40 * S.ε₀) r (subTest g φ) Qφ

/-- **GM Proposition 5.2** (`prop-geo-event0`, l. 2731–2752), for an `α` satisfying the conclusion
of Lemma 5.5 and `r ∈ ρ⁻¹𝓡_0` written `ρ r ∈ 𝓡_0`. (A) measurability and `P[E_r] ≥ 𝕡`;
(B) the Dirichlet bound (5.2) on `E_r` (with `|(h,φ)_∇|`, DV-B6); (C) the shortcut (5.3) for
`φ` = (5.35), a.s. for each pair `𝕫, 𝕨 ∈ ℂ ∖ B_{4r}(0)`. `𝓖_r` is finite and its elements are
supported in `𝔸_{r/4,3r}(0)`. D79 (3): the tubes and bumps `U, fb, gb` are deterministic and
chosen before the probability space; `E_r` is invariant under additive constants (GM l. 2801).
D87: a uniform bound `N` on `#𝓖_r` (GM's grid is scale-free; DV-M2N2-a) and the invariance of
`E_r` holds a.s. (`D_{h+c} = e^{ξc}D_h` only a.s.; DV-M2N2-b). -/
def P5_2 : Prop := ∀ {γ : ℝ} {D D' : DistC → ContMetric} {c : ℝ → ℝ} {cs Cs : ℝ},
  PairSetting γ D D' c → RatiosAre D D' cs Cs → 0 < cs → cs < Cs →
  ∀ {α p₀ : ℝ}, 3 / 4 ≤ α → α < 1 → 0 < p₀ → p₀ < 1 → EndpointProp D D' cs Cs α p₀ →
  ∀ {c₁ c₂ η : ℝ}, cs < c₁ → c₁ < c₂ → c₂ < Cs → EtaChoice cs Cs c₁ c₂ η →
  ∀ 𝕡 ∈ Ioo (0 : ℝ) 1, ∃ (S : EData) (b₀ : ℝ), 0 < b₀ ∧ S.ξ = xiGamma γ ∧ S.c = c ∧
    S.cs = cs ∧ S.Cs = Cs ∧ S.c₁ = c₁ ∧ S.η = η ∧ S.Ranges ∧ ∃ N : ℕ,
  ∀ r : ℝ, S.ρ * r ∈ goodRadii D D' α c₁ p₀ →
  ∃ (U : ℂ → ℂ → Set ℂ) (fb gb : Set ℂ → TestC),
    (bumpFam S U fb gb r).Finite ∧ (bumpFam S U fb gb r).ncard ≤ N ∧
    (∀ φ ∈ bumpFam S U fb gb r, tsupport φ ⊆ (annulus 0 (r / 4) (3 * r) : Set ℂ)) ∧
    -- (B)
    (∀ g ∈ eventE D D' S U fb gb r, ∀ φ ∈ bumpFam S U fb gb r,
      |dirInner g φ| + gradEnergy φ / 2 ≤ S.Λ₀) ∧
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P →
      -- (A)
      AEEventIn P (fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) (5 * r) 0))
        (annulus 0 (r / 4) (4 * r))) (h ⁻¹' eventE D D' S U fb gb r) ∧
      -- invariance under additive constants, a.s. (D79 (3), D87 (4), GM l. 2801)
      (∀ᵐ ω ∂P, ∀ c : ℝ, addConst (h ω) c ∈ eventE D D' S U fb gb r ↔
        h ω ∈ eventE D D' S U fb gb r) ∧
      ENNReal.ofReal 𝕡 ≤ P (h ⁻¹' eventE D D' S U fb gb r) ∧
      -- (C)
      (∀ z w : ℂ, z ∉ Metric.ball (0 : ℂ) (4 * r) → w ∉ Metric.ball (0 : ℂ) (4 * r) →
        ∀ᵐ ω ∂P, ∀ x' y' : ℂ, IsHitPt (D (h ω)) z x' r → IsHitPt (D (h ω)) w y' r →
          phiChoice S U fb gb r x' y' ∈ bumpFam S U fb gb r ∧
          ∀ Q Qφ : C(unitInterval, ℂ), IsGeod01 (D (h ω)) z w Q →
            (range Q ∩ Metric.ball (0 : ℂ) (2 * r)).Nonempty → h ω ∈ eventE D D' S U fb gb r →
            IsGeod01 (D (subTest (h ω) (phiChoice S U fb gb r x' y'))) z w Qφ →
            ShortcutConcl D D' cs Cs c₂ b₀ r (subTest (h ω) (phiChoice S U fb gb r x' y')) Qφ)

end LQGMetric.GM
