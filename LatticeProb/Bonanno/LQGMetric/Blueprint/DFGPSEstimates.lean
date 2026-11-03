/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Blueprint.DFGPSEstimates at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Blueprint.M2Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Blueprint: the DFGPS estimates GM §2.4 cites, GM's tightness facts S2.4a–e, and ξQ < 1 + ξ²/2

Sources:
* DFGPS = Dubédat–Falconet–Gwynne–Pfeffer–Sun, *Weak LQG metrics and Liouville first passage
  percolation*, arXiv:1905.00380, `literature/src/1905.00380/lqg-metric-estimates-final.tex`
  (cited `T:`): Lemma 3.8 (T:1727–1731), Prop 3.18 (T:2247–2254), Lemma 3.20 (T:2317–2330),
  Lemma 3.22 (T:2367–2373), Prop 4.1 (T:2444–2451), Prop 4.3 (T:2593–2600). Conventions T:610–611
  ("polynomially / superpolynomially high probability"); §3–4 setting T:1405: "`D` denotes a weak
  LQG metric and `h` denotes a whole-plane GFF normalized so that `h_1(0) = 0`".
* GM = `literature/src/1905.00383/uniqueness-final.tex` (cited `U:`): the restatements GM Lemmas
  2.8–2.10, 2.12 (U:1022–1084), the unproved tightness claim (U:449–452) in the forms used at
  U:928–933, 1071, 1383–1391, 1434, 1492, 3605, 3644 (decision D14 = DEC-A D-A3: S2.4a–e, no source,
  own proofs), and ξQ − 1 − ξ²/2 < 0 (U:1056, citing Ang Thm 1.9; proved by route B, decision D12).

Reading conventions (proposed deviations BP-M2-D1…D4, see the P2-BP-M2 report):
* "w.p. `1 − O_ε(ε^p)`, uniformly in `𝕣`" = `∃ C ε₀ > 0, ∀ ε ∈ (0,ε₀), ∀ 𝕣 > 0, P[Eᶜ] ≤ C ε^p`
  (`PolyHighProb` with `∃ p > 0`, `SuperPolyHighProb` with `∀ p > 0`); "P[E] ≥ 1 − x" is written
  `P Eᶜ ≤ x` (D30). Events over uncountably many points are evaluated with the outer measure.
* The cited Props quantify their constants before the probability space and the field (D56,
  D57): `PolyHighProbU`/`SuperPolyHighProbU` for DFGPS, `∃ const, ∀ Ω P h` for S2.4a–e.
* `D_h(u,v;V)` is `(D (h ω)).internal V u v ∈ [0,∞]`; `D_h(u,v)` is `(D (h ω)).1 (u, v)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.Blueprint

/-! ## Probability conventions and Euclidean sets -/

section Conv
variable {Ω : Type} [MeasurableSpace Ω]

/-- "`E^ε_𝕣` holds with polynomially high probability as `ε → 0`, at a rate uniform in `𝕣`"
(DFGPS T:610): `∃ p > 0`, `P[(E^ε_𝕣)ᶜ] = O(ε^p)` with constants independent of `𝕣`. -/
def PolyHighProb (P : Measure Ω) (E : ℝ → ℝ → Set Ω) : Prop :=
  ∃ p : ℝ, 0 < p ∧ ∃ C ε₀ : ℝ, 0 < ε₀ ∧
    ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∀ 𝕣 : ℝ, 0 < 𝕣 → P (E ε 𝕣)ᶜ ≤ ENNReal.ofReal (C * ε ^ p)

/-- "… with superpolynomially high probability …" (DFGPS T:611): `P[(E^ε_𝕣)ᶜ] = O(ε^p)` for
every `p > 0`, uniformly in `𝕣`; GM's "`1 − o^∞_ε(ε)`" (U:1080). -/
def SuperPolyHighProb (P : Measure Ω) (E : ℝ → ℝ → Set Ω) : Prop :=
  ∀ p : ℝ, 0 < p → ∃ C ε₀ : ℝ, 0 < ε₀ ∧
    ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∀ 𝕣 : ℝ, 0 < 𝕣 → P (E ε 𝕣)ᶜ ≤ ENNReal.ofReal (C * ε ^ p)

end Conv

/-! ### Uniform-in-the-field conventions (D57)

DFGPS's "with polynomially high probability as `ε → 0`, at a rate uniform in `𝕣`" for "a
whole-plane GFF normalized so that `h_1(0) = 0`" (T:1405): the constants `p, C, ε₀` depend only on
the data of the statement, not on the probability space carrying the field. Events are sets of
fields (`E ε 𝕣 ⊆ DistC`), pulled back along `h`. Consumers that work on one probability space use
`PolyHighProbU.toPolyHighProb` / `SuperPolyHighProbU.toSuperPolyHighProb`. -/

/-- "`E^ε_𝕣` holds with polynomially high probability as `ε → 0`, uniformly in `𝕣`", with
constants uniform over all normalized whole-plane GFFs (D57). -/
def PolyHighProbU (E : ℝ → ℝ → Set DistC) : Prop :=
  ∃ p : ℝ, 0 < p ∧ ∃ C ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsNormalizedWPGFF h P → ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∀ 𝕣 : ℝ, 0 < 𝕣 →
        P (h ⁻¹' E ε 𝕣)ᶜ ≤ ENNReal.ofReal (C * ε ^ p)

/-- superpolynomial version of `PolyHighProbU` (D57) -/
def SuperPolyHighProbU (E : ℝ → ℝ → Set DistC) : Prop :=
  ∀ p : ℝ, 0 < p → ∃ C ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsNormalizedWPGFF h P → ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∀ 𝕣 : ℝ, 0 < 𝕣 →
        P (h ⁻¹' E ε 𝕣)ᶜ ≤ ENNReal.ofReal (C * ε ^ p)

theorem PolyHighProbU.toPolyHighProb {E : ℝ → ℝ → Set DistC} (H : PolyHighProbU E)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWPGFF h P) : PolyHighProb P fun ε 𝕣 => h ⁻¹' E ε 𝕣 := by
  obtain ⟨p, hp, C, ε₀, hε₀, H⟩ := H
  exact ⟨p, hp, C, ε₀, hε₀, H P h hh⟩

theorem SuperPolyHighProbU.toSuperPolyHighProb {E : ℝ → ℝ → Set DistC}
    (H : SuperPolyHighProbU E) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsNormalizedWPGFF h P) :
    SuperPolyHighProb P fun ε 𝕣 => h ⁻¹' E ε 𝕣 := by
  intro p hp
  obtain ⟨C, ε₀, hε₀, H⟩ := H p hp
  exact ⟨C, ε₀, hε₀, H P h hh⟩

/-- `r K + z` -/
def scaleSet (r : ℝ) (z : ℂ) (K : Set ℂ) : Set ℂ := (fun x => (r : ℂ) * x + z) '' K

/-- the closed square `[m₁ s, (m₁+1) s] × [m₂ s, (m₂+1) s]` (side `s`, corners in `s ℤ²`) -/
def gridSquare (s : ℝ) (m : ℤ × ℤ) : Set ℂ :=
  {x | m.1 * s ≤ x.re ∧ x.re ≤ (m.1 + 1) * s ∧ m.2 * s ≤ x.im ∧ x.im ≤ (m.2 + 1) * s}

/-- `L` is a line segment, an arc of a circle, or a whole circle (DFGPS T:2445) -/
def IsSegmentOrArc (L : Set ℂ) : Prop :=
  (∃ a b : ℂ, L = segment ℝ a b) ∨
  (∃ (z : ℂ) (ρ θ₁ θ₂ : ℝ), 0 < ρ ∧ θ₁ ≤ θ₂ ∧ θ₂ ≤ θ₁ + 2 * Real.pi ∧
    L = (fun θ : ℝ => z + ρ * Complex.exp (θ * Complex.I)) '' Icc θ₁ θ₂) ∨
  (∃ (z : ℂ) (ρ : ℝ), 0 < ρ ∧ L = Metric.sphere z ρ)

/-! ## DFGPS results (GM §2.4) -/

/-- **DFGPS Lemma 3.8** (`lem-infinite-dist`, T:1727–1731): "Let `h` be a whole-plane GFF
normalized so that `h_1(0) = 0`. Almost surely, for every compact set `K ⊂ ℂ` we have
`lim_{r→∞} D_h(K, ∂B_r(0)) = ∞`. In particular, every closed, `D_h`-bounded subset of `ℂ` is
compact." (`D` a weak LQG metric, T:1405.) Used by GM.S1.1, GM.L3.1 (U:1197). -/
def DFGPSLem3_8 : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (D : DistC → ContMetric) (c : ℝ → ℝ), IsWeakLQGMetric γ D c →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsNormalizedWPGFF h P → ∀ᵐ ω ∂P,
        (∀ K : Set ℂ, IsCompact K →
          Tendsto (fun r : ℝ => setDist (D (h ω)) K (Metric.sphere 0 r)) atTop (𝓝 ⊤)) ∧
        ∀ A : Set ℂ, IsClosed A → (∃ M : ℝ, ∀ u ∈ A, ∀ v ∈ A, (D (h ω)).1 (u, v) ≤ M) →
          IsCompact A

/-- **DFGPS Proposition 3.18** (`prop-holder-uniform`, T:2247–2254): "Fix a compact set `K ⊂ ℂ`
and exponents `χ ∈ (0, ξ(Q−2))` and `χ′ > ξ(Q+2)`. For each `𝕣 > 0`, it holds with polynomially
high probability as `ε → 0`, at a rate which is uniform in `𝕣`, that
`|(u−v)/𝕣|^{χ′} ≤ 𝔠_𝕣⁻¹ e^{−ξh_𝕣(0)} D_h(u,v) ≤ |(u−v)/𝕣|^χ` for all `u,v ∈ 𝕣K` with
`|u−v| ≤ ε𝕣`." (= GM Lemma 2.8 without its internal-metric refinement, U:1022–1030.) -/
def DFGPSProp3_18 : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (D : DistC → ContMetric) (c : ℝ → ℝ), IsWeakLQGMetric γ D c →
    ∀ (K : Set ℂ), IsCompact K → ∀ χ χ' : ℝ, 0 < χ → χ < xiGamma γ * (Q γ - 2) →
      xiGamma γ * (Q γ + 2) < χ' →
    PolyHighProbU fun ε 𝕣 => {g : DistC |
        ∀ u ∈ scaleSet 𝕣 0 K, ∀ v ∈ scaleSet 𝕣 0 K, ‖u - v‖ ≤ ε * 𝕣 →
          ‖(u - v) / 𝕣‖ ^ χ' ≤
            (c 𝕣)⁻¹ * Real.exp (-xiGamma γ * circleAvg g 𝕣 0) * (D g).1 (u, v) ∧
          (c 𝕣)⁻¹ * Real.exp (-xiGamma γ * circleAvg g 𝕣 0) * (D g).1 (u, v) ≤
            ‖(u - v) / 𝕣‖ ^ χ}

/-- **DFGPS Lemma 3.20** (`lem-holder-upper`, T:2317–2330; `K` the fixed compact set of T:2259):
"For each `χ ∈ (0, ξ(Q−2))` and each `𝕣 > 0`, it holds with polynomially high probability as
`ε → 0`, at a rate which is uniform in `𝕣`, that
`𝔠_𝕣⁻¹ e^{−ξh_𝕣(0)} D_h(u,v; B_{2|u−v|}(u)) ≤ |(u−v)/𝕣|^χ` for all `u,v ∈ 𝕣K` with `|u−v| ≤ ε𝕣`.
Furthermore, it also holds with polynomially high probability … that for each `k ∈ ℕ₀` and each
`2^{−k}ε𝕣 × 2^{−k}ε𝕣` square `S` with corners in `2^{−k}ε𝕣ℤ²` which intersects `𝕣K`, we have
`𝔠_𝕣⁻¹ e^{−ξh_𝕣(0)} sup_{u,v∈S} D_h(u,v;S) ≤ (2^{−k}ε)^χ`." First display: GM (2.8) upper half;
second display: GM Lemma 2.9 (U:1034–1040). In the first display we read `u ≠ v` (D55,
DV-AUDM2-1): for `u = v` the ball `B_{2|u−v|}(u)` is empty and the internal metric is `∞`, whereas
the printed bound is `0`; the statement is meant for distinct points (T:2321). Constants uniform in
the field (D57). -/
def DFGPSLem3_20 : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (D : DistC → ContMetric) (c : ℝ → ℝ), IsWeakLQGMetric γ D c →
    ∀ (K : Set ℂ), IsCompact K → ∀ χ : ℝ, 0 < χ → χ < xiGamma γ * (Q γ - 2) →
      PolyHighProbU (fun ε 𝕣 => {g : DistC |
        ∀ u ∈ scaleSet 𝕣 0 K, ∀ v ∈ scaleSet 𝕣 0 K, u ≠ v → ‖u - v‖ ≤ ε * 𝕣 →
          ENNReal.ofReal ((c 𝕣)⁻¹ * Real.exp (-xiGamma γ * circleAvg g 𝕣 0)) *
              (D g).internal (Metric.ball u (2 * ‖u - v‖)) u v ≤
            ENNReal.ofReal (‖(u - v) / 𝕣‖ ^ χ)}) ∧
      PolyHighProbU (fun ε 𝕣 => {g : DistC |
        ∀ (k : ℕ) (m : ℤ × ℤ), (gridSquare ((2 : ℝ)⁻¹ ^ k * ε * 𝕣) m ∩ scaleSet 𝕣 0 K).Nonempty →
          ENNReal.ofReal ((c 𝕣)⁻¹ * Real.exp (-xiGamma γ * circleAvg g 𝕣 0)) *
              internalDiam (D g) (gridSquare ((2 : ℝ)⁻¹ ^ k * ε * 𝕣) m)
                (gridSquare ((2 : ℝ)⁻¹ ^ k * ε * 𝕣) m) ≤
            ENNReal.ofReal (((2 : ℝ)⁻¹ ^ k * ε) ^ χ)})

/-- **DFGPS Lemma 3.22** (`lem-holder-inverse`, T:2367–2373), **in the corrected form GM use**
(GM (2.7), U:1026; BP-M2-D1): "For each `χ′ > ξ(Q+2)` and each `𝕣 > 0`, it holds with
polynomially high probability as `ε → 0`, at a rate which is uniform in `𝕣`, that
`𝔠_𝕣⁻¹ e^{−ξh_𝕣(0)} D_h(u,v) ≥ |(u−v)/𝕣|^{χ′}` for all `u,v ∈ K` with `|u−v| ≤ ε`" — printed
with `u,v ∈ K`, `|u−v| ≤ ε`; the proof (T:2375, union over `B_{ε𝕣}(K) ∩ 2^{−k−2}ε𝕣ℤ²`) and
Prop 3.18 have `u,v ∈ 𝕣K`, `|u−v| ≤ ε𝕣`, which is stated here. -/
def DFGPSLem3_22 : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (D : DistC → ContMetric) (c : ℝ → ℝ), IsWeakLQGMetric γ D c →
    ∀ (K : Set ℂ), IsCompact K → ∀ χ' : ℝ, xiGamma γ * (Q γ + 2) < χ' →
    PolyHighProbU fun ε 𝕣 => {g : DistC |
        ∀ u ∈ scaleSet 𝕣 0 K, ∀ v ∈ scaleSet 𝕣 0 K, ‖u - v‖ ≤ ε * 𝕣 →
          ‖(u - v) / 𝕣‖ ^ χ' ≤
            (c 𝕣)⁻¹ * Real.exp (-xiGamma γ * circleAvg g 𝕣 0) * (D g).1 (u, v)}

/-- **DFGPS Proposition 4.1** (`prop-line-path`, T:2444–2451; = GM Lemma 2.10, U:1047–1054, which
omits the whole-circle case that GM's proof of Lemma 2.11 uses, U:1071): "Let `L ⊂ ℂ` be a compact
set which is either a line segment, an arc of a circle, or a whole circle and fix `b > 0`. For each
`𝕣 > 0` and each `p > 0`, it holds with probability at least `1 − ε^{p²/(2ξ²) + o_ε(1)}` that
`inf{D_h(u,v; B_{ε𝕣}(𝕣L)) : u,v ∈ B_{ε𝕣}(𝕣L), |u−v| ≥ b𝕣} ≥ ε^{p + ξQ − 1 − ξ²/2} 𝔠_𝕣 e^{ξh_𝕣(0)}`,
where the rate of the `o_ε(1)` depends on `L, b, p` but not on `𝕣`." -/
def DFGPSProp4_1 : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (D : DistC → ContMetric) (c : ℝ → ℝ), IsWeakLQGMetric γ D c →
    ∀ (L : Set ℂ), IsSegmentOrArc L → ∀ b : ℝ, 0 < b → ∀ p : ℝ, 0 < p →
    ∀ ζ : ℝ, 0 < ζ → ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsNormalizedWPGFF h P → ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∀ 𝕣 : ℝ, 0 < 𝕣 →
          P (h ⁻¹' {g : DistC | ∀ u ∈ Metric.thickening (ε * 𝕣) (scaleSet 𝕣 0 L),
              ∀ v ∈ Metric.thickening (ε * 𝕣) (scaleSet 𝕣 0 L), b * 𝕣 ≤ ‖u - v‖ →
              ENNReal.ofReal (ε ^ (p + xiGamma γ * Q γ - 1 - xiGamma γ ^ 2 / 2) *
                  scaleFac (xiGamma γ) c g 𝕣 0) ≤
                (D g).internal (Metric.thickening (ε * 𝕣) (scaleSet 𝕣 0 L)) u v})ᶜ ≤
            ENNReal.ofReal (ε ^ (p ^ 2 / (2 * xiGamma γ ^ 2) - ζ))

/-- **DFGPS Proposition 4.3** (`prop-geo-bdy`, T:2593–2600; restated verbatim as GM Lemma 2.12,
U:1077–1084, "with probability `1 − o^∞_ε(ε)`"): "For each `M > 0` and each `𝕣 > 0`, it holds with
superpolynomially high probability as `ε → 0`, at a rate which is uniform in the choice of `𝕣`,
that the following is true. For each `s > 0` for which `𝓑_s(0;D_h) ⊂ B_{ε^{−M}𝕣}(0)` and each
`D_h`-geodesic `P` from `0` to a point outside of `𝓑_s(0;D_h)`,
`area(B_{ε𝕣}(P) ∩ B_{ε𝕣}(∂𝓑_s(0;D_h))) ≤ ε^{2 − 1/M} 𝕣²`." GM use it at centre `𝕫` and for filled
balls (GM.S4.8, derived in M2 from this Prop by IV′, translation invariance and
`∂𝓑^• ⊂ ∂𝓑`). -/
def DFGPSProp4_3 : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (D : DistC → ContMetric) (c : ℝ → ℝ), IsWeakLQGMetric γ D c →
    ∀ M : ℝ, 0 < M →
    SuperPolyHighProbU fun ε 𝕣 => {g : DistC |
        ∀ s : ℝ, 0 < s → ballM (D g) 0 s ⊆ Metric.ball 0 (ε ^ (-M) * 𝕣) →
          ∀ w : ℂ, w ∉ ballM (D g) 0 s → ∀ (G : ℝ → ℂ) (L : ℝ),
            IsGeodesicL (D g) G L 0 w →
            volume (Metric.thickening (ε * 𝕣) (G '' Icc 0 L) ∩
                Metric.thickening (ε * 𝕣) (frontier (ballM (D g) 0 s))) ≤
              ENNReal.ofReal (ε ^ (2 - 1 / M) * 𝕣 ^ 2)}

/-! ## GM's tightness facts S2.4a–e (GM U:449–452; decision D14 = DEC-A D-A3; no proof in GM)

The constants (`s`, `S`, `b`, `A`, `R`) are chosen before the probability space and the field
(D56): GM's tightness is uniform over all whole-plane GFFs, as in the proved `GM.Tight.gm_S2_4*`.
The `.perSpace` adapters below give the earlier per-space shape. -/

/-- **GM.S2.4a** (crossing lower bounds; GM U:449–452 first functional "`(𝔠_r⁻¹e^{−ξh_r(0)}
D_h(rK, r∂U))⁻¹` is tight", used at U:928–933, 1383–1391; centres `z` by IV′, D-A3). No proof in
GM; own proof (D14). (i) for `U` bounded open and `K ⊂ U` compact, `∀ p < 1 ∃ s > 0 ∀ z, r`:
`P[D_h(rK+z, r∂U+z) ≥ s 𝔠_r e^{ξh_r(z)}] ≥ p`; (ii) the separated-points form
`P[D_h(u,v) ≥ s 𝔠_r e^{ξh_r(z)} ∀ u,v ∈ rK+z with |u−v| ≥ br] ≥ p`. -/
def GMS2_4a : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (D : DistC → ContMetric) (c : ℝ → ℝ), IsWeakLQGMetric γ D c →
      (∀ (U K : Set ℂ), IsOpen U → Bornology.IsBounded U → IsCompact K → K ⊆ U →
        ∀ p : ℝ, p < 1 → ∃ s : ℝ, 0 < s ∧
          ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
            (h : Ω → DistC), IsWholePlaneGFF h P → ∀ (z : ℂ) (r : ℝ), 0 < r →
          P {ω | ENNReal.ofReal (s * scaleFac (xiGamma γ) c (h ω) r z) ≤
            setDist (D (h ω)) (scaleSet r z K) (scaleSet r z (frontier U))}ᶜ ≤
              ENNReal.ofReal (1 - p)) ∧
      (∀ (K : Set ℂ), IsCompact K → ∀ b : ℝ, 0 < b → ∀ p : ℝ, p < 1 →
        ∃ s : ℝ, 0 < s ∧
          ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
            (h : Ω → DistC), IsWholePlaneGFF h P → ∀ (z : ℂ) (r : ℝ), 0 < r →
          P {ω | ∀ u ∈ scaleSet r z K, ∀ v ∈ scaleSet r z K, b * r ≤ ‖u - v‖ →
            s * scaleFac (xiGamma γ) c (h ω) r z ≤ (D (h ω)).1 (u, v)}ᶜ ≤ ENNReal.ofReal (1 - p))

/-- **GM.S2.4b** (uniform modulus of continuity; used at U:1071 "any points `u,v ∈ B_𝕣(0)` with
`D_h(u,v) ≥ s𝔠_𝕣e^{ξh_𝕣(0)}` satisfy `|u−v| ≥ b𝕣`", and P3.6 (3.18)). No proof in GM; own proof
(D14): for `K` compact, `∀ s > 0, p < 1 ∃ b > 0 ∀ z, r`:
`P[D_h(u,v) ≤ s 𝔠_r e^{ξh_r(z)} ∀ u,v ∈ rK+z with |u−v| ≤ br] ≥ p`. -/
def GMS2_4b : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (D : DistC → ContMetric) (c : ℝ → ℝ), IsWeakLQGMetric γ D c →
    ∀ (K : Set ℂ), IsCompact K → ∀ s : ℝ, 0 < s → ∀ p : ℝ, p < 1 →
      ∃ b : ℝ, 0 < b ∧
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (h : Ω → DistC), IsWholePlaneGFF h P → ∀ (z : ℂ) (r : ℝ), 0 < r →
          P {ω | ∀ u ∈ scaleSet r z K, ∀ v ∈ scaleSet r z K, ‖u - v‖ ≤ b * r →
            (D (h ω)).1 (u, v) ≤ s * scaleFac (xiGamma γ) c (h ω) r z}ᶜ ≤ ENNReal.ofReal (1 - p)

/-- **GM.S2.4c** (internal diameters; GM U:449–452 second functional "`𝔠_r⁻¹e^{−ξh_r(0)}
sup_{u,v∈rK} D_h(u,v; rU)` is tight", used at U:928–933, 1383–1391). No proof in GM; own proof
(D14), with `U` **bounded and connected** (DA5: otherwise the internal diameter can be `∞`):
`∀ p < 1 ∃ S ∀ z, r`: `P[sup_{u,v∈rK+z} D_h(u,v; rU+z) ≤ S 𝔠_r e^{ξh_r(z)}] ≥ p`. -/
def GMS2_4c : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (D : DistC → ContMetric) (c : ℝ → ℝ), IsWeakLQGMetric γ D c →
    ∀ (U K : Set ℂ), IsOpen U → Bornology.IsBounded U →
      IsPreconnected U → IsCompact K → K ⊆ U → ∀ p : ℝ, p < 1 →
      ∃ S : ℝ, 0 < S ∧
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (h : Ω → DistC), IsWholePlaneGFF h P → ∀ (z : ℂ) (r : ℝ), 0 < r →
          P {ω | internalDiam (D (h ω)) (scaleSet r z K) (scaleSet r z U) ≤
            ENNReal.ofReal (S * scaleFac (xiGamma γ) c (h ω) r z)}ᶜ ≤ ENNReal.ofReal (1 - p)

/-- **GM.S2.4d** (disconnecting path; GM U:1331 condition 3 of `𝖤_r(z)` and U:1391 "by Axiom V
there exists `A > 1` … condition 3 occurs with probability at least …"). No proof in GM; own proof
(D14): `∀ α ∈ (0,1), p < 1 ∃ A > 1 ∀ z, r`: w.p. `≥ p` there is a path in `A_{αr,r}(z)`
disconnecting its inner and outer boundaries (every path from `∂B_{αr}(z)` to `∂B_r(z)` meets it:
`Disconnects` of `Topo/Disconnect.lean`, written out) with `D_h`-length
`≤ A·D_h(∂B_{αr}(z), ∂B_r(z))`. -/
def GMS2_4d : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (D : DistC → ContMetric) (c : ℝ → ℝ), IsWeakLQGMetric γ D c →
    ∀ α : ℝ, 0 < α → α < 1 → ∀ p : ℝ, p < 1 →
      ∃ A : ℝ, 1 < A ∧
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (h : Ω → DistC), IsWholePlaneGFF h P → ∀ (z : ℂ) (r : ℝ), 0 < r →
          P {ω | ∃ (a b : ℝ) (G : ℝ → ℂ), a ≤ b ∧ ContinuousOn G (Icc a b) ∧
            G '' Icc a b ⊆ (annulus z (α * r) r : Set ℂ) ∧
            (∀ (x y : ℂ) (η : Path x y), x ∈ Metric.sphere z (α * r) → y ∈ Metric.sphere z r →
              (range η ∩ G '' Icc a b).Nonempty) ∧
            (D (h ω)).len G a b ≤ ENNReal.ofReal A *
              setDist (D (h ω)) (Metric.sphere z (α * r)) (Metric.sphere z r)}ᶜ ≤
            ENNReal.ofReal (1 - p)

/-- **GM.S2.4e** (geodesic confinement; GM U:1434 "there is some large bounded open set `U` …
the `D_h`-diameter of `B_𝕣(0)` is smaller than the `D_h`-distance from `B_𝕣(0)` to `∂(𝕣U)`",
U:3605 with `B_{2𝕣}(0)`). No proof in GM; own proof (D14; false from Axiom V alone, uses
DFGPS Thm 1.5 and LM Lemma 3.1), with `U = B_R(0)`: `∀ β ∈ (0,1) ∃ R > 1 ∀ z, r`:
`P[sup_{u,v∈B_r(z)} D_h(u,v) < D_h(B_r(z), ∂B_{Rr}(z))] ≥ 1 − β`. -/
def GMS2_4e : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ (D : DistC → ContMetric) (c : ℝ → ℝ), IsWeakLQGMetric γ D c →
    ∀ β : ℝ, 0 < β → β < 1 →
      ∃ R : ℝ, 1 < R ∧
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (h : Ω → DistC), IsWholePlaneGFF h P → ∀ (z : ℂ) (r : ℝ), 0 < r →
          P {ω | (⨆ u ∈ Metric.ball z r, ⨆ v ∈ Metric.ball z r,
              ENNReal.ofReal ((D (h ω)).1 (u, v))) <
            setDist (D (h ω)) (Metric.ball z r) (Metric.sphere z (R * r))}ᶜ ≤ ENNReal.ofReal β

/-! ## ξQ < 1 + ξ²/2 -/

/-- **GM.S2.5** (U:1056, citing Ang Thm 1.9 "`ξQ ≤ 1`", also DFGPS T:2453): "for each
`γ ∈ (0,2)` … `ξQ − 1 − ξ²/2 < 0`". Proved by route B (decision D12), not from Ang. -/
def GMXiQBound : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 → xiGamma γ * Q γ - 1 - xiGamma γ ^ 2 / 2 < 0

/-! ## Adapters to the per-space shape (D56, D57)

For consumers written against the earlier statements, in which `(Ω, P, h)` came before the
constants. Each adapter has the old statement with the same explicit argument order. -/

section PerSpace

theorem DFGPSProp3_18.perSpace (H : DFGPSProp3_18) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (D : DistC → ContMetric) (c : ℝ → ℝ) (hD : IsWeakLQGMetric γ D c) (K : Set ℂ)
    (hK : IsCompact K) (χ χ' : ℝ) (hχ : 0 < χ) (hχQ : χ < xiGamma γ * (Q γ - 2))
    (hχ' : xiGamma γ * (Q γ + 2) < χ') {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsNormalizedWPGFF h P) :
    PolyHighProb P fun ε 𝕣 => {ω |
        ∀ u ∈ scaleSet 𝕣 0 K, ∀ v ∈ scaleSet 𝕣 0 K, ‖u - v‖ ≤ ε * 𝕣 →
          ‖(u - v) / 𝕣‖ ^ χ' ≤
            (c 𝕣)⁻¹ * Real.exp (-xiGamma γ * circleAvg (h ω) 𝕣 0) * (D (h ω)).1 (u, v) ∧
          (c 𝕣)⁻¹ * Real.exp (-xiGamma γ * circleAvg (h ω) 𝕣 0) * (D (h ω)).1 (u, v) ≤
            ‖(u - v) / 𝕣‖ ^ χ} :=
  (H γ hγ hγ2 D c hD K hK χ χ' hχ hχQ hχ').toPolyHighProb P h hh

theorem DFGPSLem3_20.perSpace (H : DFGPSLem3_20) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (D : DistC → ContMetric) (c : ℝ → ℝ) (hD : IsWeakLQGMetric γ D c) (K : Set ℂ)
    (hK : IsCompact K) (χ : ℝ) (hχ : 0 < χ) (hχQ : χ < xiGamma γ * (Q γ - 2))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWPGFF h P) :
    PolyHighProb P (fun ε 𝕣 => {ω |
        ∀ u ∈ scaleSet 𝕣 0 K, ∀ v ∈ scaleSet 𝕣 0 K, u ≠ v → ‖u - v‖ ≤ ε * 𝕣 →
          ENNReal.ofReal ((c 𝕣)⁻¹ * Real.exp (-xiGamma γ * circleAvg (h ω) 𝕣 0)) *
              (D (h ω)).internal (Metric.ball u (2 * ‖u - v‖)) u v ≤
            ENNReal.ofReal (‖(u - v) / 𝕣‖ ^ χ)}) ∧
      PolyHighProb P (fun ε 𝕣 => {ω |
        ∀ (k : ℕ) (m : ℤ × ℤ), (gridSquare ((2 : ℝ)⁻¹ ^ k * ε * 𝕣) m ∩ scaleSet 𝕣 0 K).Nonempty →
          ENNReal.ofReal ((c 𝕣)⁻¹ * Real.exp (-xiGamma γ * circleAvg (h ω) 𝕣 0)) *
              internalDiam (D (h ω)) (gridSquare ((2 : ℝ)⁻¹ ^ k * ε * 𝕣) m)
                (gridSquare ((2 : ℝ)⁻¹ ^ k * ε * 𝕣) m) ≤
            ENNReal.ofReal (((2 : ℝ)⁻¹ ^ k * ε) ^ χ)}) :=
  ⟨(H γ hγ hγ2 D c hD K hK χ hχ hχQ).1.toPolyHighProb P h hh,
    (H γ hγ hγ2 D c hD K hK χ hχ hχQ).2.toPolyHighProb P h hh⟩

theorem DFGPSLem3_22.perSpace (H : DFGPSLem3_22) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (D : DistC → ContMetric) (c : ℝ → ℝ) (hD : IsWeakLQGMetric γ D c) (K : Set ℂ)
    (hK : IsCompact K) (χ' : ℝ) (hχ' : xiGamma γ * (Q γ + 2) < χ')
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWPGFF h P) :
    PolyHighProb P fun ε 𝕣 => {ω |
        ∀ u ∈ scaleSet 𝕣 0 K, ∀ v ∈ scaleSet 𝕣 0 K, ‖u - v‖ ≤ ε * 𝕣 →
          ‖(u - v) / 𝕣‖ ^ χ' ≤
            (c 𝕣)⁻¹ * Real.exp (-xiGamma γ * circleAvg (h ω) 𝕣 0) * (D (h ω)).1 (u, v)} :=
  (H γ hγ hγ2 D c hD K hK χ' hχ').toPolyHighProb P h hh

theorem DFGPSProp4_1.perSpace (H : DFGPSProp4_1) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (D : DistC → ContMetric) (c : ℝ → ℝ) (hD : IsWeakLQGMetric γ D c) (L : Set ℂ)
    (hL : IsSegmentOrArc L) (b : ℝ) (hb : 0 < b) (p : ℝ) (hp : 0 < p)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWPGFF h P) (ζ : ℝ) (hζ : 0 < ζ) : ∃ ε₀ : ℝ, 0 < ε₀ ∧
        ∀ ε ∈ Ioo (0 : ℝ) ε₀, ∀ 𝕣 : ℝ, 0 < 𝕣 →
          P {ω | ∀ u ∈ Metric.thickening (ε * 𝕣) (scaleSet 𝕣 0 L),
              ∀ v ∈ Metric.thickening (ε * 𝕣) (scaleSet 𝕣 0 L), b * 𝕣 ≤ ‖u - v‖ →
              ENNReal.ofReal (ε ^ (p + xiGamma γ * Q γ - 1 - xiGamma γ ^ 2 / 2) *
                  scaleFac (xiGamma γ) c (h ω) 𝕣 0) ≤
                (D (h ω)).internal (Metric.thickening (ε * 𝕣) (scaleSet 𝕣 0 L)) u v}ᶜ ≤
            ENNReal.ofReal (ε ^ (p ^ 2 / (2 * xiGamma γ ^ 2) - ζ)) := by
  obtain ⟨ε₀, hε₀, H⟩ := H γ hγ hγ2 D c hD L hL b hb p hp ζ hζ
  exact ⟨ε₀, hε₀, H P h hh⟩

theorem DFGPSProp4_3.perSpace (H : DFGPSProp4_3) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (D : DistC → ContMetric) (c : ℝ → ℝ) (hD : IsWeakLQGMetric γ D c) (M : ℝ) (hM : 0 < M)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWPGFF h P) :
    SuperPolyHighProb P fun ε 𝕣 => {ω |
        ∀ s : ℝ, 0 < s → ballM (D (h ω)) 0 s ⊆ Metric.ball 0 (ε ^ (-M) * 𝕣) →
          ∀ w : ℂ, w ∉ ballM (D (h ω)) 0 s → ∀ (G : ℝ → ℂ) (L : ℝ),
            IsGeodesicL (D (h ω)) G L 0 w →
            volume (Metric.thickening (ε * 𝕣) (G '' Icc 0 L) ∩
                Metric.thickening (ε * 𝕣) (frontier (ballM (D (h ω)) 0 s))) ≤
              ENNReal.ofReal (ε ^ (2 - 1 / M) * 𝕣 ^ 2)} :=
  (H γ hγ hγ2 D c hD M hM).toSuperPolyHighProb P h hh

theorem GMS2_4a.perSpace (H : GMS2_4a) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (D : DistC → ContMetric) (c : ℝ → ℝ) (hD : IsWeakLQGMetric γ D c)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsWholePlaneGFF h P) :
      (∀ (U K : Set ℂ), IsOpen U → Bornology.IsBounded U → IsCompact K → K ⊆ U →
        ∀ p : ℝ, p < 1 → ∃ s : ℝ, 0 < s ∧ ∀ (z : ℂ) (r : ℝ), 0 < r →
          P {ω | ENNReal.ofReal (s * scaleFac (xiGamma γ) c (h ω) r z) ≤
            setDist (D (h ω)) (scaleSet r z K) (scaleSet r z (frontier U))}ᶜ ≤
              ENNReal.ofReal (1 - p)) ∧
      (∀ (K : Set ℂ), IsCompact K → ∀ b : ℝ, 0 < b → ∀ p : ℝ, p < 1 →
        ∃ s : ℝ, 0 < s ∧ ∀ (z : ℂ) (r : ℝ), 0 < r →
          P {ω | ∀ u ∈ scaleSet r z K, ∀ v ∈ scaleSet r z K, b * r ≤ ‖u - v‖ →
            s * scaleFac (xiGamma γ) c (h ω) r z ≤ (D (h ω)).1 (u, v)}ᶜ ≤
              ENNReal.ofReal (1 - p)) := by
  refine ⟨fun U K hU hUb hK hKU p hp => ?_, fun K hK b hb p hp => ?_⟩
  · obtain ⟨s, hs, Hs⟩ := (H γ hγ hγ2 D c hD).1 U K hU hUb hK hKU p hp
    exact ⟨s, hs, fun z r hr => Hs P h hh z r hr⟩
  · obtain ⟨s, hs, Hs⟩ := (H γ hγ hγ2 D c hD).2 K hK b hb p hp
    exact ⟨s, hs, fun z r hr => Hs P h hh z r hr⟩

theorem GMS2_4b.perSpace (H : GMS2_4b) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (D : DistC → ContMetric) (c : ℝ → ℝ) (hD : IsWeakLQGMetric γ D c)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsWholePlaneGFF h P) (K : Set ℂ) (hK : IsCompact K) (s : ℝ) (hs : 0 < s) (p : ℝ)
    (hp : p < 1) :
        ∃ b : ℝ, 0 < b ∧ ∀ (z : ℂ) (r : ℝ), 0 < r →
          P {ω | ∀ u ∈ scaleSet r z K, ∀ v ∈ scaleSet r z K, ‖u - v‖ ≤ b * r →
            (D (h ω)).1 (u, v) ≤ s * scaleFac (xiGamma γ) c (h ω) r z}ᶜ ≤
              ENNReal.ofReal (1 - p) := by
  obtain ⟨b, hb, Hb⟩ := H γ hγ hγ2 D c hD K hK s hs p hp
  exact ⟨b, hb, fun z r hr => Hb P h hh z r hr⟩

theorem GMS2_4c.perSpace (H : GMS2_4c) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (D : DistC → ContMetric) (c : ℝ → ℝ) (hD : IsWeakLQGMetric γ D c)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsWholePlaneGFF h P) (U K : Set ℂ) (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUc : IsPreconnected U) (hK : IsCompact K) (hKU : K ⊆ U) (p : ℝ) (hp : p < 1) :
        ∃ S : ℝ, 0 < S ∧ ∀ (z : ℂ) (r : ℝ), 0 < r →
          P {ω | internalDiam (D (h ω)) (scaleSet r z K) (scaleSet r z U) ≤
            ENNReal.ofReal (S * scaleFac (xiGamma γ) c (h ω) r z)}ᶜ ≤ ENNReal.ofReal (1 - p) := by
  obtain ⟨S, hS, HS⟩ := H γ hγ hγ2 D c hD U K hU hUb hUc hK hKU p hp
  exact ⟨S, hS, fun z r hr => HS P h hh z r hr⟩

theorem GMS2_4d.perSpace (H : GMS2_4d) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (D : DistC → ContMetric) (c : ℝ → ℝ) (hD : IsWeakLQGMetric γ D c)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsWholePlaneGFF h P) (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (p : ℝ) (hp : p < 1) :
        ∃ A : ℝ, 1 < A ∧ ∀ (z : ℂ) (r : ℝ), 0 < r →
          P {ω | ∃ (a b : ℝ) (G : ℝ → ℂ), a ≤ b ∧ ContinuousOn G (Icc a b) ∧
            G '' Icc a b ⊆ (annulus z (α * r) r : Set ℂ) ∧
            (∀ (x y : ℂ) (η : Path x y), x ∈ Metric.sphere z (α * r) → y ∈ Metric.sphere z r →
              (range η ∩ G '' Icc a b).Nonempty) ∧
            (D (h ω)).len G a b ≤ ENNReal.ofReal A *
              setDist (D (h ω)) (Metric.sphere z (α * r)) (Metric.sphere z r)}ᶜ ≤
            ENNReal.ofReal (1 - p) := by
  obtain ⟨A, hA, HA⟩ := H γ hγ hγ2 D c hD α hα0 hα1 p hp
  exact ⟨A, hA, fun z r hr => HA P h hh z r hr⟩

theorem GMS2_4e.perSpace (H : GMS2_4e) (γ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2)
    (D : DistC → ContMetric) (c : ℝ → ℝ) (hD : IsWeakLQGMetric γ D c)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsWholePlaneGFF h P) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1) :
        ∃ R : ℝ, 1 < R ∧ ∀ (z : ℂ) (r : ℝ), 0 < r →
          P {ω | (⨆ u ∈ Metric.ball z r, ⨆ v ∈ Metric.ball z r,
              ENNReal.ofReal ((D (h ω)).1 (u, v))) <
            setDist (D (h ω)) (Metric.ball z r) (Metric.sphere z (R * r))}ᶜ ≤
              ENNReal.ofReal β := by
  obtain ⟨R, hR, HR⟩ := H γ hγ hγ2 D c hD β hβ0 hβ1
  exact ⟨R, hR, fun z r hr => HR P h hh z r hr⟩

end PerSpace

end LQGMetric.Blueprint
