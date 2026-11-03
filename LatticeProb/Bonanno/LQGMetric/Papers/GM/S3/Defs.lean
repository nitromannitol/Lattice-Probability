/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S3.Defs at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Blueprint.M2Defs
import LatticeProb.Bonanno.LQGMetric.Blueprint.GMWeakUniqueness
import Mathlib.Analysis.SpecialFunctions.Log.Base
import LatticeProb.Bonanno.LQGMetric.Blueprint.LMResults
import LatticeProb.Bonanno.LQGMetric.Blueprint.MQGeodesic
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSEstimatesF
import LatticeProb.Bonanno.LQGMetric.Blueprint.CONFResults
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.SigmaMod

/-!
# GM §3 definitions and the M2 node statements (task P2-M2A, WP-M2a, row 1 of `blueprint/M2.md`)

Verbatim the type-checked code of `blueprint/M2.md` §5 (GM = Gwynne–Miller, arXiv:1905.00383v3,
`literature/src/1905.00383/uniqueness-final.tex`):

* `lowerRatio`, `upperRatio`: the optimal constants `c_*`, `C_*` of GM (1.21), l. 662;
* `GUp`, `GLow`: the events `Ḡ_r(C', β)`, `G̲_r(c', β)` of GM (3.2), (3.3), l. 1210–1217;
* `scaleCount`, `UniqueGeodIn`, `attainedUp`, `attainedLow`, `badScale`: the events (A), (A′), (B)
  of GM Props 3.4–3.6, l. 1251–1297;
* `PairSetting`, `RatiosAre`: the setting of GM §3, l. 1182, and "`c_*`, `C_*` are a.s. the
  deterministic constants `cs`, `Cs`" (BP-M2-6);
* `stopLastExit`, `GeoIterateHyp`: GM Theorem 4.2's hypotheses, l. 1554–1566;
* the statements of the exported M2 nodes as Props (`P2_2`, `L2_7`, `L2_11`, `L3_1`, `P3_2`–`P3_6`,
  `T4_2`, `P4_3`, `P6_1`, `S6_23`, `AsmM2`): an M2 package that needs a node of an unfinished
  package takes it as an argument of this type (`blueprint/M2.md` §4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-! ## M2 definitions (WP-M2a, file `LQGMetric/Papers/GM/S3/Defs.lean`) -/

/-- `c_*(g) = inf_{u≠v} D̃_g(u,v)/D_g(u,v)` (GM (1.21), l. 662) -/
def lowerRatio (D D' : DistC → ContMetric) (g : DistC) : ℝ :=
  ⨅ p : {p : ℂ × ℂ // p.1 ≠ p.2}, (D' g).1 p.1 / (D g).1 p.1

/-- `C_*(g) = sup_{u≠v} D̃_g(u,v)/D_g(u,v)` (GM (1.21)) -/
def upperRatio (D D' : DistC → ContMetric) (g : DistC) : ℝ :=
  ⨆ p : {p : ℂ × ℂ // p.1 ≠ p.2}, (D' g).1 p.1 / (D g).1 p.1

/-- `Ḡ_r(C', β)` (GM (3.2), l. 1210): `∃ 𝕫, 𝕨 ∈ B_r(0)`, `|𝕫 − 𝕨| ≥ βr`, `D̃(𝕫,𝕨) ≥ C' D(𝕫,𝕨)` -/
def GUp (D D' : DistC → ContMetric) (r C' β : ℝ) : Set DistC :=
  {g | ∃ z ∈ Metric.ball (0 : ℂ) r, ∃ w ∈ Metric.ball (0 : ℂ) r,
    β * r ≤ ‖z - w‖ ∧ C' * (D g).1 (z, w) ≤ (D' g).1 (z, w)}

/-- `G̲_r(c', β)` (GM (3.3), l. 1215): the same with `D̃(𝕫,𝕨) ≤ c' D(𝕫,𝕨)` -/
def GLow (D D' : DistC → ContMetric) (r c' β : ℝ) : Set DistC :=
  {g | ∃ z ∈ Metric.ball (0 : ℂ) r, ∃ w ∈ Metric.ball (0 : ℂ) r,
    β * r ≤ ‖z - w‖ ∧ (D' g).1 (z, w) ≤ c' * (D g).1 (z, w)}

/-- the number of `k ∈ ℕ` with `8^{-k}𝕣 ∈ [ε^{1+ν}𝕣, ε𝕣]` satisfying `Q` -/
def scaleCount (ε ν : ℝ) (Q : ℕ → Prop) : ℕ :=
  {k : ℕ | ε ^ (1 + ν) ≤ (8 : ℝ)⁻¹ ^ k ∧ (8 : ℝ)⁻¹ ^ k ≤ ε ∧ Q k}.ncard

/-- the `D`-geodesic from `u` to `v` is unique and contained in `S` -/
def UniqueGeodIn (D : ContMetric) (u v : ℂ) (S : Set ℂ) : Prop :=
  UniqueGeod D u v ∧ ∀ η, IsGeod01 D u v η → range η ⊆ S

/-- the event of GM P3.4 (A) at radius `r` (GM (3.4), l. 1256) -/
def attainedUp (D D' : DistC → ContMetric) (α r C' : ℝ) : Set DistC :=
  {g | ∃ u ∈ Metric.sphere (0 : ℂ) (α * r), ∃ v ∈ Metric.sphere (0 : ℂ) r,
    C' * (D g).1 (u, v) ≤ (D' g).1 (u, v) ∧
    UniqueGeodIn (D g) u v (closure (annulus 0 (α * r) r : Set ℂ))}

/-- the event of GM P3.5 (A′) (l. 1276): `D̃ ≤ c'D` and the `D̃`-geodesic unique in `cl A` -/
def attainedLow (D D' : DistC → ContMetric) (α r c' : ℝ) : Set DistC :=
  {g | ∃ u ∈ Metric.sphere (0 : ℂ) (α * r), ∃ v ∈ Metric.sphere (0 : ℂ) r,
    (D' g).1 (u, v) ≤ c' * (D g).1 (u, v) ∧
    UniqueGeodIn (D' g) u v (closure (annulus 0 (α * r) r : Set ℂ))}

/-- the event of GM P3.6 (B) at radius `r` (l. 1294): every `(u,v) ∈ ∂B_{αr} × ∂B_r` whose
`D`-geodesic is unique and in `cl A_{αr,r}(0)` has `D̃(u,v) ≤ C'D(u,v)` -/
def badScale (D D' : DistC → ContMetric) (α r C' : ℝ) : Set DistC :=
  {g | ∀ u ∈ Metric.sphere (0 : ℂ) (α * r), ∀ v ∈ Metric.sphere (0 : ℂ) r,
    UniqueGeodIn (D g) u v (closure (annulus 0 (α * r) r : Set ℂ)) →
      (D' g).1 (u, v) ≤ C' * (D g).1 (u, v)}

/-- the weak-uniqueness setting of GM §3 (l. 1182): two weak metrics with the same `𝔠` -/
def PairSetting (γ : ℝ) (D D' : DistC → ContMetric) (c : ℝ → ℝ) : Prop :=
  0 < γ ∧ γ < 2 ∧ IsWeakLQGMetric γ D c ∧ IsWeakLQGMetric γ D' c

/-- "`c_*` and `C_*` are a.s. equal to `cs`, `Cs`" for every whole-plane GFF -/
def RatiosAre (D D' : DistC → ContMetric) (cs Cs : ℝ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ᵐ ω ∂P, lowerRatio D D' (h ω) = cs ∧ upperRatio D D' (h ω) = Cs

/-! ## Exported results as Props (statements of `theorem gm_<name>`) -/

/-- GM Proposition 2.2 (l. 890–896) -/
def P2_2 : Prop := ∀ {γ : ℝ} {D D' : DistC → ContMetric} {c : ℝ → ℝ}, PairSetting γ D D' c →
  ∃ C : ℝ, 0 < C ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC), IsWholePlaneGFF h P → ∀ᵐ ω ∂P, ∀ u v : ℂ,
      C⁻¹ * (D (h ω)).1 (u, v) ≤ (D' (h ω)).1 (u, v) ∧ (D' (h ω)).1 (u, v) ≤ C * (D (h ω)).1 (u, v)

/-- GM Lemma 2.7 (l. 964–971) -/
def L2_7 : Prop := ∀ {s p q : ℝ}, 0 < s → 0 < p → p < 1 → 0 < q → q < 1 → ∃ n₀ : ℕ,
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ (Z : Finset ℂ), n₀ ≤ Z.card →
    (∀ z ∈ Z, ∀ w ∈ Z, z ≠ w → 2 * (1 + s) ≤ ‖z - w‖) → ∀ E : ℂ → Set Ω,
    (∀ z ∈ Z, AEEventIn P (fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) (1 + s) z))
      (ballO z 1)) (E z)) →
    (∀ z ∈ Z, ENNReal.ofReal p ≤ P (E z)) → ENNReal.ofReal q ≤ P (⋃ z ∈ Z, E z)

/-- GM Lemma 2.11 (l. 1062–1066) -/
def L2_11 : Prop := ∀ {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}, 0 < γ → γ < 2 →
  IsWeakLQGMetric γ D c → ∀ {s S p : ℝ}, 0 < s → s < S → 0 < p → p < 1 →
  ∃ α₀ : ℝ, 1 / 2 < α₀ ∧ α₀ < 1 ∧ ∀ α ∈ Ico α₀ 1, ∀ (z : ℂ) (r : ℝ), 0 < r →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ENNReal.ofReal p ≤ P {ω | ∀ u ∈ (annulus z (α * r) r : Set ℂ),
      ∀ v ∈ (annulus z (α * r) r : Set ℂ),
        s * scaleFac (xiGamma γ) c (h ω) r z ≤ (D (h ω)).1 (u, v) →
          ENNReal.ofReal (S * scaleFac (xiGamma γ) c (h ω) r z) ≤
            (D (h ω)).internal (annulus z (α * r) r) u v}

/-- GM Lemma 3.1 (l. 1186–1188) with GM.S1.23 (l. 662): `c_*`, `C_*` are a.s. deterministic,
`0 < c_* ≤ C_* < ∞` -/
def L3_1 : Prop := ∀ {γ : ℝ} {D D' : DistC → ContMetric} {c : ℝ → ℝ}, PairSetting γ D D' c →
  ∃ cs Cs : ℝ, 0 < cs ∧ cs ≤ Cs ∧ RatiosAre D D' cs Cs

/-- GM Proposition 3.2 (l. 1230–1232) -/
def P3_2 : Prop := ∀ {γ : ℝ} {D D' : DistC → ContMetric} {c : ℝ → ℝ} {cs Cs : ℝ},
  PairSetting γ D D' c → RatiosAre D D' cs Cs → ∀ {μ ν : ℝ}, 0 < μ → μ < ν → ν < 1 →
  ∃ βb pb : ℝ, βb ∈ Ioo (0 : ℝ) 1 ∧ pb ∈ Ioo (0 : ℝ) 1 ∧ ∀ C' ∈ Ioo (0 : ℝ) Cs, ∃ ε₀ : ℝ, 0 < ε₀ ∧
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ ε ∈ Ioo (0 : ℝ) ε₀,
      μ * Real.logb 8 ε⁻¹ ≤ scaleCount ε ν (fun k =>
        ENNReal.ofReal pb ≤ P (h ⁻¹' GUp D D' ((8 : ℝ)⁻¹ ^ k) C' βb))

/-- GM Proposition 3.3 (l. 1235–1237; `β̲ ∈ (0,1)`, GA S3.3 note) -/
def P3_3 : Prop := ∀ {γ : ℝ} {D D' : DistC → ContMetric} {c : ℝ → ℝ} {cs Cs : ℝ},
  PairSetting γ D D' c → RatiosAre D D' cs Cs → ∀ {μ ν : ℝ}, 0 < μ → μ < ν → ν < 1 →
  ∃ βl pl : ℝ, βl ∈ Ioo (0 : ℝ) 1 ∧ pl ∈ Ioo (0 : ℝ) 1 ∧ ∀ c' : ℝ, cs < c' → ∃ ε₀ : ℝ, 0 < ε₀ ∧
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ ε ∈ Ioo (0 : ℝ) ε₀,
      μ * Real.logb 8 ε⁻¹ ≤ scaleCount ε ν (fun k =>
        ENNReal.ofReal pl ≤ P (h ⁻¹' GLow D D' ((8 : ℝ)⁻¹ ^ k) c' βl))

/-- GM Proposition 3.4 (l. 1251–1261) -/
def P3_4 : Prop := ∀ {γ : ℝ} {D D' : DistC → ContMetric} {c : ℝ → ℝ} {cs Cs : ℝ},
  PairSetting γ D D' c → RatiosAre D D' cs Cs → ∀ {μ ν : ℝ}, 0 < μ → μ < ν → ν < 1 →
  ∃ α₀ p : ℝ, α₀ ∈ Ioo (1 / 2 : ℝ) 1 ∧ p ∈ Ioo (0 : ℝ) 1 ∧ ∀ α ∈ Ico α₀ 1, ∀ C' ∈ Ioo (0 : ℝ) Cs,
  ∃ C'' ∈ Ioo C' Cs, ∀ β ∈ Ioo (0 : ℝ) 1, ∃ ε₀ : ℝ, 0 < ε₀ ∧
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ R : ℝ, 0 < R → ENNReal.ofReal β ≤ P (h ⁻¹' GUp D D' R C'' β) →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀, μ * Real.logb 8 ε⁻¹ ≤ scaleCount ε ν (fun k =>
      ENNReal.ofReal p ≤ P (h ⁻¹' attainedUp D D' α ((8 : ℝ)⁻¹ ^ k * R) C'))

/-- GM Proposition 3.5 (l. 1271–1280), main export to §§4–5 -/
def P3_5 : Prop := ∀ {γ : ℝ} {D D' : DistC → ContMetric} {c : ℝ → ℝ} {cs Cs : ℝ},
  PairSetting γ D D' c → RatiosAre D D' cs Cs → ∀ {μ ν : ℝ}, 0 < μ → μ < ν → ν < 1 →
  ∃ α₀ p : ℝ, α₀ ∈ Ioo (1 / 2 : ℝ) 1 ∧ p ∈ Ioo (0 : ℝ) 1 ∧ ∀ α ∈ Ico α₀ 1, ∀ c' : ℝ, cs < c' →
  ∃ c'' ∈ Ioo cs c', ∀ β ∈ Ioo (0 : ℝ) 1, ∃ ε₀ : ℝ, 0 < ε₀ ∧
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ R : ℝ, 0 < R → ENNReal.ofReal β ≤ P (h ⁻¹' GLow D D' R c'' β) →
    ∀ ε ∈ Ioc (0 : ℝ) ε₀, μ * Real.logb 8 ε⁻¹ ≤ scaleCount ε ν (fun k =>
      ENNReal.ofReal p ≤ P (h ⁻¹' attainedLow D D' α ((8 : ℝ)⁻¹ ^ k * R) c'))

/-- GM Proposition 3.6 (l. 1288–1297), with `(ν − μ)/2` in (B) (deviation GA-5) -/
def P3_6 : Prop := ∀ {γ : ℝ} {D D' : DistC → ContMetric} {c : ℝ → ℝ} {cs Cs : ℝ},
  PairSetting γ D D' c → RatiosAre D D' cs Cs → ∀ {μ ν : ℝ}, 0 < μ → μ < ν → ν < 1 →
  ∃ α₀ p : ℝ, α₀ ∈ Ioo (1 / 2 : ℝ) 1 ∧ p ∈ Ioo (0 : ℝ) 1 ∧ ∀ α ∈ Ico α₀ 1, ∀ C' ∈ Ioo (0 : ℝ) Cs,
  ∃ C'' ∈ Ioo C' Cs, ∀ β ∈ Ioo (0 : ℝ) 1, ∃ ε₀ : ℝ, 0 < ε₀ ∧
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ R : ℝ, 0 < R → ∀ ε ∈ Ioc (0 : ℝ) ε₀,
    (ν - μ) / 2 * Real.logb 8 ε⁻¹ ≤ scaleCount ε ν (fun k =>
      ENNReal.ofReal (1 - p) ≤ P (h ⁻¹' badScale D D' α ((8 : ℝ)⁻¹ ^ k * R) C')) →
    P (h ⁻¹' GUp D D' R C'' β) < ENNReal.ofReal β

/-- the last time `η : [0,1] → ℂ` is in `K`: `T = sup{t ∈ [0,1] : η(t) ∈ K}` (`0` if `η` never
meets `K`; GM l. 1561) -/
def lastExitTime (η : C(unitInterval, ℂ)) (K : Set ℂ) : ℝ :=
  sSup {s : ℝ | ∃ u : unitInterval, (u : ℝ) = s ∧ η u ∈ K}

/-- `η` stopped at the last time `T` it exits `K` and reparametrized on `[0,1]` in proportion
to its own length: `u ↦ η(uT)`, `T = lastExitTime η K` (GM l. 1561: the unit-speed `D_h`-geodesic
stopped at `T`; D89a: for a geodesic `η` parametrized proportionally to its total length `L`, the
stopped path `t ↦ η(min(t,T))` on `[0,1]` would determine `L`, which GM's stopped unit-speed
geodesic does not) -/
def stopLastExit (η : C(unitInterval, ℂ)) (K : Set ℂ) (u : unitInterval) : ℂ :=
  η (Set.projIcc 0 1 zero_le_one ((u : ℝ) * lastExitTime η K))

/-- hypotheses (1)–(4) of GM Theorem 4.2 (l. 1554–1566) for given data. `sel 𝕫 𝕨 g` is the
geodesic `P^{𝕫,𝕨}` of `D_g` (D31 selector; a.s. a `D_h`-geodesic is part of the hypothesis).
D79: `ℛ ⊂ (0, ε₀𝕣]` (GM's `ℛ ⊂ (0, ε₀]` at base scale `𝕣 = 1`, forced by (1)); `E_r(z)` and
`𝔈_r(z)` are unaffected by adding a constant to the field (GM l. 2801); in (4) the conditioning is
on `h|_{ℂ∖B_{λ₃r}(z)}` modulo additive constants (`fieldSigmaClosed0`; GM l. 1200–1205, 2801). -/
def GeoIterateHyp (D : DistC → ContMetric) (sel : ℂ → ℂ → DistC → C(unitInterval, ℂ))
    (μ ν : ℝ) (lam : Fin 5 → ℝ) (𝕡 R ε₀ Λ : ℝ) (Rad : Set ℝ)
    (E : ℝ → ℂ → Set DistC) (Ef : ℝ → ℂ → ℂ → ℂ → Set DistC) : Prop :=
  Rad ⊆ Ioc 0 (ε₀ * R) ∧ 1 < Λ ∧
  -- invariance under additive constants (GM l. 2801)
  (∀ (r : ℝ) (z : ℂ) (g : DistC) (c : ℝ), addConst g c ∈ E r z ↔ g ∈ E r z) ∧
  (∀ (r : ℝ) (z a b : ℂ) (g : DistC) (c : ℝ), addConst g c ∈ Ef r z a b ↔ g ∈ Ef r z a b) ∧
  -- (1) density of radii
  (∀ ε ∈ Ioc (0 : ℝ) ε₀, ∃ rr : ℕ → ℝ, (∀ k < ⌊μ * Real.logb 8 ε⁻¹⌋₊,
      rr k ∈ Icc (ε ^ (1 + ν) * R) (ε * R) ∧ rr k ∈ Rad) ∧
      ∀ k, k + 1 < ⌊μ * Real.logb 8 ε⁻¹⌋₊ → lam 3 / lam 0 ≤ rr k / rr (k + 1)) ∧
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P →
    (∀ a b : ℂ, a ≠ b → ∀ᵐ ω ∂P, IsGeod01 (D (h ω)) a b (sel a b (h ω))) ∧
    -- (2) measurability
    (∀ z : ℂ, ∀ r ∈ Rad, AEEventIn P (fieldSigma (fun ω => addConst (h ω)
        (-circleAvg (h ω) (lam 4 * r) z)) (annulus z (lam 0 * r) (lam 3 * r))) (h ⁻¹' E r z)) ∧
    (∀ z : ℂ, ∀ r ∈ Rad, ∀ a b : ℂ, AEEventIn P (fieldSigma h (ballO z (lam 3 * r)) ⊔
        MeasurableSpace.comap (fun ω => stopLastExit (sel a b (h ω)) (Metric.ball z (lam 3 * r)))
          inferInstance) (h ⁻¹' Ef r z a b)) ∧
    -- (3)
    (∀ z : ℂ, ∀ r ∈ Rad, ENNReal.ofReal 𝕡 ≤ P (h ⁻¹' E r z)) ∧
    -- (4) (4.2)
    (∀ z : ℂ, ∀ r ∈ Rad, ∀ a b : ℂ, a ≠ b → a ∉ Metric.ball z (lam 3 * r) →
      b ∉ Metric.ball z (lam 3 * r) →
      let hit : Set Ω := {ω | (range (sel a b (h ω)) ∩ Metric.ball z (lam 1 * r)).Nonempty}
      let m := fieldSigmaClosed0 h (Metric.ball z (lam 2 * r))ᶜ
      (fun ω => Λ⁻¹ * (P[(h ⁻¹' E r z ∩ hit).indicator (fun _ => (1 : ℝ)) | m]) ω) ≤ᵐ[P]
        P[(h ⁻¹' Ef r z a b ∩ hit).indicator (fun _ => (1 : ℝ)) | m])

/-- GM Theorem 4.2 (l. 1554–1568), with the conclusion as proved (D74): the pair `(z, r)` also
has `𝕫, 𝕨 ∉ B_{λ₄ r}(z)` (GM's proof: `(z, r) ∈ 𝒵_k`, (4.3) l. 1680–1683, and
`𝕨 ∉ B_{3λ₄ε𝕣}(𝓑^•_{t_k})`, l. 1902), which Prop 4.3 needs in Prop 6.1 Step 1 (l. 3590–3599).
D79: the selector is invariant under additive constants (`D_{h+c} = e^{ξc}D_h` has the same
geodesics; GM's `P^{𝕫,𝕨}` is "the" geodesic). D95: `0 < ε₀` (GM l. 1557, "a small number
`ε₀ > 0`"; false without it). -/
def T4_2 : Prop := ∀ {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}, 0 < γ → γ < 2 →
  IsWeakLQGMetric γ D c → ∀ (sel : ℂ → ℂ → DistC → C(unitInterval, ℂ)),
  (∀ (a b : ℂ) (g : DistC) (c : ℝ), sel a b (addConst g c) = sel a b g) →
  ∃ νs : ℝ, νs ∈ Ioo (0 : ℝ) 1 ∧ ∀ {μ ν : ℝ}, 0 < μ → μ < ν → ν ≤ νs → ∀ lam : Fin 5 → ℝ,
  0 < lam 0 → lam 0 < lam 1 → lam 1 ≤ lam 2 → lam 2 ≤ lam 3 → lam 3 < lam 4 →
  ∃ 𝕡 ∈ Ioo (0 : ℝ) 1, ∀ (q ℓ : ℝ) (U : Set ℂ), 0 < q → ℓ ∈ Ioo (0 : ℝ) 1 → IsOpen U →
  Bornology.IsBounded U → ∀ ε₀ Λ η : ℝ, 0 < ε₀ → 0 < η → ∃ ε₁ : ℝ, 0 < ε₁ ∧
  ∀ (R : ℝ) (Rad : Set ℝ) (E : ℝ → ℂ → Set DistC) (Ef : ℝ → ℂ → ℂ → ℂ → Set DistC), 0 < R →
    GeoIterateHyp D sel μ ν lam 𝕡 R ε₀ Λ Rad E Ef →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ ε ∈ Ioo (0 : ℝ) ε₁,
    P {ω | ∀ a b : ℂ, (∃ m : ℤ × ℤ, a = ((ε ^ q * R : ℝ) : ℂ) * (m.1 + m.2 * Complex.I)) →
      (∃ m : ℤ × ℤ, b = ((ε ^ q * R : ℝ) : ℂ) * (m.1 + m.2 * Complex.I)) →
      a ∈ (fun x => (R : ℂ) * x) '' U → b ∈ (fun x => (R : ℂ) * x) '' U → ℓ * R ≤ ‖a - b‖ →
      ∃ z : ℂ, ∃ r ∈ Rad, r ∈ Icc (ε ^ (1 + ν) * R) (ε * R) ∧
        (range (sel a b (h ω)) ∩ Metric.ball z (lam 1 * r)).Nonempty ∧ h ω ∈ Ef r z a b ∧
        a ∉ Metric.ball z (lam 3 * r) ∧ b ∉ Metric.ball z (lam 3 * r)}ᶜ ≤
      ENNReal.ofReal η

/-- GM Proposition 4.3 (l. 1582–1593), conclusion as proved (DV-B10: `P(s), P(t) ∈ B_{3r/2}(z)`),
with every other radius (DV-B3: `μ/2` in T4.2); `sel` is an a.s. `D_h`-geodesic selector (D74:
GM's `P^{𝕫,𝕨}` is "the `D_h`-geodesic", in the form used by `GeoIterateHyp`); D79: `sel` is
invariant under additive constants and measurable in the field (GM_B M1, D31: a Lusin–Souslin
selector of the a.s. unique geodesic), as GM's Lemma 5.4 needs `{h − φ ∈ 𝔈_r}` (l. 2801–2835);
D87: `𝕡 ∈ (0,1)` (GM l. 1588, 𝕡 from Thm 4.2) and `∀ 𝕡` precedes `∃ b ρ` (GM l. 2731);
D91: `νs < 1` (GM l. 1586: ν ≤ ν_* with ν_* ∈ (0,1) from Thm 4.2) -/
def P4_3 : Prop := ∀ {γ : ℝ} {D D' : DistC → ContMetric} {c : ℝ → ℝ} {cs Cs : ℝ},
  PairSetting γ D D' c → RatiosAre D D' cs Cs → cs < Cs →
  ∀ (sel : ℂ → ℂ → DistC → C(unitInterval, ℂ)),
  (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ a b : ℂ, a ≠ b → ∀ᵐ ω ∂P, IsGeod01 (D (h ω)) a b (sel a b (h ω))) →
  (∀ (a b : ℂ) (g : DistC) (c : ℝ), sel a b (addConst g c) = sel a b g) →
  (∀ a b : ℂ, Measurable (sel a b)) →
  ∀ (νs μ ν c₁ c₂ : ℝ),
  0 < μ → μ < ν → ν ≤ νs → νs < 1 → cs < c₁ → c₁ < c₂ → c₂ < Cs →
  ∀ 𝕡 ∈ Ioo (0 : ℝ) 1, ∃ b ρ : ℝ, b ∈ Ioo (0 : ℝ) 1 ∧ ρ ∈ Ioo (0 : ℝ) 1 ∧ ∃ c'' : ℝ, cs < c'' ∧
  ∀ β ∈ Ioo (0 : ℝ) 1, ∃ ε₀ Λ : ℝ, ε₀ ∈ Ioo (0 : ℝ) 1 ∧ 1 < Λ ∧
  ∀ R : ℝ, 0 < R → (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsWholePlaneGFF h P → ENNReal.ofReal β ≤ P (h ⁻¹' GLow D D' R c'' β)) →
  ∃ (Rad : Set ℝ) (E : ℝ → ℂ → Set DistC) (Ef : ℝ → ℂ → ℂ → ℂ → Set DistC),
    GeoIterateHyp D sel (μ / 2) ν ![1 / 4, 2, 3, 4, 5] 𝕡 (ρ⁻¹ * R) ε₀ Λ Rad E Ef ∧
    ∀ (z : ℂ), ∀ r ∈ Rad, ∀ a a' : ℂ, a ∉ Metric.ball z (4 * r) → a' ∉ Metric.ball z (4 * r) →
      ∀ g ∈ Ef r z a a', ∃ s t : unitInterval, s < t ∧
        sel a a' g s ∈ Metric.ball z (3 / 2 * r) ∧ sel a a' g t ∈ Metric.ball z (3 / 2 * r) ∧
        b * r ≤ ‖sel a a' g s - sel a a' g t‖ ∧
        (D' g).1 (sel a a' g s, sel a a' g t) ≤ c₂ * (D g).1 (sel a a' g s, sel a a' g t)

/-- GM Proposition 6.1 (l. 3570–3574) -/
def P6_1 : Prop := ∀ {γ : ℝ} {D D' : DistC → ContMetric} {c : ℝ → ℝ} {cs Cs : ℝ},
  PairSetting γ D D' c → RatiosAre D D' cs Cs → cs < Cs →
  ∃ c'' : ℝ, cs < c'' ∧ ∀ β ∈ Ioo (0 : ℝ) 1, ∀ βb ∈ Ioo (0 : ℝ) 1, ∀ η : ℝ, 0 < η →
  ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ R : ℝ, 0 < R →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ENNReal.ofReal β ≤ P (h ⁻¹' GLow D D' R c'' β) →
    ∀ δ ∈ Ioo (0 : ℝ) δ₀, P (h ⁻¹' GUp D D' R (Cs - δ) βb) ≤ ENNReal.ofReal η

/-- GM.S6.2–S6.3 (l. 3658–3659): `c_* = C_*` ⇒ `D̃_h = c_* D_h` for every GFF plus a continuous
function -/
def S6_23 : Prop := ∀ {γ : ℝ} {D D' : DistC → ContMetric} {c : ℝ → ℝ} {Cs : ℝ},
  PairSetting γ D D' c → RatiosAre D D' Cs Cs →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsGFFPlusCont h P → ∀ᵐ ω ∂P, ∀ u v : ℂ, (D' (h ω)).1 (u, v) = Cs * (D (h ω)).1 (u, v)

end LQGMetric.GM
