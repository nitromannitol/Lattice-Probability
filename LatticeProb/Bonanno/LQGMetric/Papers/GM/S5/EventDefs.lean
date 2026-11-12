/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.EventDefs at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Defs
import LatticeProb.Bonanno.LQGMetric.Field.CameronMartin

/-!
# GM §5.4–§5.5: the bump functions `𝓖_r`, the event `E_r` and the shortcut (statements)

GM = Gwynne–Miller, *Existence and uniqueness of the LQG metric for γ ∈ (0,2)*, arXiv:1905.00383,
`literature/src/1905.00383/uniqueness-final.tex` (task P2-M2M, WP-M2m, row 16 of `blueprint/M2.md`;
inventory `blueprint/GM_B.md` §2d).

* `dirInner g φ = (g, φ)_∇ := ⟨g, −Δφ/(2π)⟩` (`cmTest`, `LQGMetric.Field.Green`) and
  `gradEnergy φ = (φ, φ)_∇`; the normalization is the one of the Cameron–Martin formula
  `LQGMetric.Field.CameronMartin`.
* `EData`: the constants of GM §5.4 (l. 3180–3186): `ξ`, `𝔠`, `c_*`, `C_*`, `c_1'`, `η` (5.15), the
  output `ρ, b, ε_0` of Lemma 5.8 for `δ`, and GM's `Δ, A, ζ, a, θ, M, Λ_0` (`a` = GM's `a`).
* `lineTube θ r x` = `W_r^x` (GM (5.28), l. 3205), `Kf`, `Kg` (GM (5.29), l. 3213),
  `bumpPhi` = `φ_r^{x,y}` (GM (5.30)), `bumpFam` = `𝓖_r` (GM (5.31)). GM chooses `f_r^{x,y}` "in a
  deterministic manner depending only on `U_r^{x,y}`" and `g_r^x` depending only on `W_r^x`: here
  the choices are functions `fb gb : Set ℂ → TestC` applied to these sets; `IsBumpChoice` records
  GM's requirements (values in `[0,1]`, `≡ 1` on the set, `0` off its `ζr`- resp. `θ²r`-neighbourhood).
* `eventE` = `E_r` (GM §5.4.2, l. 3240–3266): `linkEvent` (conditions (1)–(3) of Lemma 5.8) and
  conditions (4)–(10); condition (10) with `|(h,φ)_∇|` (DV-B6).
* `IsHitPt`, `phiChoice` (GM l. 3340–3352, (5.35)).
* Statements `L5_9`, `L5_10`, `L5_11`, `P5_2`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

namespace LQGMetric.GM
open Blueprint

/-- the Dirichlet inner product `(g, φ)_∇ := ⟨g, −Δφ/(2π)⟩` of a distribution and a test function
(so that `(φ, φ)_∇ = gradEnergy φ` for smooth `g = φ`, Green's identity) -/
def dirInner (g : DistC) (φ : TestC) : ℝ := g (cmTest φ)

/-- the constants of GM §5.4 (l. 3180–3186). `ρ, b, ε₀` are the output of Lemma 5.8 for `δ`;
`a` is GM's `a` (`\Aacross`). -/
structure EData where
  /-- `ξ = γ / d_γ` -/
  ξ : ℝ
  /-- the scaling constants `𝔠_r` -/
  c : ℝ → ℝ
  cs : ℝ
  Cs : ℝ
  c₁ : ℝ
  η : ℝ
  δ : ℝ
  ρ : ℝ
  b : ℝ
  ε₀ : ℝ
  Δ : ℝ
  A : ℝ
  ζ : ℝ
  a : ℝ
  θ : ℝ
  M : ℝ
  Λ₀ : ℝ

namespace EData

/-- `K_f = ξ⁻¹ log(100 A / (a Δ))` (GM (5.29)) -/
def Kf (S : EData) : ℝ := S.ξ⁻¹ * Real.log (100 * S.A / (S.a * S.Δ))

/-- `K_g = K_f + ξ⁻¹ log M` (GM (5.29)) -/
def Kg (S : EData) : ℝ := S.Kf + S.ξ⁻¹ * Real.log S.M

end EData

/-- `W_r^x(θ)` (GM (5.28), l. 3205): the interior of the union of the squares of
`𝓢_{θr}([x, (3/2 − θ)x])` -/
def lineTube (θ r : ℝ) (x : ℂ) : Set ℂ :=
  interior (⋃ m ∈ squareSet (θ * r) (segment ℝ x (((3 / 2 - θ : ℝ) : ℂ) * x)),
    gridSquare (θ * r) m)

/-- `φ_r^{x,y} = K_f f_r^{x,y} + K_g (g_r^x + g_r^y)` (GM (5.30)) with `f_r^{x,y} = fb (U x y)`,
`g_r^x = gb (W_r^x)` -/
def bumpPhi (S : EData) (U : ℂ → ℂ → Set ℂ) (fb gb : Set ℂ → TestC) (r : ℝ) (x y : ℂ) : TestC :=
  S.Kf • fb (U x y) + S.Kg • (gb (lineTube S.θ r x) + gb (lineTube S.θ r y))

/-- `𝓖_r` (GM (5.31)) -/
def bumpFam (S : EData) (U : ℂ → ℂ → Set ℂ) (fb gb : Set ℂ → TestC) (r : ℝ) : Set TestC :=
  {φ | ∃ x ∈ Metric.sphere (0 : ℂ) (2 * r), ∃ y ∈ Metric.sphere (0 : ℂ) (2 * r),
    S.δ * r ≤ ‖x - y‖ ∧ φ = bumpPhi S U fb gb r x y} ∪ {0}

/-- `F` is `[0,1]`-valued, `≡ 1` on `V` and vanishes off `B_d(V)` -/
def IsBumpFor (F : TestC) (V : Set ℂ) (d : ℝ) : Prop :=
  (∀ z, F z ∈ Icc (0 : ℝ) 1) ∧ (∀ z ∈ V, F z = 1) ∧ ∀ z ∉ Metric.thickening d V, F z = 0

/-- GM's requirements on `f_r^{x,y}` and `g_r^x` (l. 3191, 3209) -/
def IsBumpChoice (S : EData) (U : ℂ → ℂ → Set ℂ) (fb gb : Set ℂ → TestC) (r : ℝ) : Prop :=
  (∀ x ∈ Metric.sphere (0 : ℂ) (2 * r), ∀ y ∈ Metric.sphere (0 : ℂ) (2 * r), S.δ * r ≤ ‖x - y‖ →
    IsBumpFor (fb (U x y)) (U x y) (S.ζ * r)) ∧
  ∀ x ∈ Metric.sphere (0 : ℂ) (2 * r), IsBumpFor (gb (lineTube S.θ r x)) (lineTube S.θ r x)
    (S.θ ^ 2 * r)

/-- the tube properties of GM Lemma 5.8 (as in `L5_8`), and the local attachment of `U` at its
end points (decision D83, (T5)): every point of `U ∩ B_{4ε₀r}(x)` is joined to `x` inside
`U ∩ B_{5ε₀r}(x)`, and likewise at `y`. GM's construction (l. 3086–3088: `U` near `x` consists of
the squares along the smooth path `L̂_x`, which may be taken radial near `x`) has this property;
the proof of Lemma 5.11 (GM l. 3480–3483, "the connected component of `(U ∪ 𝒲) ∖ O_u` containing
`𝕩'` lies at distance `≥ ε₀r` from the others") needs it to keep the tube `W^y` away from the
`x`-component. -/
def IsTubeFam (S : EData) (U : ℂ → ℂ → Set ℂ) (r : ℝ) : Prop :=
  ∀ x ∈ Metric.sphere (0 : ℂ) (2 * r), ∀ y ∈ Metric.sphere (0 : ℂ) (2 * r), S.δ * r ≤ ‖x - y‖ →
    IsOpen (U x y) ∧ IsConnected (U x y) ∧ U x y ⊆ Metric.ball 0 (3 * r) ∧
    IsSquareTube (U x y) (S.ε₀ * r) {w : ℂ | r / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * r} ∧ x ∈ U x y ∧ y ∈ U x y ∧
    -- (T5)
    U x y ∩ Metric.ball x (4 * S.ε₀ * r) ⊆
      connectedComponentIn (U x y ∩ Metric.ball x (5 * S.ε₀ * r)) x ∧
    U x y ∩ Metric.ball y (4 * S.ε₀ * r) ⊆
      connectedComponentIn (U x y ∩ Metric.ball y (5 * S.ε₀ * r)) y

/-- the event `E_r` (GM §5.4.2, l. 3240–3266); `sf g = 𝔠_r e^{ξ h_r(0)}`. Condition (10) with
`|(h,φ)_∇|` and `(φ,φ)_∇ = gradEnergy φ ≥ 0` (DV-B6). -/
def eventE (D D' : DistC → ContMetric) (S : EData) (U : ℂ → ℂ → Set ℂ) (fb gb : Set ℂ → TestC)
    (r : ℝ) : Set DistC :=
  linkEvent D D' S.cs S.Cs S.c₁ S.η S.δ S.ρ S.b S.ε₀ r U ∩
  {g | let sf := scaleFac S.ξ S.c g r 0
    -- (4)
    (∀ x ∈ Metric.sphere (0 : ℂ) (2 * r), ∀ y ∈ Metric.sphere (0 : ℂ) (2 * r), ‖x - y‖ < S.δ * r →
      (D g).internal (annulus 0 r (4 * r)) ((3 / 2 : ℂ) * x) ((3 / 2 : ℂ) * y) ≤
        ENNReal.ofReal (S.Δ * sf) ∧
      ENNReal.ofReal (S.Δ * sf) ≤
        setDist (D g) (Metric.sphere 0 (2 * r)) (Metric.sphere 0 (3 * r))) ∧
    -- (5)
    (∀ x ∈ Metric.sphere (0 : ℂ) (2 * r), ∀ y ∈ Metric.sphere (0 : ℂ) (2 * r), S.δ * r ≤ ‖x - y‖ →
      internalDiam (D g) (U x y) (U x y) ≤ ENNReal.ofReal (S.A * sf)) ∧
    -- (6)
    (∀ x ∈ Metric.sphere (0 : ℂ) (2 * r), ∀ y ∈ Metric.sphere (0 : ℂ) (2 * r), S.δ * r ≤ ‖x - y‖ →
      ∀ (P : ℝ → ℂ) (s t : ℝ), s ≤ t → ContinuousOn P (Icc s t) →
        P '' Icc s t ⊆ Metric.thickening (2 * S.ζ * r) (frontier (U x y)) →
        S.ε₀ * r / 100 ≤ Metric.diam (P '' Icc s t) →
        ENNReal.ofReal (100 * S.A * sf) ≤ (D g).len P s t) ∧
    -- (7)
    (∀ z₁ ∈ (annulus 0 (r / 4) (4 * r) : Set ℂ), ∀ z₂ ∈ (annulus 0 (r / 4) (4 * r) : Set ℂ),
      S.ζ * r ≤ ‖z₁ - z₂‖ →
        ENNReal.ofReal (S.a * sf) ≤ (D g).internal (annulus 0 (r / 4) (4 * r)) z₁ z₂) ∧
    -- (8)
    (∀ x ∈ Metric.sphere (0 : ℂ) (2 * r),
      (D g).internal (annulus 0 r (4 * r)) ((3 / 2 : ℂ) * x) (((3 / 2 - S.θ : ℝ) : ℂ) * x) ≤
        ENNReal.ofReal (Real.exp (-S.ξ * S.Kf) * sf)) ∧
    -- (9)
    (∀ x ∈ Metric.sphere (0 : ℂ) (2 * r),
      internalDiam (D g) (lineTube S.θ r x) (lineTube S.θ r x) ≤ ENNReal.ofReal (S.M * sf)) ∧
    -- (10)
    (∀ φ ∈ bumpFam S U fb gb r, |dirInner g φ| + gradEnergy φ / 2 ≤ S.Λ₀)}

/-- `x'` is a point of `∂B_{3r}(0)` hit first by the `D`-metric ball grown from `z` (GM l. 3341):
`x' ∈ ∂B_{3r}(0)` and `D(z, x') = D(z, cl B_{3r}(0))` -/
def IsHitPt (D : ContMetric) (z x' : ℂ) (r : ℝ) : Prop :=
  ‖x'‖ = 3 * r ∧ ∀ y ∈ Metric.closedBall (0 : ℂ) (3 * r), D.1 (z, x') ≤ D.1 (z, y)

/-- the bump function `φ` of GM (5.35) for the hitting points `x', y'` (`x = 2x'/3`, `y = 2y'/3`) -/
def phiChoice (S : EData) (U : ℂ → ℂ → Set ℂ) (fb gb : Set ℂ → TestC) (r : ℝ) (x' y' : ℂ) :
    TestC :=
  if S.δ * r ≤ ‖(2 / 3 : ℂ) * x' - (2 / 3 : ℂ) * y'‖ then
    bumpPhi S U fb gb r ((2 / 3 : ℂ) * x') ((2 / 3 : ℂ) * y') else 0

/-- `h − φ` -/
def subTest (g : DistC) (φ : TestC) : DistC := addFun g (-testCont φ)

/-- the conclusion (5.3)/(5.36) at a field `g` for a `D_g`-geodesic `Q` (on `[0,1]`), separation
`b₀ r` and constant `c₂ = c_2'` -/
def ShortcutConcl (D D' : DistC → ContMetric) (cs Cs c₂ b₀ r : ℝ) (g : DistC)
    (Q : C(unitInterval, ℂ)) : Prop :=
  ∃ s t : unitInterval, 0 < s ∧ s < t ∧ t < 1 ∧
    Q s ∈ Metric.ball (0 : ℂ) (3 / 2 * r) ∧ Q t ∈ Metric.ball (0 : ℂ) (3 / 2 * r) ∧
    b₀ * r ≤ ‖Q s - Q t‖ ∧ (D' g).1 (Q s, Q t) ≤ c₂ * (D g).1 (Q s, Q t) ∧
    ENNReal.ofReal ((D' g).1 (Q s, Q t)) ≤
      ENNReal.ofReal (cs / Cs) * setDist (D' g) {Q s} (Metric.sphere 0 (3 * r))

end LQGMetric.GM
