/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Defs at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.Defs

/-!
# GM §5.1–§5.3: good radii, half-annuli, square tubes and the events of Lemmas 5.5–5.8

GM = Gwynne–Miller, *Existence and uniqueness of the LQG metric for γ ∈ (0,2)*, arXiv:1905.00383,
`literature/src/1905.00383/uniqueness-final.tex` (task P2-M2L, WP-M2l, row 15 of `blueprint/M2.md`).

* `goodRadii D D' α c₁ p₀` = `𝓡_0` (GM (5.1), l. 2662–2668): the radii `r > 0` such that, with
  probability at least `p₀`, there are `u ∈ ∂B_{αr}(0)`, `v ∈ ∂B_r(0)` with `D̃_h(u,v) ≤ c₁' D_h(u,v)`
  and the `D̃_h`-geodesic from `u` to `v` unique and contained in `cl 𝔸_{αr,r}(0)` (this is the event
  `attainedLow` of GM P3.5 (A′)). "With probability at least `p₀`" is read for every whole-plane GFF
  on every probability space (the law of `h` modulo constants is unique; convention BP-M2-6).
* `IsHalfAnnulus` (l. 2889), `endpointEvent` (GM Lemma 5.5, l. 2890–2897).
* `squareSet ε X` = `𝓢_ε(X)` (GM (5.14), l. 2936), `IsSquareTube` ("the interior of a finite union
  of squares in `𝓢_ε(X)`"), `EtaChoice` (GM (5.15), l. 2940).
* `nearComp`, `SepFrom` (conditions 2, 3 of GM Lemmas 5.6 and 5.8), `tubeEvent` (= `F_r(z)`, GM Lemma
  5.6, l. 2944–2958), `linkEvent` (the event of GM Lemma 5.8, l. 3047–3062).
* The statements `L5_5`, `L5_6`, `L5_7`, `L5_8` (proved results are `gm_L5_5`, …).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

namespace LQGMetric.GM
open Blueprint

/-- `𝓡_0` (GM (5.1), l. 2662–2668) for given `α`, `c₁ = c_1'` and `p₀` -/
def goodRadii (D D' : DistC → ContMetric) (α c₁ p₀ : ℝ) : Set ℝ :=
  {r | 0 < r ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC), IsWholePlaneGFF h P →
      ENNReal.ofReal p₀ ≤ P (h ⁻¹' attainedLow D D' α r c₁)}

/-- `H` is a half-annulus of `𝔸_{r₁,r₂}(z)`: its intersection with an open half-plane whose boundary
passes through `z` (GM l. 2889) -/
def IsHalfAnnulus (H : Set ℂ) (z : ℂ) (r₁ r₂ : ℝ) : Prop :=
  ∃ e : ℂ, ‖e‖ = 1 ∧ H = (annulus z r₁ r₂ : Set ℂ) ∩ {w | 0 < ((w - z) * (starRingEnd ℂ) e).re}

/-- the event of GM Lemma 5.5 (l. 2890–2897) for a given half-annulus `H`; `cs`, `Cs` stand for
`c_*`, `C_*` -/
def endpointEvent (D D' : DistC → ContMetric) (cs Cs α c₁ r : ℝ) (z : ℂ) (H : Set ℂ) :
    Set DistC :=
  {g | ∃ u ∈ Metric.sphere z (α * r), ∃ v ∈ Metric.sphere z r,
    (D' g).1 (u, v) ≤ c₁ * (D g).1 (u, v) ∧ UniqueGeodIn (D' g) u v (closure H) ∧
    ENNReal.ofReal ((D' g).1 (u, v)) ≤
      ENNReal.ofReal ((cs / Cs) ^ 2) * setDist (D' g) (annulus z (α * r) r) (Metric.sphere z (2 * r))}

/-- the conclusion of GM Lemma 5.5 for a given `α` (and `p₀`): for all `c₁`, `r ∈ 𝓡_0`, `z` there is
a deterministic half-annulus `H_r(z) ⊂ 𝔸_{αr,r}(z)` with `P[endpointEvent] ≥ p₀/8` -/
def EndpointProp (D D' : DistC → ContMetric) (cs Cs α p₀ : ℝ) : Prop :=
  ∀ c₁ : ℝ, ∀ r ∈ goodRadii D D' α c₁ p₀, ∀ z : ℂ,
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∃ H : Set ℂ, IsHalfAnnulus H z (α * r) r ∧
      ENNReal.ofReal (p₀ / 8) ≤ P (h ⁻¹' endpointEvent D D' cs Cs α c₁ r z H)

/-- **GM Lemma 5.5** (`lem-endpoint-geodesic`, l. 2890–2897). `α₀`, `p₀` are GM's `α_*`, `p_0`
(any values in `(0,1)`); the conclusion is uniform in `c_1'`. -/
def L5_5 : Prop := ∀ {γ : ℝ} {D D' : DistC → ContMetric} {c : ℝ → ℝ} {cs Cs : ℝ},
  PairSetting γ D D' c → 0 < cs → 0 < Cs → ∀ {α₀ p₀ : ℝ}, α₀ < 1 → 0 < p₀ → p₀ < 1 →
  ∃ α ∈ Ico α₀ 1, 3 / 4 ≤ α ∧ EndpointProp D D' cs Cs α p₀

/-! ## Squares and tubes -/

/-- `𝓢_ε(X)` (GM (5.14), l. 2936), as the set of indices `m` of the closed squares
`gridSquare ε m` (corners in `εℤ²`) which intersect `X` -/
def squareSet (ε : ℝ) (X : Set ℂ) : Set (ℤ × ℤ) := {m | (gridSquare ε m ∩ X).Nonempty}

/-- `V` is the interior of a finite union of squares in `𝓢_ε(X)` -/
def IsSquareTube (V : Set ℂ) (ε : ℝ) (X : Set ℂ) : Prop :=
  ∃ F : Finset (ℤ × ℤ), (↑F : Set (ℤ × ℤ)) ⊆ squareSet ε X ∧
    V = interior (⋃ m ∈ F, gridSquare ε m)

/-- the choice of `η` in GM (5.15) (l. 2925–2940): GM's two inequalities, the positivity of the
denominator of (5.15) (GM's "small η"; without it (5.15) holds for large `η`, e.g. `C_*/c_* = 10`,
`η = 1/2`, and (5.46) fails) and `1 + 3η ≤ C_*/c_*` for the repair of GM l. 3505 (decision D83). -/
def EtaChoice (cs Cs c₁ c₂ η : ℝ) : Prop :=
  0 < η ∧ η < 1 ∧ c₁ * (1 + 2 * η) / (1 - 2 * cs⁻¹ * Cs * η) < c₂ ∧ 1 + 2 * η < Cs / cs ∧
    2 * cs⁻¹ * Cs * η < 1 ∧ 1 + 3 * η ≤ Cs / cs

/-- `O_u`: the connected component of `V ∩ B_δ(u)` containing `u` -/
def nearComp (V : Set ℂ) (δ : ℝ) (u : ℂ) : Set ℂ := connectedComponentIn (V ∩ Metric.ball u δ) u

/-- the connected component of `V ∖ O` containing `a` lies at Euclidean distance at least `d`
from the union of the other connected components of `V ∖ O` -/
def SepFrom (V O : Set ℂ) (a : ℂ) (d : ℝ) : Prop :=
  ∀ x ∈ connectedComponentIn (V \ O) a, ∀ y ∈ V \ O, y ∉ connectedComponentIn (V \ O) a →
    d ≤ dist x y

/-- condition (2) of GM Lemmas 5.6 and 5.8 in its robust reading (decision D69): `SepFrom` holds
for `O_{u'}` (radius `δ`) at every point `u'` of a neighbourhood of `u`. GM's proof of condition (2)
(l. 2982–2989, 3111–3127) works verbatim for all `u'` near `u`, and the set of such `u` is open,
hence Borel (needed for Lemma 5.7); the pointwise condition is `SepNear.sepFrom`. -/
def SepNear (V : Set ℂ) (δ : ℝ) (u a : ℂ) (d : ℝ) : Prop :=
  ∀ᶠ u' in 𝓝 u, SepFrom V (nearComp V δ u') a d

/-- the robust condition implies GM's pointwise condition (2) at `u` -/
lemma SepNear.sepFrom {V : Set ℂ} {δ : ℝ} {u a : ℂ} {d : ℝ} (h : SepNear V δ u a d) :
    SepFrom V (nearComp V δ u) a d :=
  h.self_of_nhds

/-- condition (2) of GM Lemma 5.6 with its disconnection clause (decision D77, decisions/DEC-77.md),
in the robust reading of D69: at every point `u'` of a neighbourhood of `u`, removing
`O_{u'}` (radius `δ`) disconnects `b` from `a` in `V` (GM's title of condition (2), "Removing
neighborhoods of `u,v` disconnects `V_r(z)`", l. 2949, and its proof, l. 2988: "removing `O_u`
disconnects `V_r(z)` into at least two connected components"), and the component of `a` lies at
distance `≥ d` from the other components (`SepFrom`). Without the disconnection clause `SepFrom`
is vacuous when `V ∖ O_u` is connected. -/
def SepDiscNear (V : Set ℂ) (δ : ℝ) (u a b : ℂ) (d : ℝ) : Prop :=
  ∀ᶠ u' in 𝓝 u, SepFrom V (nearComp V δ u') a d ∧
    b ∉ connectedComponentIn (V \ nearComp V δ u') a

lemma SepDiscNear.sepNear {V : Set ℂ} {δ : ℝ} {u a b : ℂ} {d : ℝ} (h : SepDiscNear V δ u a b d) :
    SepNear V δ u a d :=
  h.mono fun _ h' => h'.1

lemma SepDiscNear.sepFrom {V : Set ℂ} {δ : ℝ} {u a b : ℂ} {d : ℝ} (h : SepDiscNear V δ u a b d) :
    SepFrom V (nearComp V δ u) a d :=
  h.sepNear.sepFrom

/-- the pointwise disconnection at `u` -/
lemma SepDiscNear.not_mem_comp {V : Set ℂ} {δ : ℝ} {u a b : ℂ} {d : ℝ}
    (h : SepDiscNear V δ u a b d) : b ∉ connectedComponentIn (V \ nearComp V δ u) a :=
  h.self_of_nhds.2

/-- the set of points satisfying `SepDiscNear` is open -/
lemma isOpen_setOf_sepDiscNear (V : Set ℂ) (δ : ℝ) (a b : ℂ) (d : ℝ) :
    IsOpen {u : ℂ | SepDiscNear V δ u a b d} :=
  isOpen_setOfPred_eventually_nhds

/-- the event `F_r(z)` of GM Lemma 5.6 (l. 2944–2958) for a given tube `V = V_r(z)`, with
`b = b_1`, `ε = ε_1`, `c₁ = c_1'` and `η` as in (5.15); condition (1) also at `v` (D83 (b): GM's
condition (2) is symmetric in `u ↔ v`, and Lemma 5.5's bound gives the clause at `v` likewise) -/
def tubeEvent (D D' : DistC → ContMetric) (cs Cs c₁ η b ε r : ℝ) (z : ℂ) (V : Set ℂ) :
    Set DistC :=
  {g | ∃ u ∈ V ∩ Metric.closedBall z r, ∃ v ∈ V ∩ Metric.closedBall z r,
    -- (1)
    b * r ≤ ‖u - v‖ ∧ (D' g).1 (u, v) ≤ c₁ * (D g).1 (u, v) ∧
    ENNReal.ofReal ((D' g).1 (u, v)) ≤
      ENNReal.ofReal ((cs / Cs) ^ 2) * setDist (D' g) {u} (Metric.sphere z (2 * r)) ∧
    ENNReal.ofReal ((D' g).1 (u, v)) ≤
      ENNReal.ofReal ((cs / Cs) ^ 2) * setDist (D' g) {v} (Metric.sphere z (2 * r)) ∧
    UniqueGeodIn (D' g) u v (V ∩ Metric.closedBall z r) ∧
    -- (2)
    SepDiscNear V (20 * ε * r) u (z - 2 * r) (z + 2 * r) (ε * r) ∧
    SepDiscNear V (20 * ε * r) v (z + 2 * r) (z - 2 * r) (ε * r) ∧
    -- (3)
    (∀ w ∈ nearComp V (20 * ε * r) u,
      (D' g).internal V u w ≤ ENNReal.ofReal (η * (D' g).1 (u, v))) ∧
    (∀ w ∈ nearComp V (20 * ε * r) v,
      (D' g).internal V v w ≤ ENNReal.ofReal (η * (D' g).1 (u, v)))}

/-- **GM Lemma 5.6** (`lem-deterministic-geodesic`, l. 2940–2958), for an `α` satisfying the
conclusion of Lemma 5.5 (`b_1 = 1 − α` in GM's proof). Constants after `c₁, c₂, η` (deviation
P2-M2L-2: GM's `p_1` depends on `ε_1`, hence on `c_1', c_2'`, through the number of square sets).
Squares of `𝓢_{ε₁r}(cl B_{2r}(z))` (D69: with GM's open ball, `z − 2r ∉ V` when `z − 2r` lies on a
grid line, so GM's statement is false for such `z`); condition (2) in the robust form `SepNear`
with GM's disconnection clause (`SepDiscNear`, D77). `V` is deterministic, chosen before the
probability space (GM l. 2941, decision D92). -/
def L5_6 : Prop := ∀ {γ : ℝ} {D D' : DistC → ContMetric} {c : ℝ → ℝ} {cs Cs : ℝ},
  PairSetting γ D D' c → RatiosAre D D' cs Cs → 0 < cs → cs < Cs →
  ∀ {α p₀ : ℝ}, 3 / 4 ≤ α → α < 1 → 0 < p₀ → p₀ < 1 → EndpointProp D D' cs Cs α p₀ →
  ∀ {c₁ c₂ η : ℝ}, cs < c₁ → c₁ < c₂ → c₂ < Cs → EtaChoice cs Cs c₁ c₂ η →
  ∃ b₁ p₁ ε₁ : ℝ, b₁ ∈ Ioo (0 : ℝ) (1 / 100) ∧ p₁ ∈ Ioo (0 : ℝ) (1 / 100) ∧
    ε₁ ∈ Ioo (0 : ℝ) (b₁ / 100) ∧
  ∀ (z : ℂ), ∀ r ∈ goodRadii D D' α c₁ p₀, ∃ V : Set ℂ, IsOpen V ∧ IsConnected V ∧
    V ⊆ Metric.ball z ((2 + 2 * ε₁) * r) ∧
    IsSquareTube V (ε₁ * r) (Metric.closedBall z (2 * r)) ∧
    z - 2 * r ∈ V ∧ z + 2 * r ∈ V ∧
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ENNReal.ofReal p₁ ≤ P (h ⁻¹' tubeEvent D D' cs Cs c₁ η b₁ ε₁ r z V)

/-- the event of GM Lemma 5.8 (l. 3047–3062) for a given family of tubes `U x y = U_r^{x,y}`;
condition (1) also at `v` (D83 (b)) -/
def linkEvent (D D' : DistC → ContMetric) (cs Cs c₁ η δ ρ b ε r : ℝ) (U : ℂ → ℂ → Set ℂ) :
    Set DistC :=
  {g | ∀ x ∈ Metric.sphere (0 : ℂ) (2 * r), ∀ y ∈ Metric.sphere (0 : ℂ) (2 * r), δ * r ≤ ‖x - y‖ →
    ∃ u ∈ (annulus 0 ((1 - 4 * ρ) * r) ((1 + 4 * ρ) * r) : Set ℂ) ∩ U x y,
    ∃ v ∈ (annulus 0 ((1 - 4 * ρ) * r) ((1 + 4 * ρ) * r) : Set ℂ) ∩ U x y,
    -- (1)
    b * r ≤ ‖u - v‖ ∧ (D' g).1 (u, v) ≤ c₁ * (D g).1 (u, v) ∧
    ENNReal.ofReal ((D' g).1 (u, v)) ≤
      ENNReal.ofReal ((cs / Cs) ^ 2) * setDist (D' g) {u} (Metric.sphere u (4 * ρ * r)) ∧
    ENNReal.ofReal ((D' g).1 (u, v)) ≤
      ENNReal.ofReal ((cs / Cs) ^ 2) * setDist (D' g) {v} (Metric.sphere v (4 * ρ * r)) ∧
    UniqueGeodIn (D' g) u v (U x y) ∧
    -- (2)
    SepDiscNear (U x y) (20 * ε * r) u x y (ε * r) ∧
    SepDiscNear (U x y) (20 * ε * r) v y x (ε * r) ∧
    -- (3)
    (∀ w ∈ nearComp (U x y) (20 * ε * r) u,
      (D' g).internal (U x y) u w ≤ ENNReal.ofReal (η * (D' g).1 (u, v))) ∧
    (∀ w ∈ nearComp (U x y) (20 * ε * r) v,
      (D' g).internal (U x y) v w ≤ ENNReal.ofReal (η * (D' g).1 (u, v)))}

/-- **GM Lemma 5.8** (`lem-highprob-geodesic`, l. 3044–3062), for an `α` satisfying the conclusion of
Lemma 5.5; `r ∈ ρ⁻¹𝓡_0` is written `ρ r ∈ 𝓡_0`. Squares of `𝓢_{ε₀r}(cl 𝔸_{r/2,2r}(0))` (D69: with
GM's open annulus, `x ∉ U` when `x ∈ ∂B_{2r}(0)` is a grid corner). `U` is deterministic, chosen
before the probability space (GM l. 3045, decision D92), and attached locally at `x`, `y` (the (T5)
clause, decision D83 (c)). -/
def L5_8 : Prop := ∀ {γ : ℝ} {D D' : DistC → ContMetric} {c : ℝ → ℝ} {cs Cs : ℝ},
  PairSetting γ D D' c → RatiosAre D D' cs Cs → 0 < cs → cs < Cs →
  ∀ {α p₀ : ℝ}, 3 / 4 ≤ α → α < 1 → 0 < p₀ → p₀ < 1 → EndpointProp D D' cs Cs α p₀ →
  ∀ {c₁ c₂ η : ℝ}, cs < c₁ → c₁ < c₂ → c₂ < Cs → EtaChoice cs Cs c₁ c₂ η →
  ∀ {p δ : ℝ}, p ∈ Ioo (0 : ℝ) 1 → δ ∈ Ioo (0 : ℝ) 1 →
  ∃ b ρ ε₀ : ℝ, b ∈ Ioo (0 : ℝ) (1 / 100) ∧ ρ ∈ Ioo (0 : ℝ) (1 / 100) ∧ ε₀ ∈ Ioo (0 : ℝ) (b / 100) ∧
  ∀ r : ℝ, ρ * r ∈ goodRadii D D' α c₁ p₀ → ∃ U : ℂ → ℂ → Set ℂ,
    (∀ x ∈ Metric.sphere (0 : ℂ) (2 * r), ∀ y ∈ Metric.sphere (0 : ℂ) (2 * r), δ * r ≤ ‖x - y‖ →
      IsOpen (U x y) ∧ IsConnected (U x y) ∧ U x y ⊆ Metric.ball 0 (3 * r) ∧
      IsSquareTube (U x y) (ε₀ * r) {w : ℂ | r / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2 * r} ∧ x ∈ U x y ∧
      y ∈ U x y ∧
      U x y ∩ Metric.ball x (4 * ε₀ * r) ⊆
        connectedComponentIn (U x y ∩ Metric.ball x (5 * ε₀ * r)) x ∧
      U x y ∩ Metric.ball y (4 * ε₀ * r) ⊆
        connectedComponentIn (U x y ∩ Metric.ball y (5 * ε₀ * r)) y) ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsWholePlaneGFF h P → ENNReal.ofReal p ≤ P (h ⁻¹' linkEvent D D' cs Cs c₁ η δ ρ b ε₀ r U)

end LQGMetric.GM
