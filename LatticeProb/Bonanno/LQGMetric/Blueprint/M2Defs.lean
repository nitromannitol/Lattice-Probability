/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Blueprint.M2Defs at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Statement.LQGMetric
import LatticeProb.Bonanno.LQGMetric.Metric.SetDist
import LatticeProb.Bonanno.LQGMetric.Prob.CondIndepEv

/-!
# Blueprint-side definitions for milestone M2 (GM §§2–6 and the results they cite)

Small definitions used by the M2 Blueprint Props (`Blueprint/LMResults.lean`,
`DFGPSEstimates.lean`, `CONFResults.lean`, `MQGeodesic.lean`) and by `blueprint/M2.md`.
Sources (GM = `literature/src/1905.00383/uniqueness-final.tex`, LM =
`literature/src/1905.00379/local-metrics-final.tex`, CONF =
`literature/src/1905.00381/confluence-final.tex`):

* Euclidean balls `B_r(z)` and annuli `A_{r₁,r₂}(z) = B_{r₂}(z) ∖ cl B_{r₁}(z)` (GM l. 160–170);
* `D(A, B)` (GM l. 255: distance between sets), internal diameters `sup_{u,v∈A} D(u,v;V)`;
* metric balls `𝓑_s(z;D)` and filled metric balls `𝓑^•_s(z;D)` (CONF l. 377, GM l. 846):
  the union of `cl 𝓑_s(z;D)` and the points disconnected from `∞` by it;
* geodesics: `IsGeod01` (decision D31, `decisions/DEC-C.md` rule 1: constant-speed parametrization
  on `[0,1]`) and the unit-speed form `IsGeodesicL` (`P(t)` at `D`-length time `t`, as GM write);
* restriction σ-algebras `σ(h|_V)` (V open) and `σ(h|_K) = ⋂_{ε>0} σ(h|_{B_ε(K)})` (K closed,
  LM l. 164 footnote), σ-algebras of internal metrics, conditional independence (`CondIndepEv`);
* jointly local (LM Def 1.3, l. 245–248) and ξ-additive (LM Def 1.5, l. 284–287) pairs of random
  metrics, for `U = ℂ` (decision D21);
* local sets in determined form (decision D32: `{A ⊆ U}` a.s. in `σ(h|_U)`) and the σ-algebra
  `σ(A, h|_A)` through dyadic hulls (D32), stopping times for the filled-ball filtration;
* "a.s. equal to an event of a σ-algebra" (`AEEventIn`, decision D30's `AEEventDeterminedBy`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.Blueprint

/-! ## Euclidean sets -/

/-- the open Euclidean ball `B_r(z)` as an open set -/
def ballO (z : ℂ) (r : ℝ) : TopologicalSpace.Opens ℂ := ⟨Metric.ball z r, Metric.isOpen_ball⟩

/-- the open Euclidean annulus `A_{r₁,r₂}(z) = B_{r₂}(z) ∖ cl B_{r₁}(z)` (GM l. 165) -/
def annulus (z : ℂ) (r₁ r₂ : ℝ) : TopologicalSpace.Opens ℂ :=
  ⟨{w | r₁ < ‖w - z‖ ∧ ‖w - z‖ < r₂},
    (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).inter
      (isOpen_lt (continuous_id.sub continuous_const).norm continuous_const)⟩

/-- an open set as an element of `Opens ℂ` -/
def toOpens (U : Set ℂ) (hU : IsOpen U) : TopologicalSpace.Opens ℂ := ⟨U, hU⟩

/-- the open Euclidean `ε`-neighbourhood `B_ε(K)` as an open set -/
def nbhdO (ε : ℝ) (K : Set ℂ) : TopologicalSpace.Opens ℂ :=
  ⟨Metric.thickening ε K, Metric.isOpen_thickening⟩

/-! ## Metric quantities of a continuous metric -/

/-- `D(A, B) = inf_{u∈A, v∈B} D(u, v)` (GM l. 255), in `[0, ∞]` -/
def setDist (D : ContMetric) (A B : Set ℂ) : ℝ≥0∞ :=
  MetricGeometry.setEDist (D.pt '' A) (D.pt '' B)

/-- `sup_{u,v ∈ A} D(u, v; V)` (internal diameter of `A` in `V`) -/
def internalDiam (D : ContMetric) (A V : Set ℂ) : ℝ≥0∞ :=
  ⨆ u ∈ A, ⨆ v ∈ A, D.internal V u v

/-- the open metric ball `𝓑_s(z; D) = {w : D(z, w) < s}` -/
def ballM (D : ContMetric) (z : ℂ) (s : ℝ) : Set ℂ := {w | D.1 (z, w) < s}

/-- the filled metric ball `𝓑^•_s(z; D)` (CONF l. 377, GM l. 846): the union of
`X := cl 𝓑_s(z; D)` and the set of points disconnected from `∞` by `X`, i.e. the points of `Xᶜ`
whose connected component in `Xᶜ` is bounded. -/
def filledBall (D : ContMetric) (z : ℂ) (s : ℝ) : Set ℂ :=
  closure (ballM D z s) ∪
    {x | x ∉ closure (ballM D z s) ∧
      Bornology.IsBounded (connectedComponentIn (closure (ballM D z s))ᶜ x)}

/-- `η` is a `D`-geodesic from `z` to `w` in constant-speed parametrization on `[0,1]`
(decision D31, rule 1: `η 0 = z`, `η 1 = w`, `D(η s, η t) = |t − s| D(z, w)`); "the geodesic is
unique" is literal uniqueness of `η`. -/
def IsGeod01 (D : ContMetric) (z w : ℂ) (η : C(unitInterval, ℂ)) : Prop :=
  η 0 = z ∧ η 1 = w ∧ ∀ s t : unitInterval, D.1 (η s, η t) = |(t : ℝ) - s| * D.1 (z, w)

/-- `P : [0, L] → ℂ` is a `D`-geodesic from `z` to `w` parametrized by `D`-length (GM's
convention "`P(t)` at time `t`"); then `L = D(z, w)`. Equivalent to `IsGeod01` by `P(t) = η(t/L)`. -/
def IsGeodesicL (D : ContMetric) (P : ℝ → ℂ) (L : ℝ) (z w : ℂ) : Prop :=
  0 ≤ L ∧ P 0 = z ∧ P L = w ∧ ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, D.1 (P s, P t) = |t - s|

/-- the `D`-geodesic from `z` to `w` exists and is unique -/
def UniqueGeod (D : ContMetric) (z w : ℂ) : Prop := ∃! η, IsGeod01 D z w η

/-- `𝔠_r e^{ξ h_r(z)}`, the scale of `D_h` at `B_r(z)` (GM l. 440–447) -/
def scaleFac (ξ : ℝ) (c : ℝ → ℝ) (h : DistC) (r : ℝ) (z : ℂ) : ℝ :=
  c r * Real.exp (ξ * circleAvg h r z)

/-! ## σ-algebras of the field and of random metrics -/

section Sigma0On
variable {Ω : Type*}

/-- `σ(⟨h, ψ⟩ : ψ ∈ 𝓓(ℂ), ∫ ψ = 0, supp ψ ⊆ V)`: `σ(h|_V)` modulo additive constants (D79; GM
l. 214, 1200–1205; CONF C:1154, 1187). Moved here from `Papers/GM/S3/SigmaMod.lean` (D110 P1;
`GM.fieldSigma0On` is an alias). -/
def fieldSigma0On (h : Ω → DistC) (V : Set ℂ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω (ψ : {ψ : TestC0 // tsupport (ψ.1 : ℂ → ℝ) ⊆ V}) => h ω ψ.1.1)
    MeasurableSpace.pi

/-- `σ(h|_K)` modulo additive constants: `⋂_{ε>0} σ(h|_{B_ε(K)} mod const)` (D79, D110) -/
def fieldSigmaClosed0 (h : Ω → DistC) (K : Set ℂ) : MeasurableSpace Ω :=
  ⨅ (ε : ℝ) (_ : 0 < ε), fieldSigma0On h (Metric.thickening ε K)

end Sigma0On

section Sigma
variable {Ω : Type} [MeasurableSpace Ω]

/-- `σ(h|_V)` for `V` open -/
def fieldSigma (h : Ω → DistC) (V : TopologicalSpace.Opens ℂ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω => restrictTo V (h ω)) inferInstance

/-- `σ(h|_K) := ⋂_{ε>0} σ(h|_{B_ε(K)})` for a (closed) set `K` (LM l. 164 footnote) -/
def fieldSigmaClosed (h : Ω → DistC) (K : Set ℂ) : MeasurableSpace Ω :=
  ⨅ (ε : ℝ) (_ : 0 < ε), fieldSigma h (nbhdO ε K)

/-- `σ(I(·,·; V))` for a random family of internal metrics `I ω V : ℂ → ℂ → [0,∞]` -/
def famSigma (I : Ω → Set ℂ → ℂ → ℂ → ℝ≥0∞) (V : Set ℂ) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω => I ω V) inferInstance

/-- the internal metrics `V ↦ D(·,·;V)` of a random metric -/
def internalFam (D : Ω → ContMetric) : Ω → Set ℂ → ℂ → ℂ → ℝ≥0∞ :=
  fun ω V => (D ω).internal V

/-- **jointly local** families of internal metrics for `h` on `U = ℂ` (LM Def 1.3, l. 245–248,
`n = 2`): for every open `V`, `{I_j(·,·;V)}_j` is conditionally independent of
`(h|_{ℂ∖V}, {I_j(·,·;ℂ∖cl V)}_j)` given `h|_V`. -/
def IsJointlyLocalFam (P : Measure Ω) (h : Ω → DistC) (I₁ I₂ : Ω → Set ℂ → ℂ → ℂ → ℝ≥0∞) :
    Prop :=
  ∀ V : TopologicalSpace.Opens ℂ,
    CondIndepEv (fieldSigma h V) (famSigma I₁ V ⊔ famSigma I₂ V)
      (fieldSigmaClosed h (V : Set ℂ)ᶜ ⊔ famSigma I₁ (closure (V : Set ℂ))ᶜ ⊔
        famSigma I₂ (closure (V : Set ℂ))ᶜ) P

/-- `(h, D₁, D₂)` is a coupling of `h` with two random continuous length metrics on `ℂ` which are
**jointly local** for `h` (LM Def 1.3). -/
def IsJointlyLocal2 (P : Measure Ω) (h : Ω → DistC) (D₁ D₂ : Ω → ContMetric) : Prop :=
  Measurable D₁ ∧ Measurable D₂ ∧ (∀ᵐ ω ∂P, (D₁ ω).IsLength ∧ (D₂ ω).IsLength) ∧
    IsJointlyLocalFam P h (internalFam D₁) (internalFam D₂)

/-- `(D₁, D₂)` are **ξ-additive** for `h` on `U = ℂ` (LM Def 1.5, l. 284–287): jointly local, and
for each `z ∈ ℂ`, `r > 0`, `(e^{−ξh_r(z)}D₁, e^{−ξh_r(z)}D₂)` are jointly local for `h − h_r(z)`.
The internal metric of `e^{−ξh_r(z)}D_j` is `e^{−ξh_r(z)}D_j(·,·;V)`. -/
def IsXiAdditive2 (ξ : ℝ) (P : Measure Ω) (h : Ω → DistC) (D₁ D₂ : Ω → ContMetric) : Prop :=
  IsJointlyLocal2 P h D₁ D₂ ∧ ∀ (z : ℂ) (r : ℝ), 0 < r →
    IsJointlyLocalFam P (fun ω => addConst (h ω) (-circleAvg (h ω) r z))
      (fun ω V u v => ENNReal.ofReal (Real.exp (-ξ * circleAvg (h ω) r z)) * (D₁ ω).internal V u v)
      (fun ω V u v => ENNReal.ofReal (Real.exp (-ξ * circleAvg (h ω) r z)) * (D₂ ω).internal V u v)

/-- `E` is a.s. equal to an event of the σ-algebra `m` (decision D30, `AEEventDeterminedBy`) -/
def AEEventIn (P : Measure Ω) (m : MeasurableSpace Ω) (E : Set Ω) : Prop :=
  ∃ F : Set Ω, MeasurableSet[m] F ∧ E =ᵐ[P] F

/-- a random set `A` is a **local set** of `h`, determined form (decision D32; CONF l. 472–473,
"`A` is determined by `h|_U` on the event `{A ⊂ U}`"): for every open `U`, `{A ⊆ U}` is a.s. an
event of `σ(h|_U)`. -/
def IsLocalSetDet (P : Measure Ω) (h : Ω → DistC) (A : Ω → Set ℂ) : Prop :=
  ∀ U : TopologicalSpace.Opens ℂ, AEEventIn P (fieldSigma h U) {ω | A ω ⊆ U}

/-- the closed dyadic square of level `n` with lower-left corner `2^{-n} k` -/
def dyadicSq (n : ℕ) (k : ℤ × ℤ) : Set ℂ :=
  {x | (k.1 : ℝ) / 2 ^ n ≤ x.re ∧ x.re ≤ (k.1 + 1) / 2 ^ n ∧
    (k.2 : ℝ) / 2 ^ n ≤ x.im ∧ x.im ≤ (k.2 + 1) / 2 ^ n}

/-- the dyadic hull `A^{(n)}`: the union of the level-`n` dyadic squares meeting `A` (D32) -/
def dyadicHull (n : ℕ) (A : Set ℂ) : Set ℂ :=
  ⋃ (k : ℤ × ℤ) (_ : (dyadicSq n k ∩ A).Nonempty), dyadicSq n k

/-- `σ(A)` for a random set: generated by the events `{A ∩ U ≠ ∅}`, `U` open (Effros) -/
def setSigma (A : Ω → Set ℂ) : MeasurableSpace Ω :=
  MeasurableSpace.generateFrom {E | ∃ U : Set ℂ, IsOpen U ∧ E = {ω | (A ω ∩ U).Nonempty}}

/-- `σ(A, h|_{int A^{(n)}})`: `σ(A)` together with the events `{A^{(n)} = S} ∩ F`,
`F ∈ σ(h|_{int S})` -/
def hullSigma (h : Ω → DistC) (A : Ω → Set ℂ) (n : ℕ) : MeasurableSpace Ω :=
  setSigma A ⊔ MeasurableSpace.generateFrom
    {E | ∃ (S : Set ℂ) (F : Set Ω), MeasurableSet[fieldSigma h (toOpens (interior S)
      isOpen_interior)] F ∧ E = {ω | dyadicHull n (A ω) = S} ∩ F}

/-- `σ(A, h|_A) := ⋂_n σ(A, h|_{int A^{(n)}})` (CONF l. 474: `⋂_ε σ(A, h|_{B_ε(A)})`; D32's
dyadic-hull form) -/
def localSigma (h : Ω → DistC) (A : Ω → Set ℂ) : MeasurableSpace Ω :=
  ⨅ n : ℕ, hullSigma h A n

/-- `σ(A, h|_{int A^{(n)}})` modulo additive constants: `hullSigma` with the mean-zero pairings
`fieldSigma0On` (D108, D110; moved from `Papers/CONF/S3D108A.lean`, `CONF.hullSigma0` is an
alias) -/
def hullSigma0 (h : Ω → DistC) (A : Ω → Set ℂ) (n : ℕ) : MeasurableSpace Ω :=
  setSigma A ⊔ MeasurableSpace.generateFrom
    {E | ∃ (S : Set ℂ) (F : Set Ω), MeasurableSet[fieldSigma0On h (interior S)] F ∧
      E = {ω | dyadicHull n (A ω) = S} ∩ F}

/-- `σ(A, h|_A)` modulo additive constants `:= ⋂_n hullSigma0 h A n` (CONF l. 474 read with
"`h` viewed modulo additive constant", C:1154; D108) -/
def localSigma0 (h : Ω → DistC) (A : Ω → Set ℂ) : MeasurableSpace Ω :=
  ⨅ n : ℕ, hullSigma0 h A n

/-- `A` is a local set of `h` modulo additive constants (determined form, as `IsLocalSetDet`,
D32, D108): `{A ⊆ U}` is a.s. an event of `σ(h|_U mod const)` (CONF C:1431–1432) -/
def IsLocalSetDet0 (P : Measure Ω) (h : Ω → DistC) (A : Ω → Set ℂ) : Prop :=
  ∀ U : Set ℂ, IsOpen U → AEEventIn P (fieldSigma0On h U) {ω | A ω ⊆ U}

/-- the filtration generated by `(𝓑^•_s(z; D_h), h|_{𝓑^•_s(z;D_h)})`, `s ≤ t` (CONF l. 477,
GM l. 854; D49: the generated filtration `⨆_{s ≤ t}`, a filtration surely) -/
def filledBallSigma (D : DistC → ContMetric) (h : Ω → DistC) (z : ℂ) (t : ℝ) :
    MeasurableSpace Ω :=
  ⨆ (s : ℝ) (_ : s ≤ t), localSigma h (fun ω => filledBall (D (h ω)) z s)

/-- `τ` is a stopping time for the (right-continuous version of the) filtration generated by
`(𝓑^•_s(z;D_h), h|_{𝓑^•_s})` (CONF l. 477, GM l. 854): `{τ < t} ∈ 𝓕_t` for all `t` (optional
time; D49) -/
def IsFilledBallStoppingTime (D : DistC → ContMetric) (h : Ω → DistC) (z : ℂ) (τ : Ω → ℝ) :
    Prop :=
  ∀ t : ℝ, MeasurableSet[filledBallSigma D h z t] {ω | τ ω < t}

/-- the filtration generated by `(cl 𝓑_s(z; D_h), h|_{cl 𝓑_s})`, `s ≤ t`, and its (optional)
stopping times (D49) -/
def IsClosedBallStoppingTime (D : DistC → ContMetric) (h : Ω → DistC) (z : ℂ) (τ : Ω → ℝ) :
    Prop :=
  ∀ t : ℝ, MeasurableSet[⨆ (s : ℝ) (_ : s ≤ t),
    localSigma h (fun ω => closure (ballM (D (h ω)) z s))] {ω | τ ω < t}

end Sigma

end LQGMetric.Blueprint
