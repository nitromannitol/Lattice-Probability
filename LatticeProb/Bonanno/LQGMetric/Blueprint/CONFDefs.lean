/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Blueprint.CONFDefs at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Blueprint.M2Defs
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-!
# Blueprint-side definitions for the CONF results used by GM §§2, 4

Source: Gwynne–Miller, *Confluence of geodesics in Liouville quantum gravity for γ ∈ (0,2)*,
arXiv:1905.00381 (CONF), `literature/src/1905.00381/confluence-final.tex`. All objects are stated
at a general deterministic centre `𝕫` (GM's versions, GM l. 1096–1168; CONF works at centre `0`).

* oriented Jordan parametrizations of `∂𝓑^•_s` (orientation by a continuous angle lift; the Jordan
  property itself is GM.S-Jordan, decision D17) and **leftmost / rightmost geodesics** (CONF
  Lemma 2.4, l. 533–566; CONF never defines "lies to the left"; here they are defined by CONF's
  approximation characterization, see `IsSideGeod`) — a proposed reading;
* `τ_𝕣` (CONF (3.1), l. 1032); the harmonic part `𝔥^U` of `h|_U`; the squares `𝒮^z_ε(V)` (CONF
  (3.4), l. 1124); the sets `𝒰_r(z;δ)`, `U_ε` (l. 1127–1131); the events `E^U_r(z)`, `E_r(z)`
  (l. 1133–1145); the radii `ρ^n_𝕣(z)` (CONF (3.13), l. 1258); `R^ε_𝕣(K)` (CONF (3.16), l. 1289);
  `σ^ε_{s,𝕣}` (CONF (3.17), l. 1295); the regularity event `𝓔_𝕣(a)` (l. 1484–1491);
* `d^U` (CONF (2.18), l. 931) with the prime-end closure read as the Euclidean closure (DV-B11).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.classDefReducibility false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.Blueprint

/-! ## Orientation and leftmost geodesics -/

/-- `φ : ℝ → ℂ` is a `2π`-periodic Jordan parametrization of `Γ`, positively oriented around `z`:
continuous, injective on `[0, 2π)`, with range `Γ`, and a continuous angle lift `θ` of
`φ − z` with `θ(t + 2π) = θ(t) + 2π` (counterclockwise once around `z`). -/
def IsPosJordanParam (Γ : Set ℂ) (z : ℂ) (φ : ℝ → ℂ) : Prop :=
  Continuous φ ∧ (∀ t, φ (t + 2 * Real.pi) = φ t) ∧ InjOn φ (Ico 0 (2 * Real.pi)) ∧
    range φ = Γ ∧ ∃ θ : ℝ → ℝ, Continuous θ ∧ (∀ t, θ (t + 2 * Real.pi) = θ t + 2 * Real.pi) ∧
      ∀ t, φ t - z = (‖φ t - z‖ : ℂ) * Complex.exp ((θ t : ℂ) * Complex.I)

/-- `sup_{t ∈ [0,s]} |P t − Q t|` (Euclidean uniform distance on `[0, s]`) -/
def supDistOn (P Q : ℝ → ℂ) (s : ℝ) : ℝ≥0∞ := ⨆ t ∈ Icc 0 s, edist (P t) (Q t)

/-- **Leftmost (`left = true`) / rightmost (`left = false`) `D`-geodesic** from `z` to
`y ∈ ∂𝓑^•_s(z;D)` (CONF Lemma 2.4, l. 533–566). Reading (CONF gives no definition of "lies to the
left"): `P` is a `D`-geodesic from `z` to `y` (unit speed, length `s`) and the uniform limit on
`[0, s]` of `D`-geodesics `P_n` from `z` to points `y_n = φ(t_n) ∈ ∂𝓑^•_s` with `t_n ↓ t₀`
(left: counterclockwise side, which is the left when standing at `y` looking outward) resp.
`t_n ↑ t₀` (right), where `φ` is a positively oriented Jordan parametrization of `∂𝓑^•_s` and
`φ(t₀) = y`. This is the construction in CONF's proof (l. 548–556: `y_n^-` in the clockwise arc
from a point to `y`, converging to `y` from the left). -/
def IsSideGeod (left : Bool) (D : ContMetric) (z : ℂ) (s : ℝ) (y : ℂ) (P : ℝ → ℂ) : Prop :=
  y ∈ frontier (filledBall D z s) ∧ IsGeodesicL D P s z y ∧
    ∃ φ : ℝ → ℂ, IsPosJordanParam (frontier (filledBall D z s)) z φ ∧ ∃ t₀ : ℝ, φ t₀ = y ∧
      ∃ (t : ℕ → ℝ) (Pn : ℕ → ℝ → ℂ), Tendsto t atTop (𝓝 t₀) ∧
        (∀ n, if left then t₀ < t n else t n < t₀) ∧
        (∀ n, IsGeodesicL D (Pn n) s z (φ (t n))) ∧
        Tendsto (fun n => supDistOn (Pn n) P s) atTop (𝓝 0)

/-- leftmost `D`-geodesic from `z` to `y ∈ ∂𝓑^•_s(z;D)` (see `IsSideGeod`) -/
def IsLeftmostGeod (D : ContMetric) (z : ℂ) (s : ℝ) (y : ℂ) (P : ℝ → ℂ) : Prop :=
  IsSideGeod true D z s y P

/-- the set of points of `∂𝓑^•_t(z;D)` hit by leftmost `D`-geodesics from `z` to `∂𝓑^•_s(z;D)`
(CONF's `X_{t,s}`, l. 1049) -/
def hitSet (D : ContMetric) (z : ℂ) (t s : ℝ) : Set ℂ :=
  {x | x ∈ frontier (filledBall D z t) ∧ ∃ y P, IsLeftmostGeod D z s y P ∧ ∃ u ∈ Icc 0 s, P u = x}

/-- an arc of `∂𝓑^•_s` (decision D17 / DEC-B J2: a connected subset of the Jordan curve) -/
def IsBdyArc (D : ContMetric) (z : ℂ) (s : ℝ) (I : Set ℂ) : Prop :=
  I ⊆ frontier (filledBall D z s) ∧ IsConnected I

/-- `d^U(z, w) = inf {diam X : X ⊆ U connected, z, w ∈ Cl′(X)}` (CONF (2.18), l. 931), with the
prime-end closure `Cl′(X)` read as the Euclidean closure (DV-B11; exact for Jordan boundaries) -/
def dU (U : Set ℂ) (z w : ℂ) : ℝ≥0∞ :=
  ⨅ (X : Set ℂ) (_ : X ⊆ U) (_ : IsConnected X) (_ : z ∈ closure X) (_ : w ∈ closure X),
    Metric.ediam X

/-! ## Random objects of CONF §3 -/

section Random
variable {Ω : Type} [MeasurableSpace Ω]

/-- `τ_𝕣 := inf {s > 0 : 𝓑^•_s(𝕫; D_h) ⊄ B_𝕣(𝕫)}` (CONF (3.1), l. 1032, at centre `𝕫`) -/
def tauR (D : DistC → ContMetric) (h : Ω → DistC) (z₀ : ℂ) (R : ℝ) (ω : Ω) : ℝ :=
  sInf {s | 0 < s ∧ ¬ filledBall (D (h ω)) z₀ s ⊆ Metric.ball z₀ R}

/-- `H` is the harmonic part `𝔥^U` of `h|_U` (CONF l. 1138; Markov property): `H ω` is harmonic on
`U` and for test functions `φ` supported in `U`, `ψ` supported in `ℂ ∖ cl U` with `∫ψ = 1`,
`E[(h, φ − (∫φ)ψ) | h|_{ℂ∖U}] = (H, φ) − (∫φ)(h, ψ)` (the pairing `φ − (∫φ)ψ` is mean zero).
The conditioning σ-algebra is `σ(h|_{ℂ∖U})` **modulo additive constants**
(`fieldSigmaClosed0 h Uᶜ`; decision D110: CONF C:347, 1154, 1187 normalize `h` away from `U`;
with the raw `fieldSigmaClosed h Uᶜ` no harmonic part exists for a field with a random additive
constant, DEC-110 §1). The definition is constant-covariant: `𝔥^U_{h+c} = 𝔥^U_h + c`
(`CONF.isHarmPart0_addConst_iff`). -/
def IsHarmPart (P : Measure Ω) (h : Ω → DistC) (U : Set ℂ) (H : Ω → ℂ → ℝ) : Prop :=
  (∀ ω, InnerProductSpace.HarmonicOnNhd (H ω) U) ∧
  ∀ φ ψ : TestC, tsupport ⇑φ ⊆ U → tsupport ⇑ψ ⊆ (closure U)ᶜ → ∫ x, ψ x = 1 →
    P[fun ω => h ω (φ - (∫ x, φ x) • ψ) | fieldSigmaClosed0 h Uᶜ] =ᵐ[P]
      fun ω => (∫ x, H ω x * φ x) - (∫ x, φ x) * h ω ψ

open Classical in
/-- a chosen version of the harmonic part (junk `0` if none exists) -/
def harmPart (P : Measure Ω) (h : Ω → DistC) (U : Set ℂ) : Ω → ℂ → ℝ :=
  if hH : ∃ H, IsHarmPart P h U H then hH.choose else fun _ _ => 0

end Random

/-- the square `[x, x+ε] × [y, y+ε]` with `(x, y) = z + ε k` (an element of `𝒮^z_ε`, CONF (3.4)) -/
def confSq (ε : ℝ) (z : ℂ) (k : ℤ × ℤ) : Set ℂ :=
  {w | z.re + k.1 * ε ≤ w.re ∧ w.re ≤ z.re + (k.1 + 1) * ε ∧
    z.im + k.2 * ε ≤ w.im ∧ w.im ≤ z.im + (k.2 + 1) * ε}

/-- indices of the squares of `𝒮^z_ε(V)` (those meeting `V`) -/
def confSqIdx (ε : ℝ) (z : ℂ) (V : Set ℂ) : Set (ℤ × ℤ) := {k | (confSq ε z k ∩ V).Nonempty}

/-- the element of `𝒰_r(z;δ)` obtained by removing the squares `T ⊆ 𝒮^z_{δr}(A_{3r,4r}(z))`
(CONF l. 1127: `A_{3r,4r}(z) ∖ U` is a finite union of `S ∩ A_{3r,4r}(z)`) -/
def confU (r δ : ℝ) (z : ℂ) (T : Finset (ℤ × ℤ)) : Set ℂ :=
  (annulus z (3 * r) (4 * r) : Set ℂ) \ (⋃ k ∈ T, confSq (δ * r) z k)

/-- `U_ε := {u ∈ U : dist(u, ∂U) > ε}` (CONF (3.5), l. 1130; CONF writes `dist(z, ∂U)`, a typo) -/
def innerPart (U : Set ℂ) (ε : ℝ) : Set ℂ := {u | u ∈ U ∧ ε < Metric.infDist u (frontier U)}

/-- the parameters `c, δ ∈ (0,1)`, `A > 0`, `η > 0` of CONF §3.1–3.2 -/
structure CONFParams where
  c : ℝ
  δ : ℝ
  A : ℝ
  η : ℝ

section Random2
variable {Ω : Type} [MeasurableSpace Ω]

/-- the event `E^U_r(z) = E^U_r(z; c, δ, A)` (CONF l. 1133–1141), for `U = confU r δ z T` -/
def confEU (ξ : ℝ) (cc : ℝ → ℝ) (D : DistC → ContMetric) (P : Measure Ω) (h : Ω → DistC)
    (p : CONFParams) (r : ℝ) (z : ℂ) (T : Finset (ℤ × ℤ)) : Set Ω :=
  {ω | ENNReal.ofReal (p.c * scaleFac ξ cc (h ω) r z) ≤
        setDist (D (h ω)) (Metric.sphere z (2 * r)) (Metric.sphere z (3 * r)) ∧
      (∀ k ∈ confSqIdx (p.δ * r) z (annulus z (3 * r) (4 * r)),
        internalDiam (D (h ω)) (confSq (p.δ * r) z k) (annulus z (2 * r) (5 * r)) ≤
          ENNReal.ofReal (p.c / 100 * scaleFac ξ cc (h ω) r z)) ∧
      ∀ u ∈ innerPart (confU r p.δ z T) (p.δ * r / 4),
        |harmPart P h (confU r p.δ z T) ω u - circleAvg (h ω) r z| ≤ p.A}

/-- `E_r(z) := ⋂_{U ∈ 𝒰_r(z;δ)} E^U_r(z)` (CONF (3.6), l. 1144) -/
def confE (ξ : ℝ) (cc : ℝ → ℝ) (D : DistC → ContMetric) (P : Measure Ω) (h : Ω → DistC)
    (p : CONFParams) (r : ℝ) (z : ℂ) : Set Ω :=
  ⋂ (T : Finset (ℤ × ℤ)) (_ : ∀ k ∈ T, k ∈ confSqIdx (p.δ * r) z (annulus z (3 * r) (4 * r))),
    confEU ξ cc D P h p r z T

/-- `ρ^0_𝕣(z) := 𝕣`, `ρ^n_𝕣(z) := inf {r ≥ 6ρ^{n−1}_𝕣(z) : r ∈ 2^ℤ 𝕣, E_r(z) occurs}`
(CONF (3.13), l. 1258), in `[0, ∞]` (`inf ∅ = ∞`) -/
def confRho (ξ : ℝ) (cc : ℝ → ℝ) (D : DistC → ContMetric) (P : Measure Ω) (h : Ω → DistC)
    (p : CONFParams) (R : ℝ) (z : ℂ) : ℕ → Ω → ℝ≥0∞
  | 0 => fun _ => ENNReal.ofReal R
  | n + 1 => fun ω => ⨅ (k : ℤ) (_ : 6 * confRho ξ cc D P h p R z n ω ≤
      ENNReal.ofReal ((2 : ℝ) ^ k * R)) (_ : ω ∈ confE ξ cc D P h p ((2 : ℝ) ^ k * R) z),
      ENNReal.ofReal ((2 : ℝ) ^ k * R)

/-- `⌊η log ε⁻¹⌋` -/
def confN (p : CONFParams) (ε : ℝ) : ℕ := ⌊p.η * Real.log ε⁻¹⌋₊

/-- the grid `m ℤ²` -/
def gridPts (m : ℝ) : Set ℂ := {w | ∃ a b : ℤ, w = ⟨a * m, b * m⟩}

/-- `R^ε_𝕣(K) := 6 sup {ρ^{⌊η log ε⁻¹⌋}_{ε𝕣}(z) : z ∈ (ε𝕣/4)ℤ² ∩ B_{ε𝕣}(K)} + ε𝕣`
(CONF (3.16), l. 1289) -/
def confRK (ξ : ℝ) (cc : ℝ → ℝ) (D : DistC → ContMetric) (P : Measure Ω) (h : Ω → DistC)
    (p : CONFParams) (R ε : ℝ) (K : Set ℂ) (ω : Ω) : ℝ≥0∞ :=
  6 * (⨆ z ∈ gridPts (ε * R / 4) ∩ Metric.thickening (ε * R) K,
    confRho ξ cc D P h p (ε * R) z (confN p ε) ω) + ENNReal.ofReal (ε * R)

/-- the `[0,∞]`-neighbourhood `{x : dist(x, K) < ρ}` -/
def enbhd (ρ : ℝ≥0∞) (K : Set ℂ) : Set ℂ := {x | Metric.infEDist x K < ρ}

/-- the filled ball at a radius in `[0, ∞]` (`𝓑^•_∞ := ℂ`) -/
def filledBallE (D : ContMetric) (z : ℂ) (s : ℝ≥0∞) : Set ℂ :=
  if s = ⊤ then univ else filledBall D z s.toReal

/-- `σ^ε_{s,𝕣} := inf {s′ > s : B_{R^ε_𝕣(𝓑^•_s)}(𝓑^•_s) ⊆ 𝓑^•_{s′}}` (CONF (3.17), l. 1295),
centre `𝕫`, in `[0, ∞]` -/
def confSigma (ξ : ℝ) (cc : ℝ → ℝ) (D : DistC → ContMetric) (P : Measure Ω) (h : Ω → DistC)
    (p : CONFParams) (z₀ : ℂ) (R ε s : ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨅ (s' : ℝ) (_ : s < s') (_ : enbhd (confRK ξ cc D P h p R ε (filledBall (D (h ω)) z₀ s) ω)
      (filledBall (D (h ω)) z₀ s) ⊆ filledBall (D (h ω)) z₀ s'), ENNReal.ofReal s'

/-- the regularity event `𝓔^𝕫_𝕣(a)` (CONF l. 1484–1491, at centre `𝕫` as GM S2.7, l. 1153–1158).
Condition 2 is read with `e^{+ξ h_𝕣(𝕫)}` (CONF prints `e^{−ξ h_𝕣(0)}`, a sign typo: with the minus
sign Lemma 3.8 fails for small `𝕣`). `χ` is the fixed Hölder exponent in `(0, ξ(Q−2))`. -/
def confReg (ξ : ℝ) (cc : ℝ → ℝ) (D : DistC → ContMetric) (P : Measure Ω) (h : Ω → DistC)
    (p : CONFParams) (χ : ℝ) (z₀ : ℂ) (R a : ℝ) : Set Ω :=
  {ω | Metric.ball z₀ (a * R) ⊆ filledBall (D (h ω)) z₀ (tauR D h z₀ R ω) ∧
    a * scaleFac ξ cc (h ω) R z₀ ≤ tauR D h z₀ (3 * R) ω - tauR D h z₀ (2 * R) ω ∧
    (∀ u ∈ Metric.ball z₀ (4 * R), ∀ v ∈ Metric.ball z₀ (4 * R), ‖u - v‖ / R ≤ a →
      (scaleFac ξ cc (h ω) R z₀)⁻¹ * (D (h ω)).1 (u, v) ≤ (‖u - v‖ / R) ^ χ) ∧
    ∀ (j : ℕ), (2 : ℝ)⁻¹ ^ j ≤ a → ∀ z ∈ gridPts ((2 : ℝ)⁻¹ ^ j * R / 4) ∩ Metric.ball z₀ (4 * R),
      confRho ξ cc D P h p ((2 : ℝ)⁻¹ ^ j * R) z (confN p ((2 : ℝ)⁻¹ ^ j)) ω ≤
        ENNReal.ofReal (((2 : ℝ)⁻¹ ^ j) ^ (1 / 2 : ℝ) * R)}

/-- `σ(𝓑^•_T, h|_{𝓑^•_T})` for a random radius `T ∈ [0, ∞]` -/
def filledBallSigmaAt (D : DistC → ContMetric) (h : Ω → DistC) (z₀ : ℂ) (T : Ω → ℝ≥0∞) :
    MeasurableSpace Ω :=
  localSigma h (fun ω => filledBallE (D (h ω)) z₀ (T ω))

/-- `σ(𝓑^•_T, h|_{𝓑^•_T})` modulo additive constants, `T ∈ [0, ∞]` (D108; moved from
`Papers/CONF/S3D108A.lean` by D110 P1, `CONF.filledBallSigmaAt0` is an alias) -/
def filledBallSigmaAt0 (D : DistC → ContMetric) (h : Ω → DistC) (z₀ : ℂ) (T : Ω → ℝ≥0∞) :
    MeasurableSpace Ω :=
  localSigma0 h (fun ω => filledBallE (D (h ω)) z₀ (T ω))

end Random2

end LQGMetric.Blueprint
