/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Blueprint.LMResults at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Blueprint.M2Defs
import LatticeProb.Bonanno.LQGMetric.Field.ZeroBoundary
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic

/-!
# Blueprint: results of LM (Gwynne–Miller, *Local metrics of the Gaussian free field*) used by GM

Source: LM = arXiv:1905.00379, `literature/src/1905.00379/local-metrics-final.tex`. Inventory:
`blueprint/LocalMetrics.md` §0–§2; GM's restatements: GM (`literature/src/1905.00383/
uniqueness-final.tex`) Def 2.3/2.4 (l. 898–913), Thm 2.5 (l. 917–925), Lemma 2.6 (l. 947–958).
Scope (decision D21): `U = ℂ`; Lemma 1.4 for `n = 2`; Lemma 3.1 for `N = 0` metrics (the form
GM Lemma 2.6 uses). Each Prop is stated as LM state it, in these special cases.

* `IsLocalMetric` — LM Def 1.2 (l. 219–221) for `U = ℂ`.
* `LMLem1_4` — LM Lemma 1.4 (`lem-jointly-local`, l. 253–256), `n = 2`.
* `LMThm1_6` — LM Thm 1.6 (`thm-bilip`, l. 291–299), `U = ℂ` (= GM Thm 2.5).
* `LMLem2_1` — LM Lemma 2.1 (`lem-whole-plane-markov`, l. 425–429; = GMSh Lemma 2.2), the case
  `V ∩ ∂𝔻 = ∅` (last sentence of the lemma; the case GM, LM §3 and CONF use).
* `LMLem3_1a`, `LMLem3_1b` — LM Lemma 3.1 (`lem-annulus-iterate`, l. 573–590) parts (1) and (2),
  `N = 0` (= GM Lemma 2.6, l. 947–958).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.Blueprint

/-- **LM Definition 1.2** (l. 219–221), `U = ℂ`: `(h, D)` a coupling of `h` with a random
continuous length metric; `D` is *local* for `h` if for every open `V`, `D(·,·;V)` is conditionally
independent of `(h|_{ℂ∖V}, D(·,·;ℂ∖cl V))` given `h|_V`. -/
def IsLocalMetric {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistC)
    (D : Ω → ContMetric) : Prop :=
  Measurable D ∧ (∀ᵐ ω ∂P, (D ω).IsLength) ∧
    ∀ V : TopologicalSpace.Opens ℂ,
      CondIndepEv (fieldSigma h V) (famSigma (internalFam D) V)
        (fieldSigmaClosed h (V : Set ℂ)ᶜ ⊔ famSigma (internalFam D) (closure (V : Set ℂ))ᶜ) P

/-- **LM Lemma 1.4** (`lem-jointly-local`, l. 253–256), `n = 2`, `U = ℂ`: "Let `(h, D_1, …, D_n)`
be a coupling of a GFF on a domain `U ⊂ ℂ` with `n` random continuous length metrics such that each
`D_j` is local for `h` and `(D_1, …, D_n)` are conditionally independent given `h`. Then
`D_1, …, D_n` are jointly local for `h`." -/
def LMLem1_4 : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (D₁ D₂ : Ω → ContMetric), IsWholePlaneGFF h P →
    IsLocalMetric P h D₁ → IsLocalMetric P h D₂ →
    CondIndepEv (MeasurableSpace.comap h inferInstance) (MeasurableSpace.comap D₁ inferInstance)
      (MeasurableSpace.comap D₂ inferInstance) P →
    IsJointlyLocal2 P h D₁ D₂

/-- **LM Theorem 1.6** (`thm-bilip`, l. 291–299; = GM Thm 2.5, l. 917–925), `U = ℂ`: "Let `ξ ∈ ℝ`,
let `h` be a whole-plane GFF normalized so that `h_1(0) = 0`, … and let `(h, D, D̃)` be a coupling of
`h` with two random continuous metrics … which are jointly local and ξ-additive for `h`. There is a
universal constant `p ∈ (0,1)` such that the following is true. Suppose there is a deterministic
constant `C > 0` such that for each compact set `K` there exists `r_K > 0` such that
`P[sup_{u,v∈∂B_r(z)} D̃(u,v; B_{2r}(z) ∖ cl B_{r/2}(z)) ≤ C D(∂B_{r/2}(z), ∂B_r(z))] ≥ p` for all
`z ∈ K`, `r ∈ (0, r_K]`. Then a.s. `D̃(z,w) ≤ C D(z,w)` for each `z, w`." -/
def LMThm1_6 : Prop :=
  ∃ p : ℝ, 0 < p ∧ p < 1 ∧
    ∀ (ξ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC) (D D' : Ω → ContMetric), IsNormalizedWPGFF h P → IsXiAdditive2 ξ P h D D' →
      ∀ C : ℝ, 0 < C →
      (∀ K : Set ℂ, IsCompact K → ∃ rK : ℝ, 0 < rK ∧ ∀ z ∈ K, ∀ r ∈ Ioc (0 : ℝ) rK,
        ENNReal.ofReal p ≤ P {ω | internalDiam (D' ω) (Metric.sphere z r) (annulus z (r / 2) (2 * r))
          ≤ ENNReal.ofReal C * setDist (D ω) (Metric.sphere z (r / 2)) (Metric.sphere z r)}) →
      ∀ᵐ ω ∂P, ∀ z w : ℂ, (D' ω).1 (z, w) ≤ C * (D ω).1 (z, w)

/-- **LM Lemma 2.1** (`lem-whole-plane-markov`, l. 425–429; proven in GMSh = arXiv:1807.07511,
Lemma 2.2), the case `V ∩ ∂𝔻 = ∅` (the lemma's last sentence; then `∂V` is harmonically
non-trivial automatically, since `ℂ ∖ V ⊇ ∂𝔻`): for `h` a whole-plane GFF with `h_1(0) = 0` and
`V` open, `h = 𝔥 + h̊` where `𝔥` is a random distribution which is harmonic on `V` and is
determined by `h|_{ℂ∖V}`, and `h̊` is independent from `𝔥`; "if `V` is disjoint from `∂𝔻`, then `h̊`
is a zero-boundary GFF and is independent from `h|_{ℂ∖V}`." Harmonic on `V`: `𝔥|_V` is given by a
harmonic function. Zero-boundary GFF on `V`: `h̊|_V` is one (`IsZeroBoundaryGFF`) and `h̊` vanishes
off `cl V`. "Determined by" is a.s. equality with a `σ(h|_{ℂ∖V})`-measurable distribution.
The harmonic clause holds almost surely (D61: the source statements are about random objects;
on a null set `h ω` is an arbitrary distribution). -/
def LMLem2_1 : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsNormalizedWPGFF h P → ∀ V : TopologicalSpace.Opens ℂ,
      Disjoint (V : Set ℂ) (Metric.sphere (0 : ℂ) 1) →
    ∃ hh hz : Ω → DistC, (∀ ω, h ω = hh ω + hz ω) ∧
      (∀ᵐ ω ∂P, ∃ g : ℂ → ℝ, InnerProductSpace.HarmonicOnNhd g (V : Set ℂ) ∧
        ∀ φ : TestOn V, restrictTo V (hh ω) φ = ∫ x, g x * φ x) ∧
      (∃ G : Ω → DistC, @Measurable Ω DistC (fieldSigmaClosed h (V : Set ℂ)ᶜ) _ G ∧
        hh =ᵐ[P] G) ∧
      IndepFun hh hz P ∧
      IsZeroBoundaryGFF V (fun ω => restrictTo V (hz ω)) P ∧
      (∀ ω, restrictTo (toOpens (closure (V : Set ℂ))ᶜ isClosed_closure.isOpen_compl) (hz ω) = 0) ∧
      Indep (MeasurableSpace.comap hz inferInstance) (fieldSigmaClosed h (V : Set ℂ)ᶜ) P

/-- `𝒩(K) = #{k ∈ [1, K] : E_{r_k} occurs}` (LM l. 576) -/
def countOcc {Ω : Type} (E : ℕ → Set Ω) (K : ℕ) (ω : Ω) : ℕ := by
  classical exact ((Finset.Icc 1 K).filter fun k => ω ∈ E k).card

/-- the hypotheses of LM Lemma 3.1 with `N = 0` (LM l. 574–576; GM Lemma 2.6, l. 947–952):
`(r_k)` decreasing positive with `r_{k+1}/r_k ≤ s₁`, and each `E_{r_k}` measurable w.r.t.
`σ((h − h_{r_k}(0))|_{A_{s₁r_k, s₂r_k}(0)})`. -/
def AnnulusIterHyp {Ω : Type} (h : Ω → DistC) (s₁ s₂ : ℝ) (r : ℕ → ℝ) (E : ℕ → Set Ω) : Prop :=
  (∀ k, 0 < r k) ∧ Antitone r ∧ (∀ k, r (k + 1) / r k ≤ s₁) ∧
    ∀ k, MeasurableSet[fieldSigma (fun ω => addConst (h ω) (-circleAvg (h ω) (r k) 0))
      (annulus 0 (s₁ * r k) (s₂ * r k))] (E k)

/-- **LM Lemma 3.1 (1)** (`lem-annulus-iterate`, l. 573–585), `N = 0` (= GM Lemma 2.6): "For each
`a > 0` and each `b ∈ (0,1)`, there exists `p = p(a,b,s₁,s₂) ∈ (0,1)` and `c = c(a,b,s₁,s₂) > 0`
such that if `P[E_{r_k}] ≥ p` for all `k`, then `P[𝒩(K) < bK] ≤ c e^{−aK}` for all `K ∈ ℕ`." -/
def LMLem3_1a : Prop :=
  ∀ s₁ s₂ : ℝ, 0 < s₁ → s₁ < s₂ → s₂ < 1 → ∀ a : ℝ, 0 < a → ∀ b : ℝ, 0 < b → b < 1 →
    ∃ p c : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
        IsNormalizedWPGFF h P → ∀ (r : ℕ → ℝ) (E : ℕ → Set Ω), AnnulusIterHyp h s₁ s₂ r E →
        (∀ k, ENNReal.ofReal p ≤ P (E k)) →
        ∀ K : ℕ, P {ω | (countOcc E K ω : ℝ) < b * K} ≤ ENNReal.ofReal (c * Real.exp (-a * K))

end LQGMetric.Blueprint
