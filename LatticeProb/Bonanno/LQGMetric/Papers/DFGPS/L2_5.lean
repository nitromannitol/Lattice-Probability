/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_5 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_9
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_10
import LatticeProb.Bonanno.LQGMetric.Metric.InternalLimitC

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.5 (`lem-lfpp-tight`, T:817–830): statement

"Let `h` be a whole-plane GFF plus a bounded continuous function.
A. The laws of the metrics `𝔞_ε⁻¹ D_h^ε` are tight w.r.t. the local uniform topology on `ℂ × ℂ`
and any subsequential limit of these laws is supported on continuous length metrics on `ℂ`.
B. Let `𝒲` be the (countable) set of all dyadic domains. For any sequence of positive `ε`'s
tending to zero, there is a subsequence `ℰ` and a coupling of a continuous length metric `D_h` on
`ℂ` and a length metric `D_{h,W}` on `W̄` for each `W ∈ 𝒲` which induces the Euclidean topology
on `W̄` such that … along `ℰ`, we have the convergence of joint laws
`(𝔞_ε⁻¹ D_h^ε, {𝔞_ε⁻¹ D_h^ε(·,·;W̄)}_{W∈𝒲}) → (D_h, {D_{h,W}}_{W∈𝒲})` … Furthermore, for each
`W ∈ 𝒲` we have the a.s. equality of internal metrics `D_{h,W}(·,·;W) = D_h(·,·;W)`."

Readings: laws on `C(ℂ × ℂ, ℝ)` (local uniform topology) and on the countable product
`C(ℂ × ℂ, ℝ) × Π_{W ∈ 𝒲} C(W̄ × W̄, ℝ)` (uniform topology on each factor); "subsequential limit"
along `ε_n → 0` (BP-DF-1); the coupling is the limit law `μ`. In B the dyadic domains are those
with connected closure (`dyadicDomainsC`, see `Lem2_9`, DF-L29-CONN). The internal metric of
`D_{h,W}` on `W` is taken in the metric space `(W̄, D_{h,W})` (form of `lem2_11`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint MetricGeometry

/-- `(z, w) ↦ 𝔞_ε⁻¹ D_h^ε(z, w)` as an element of `C(ℂ × ℂ, ℝ)` (junk `0` if discontinuous) -/
def lfppC (ξ ε : ℝ) (h : DistC) : C(ℂ × ℂ, ℝ) :=
  toCMap fun p => (aEpsDF ξ ε)⁻¹ * lfppDist ξ ε h p

/-- `d` is a continuous length metric on `ℂ` -/
def IsContLengthMetric (d : C(ℂ × ℂ, ℝ)) : Prop :=
  ∃ hd : IsContinuousMetric d, ContMetric.IsLength ⟨d, hd⟩

/-- **DFGPS Lemma 2.5 A** (T:822). -/
def Lem2_5A : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsGFFPlusBddCont h P →
      IsTightMeasureSet {μ | ∃ ε ∈ Ioo (0 : ℝ) 1, μ = P.map fun ω => lfppC (xiGamma γ) ε (h ω)} ∧
      ∀ (εn : ℕ → ℝ) (ν : ℕ → ProbabilityMeasure C(ℂ × ℂ, ℝ)) (μ : ProbabilityMeasure C(ℂ × ℂ, ℝ)),
        (∀ n, εn n ∈ Ioo (0 : ℝ) 1 ∧
          (ν n : Measure _) = P.map fun ω => lfppC (xiGamma γ) (εn n) (h ω)) →
        Tendsto εn atTop (𝓝 0) → Tendsto ν atTop (𝓝 μ) →
        ∀ᵐ d ∂(μ : Measure C(ℂ × ℂ, ℝ)), IsContLengthMetric d

/-- the dyadic domains with connected closure -/
def dyadicDomainsC : Set (Set ℂ) := {W | LFPP.IsDyadicDomain W ∧ IsConnected (closure W)}

/-- the family `{d_W}_{W ∈ 𝒲}` of metrics on the `W̄` -/
abbrev DyFam : Type := (W : dyadicDomainsC) → C(closure (W : Set ℂ) × closure (W : Set ℂ), ℝ)

/-- the state space `C(ℂ × ℂ, ℝ) × Π_{W ∈ 𝒲} C(W̄ × W̄, ℝ)` of the joint laws of Lemma 2.5 B,
with the product topology and its Borel σ-algebra -/
def DyProd : Type := C(ℂ × ℂ, ℝ) × DyFam

instance : TopologicalSpace DyProd := inferInstanceAs (TopologicalSpace (C(ℂ × ℂ, ℝ) × DyFam))
instance : MeasurableSpace DyProd := borel DyProd
instance : BorelSpace DyProd := ⟨rfl⟩

/-- the limit object of DFGPS Lemma 2.5 B: `D` a continuous length metric on `ℂ`; each `d_W` a
length metric on `W̄` inducing its topology, whose internal metric on `W` is that of `D`. -/
def IsDyadicLimit (x : DyProd) : Prop :=
  IsContLengthMetric x.1 ∧ ∀ W : dyadicDomainsC, ∃ hd : IsMetricFun ⇑(x.2 W),
    IsLengthMetricFun ⇑(x.2 W) hd ∧ Continuous (MetricFunSpace.pt _ hd) ∧
    Continuous (metricFunSpaceVal _ hd) ∧ ∀ hc : IsContinuousMetric x.1,
      ∀ u v : closure (W : Set ℂ), u.1 ∈ (W : Set ℂ) → v.1 ∈ (W : Set ℂ) →
        ContMetric.internal ⟨x.1, hc⟩ W u v = internalEDist
          {y : MetricFunSpace _ hd | (metricFunSpaceVal _ hd y).1 ∈ (W : Set ℂ)}
          (MetricFunSpace.pt _ hd u) (MetricFunSpace.pt _ hd v)

/-- **DFGPS Lemma 2.5 B** (T:823–829). -/
def Lem2_5B : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
      IsGFFPlusBddCont h P → ∀ εk : ℕ → ℝ, (∀ k, 0 < εk k) → Tendsto εk atTop (𝓝 0) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ μ : ProbabilityMeasure DyProd,
        (∀ ν : ℕ → ProbabilityMeasure DyProd,
          (∀ n, (ν n : Measure DyProd) = Measure.map (β := DyProd) (fun ω => ((lfppC (xiGamma γ) (εk (φ n)) (h ω),
            fun W : dyadicDomainsC => lfppSqC (xiGamma γ) (εk (φ n)) (h ω) (closure W)) : DyProd)) P) →
          Tendsto ν atTop (𝓝 μ)) ∧
        ∀ᵐ x ∂(μ : Measure DyProd), IsDyadicLimit x

/-- **DFGPS Lemma 2.5** (`lem-lfpp-tight`, T:817–830). -/
def Lem2_5 : Prop := Lem2_5A ∧ Lem2_5B

end LQGMetric.DFGPS
