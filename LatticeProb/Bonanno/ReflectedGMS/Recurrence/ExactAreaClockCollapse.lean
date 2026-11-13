/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Recurrence.ExactAreaClockCollapse at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Recurrence.ExactAreaClockCollapseLaplace
import LatticeProb.Bonanno.ReflectedGMS.Recurrence.AreaClockLevelZeroFiniteness
import LatticeProb.Bonanno.ReflectedGMS.Process.ExactHoldingIntervalLength
import LatticeProb.Bonanno.ReflectedGMS.Process.FastClockTimeChange

/-!
# The two area-clock residuals are one: `hexactclock` from `EnvironmentWalkData`

`EnvironmentWalkDataProducer.AreaClockReachesLevelZeroIndices` (`hclock`) and its exact-holding
twin `ExactExponentialTimeChange.ExactAreaClockReachesLevelZeroIndices` (`hexactclock`) are the
same clock `τ_{[(0,K)]}` of `ReflectedWalk.IndexSet` evaluated at two holding families:

* the sample's own i.i.d. unit exponentials `ω.2`, so `τ = ∑_ξ c_ξ E_ξ`;
* the unit family `fun _ => 1`, so `τ = ∑_ξ c_ξ`,

with the *same* weights `c_ξ = 1/w(Y_ξ)` on `{ξ ∈ Ξ : ξ < [(0,K)]}`, which depend on the chain
path `Y = ω.1` only (`tau_eq_tsum_ofReal_mul`).  This file proves the hard direction
`∑ c_ξ E_ξ < ∞ a.s. ⟹ ∑ c_ξ < ∞ a.s.` and with it `hexactclock` outright.

## The argument

* **Conditionally on the path** (`expFamily_ae_tau_eq_top_of_tau_one_eq_top`): for a *fixed*
  `Y` the weights are deterministic, so if `∑ c_ξ = ∞` then `∑ c_ξ E_ξ = ∞` for
  `expFamily`-almost every `E`.  This is
  `ExactAreaClockCollapseLaplace.ae_tsum_ofReal_mul_eq_top` (Laplace transform; no
  three-series theorem).
* **Fubini** (`sampleLaw_ae_tau_eq_top_of_tau_one_eq_top`): `Existence.sampleLaw D hG z` is
  *definitionally* the product `(D.coupling hG (D.nz z) z).prod expFamily`, so
  `Measure.ae_prod_iff_ae_ae` turns the path-by-path statement into a joint one.  Its
  measurability hypothesis is supplied by `ReflectedWalk.PathProperties.measurable_tau`, once
  for each holding family; the index `[(0,K)] = Finsupp.single 0 K` does not depend on the path
  (`IndexSet.addr_zero`), which is what makes the event measurable.
* **Contraposition** (`sampleLaw_ae_tau_one_addr_zero_lt_top`): almost surely, for every `K`,
  `τ¹_{[(0,K)]} = ∞ ⟹ τ^E_{[(0,K)]} = ∞`; so finiteness of the exponential clock forces
  finiteness of the exact one.  This holds for **every** positive rate `w`.

## Consequences

* `exactAreaClockReachesLevelZeroIndices_of_areaClockReachesLevelZeroIndices`: `hclock ⟹
  hexactclock`, for one environment and one exhaustion.
* `ae_exactAreaClockReachesLevelZeroIndices_of_environmentWalkData`: the `hexactclock` input of
  `PathwiseClockClauseResidual.ae_hlift_of_clock_residuals`, **verbatim**, proved for every
  environment measure `ν` with no hypothesis — through the already-closed `hclock`
  (`AreaClockLevelZeroFiniteness.areaClockReachesLevelZeroIndices_of_environmentWalkData`).
* `ae_hlift_of_regularSpatialExtension`: `hlift` from `hreg` alone.
* `reflectedInvarianceConclusions_of_named_inputs_no_clock_residuals`: the invariance reduction
  with `hlift` replaced by `hreg`; its named open inputs are `hΦ`, `hdata`, `hreg`,
  `hbracket`, `hlimit`.  It is an implication, not a proof of the invariance principle.
-/

-- Merged from `ReflectedGMS/Process/PathwiseClockClauseResidual.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_PathwiseClockClauseResidual

/-!
# `hlift` from `hreg` and one new residual

`Process/PathwiseClockClauseLift.ae_hlift_of_atomic_inputs` reduces the `hlift`
input of the invariance assembly to four atomic inputs `hfast`, `hexact`,
`hhold`, `hreg`.  Three of them are discharged in this directory:

| input | discharged by | cost |
|-------|---------------|------|
| `hfast` | `FastClockTimeChange.ae_hfast_of_clock_residual` | **nothing** — the assembly's own `hclock` |
| `hexact` | `ExactExponentialTimeChange.ae_hexact_of_clock_residuals` | `hclock` + `hexactclock` |
| `hhold` | `ExactHoldingIntervalLength.ae_hhold_of_exact_clock_residual` | `hexactclock` |

`hclock` is *already* an input of
`InvarianceAssemblyNoReturn.reflectedInvarianceConclusions_of_named_inputs_no_return`,
so the net new obligation of all three is the single environment-level clause

  `ExactExponentialTimeChange.ExactAreaClockReachesLevelZeroIndices`,

the exact-holding twin of the project's existing area-clock residual: for every
starting cell, almost surely `∑_{ξ < [(0,K)]} a_{Y_ξ}/π(Y_ξ) < ∞` for every `K`.

`hreg` — the regular spatial extension — is untouched here; it is the open
spatial-extension construction and belongs to its own packet.

Nothing in this file certifies `hclock`, `hexactclock` or `hreg`.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ReflectedGMS.PathwiseClockClauseResidual

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients
open HarmonicMainStatement StatementIngredients AreaClocks SpatialEnds
open ReflectedWalk
open InvarianceMainStatement QuenchedFormulation
open ReflectedGMS.InvarianceAssembly ReflectedGMS.EnvironmentWalkDataProducer
open ReflectedGMS.ExactExponentialTimeChange

/-- **The `hlift` input of the invariance assembly, from `hreg` and two clock
residuals.**

This is `PathwiseClockClauseLift.ae_hlift_of_atomic_inputs` with its `hfast`,
`hexact` and `hhold` arguments supplied.  Of the two clock hypotheses, `hclock`
is verbatim an input the assembly already carries, so the *new* obligation
created by this reduction is `hexactclock` alone. -/
theorem ae_hlift_of_clock_residuals (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν) (Φ : CellField)
    (hclock : ∀ᵐ e ∂ν, ∀ hnt : Nontrivial (Vertex e.val),
      letI := hnt
      ∀ (D : (decode e).graph.Exhaustion)
        (hG : (decode e).graph.toSimpleGraph.Connected),
        EnvironmentWalkData e D hG → AreaClockReachesLevelZeroIndices e D hG)
    (hexactclock : ∀ᵐ e ∂ν, ∀ hnt : Nontrivial (Vertex e.val),
      letI := hnt
      ∀ (D : (decode e).graph.Exhaustion)
        (hG : (decode e).graph.toSimpleGraph.Connected),
        EnvironmentWalkData e D hG → ExactAreaClockReachesLevelZeroIndices e D hG)
    (hreg : ∀ n : ℕ, ∀ᵐ e ∂ν, ∀ hn : (e.val.1 n).isSome,
      ∀ hnt : Nontrivial (Vertex e.val),
        letI := hnt
        ∀ (D : (decode e).graph.Exhaustion)
          (hG : (decode e).graph.toSimpleGraph.Connected),
          EnvironmentWalkData e D hG →
          ∀ Xexp : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e),
            (∀ᵐ ω ∂(areaSampleLaw (decode e) D hG ⟨n, hn⟩),
              (∀ t, collapse (Xexp t ω) = exponentialAreaPath (decode e) D t ω) ∧
              IsEndLabeling (decode e) (fun t => Xexp t ω) ∧
              AvoidsSpatialInfinity (decode e) (fun t => Xexp t ω)) →
            ∃ M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane,
              ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG ⟨n, hn⟩),
                RegularSpatialExtension (decode e) (Φ.at e)
                  (fun t => Xexp t ω) (fun t => M t ω)) :
    ∀ n : ℕ, ∀ᵐ e ∂ν, ∀ hn : (e.val.1 n).isSome,
      ∀ hnt : Nontrivial (Vertex e.val),
        letI := hnt
        ∀ (D : (decode e).graph.Exhaustion)
          (hG : (decode e).graph.toSimpleGraph.Connected),
          EnvironmentWalkData e D hG →
          ∃ (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
            (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane),
            PathwiseClockClauses e D hG Φ ⟨n, hn⟩ Xexp Xexact M :=
  PathwiseClockClauseLift.ae_hlift_of_atomic_inputs ν hmt hFE Φ
    (FastClockTimeChange.ae_hfast_of_clock_residual ν hclock)
    (ExactExponentialTimeChange.ae_hexact_of_clock_residuals ν hclock hexactclock)
    (ExactHoldingIntervalLength.ae_hhold_of_exact_clock_residual ν hexactclock)
    hreg

end ReflectedGMS.PathwiseClockClauseResidual

end Merged_PathwiseClockClauseResidual

set_option autoImplicit false

open MeasureTheory
open scoped NNReal ENNReal

namespace ReflectedGMS.ExactAreaClockCollapse

universe u

/-! ## The clock as a weighted series of the unit holding times -/

section Deterministic

open ReflectedWalk.IndexSet

variable {V : Type u}

/-- **The clock `τ_η` is the weighted series `∑_ξ E_ξ c_ξ`**, with the path-dependent,
`E`-independent weights `c_ξ = 1/w(Y_ξ)` on `{ξ ∈ Ξ : ξ < η}` and `0` elsewhere.  Nothing is
assumed of `E` or `w`. -/
theorem tau_eq_tsum_ofReal_mul (Gs : ℕ → Set V) (Y : ℕ → ℕ → V) (w : V → ℝ)
    (E : (ℕ →₀ ℕ) → ℝ) (η : ℕ →₀ ℕ) :
    tau Gs Y w E η =
      ∑' a, ENNReal.ofReal (E a * (below Gs Y η).indicator (fun b => 1 / w (Yxi Gs Y b)) a) := by
  unfold tau
  refine tsum_congr fun a => ?_
  by_cases ha : a ∈ below Gs Y η
  · simp only [Set.indicator_of_mem ha, holding]
    exact congrArg ENNReal.ofReal (div_eq_mul_one_div (E a) (w (Yxi Gs Y a)))
  · simp only [Set.indicator_of_notMem ha, mul_zero, ENNReal.ofReal_zero]

/-- **The exact clock is the plain series of the same weights.** -/
theorem tau_one_eq_tsum_ofReal (Gs : ℕ → Set V) (Y : ℕ → ℕ → V) (w : V → ℝ)
    (η : ℕ →₀ ℕ) :
    tau Gs Y w (fun _ => 1) η =
      ∑' a, ENNReal.ofReal ((below Gs Y η).indicator (fun b => 1 / w (Yxi Gs Y b)) a) := by
  rw [tau_eq_tsum_ofReal_mul]
  simp only [one_mul]

end Deterministic

/-! ## Conditionally on the chain path -/

section PerPath

open ReflectedWalk ReflectedWalk.IndexSet

variable {V : Type u}

/-- **For a fixed path, an infinite exact clock forces an infinite exponential clock**, for
`expFamily`-almost every family of unit holding times.  The weights `1/w(Y_ξ)` are
deterministic once the path is fixed, and nonnegative because `w > 0`. -/
theorem expFamily_ae_tau_eq_top_of_tau_one_eq_top (Gs : ℕ → Set V) (Y : ℕ → ℕ → V)
    {w : V → ℝ} (hw : ∀ x, 0 < w x) (η : ℕ →₀ ℕ)
    (h1 : tau Gs Y w (fun _ => 1) η = ⊤) :
    ∀ᵐ E ∂expFamily, tau Gs Y w E η = ⊤ := by
  have hc : ∀ a, 0 ≤ (below Gs Y η).indicator (fun b => 1 / w (Yxi Gs Y b)) a :=
    Set.indicator_nonneg fun b _ => (one_div_pos.mpr (hw (Yxi Gs Y b))).le
  have hsum : ∑' a, ENNReal.ofReal ((below Gs Y η).indicator (fun b => 1 / w (Yxi Gs Y b)) a)
      = ⊤ := (tau_one_eq_tsum_ofReal Gs Y w η).symm.trans h1
  have h : ∀ᵐ E ∂expFamily, ∑' a, ENNReal.ofReal
      (E a * (below Gs Y η).indicator (fun b => 1 / w (Yxi Gs Y b)) a) = ⊤ :=
    ExactAreaClockCollapseLaplace.ae_tsum_ofReal_mul_eq_top hc hsum
  filter_upwards [h] with E hE
  rw [tau_eq_tsum_ofReal_mul]
  exact hE

end PerPath

/-! ## Fubini over the product structure of the sample law -/

section Sample

open ReflectedWalk ReflectedWalk.IndexSet

variable {V : Type u} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
  [Nontrivial V] {G : ConductanceGraph V}

/-- **Under `P_z`, almost surely an infinite exact clock forces an infinite exponential
clock**, for one fixed index `η`.  `Existence.sampleLaw D hG z` is definitionally
`(D.coupling hG (D.nz z) z).prod expFamily`; the event is measurable by
`PathProperties.measurable_tau`, and `Measure.ae_prod_iff_ae_ae` reduces it to
`expFamily_ae_tau_eq_top_of_tau_one_eq_top` path by path. -/
theorem sampleLaw_ae_tau_eq_top_of_tau_one_eq_top (D : G.Exhaustion)
    (hG : G.toSimpleGraph.Connected) {w : V → ℝ} (hw : ∀ x, 0 < w x) (z : V)
    (η : ℕ →₀ ℕ) :
    ∀ᵐ ω ∂Existence.sampleLaw D hG z,
      tau (D.levelSets (D.nz z)) ω.1 w (fun _ => 1) η = ⊤ →
        tau (D.levelSets (D.nz z)) ω.1 w ω.2 η = ⊤ := by
  have h1 : MeasurableSet {ω : (ℕ → ℕ → V) × ((ℕ →₀ ℕ) → ℝ) |
      tau (D.levelSets (D.nz z)) ω.1 w (fun _ => 1) η = ⊤} :=
    (PathProperties.measurable_tau (Ω := (ℕ → ℕ → V) × ((ℕ →₀ ℕ) → ℝ))
      (D.levelSets (D.nz z)) w (Y := Prod.fst) (E := fun _ _ => (1 : ℝ))
      measurable_fst measurable_const η) (measurableSet_singleton ⊤)
  have h2 : MeasurableSet {ω : (ℕ → ℕ → V) × ((ℕ →₀ ℕ) → ℝ) |
      tau (D.levelSets (D.nz z)) ω.1 w ω.2 η = ⊤} :=
    (PathProperties.measurable_tau (Ω := (ℕ → ℕ → V) × ((ℕ →₀ ℕ) → ℝ))
      (D.levelSets (D.nz z)) w measurable_fst measurable_snd η) (measurableSet_singleton ⊤)
  have hmeas : MeasurableSet {ω : (ℕ → ℕ → V) × ((ℕ →₀ ℕ) → ℝ) |
      tau (D.levelSets (D.nz z)) ω.1 w (fun _ => 1) η = ⊤ →
        tau (D.levelSets (D.nz z)) ω.1 w ω.2 η = ⊤} :=
    h1.imp h2
  have hprod : ∀ᵐ ω ∂(D.coupling hG (D.nz z) z).prod expFamily,
      tau (D.levelSets (D.nz z)) ω.1 w (fun _ => 1) η = ⊤ →
        tau (D.levelSets (D.nz z)) ω.1 w ω.2 η = ⊤ := by
    refine (Measure.ae_prod_iff_ae_ae hmeas).2 (Filter.Eventually.of_forall fun y => ?_)
    by_cases hy : tau (D.levelSets (D.nz z)) y w (fun _ => 1) η = ⊤
    · filter_upwards [expFamily_ae_tau_eq_top_of_tau_one_eq_top (D.levelSets (D.nz z)) y hw η hy]
        with E hE
      exact fun _ => hE
    · exact Filter.Eventually.of_forall fun _ h => absurd h hy
  exact hprod

/-- **The exact level-`0` clock is finite whenever the exponential one is**, for an arbitrary
positive rate `w`: the finiteness half of (3.16) transfers from the exponential holding family
to the unit one. -/
theorem sampleLaw_ae_tau_one_addr_zero_lt_top (D : G.Exhaustion)
    (hG : G.toSimpleGraph.Connected) {w : V → ℝ} (hw : ∀ x, 0 < w x) (z : V)
    (hexp : ∀ᵐ ω ∂Existence.sampleLaw D hG z, ∀ K : ℕ,
      tau (D.levelSets (D.nz z)) ω.1 w ω.2 (addr (D.levelSets (D.nz z)) ω.1 0 K) < ⊤) :
    ∀ᵐ ω ∂Existence.sampleLaw D hG z, ∀ K : ℕ,
      tau (D.levelSets (D.nz z)) ω.1 w (fun _ => 1) (addr (D.levelSets (D.nz z)) ω.1 0 K) < ⊤ := by
  have himp : ∀ᵐ ω ∂Existence.sampleLaw D hG z, ∀ K : ℕ,
      tau (D.levelSets (D.nz z)) ω.1 w (fun _ => 1) (Finsupp.single 0 K) = ⊤ →
        tau (D.levelSets (D.nz z)) ω.1 w ω.2 (Finsupp.single 0 K) = ⊤ :=
    ae_all_iff.2 fun K =>
      sampleLaw_ae_tau_eq_top_of_tau_one_eq_top D hG hw z (Finsupp.single 0 K)
  filter_upwards [hexp, himp] with ω hτ hi K
  have hK := hτ K
  simp only [ReflectedWalk.IndexSet.addr_zero] at hK ⊢
  exact lt_top_iff_ne_top.2 fun h => lt_top_iff_ne_top.1 hK (hi K h)

end Sample

/-! ## The environment level: `hexactclock` -/

section Environment

open Code EnvironmentFields StatementIngredients AreaClocks
open ReflectedWalk ReflectedWalk.IndexSet QuenchedFormulation
open ReflectedGMS.EnvironmentWalkDataProducer ReflectedGMS.ExactExponentialTimeChange

/-- **The two area-clock residuals are one**: `hclock ⟹ hexactclock`, for one environment and
one exhaustion. -/
theorem exactAreaClockReachesLevelZeroIndices_of_areaClockReachesLevelZeroIndices
    (e : Env) [Nontrivial (Vertex e.val)] (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected)
    (h3 : AreaClockReachesLevelZeroIndices e D hG) :
    ExactAreaClockReachesLevelZeroIndices e D hG := by
  intro z
  exact sampleLaw_ae_tau_one_addr_zero_lt_top D hG (areaRate_pos e) z (h3 z)

/-- **`ExactAreaClockReachesLevelZeroIndices` from the walk data**, unconditionally: the
walk data give `hclock`
(`AreaClockLevelZeroFiniteness.areaClockReachesLevelZeroIndices_of_environmentWalkData`), and
`hclock` gives its exact twin. -/
theorem exactAreaClockReachesLevelZeroIndices_of_environmentWalkData
    (e : Env) [Nontrivial (Vertex e.val)] (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected) (hdat : EnvironmentWalkData e D hG) :
    ExactAreaClockReachesLevelZeroIndices e D hG :=
  exactAreaClockReachesLevelZeroIndices_of_areaClockReachesLevelZeroIndices e D hG
    (AreaClockLevelZeroFiniteness.areaClockReachesLevelZeroIndices_of_environmentWalkData
      e D hG hdat)

/-- **The `hexactclock` input of `PathwiseClockClauseResidual.ae_hlift_of_clock_residuals`,
proved.**  The statement is copied verbatim from that theorem; it holds for every measure `ν`
on environments, with no hypothesis whatsoever. -/
theorem ae_exactAreaClockReachesLevelZeroIndices_of_environmentWalkData (ν : Measure Env) :
    ∀ᵐ e ∂ν, ∀ hnt : Nontrivial (Vertex e.val),
      letI := hnt
      ∀ (D : (decode e).graph.Exhaustion)
        (hG : (decode e).graph.toSimpleGraph.Connected),
        EnvironmentWalkData e D hG → ExactAreaClockReachesLevelZeroIndices e D hG := by
  refine Filter.Eventually.of_forall fun e hnt => ?_
  intro D hG hdat
  exact @exactAreaClockReachesLevelZeroIndices_of_environmentWalkData e hnt D hG hdat

end Environment

/-! ## `hlift` from `hreg` alone -/

section Lift

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients
open HarmonicMainStatement StatementIngredients AreaClocks SpatialEnds
open ReflectedWalk
open InvarianceMainStatement QuenchedFormulation
open ReflectedGMS.InvarianceAssembly ReflectedGMS.EnvironmentWalkDataProducer
open ReflectedGMS.ExactExponentialTimeChange

/-- **The `hlift` input of the invariance assembly, from `hreg` alone.**
`PathwiseClockClauseResidual.ae_hlift_of_clock_residuals` with `hclock` discharged by
`AreaClockLevelZeroFiniteness.ae_areaClockReachesLevelZeroIndices_of_environmentWalkData` and
`hexactclock` by `ae_exactAreaClockReachesLevelZeroIndices_of_environmentWalkData`.  `hreg` —
the regular spatial extension — is untouched and open. -/
theorem ae_hlift_of_regularSpatialExtension (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν) (Φ : CellField)
    (hreg : ∀ n : ℕ, ∀ᵐ e ∂ν, ∀ hn : (e.val.1 n).isSome,
      ∀ hnt : Nontrivial (Vertex e.val),
        letI := hnt
        ∀ (D : (decode e).graph.Exhaustion)
          (hG : (decode e).graph.toSimpleGraph.Connected),
          EnvironmentWalkData e D hG →
          ∀ Xexp : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e),
            (∀ᵐ ω ∂(areaSampleLaw (decode e) D hG ⟨n, hn⟩),
              (∀ t, collapse (Xexp t ω) = exponentialAreaPath (decode e) D t ω) ∧
              IsEndLabeling (decode e) (fun t => Xexp t ω) ∧
              AvoidsSpatialInfinity (decode e) (fun t => Xexp t ω)) →
            ∃ M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane,
              ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG ⟨n, hn⟩),
                RegularSpatialExtension (decode e) (Φ.at e)
                  (fun t => Xexp t ω) (fun t => M t ω)) :
    ∀ n : ℕ, ∀ᵐ e ∂ν, ∀ hn : (e.val.1 n).isSome,
      ∀ hnt : Nontrivial (Vertex e.val),
        letI := hnt
        ∀ (D : (decode e).graph.Exhaustion)
          (hG : (decode e).graph.toSimpleGraph.Connected),
          EnvironmentWalkData e D hG →
          ∃ (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
            (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane),
            PathwiseClockClauses e D hG Φ ⟨n, hn⟩ Xexp Xexact M :=
  PathwiseClockClauseResidual.ae_hlift_of_clock_residuals ν hmt hFE Φ
    (AreaClockLevelZeroFiniteness.ae_areaClockReachesLevelZeroIndices_of_environmentWalkData ν)
    (ae_exactAreaClockReachesLevelZeroIndices_of_environmentWalkData ν) hreg

end Lift

/-! ## The invariance reduction with both clock residuals removed -/

section Assembly

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients
open HarmonicMainStatement StatementIngredients AreaClocks SpatialEnds
open ReflectedWalk
open InvarianceMainStatement QuenchedFormulation
open ReflectedGMS.InvarianceAssembly ReflectedGMS.EnvironmentWalkDataProducer

/-- **Reduction of `ReflectedInvarianceConclusions` to named inputs, with `hclock` and
`hexactclock` both discharged and `hlift` replaced by `hreg`.**

This is `AreaClockLevelZeroFiniteness.reflectedInvarianceConclusions_of_named_inputs_no_clock`
with its `hlift` argument supplied by `ae_hlift_of_regularSpatialExtension`.  The remaining named
open inputs are `hΦ`, `hdata`, `hreg`, `hbracket`, `hlimit`; `hmt` and `hFE` are the main
theorem's own environment hypotheses.  It is an implication, not a proof of the reflected
invariance principle. -/
theorem reflectedInvarianceConclusions_of_named_inputs_no_clock_residuals
    (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (Φ : CellField) (hΦ : IsHarmonicCoordinate ν Φ)
    (hdata : ∀ᵐ e ∂ν, ∃ hnt : Nontrivial (Vertex e.val),
      letI := hnt
      ∃ (D : (decode e).graph.Exhaustion)
        (hG : (decode e).graph.toSimpleGraph.Connected), EnvironmentWalkData e D hG)
    (hreg : ∀ n : ℕ, ∀ᵐ e ∂ν, ∀ hn : (e.val.1 n).isSome,
      ∀ hnt : Nontrivial (Vertex e.val),
        letI := hnt
        ∀ (D : (decode e).graph.Exhaustion)
          (hG : (decode e).graph.toSimpleGraph.Connected),
          EnvironmentWalkData e D hG →
          ∀ Xexp : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e),
            (∀ᵐ ω ∂(areaSampleLaw (decode e) D hG ⟨n, hn⟩),
              (∀ t, collapse (Xexp t ω) = exponentialAreaPath (decode e) D t ω) ∧
              IsEndLabeling (decode e) (fun t => Xexp t ω) ∧
              AvoidsSpatialInfinity (decode e) (fun t => Xexp t ω)) →
            ∃ M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane,
              ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG ⟨n, hn⟩),
                RegularSpatialExtension (decode e) (Φ.at e)
                  (fun t => Xexp t ω) (fun t => M t ω))
    (hbracket : ∀ n : ℕ, ∀ᵐ e ∂ν, ∀ hn : (e.val.1 n).isSome,
      ∀ hnt : Nontrivial (Vertex e.val),
        letI := hnt
        ∀ (D : (decode e).graph.Exhaustion)
          (hG : (decode e).graph.toSimpleGraph.Connected),
          EnvironmentWalkData e D hG →
          ∀ (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
            (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane),
            PathwiseClockClauses e D hG Φ ⟨n, hn⟩ Xexp Xexact M →
            CanonicalBracket e D Φ (areaSampleLaw (decode e) D hG ⟨n, hn⟩) M)
    (hlimit : ∀ n : ℕ, ∀ᵐ e ∂ν, ∀ hn : (e.val.1 n).isSome,
      ∀ hnt : Nontrivial (Vertex e.val),
        letI := hnt
        ∀ (D : (decode e).graph.Exhaustion)
          (hG : (decode e).graph.toSimpleGraph.Connected),
          EnvironmentWalkData e D hG →
          ∀ (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
            (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane),
            PathwiseClockClauses e D hG Φ ⟨n, hn⟩ Xexp Xexact M →
            ∀ target : AnisotropicBrownianTarget,
              target.covariance = meanCovariance ν Φ →
              ∀ z : CellField, IsCellRepresentative z →
                RepresentativePathConclusions e z
                  (areaSampleLaw (decode e) D hG ⟨n, hn⟩) target Xexp Xexact) :
    ReflectedInvarianceConclusions ν :=
  AreaClockLevelZeroFiniteness.reflectedInvarianceConclusions_of_named_inputs_no_clock
    ν hmt hFE Φ hΦ hdata (ae_hlift_of_regularSpatialExtension ν hmt hFE Φ hreg) hbracket hlimit

end Assembly

end ReflectedGMS.ExactAreaClockCollapse
