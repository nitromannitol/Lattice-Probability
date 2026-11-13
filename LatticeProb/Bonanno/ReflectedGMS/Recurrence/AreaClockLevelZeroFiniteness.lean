/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Recurrence.AreaClockLevelZeroFiniteness at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Recurrence.EnvironmentWalkDataProducer
import LatticeProb.Bonanno.ReflectedGMS.InvarianceAssemblyNoReturn

/-!
# The area clock reaches every level-`0` index, from recurrence of the path

`EnvironmentWalkDataProducer.AreaClockReachesLevelZeroIndices e D hG` is the
finiteness half of the manuscript's (3.16) for `w = areaRate`:

  `∀ z, ∀ᵐ ω, ∀ K, τ_{[(0,K)]} < ∞`.

It is the residual input of *two* named hypotheses of the invariance assembly —
the `hdata` input, through
`EnvironmentWalkDataProducer.environmentWalkData_of_areaClockReachesLevelZeroIndices`,
and the `hclock` input of
`InvarianceAssemblyNoReturn.reflectedInvarianceConclusions_of_named_inputs_no_return`.
This file proves the **converse implication**, unconditionally, and with it
discharges `hclock` outright.

## The deterministic core

`tau_addr_zero_lt_top_of_recurrent` is the statement that a sample path which
visits the *starting* vertex `z` at arbitrarily large times cannot have an
infinite level-`0` clock.  Nothing probabilistic enters.

Suppose `τ_{[(0,K)]} = ∞` for some `K`, and let `m + 1` be the least such index
(`m + 1 ≥ 1` because `τ_{[(0,0)]} = τ_{ξ₀} = 0`).  Let

  `S := τ_{[(0,m)]} + T_{[(0,m)]} < ∞`.

Every time `t` at which the path sits at `z` lies in a holding interval
`[τ_η, τ_η̂)` with `Y_η = z`.  Since `z ∈ VG_{n_z} = Gs 0`, (3.14)
(`IndexSet.Consistent.exists_addr_eq_of_mem`) forces `η` to be a **level-`0`**
address `[(0,j)]` — this is the crux: the excursions strictly between two
consecutive level-`0` indices happen outside `VG_{n_z}`, so they never sit at
`z`.  From `τ_{[(0,j)]} ≤ t < ∞` and minimality of `m + 1` we get `j ≤ m`, and
`τ_η̂ = τ_η + T_η` (`PathProperties.tau_succ`) together with
`τ_{succ [(0,j)]} ≤ τ_{[(0,j+1)]}` gives `t < S` for every such `t`.  So the
path is at `z` only before the finite time `S`, contradicting recurrence.

## Consequences

* `ae_tau_addr_zero_lt_top_of_recurrent` — the almost-sure form for the
  canonical construction and an arbitrary rate `w`, obtained from property (v)
  of Theorem 1.6 (`Theorem16.Recurrent`) for the constructed process.
* `areaClockReachesLevelZeroIndices_of_environmentWalkData` — the area clock
  reaches every level-`0` index **as soon as the canonical construction is a
  reflected walk for it**.  Combined with
  `environmentWalkData_of_areaClockReachesLevelZeroIndices` this gives the
  equivalence `areaClockReachesLevelZeroIndices_iff_environmentWalkData`.
* `ae_areaClockReachesLevelZeroIndices_of_environmentWalkData` is literally the
  `hclock` input of `reflectedInvarianceConclusions_of_named_inputs_no_return`,
  proved for **every** environment measure `ν`, and
  `reflectedInvarianceConclusions_of_named_inputs_no_clock` is that reduction
  with `hclock` removed from the list of named open inputs.

## What is *not* proved

The clock clause itself remains open, and this file does not weaken it: what is
established is that it is *equivalent* to the `hdata` clause for the same
environment and exhaustion, not that either holds.  The single genuine residual
is therefore unchanged and is `EnvironmentWalkDataProducer.EnvironmentAreaClockAdmissible`
(`environmentAreaClockAdmissible_iff_exists_environmentWalkData` below restates
it in walk-data form).  In particular nothing here supplies `hdata`; the only
open input that disappears is `hclock`, which is now seen to have carried no
content beyond `hdata`.
-/

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

namespace ReflectedGMS.AreaClockLevelZeroFiniteness

open Code EnvironmentFields EnvironmentLaws HarmonicLawIngredients
open HarmonicMainStatement StatementIngredients AreaClocks SpatialEnds
open ReflectedWalk ReflectedWalk.IndexSet
open InvarianceMainStatement QuenchedFormulation
open ReflectedGMS.InvarianceAssembly ReflectedGMS.EnvironmentWalkDataProducer
open ReflectedGMS.InvarianceAssemblyNoReturn

/-! ## The deterministic core -/

section Deterministic

universe u

variable {V : Type u}

/-- **A path that returns to its starting vertex forever has a finite level-`0`
clock.**  If the sample `(Y, E)` is consistent and the continuous-time path
`X` of (3.26) equals `z ∈ Gs 0` at arbitrarily large times, then every level-`0`
index is reached in finite time.

This is the exact converse of `ReflectedWalk.Existence.exists_ge_X_eq`, which
derives recurrence *from* (3.16); no positivity of `w` or `E` is needed here. -/
theorem tau_addr_zero_lt_top_of_recurrent (Gs : ℕ → Set V) (Y : ℕ → ℕ → V)
    (w : V → ℝ) (Eh : (ℕ →₀ ℕ) → ℝ) (h : Consistent Gs Y) (hGm : Monotone Gs)
    (hcov : ∀ x, ∃ n, x ∈ Gs n) {z : V} (hz : z ∈ Gs 0)
    (hrec : ∀ T : ℝ≥0, ∃ t : ℝ≥0, T ≤ t ∧ X Gs Y w Eh t = some z) (K : ℕ) :
    tau Gs Y w Eh (addr Gs Y 0 K) < ⊤ := by
  classical
  by_contra hcon
  have hex : ∃ j, tau Gs Y w Eh (addr Gs Y 0 j) = ⊤ :=
    ⟨K, top_le_iff.mp (not_lt.mp hcon)⟩
  have hfind : tau Gs Y w Eh (addr Gs Y 0 (Nat.find hex)) = ⊤ := Nat.find_spec hex
  have hmin : ∀ j, j < Nat.find hex → tau Gs Y w Eh (addr Gs Y 0 j) ≠ ⊤ :=
    fun j hj => Nat.find_min hex hj
  have hne0 : Nat.find hex ≠ 0 := by
    intro h0
    rw [h0, addr_zero_eq_zero, PathProperties.tau_zero] at hfind
    exact ENNReal.zero_ne_top hfind
  obtain ⟨m, hm⟩ : ∃ m, Nat.find hex = m + 1 := ⟨Nat.find hex - 1, by omega⟩
  rw [hm] at hfind hmin
  have hmfin : tau Gs Y w Eh (addr Gs Y 0 m) ≠ ⊤ := hmin m (Nat.lt_succ_self m)
  have hSne : tau Gs Y w Eh (addr Gs Y 0 m) + holding Gs Y w Eh (addr Gs Y 0 m) ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hmfin, holding_ne_top Gs Y w Eh _⟩
  -- every time at which the path sits at `z` precedes the finite time `S`
  have key : ∀ t : ℝ≥0, X Gs Y w Eh t = some z →
      (t : ℝ≥0∞) < tau Gs Y w Eh (addr Gs Y 0 m) + holding Gs Y w Eh (addr Gs Y 0 m) := by
    intro t ht
    obtain ⟨η, hη⟩ : ∃ η, InInterval Gs Y w Eh η t := by
      by_contra hc
      rw [(X_eq_none_iff Gs Y w Eh t).mpr hc] at ht
      exact absurd ht (by simp)
    have hYz : Yxi Gs Y η = z := by
      have hXη := h.X_eq_of_inInterval Gs Y w Eh hGm hcov hη
      rw [ht] at hXη
      exact (Option.some_inj.mp hXη).symm
    obtain ⟨j, hj⟩ :=
      h.exists_addr_eq_of_mem Gs Y hGm hη.1 (n := 0) (by rw [hYz]; exact hz)
    subst hj
    have hjfin : tau Gs Y w Eh (addr Gs Y 0 j) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.coe_ne_top hη.2.1
    have hjle : j ≤ m := by
      by_contra hcon2
      have hle : tau Gs Y w Eh (addr Gs Y 0 (m + 1)) ≤ tau Gs Y w Eh (addr Gs Y 0 j) :=
        tau_mono Gs Y w Eh ((addr_le_addr_iff Gs Y).mpr (by omega))
      rw [hfind] at hle
      exact hjfin (top_le_iff.mp hle)
    have h1 : (t : ℝ≥0∞) <
        tau Gs Y w Eh (addr Gs Y 0 j) + holding Gs Y w Eh (addr Gs Y 0 j) := by
      have h2 := hη.2.2
      rwa [PathProperties.tau_succ Gs Y w Eh h hGm hcov (realized_addr Gs Y 0 j)] at h2
    refine lt_of_lt_of_le h1 ?_
    rcases eq_or_lt_of_le hjle with rfl | hjm
    · exact le_rfl
    · calc tau Gs Y w Eh (addr Gs Y 0 j) + holding Gs Y w Eh (addr Gs Y 0 j)
          = tau Gs Y w Eh (IndexSet.succ Gs Y (addr Gs Y 0 j)) :=
            (PathProperties.tau_succ Gs Y w Eh h hGm hcov (realized_addr Gs Y 0 j)).symm
        _ ≤ tau Gs Y w Eh (addr Gs Y 0 (j + 1)) :=
            h.tau_succ_le Gs Y w Eh hGm hcov (realized_addr Gs Y 0 j)
              (realized_addr Gs Y 0 (j + 1)) (addr_lt_addr_succ Gs Y 0 j)
        _ ≤ tau Gs Y w Eh (addr Gs Y 0 m) :=
            tau_mono Gs Y w Eh ((addr_le_addr_iff Gs Y).mpr hjm)
        _ ≤ _ := le_self_add
  obtain ⟨t, hTt, hXt⟩ := hrec
    (tau Gs Y w Eh (addr Gs Y 0 m) + holding Gs Y w Eh (addr Gs Y 0 m)).toNNReal
  have hlt := key t hXt
  rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hSne] at hTt
  exact absurd hlt (not_lt.mpr hTt)

end Deterministic

/-! ## The almost-sure form for the canonical construction -/

section Probabilistic

universe u

variable {V : Type u} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
  [Nontrivial V] {G : ConductanceGraph V}

/-- **Property (v) of Theorem 1.6 implies the finiteness half of (3.16).**  For the
canonical construction `Existence.process D w` under `P_z`, recurrence at the
starting vertex `z` forces every level-`0` index to be reached in finite time.

The hypothesis is exactly the seventh conjunct of `IsReflectedWalk` at `z`. -/
theorem ae_tau_addr_zero_lt_top_of_recurrent (D : G.Exhaustion)
    (hG : G.toSimpleGraph.Connected) (w : V → ℝ) (z : V)
    (hrec : Theorem16.Recurrent z (Existence.sampleLaw D hG z) (Existence.process D w)) :
    ∀ᵐ ω ∂Existence.sampleLaw D hG z, ∀ K : ℕ,
      tau (D.levelSets (D.nz z)) ω.1 w ω.2 (addr (D.levelSets (D.nz z)) ω.1 0 K) < ⊤ := by
  have hz : z ∈ D.levelSets (D.nz z) 0 := by
    rw [ConductanceGraph.Exhaustion.levelSets_apply, Nat.add_zero]
    exact Finset.mem_coe.mpr (D.mem_Gsub_nz z)
  filter_upwards [Existence.sampleLaw_ae_consistent D hG z,
    Existence.sampleLaw_ae_start D hG z, hrec] with ω hc h0 hr
  intro K
  refine tau_addr_zero_lt_top_of_recurrent _ _ _ _ hc (D.levelSets_mono _)
    (D.exists_mem_levelSets _) hz (fun T => ?_) K
  obtain ⟨t, hTt, hXt⟩ := hr T
  exact ⟨t, hTt, by rw [← Existence.process_eq D w (h0 0) hc t]; exact hXt⟩

end Probabilistic

/-! ## The area clock -/

section AreaClock

variable (e : Env) [Nontrivial (Vertex e.val)]

/-- **The residual clock clause holds as soon as the canonical construction is a
reflected walk for the area rate.**  Unconditional: the only input is the walk
data itself, whose area-clock conjunct contains property (v). -/
theorem areaClockReachesLevelZeroIndices_of_environmentWalkData
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected)
    (hdat : EnvironmentWalkData e D hG) :
    AreaClockReachesLevelZeroIndices e D hG := by
  obtain ⟨_, _, harea, _⟩ := hdat
  intro z
  exact ae_tau_addr_zero_lt_top_of_recurrent D hG (areaRate (decode e)) z
    (harea z).2.2.2.2.2.2.1

end AreaClock

/-! ## The `hclock` input of the invariance assembly, discharged -/

/-- **The `hclock` input of
`InvarianceAssemblyNoReturn.reflectedInvarianceConclusions_of_named_inputs_no_return`,
proved.**  The statement is copied verbatim from that theorem; it holds for every
measure `ν` on environments, with no hypothesis whatsoever. -/
theorem ae_areaClockReachesLevelZeroIndices_of_environmentWalkData (ν : Measure Env) :
    ∀ᵐ e ∂ν, ∀ hnt : Nontrivial (Vertex e.val),
      letI := hnt
      ∀ (D : (decode e).graph.Exhaustion)
        (hG : (decode e).graph.toSimpleGraph.Connected),
        EnvironmentWalkData e D hG → AreaClockReachesLevelZeroIndices e D hG := by
  refine Filter.Eventually.of_forall fun e hnt => ?_
  intro D hG hdat
  exact @areaClockReachesLevelZeroIndices_of_environmentWalkData e hnt D hG hdat

/-- **Reduction of `ReflectedInvarianceConclusions` to named inputs, with both the
recurrence input and the area-clock input removed.**

This is `InvarianceAssemblyNoReturn.reflectedInvarianceConclusions_of_named_inputs_no_return`
with `hclock` discharged by the theorem above.  The remaining named open inputs
are `hΦ`, `hdata`, `hlift`, `hbracket`, `hlimit`; `hmt` and `hFE` are the main
theorem's own environment hypotheses.

It is an implication, not a proof of the reflected invariance principle. -/
theorem reflectedInvarianceConclusions_of_named_inputs_no_clock
    (ν : Measure Env) [IsProbabilityMeasure ν]
    (hmt : MassTransport ν) (hFE : FiniteEnergyMoment ν)
    (Φ : CellField) (hΦ : IsHarmonicCoordinate ν Φ)
    (hdata : ∀ᵐ e ∂ν, ∃ hnt : Nontrivial (Vertex e.val),
      letI := hnt
      ∃ (D : (decode e).graph.Exhaustion)
        (hG : (decode e).graph.toSimpleGraph.Connected), EnvironmentWalkData e D hG)
    (hlift : ∀ n : ℕ, ∀ᵐ e ∂ν, ∀ hn : (e.val.1 n).isSome,
      ∀ hnt : Nontrivial (Vertex e.val),
        letI := hnt
        ∀ (D : (decode e).graph.Exhaustion)
          (hG : (decode e).graph.toSimpleGraph.Connected),
          EnvironmentWalkData e D hG →
          ∃ (Xexp Xexact : ℝ≥0 → Existence.Sample (Vertex e.val) → State (decode e))
            (M : ℝ≥0 → Existence.Sample (Vertex e.val) → Plane),
            PathwiseClockClauses e D hG Φ ⟨n, hn⟩ Xexp Xexact M)
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
  reflectedInvarianceConclusions_of_named_inputs_no_return ν hmt hFE Φ hΦ hdata
    (ae_areaClockReachesLevelZeroIndices_of_environmentWalkData ν) hlift hbracket hlimit

end ReflectedGMS.AreaClockLevelZeroFiniteness
