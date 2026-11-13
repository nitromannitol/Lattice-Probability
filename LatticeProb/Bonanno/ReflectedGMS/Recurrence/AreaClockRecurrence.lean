/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Recurrence.AreaClockRecurrence at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Recurrence.EnvironmentWalkDataProducer

/-!
# Recurrence of the reflected area clock at **every** vertex

`InvarianceMainStatement.FixedStartConclusions` asks for
`AreaClocks.ReturnsToEveryVertex`, i.e.

  `∀ᵐ ω, ∀ v : V, ∀ T : ℝ≥0, ∃ t, T ≤ t ∧ X t ω = some v`,

for both area clocks.  The sibling project proves property (v) of Theorem 1.6,
`ReflectedWalk.Theorem16.Recurrent z (sampleLaw E hG z) (process E w)`, which is
the *same* predicate but only at the **starting** vertex `z`
(`ReflectedWalk.Existence.recurrent`).  The reason its proof is confined to `z`
is that its deterministic core `ReflectedWalk.Existence.exists_ge_X_eq` consumes
recurrence of the **level-`0`** embedded chain `Y⁰`, and the level-`0` chain of
the coupling based at `n_z` is the walk reflected off `∂VG_{n_z}`: Remark 3.1
(`Exhaustion.chainLaw_ae_exists_gt_eq`) gives it recurrence only at vertices of
`VG_{n_z}`.  A vertex far away is reached infinitely often by a **higher** level
chain, not by the level-`0` one.

This file removes exactly that restriction.

* `exists_gt_Yxi_eq_level` generalises `IndexSet.Consistent.exists_gt_Yxi_eq`
  from level `0` to an arbitrary level `i`: if `Yⁱ` visits `z` at arbitrarily
  large indices then `Ξ` contains arbitrarily large `ξ` with `Y_ξ = z`.  The
  level-`0` proof compares `ξ` with `[(0, k'+1)]` directly; at level `i` the
  comparison goes through the excursion bracket
  `IndexSet.J_addr_apply_zero_le`, which says that the level-`0` coordinate `c`
  of `[(i,k')]` satisfies `J^{0,i}(c) ≤ k' < J^{0,i}(c+1)`; since `J^{0,i}` is
  strictly monotone, choosing `k' > J^{0,i}(ξ₀+1)` forces `ξ₀ < c`, and then
  `ξ < [(0, ξ₀+1)] ≤ [(0, c)] ≤ [(i,k')]`.
* `exists_ge_X_eq_level` is the resulting level-`i` form of the deterministic
  core, with the same clock hypotheses (3.16) as the level-`0` one.
* `ae_forall_exists_ge_process_eq` is the almost-sure statement for **every**
  vertex, obtained by running the above at the level `n_v` that is guaranteed to
  contain `v`, and interchanging `∀ v` with `∀ᵐ` by countability of the vertex
  set.
* `returnsToEveryVertex_exponentialAreaPath` specialises it to the area clock,
  whose clock hypothesis is the project's own residual
  `EnvironmentWalkDataProducer.AreaClockReachesLevelZeroIndices` — the *same*
  single residual that already reduces the `hdata` input of the invariance
  assembly.
* `returnsToEveryVertex_of_isHomeomorphicTimeChange` transports
  `ReturnsToEveryVertex` along a pathwise homeomorphic time change, which is how
  the exact-holding clock inherits the property from the exponential one: that
  time change is a clause of `InvarianceAssembly.PathwiseClockClauses`, i.e. of
  the `hlift` input, so no new hypothesis is introduced.

No result here weakens the manuscript statement: `ReturnsToEveryVertex` is
proved in the exact form `FixedStartConclusions` consumes.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ReflectedGMS.AreaClockRecurrence

open Code EnvironmentFields StatementIngredients AreaClocks
open ReflectedWalk ReflectedWalk.IndexSet QuenchedFormulation
open ReflectedGMS.EnvironmentWalkDataProducer

/-! ## The deterministic core at an arbitrary level -/

section Deterministic

universe u

variable {V : Type u}

/-- **Property (v) at the discrete level, from an arbitrary level `i`.**  This is
`IndexSet.Consistent.exists_gt_Yxi_eq` with the level-`0` chain replaced by the
level-`i` chain: if `Yⁱ` visits `z` at arbitrarily large indices, then `Ξ`
contains arbitrarily large `ξ` with `Y_ξ = z`.

The level-`0` statement compares `ξ` with the level-`0` address `[(0, k')]`
supplied by recurrence.  Here the witness `[(i, k')]` is a level-`i` address, so
the comparison is routed through its level-`0` coordinate
`c = [(i,k')]₀`, for which `IndexSet.J_addr_apply_zero_le` gives
`J^{0,i}(c) ≤ k' < J^{0,i}(c+1)`.  Choosing `k'` beyond `J^{0,i}(ξ₀ + 1)` and
using strict monotonicity of `J^{0,i}` forces `ξ₀ + 1 ≤ c`, whence
`ξ < [(0, ξ₀+1)] ≤ [(0, c)] ≤ [(i, k')]`. -/
theorem exists_gt_Yxi_eq_level (Gs : ℕ → Set V) (Y : ℕ → ℕ → V)
    (h : Consistent Gs Y) {z : V} (i : ℕ)
    (hrec : ∀ k, ∃ k', k < k' ∧ Y i k' = z) (ξ : Xi Gs Y) :
    ∃ η : Xi Gs Y, ξ < η ∧ Yxi Gs Y (ofLex η.1) = z := by
  obtain ⟨k', hk', hz⟩ := hrec (J Gs Y 0 i (ofLex ξ.1 0 + 1))
  refine ⟨⟨toLex (addr Gs Y i k'), realized_addr Gs Y i k'⟩, ?_, ?_⟩
  · show ξ.1 < toLex (addr Gs Y i k')
    have hbracket : k' < J Gs Y 0 i (addr Gs Y i k' 0 + 1) :=
      (J_addr_apply_zero_le Gs Y i k').2
    have hlt : J Gs Y 0 i (ofLex ξ.1 0 + 1) < J Gs Y 0 i (addr Gs Y i k' 0 + 1) :=
      lt_trans hk' hbracket
    have hc : ofLex ξ.1 0 + 1 ≤ addr Gs Y i k' 0 := by
      have := (J_strictMono Gs Y 0 i).lt_iff_lt.mp hlt
      omega
    calc ξ.1 < toLex (addr Gs Y 0 (ofLex ξ.1 0 + 1)) := lt_addr_zero_succ Gs Y ξ.2
      _ ≤ toLex (addr Gs Y 0 (addr Gs Y i k' 0)) := (addr_le_addr_iff Gs Y).mpr hc
      _ ≤ toLex (addr Gs Y i k') := addr_zero_le Gs Y (realized_addr Gs Y i k')
  · show Yxi Gs Y (addr Gs Y i k') = z
    rw [h.Yxi_addr]
    exact hz

/-- **Property (v), deterministic core, from an arbitrary level** (p. 25).  This
is `ReflectedWalk.Existence.exists_ge_X_eq` with its level-`0` recurrence
hypothesis replaced by recurrence of the level-`i` chain; the clock hypotheses
are unchanged. -/
theorem exists_ge_X_eq_level (Gs : ℕ → Set V) (Y : ℕ → ℕ → V) (w : V → ℝ)
    (E : (ℕ →₀ ℕ) → ℝ) (h : Consistent Gs Y) (hG : Monotone Gs)
    (hcov : ∀ x, ∃ n, x ∈ Gs n) (hsum : HoldingTimesSummable Gs Y w E)
    (hE : ∀ a, 0 < E a) (hw : ∀ x, 0 < w x) {z : V} (i : ℕ)
    (hrec : ∀ k, ∃ k', k < k' ∧ Y i k' = z) (T : ℝ≥0) :
    ∃ t : ℝ≥0, T ≤ t ∧ X Gs Y w E t = some z := by
  obtain ⟨K, hK⟩ := PathProperties.exists_lt_tau_addr_zero Gs Y w E hsum.1
    (ENNReal.coe_ne_top (r := T))
  obtain ⟨η, hη, hz⟩ := exists_gt_Yxi_eq_level Gs Y h i hrec
    ⟨toLex (addr Gs Y 0 K), realized_addr Gs Y 0 K⟩
  have hreal : Realized Gs Y (ofLex η.1) := η.2
  have hτ : tau Gs Y w E (addr Gs Y 0 K) ≤ tau Gs Y w E (ofLex η.1) :=
    tau_mono Gs Y w E (le_of_lt hη)
  have hne : tau Gs Y w E (ofLex η.1) ≠ ⊤ := (hsum.2 _ hreal).ne
  refine ⟨(tau Gs Y w E (ofLex η.1)).toNNReal, ?_, ?_⟩
  · rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hne]
    exact le_trans hK.le hτ
  · rw [h.X_eq_of_inInterval Gs Y w E hG hcov ⟨hreal, ?_, ?_⟩, hz]
    · rw [ENNReal.coe_toNNReal hne]
    · rw [ENNReal.coe_toNNReal hne, PathProperties.tau_succ Gs Y w E h hG hcov hreal]
      exact ENNReal.lt_add_right hne (Existence.holding_pos Gs Y w E hw (hE _)).ne'

end Deterministic

/-! ## The almost-sure statement for every vertex -/

section Probabilistic

universe u

variable {V : Type u} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
  [Nontrivial V] {G : ConductanceGraph V}

/-- **The constructed reflected walk returns to every vertex at arbitrarily large
times.**  This is `ReflectedWalk.Existence.recurrent` (property (v)) with the
starting vertex `z` replaced by an arbitrary vertex `v`, and with the
quantifier `∀ v` inside the almost-sure quantifier.

The clock hypothesis `hsum` is verbatim the one carried by
`ReflectedWalk.Existence.recurrent`, so nothing is assumed beyond what the
sibling project already assumes for recurrence at the starting vertex. -/
theorem ae_forall_exists_ge_process_eq (D : G.Exhaustion)
    (hG : G.toSimpleGraph.Connected) (w : V → ℝ) (hw : ∀ x, 0 < w x) (z : V)
    (hsum : ∀ᵐ ω ∂Existence.sampleLaw D hG z,
      HoldingTimesSummable (D.levelSets (D.nz z)) ω.1 w ω.2) :
    ∀ᵐ ω ∂Existence.sampleLaw D hG z, ∀ v : V, ∀ T : ℝ≥0,
      ∃ t : ℝ≥0, T ≤ t ∧ Existence.process D w t ω = some v := by
  have hrec : ∀ v : V, ∀ᵐ ω ∂Existence.sampleLaw D hG z,
      ∀ k, ∃ k', k < k' ∧ ω.1 (D.nz v) k' = v := by
    intro v
    refine Existence.sampleLaw_ae_level (z := z)
      (q := fun p : ℕ → V => ∀ k, ∃ k', k < k' ∧ p k' = v) D hG (D.nz v) ?_
    exact D.chainLaw_ae_exists_gt_eq hG (D.nz z + D.nz v)
      (D.mono (Nat.le_add_left (D.nz v) (D.nz z)) (D.mem_Gsub_nz v)) z
  filter_upwards [Existence.sampleLaw_ae_consistent D hG z,
    Existence.sampleLaw_ae_start D hG z, Existence.sampleLaw_ae_pos D hG z, hsum,
    ae_all_iff.2 hrec] with ω hc h0 hpos hs hrecω
  intro v T
  obtain ⟨t, hTt, hXt⟩ := exists_ge_X_eq_level (D.levelSets (D.nz z)) ω.1 w ω.2 hc
    (D.levelSets_mono (D.nz z)) (D.exists_mem_levelSets (D.nz z)) hs hpos hw
    (D.nz v) (hrecω v) T
  refine ⟨t, hTt, ?_⟩
  rw [Existence.process_eq D w (h0 0) hc t]
  exact hXt

/-- The same statement in the shape `AreaClocks.ReturnsToEveryVertex` consumes. -/
theorem returnsToEveryVertex_process (D : G.Exhaustion)
    (hG : G.toSimpleGraph.Connected) (w : V → ℝ) (hw : ∀ x, 0 < w x) (z : V)
    (hsum : ∀ᵐ ω ∂Existence.sampleLaw D hG z,
      HoldingTimesSummable (D.levelSets (D.nz z)) ω.1 w ω.2) :
    ReturnsToEveryVertex (Existence.sampleLaw D hG z) (Existence.process D w) :=
  ae_forall_exists_ge_process_eq D hG w hw z hsum

end Probabilistic

/-! ## Transport along a pathwise homeomorphic time change -/

section TimeChange

universe u v

variable {V : Type u} {Ω : Type v} [MeasurableSpace Ω]

/-- **`ReturnsToEveryVertex` is invariant under a pathwise homeomorphic time
change.**  If `X t ω = Y (h t) ω` for a strictly monotone homeomorphism `h` of
`ℝ≥0`, then `X` visits every vertex at arbitrarily large times as soon as `Y`
does: given `T`, a visit of `Y` at some `s ≥ h T` is a visit of `X` at
`h⁻¹ s ≥ T`. -/
theorem returnsToEveryVertex_of_isHomeomorphicTimeChange (P : Measure Ω)
    (X Y : ℝ≥0 → Ω → Option V) (hY : ReturnsToEveryVertex P Y)
    (hTC : ∀ᵐ ω ∂P, IsHomeomorphicTimeChange (fun t => X t ω) (fun t => Y t ω)) :
    ReturnsToEveryVertex P X := by
  filter_upwards [hY, hTC] with ω hYω hTCω
  obtain ⟨c, hmono, _, heq⟩ := hTCω
  intro v T
  obtain ⟨s, hs, hYs⟩ := hYω v (c T)
  refine ⟨c.symm s, ?_, ?_⟩
  · by_contra hcon
    rw [not_le] at hcon
    have hlt : c (c.symm s) < c T := hmono hcon
    rw [c.apply_symm_apply] at hlt
    exact absurd hs (not_le.mpr hlt)
  · have hstep : X (c.symm s) ω = Y (c (c.symm s)) ω := heq (c.symm s)
    rw [hstep, c.apply_symm_apply]
    exact hYs

end TimeChange

/-! ## The area clocks -/

section AreaClock

variable (e : Env) [Nontrivial (Vertex e.val)]

/-- **The exponential area clock returns to every vertex.**  The only hypothesis
is the project's own residual clause
`EnvironmentWalkDataProducer.AreaClockReachesLevelZeroIndices`, which is already
the single open input reducing `hdata`; positivity of the area rate and the
divergence half of (3.16) are unconditional. -/
theorem returnsToEveryVertex_exponentialAreaPath
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected)
    (h3 : AreaClockReachesLevelZeroIndices e D hG) (start : Vertex e.val) :
    ReturnsToEveryVertex (areaSampleLaw (decode e) D hG start)
      (exponentialAreaPath (decode e) D) :=
  returnsToEveryVertex_process D hG (areaRate (decode e)) (areaRate_pos e) start
    (areaClock_holdingTimesSummable e D hG h3 start)

/-- **The exact-holding area clock returns to every vertex**, given the pathwise
homeomorphic time change onto the exponential clock.  That time change is a
clause of `InvarianceAssembly.PathwiseClockClauses`, i.e. of the `hlift` input
of the invariance assembly, so the exact clock costs no hypothesis of its own
beyond the exponential one. -/
theorem returnsToEveryVertex_exactAreaPath
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected)
    (h3 : AreaClockReachesLevelZeroIndices e D hG) (start : Vertex e.val)
    (hTC : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      IsHomeomorphicTimeChange (fun t => exactAreaPath (decode e) D t ω)
        (fun t => exponentialAreaPath (decode e) D t ω)) :
    ReturnsToEveryVertex (areaSampleLaw (decode e) D hG start)
      (exactAreaPath (decode e) D) :=
  returnsToEveryVertex_of_isHomeomorphicTimeChange _ _ _
    (returnsToEveryVertex_exponentialAreaPath e D hG h3 start) hTC

/-- **Both recurrence clauses of `FixedStartConclusions` at once.** -/
theorem returnsToEveryVertex_both
    (D : (decode e).graph.Exhaustion)
    (hG : (decode e).graph.toSimpleGraph.Connected)
    (h3 : AreaClockReachesLevelZeroIndices e D hG) (start : Vertex e.val)
    (hTC : ∀ᵐ ω ∂(areaSampleLaw (decode e) D hG start),
      IsHomeomorphicTimeChange (fun t => exactAreaPath (decode e) D t ω)
        (fun t => exponentialAreaPath (decode e) D t ω)) :
    ReturnsToEveryVertex (areaSampleLaw (decode e) D hG start)
        (exponentialAreaPath (decode e) D) ∧
      ReturnsToEveryVertex (areaSampleLaw (decode e) D hG start)
        (exactAreaPath (decode e) D) :=
  ⟨returnsToEveryVertex_exponentialAreaPath e D hG h3 start,
    returnsToEveryVertex_exactAreaPath e D hG h3 start hTC⟩

end AreaClock

end ReflectedGMS.AreaClockRecurrence
