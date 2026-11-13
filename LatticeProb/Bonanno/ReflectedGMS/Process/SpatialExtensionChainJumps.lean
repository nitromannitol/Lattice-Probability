/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Process.SpatialExtensionChainJumps at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Process.SpatialExtensionCore
import LatticeProb.Bonanno.ReflectedGMS.Process.FastClockTimeChange

/-!
# Three of the four inputs of `SpatialExtensionConstruction.ae_hreg_of_inputs`, discharged

`SpatialExtensionConstruction.ae_hreg_of_inputs` produces the `hreg` input of
`PathwiseClockClauseLift.ae_hlift_of_atomic_inputs` (manuscript `p:prop:pathsextend`) from four
named inputs `hcut`, `htc`, `hnbj`, `hedge`.  This file proves `htc` and `hedge` outright and
proves the vertex half of `hnbj`, all from the coupled-chain construction (3.26) of the
reflected walk and the checked area-clock summability.

* **`htc`** — the area path is a homeomorphic time change of the summable fast path.  This is
  the proof of `FastClockTimeChange.ae_isHomeomorphicTimeChange_fast` with the admissible rate
  `w*` replaced by any rate `w ≥ w*`: Lemma 3.5 applies to every such `w`
  (`ae_isHomeomorphicTimeChange_of_rateFunction_le`).
* **`hedge`** — a sojourn at `v` followed immediately by `w ≠ v` is the holding interval of a
  class `η` of `Ξ` followed by its successor `η̂` (3.24), and `Y_η`, `Y_η̂` are consecutive
  states of the level-`m` chain with `Y_η ∈ VG_m`.  From inside `VG_m` the chain jumps with
  probability `c(x,y)/π(x)` (3.2), so almost surely only along edges (`edgeJumps_X`,
  `ae_edgeJumps_process`).
* **No entrance from the boundary** — a vertex time `t > 0` of the path is preceded by a sojourn
  at a vertex (`noBoundaryEntrance_X`, `ae_noBoundaryEntrance_process`).  If `t` starts the class
  `η` and `m` is a level containing `Y_η` and all its (finitely many) neighbours, the preceding
  level-`m` state `Y^m_{k}` jumped to `Y_η`.  From outside `VG_m` that jump has probability
  `hm^x_{VG_m}(Y_η) = 0`: the indicator of `Y_η` is its own energy-minimising extension because
  every edge at `Y_η` lies inside `VG_m` (`harmonicMeasure_eq_zero_of_neighbors_mem`).  So
  `Y^m_k ∈ VG_m`, the class of `(m,k)` is the immediate predecessor of `η`, and its holding
  interval ends at `t`.

What remains of `hnbj` is its part at nonvertex times:
`NoJumpsAtNonvertexTimes` — a càdlàg path equal to `Φ` at vertex times has no jump at a
nonvertex time.  That is the Beurling–Deny / Lévy-system content of manuscript
`p:prop:purejump` (no jumping measure charges a pair with a nonvertex endpoint).  It is stated
here for the summable fast clock, where the compact realization lives, and transported to the
area clock by the time change (`noJumpsAtNonvertexTimes_of_timeChange`).

## Remaining named inputs for `hreg` once these are wired into a producer (open, not certified)

The environment-level producer (`ae_hreg_of_cutoffs_and_continuity`) is not in this file; see
`outputs/opus-hreg-spatial-extension-handoff.md`.  This file is UNCHECKED as of 2026-09-16.

1. `hcut` — `p:lem:spatialcutoffs` for `Φ` (unchanged from `ae_hreg_of_inputs`).
2. `hcont` — `NoJumpsAtNonvertexTimes` for the summable fast path, i.e. the nonvertex-time part
   of `p:prop:purejump`.

Both are satisfiable for the actual reflected walk by the manuscript: (1) is
`p:lem:spatialcutoffs`; (2) holds because the unique càdlàg extension is continuous at
nonvertex times (`p:prop:pathsextend`, second paragraph), and is vacuous on samples with no
càdlàg vertex-agreeing path.  Neither restates `hreg`: (1) is a statement about `Φ` and the
graph, and (2) asserts no existence and says nothing at vertex times, about holding intervals,
edges, uniqueness or boundedness.
-/

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal

namespace ReflectedGMS.SpatialExtensionChainJumps

open AreaClocks ReflectedWalk ReflectedWalk.IndexSet
open ReflectedGMS.SpatialExtensionConstruction

universe u

/-! ## A Markov chain makes only steps of positive probability -/

section Chain

/-- A chain on a countable space almost surely never makes a step to which its kernel gives
zero mass.  The Markov property at a deterministic time (`MarkovChain.chainLaw_map_walkShift`)
reduces every index to the first step. -/
theorem chainLaw_ae_forall_stepKernel_ne_zero {S : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] (κ : Kernel S S) [IsMarkovKernel κ] (z : S) :
    ∀ᵐ ω ∂MarkovChain.chainLaw κ z, ∀ j : ℕ, κ (ω j) {ω (j + 1)} ≠ 0 := by
  have hA : MeasurableSet {ω : ℕ → S | κ (ω 0) {ω 1} = 0} := by
    have hB : MeasurableSet {p : S × S | κ p.1 {p.2} = 0} := (Set.to_countable _).measurableSet
    have hmap : Measurable fun ω : ℕ → S => (ω 0, ω 1) :=
      (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
    have hpre : MeasurableSet
        ((fun ω : ℕ → S => (ω 0, ω 1)) ⁻¹' {p : S × S | κ p.1 {p.2} = 0}) := hmap hB
    exact hpre
  have hbase : ∀ y : S, MarkovChain.chainLaw κ y {ω : ℕ → S | κ (ω 0) {ω 1} = 0} = 0 := by
    intro y
    have hC : MeasurableSet {u : S | κ y {u} = 0} := (Set.to_countable _).measurableSet
    have hCzero : κ y {u : S | κ y {u} = 0} = 0 := by
      rw [← Set.biUnion_of_singleton {u : S | κ y {u} = 0}]
      exact (measure_biUnion_null_iff (Set.to_countable _)).2 fun u hu => hu
    have hm : (MarkovChain.chainLaw κ y).map (fun ω => ω 1) {u : S | κ y {u} = 0} = 0 := by
      rw [MarkovChain.chainLaw_marginal_one]
      exact hCzero
    rw [Measure.map_apply (measurable_pi_apply 1) hC] at hm
    have hm' : MarkovChain.chainLaw κ y {ω : ℕ → S | κ y {ω 1} = 0} = 0 := hm
    have h1 : ∀ᵐ ω ∂MarkovChain.chainLaw κ y, κ y {ω 1} ≠ 0 := by
      rw [ae_iff]
      simpa using hm'
    have h0 : ∀ᵐ ω ∂MarkovChain.chainLaw κ y, ω 0 = y := MarkovChain.chainLaw_ae_start κ y
    have hne : ∀ᵐ ω ∂MarkovChain.chainLaw κ y, κ (ω 0) {ω 1} ≠ 0 := by
      filter_upwards [h0, h1] with ω hω0 hω1
      rw [hω0]
      exact hω1
    simpa using ae_iff.1 hne
  rw [ae_all_iff]
  intro j
  have hmapzero : ((MarkovChain.chainLaw κ z).map (MarkovChain.walkShift j))
      {ω : ℕ → S | κ (ω 0) {ω 1} = 0} = 0 := by
    rw [MarkovChain.chainLaw_map_walkShift, Measure.bind_apply hA (Kernel.aemeasurable _)]
    have hzero : ∀ y : S,
        MarkovChain.pathKernel κ y {ω : ℕ → S | κ (ω 0) {ω 1} = 0} = 0 := by
      intro y
      rw [MarkovChain.pathKernel_apply]
      exact hbase y
    simp only [hzero]
    exact lintegral_zero
  rw [Measure.map_apply (MarkovChain.measurable_walkShift j) hA] at hmapzero
  have hpre : MarkovChain.chainLaw κ z {ω : ℕ → S | κ (ω j) {ω (j + 1)} = 0} = 0 := hmapzero
  rw [ae_iff]
  simpa using hpre

end Chain

/-! ## The level chains jump along edges from inside, and not into an interior vertex from
outside -/

section Graph

variable {V : Type u}

/-- The indicator of `y` has no larger edge gradient than any function agreeing with it on a
finite set `A` containing `y` and all neighbours of `y`. -/
theorem gradSq_indic_le (G : ConductanceGraph V) {A : Finset V} {y : V} (hy : y ∈ A)
    (hnbr : ∀ u, 0 < G.c y u → u ∈ A) {g : V → ℝ} (hgA : Set.EqOn g (G.indic y) ↑A)
    (p : V × V) : G.gradSq (G.indic y) p ≤ G.gradSq g p := by
  obtain ⟨a, b⟩ := p
  show G.c a b * (G.indic y b - G.indic y a) ^ 2 ≤ G.c a b * (g b - g a) ^ 2
  by_cases hy' : a = y ∨ b = y
  · rcases (G.c_nonneg a b).lt_or_eq with hab | hab
    · have hmem : a ∈ A ∧ b ∈ A := by
        rcases hy' with rfl | rfl
        · exact ⟨hy, hnbr b hab⟩
        · exact ⟨hnbr a (by rw [G.c_symm]; exact hab), hy⟩
      exact le_of_eq (by rw [hgA (Finset.mem_coe.2 hmem.1), hgA (Finset.mem_coe.2 hmem.2)])
    · rw [← hab]
      simp
  · push_neg at hy'
    have h1 : G.indic y a = 0 := by simp [ConductanceGraph.indic, hy'.1]
    have h2 : G.indic y b = 0 := by simp [ConductanceGraph.indic, hy'.2]
    rw [h1, h2, sub_zero, zero_pow two_ne_zero, mul_zero]
    exact mul_nonneg (G.c_nonneg a b) (sq_nonneg _)

/-- **The harmonic measure from outside a finite set gives no mass to a vertex all of whose
edges stay inside the set.**  The indicator of `y` is then its own energy-minimising
extension (Proposition 1.3, uniqueness), and it vanishes off `A`. -/
theorem harmonicMeasure_eq_zero_of_neighbors_mem (G : ConductanceGraph V)
    (hG : G.toSimpleGraph.Connected) {A : Finset V} {x y : V} (hy : y ∈ A)
    (hnbr : ∀ u, 0 < G.c y u → u ∈ A) (hx : x ∉ A) :
    G.harmonicMeasure hG A x y = 0 := by
  have hA : A.Nonempty := ⟨y, hy⟩
  have hfin : G.HasFiniteEnergy (G.indic y) :=
    Summable.of_nonneg_of_le (fun p => G.gradSq_nonneg _ p)
      (fun p => gradSq_indic_le G hy hnbr (G.energyMin_eqOn hG hA (G.indic y)) p)
      (G.energyMin_hasFiniteEnergy hG hA (G.indic y))
  have hmin : ∀ g : V → ℝ, G.HasFiniteEnergy g → Set.EqOn g (G.indic y) ↑A →
      G.Energy (G.indic y) ≤ G.Energy g := by
    intro g hg hgA
    unfold ConductanceGraph.Energy
    exact div_le_div_of_nonneg_right (hfin.tsum_le_tsum (gradSq_indic_le G hy hnbr hgA) hg)
      (by norm_num)
  have heq : G.indic y = G.energyMin hG A (G.indic y) :=
    G.energyMin_unique hG hA (G.indic y) hfin (fun _ _ => rfl) hmin
  show G.energyMin hG A (G.indic y) x = 0
  rw [← heq]
  have hxy : x ≠ y := fun h => hx (h ▸ hy)
  simp [ConductanceGraph.indic, hxy]

variable [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V] [Nontrivial V]
  {G : ConductanceGraph V}

/-- A step of positive probability of the level-`n` chain from a vertex of `VG_n` follows an
edge (3.2). -/
theorem adj_of_stepKernel_ne_zero (D : G.Exhaustion) (hG : G.toSimpleGraph.Connected)
    {n : ℕ} {x y : V} (hx : x ∈ D.Gsub n) (h : D.stepKernel hG n x {y} ≠ 0) :
    G.toSimpleGraph.Adj x y := by
  rw [ConductanceGraph.Exhaustion.stepKernel_singleton] at h
  have h2 : D.transProb hG n x y = G.c x y / G.pi x := G.transProb_of_mem hG hx y
  rw [h2] at h
  have hpos : 0 < G.c x y / G.pi x := ENNReal.ofReal_pos.1 (pos_iff_ne_zero.2 h)
  rcases (G.c_nonneg x y).lt_or_eq with hc | hc
  · exact hc
  · rw [← hc, zero_div] at hpos
    exact absurd hpos (lt_irrefl 0)

/-- A step of positive probability of the level-`n` chain into a vertex of `VG_n` whose
neighbours all lie in `VG_n` starts inside `VG_n`: the harmonic-measure jump (3.3) from
outside gives it no mass. -/
theorem mem_of_stepKernel_ne_zero (D : G.Exhaustion) (hG : G.toSimpleGraph.Connected)
    {n : ℕ} {x y : V} (hy : y ∈ D.Gsub n)
    (hnbr : ∀ u, G.toSimpleGraph.Adj y u → u ∈ D.Gsub n)
    (h : D.stepKernel hG n x {y} ≠ 0) : x ∈ D.Gsub n := by
  by_contra hx
  apply h
  rw [ConductanceGraph.Exhaustion.stepKernel_singleton]
  have h2 : D.transProb hG n x y = G.harmonicMeasure hG (D.Gsub n) x y :=
    G.transProb_of_not_mem_of_mem hG hx hy
  rw [h2, harmonicMeasure_eq_zero_of_neighbors_mem G hG hy (fun u hu => hnbr u hu) hx,
    ENNReal.ofReal_zero]

/-- Almost surely under the canonical sample law, no level chain makes a step of zero
probability. -/
theorem sampleLaw_ae_forall_stepKernel_ne_zero (D : G.Exhaustion)
    (hG : G.toSimpleGraph.Connected) (z : V) :
    ∀ᵐ ω ∂Existence.sampleLaw D hG z, ∀ i j : ℕ,
      D.stepKernel hG (D.nz z + i) (ω.1 i j) {ω.1 i (j + 1)} ≠ 0 := by
  rw [ae_all_iff]
  intro i
  refine Existence.sampleLaw_ae_level (z := z)
    (q := fun p : ℕ → V => ∀ j : ℕ, D.stepKernel hG (D.nz z + i) (p j) {p (j + 1)} ≠ 0)
    D hG i ?_
  exact chainLaw_ae_forall_stepKernel_ne_zero (D.stepKernel hG (D.nz z + i)) z

end Graph

/-! ## Deterministic path statements for the construction (3.26) -/

section Deterministic

variable {V : Type u}

/-- A vertex time `t > 0` is preceded by a sojourn at a vertex: the path does not enter a
vertex directly from the nonvertex state. -/
def NoBoundaryEntrance (X : ℝ≥0 → Option V) : Prop :=
  ∀ t : ℝ≥0, 0 < t → ∀ x : V, X t = some x → LeftVertexConstant X t

/-- **The nonvertex-time part of manuscript `p:prop:purejump`, pathwise.**  A càdlàg
plane-valued path equal to `Φ` at every vertex time does not jump at a positive nonvertex
time.  It asserts no existence, and nothing at vertex times. -/
def NoJumpsAtNonvertexTimes (X : ℝ≥0 → Option V) (Φ : V → Plane) : Prop :=
  ∀ Z : ℝ≥0 → Plane, IsCadlag Z → (∀ t x, X t = some x → Z t = Φ x) →
    ∀ t : ℝ≥0, 0 < t → X t = none → Function.leftLim Z t = Z t

/-- `NoBoundaryJumps` splits into its vertex part, no entrance from the nonvertex state, and
its nonvertex part. -/
theorem noBoundaryJumps_of_noBoundaryEntrance {X : ℝ≥0 → Option V} {Φ : V → Plane}
    (hent : NoBoundaryEntrance X) (hcont : NoJumpsAtNonvertexTimes X Φ) :
    NoBoundaryJumps X Φ := by
  intro Z hZ hvert t ht hne
  cases hXt : X t with
  | none => exact absurd (hcont Z hZ hvert t ht hXt) hne
  | some x => exact hent t ht x hXt

/-- The nonvertex-time part transports along a homeomorphic time change. -/
theorem noJumpsAtNonvertexTimes_of_timeChange {X Y : ℝ≥0 → Option V} {Φ : V → Plane}
    (htc : IsHomeomorphicTimeChange X Y) (hY : NoJumpsAtNonvertexTimes Y Φ) :
    NoJumpsAtNonvertexTimes X Φ := by
  obtain ⟨h, hmono, -, hXY⟩ := htc
  have hsymm : StrictMono h.symm := fun a b hab =>
    hmono.lt_iff_lt.1 (by rw [h.apply_symm_apply, h.apply_symm_apply]; exact hab)
  intro Z hZ hvert t ht hXt
  have hWcad : IsCadlag (fun u => Z (h.symm u)) := isCadlag_comp_of_strictMono h.symm hsymm hZ
  have hWvert : ∀ u x, Y u = some x → Z (h.symm u) = Φ x := by
    intro u x hu
    exact hvert (h.symm u) x (by rw [hXY, h.apply_symm_apply]; exact hu)
  have htpos : 0 < h t := lt_of_le_of_lt zero_le (hmono ht)
  haveI : (𝓝[<] (h t)).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, htpos⟩
  have hlim : Function.leftLim (fun u => Z (h.symm u)) (h t) = Function.leftLim Z t := by
    refine leftLim_eq_of_tendsto ((hZ.tendsto_nhdsLT_leftLim t).comp ?_)
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_nhdsWithin_of_forall fun u hu => ?_⟩
    · have h1 : Tendsto h.symm (𝓝 (h t)) (𝓝 t) := by
        have h2 := h.symm.continuous.tendsto (h t)
        rwa [h.symm_apply_apply] at h2
      exact h1.mono_left nhdsWithin_le_nhds
    · exact (hsymm hu).trans_eq (h.symm_apply_apply t)
  have hYt : Y (h t) = none := by
    rw [← hXY t]
    exact hXt
  have key := hY _ hWcad hWvert (h t) htpos hYt
  exact hlim.symm.trans (key.trans (congrArg Z (h.symm_apply_apply t)))

/-- A finite set of vertices lies in one level of an increasing covering family. -/
theorem exists_levelSets_superset_of_finite {Gs : ℕ → Set V} (hmono : Monotone Gs)
    (hcov : ∀ x, ∃ n, x ∈ Gs n) {S : Set V} (hS : S.Finite) : ∃ N, S ⊆ Gs N := by
  choose f hf using hcov
  obtain ⟨N, hN⟩ := (hS.image f).bddAbove
  exact ⟨N, fun x hx => hmono (hN (Set.mem_image_of_mem f hx)) (hf x)⟩

/-- Consecutive classes `η`, `η̂` of `Ξ` carry adjacent vertices once every level chain jumps
along edges from inside its level set: `Y_η = Y^m_k ∈ VG_m` and `Y_η̂ = Y^m_{k+1}` (3.24). -/
theorem adj_Yxi_succ (G : ConductanceGraph V) {Gs : ℕ → Set V} {Y : ℕ → ℕ → V} {w : V → ℝ}
    (hcd : HoldingTimeChange.ChainData Gs Y w)
    (hstep : ∀ m j, Y m j ∈ Gs m → G.toSimpleGraph.Adj (Y m j) (Y m (j + 1)))
    (η : ℕ →₀ ℕ) : G.toSimpleGraph.Adj (Yxi Gs Y η) (Yxi Gs Y (succ Gs Y η)) := by
  have hx := exists_level_le_mem Gs Y hcd.monotone hcd.cover η
  have key : ∃ m, level η ≤ m ∧ Yxi Gs Y η ∈ Gs m ∧ succ Gs Y η = succAt Gs Y m η := by
    refine ⟨Classical.choose hx, (Classical.choose_spec hx).1, (Classical.choose_spec hx).2, ?_⟩
    unfold IndexSet.succ
    rw [dif_pos hx]
  obtain ⟨m, hlev, hmem, hsucc⟩ := key
  have h1 : Yxi Gs Y (succ Gs Y η) = Y m (tm Gs Y m η + 1) := by
    rw [hsucc]
    show Yxi Gs Y (addr Gs Y m (tm Gs Y m η + 1)) = Y m (tm Gs Y m η + 1)
    exact hcd.consistent.Yxi_addr Gs Y m (tm Gs Y m η + 1)
  have h2 : Yxi Gs Y η = Y m (tm Gs Y m η) := hcd.consistent.Yxi_eq Gs Y hlev
  rw [h1, h2]
  rw [h2] at hmem
  exact hstep m (tm Gs Y m η) hmem

/-- **Edge jumps for the construction (3.26).**  A sojourn at `v` ending at time `t` with
`X_t = u ≠ v` is the holding interval of a class `η` with `t = τ_η̂`, so `v = Y_η` and
`u = Y_η̂` are adjacent. -/
theorem edgeJumps_X (F : IndexedCells V) {Gs : ℕ → Set V} {Y : ℕ → ℕ → V} {w : V → ℝ}
    {E : (ℕ →₀ ℕ) → ℝ} (hcd : HoldingTimeChange.ChainData Gs Y w)
    (hd : HoldingTimeChange.ClockData Gs Y w E)
    (hstep : ∀ m j, Y m j ∈ Gs m → F.graph.toSimpleGraph.Adj (Y m j) (Y m (j + 1))) :
    EdgeJumps F (X Gs Y w E) := by
  intro t v u hleft hu hvu
  obtain ⟨s, hst, hconst⟩ := hleft
  have hsv : X Gs Y w E s = some v := hconst s ⟨le_rfl, hst⟩
  obtain ⟨η, hIη, hYη⟩ := Existence.exists_inInterval_of_X_eq_some Gs Y w E hsv
  obtain ⟨hηR, hη1, hη2⟩ := hIη
  have hsuccR : Realized Gs Y (succ Gs Y η) := hcd.realized_succ hηR
  have hsuccF : tau Gs Y w E (succ Gs Y η) ≠ ⊤ := hd.tau_ne_top hsuccR
  have hadj := adj_Yxi_succ F.graph hcd hstep η
  have hsucc2 : tau Gs Y w E (succ Gs Y η) < tau Gs Y w E (succ Gs Y (succ Gs Y η)) := by
    rw [hcd.tau_succ hsuccR]
    exact ENNReal.lt_add_right hsuccF
      (Existence.holding_pos Gs Y w E hcd.ratePos (a := succ Gs Y η) (hd.pos _)).ne'
  have hge : tau Gs Y w E (succ Gs Y η) ≤ ((t : ℝ≥0) : ℝ≥0∞) := by
    by_contra hcon
    have hInt : InInterval Gs Y w E η ((t : ℝ≥0) : ℝ≥0∞) :=
      ⟨hηR, hη1.trans (ENNReal.coe_le_coe.2 hst.le), not_le.1 hcon⟩
    rw [hcd.consistent.X_eq_of_inInterval Gs Y w E hcd.monotone hcd.cover hInt, hYη] at hu
    exact hvu (Option.some_injective V hu)
  have hle : ((t : ℝ≥0) : ℝ≥0∞) ≤ tau Gs Y w E (succ Gs Y η) := by
    by_contra hcon
    have hp : ((tau Gs Y w E (succ Gs Y η)).toNNReal : ℝ≥0∞) = tau Gs Y w E (succ Gs Y η) :=
      ENNReal.coe_toNNReal hsuccF
    have hps : s ≤ (tau Gs Y w E (succ Gs Y η)).toNNReal := by
      rw [← ENNReal.coe_le_coe, hp]
      exact hη2.le
    have hpt : (tau Gs Y w E (succ Gs Y η)).toNNReal < t := by
      rw [← ENNReal.coe_lt_coe, hp]
      exact not_le.1 hcon
    have hXp := hconst _ ⟨hps, hpt⟩
    have hInt : InInterval Gs Y w E (succ Gs Y η)
        (((tau Gs Y w E (succ Gs Y η)).toNNReal : ℝ≥0) : ℝ≥0∞) := by
      refine ⟨hsuccR, le_of_eq hp.symm, ?_⟩
      rw [hp]
      exact hsucc2
    rw [hcd.consistent.X_eq_of_inInterval Gs Y w E hcd.monotone hcd.cover hInt] at hXp
    have hveq : Yxi Gs Y (succ Gs Y η) = v := Option.some_injective V hXp
    rw [hveq, ← hYη] at hadj
    exact hadj.ne rfl
  have hInt : InInterval Gs Y w E (succ Gs Y η) ((t : ℝ≥0) : ℝ≥0∞) := by
    refine ⟨hsuccR, hge, ?_⟩
    rw [le_antisymm hle hge]
    exact hsucc2
  rw [hcd.consistent.X_eq_of_inInterval Gs Y w E hcd.monotone hcd.cover hInt] at hu
  have hueq : Yxi Gs Y (succ Gs Y η) = u := Option.some_injective V hu
  rw [← hYη, ← hueq]
  exact hadj

/-- **No entrance from the nonvertex state for the construction (3.26).**  A class `η` with
`τ_η > 0` has, at any level `N` containing `Y_η` and its neighbours, a positive level time
`k + 1`; the preceding state `Y^N_k` lies in `VG_N` by `hin`, so the class of `(N,k)` is the
immediate predecessor of `η` and its holding interval ends at `τ_η`. -/
theorem noBoundaryEntrance_X (G : ConductanceGraph V) {Gs : ℕ → Set V} {Y : ℕ → ℕ → V}
    {w : V → ℝ} {E : (ℕ →₀ ℕ) → ℝ} (hcd : HoldingTimeChange.ChainData Gs Y w)
    (hd : HoldingTimeChange.ClockData Gs Y w E)
    (hloc : ∀ x : V, ∃ N, ∀ u, G.toSimpleGraph.Adj x u → u ∈ Gs N)
    (hin : ∀ m j, Y m (j + 1) ∈ Gs m →
      (∀ u, G.toSimpleGraph.Adj (Y m (j + 1)) u → u ∈ Gs m) → Y m j ∈ Gs m) :
    NoBoundaryEntrance (X Gs Y w E) := by
  intro t ht x hx
  obtain ⟨η, hIη, hYη⟩ := Existence.exists_inInterval_of_X_eq_some Gs Y w E hx
  obtain ⟨hηR, hη1, hη2⟩ := hIη
  have hηF : tau Gs Y w E η ≠ ⊤ := hd.tau_ne_top hηR
  rcases hη1.lt_or_eq with hlt | heq
  · -- the sojourn at `x` started strictly before `t`
    refine ⟨x, (tau Gs Y w E η).toNNReal, ?_, fun r hr => ?_⟩
    · rw [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal hηF]
      exact hlt
    · have hInt : InInterval Gs Y w E η ((r : ℝ≥0) : ℝ≥0∞) := by
        refine ⟨hηR, ?_, lt_trans (ENNReal.coe_lt_coe.2 hr.2) hη2⟩
        rw [← ENNReal.coe_toNNReal hηF, ENNReal.coe_le_coe]
        exact hr.1
      rw [hcd.consistent.X_eq_of_inInterval Gs Y w E hcd.monotone hcd.cover hInt, hYη]
  · -- the sojourn at `x` starts at `t`: find the immediate predecessor of `η`
    obtain ⟨N₁, hN₁⟩ := hloc x
    obtain ⟨N₂, hN₂⟩ := hcd.cover x
    obtain ⟨N, hN₁N, hN₂N, hlevN⟩ : ∃ N, N₁ ≤ N ∧ N₂ ≤ N ∧ level η ≤ N :=
      ⟨max (level η) (max N₁ N₂), le_trans (le_max_left _ _) (le_max_right _ _),
        le_trans (le_max_right _ _) (le_max_right _ _), le_max_left _ _⟩
    have hxN : x ∈ Gs N := hcd.monotone hN₂N hN₂
    have hnbrN : ∀ u, G.toSimpleGraph.Adj x u → u ∈ Gs N :=
      fun u hu => hcd.monotone hN₁N (hN₁ u hu)
    have hrep : addr Gs Y N (tm Gs Y N η) = η := addr_tm_of_level_le Gs Y hηR hlevN
    have hYN : Y N (tm Gs Y N η) = x := by
      rw [← hcd.consistent.Yxi_eq Gs Y hlevN]
      exact hYη
    have htm0 : tm Gs Y N η ≠ 0 := by
      intro h0
      rw [h0, addr_zero_eq_zero] at hrep
      rw [← hrep, PathProperties.tau_zero] at heq
      exact ht.ne' (ENNReal.coe_eq_zero.1 heq.symm)
    obtain ⟨k, hk⟩ : ∃ k, tm Gs Y N η = k + 1 := ⟨tm Gs Y N η - 1, by omega⟩
    have hηaddr : addr Gs Y N (k + 1) = η := by
      rw [← hk]
      exact hrep
    have hYk1 : Y N (k + 1) = x := by
      rw [← hk]
      exact hYN
    have hyN : Y N k ∈ Gs N :=
      hin N k (by rw [hYk1]; exact hxN) (by rw [hYk1]; exact hnbrN)
    have haR : Realized Gs Y (addr Gs Y N k) := realized_addr Gs Y N k
    have hYa : Yxi Gs Y (addr Gs Y N k) = Y N k := hcd.consistent.Yxi_addr Gs Y N k
    have hmemN : Yxi Gs Y (addr Gs Y N k) ∈ Gs N := by
      rw [hYa]
      exact hyN
    have hsuccAt : succAt Gs Y N (addr Gs Y N k) = η := by
      show addr Gs Y N (tm Gs Y N (addr Gs Y N k) + 1) = η
      rw [tm_addr]
      exact hηaddr
    have hsucc : succ Gs Y (addr Gs Y N k) = η := by
      obtain ⟨hsR, hlt, hnone⟩ :=
        hcd.consistent.succ_spec Gs Y hcd.monotone hcd.cover haR
      have hlt' : toLex (addr Gs Y N k) < toLex η := by
        rw [lt_iff_tm_lt Gs Y (n := N) ⟨k, rfl⟩ ⟨k + 1, hηaddr⟩, tm_addr, hk]
        exact Nat.lt_succ_self k
      rcases lt_trichotomy (toLex (succ Gs Y (addr Gs Y N k))) (toLex η) with h1 | h2 | h3
      · exact absurd ⟨hlt, by rw [hsuccAt]; exact h1⟩
          (hcd.consistent.not_lt_lt_succAt Gs Y hcd.monotone (n := N) ⟨k, rfl⟩ hmemN hsR)
      · exact toLex_inj.mp h2
      · exact absurd ⟨hlt', h3⟩ (hnone η hηR)
    have haF : tau Gs Y w E (addr Gs Y N k) ≠ ⊤ := hd.tau_ne_top haR
    have htau : tau Gs Y w E η =
        tau Gs Y w E (addr Gs Y N k) + holding Gs Y w E (addr Gs Y N k) := by
      rw [← hsucc]
      exact hcd.tau_succ haR
    have hhpos : 0 < holding Gs Y w E (addr Gs Y N k) :=
      Existence.holding_pos Gs Y w E hcd.ratePos (hd.pos _)
    have hlt2 : tau Gs Y w E (addr Gs Y N k) < ((t : ℝ≥0) : ℝ≥0∞) := by
      rw [← heq, htau]
      exact ENNReal.lt_add_right haF hhpos.ne'
    refine ⟨Y N k, (tau Gs Y w E (addr Gs Y N k)).toNNReal, ?_, fun r hr => ?_⟩
    · rw [← ENNReal.coe_lt_coe, ENNReal.coe_toNNReal haF]
      exact hlt2
    · have hInt : InInterval Gs Y w E (addr Gs Y N k) ((r : ℝ≥0) : ℝ≥0∞) := by
        refine ⟨haR, ?_, ?_⟩
        · rw [← ENNReal.coe_toNNReal haF, ENNReal.coe_le_coe]
          exact hr.1
        · rw [hsucc, heq]
          exact ENNReal.coe_lt_coe.2 hr.2
      rw [hcd.consistent.X_eq_of_inInterval Gs Y w E hcd.monotone hcd.cover hInt, hYa]

end Deterministic

/-! ## The almost-sure statements for the constructed process -/

section Probabilistic

variable {V : Type u} [MeasurableSpace V] [Countable V] [MeasurableSingletonClass V]
  [Nontrivial V]

/-- **`hedge` for the constructed process at any positive rate satisfying (3.16).** -/
theorem ae_edgeJumps_process (F : IndexedCells V) (D : F.graph.Exhaustion)
    (hG : F.graph.toSimpleGraph.Connected) (w : V → ℝ) (hw : ∀ v, 0 < w v) (z : V)
    (hsum : ∀ᵐ ω ∂Existence.sampleLaw D hG z,
      HoldingTimesSummable (D.levelSets (D.nz z)) ω.1 w ω.2) :
    ∀ᵐ ω ∂Existence.sampleLaw D hG z,
      EdgeJumps F (fun t => Existence.process D w t ω) := by
  filter_upwards [Existence.sampleLaw_ae_consistent D hG z,
    Existence.sampleLaw_ae_start D hG z, Existence.sampleLaw_ae_pos D hG z,
    sampleLaw_ae_forall_stepKernel_ne_zero D hG z, hsum] with ω hc h0 hpos hstep hs
  have hcd : HoldingTimeChange.ChainData (D.levelSets (D.nz z)) ω.1 w :=
    ⟨hc, D.levelSets_mono (D.nz z), D.exists_mem_levelSets (D.nz z), hw⟩
  have hd : HoldingTimeChange.ClockData (D.levelSets (D.nz z)) ω.1 w ω.2 := ⟨hpos, hs⟩
  have heq : (fun t => Existence.process D w t ω) = X (D.levelSets (D.nz z)) ω.1 w ω.2 :=
    funext fun t => Existence.process_eq D w (h0 0) hc t
  rw [heq]
  exact edgeJumps_X F hcd hd fun m j hm =>
    adj_of_stepKernel_ne_zero D hG (n := D.nz z + m)
      (show ω.1 m j ∈ D.Gsub (D.nz z + m) from hm) (hstep m j)

/-- **No entrance from the nonvertex state for the constructed process**, on a locally finite
graph, at any positive rate satisfying (3.16). -/
theorem ae_noBoundaryEntrance_process (F : IndexedCells V)
    (hloc : ∀ v, (F.graph.toSimpleGraph.neighborSet v).Finite) (D : F.graph.Exhaustion)
    (hG : F.graph.toSimpleGraph.Connected) (w : V → ℝ) (hw : ∀ v, 0 < w v) (z : V)
    (hsum : ∀ᵐ ω ∂Existence.sampleLaw D hG z,
      HoldingTimesSummable (D.levelSets (D.nz z)) ω.1 w ω.2) :
    ∀ᵐ ω ∂Existence.sampleLaw D hG z,
      NoBoundaryEntrance (fun t => Existence.process D w t ω) := by
  filter_upwards [Existence.sampleLaw_ae_consistent D hG z,
    Existence.sampleLaw_ae_start D hG z, Existence.sampleLaw_ae_pos D hG z,
    sampleLaw_ae_forall_stepKernel_ne_zero D hG z, hsum] with ω hc h0 hpos hstep hs
  have hcd : HoldingTimeChange.ChainData (D.levelSets (D.nz z)) ω.1 w :=
    ⟨hc, D.levelSets_mono (D.nz z), D.exists_mem_levelSets (D.nz z), hw⟩
  have hd : HoldingTimeChange.ClockData (D.levelSets (D.nz z)) ω.1 w ω.2 := ⟨hpos, hs⟩
  have heq : (fun t => Existence.process D w t ω) = X (D.levelSets (D.nz z)) ω.1 w ω.2 :=
    funext fun t => Existence.process_eq D w (h0 0) hc t
  rw [heq]
  refine noBoundaryEntrance_X F.graph hcd hd (fun x => ?_) fun m j hm hnbr =>
    mem_of_stepKernel_ne_zero D hG (n := D.nz z + m)
      (show ω.1 m (j + 1) ∈ D.Gsub (D.nz z + m) from hm)
      (fun u hu => show u ∈ D.Gsub (D.nz z + m) from hnbr u hu) (hstep m j)
  obtain ⟨N, hN⟩ := exists_levelSets_superset_of_finite (D.levelSets_mono (D.nz z))
    (D.exists_mem_levelSets (D.nz z)) (hloc x)
  exact ⟨N, fun u hu => hN hu⟩

/-- **`htc` for any rate dominating the admissible rate.**  The proof of
`FastClockTimeChange.ae_isHomeomorphicTimeChange_fast`, with Lemma 3.5 applied at `w ≥ w*`. -/
theorem ae_isHomeomorphicTimeChange_of_rateFunction_le (F : IndexedCells V)
    (D : F.graph.Exhaustion) (hG : F.graph.toSimpleGraph.Connected)
    (hrate : ∀ v, 0 < areaRate F v) (w : V → ℝ) (hw : ∀ v, 0 < w v)
    (hdom : ∀ v, D.rateFunction hG v ≤ w v) (z : V)
    (hexp : ∀ᵐ ω ∂(areaSampleLaw F D hG z),
      HoldingTimesSummable (D.levelSets (D.nz z)) ω.1 (areaRate F) ω.2) :
    ∀ᵐ ω ∂(areaSampleLaw F D hG z),
      IsHomeomorphicTimeChange (fun t => exponentialAreaPath F D t ω)
        (fun t => Existence.process D w t ω) := by
  have hfin : {x : V | w x < D.rateFunction hG x}.Finite := by
    have he : {x : V | w x < D.rateFunction hG x} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact not_lt_of_ge (hdom x)
    rw [he]
    exact finite_empty
  have hfast : ∀ᵐ ω ∂(areaSampleLaw F D hG z),
      HoldingTimesSummable (D.levelSets (D.nz z)) ω.1 w ω.2 :=
    D.rateFunction_ae_holdingTimesSummable hG w hw hfin (D.nz z) (D.mem_Gsub_nz z)
  filter_upwards [Existence.sampleLaw_ae_consistent D hG z,
    Existence.sampleLaw_ae_start D hG z, Existence.sampleLaw_ae_pos D hG z,
    hexp, hfast] with ω hc h0 hpos hs1 hs2
  have hhold := FastClockTimeChange.holding_reweight (D.levelSets (D.nz z)) ω.1 hrate hw ω.2
  have hcd : HoldingTimeChange.ChainData (D.levelSets (D.nz z)) ω.1 (areaRate F) :=
    ⟨hc, D.levelSets_mono (D.nz z), D.exists_mem_levelSets (D.nz z), hrate⟩
  have hd₂ : HoldingTimeChange.ClockData (D.levelSets (D.nz z)) ω.1 (areaRate F) ω.2 :=
    ⟨hpos, hs1⟩
  have hd₁ : HoldingTimeChange.ClockData (D.levelSets (D.nz z)) ω.1 (areaRate F)
      (FastClockTimeChange.reweight (D.levelSets (D.nz z)) ω.1 (areaRate F) w ω.2) :=
    ⟨FastClockTimeChange.reweight_pos _ _ hrate hw hpos,
      FastClockTimeChange.holdingTimesSummable_congr (fun a => (hhold a).symm) hs2⟩
  have heqExp : (fun t => exponentialAreaPath F D t ω)
      = X (D.levelSets (D.nz z)) ω.1 (areaRate F) ω.2 :=
    funext fun t => Existence.process_eq D (areaRate F) (h0 0) hc t
  have heqFast : (fun t => Existence.process D w t ω)
      = X (D.levelSets (D.nz z)) ω.1 (areaRate F)
        (FastClockTimeChange.reweight (D.levelSets (D.nz z)) ω.1 (areaRate F) w ω.2) := by
    funext t
    rw [show Existence.process D w t ω = X (D.levelSets (D.nz z)) ω.1 w ω.2 t from
      Existence.process_eq D w (h0 0) hc t]
    exact FastClockTimeChange.X_congr hc (D.levelSets_mono (D.nz z))
      (D.exists_mem_levelSets (D.nz z)) (fun a => (hhold a).symm) t
  rw [heqExp, heqFast]
  exact HoldingTimeChange.isHomeomorphicTimeChange_X hcd hd₁ hd₂

end Probabilistic

end ReflectedGMS.SpatialExtensionChainJumps
