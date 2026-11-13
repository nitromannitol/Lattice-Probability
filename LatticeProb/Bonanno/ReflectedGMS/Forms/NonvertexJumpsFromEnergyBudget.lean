/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.NonvertexJumpsFromEnergyBudget at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.FullEnergyPathNoNonvertexJumps
import LatticeProb.Bonanno.ReflectedGMS.Process.SpatialExtensionCadlag
import LatticeProb.Bonanno.ReflectedGMS.Process.SpatialExtensionChainJumps

/-!
# `NoJumpsAtNonvertexTimes` from the spatial cutoffs

This is the weld between the two halves of the nonvertex part of manuscript
`p:prop:purejump`:

* `Forms/FullEnergyPathNoNonvertexJumps.ae_leftLim_eq_of_none` — theorem (★): for **one**
  vector `U` of the full Hilbert energy domain, the càdlàg path
  `fullEnergyPotentialPathLimit … U` has `leftLim = value` at every positive nonvertex time,
  proved by an energy budget with matching constants;
* `Process/SpatialExtensionCadlag.HasSpatialCutoffs` — the bridge from such vectors to the
  plane-valued field `Φ`: each coordinate `Φ · i` agrees, on each ball `{‖z v‖ ≤ R}`, with the
  decoded function of a domain vector `U i R`.

`NoJumpsAtNonvertexTimes X Φ` quantifies over **every** càdlàg vertex-agreeing path `Z`.  The
argument is local in time: given a positive nonvertex time `t`, choose a horizon `T > t` and a
radius `N` bounding the representatives visited on `[0, T + 1]`; then each coordinate of `Z`
agrees on `[0, T + 1)` with the (recentred) cutoff path of `U i N` — both are right-continuous
and they agree at the dyadic vertex times — and that path has no jump at `t` by (★).  So no
uniqueness statement about `Z` and no existence statement about the extension is used.

The hypothesis list is **verbatim** that of
`SpatialExtensionCadlag.ae_exists_cadlag_vertex_extension`, so this theorem plugs in wherever
that one already does (in particular at the canonical summable fast clock, where
`Summable m` is supplied by `SpatialExtensionEnvironment.summableFastRate_spec`).  Nothing
here certifies the cutoffs or the spatial bound.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace ReflectedGMS.NonvertexJumpsFromEnergyBudget

open ReflectedWalk FullNetworkForm
open ReflectedGMS.SpatialExtensionConstruction
open ReflectedGMS.FullEnergyPathNoNonvertexJumps

universe u

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
  [Nontrivial V] [DecidableEq V]

section Main

variable {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer} {PF : ProcessFamily V}
  (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF) (hG : G.toSimpleGraph.Connected)
  (hm : ∀ v, 0 < m v) (hmsum : Summable m)

include h hG hm hmsum

/-- **The nonvertex-time continuity clause of `p:prop:purejump`, from the spatial cutoffs.**

Almost surely under `P_o`, *every* càdlàg plane-valued path agreeing with `Φ` at the vertex
times of the walk is continuous at every positive nonvertex time. -/
theorem ae_noJumpsAtNonvertexTimes_of_cutoffs (z Φ : V → Plane)
    (hcut : HasSpatialCutoffs G m z Φ) (o : V)
    (hbdd : ∀ᵐ ω ∂PF.P o, ∀ T : ℝ≥0, ∃ M : ℝ, ∀ t : ℝ≥0, t ≤ T →
      ∀ v : V, PF.X t ω = some v → ‖z v‖ ≤ M) :
    ∀ᵐ ω ∂PF.P o,
      SpatialExtensionChainJumps.NoJumpsAtNonvertexTimes (fun t => PF.X t ω) Φ := by
  classical
  choose U hU using hcut
  -- the three pathwise facts about the cutoff paths, the third being (★)
  have hpaths : ∀ᵐ ω ∂PF.P o, ∀ (i : Fin 2) (R : ℕ),
      IsCadlag (fun t ↦ fullEnergyPotentialPathLimit G m hm PF o (U i R) t ω) ∧
      (∀ t x, PF.X t ω = some x →
        fullEnergyPotentialPathLimit G m hm PF o (U i R) t ω =
          unweight m (valueInclusion G m (U i R)) x -
            unweight m (valueInclusion G m (U i R)) o) ∧
      (∀ t : ℝ≥0, 0 < t → PF.X t ω = none →
        Function.leftLim (fun s ↦ fullEnergyPotentialPathLimit G m hm PF o (U i R) s ω) t =
          fullEnergyPotentialPathLimit G m hm PF o (U i R) t ω) := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro R
    filter_upwards [fullEnergyPotentialPathLimit_ae_cadlag_and_uniform h hG hm hmsum o (U i R) o,
      fullEnergyPotentialPathLimit_ae_eq_at_vertex_times h hG hm hmsum o (U i R) o,
      ae_leftLim_eq_of_none h hG hm hmsum o (U i R) o] with ω h1 h2 h3
    exact ⟨h1.1, h2, h3⟩
  have hdy : ∀ᵐ ω ∂PF.P o, ∀ s ∈ globalDyadicSupport, ∃ x : V, PF.X s ω = some x := by
    rw [ae_ball_iff globalDyadicSupport_countable]
    intro s _
    exact ((h o).2.1 s).mono fun _ hω => hω.1
  filter_upwards [hpaths, hdy, hbdd] with ω hp hd hb
  intro Z hZ hvert t ht hXt
  -- a horizon past `t` and a radius covering the representatives visited on `[0, T + 1]`
  obtain ⟨T, hT⟩ : ∃ T : ℕ, t < (T : ℝ≥0) := exists_nat_gt t
  obtain ⟨M, hM⟩ := hb ((T : ℝ≥0) + 1)
  obtain ⟨N, hN⟩ := exists_nat_ge M
  have htT : t < (T : ℝ≥0) + 1 := hT.trans (lt_add_of_pos_right _ one_pos)
  have hbound : ∀ s : ℝ≥0, s ≤ (T : ℝ≥0) + 1 → ∀ x : V, PF.X s ω = some x → ‖z x‖ ≤ (N : ℝ) :=
    fun s hs x hx => (hM s hs x hx).trans hN
  -- the recentred cutoff paths at radius `N`
  let Q : Fin 2 → ℝ≥0 → ℝ := fun i s ↦
    fullEnergyPotentialPathLimit G m hm PF o (U i N) s ω +
      unweight m (valueInclusion G m (U i N)) o
  have hQcad : ∀ i, IsCadlag (Q i) := fun i ↦ (hp i N).1.add IsCadlag.const
  have hQvert : ∀ (i : Fin 2) (s : ℝ≥0) (x : V), PF.X s ω = some x → ‖z x‖ ≤ (N : ℝ) →
      Q i s = Φ x i := by
    intro i s x hx hzx
    show fullEnergyPotentialPathLimit G m hm PF o (U i N) s ω +
      unweight m (valueInclusion G m (U i N)) o = Φ x i
    rw [(hp i N).2.1 s x hx, sub_add_cancel]
    exact hU i N hzx
  -- `Z` agrees coordinatewise with the cutoff paths on `[0, T + 1)`
  have hZQ : ∀ (i : Fin 2) (s : ℝ≥0), s < (T : ℝ≥0) + 1 → Z s i = Q i s := by
    intro i s hs
    have hZi : ContinuousWithinAt (fun u => Z u i) (Ioi s) s :=
      hZ.isRightContinuous.continuous_comp
        (PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) i) s
    refine eq_at_of_rightContinuous_of_eqOn_dyadic hs hZi ((hQcad i).isRightContinuous s)
      fun r hr _ hrb => ?_
    obtain ⟨x, hx⟩ := hd r hr
    rw [hvert r x hx, hQvert i r x hx (hbound r hrb.le x hx)]
  -- the left limit, coordinate by coordinate
  haveI : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  have hcoord : ∀ i : Fin 2, Tendsto (fun s => Z s i) (𝓝[<] t) (𝓝 (Z t i)) := by
    intro i
    have hQlim : Tendsto (Q i) (𝓝[<] t) (𝓝 (Q i t)) := by
      have h1 : Tendsto (fun s => fullEnergyPotentialPathLimit G m hm PF o (U i N) s ω)
          (𝓝[<] t) (𝓝 (fullEnergyPotentialPathLimit G m hm PF o (U i N) t ω)) := by
        have hlim := (hp i N).1.tendsto_nhdsLT_leftLim t
        rwa [(hp i N).2.2 t ht hXt] at hlim
      exact h1.add tendsto_const_nhds
    have heq : Q i =ᶠ[𝓝[<] t] fun s => Z s i := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (isOpen_Iio.mem_nhds htT)] with s hs
      exact (hZQ i s hs).symm
    have hZlim := Filter.Tendsto.congr' heq hQlim
    rwa [hZQ i t htT]
  have hofLp : Tendsto (fun s => (WithLp.ofLp (Z s) : Fin 2 → ℝ)) (𝓝[<] t)
      (𝓝 (WithLp.ofLp (Z t) : Fin 2 → ℝ)) := tendsto_pi_nhds.2 hcoord
  have hlim : Tendsto Z (𝓝[<] t) (𝓝 (Z t)) := by
    have hc := ((PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).tendsto
      (WithLp.ofLp (Z t) : Fin 2 → ℝ)).comp hofLp
    simpa only [Function.comp_def, WithLp.toLp_ofLp] using hc
  exact leftLim_eq_of_tendsto hlim

end Main

end ReflectedGMS.NonvertexJumpsFromEnergyBudget
