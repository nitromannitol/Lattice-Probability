/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Process.SpatialExtensionCadlag at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.FullEnergyPotentialPathLimit
import LatticeProb.Bonanno.ReflectedGMS.Forms.GlobalDyadicDensity

/-!
# The càdlàg extension of `Φ` along a summable-speed reflected walk

Split out of `Process/SpatialExtensionConstruction.lean` so that it can be checked with
minimal imports.  This is the first paragraph of the proof of manuscript
`p:prop:pathsextend`: on a summable-speed clock the checked compact-resolvent machinery
(`fullEnergyPotentialPathLimit_ae_cadlag_and_uniform`,
`fullEnergyPotentialPathLimit_ae_eq_at_vertex_times`) gives, for every vector `U` of the full
Hilbert energy domain, a càdlàg path equal to `U(X_t) − U(X_0)` at vertex times.  The cutoffs
of `p:lem:spatialcutoffs` (`HasSpatialCutoffs`) are patched together across radii using a
compact-time spatial bound and right-density of the dyadic vertex times
(`ae_exists_cadlag_vertex_extension`).  The cutoff family and the spatial bound are
hypotheses; nothing here certifies them.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace ReflectedGMS.SpatialExtensionConstruction

open ReflectedWalk

/-! ## The càdlàg extension on a summable-speed clock -/

section Construction

variable {V : Type*} [MeasurableSpace V] [MeasurableSingletonClass V] [Countable V]
  [Nontrivial V] [DecidableEq V]

/-- **`p:lem:spatialcutoffs` as a family.**  Each coordinate of `Φ` agrees on every ball
`{‖z v‖ ≤ R}` with (the decoded function of) a vector of the full Hilbert energy domain for
the speed `m`.  This is the conclusion shape of
`SpatialHarmonicCutoff.exists_spatialHarmonicCutoff_hilbertDomain`. -/
def HasSpatialCutoffs (G : ConductanceGraph V) (m : V → ℝ) (z Φ : V → Plane) : Prop :=
  ∀ (i : Fin 2) (R : ℕ), ∃ U : FullNetworkForm.hilbertDomain G m,
    Set.EqOn (FullNetworkForm.unweight m (FullNetworkForm.valueInclusion G m U))
      (fun v => Φ v i) {v | ‖z v‖ ≤ (R : ℝ)}

/-- Two functions right-continuous at `t` that agree at the dyadic times of `(t, b)` agree at
`t`: the dyadic support clusters at `t` from the right. -/
theorem eq_at_of_rightContinuous_of_eqOn_dyadic {f g : ℝ≥0 → ℝ} {t b : ℝ≥0} (htb : t < b)
    (hf : ContinuousWithinAt f (Ioi t) t) (hg : ContinuousWithinAt g (Ioi t) t)
    (heq : ∀ s ∈ globalDyadicSupport, t < s → s < b → f s = g s) : f t = g t := by
  haveI := globalDyadicSupport_nhdsWithin_Ioi_neBot t
  have hle : 𝓝[globalDyadicSupport ∩ Ioi t] t ≤ 𝓝[Ioi t] t :=
    nhdsWithin_mono t inter_subset_right
  have hf' : Tendsto f (𝓝[globalDyadicSupport ∩ Ioi t] t) (𝓝 (f t)) :=
    hf.tendsto.mono_left hle
  have hg' : Tendsto g (𝓝[globalDyadicSupport ∩ Ioi t] t) (𝓝 (g t)) :=
    hg.tendsto.mono_left hle
  have hfg : Tendsto f (𝓝[globalDyadicSupport ∩ Ioi t] t) (𝓝 (g t)) := by
    refine hg'.congr' ?_
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (isOpen_Iio.mem_nhds htb)] with s hs hsb
    exact (heq s hs.1 hs.2 hsb).symm
  exact tendsto_nhds_unique hf' hfg

/-- **The càdlàg extension of `Φ` along the summable-speed reflected walk.**  For each
coordinate `i` and radius `R`, the checked full-energy path limit of the cutoff vector is
càdlàg and equals `Φ^i(X_t) − Φ^i(X_0)` at every vertex time inside the ball.  On the
almost-sure event where the visited representatives are bounded on every compact time
interval, the paths for large radii agree on `[0, T]` (they agree at the dyadic vertex times
and are right-continuous), so their eventual value defines one path, càdlàg and equal to `Φ`
at all vertex times.  Only the cutoff family is an input. -/
theorem ae_exists_cadlag_vertex_extension
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer} {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF) (hG : G.toSimpleGraph.Connected)
    (hm : ∀ v, 0 < m v) (hmsum : Summable m) (z Φ : V → Plane)
    (hcut : HasSpatialCutoffs G m z Φ) (o : V)
    (hbdd : ∀ᵐ ω ∂PF.P o, ∀ T : ℝ≥0, ∃ M : ℝ, ∀ t : ℝ≥0, t ≤ T →
      ∀ v : V, PF.X t ω = some v → ‖z v‖ ≤ M) :
    ∀ᵐ ω ∂PF.P o, ∃ Z : ℝ≥0 → Plane, IsCadlag Z ∧
      ∀ t x, PF.X t ω = some x → Z t = Φ x := by
  choose U hU using hcut
  have hpaths : ∀ᵐ ω ∂PF.P o, ∀ (i : Fin 2) (R : ℕ),
      IsCadlag (fun t ↦ fullEnergyPotentialPathLimit G m hm PF o (U i R) t ω) ∧
      ∀ t x, PF.X t ω = some x →
        fullEnergyPotentialPathLimit G m hm PF o (U i R) t ω =
          FullNetworkForm.unweight m (FullNetworkForm.valueInclusion G m (U i R)) x -
            FullNetworkForm.unweight m (FullNetworkForm.valueInclusion G m (U i R)) o := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    intro R
    filter_upwards [fullEnergyPotentialPathLimit_ae_cadlag_and_uniform h hG hm hmsum o
      (U i R) o, fullEnergyPotentialPathLimit_ae_eq_at_vertex_times h hG hm hmsum o
      (U i R) o] with ω h1 h2
    exact ⟨h1.1, h2⟩
  have hdy : ∀ᵐ ω ∂PF.P o, ∀ s ∈ globalDyadicSupport, ∃ x : V, PF.X s ω = some x := by
    rw [ae_ball_iff globalDyadicSupport_countable]
    intro s _
    exact ((h o).2.1 s).mono fun _ hω => hω.1
  filter_upwards [hpaths, hdy, hbdd] with ω hp hd hb
  choose M hM using hb
  choose N hN using fun T : ℕ => exists_nat_ge (M ((T : ℝ≥0) + 1))
  -- the recentred cutoff paths
  let Q : Fin 2 → ℕ → ℝ≥0 → ℝ := fun i R t ↦
    fullEnergyPotentialPathLimit G m hm PF o (U i R) t ω +
      FullNetworkForm.unweight m (FullNetworkForm.valueInclusion G m (U i R)) o
  have hQcad : ∀ i R, IsCadlag (Q i R) := fun i R ↦ (hp i R).1.add IsCadlag.const
  have hQvert : ∀ (i : Fin 2) (R : ℕ) (t : ℝ≥0) (x : V), PF.X t ω = some x →
      ‖z x‖ ≤ (R : ℝ) → Q i R t = Φ x i := by
    intro i R t x hx hzx
    show fullEnergyPotentialPathLimit G m hm PF o (U i R) t ω +
      FullNetworkForm.unweight m (FullNetworkForm.valueInclusion G m (U i R)) o = Φ x i
    rw [(hp i R).2 t x hx, sub_add_cancel]
    exact hU i R hzx
  -- the spatial bound on `[0, T + 1]`, with a natural radius
  have hbound : ∀ (T : ℕ) (t : ℝ≥0), t ≤ (T : ℝ≥0) + 1 → ∀ x : V, PF.X t ω = some x →
      ‖z x‖ ≤ (N T : ℝ) := fun T t ht x hx ↦ (hM _ t ht x hx).trans (hN T)
  -- consistency of the cutoff paths on `[0, T]`
  have hconst : ∀ (i : Fin 2) (T R : ℕ), N T ≤ R → ∀ t : ℝ≥0, t ≤ (T : ℝ≥0) →
      Q i R t = Q i (N T) t := by
    intro i T R hR t ht
    have htb : t < (T : ℝ≥0) + 1 := lt_of_le_of_lt ht (lt_add_of_pos_right _ one_pos)
    refine eq_at_of_rightContinuous_of_eqOn_dyadic htb ((hQcad i R).isRightContinuous t)
      ((hQcad i (N T)).isRightContinuous t) fun s hs _ hsb ↦ ?_
    obtain ⟨x, hx⟩ := hd s hs
    have hzx : ‖z x‖ ≤ (N T : ℝ) := hbound T s hsb.le x hx
    rw [hQvert i R s x hx (hzx.trans (Nat.cast_le.2 hR)), hQvert i (N T) s x hx hzx]
  -- the coordinate limits
  let Zc : Fin 2 → ℝ≥0 → ℝ := fun i t ↦ limUnder atTop fun R : ℕ ↦ Q i R t
  have hZc : ∀ (i : Fin 2) (T : ℕ) (t : ℝ≥0), t ≤ (T : ℝ≥0) → Zc i t = Q i (N T) t := by
    intro i T t ht
    show limUnder atTop (fun R : ℕ ↦ Q i R t) = Q i (N T) t
    refine Filter.Tendsto.limUnder_eq (tendsto_const_nhds.congr' ?_)
    filter_upwards [eventually_ge_atTop (N T)] with R hR
    exact (hconst i T R hR t ht).symm
  have hhor : ∀ t : ℝ≥0, ∃ T : ℕ, t < (T : ℝ≥0) := fun t ↦ exists_nat_gt t
  have hZccad : ∀ i, IsCadlag (Zc i) := by
    intro i
    constructor
    · intro t
      obtain ⟨T, hT⟩ := hhor t
      have hev : Zc i =ᶠ[𝓝[>] t] Q i (N T) := by
        filter_upwards [mem_nhdsWithin_of_mem_nhds
          (mem_of_superset (isOpen_Iio.mem_nhds hT) Iio_subset_Iic_self)] with s hs
        exact hZc i T s hs
      exact ((hQcad i (N T)).isRightContinuous t).congr_of_eventuallyEq hev (hZc i T t hT.le)
    · intro t
      obtain ⟨T, hT⟩ := hhor t
      obtain ⟨l, hl⟩ := (hQcad i (N T)).tendsto_nhdsLT t
      refine ⟨l, hl.congr' ?_⟩
      filter_upwards [mem_nhdsWithin_of_mem_nhds
        (mem_of_superset (isOpen_Iio.mem_nhds hT) Iio_subset_Iic_self)] with s hs
      exact (hZc i T s hs).symm
  refine ⟨fun t ↦ (WithLp.toLp 2 (fun i ↦ Zc i t) : Plane), ?_, ?_⟩
  · have hpi : IsCadlag (fun t ↦ fun i ↦ Zc i t) := by
      constructor
      · intro t
        exact continuousWithinAt_pi.2 fun i ↦ (hZccad i).isRightContinuous t
      · intro t
        choose l hl using fun i ↦ (hZccad i).tendsto_nhdsLT t
        exact ⟨l, tendsto_pi_nhds.2 hl⟩
    exact hpi.continuous_comp (PiLp.continuous_toLp 2 fun _ : Fin 2 => ℝ)
  · intro t x hx
    obtain ⟨T, hT⟩ := hhor t
    have hzx : ‖z x‖ ≤ (N T : ℝ) := hbound T t (hT.le.trans le_self_add) x hx
    have hcoord : ∀ i, Zc i t = Φ x i := fun i ↦ by
      rw [hZc i T t hT.le]
      exact hQvert i (N T) t x hx hzx
    exact (congrArg (WithLp.toLp 2) (funext hcoord)).trans (WithLp.toLp_ofLp 2 (Φ x))

end Construction


end ReflectedGMS.SpatialExtensionConstruction
