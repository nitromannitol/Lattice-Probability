/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.ReflectedCompactPaths at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.GlobalDyadicSupport
import LatticeProb.Bonanno.ReflectedGMS.Forms.DyadicLeftLimits
import LatticeProb.Bonanno.ReflectedGMS.Forms.GlobalDyadicDensity
import LatticeProb.Bonanno.ReflectedGMS.Forms.ResolventCompactLimits
import LatticeProb.Bonanno.ReflectedGMS.Forms.DenseRightLimitExtension
import LatticeProb.Bonanno.ReflectedGMS.Forms.VertexIndicatorRightContinuity
import LatticeProb.Bonanno.ReflectedGMS.Forms.VertexIndicatorLeftLimits

/-!
# Actual reflected paths in the resolvent compactification

The dyadic one-sided limits of all defining coordinates give a cadlag path in
the compact resolvent space.  Vertex indicators retain the original
`Option V`-valued path at every time: an actual vertex is embedded exactly,
whereas `none` is represented by a point outside the vertex range.
-/

-- Merged from `ReflectedGMS/Forms/GlobalDyadicLimits.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_GlobalDyadicLimits

/-! Global one-sided potential limits on the union of the existing dyadic
meshes, on a single event for every vertex coordinate and every time. -/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace ReflectedGMS

universe u
variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V]

theorem negativeDiscountedVertexPotential_ae_global_one_sided_limits [DecidableEq V]
    {G : ReflectedWalk.ConductanceGraph V} {m : V → ℝ}
    {hmin : G.EnergyMinimizer} {PF : ReflectedWalk.ProcessFamily V}
    (h : ReflectedWalk.IsReflectedWalk G (fun v ↦ G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) {alpha : ℝ} (ha : 0 < alpha) (z : V) :
    ∀ᵐ ω ∂PF.P z, ∀ y : V,
      (∀ t, ∃ c : ℝ, Tendsto (negativeDiscountedVertexPotential G m PF alpha y ω)
        (𝓝[globalDyadicSupport ∩ Ioi t] t) (𝓝 c)) ∧
      (∀ t, ∃ c : ℝ, Tendsto (negativeDiscountedVertexPotential G m PF alpha y ω)
        (𝓝[globalDyadicSupport ∩ Iio t] t) (𝓝 c)) := by
  have hr := ae_all_iff.mpr (fun y : V ↦
    negativeDiscountedVertexPotential_ae_dyadic_right_limits h hG hm hmsum ha y z)
  have hl := ae_all_iff.mpr (fun y : V ↦
    negativeDiscountedVertexPotential_ae_dyadic_left_limits h hG hm hmsum ha y z)
  filter_upwards [hr, hl] with ω hrω hlω y
  constructor
  · intro t
    obtain ⟨N, ht⟩ := exists_pow_two_horizon t
    have htt : t < ((2 ^ N : ℕ) : ℝ≥0) := by simpa using ht
    obtain ⟨c, hc⟩ := hrω y (2 ^ N) (by positivity) t htt
    refine ⟨c, ?_⟩
    rw [nhdsWithin_globalDyadicSupport_eq N ht (Ioi t)]
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hc
  · intro t
    by_cases ht0 : t = 0
    · subst t
      exact ⟨0, by simp⟩
    · obtain ⟨N, ht⟩ := exists_pow_two_horizon t
      have htt : t ≤ ((2 ^ N : ℕ) : ℝ≥0) := by simpa using ht.le
      obtain ⟨c, hc⟩ := hlω y (2 ^ N) (by positivity) t (pos_iff_ne_zero.mpr ht0) htt
      refine ⟨c, ?_⟩
      rw [nhdsWithin_globalDyadicSupport_eq N ht (Iio t)]
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using hc

end ReflectedGMS

end Merged_GlobalDyadicLimits

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace ReflectedGMS

open ReflectedWalk ReflectedWalk.Theorem16 FullNetworkForm

universe u

namespace ResolventCompactSpace

variable {V : Type u} [DecidableEq V]

/-- Collapse the added compact boundary back to the single point `none`. -/
noncomputable def toOption (G : ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (p : Space G m hm) : Option V := by
  classical
  exact if hp : p ∈ range (vertex G m hm) then some (Classical.choose hp) else none

@[simp] theorem toOption_vertex (G : ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (x : V) :
    toOption G m hm (vertex G m hm x) = some x := by
  classical
  simp only [toOption, dif_pos (mem_range_self x), Option.some.injEq]
  exact vertex_injective G m hm (Classical.choose_spec (mem_range_self x))

/-- An indicator value of one identifies the corresponding embedded vertex. -/
theorem eq_vertex_of_indicatorCoordinate_eq_one
    (G : ConductanceGraph V) (m : V → ℝ) (hm : ∀ v, 0 < m v)
    {p : Space G m hm} {x : V}
    (hx : indicatorCoordinate G m hm x p = 1) :
    p = vertex G m hm x := by
  rcases CompactVertexSpace.closure_coordinate_dichotomy
      (feature G m) bound (feature_abs_le G m hm) x p with hp | hp
  · exact Subtype.ext hp
  · change (p.1.1 x : ℝ) = 0 at hp
    change (p.1.1 x : ℝ) = 1 at hx
    linarith

theorem toOption_eq_none_iff (G : ConductanceGraph V) (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (p : Space G m hm) :
    toOption G m hm p = none ↔ p ∉ range (vertex G m hm) := by
  classical
  by_cases hp : p ∈ range (vertex G m hm)
  · simp [toOption, hp]
  · simp [toOption, hp]

end ResolventCompactSpace

variable {V : Type u} [MeasurableSpace V] [MeasurableSingletonClass V]
  [Countable V] [Nontrivial V]

private theorem exists_compact_limit_of_vertex_coordinate_limits [DecidableEq V]
    {G : ConductanceGraph V} {m : V → ℝ} (hm : ∀ v, 0 < m v)
    {A : Type*} (path : A → V) (l : Filter A) [NeBot l]
    (hI : ∀ y, ∃ c : ℝ,
      Tendsto (fun a => if path a = y then (1 : ℝ) else 0) l (𝓝 c))
    (hU : ∀ y, ∃ c : ℝ,
      Tendsto (fun a => vertexOccupationPotential G m 1 (path a) y) l (𝓝 c)) :
    ∃ p : ResolventCompactSpace.Space G m hm,
      Tendsto (fun a => ResolventCompactSpace.vertex G m hm (path a)) l (𝓝 p) := by
  choose iLim hiLim using hI
  choose uLim huLim using hU
  let rLim : ResolventCompactSpace.Index V → ℝ := fun q =>
    q.sum fun y c => (c : ℝ) * uLim y
  have hr (q : ResolventCompactSpace.Index V) :
      Tendsto (fun a => q.sum fun y c =>
        (c : ℝ) * vertexOccupationPotential G m 1 (path a) y) l (𝓝 (rLim q)) := by
    classical
    unfold rLim
    exact tendsto_finsetSum q.support fun y hy =>
      tendsto_const_nhds.mul (huLim y)
  obtain ⟨p, hp, -⟩ :=
    ResolventCompactSpace.existsUnique_tendsto_vertex_of_definingCoordinate_limits
      G m hm path l iLim rLim hiLim hr
  exact ⟨p, hp.1⟩

private theorem undiscountedPotential_limit [DecidableEq V]
    {G : ConductanceGraph V} {m : V → ℝ} {PF : ProcessFamily V}
    (z y : V) (ω : PF.Ω) (S : Set ℝ≥0) (t : ℝ≥0)
    (hdefined : ∀ s ∈ S, ∃ x : V, PF.X s ω = some x)
    {c : ℝ}
    (hc : Tendsto (negativeDiscountedVertexPotential G m PF 1 y ω)
      (𝓝[S] t) (𝓝 c)) :
    Tendsto (fun s => vertexOccupationPotential G m 1 ((PF.X s ω).getD z) y)
      (𝓝[S] t) (𝓝 (-Real.exp (t : ℝ) * c)) := by
  have he : Tendsto (fun s : ℝ≥0 => -Real.exp (s : ℝ)) (𝓝[S] t)
      (𝓝 (-Real.exp (t : ℝ))) := by
    exact ((Real.continuous_exp.comp continuous_subtype_val).neg.continuousAt).mono_left
      inf_le_left
  apply (he.mul hc).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  obtain ⟨x, hx⟩ := hdefined s hs
  simp only [negativeDiscountedVertexPotential, hx, Option.elim_some,
    Option.getD_some]
  ring_nf
  rw [← Real.exp_add]
  simp

private theorem compact_right_limit [DecidableEq V]
    {G : ConductanceGraph V} {m : V → ℝ} (hm : ∀ v, 0 < m v)
    {PF : ProcessFamily V} (z : V) (ω : PF.Ω)
    (hdefined : ∀ s ∈ globalDyadicSupport,
      ∃ x : V, PF.X s ω = some x)
    (hindicator : ∀ y : V,
      IsRightContinuous (fun t => if PF.X t ω = some y then (1 : ℝ) else 0))
    (hpotential : ∀ y : V, ∀ t, ∃ c : ℝ,
      Tendsto (negativeDiscountedVertexPotential G m PF 1 y ω)
        (𝓝[globalDyadicSupport ∩ Ioi t] t) (𝓝 c))
    (t : ℝ≥0) :
    ∃ p : ResolventCompactSpace.Space G m hm,
      Tendsto (fun s => ResolventCompactSpace.vertex G m hm ((PF.X s ω).getD z))
        (𝓝[globalDyadicSupport ∩ Ioi t] t) (𝓝 p) := by
  letI : NeBot (𝓝[globalDyadicSupport ∩ Ioi t] t) := by
    exact globalDyadicSupport_nhdsWithin_Ioi_neBot t
  apply exists_compact_limit_of_vertex_coordinate_limits hm
  · intro y
    refine ⟨if PF.X t ω = some y then 1 else 0, ?_⟩
    apply ((hindicator y t).mono_left (nhdsWithin_mono t inter_subset_right)).congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    obtain ⟨x, hx⟩ := hdefined s hs.1
    simp [hx]
  · intro y
    obtain ⟨c, hc⟩ := hpotential y t
    exact ⟨-Real.exp (t : ℝ) * c,
      undiscountedPotential_limit z y ω _ t
        (fun s hs => hdefined s hs.1) hc⟩

private theorem compact_left_limit [DecidableEq V]
    {G : ConductanceGraph V} {m : V → ℝ} (hm : ∀ v, 0 < m v)
    {PF : ProcessFamily V} (z : V) (ω : PF.Ω)
    (hdefined : ∀ s ∈ globalDyadicSupport,
      ∃ x : V, PF.X s ω = some x)
    (hindicator : ∀ y : V, ∀ t : ℝ≥0, 0 < t → ∃ c : ℝ,
      Tendsto (fun s => if PF.X s ω = some y then (1 : ℝ) else 0)
        (𝓝[<] t) (𝓝 c))
    (hpotential : ∀ y : V, ∀ t, ∃ c : ℝ,
      Tendsto (negativeDiscountedVertexPotential G m PF 1 y ω)
        (𝓝[globalDyadicSupport ∩ Iio t] t) (𝓝 c))
    (t : ℝ≥0) :
    ∃ p : ResolventCompactSpace.Space G m hm,
      Tendsto (fun s => ResolventCompactSpace.vertex G m hm ((PF.X s ω).getD z))
        (𝓝[globalDyadicSupport ∩ Iio t] t) (𝓝 p) := by
  by_cases ht : t = 0
  · subst t
    exact ⟨ResolventCompactSpace.vertex G m hm z, by simp⟩
  have htpos : 0 < t := pos_iff_ne_zero.mpr ht
  letI : NeBot (𝓝[globalDyadicSupport ∩ Iio t] t) := by
    exact globalDyadicSupport_nhdsWithin_Iio_neBot htpos
  apply exists_compact_limit_of_vertex_coordinate_limits hm
  · intro y
    obtain ⟨c, hc⟩ := hindicator y t htpos
    refine ⟨c, (hc.mono_left (nhdsWithin_mono t inter_subset_right)).congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    obtain ⟨x, hx⟩ := hdefined s hs.1
    simp [hx]
  · intro y
    obtain ⟨c, hc⟩ := hpotential y t
    exact ⟨-Real.exp (t : ℝ) * c,
      undiscountedPotential_limit z y ω _ t
        (fun s hs => hdefined s hs.1) hc⟩

/-- Almost every actual reflected path has a cadlag lift to the resolvent
compactification, and collapsing its added boundary recovers the original
`Option V`-valued path at every time. -/
theorem reflected_ae_exists_cadlag_resolventCompact_lift [DecidableEq V]
    {G : ConductanceGraph V} {m : V → ℝ} {hmin : G.EnergyMinimizer}
    {PF : ProcessFamily V}
    (h : IsReflectedWalk G (fun v => G.pi v / m v) hmin PF)
    (hG : G.toSimpleGraph.Connected) (hm : ∀ v, 0 < m v)
    (hmsum : Summable m) (default z : V) :
    ∀ᵐ ω ∂PF.P z, ∃ Y : ℝ≥0 → ResolventCompactSpace.Space G m hm,
      IsCadlag Y ∧
      (∀ t, Tendsto
        (fun s => ResolventCompactSpace.vertex G m hm ((PF.X s ω).getD default))
        (𝓝[globalDyadicSupport ∩ Ioi t] t) (𝓝 (Y t))) ∧
      ∀ t,
        ResolventCompactSpace.toOption G m hm (Y t) = PF.X t ω := by
  classical
  have hsupport : ∀ᵐ ω ∂PF.P z, ∀ s ∈ globalDyadicSupport,
      ∃ x : V, PF.X s ω = some x := by
    rw [ae_ball_iff globalDyadicSupport_countable]
    intro s hs
    exact ((h z).2.1 s).mono fun _ hω => hω.1
  filter_upwards [hsupport,
    reflected_vertexIndicators_ae_isRightContinuous h z,
    reflected_vertexIndicators_ae_tendsto_nhdsLT h hG
      (fun v => div_pos (G.pi_pos_of_connected hG v) (hm v)) z,
    negativeDiscountedVertexPotential_ae_global_one_sided_limits
      h hG hm hmsum (by norm_num : (0 : ℝ) < 1) z] with ω hdef hright hleft hpot
  let f : ℝ≥0 → ResolventCompactSpace.Space G m hm := fun s =>
    ResolventCompactSpace.vertex G m hm ((PF.X s ω).getD default)
  choose Y hY using fun t =>
    compact_right_limit hm default ω hdef hright (fun y => (hpot y).1) t
  refine ⟨Y, isCadlag_of_supported_one_sided_limits
    (fun t => ?_) hY (fun t => compact_left_limit hm default ω hdef hleft
      (fun y => (hpot y).2) t), hY, fun t => ?_⟩
  · exact globalDyadicSupport_nhdsWithin_Ioi_neBot t
  · letI : NeBot (𝓝[globalDyadicSupport ∩ Ioi t] t) :=
      globalDyadicSupport_nhdsWithin_Ioi_neBot t
    by_cases hXt : PF.X t ω = none
    · rw [hXt]
      apply (ResolventCompactSpace.toOption_eq_none_iff G m hm (Y t)).2
      rintro ⟨x, hx⟩
      have hlimY := (ResolventCompactSpace.indicatorCoordinate G m hm x).continuous.continuousAt.tendsto.comp
        (hY t)
      have hlim0 : Tendsto (fun s => ResolventCompactSpace.indicatorCoordinate G m hm x (f s))
          (𝓝[globalDyadicSupport ∩ Ioi t] t) (𝓝 0) := by
        have hr : Tendsto (fun s => if PF.X s ω = some x then (1 : ℝ) else 0)
            (𝓝[globalDyadicSupport ∩ Ioi t] t)
            (𝓝 (if PF.X t ω = some x then 1 else 0)) :=
          (hright x t).mono_left (nhdsWithin_mono t inter_subset_right)
        rw [if_neg (by simp [hXt])] at hr
        apply hr.congr'
        filter_upwards [self_mem_nhdsWithin] with s hs
        obtain ⟨v, hv⟩ := hdef s hs.1
        simp [f, hv]
      have : ResolventCompactSpace.indicatorCoordinate G m hm x (Y t) = 0 :=
        tendsto_nhds_unique hlimY hlim0
      have hone : ResolventCompactSpace.indicatorCoordinate G m hm x (Y t) = 1 := by
        rw [← hx]
        simp
      linarith
    · obtain ⟨x, hx⟩ : ∃ x, PF.X t ω = some x := by
        cases hopt : PF.X t ω with
        | none => exact False.elim (hXt hopt)
        | some x => exact ⟨x, rfl⟩
      have hlimY :=
        (ResolventCompactSpace.indicatorCoordinate G m hm x).continuous.continuousAt.tendsto.comp
          (hY t)
      have hlim1 : Tendsto
          (fun s => ResolventCompactSpace.indicatorCoordinate G m hm x (f s))
          (𝓝[globalDyadicSupport ∩ Ioi t] t) (𝓝 1) := by
        have hr : Tendsto (fun s => if PF.X s ω = some x then (1 : ℝ) else 0)
            (𝓝[globalDyadicSupport ∩ Ioi t] t)
            (𝓝 (if PF.X t ω = some x then 1 else 0)) :=
          (hright x t).mono_left (nhdsWithin_mono t inter_subset_right)
        rw [if_pos hx] at hr
        apply hr.congr'
        filter_upwards [self_mem_nhdsWithin] with s hs
        obtain ⟨v, hv⟩ := hdef s hs.1
        simp [f, hv]
      have hone : ResolventCompactSpace.indicatorCoordinate G m hm x (Y t) = 1 :=
        tendsto_nhds_unique hlimY hlim1
      have hvertex : Y t = ResolventCompactSpace.vertex G m hm x :=
        ResolventCompactSpace.eq_vertex_of_indicatorCoordinate_eq_one G m hm hone
      simp [hvertex, hx]

end ReflectedGMS
