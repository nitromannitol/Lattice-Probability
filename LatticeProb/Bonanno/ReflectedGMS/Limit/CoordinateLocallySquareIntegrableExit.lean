/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.CoordinateLocallySquareIntegrableExit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.LocalHarmonicClockOrthogonality
import LatticeProb.Bonanno.ReflectedGMS.Process.SpatialExtensionCadlag
import LatticeProb.Bonanno.ReflectedGMS.Process.SpatialExtensionChainJumps
import LatticeProb.Bonanno.ReflectedGMS.Forms.GlobalDyadicDensity

/-!
# Step (d) of bracket atom 1, pathwise: the stopped coordinate is the time-changed stopped
# fast potential

Along one sample, let `X` be the area path, `Y` the fast path, and `e` the area clock, so that
`X_t = Y_{e⁻¹ t}`.  Let `M` be the càdlàg spatial extension of `Φ` along `X`, and `N` the
centred full-energy path of the cutoff `u` along `Y` (`N_q = u(Y_q) − u(start)` at vertex
times).  With `A = {‖z‖ ≤ R/2}` (the region of the variational test of step (a)) and
`σ = ` the first time `X` sits at a vertex outside `A`, this file proves, **deterministically**,

`M_{t ∧ σ} · i = u(start) + N_{e⁻¹(t) ∧ e⁻¹(σ)}`  for every `t`,

together with a uniform bound on the stopped fast path — exactly the identification and the
`hC` input the clock change `martingale_stoppedValue_clock_of_bound_of_ae` needs.

## The one delicate point: the value at the exit time

Before `σ` every vertex visited is in `A`, where `u = Φ · i`, and both sides are right limits
along dyadic vertex times.  **At `σ` itself** the visited vertex is outside `A`, and `u = Φ · i`
is only known on `B = {‖z‖ ≤ R}`.  Two cases (`exists_right_window`):

* `X_σ = w` a vertex.  If `w ∉ A`, the path is left-vertex-constant at `σ`
  (`NoBoundaryEntrance`, the checked "no entrance from the nonvertex state"), at some `v ∈ A`,
  and the jump `v → w` is an edge (`EdgeJumps`), so `‖z w‖ ≤ R` by the geometric
  `LocalHarmonicClock.norm_le_of_adj`.
* `X_σ = none` (an end at a finite position may sit on the boundary of `A`, since the cells
  need not be locally finite).  `M` is continuous there, its values just before `σ` are
  `Φ`-values on `A`, so `‖Φ‖ ≤ K + 2` on the vertices visited just after `σ`, which the
  sublinear comparison `hzΦ` places in `B`.

In both cases the vertices visited on a short window `(σ, σ + δ)` lie in `B`, and the
right-limit argument goes through at `σ` too.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace ReflectedGMS.CoordinateLocallySquareIntegrableExit

open StatementIngredients
open ReflectedGMS.SpatialExtensionConstruction ReflectedGMS.SpatialExtensionChainJumps

universe u

/-! ## Right limits along dyadic times -/

/-- A path right continuous at `θ` and bounded along the dyadic times just to the right of `θ`
is bounded at `θ`. -/
theorem norm_le_of_dyadic_right {f : ℝ≥0 → Plane} {θ δ : ℝ≥0} (hδ : 0 < δ)
    (hf : ContinuousWithinAt f (Ioi θ) θ) {K : ℝ}
    (hK : ∀ r ∈ globalDyadicSupport, θ < r → r < θ + δ → ‖f r‖ ≤ K) : ‖f θ‖ ≤ K := by
  haveI := globalDyadicSupport_nhdsWithin_Ioi_neBot θ
  have hle : 𝓝[globalDyadicSupport ∩ Ioi θ] θ ≤ 𝓝[Ioi θ] θ :=
    nhdsWithin_mono θ inter_subset_right
  have hlim : Tendsto (fun r => ‖f r‖) (𝓝[globalDyadicSupport ∩ Ioi θ] θ) (𝓝 ‖f θ‖) :=
    (hf.tendsto.mono_left hle).norm
  refine le_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (isOpen_Iio.mem_nhds (lt_add_of_pos_right θ hδ))] with r hr hrb
  exact hK r hr.1 hr.2 hrb

/-! ## The deterministic identification -/

section Pathwise

variable {V : Type u} [Countable V] {F : IndexedCells V} (hF : Geometry F)
  {z : V → Plane} (hz : CellRepresentatives F z) {R : ℝ} (hR : 0 < R)
  (hD : ∀ v : V, Hits F (Metric.closedBall (0 : Plane) R) v →
    Metric.diam (F.cell v : Set Plane) ≤ R / 100)
  {Φ : V → Plane} {K : ℝ}
  (hzΦ : ∀ v, ‖Φ v‖ ≤ K + 2 → ‖z v‖ ≤ R)
  (hΦA : ∀ v, ‖z v‖ ≤ R / 2 → ‖Φ v‖ ≤ K)
  {X : ℝ≥0 → Option V}
  (hrc : ∀ t, (∃ x, X t = some x) → ∃ ε : ℝ≥0, 0 < ε ∧ ∀ s ∈ Ico t (t + ε), X s = X t)
  (hent : NoBoundaryEntrance X) (hedge : EdgeJumps F X)
  (hdy : ∀ s ∈ globalDyadicSupport, ∃ x, X s = some x)
  {M : ℝ≥0 → Plane} (hMv : ∀ t v, X t = some v → M t = Φ v)
  (hMn : ∀ t, X t = none → ContinuousAt M t)
  {σ : WithTop ℝ≥0} (hσpos : 0 < σ)
  (hpre : ∀ r : ℝ≥0, (r : WithTop ℝ≥0) < σ → ∀ v, X r = some v → ‖z v‖ ≤ R / 2)

include hF hz hR hD hzΦ hΦA hrc hent hedge hdy hMv hMn hσpos hpre in
/-- **The right window.**  At every time `θ ≤ σ` there is a window `(θ, θ + δ)` on which every
vertex visited lies in `B = {‖z‖ ≤ R}`; at `θ = σ` this is the exit-time analysis described in
the module docstring. -/
theorem exists_right_window (θ : ℝ≥0) (hθ : (θ : WithTop ℝ≥0) ≤ σ) :
    ∃ δ : ℝ≥0, 0 < δ ∧
      ∀ r : ℝ≥0, θ < r → r < θ + δ → ∀ x, X r = some x → ‖z x‖ ≤ R := by
  have hR2 : R / 2 ≤ R := by linarith
  rcases hθ.lt_or_eq with hlt | heq
  · -- strictly before the exit: every vertex of the window is in `A`
    by_cases hσ : σ = ⊤
    · refine ⟨1, one_pos, fun r _ _ x hx => ?_⟩
      have hA := hpre r (by rw [hσ]; exact WithTop.coe_lt_top r) x hx
      linarith
    · obtain ⟨s, rfl⟩ := WithTop.ne_top_iff_exists.1 hσ
      have hθs : θ < s := WithTop.coe_lt_coe.1 hlt
      refine ⟨s - θ, tsub_pos_of_lt hθs, fun r _ hr x hx => ?_⟩
      have hrs : r < s := by
        calc r < θ + (s - θ) := hr
          _ = s := add_tsub_cancel_of_le hθs.le
      have hA := hpre r (WithTop.coe_lt_coe.2 hrs) x hx
      linarith
  · -- at the exit
    have hθpos : 0 < θ := by
      have h0 : ((0 : ℝ≥0) : WithTop ℝ≥0) < (θ : WithTop ℝ≥0) := by
        rw [heq]
        exact hσpos
      exact WithTop.coe_lt_coe.1 h0
    have hpreθ : ∀ r : ℝ≥0, r < θ → ∀ v, X r = some v → ‖z v‖ ≤ R / 2 := fun r hr v hv =>
      hpre r (by rw [← heq]; exact WithTop.coe_lt_coe.2 hr) v hv
    cases hXθ : X θ with
    | some w =>
      obtain ⟨ε, hε, hconst⟩ := hrc θ ⟨w, hXθ⟩
      have hw : ‖z w‖ ≤ R := by
        by_cases hwA : ‖z w‖ ≤ R / 2
        · linarith
        · obtain ⟨v, s, hsθ, hsconst⟩ := hent θ hθpos w hXθ
          have hv : ‖z v‖ ≤ R / 2 := hpreθ s hsθ v (hsconst s ⟨le_rfl, hsθ⟩)
          have hvw : v ≠ w := by
            rintro rfl
            exact hwA hv
          have hadj := hedge θ v w ⟨s, hsθ, hsconst⟩ hXθ hvw
          exact LocalHarmonicClock.norm_le_of_adj hF hz hR hD hv hadj
      refine ⟨ε, hε, fun r hr1 hr2 x hx => ?_⟩
      have hXr : X r = some w := by rw [hconst r ⟨hr1.le, hr2⟩, hXθ]
      rw [hXr] at hx
      cases hx
      exact hw
    | none =>
      obtain ⟨δ', hδ', hball⟩ := Metric.continuousAt_iff.1 (hMn θ hXθ) 1 one_pos
      -- a dyadic vertex time just before `θ`
      haveI := globalDyadicSupport_nhdsWithin_Iio_neBot hθpos
      have hevb : ∀ᶠ r in 𝓝[globalDyadicSupport ∩ Iio θ] θ, r ∈ Metric.ball θ δ' :=
        mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds θ hδ')
      have hevs : ∀ᶠ r in 𝓝[globalDyadicSupport ∩ Iio θ] θ,
          r ∈ globalDyadicSupport ∩ Iio θ := self_mem_nhdsWithin
      obtain ⟨r₀, hr₀ball, hr₀d, hr₀lt⟩ := (hevb.and hevs).exists
      obtain ⟨x₀, hx₀⟩ := hdy r₀ hr₀d
      have hx₀A := hΦA x₀ (hpreθ r₀ hr₀lt x₀ hx₀)
      have hMθ : ‖M θ‖ ≤ K + 1 := by
        have h1 : dist (M r₀) (M θ) < 1 := hball hr₀ball
        rw [hMv r₀ x₀ hx₀, dist_comm, dist_eq_norm] at h1
        have h2 := norm_sub_norm_le (M θ) (Φ x₀)
        linarith
      refine ⟨Real.toNNReal δ', Real.toNNReal_pos.2 hδ', fun r hr1 hr2 x hx => ?_⟩
      have hdist : dist r θ < δ' := by
        rw [NNReal.dist_eq]
        have h1 : (θ : ℝ) < r := by exact_mod_cast hr1
        have h4 : ((θ + Real.toNNReal δ' : ℝ≥0) : ℝ) = (θ : ℝ) + δ' := by
          push_cast
          rw [Real.coe_toNNReal δ' hδ'.le]
        have h2 : (r : ℝ) < θ + δ' := by
          calc (r : ℝ) < ((θ + Real.toNNReal δ' : ℝ≥0) : ℝ) := by exact_mod_cast hr2
            _ = θ + δ' := h4
        rw [abs_lt]
        constructor <;> linarith
      have h1 : dist (M r) (M θ) < 1 := hball hdist
      rw [hMv r x hx, dist_eq_norm] at h1
      have h2 := norm_sub_norm_le (Φ x) (M θ)
      exact hzΦ x (by linarith)

include hF hz hR hD hzΦ hΦA hrc hent hedge hdy hMv hMn hσpos hpre in
/-- **The coordinate identity up to and including the exit.**  For every `θ ≤ σ`,
`M_θ · i = u(start) + N_{e⁻¹ θ}`. -/
theorem coord_eq_of_le_exit (i : Fin 2) {u : V → ℝ} (hu : ∀ v, ‖z v‖ ≤ R → u v = Φ v i)
    (start : V) {Y : ℝ≥0 → Option V} (e : ℝ≥0 ≃o ℝ≥0) (hXY : ∀ t, X t = Y (e.symm t))
    (hMc : IsCadlag M) {N : ℝ≥0 → ℝ} (hNc : IsCadlag N)
    (hNv : ∀ q y, Y q = some y → N q = u y - u start)
    (θ : ℝ≥0) (hθ : (θ : WithTop ℝ≥0) ≤ σ) :
    M θ i = u start + N (e.symm θ) := by
  obtain ⟨δ, hδ, hwin⟩ :=
    exists_right_window hF hz hR hD hzΦ hΦA hrc hent hedge hdy hMv hMn hσpos hpre θ hθ
  refine eq_at_of_rightContinuous_of_eqOn_dyadic (f := fun r => M r i)
    (g := fun r => u start + N (e.symm r)) (lt_add_of_pos_right θ hδ) ?_ ?_ ?_
  · exact ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) i).continuousAt).comp_continuousWithinAt
      (hMc.isRightContinuous θ)
  · refine continuousWithinAt_const.add ?_
    exact (hNc.isRightContinuous (e.symm θ)).comp e.symm.continuous.continuousWithinAt
      (fun r hr => e.symm.strictMono hr)
  · intro r hr hθr hrb
    obtain ⟨x, hx⟩ := hdy r hr
    have hzx := hwin r hθr hrb x hx
    have hY : Y (e.symm r) = some x := by rw [← hXY]; exact hx
    show M r i = u start + N (e.symm r)
    rw [hMv r x hx, hNv _ x hY, hu x hzx]
    ring

include hF hz hR hD hzΦ hΦA hrc hent hedge hdy hMv hMn hσpos hpre in
/-- **The bound up to and including the exit.**  If `‖Φ‖ ≤ K'` on `B = {‖z‖ ≤ R}`, then
`‖M_θ‖ ≤ K'` for every `θ ≤ σ`. -/
theorem norm_le_of_le_exit (hMc : IsCadlag M) {K' : ℝ}
    (hΦB : ∀ v, ‖z v‖ ≤ R → ‖Φ v‖ ≤ K') (θ : ℝ≥0) (hθ : (θ : WithTop ℝ≥0) ≤ σ) :
    ‖M θ‖ ≤ K' := by
  obtain ⟨δ, hδ, hwin⟩ :=
    exists_right_window hF hz hR hD hzΦ hΦA hrc hent hedge hdy hMv hMn hσpos hpre θ hθ
  refine norm_le_of_dyadic_right hδ (hMc.isRightContinuous θ) fun r hr hθr hrb => ?_
  obtain ⟨x, hx⟩ := hdy r hr
  rw [hMv r x hx]
  exact hΦB x (hwin r hθr hrb x hx)

end Pathwise

/-! ## The stopped form -/

/-- The clock commutes with stopping: `min (e⁻¹ t) (e⁻¹ σ) = e⁻¹ (min t σ)`. -/
theorem min_coe_symm_map (e : ℝ≥0 ≃o ℝ≥0) (t : ℝ≥0) (σ : WithTop ℝ≥0) :
    min ((e.symm t : ℝ≥0) : WithTop ℝ≥0) (WithTop.map e.symm σ) =
      WithTop.map e.symm (min (t : WithTop ℝ≥0) σ) := by
  cases σ with
  | top =>
    show min ((e.symm t : ℝ≥0) : WithTop ℝ≥0) ⊤ =
      WithTop.map e.symm (min (t : WithTop ℝ≥0) ⊤)
    rw [min_eq_left le_top, min_eq_left le_top, WithTop.map_coe]
  | coe s =>
    rw [WithTop.map_coe, ← WithTop.coe_min, ← WithTop.coe_min, WithTop.map_coe]
    congr 1
    rcases le_total t s with h | h
    · rw [min_eq_left h, min_eq_left (e.symm.monotone h)]
    · rw [min_eq_right h, min_eq_right (e.symm.monotone h)]

/-- The untopped value of a finite time carried by the clock. -/
theorem untopA_map_symm (e : ℝ≥0 ≃o ℝ≥0) {θ : WithTop ℝ≥0} (hθ : θ ≠ ⊤) :
    (WithTop.map e.symm θ).untopA = e.symm θ.untopA := by
  obtain ⟨a, rfl⟩ := WithTop.ne_top_iff_exists.1 hθ
  rfl

section Stopped

variable {V : Type u} [Countable V] {F : IndexedCells V} (hF : Geometry F)
  {z : V → Plane} (hz : CellRepresentatives F z) {R : ℝ} (hR : 0 < R)
  (hD : ∀ v : V, Hits F (Metric.closedBall (0 : Plane) R) v →
    Metric.diam (F.cell v : Set Plane) ≤ R / 100)
  {Φ : V → Plane} {K : ℝ}
  (hzΦ : ∀ v, ‖Φ v‖ ≤ K + 2 → ‖z v‖ ≤ R)
  (hΦA : ∀ v, ‖z v‖ ≤ R / 2 → ‖Φ v‖ ≤ K)
  {X : ℝ≥0 → Option V}
  (hrc : ∀ t, (∃ x, X t = some x) → ∃ ε : ℝ≥0, 0 < ε ∧ ∀ s ∈ Ico t (t + ε), X s = X t)
  (hent : NoBoundaryEntrance X) (hedge : EdgeJumps F X)
  (hdy : ∀ s ∈ globalDyadicSupport, ∃ x, X s = some x)
  {M : ℝ≥0 → Plane} (hMv : ∀ t v, X t = some v → M t = Φ v)
  (hMn : ∀ t, X t = none → ContinuousAt M t)
  {σ : WithTop ℝ≥0} (hσpos : 0 < σ)
  (hpre : ∀ r : ℝ≥0, (r : WithTop ℝ≥0) < σ → ∀ v, X r = some v → ‖z v‖ ≤ R / 2)

include hF hz hR hD hzΦ hΦA hrc hent hedge hdy hMv hMn hσpos hpre in
/-- **The stopped identification.**  The coordinate of `M` stopped at `σ` is `u(start)` plus the
full-energy path `N` stopped at the carried exit `e⁻¹ σ` and read at `e⁻¹ t`. -/
theorem stoppedProcess_coord_eq (i : Fin 2) {u : V → ℝ}
    (hu : ∀ v, ‖z v‖ ≤ R → u v = Φ v i)
    (start : V) {Y : ℝ≥0 → Option V} (e : ℝ≥0 ≃o ℝ≥0) (hXY : ∀ t, X t = Y (e.symm t))
    (hMc : IsCadlag M) {N : ℝ≥0 → ℝ} (hNc : IsCadlag N)
    (hNv : ∀ q y, Y q = some y → N q = u y - u start) (t : ℝ≥0) :
    M (min (t : WithTop ℝ≥0) σ).untopA i =
      u start + N (min ((e.symm t : ℝ≥0) : WithTop ℝ≥0) (WithTop.map e.symm σ)).untopA := by
  have hne : min (t : WithTop ℝ≥0) σ ≠ ⊤ :=
    (lt_of_le_of_lt (min_le_left _ _) (WithTop.coe_lt_top t)).ne
  have hθ : (((min (t : WithTop ℝ≥0) σ).untopA : ℝ≥0) : WithTop ℝ≥0) ≤ σ := by
    rw [WithTop.untopA_eq_untop hne, WithTop.coe_untop]
    exact min_le_right _ _
  rw [min_coe_symm_map, untopA_map_symm e hne]
  exact coord_eq_of_le_exit hF hz hR hD hzΦ hΦA hrc hent hedge hdy hMv hMn hσpos hpre i hu
    start e hXY hMc hNc hNv _ hθ

include hF hz hR hD hzΦ hΦA hrc hent hedge hdy hMv hMn hσpos hpre in
/-- **The uniform bound on the stopped fast path**, at every fast time: the `hC` input of the
clock change. -/
theorem abs_stoppedProcess_le (i : Fin 2) {u : V → ℝ}
    (hu : ∀ v, ‖z v‖ ≤ R → u v = Φ v i)
    (start : V) {Y : ℝ≥0 → Option V} (e : ℝ≥0 ≃o ℝ≥0) (hXY : ∀ t, X t = Y (e.symm t))
    (hMc : IsCadlag M) {N : ℝ≥0 → ℝ} (hNc : IsCadlag N)
    (hNv : ∀ q y, Y q = some y → N q = u y - u start) {K' : ℝ}
    (hΦB : ∀ v, ‖z v‖ ≤ R → ‖Φ v‖ ≤ K') (hstart : ‖z start‖ ≤ R / 2) (q : ℝ≥0) :
    |N (min (q : WithTop ℝ≥0) (WithTop.map e.symm σ)).untopA| ≤ 2 * K' := by
  have hq : q = e.symm (e q) := (e.symm_apply_apply q).symm
  have hkey := stoppedProcess_coord_eq hF hz hR hD hzΦ hΦA hrc hent hedge hdy hMv hMn hσpos
    hpre i hu start e hXY hMc hNc hNv (e q)
  rw [← hq] at hkey
  have hne : min ((e q : ℝ≥0) : WithTop ℝ≥0) σ ≠ ⊤ :=
    (lt_of_le_of_lt (min_le_left _ _) (WithTop.coe_lt_top _)).ne
  have hθ : (((min ((e q : ℝ≥0) : WithTop ℝ≥0) σ).untopA : ℝ≥0) : WithTop ℝ≥0) ≤ σ := by
    rw [WithTop.untopA_eq_untop hne, WithTop.coe_untop]
    exact min_le_right _ _
  have hM := norm_le_of_le_exit hF hz hR hD hzΦ hΦA hrc hent hedge hdy hMv hMn hσpos hpre hMc
    hΦB _ hθ
  have hcoord : |M (min ((e q : ℝ≥0) : WithTop ℝ≥0) σ).untopA i| ≤ K' := by
    refine le_trans ?_ hM
    have := PiLp.norm_apply_le (p := 2) (M (min ((e q : ℝ≥0) : WithTop ℝ≥0) σ).untopA) i
    simpa [Real.norm_eq_abs] using this
  have hus : |u start| ≤ K' := by
    rw [hu start (by linarith)]
    refine le_trans ?_ (hΦB start (by linarith))
    have := PiLp.norm_apply_le (p := 2) (Φ start) i
    simpa [Real.norm_eq_abs] using this
  have heq : N (min (q : WithTop ℝ≥0) (WithTop.map e.symm σ)).untopA =
      M (min ((e q : ℝ≥0) : WithTop ℝ≥0) σ).untopA i - u start := by
    rw [hkey]
    ring
  rw [heq]
  calc |M (min ((e q : ℝ≥0) : WithTop ℝ≥0) σ).untopA i - u start|
      ≤ |M (min ((e q : ℝ≥0) : WithTop ℝ≥0) σ).untopA i| + |u start| := abs_sub _ _
    _ ≤ K' + K' := add_le_add hcoord hus
    _ = 2 * K' := by ring

end Stopped

end ReflectedGMS.CoordinateLocallySquareIntegrableExit
