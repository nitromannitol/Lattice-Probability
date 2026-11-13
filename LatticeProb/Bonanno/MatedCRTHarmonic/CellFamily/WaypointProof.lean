/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.CellFamily.WaypointProof at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.WaypointStrongMarkovFixed
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.WaypointProofPath

/-!
# Proof of the corrected scaled-grid estimate waypoint input `WaypointStrongMarkovInputFixed2`

the waypoint argument, Proposition 3.6′ (the waypoint proof) and §4.5, "Environment event" and "Itinerary for x"
(lines 586–606). Fix the environment net `W` of `waypoint_fixed2_environment_net`, a start `x` whose cell meets
`∂B_r(z)` at `y₀`, and the template `T = movedTemplate z r (arg (y₀ - z))`. For `m₀ = ⌈11600/s₀⌉` choose
`wp i ∈ W` within `s₀r/200` of `T(i/m₀)`. The `n`-th step restarts the walk and runs until the first visit to
`∂B_{s₀R}(wp (n+1))`, but at least one transition (`R = r/100`); it succeeds with quenched probability at least
`1/2` from every entrance state (Lemma 3.8 at scale `s₀`, `waypoint_lemma38_half`, and the fact that a vertex-path
event only depends on the start vertex). The iterated strong Markov property (`iteratedStrongMarkovLower`) gives
probability at least `2^{-m₀}` for `m₀` successes, and on that event, together with the almost-sure strict
adjacency of a loopless walk, the vertex path is a `PolarTemplateItinerary` (`waypointProof_itinerary_of_prefix`).

The main results are `waypointProof_itinerary_lower_bound` (one environment, deterministic hypotheses) and
`waypointStrongMarkovInputFixed2_holds`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.CellFamily

open MatedCRTHarmonic.Markov

/-! ### Measurability and the one-step lower bound -/

/-- The waypoint step time `max τ_inner 1` is a stopping time. -/
theorem waypointProof_isStoppingTime {E : Type*} (G : LFMultigraph ℤ E) (J : ℤ → Set ℂ)
    (wp : ℕ → ℂ) (s₀ R : ℝ) (n : ℕ) :
    IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => G.State))
      (waypointProofStep G J wp s₀ R n) :=
  IsStoppingTime.max_const (isStoppingTime_hitTime MeasurableSet.of_discrete) 1

/-- The success event of a waypoint step is an event of the stopped σ-algebra at the step time. -/
theorem waypointProof_event_measurable {E : Type*} (G : LFMultigraph ℤ E) (J : ℤ → Set ℂ)
    (wp : ℕ → ℂ) (s₀ R : ℝ) (n : ℕ) :
    MeasurableSet[(waypointProof_isStoppingTime G J wp s₀ R n).measurableSpace]
      (waypointProofEvent G J wp s₀ R n) := by
  have := GoodScales.countable_state G
  set Ain := waypointProofStates G J (sphere (wp (n + 1)) (s₀ * R)) with hAin
  set Aout := waypointProofStates G J (sphere (wp (n + 1)) R) with hAout
  have h1 : MeasurableSet[(waypointProof_isStoppingTime G J wp s₀ R n).measurableSpace]
      {ξ : ℕ → G.State | hitTime Ain ξ < hitTime Aout ξ} := by
    have hmono := IsStoppingTime.measurableSpace_mono
      (isStoppingTime_hitTime (MeasurableSet.of_discrete : MeasurableSet Ain))
      (waypointProof_isStoppingTime G J wp s₀ R n) (fun ξ => le_max_left _ _)
    exact hmono _ (waypoint_hitBefore_measurableAt_max_one MeasurableSet.of_discrete
      MeasurableSet.of_discrete)
  have h2 : MeasurableSet[(waypointProof_isStoppingTime G J wp s₀ R n).measurableSpace]
      {ξ : ℕ → G.State | GoodScales.StepOK G (G.vertexPath ξ 0) (G.vertexPath ξ 1)} := by
    apply measurableSet_stopping_of_forall_eq (waypointProof_isStoppingTime G J wp s₀ R n)
    · refine GoodScales.measurableSet_of_forall_eq_le 1 fun ω ω' hagree hω => ?_
      have h0 : ω 0 = ω' 0 := hagree 0 (Nat.zero_le 1)
      have h1 : ω 1 = ω' 1 := hagree 1 le_rfl
      change GoodScales.StepOK G (G.stateVertex (ω' 0)) (G.stateVertex (ω' 1))
      rw [← h0, ← h1]
      exact hω
    · intro ω ω' _ hagree hω
      have h0 : ω 0 = ω' 0 := hagree 0 (by simp)
      have h1 : ω 1 = ω' 1 := hagree 1 (by
        have := one_le_waypointProofTime Ain ω
        exact_mod_cast this)
      change GoodScales.StepOK G (G.stateVertex (ω' 0)) (G.stateVertex (ω' 1))
      rw [← h0, ← h1]
      exact hω
  exact h1.inter h2

/-- **One waypoint step succeeds with probability at least `1/2`** from a state whose vertex satisfies the
Lemma 3.8 lower bound for the next waypoint: the extra first-step condition holds almost surely, and the
hitting event only depends on the vertex path, hence only on the start vertex. -/
theorem waypointProof_event_prob {E : Type*} (G : LFMultigraph ℤ E) {o : ℤ}
    (H : CellularEmbedding G o) (wp : ℕ → ℂ) (s₀ R : ℝ) (n : ℕ) (y : G.State)
    (hgood : ENNReal.ofReal (1 / 2 : ℝ) ≤
      G.walkLaw (G.stateVertex y)
        {ξ | HitsBefore H.cell (wp (n + 1)) s₀ R (G.vertexPath ξ)}) :
    ENNReal.ofReal (1 / 2 : ℝ) ≤ chainLaw G.walkKernel y (waypointProofEvent G H.cell wp s₀ R n) := by
  have := GoodScales.countable_state G
  set Ain := waypointProofStates G H.cell (sphere (wp (n + 1)) (s₀ * R)) with hAin
  set Aout := waypointProofStates G H.cell (sphere (wp (n + 1)) R) with hAout
  have hstepnull : chainLaw G.walkKernel y
      {ξ : ℕ → G.State | GoodScales.StepOK G (G.vertexPath ξ 0) (G.vertexPath ξ 1)}ᶜ = 0 := by
    have hae := GoodScales.ae_stepOK G y
    rw [ae_iff] at hae
    have hsub : {ξ : ℕ → G.State | GoodScales.StepOK G (G.vertexPath ξ 0) (G.vertexPath ξ 1)}ᶜ ⊆
        {ξ | ¬ ∀ n, GoodScales.StepOK G (G.vertexPath ξ n) (G.vertexPath ξ (n + 1))} :=
      fun ξ hξ hall => hξ (hall 0)
    exact measure_mono_null hsub hae
  have heq : chainLaw G.walkKernel y (waypointProofEvent G H.cell wp s₀ R n) =
      chainLaw G.walkKernel y {ξ : ℕ → G.State | hitTime Ain ξ < hitTime Aout ξ} :=
    measure_inter_conull hstepnull
  rw [heq]
  have hmeas : MeasurableSet {ξ : ℕ → G.State |
      HitsBefore H.cell (wp (n + 1)) s₀ R (G.vertexPath ξ)} :=
    measurableSet_of_measurableSet_stopping
      (isStoppingTime_hitTime (MeasurableSet.of_discrete : MeasurableSet Ain))
      (waypoint_hitBefore_measurableAt_max_one (B := Aout) MeasurableSet.of_discrete
        MeasurableSet.of_discrete)
  have hvertex := GoodScales.chainLaw_vertexEvent_eq G
    (s := y) (s' := (Sum.inl (G.stateVertex y) : G.State)) rfl
    (Q := fun X => HitsBefore H.cell (wp (n + 1)) s₀ R X) hmeas
  change ENNReal.ofReal (1 / 2 : ℝ) ≤ chainLaw G.walkKernel y
    {ξ : ℕ → G.State | HitsBefore H.cell (wp (n + 1)) s₀ R (G.vertexPath ξ)}
  rw [hvertex]
  exact hgood

/-! ### The itinerary lower bound in a fixed environment -/

/-- **Waypoint itinerary lower bound** (the waypoint argument Proposition 3.6′ with §4.5's waypoints). In a loopless
cell configuration whose cells meeting `B_ρ(0)` have diameter at most `d ≤ s₀r/100`, let `W` be a net of the
annulus `0.85r ≤ |· - z| ≤ 1.15r` of mesh `s₀r/200` with `B_{r/100}(w) ⊆ B_ρ(0)`, and suppose the Lemma 3.8
quenched bound `1/2` holds at every `w ∈ W` (radius `r/100`, scale `s₀`). Then from every vertex whose cell meets
`∂B_r(z)` the walk follows a polar template itinerary with probability at least `2^{-⌈11600/s₀⌉}`. -/
theorem waypointProof_itinerary_lower_bound {E : Type*} (G : LFMultigraph ℤ E) {o : ℤ}
    (H : CellularEmbedding G o) (hloop : ∀ e : E, G.src e ≠ G.tgt e)
    (z : ℂ) {r s₀ d ρ : ℝ} (W : Finset ℂ)
    (hr : 0 < r) (hs₀ : 0 < s₀) (hs₀le : s₀ ≤ 1 / 10) (hd : d ≤ s₀ * r / 100)
    (hdiam : ∀ v, (H.cell v ∩ closedBall (0 : ℂ) ρ).Nonempty → diam (H.cell v) ≤ d)
    (hcover : ∀ y, 0.85 * r ≤ ‖y - z‖ → ‖y - z‖ ≤ 1.15 * r →
      ∃ w ∈ W, ‖w - y‖ ≤ s₀ * r / 200)
    (hWball : ∀ w ∈ W, ball w (r / 100) ⊆ ball (0 : ℂ) ρ)
    (hzball : ball z (2 * r) ⊆ ball (0 : ℂ) ρ)
    (hgood : ∀ w ∈ W, ∀ v ∈ verticesMeeting H.cell (ball w (4 * s₀ * (r / 100))),
      ENNReal.ofReal (1 / 2 : ℝ) ≤
        G.walkLaw v {ξ | HitsBefore H.cell w s₀ (r / 100) (G.vertexPath ξ)})
    (x : ℤ) (hx : x ∈ verticesMeeting H.cell (sphere z r)) :
    ENNReal.ofReal ((2 : ℝ) ^ (-(⌈11600 / s₀⌉ : ℤ))) ≤
      G.walkLaw x {ξ | PolarTemplateItinerary H z r (G.vertexPath ξ)} := by
  classical
  have := GoodScales.countable_state G
  obtain ⟨y₀, hy₀cell, hy₀sphere⟩ := hx
  have hy₀z : ‖y₀ - z‖ = r := by simpa [mem_sphere, dist_eq_norm] using hy₀sphere
  set ϑ := Complex.arg (y₀ - z) with hϑ
  set m : ℕ := ⌈11600 / s₀⌉₊ with hmdef
  have hmge : (11600 / s₀ : ℝ) ≤ m := Nat.le_ceil _
  have hm116 : (116000 : ℝ) ≤ 11600 / s₀ := by
    rw [le_div_iff₀ hs₀]
    nlinarith
  have hmposR : (0 : ℝ) < m := by linarith
  have hm50 : 50 ≤ m := by
    have h : (50 : ℝ) ≤ m := by linarith
    exact_mod_cast h
  have hsm : 11600 ≤ s₀ * m := by
    have h := hmge
    rw [div_le_iff₀ hs₀] at h
    linarith
  have hmvar : 29 * r / (m : ℝ) ≤ s₀ * r / 100 / 4 := by
    rw [div_le_iff₀ hmposR]
    nlinarith
  have hvar1 : 29 * r * (1 / (m : ℝ)) ≤ s₀ * r / 400 := by
    have h : 29 * r * (1 / (m : ℝ)) = 29 * r / m := by ring
    rw [h]
    linarith
  set Tm := CellularEmbedding.movedTemplate z r ϑ with hTm
  have hT0 : Tm 0 = y₀ := waypointProof_movedTemplate_zero hy₀z
  have hex : ∀ i : ℕ, ∃ w ∈ W, ‖w - Tm ((i : ℝ) / m)‖ ≤ s₀ * r / 200 := by
    intro i
    have hb := waypointProof_movedTemplate_norm_bounds z hr.le ϑ ((i : ℝ) / m)
    refine hcover _ ?_ ?_
    · have h : (0.85 : ℝ) = 17 / 20 := by norm_num
      rw [h]
      linarith [hb.1]
    · have h : (1.15 : ℝ) = 23 / 20 := by norm_num
      rw [h]
      linarith [hb.2]
  choose wp hwpW hwpnear using hex
  set R := r / 100 with hRdef
  have hR : 0 < R := by positivity
  have hd' : d ≤ s₀ * R := by
    have h : s₀ * R = s₀ * r / 100 := by rw [hRdef]; ring
    rw [h]
    exact hd
  have hlip_step : ∀ i : ℕ, ‖Tm ((i : ℝ) / m) - Tm (((i + 1 : ℕ) : ℝ) / m)‖ ≤ s₀ * r / 400 := by
    intro i
    have hlip := waypointProof_movedTemplate_lipschitz z hr.le ϑ ((i : ℝ) / m)
      (((i + 1 : ℕ) : ℝ) / m)
    have hdiff : |(i : ℝ) / m - ((i + 1 : ℕ) : ℝ) / m| = 1 / m := by
      rw [abs_sub_comm]
      push_cast
      rw [abs_of_nonneg (by
        rw [← sub_div]
        exact div_nonneg (by linarith) hmposR.le)]
      ring
    rw [hdiff] at hlip
    exact hlip.trans hvar1
  have hspacing : ∀ i : ℕ, ‖wp i - wp (i + 1)‖ ≤ (5 / 4) * (s₀ * R) := by
    intro i
    have h1 := hwpnear i
    have h2 := hwpnear (i + 1)
    have h3 := hlip_step i
    have htri : ‖wp i - wp (i + 1)‖ ≤ ‖wp i - Tm ((i : ℝ) / m)‖ +
        ‖Tm ((i : ℝ) / m) - Tm (((i + 1 : ℕ) : ℝ) / m)‖ +
        ‖wp (i + 1) - Tm (((i + 1 : ℕ) : ℝ) / m)‖ := by
      calc
        ‖wp i - wp (i + 1)‖ = ‖(wp i - Tm ((i : ℝ) / m)) +
            (Tm ((i : ℝ) / m) - Tm (((i + 1 : ℕ) : ℝ) / m)) -
            (wp (i + 1) - Tm (((i + 1 : ℕ) : ℝ) / m))‖ := by congr 1; ring
        _ ≤ ‖(wp i - Tm ((i : ℝ) / m)) + (Tm ((i : ℝ) / m) - Tm (((i + 1 : ℕ) : ℝ) / m))‖ +
            ‖wp (i + 1) - Tm (((i + 1 : ℕ) : ℝ) / m)‖ := norm_sub_le _ _
        _ ≤ _ := by
          have := norm_add_le (wp i - Tm ((i : ℝ) / m))
            (Tm ((i : ℝ) / m) - Tm (((i + 1 : ℕ) : ℝ) / m))
          linarith
    have hR' : s₀ * R = s₀ * r / 100 := by rw [hRdef]; ring
    rw [hR']
    linarith
  have hwpstep : ∀ i, ‖wp (i + 1) - wp (i + 1 + 1)‖ ≤ (5 / 4) * (s₀ * R) :=
    fun i => hspacing (i + 1)
  have hwpball : ∀ i, ball (wp (i + 1)) R ⊆ ball (0 : ℂ) ρ := fun i => hWball _ (hwpW _)
  have hwpnear' : ∀ i, 1 ≤ i → i ≤ m →
      ‖wp i - CellularEmbedding.movedTemplate z r ϑ ((i : ℝ) / m)‖ ≤ s₀ * r / 100 / 2 := by
    intro i _ _
    have h := hwpnear i
    linarith
  have hy₀ρ : y₀ ∈ ball (0 : ℂ) ρ := by
    apply hzball
    rw [mem_ball, dist_eq_norm, hy₀z]
    linarith
  have hdiamx := hdiam x ⟨y₀, hy₀cell, ball_subset_closedBall hy₀ρ⟩
  have hstart : ∀ q ∈ H.cell x, ‖q - CellularEmbedding.movedTemplate z r ϑ 0‖ < r / 60 := by
    intro q hq
    change ‖q - Tm 0‖ < r / 60
    rw [hT0]
    have hqy := (Metric.dist_le_diam_of_mem (H.isCompact_cell x).isBounded hq hy₀cell).trans hdiamx
    rw [dist_eq_norm] at hqy
    nlinarith
  have hx0 : (Sum.inl x : G.State) ∈ waypointProofEntrance G H.cell wp s₀ R 0 := by
    refine ⟨y₀, hy₀cell, ?_⟩
    have hlip := waypointProof_movedTemplate_lipschitz z hr.le ϑ 0 (((0 + 1 : ℕ) : ℝ) / m)
    have hdiff : |(0 : ℝ) - ((0 + 1 : ℕ) : ℝ) / m| = 1 / m := by
      push_cast
      rw [zero_sub, abs_neg, abs_of_nonneg (div_nonneg zero_le_one hmposR.le)]
    rw [hdiff] at hlip
    have h1 := hwpnear (0 + 1)
    have htri := norm_sub_le_norm_sub_add_norm_sub y₀ (Tm (((0 + 1 : ℕ) : ℝ) / m)) (wp (0 + 1))
    have hT0' : ‖y₀ - Tm (((0 + 1 : ℕ) : ℝ) / m)‖ ≤ 29 * r * (1 / m) := by
      rw [← hT0]
      exact hlip
    have hR' : 4 * s₀ * R = 4 * s₀ * r / 100 := by rw [hRdef]; ring
    rw [mem_ball, dist_eq_norm, hR']
    rw [norm_sub_rev (wp (0 + 1))] at h1
    nlinarith
  have hBfinite : ∀ n ω, ω ∈ waypointProofEvent G H.cell wp s₀ R n →
      waypointProofStep G H.cell wp s₀ R n ω < ⊤ := fun n ω hω =>
    waypointProofTime_lt_top (lt_of_lt_of_le hω.1 le_top)
  have hBentry : ∀ n ω, ω ∈ waypointProofEvent G H.cell wp s₀ R n →
      stopState (waypointProofStep G H.cell wp s₀ R n) ω ∈
        waypointProofEntrance G H.cell wp s₀ R (n + 1) := fun n ω hω =>
    waypointProof_entry G H hR hs₀ hs₀le hd' hdiam (hwpball n) (hwpstep n) hω
  have hprob : ∀ n y, y ∈ waypointProofEntrance G H.cell wp s₀ R n →
      (fun _ : ℕ => ENNReal.ofReal (1 / 2 : ℝ)) n ≤
        chainLaw G.walkKernel y (waypointProofEvent G H.cell wp s₀ R n) := fun n y hy =>
    waypointProof_event_prob G H wp s₀ R n y (hgood (wp (n + 1)) (hwpW _) (G.stateVertex y) hy)
  have hiter := iteratedStrongMarkovLower G.walkKernel (Sum.inl x : G.State)
    (waypointProofStep G H.cell wp s₀ R) (waypointProofEvent G H.cell wp s₀ R)
    (waypointProofEntrance G H.cell wp s₀ R) (fun _ => ENNReal.ofReal (1 / 2 : ℝ)) hx0
    (waypointProof_isStoppingTime G H.cell wp s₀ R) (waypointProof_event_measurable G H.cell wp s₀ R)
    hBfinite hBentry hprob m
  have hae := waypoint_walkLaw_ae_adj hloop x
  have hnull : G.walkLaw x
      {ξ : ℕ → G.State | ∀ j, G.adj.Adj (G.vertexPath ξ j) (G.vertexPath ξ (j + 1))}ᶜ = 0 := by
    rw [ae_iff] at hae
    simpa only [Set.compl_ofPred] using hae
  have hsub : iteratedSuccessPrefix (Sum.inl x : G.State) (waypointProofStep G H.cell wp s₀ R)
        (waypointProofEvent G H.cell wp s₀ R) m ∩
        {ξ : ℕ → G.State | ∀ j, G.adj.Adj (G.vertexPath ξ j) (G.vertexPath ξ (j + 1))} ⊆
      {ξ | PolarTemplateItinerary H z r (G.vertexPath ξ)} := by
    rintro ξ ⟨hξ, hadj⟩
    exact waypointProof_itinerary_of_prefix G H z wp hr hs₀ hs₀le hd' hdiam hwpball hwpstep hwpnear'
      hm50 hmvar hstart hx0 hξ hadj
  have hceil : ((m : ℕ) : ℤ) = ⌈11600 / s₀⌉ := Int.natCast_ceil_eq_ceil (by positivity)
  have hpow : ENNReal.ofReal ((2 : ℝ) ^ (-(⌈11600 / s₀⌉ : ℤ))) =
      ∏ _i ∈ Finset.range m, ENNReal.ofReal (1 / 2 : ℝ) := by
    rw [Finset.prod_const, Finset.card_range, ← hceil, zpow_neg, zpow_natCast, ← inv_pow,
      ← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2), one_div]
  calc
    ENNReal.ofReal ((2 : ℝ) ^ (-(⌈11600 / s₀⌉ : ℤ))) =
        ∏ _i ∈ Finset.range m, ENNReal.ofReal (1 / 2 : ℝ) := hpow
    _ ≤ chainLaw G.walkKernel (Sum.inl x : G.State)
        (iteratedSuccessPrefix (Sum.inl x : G.State) (waypointProofStep G H.cell wp s₀ R)
          (waypointProofEvent G H.cell wp s₀ R) m) := hiter
    _ = G.walkLaw x (iteratedSuccessPrefix (Sum.inl x : G.State)
          (waypointProofStep G H.cell wp s₀ R) (waypointProofEvent G H.cell wp s₀ R) m ∩
        {ξ : ℕ → G.State | ∀ j, G.adj.Adj (G.vertexPath ξ j) (G.vertexPath ξ (j + 1))}) :=
      (measure_inter_conull hnull).symm
    _ ≤ G.walkLaw x {ξ | PolarTemplateItinerary H z r (G.vertexPath ξ)} := measure_mono hsub

/-! ### The corrected waypoint input -/

/-- A scale `s₀ ∈ (0, 1/10]` with `A₈/√(log s₀⁻¹) ≤ 1/2` exists for every real `A₈`. -/
theorem waypointProof_exists_scale (A₈ : ℝ) :
    ∃ s₀ : ℝ, 0 < s₀ ∧ s₀ ≤ 1 / 10 ∧ A₈ / Real.sqrt (Real.log s₀⁻¹) ≤ 1 / 2 := by
  set s₀ := min (1 / 10 : ℝ) (Real.exp (-(4 * A₈ ^ 2 + 1))) with hs₀def
  have hs₀ : 0 < s₀ := lt_min (by norm_num) (Real.exp_pos _)
  refine ⟨s₀, hs₀, min_le_left _ _, ?_⟩
  have hlog : Real.log s₀ ≤ -(4 * A₈ ^ 2 + 1) := by
    have h := Real.log_le_log hs₀ (min_le_right (1 / 10 : ℝ) (Real.exp (-(4 * A₈ ^ 2 + 1))))
    rwa [Real.log_exp] at h
  set L := Real.log s₀⁻¹ with hL
  have hL1 : 4 * A₈ ^ 2 + 1 ≤ L := by
    rw [hL, Real.log_inv]
    linarith
  have hLpos : 0 < L := by nlinarith [sq_nonneg A₈]
  have hsqrt_pos : 0 < Real.sqrt L := Real.sqrt_pos.mpr hLpos
  have habs : 2 * |A₈| ≤ Real.sqrt L := by
    apply Real.le_sqrt_of_sq_le
    have : (2 * |A₈|) ^ 2 = 4 * A₈ ^ 2 := by rw [mul_pow, sq_abs]; ring
    rw [this]
    linarith
  rw [div_le_iff₀ hsqrt_pos]
  have := le_abs_self A₈
  linarith

/-- The mesh `2^{-k}` is positive. -/
theorem waypointProof_mesh_pos (k : ℕ) : 0 < mesh k := by
  unfold mesh
  positivity

/-- **`WaypointStrongMarkovInputFixed2` holds** for every random cell family (the waypoint argument Proposition 3.6′ and
§4.5, the waypoint proof). The two graph premises of the interface are not needed beyond the
pathwise looplessness assumed in its final clause. -/
theorem waypointStrongMarkovInputFixed2_holds (F : RandomCellFamily) (q ρ : ℝ) :
    WaypointStrongMarkovInputFixed2 F q ρ := by
  intro _hConnected _hLoopless β₈ A₈ hβ₈ hq
  obtain ⟨s₀, hs₀, hs₀le, hA⟩ := waypointProof_exists_scale A₈
  have hmin : 0 < min β₈ q := lt_min hβ₈ hq
  refine ⟨s₀, min β₈ q / 2, hs₀, hs₀le, by positivity, ?_, ?_, hA, ?_⟩
  · have := min_le_left β₈ q
    linarith
  · have := min_le_right β₈ q
    linarith
  intro k z r h1 h2 h3 _h4 h5
  have hr : 0 < r := by
    have hpos : 0 < mesh k ^ β₈ := Real.rpow_pos_of_pos (waypointProof_mesh_pos k) β₈
    linarith
  obtain ⟨W, hcard, hann, hcover, hWball⟩ := waypoint_fixed2_environment_net z hr hs₀ hs₀le h5
  refine ⟨W, hcard, hann, hcover, hWball, ?_⟩
  intro ω _hconn hloop hdiam hL38 x hx
  exact waypointProof_itinerary_lower_bound (F.G k ω) (F.H k ω) hloop z W hr hs₀ hs₀le h3 hdiam
    hcover hWball h5
    (fun w hw v hv => waypoint_lemma38_half F k ω w r s₀ β₈ A₈ (hL38 w hw) h2 hs₀le hA v hv) x hx

end MatedCRTHarmonic.CellFamily
