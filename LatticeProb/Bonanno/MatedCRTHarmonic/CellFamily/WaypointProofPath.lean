/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.CellFamily.WaypointProofPath at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.WaypointGeometry
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.WaypointIteratedMarkov
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.WaypointWalk
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.WaypointProofTemplate

/-!
# Pathwise part of the scaled-grid estimate waypoint itinerary

the waypoint argument, Proposition 3.6′ (the waypoint proof) and §4.5, "Itinerary for x" and "On I" (lines 597–616).
One waypoint step restarts the edge-end walk at the previous stopping time and stops at
`max (τ_inner) 1`, the first visit to the inner circle `∂B_{s₀R}(w)` but no earlier than one transition
(so that consecutive stages strictly advance). The step succeeds when the inner circle is hit before the
outer circle `∂B_R(w)` and the first transition is a graph step.

* `waypointProof_entry`: a successful step ends in the entrance disk `B_{4s₀R}(w')` of the next waypoint
  (the waypoint argument step 1; when the inner circle is already met at time `0`, the stopped state is the next vertex,
  whose cell meets the previous small cell);
* `waypointProof_stage_confined`: on a successful step started in `B_{4s₀R}(w)`, every visited cell up to the
  stopping time lies in `B_R(w)` (the waypoint argument steps 3–4);
* restart bookkeeping for `iteratedSuccessPrefix` (finite restart times, successes, entrance states);
* `waypointProof_itinerary_of_prefix`: on the iterated success event, with strict adjacency along the whole
  path, the vertex path is a `PolarTemplateItinerary` (the waypoint construction, "On I", item 1, in the Route M form).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.CellFamily

open MatedCRTHarmonic.Markov

/-! ### Restart bookkeeping for the iterated success event -/

section Restart

variable {S : Type*} (x : S) (δ : ℕ → (ℕ → S) → ℕ∞) (B : ℕ → Set (ℕ → S))

/-- The iterated success events decrease. -/
theorem waypointProof_prefix_antitone {i n : ℕ} (hin : i ≤ n) :
    iteratedSuccessPrefix x δ B n ⊆ iteratedSuccessPrefix x δ B i := by
  induction hin with
  | refl => exact fun _ h => h
  | step _ ih =>
      intro ξ hξ
      simp only [iteratedSuccessPrefix, Set.mem_inter_iff] at hξ
      exact ih hξ.1.1

/-- The iterated success event starts at `x`. -/
theorem waypointProof_prefix_start {n : ℕ} {ξ : ℕ → S}
    (h : ξ ∈ iteratedSuccessPrefix x δ B n) : ξ 0 = x :=
  waypointProof_prefix_antitone x δ B (Nat.zero_le n) h

/-- Each of the first `n` restarted steps occurs at a finite time and succeeds. -/
theorem waypointProof_prefix_step {i n : ℕ} (hi : i < n) {ξ : ℕ → S}
    (h : ξ ∈ iteratedSuccessPrefix x δ B n) :
    iteratedRestartTime δ i ξ < ⊤ ∧ stopShift (iteratedRestartTime δ i) ξ ∈ B i := by
  have h' := waypointProof_prefix_antitone x δ B (Nat.succ_le_of_lt hi) h
  simp only [iteratedSuccessPrefix, Set.mem_inter_iff, Set.mem_preimage] at h'
  exact ⟨h'.1.2, h'.2⟩

/-- The restart times up to `n` are finite on the `n`-step success event. -/
theorem waypointProof_restart_lt_top (hBfinite : ∀ n ω, ω ∈ B n → δ n ω < ⊤) {n : ℕ}
    {ξ : ℕ → S} (h : ξ ∈ iteratedSuccessPrefix x δ B n) :
    ∀ i ≤ n, iteratedRestartTime δ i ξ < ⊤ := by
  intro i hi
  cases i with
  | zero => simp [iteratedRestartTime]
  | succ i =>
      obtain ⟨hfin, hgood⟩ := waypointProof_prefix_step x δ B (Nat.lt_of_succ_le hi) h
      exact (thenTime_lt_top_iff (σ := iteratedRestartTime δ i) (τ := δ i) (ω := ξ)).2
        ⟨hfin, hBfinite i _ hgood⟩

/-- On the `n`-step success event, the state at the `i`-th restart time is an entrance state. -/
theorem waypointProof_prefix_entry (A : ℕ → Set S) (hA0 : x ∈ A 0)
    (hBfinite : ∀ n ω, ω ∈ B n → δ n ω < ⊤)
    (hBentry : ∀ n ω, ω ∈ B n → stopState (δ n) ω ∈ A (n + 1)) {n : ℕ} {ξ : ℕ → S}
    (h : ξ ∈ iteratedSuccessPrefix x δ B n) :
    ∀ i ≤ n, stopState (iteratedRestartTime δ i) ξ ∈ A i := by
  intro i hi
  cases i with
  | zero =>
      have hstart := waypointProof_prefix_start x δ B h
      simpa [iteratedRestartTime, stopState, hstart] using hA0
  | succ i =>
      obtain ⟨hfin, hgood⟩ := waypointProof_prefix_step x δ B (Nat.lt_of_succ_le hi) h
      have hfin' : thenTime (iteratedRestartTime δ i) (δ i) ξ ≠ ⊤ :=
        lt_top_iff_ne_top.mp ((thenTime_lt_top_iff (σ := iteratedRestartTime δ i) (τ := δ i)
          (ω := ξ)).2 ⟨hfin, hBfinite i _ hgood⟩)
      change stopState (thenTime (iteratedRestartTime δ i) (δ i)) ξ ∈ A (i + 1)
      rw [stopState_thenTime hfin']
      exact hBentry i _ hgood

end Restart

/-! ### One waypoint step -/

/-- The edge-end states whose current vertex has a cell meeting `D`. -/
def waypointProofStates {E : Type*} (G : LFMultigraph ℤ E) (J : ℤ → Set ℂ) (D : Set ℂ) :
    Set G.State :=
  G.stateVertex ⁻¹' verticesMeeting J D

/-- The stopping time of one waypoint step: the first visit to the inner target, but at least one
transition. -/
def waypointProofTime {S : Type*} (A : Set S) (ξ : ℕ → S) : ℕ∞ := max (hitTime A ξ) 1

/-- The success event of one waypoint step: the inner target is visited before the outer one, and the
first transition of the vertex path is an admissible graph step. -/
def waypointProofSuccess {E : Type*} (G : LFMultigraph ℤ E) (A B : Set G.State) :
    Set (ℕ → G.State) :=
  {ξ | hitTime A ξ < hitTime B ξ} ∩
    {ξ | GoodScales.StepOK G (G.vertexPath ξ 0) (G.vertexPath ξ 1)}

theorem waypointProofTime_lt_top {S : Type*} {A : Set S} {ξ : ℕ → S} (h : hitTime A ξ < ⊤) :
    waypointProofTime A ξ < ⊤ :=
  max_lt h (by decide)

theorem one_le_waypointProofTime {S : Type*} (A : Set S) (ξ : ℕ → S) :
    1 ≤ waypointProofTime A ξ :=
  le_max_right _ _

theorem waypointProofTime_of_eq_zero {S : Type*} {A : Set S} {ξ : ℕ → S} (h : hitTime A ξ = 0) :
    waypointProofTime A ξ = ((1 : ℕ) : ℕ∞) := by
  rw [waypointProofTime, h]
  rfl

theorem waypointProofTime_of_eq_pos {S : Type*} {A : Set S} {ξ : ℕ → S} {k : ℕ} (h : hitTime A ξ = k)
    (hk : 1 ≤ k) : waypointProofTime A ξ = (k : ℕ∞) := by
  rw [waypointProofTime, h]
  exact max_eq_left (by exact_mod_cast hk)

private theorem waypointProof_norm_le_diam {E : Type*} {G : LFMultigraph ℤ E} {o : ℤ}
    (H : CellularEmbedding G o) {v : ℤ} {d : ℝ}
    (hdiam : Metric.diam (H.cell v) ≤ d) {a b : ℂ}
    (ha : a ∈ H.cell v) (hb : b ∈ H.cell v) : ‖a - b‖ ≤ d := by
  have h := (Metric.dist_le_diam_of_mem (H.isCompact_cell v).isBounded ha hb).trans hdiam
  simpa [dist_eq_norm] using h

private theorem waypointProof_mem_sphere {w p : ℂ} {a : ℝ} (hp : p ∈ sphere w a) : ‖p - w‖ = a := by
  simpa [mem_sphere, dist_eq_norm] using hp

private theorem waypointProof_mem_ball {w p : ℂ} {a : ℝ} (hp : p ∈ ball w a) : ‖p - w‖ < a := by
  simpa [mem_ball, dist_eq_norm] using hp

private theorem waypointProof_mem_ball_of {w p : ℂ} {a : ℝ} (hp : ‖p - w‖ < a) : p ∈ ball w a := by
  simpa [mem_ball, dist_eq_norm] using hp

/-- **Entrance of the next step** (the waypoint argument, step 1, with the strict-advance correction). A successful
step for the waypoint `w` stops in a state whose cell meets the next entrance disk `B_{4s₀R}(w')`, as soon as
consecutive waypoints are `1.25 s₀R` apart and cells near `w` have diameter at most `s₀R`. -/
theorem waypointProof_entry {E : Type*} (G : LFMultigraph ℤ E) {o : ℤ} (H : CellularEmbedding G o)
    {w w' : ℂ} {R s₀ d ρ : ℝ} (hR : 0 < R) (hs₀ : 0 < s₀) (hs₀le : s₀ ≤ 1 / 10)
    (hd : d ≤ s₀ * R)
    (hdiam : ∀ v, (H.cell v ∩ closedBall (0 : ℂ) ρ).Nonempty → diam (H.cell v) ≤ d)
    (hball : ball w R ⊆ ball (0 : ℂ) ρ) (hww' : ‖w - w'‖ ≤ (5 / 4) * (s₀ * R))
    {ξ : ℕ → G.State}
    (hξ : ξ ∈ waypointProofSuccess G (waypointProofStates G H.cell (sphere w (s₀ * R)))
      (waypointProofStates G H.cell (sphere w R))) :
    stopState (waypointProofTime (waypointProofStates G H.cell (sphere w (s₀ * R)))) ξ ∈
      waypointProofStates G H.cell (ball w' (4 * s₀ * R)) := by
  set Ain := waypointProofStates G H.cell (sphere w (s₀ * R)) with hAin
  obtain ⟨hsucc, hstep⟩ := hξ
  have hsucc' : hitTime Ain ξ < hitTime (waypointProofStates G H.cell (sphere w R)) ξ := hsucc
  have hfin : hitTime Ain ξ ≠ ⊤ := ne_top_of_lt hsucc'
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hfin
  have hsR : 0 < s₀ * R := mul_pos hs₀ hR
  have hkmem : ξ k ∈ Ain := (hitTime_eq_coe_iff.mp hk.symm).1
  obtain ⟨p, hpcell, hpsphere⟩ := hkmem
  have hpw : ‖p - w‖ = s₀ * R := waypointProof_mem_sphere hpsphere
  have hpw' : ‖p - w'‖ ≤ s₀ * R + (5 / 4) * (s₀ * R) := by
    have htri := norm_sub_le_norm_sub_add_norm_sub p w w'
    linarith
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    have htime : waypointProofTime Ain ξ = ((1 : ℕ) : ℕ∞) :=
      waypointProofTime_of_eq_zero hk.symm
    rw [stopState_eq_of_eq htime]
    change ((H.cell (G.vertexPath ξ 1)) ∩ ball w' (4 * s₀ * R)).Nonempty
    rcases hstep with heq | hadj
    · refine ⟨p, ?_, waypointProof_mem_ball_of (by nlinarith)⟩
      rw [heq]
      exact hpcell
    · obtain ⟨q, hq0, hq1⟩ := H.inter_of_adj _ _ hadj
      have hpρ : p ∈ ball (0 : ℂ) ρ := hball (waypointProof_mem_ball_of (by nlinarith))
      have hdm := hdiam (G.vertexPath ξ 0) ⟨p, hpcell, ball_subset_closedBall hpρ⟩
      have hqp : ‖q - p‖ ≤ d := waypointProof_norm_le_diam H hdm hq0 hpcell
      refine ⟨q, hq1, waypointProof_mem_ball_of ?_⟩
      have htri := norm_sub_le_norm_sub_add_norm_sub q p w'
      nlinarith
  · have htime : waypointProofTime Ain ξ = (k : ℕ∞) := waypointProofTime_of_eq_pos hk.symm hkpos
    rw [stopState_eq_of_eq htime]
    exact ⟨p, hpcell, waypointProof_mem_ball_of (by nlinarith)⟩

/-- **Confinement of one stage** (the waypoint argument, steps 3–4). On a successful step started in `B_{4s₀R}(w)`,
with strict adjacency along the path and cells near `w` of diameter at most `s₀R`, every cell visited up to the
stopping time lies in the open disk `B_R(w)`. -/
theorem waypointProof_stage_confined {E : Type*} (G : LFMultigraph ℤ E) {o : ℤ}
    (H : CellularEmbedding G o) {w : ℂ} {R s₀ d ρ : ℝ} (hR : 0 < R) (hs₀ : 0 < s₀)
    (hs₀le : s₀ ≤ 1 / 10) (hd : d ≤ s₀ * R)
    (hdiam : ∀ v, (H.cell v ∩ closedBall (0 : ℂ) ρ).Nonempty → diam (H.cell v) ≤ d)
    (hball : ball w R ⊆ ball (0 : ℂ) ρ) {η : ℕ → G.State}
    (hstart : η 0 ∈ waypointProofStates G H.cell (ball w (4 * s₀ * R)))
    (hη : η ∈ waypointProofSuccess G (waypointProofStates G H.cell (sphere w (s₀ * R)))
      (waypointProofStates G H.cell (sphere w R)))
    (hadj : ∀ j, G.adj.Adj (G.vertexPath η j) (G.vertexPath η (j + 1))) :
    ∀ j ≤ (waypointProofTime (waypointProofStates G H.cell (sphere w (s₀ * R))) η).toNat,
      H.cell (G.vertexPath η j) ⊆ ball w R := by
  set Ain := waypointProofStates G H.cell (sphere w (s₀ * R)) with hAin
  set Aout := waypointProofStates G H.cell (sphere w R) with hAout
  obtain ⟨hsucc, -⟩ := hη
  have hsucc' : hitTime Ain η < hitTime Aout η := hsucc
  have hfin : hitTime Ain η ≠ ⊤ := ne_top_of_lt hsucc'
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hfin
  have hsR : 0 < s₀ * R := mul_pos hs₀ hR
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    have htime : waypointProofTime Ain η = ((1 : ℕ) : ℕ∞) :=
      waypointProofTime_of_eq_zero hk.symm
    rw [htime, ENat.toNat_natCast]
    have hmem : η 0 ∈ Ain := (hitTime_eq_coe_iff.mp hk.symm).1
    obtain ⟨p, hpcell, hpsphere⟩ := hmem
    have hpw : ‖p - w‖ = s₀ * R := waypointProof_mem_sphere hpsphere
    have hpρ : p ∈ ball (0 : ℂ) ρ := hball (waypointProof_mem_ball_of (by nlinarith))
    have hdm0 := hdiam (G.vertexPath η 0) ⟨p, hpcell, ball_subset_closedBall hpρ⟩
    have hcell0 : H.cell (G.vertexPath η 0) ⊆ ball w R :=
      waypoint_cell_subset_ball_of_diam H hdm0 p hpcell (le_of_eq hpw) (by nlinarith)
    intro j hj
    rcases Nat.lt_or_ge j 1 with hj0 | hj1
    · have : j = 0 := by omega
      subst this
      exact hcell0
    · have : j = 1 := by omega
      subst this
      obtain ⟨q, hq0, hq1⟩ := H.inter_of_adj _ _ (hadj 0)
      have hqp : ‖q - p‖ ≤ d := waypointProof_norm_le_diam H hdm0 hq0 hpcell
      have hqw : ‖q - w‖ ≤ d + s₀ * R := by
        have htri := norm_sub_le_norm_sub_add_norm_sub q p w
        linarith
      have hqρ : q ∈ ball (0 : ℂ) ρ := hball (waypointProof_mem_ball_of (by nlinarith))
      have hdm1 := hdiam (G.vertexPath η 1) ⟨q, hq1, ball_subset_closedBall hqρ⟩
      exact waypoint_cell_subset_ball_of_diam H hdm1 q hq1 hqw (by nlinarith)
  · have htime : waypointProofTime Ain η = (k : ℕ∞) := waypointProofTime_of_eq_pos hk.symm hkpos
    rw [htime, ENat.toNat_natCast]
    have havoid := waypoint_hitBefore_avoids_outer hsucc' hk.symm
    obtain ⟨q, hqcell, hqball⟩ := hstart
    have hqw : ‖q - w‖ < 4 * (s₀ * R) := by
      have := waypointProof_mem_ball hqball
      linarith
    refine waypoint_segment_confined_of_avoiding_sphere H w R (s₀ * R) d ρ (G.vertexPath η) k
      (fun j _ => hadj j) ⟨q, hqcell, hqw⟩ hdiam ?_ hball (by nlinarith) havoid
    exact (ball_subset_ball (by nlinarith)).trans hball

/-! ### The iterated waypoint steps -/

/-- The stopping time of the `n`-th waypoint step, aimed at the waypoint `wp (n+1)` with inner radius
`s₀R`. -/
def waypointProofStep {E : Type*} (G : LFMultigraph ℤ E) (J : ℤ → Set ℂ) (wp : ℕ → ℂ) (s₀ R : ℝ)
    (n : ℕ) : (ℕ → G.State) → ℕ∞ :=
  waypointProofTime (waypointProofStates G J (sphere (wp (n + 1)) (s₀ * R)))

/-- The success event of the `n`-th waypoint step: inner circle `∂B_{s₀R}(wp (n+1))` before the outer circle
`∂B_R(wp (n+1))`, and an admissible first transition. -/
def waypointProofEvent {E : Type*} (G : LFMultigraph ℤ E) (J : ℤ → Set ℂ) (wp : ℕ → ℂ) (s₀ R : ℝ)
    (n : ℕ) : Set (ℕ → G.State) :=
  waypointProofSuccess G (waypointProofStates G J (sphere (wp (n + 1)) (s₀ * R)))
    (waypointProofStates G J (sphere (wp (n + 1)) R))

/-- The entrance states of the `n`-th waypoint step: cells meeting `B_{4s₀R}(wp (n+1))`. -/
def waypointProofEntrance {E : Type*} (G : LFMultigraph ℤ E) (J : ℤ → Set ℂ) (wp : ℕ → ℂ) (s₀ R : ℝ)
    (n : ℕ) : Set G.State :=
  waypointProofStates G J (ball (wp (n + 1)) (4 * s₀ * R))

/-- A stage index `i > 0` of the clamped stage map satisfies `τ (i - 1) < j ≤ τ i` and `i ≤ m`. -/
theorem waypointProof_stage_bounds (τ : ℕ → ℕ) (m n : ℕ) (hn : τ m = n) {j : ℕ} (hj : j ≤ n)
    (hpos : 0 < waypointStageWithin τ m n hn j) :
    waypointStageWithin τ m n hn j ≤ m ∧ j ≤ τ (waypointStageWithin τ m n hn j) ∧
      τ (waypointStageWithin τ m n hn j - 1) < j := by
  have hmin : min j n = j := Nat.min_eq_left hj
  have hjn : min j n ≤ τ m := by rw [hn]; exact Nat.min_le_right j n
  have hdef : waypointStageWithin τ m n hn j = waypointStage τ m (min j n) hjn := rfl
  rw [hdef] at hpos ⊢
  refine ⟨waypointStage_le τ m (min j n) hjn, ?_, ?_⟩
  · exact (le_of_eq hmin.symm).trans (waypointStage_spec τ m (min j n) hjn)
  · by_contra hcon
    have hcon' : min j n ≤ τ (waypointStage τ m (min j n) hjn - 1) :=
      (le_of_eq hmin).trans (Nat.le_of_not_lt hcon)
    have hle : waypointStage τ m (min j n) hjn ≤ waypointStage τ m (min j n) hjn - 1 := by
      unfold waypointStage
      exact Nat.find_le hcon'
    omega

/-- **The waypoint itinerary on the iterated success event** (the waypoint construction, "On I", item 1). Let the walk start at
`x`, whose cell is within `r/60` of the template start, and let the `m` waypoint steps succeed, with strict
adjacency along the whole vertex path. If consecutive waypoints are `1.25 s₀R` apart (`R = r/100`), each waypoint
is within `s₀r/200` of the template sample `T(i/m)`, the template varies by at most `s₀r/400` over each sample
interval, and cells near the waypoints have diameter at most `s₀R`, then the vertex path is a
`PolarTemplateItinerary`. -/
theorem waypointProof_itinerary_of_prefix {E : Type*} (G : LFMultigraph ℤ E) {o : ℤ}
    (H : CellularEmbedding G o) (z : ℂ) {r s₀ d ρ ϑ : ℝ} (wp : ℕ → ℂ) {m : ℕ} {x : ℤ}
    (hr : 0 < r) (hs₀ : 0 < s₀) (hs₀le : s₀ ≤ 1 / 10) (hd : d ≤ s₀ * (r / 100))
    (hdiam : ∀ v, (H.cell v ∩ closedBall (0 : ℂ) ρ).Nonempty → diam (H.cell v) ≤ d)
    (hwpball : ∀ i, ball (wp (i + 1)) (r / 100) ⊆ ball (0 : ℂ) ρ)
    (hwpstep : ∀ i, ‖wp (i + 1) - wp (i + 1 + 1)‖ ≤ (5 / 4) * (s₀ * (r / 100)))
    (hwpnear : ∀ i, 1 ≤ i → i ≤ m →
      ‖wp i - CellularEmbedding.movedTemplate z r ϑ ((i : ℝ) / m)‖ ≤ s₀ * r / 100 / 2)
    (hm : 50 ≤ m) (hmvar : 29 * r / (m : ℝ) ≤ s₀ * r / 100 / 4)
    (hstart : ∀ q ∈ H.cell x, ‖q - CellularEmbedding.movedTemplate z r ϑ 0‖ < r / 60)
    (hx0 : (Sum.inl x : G.State) ∈ waypointProofEntrance G H.cell wp s₀ (r / 100) 0)
    {ξ : ℕ → G.State}
    (hξ : ξ ∈ iteratedSuccessPrefix (Sum.inl x : G.State) (waypointProofStep G H.cell wp s₀ (r / 100))
      (waypointProofEvent G H.cell wp s₀ (r / 100)) m)
    (hadj : ∀ j, G.adj.Adj (G.vertexPath ξ j) (G.vertexPath ξ (j + 1))) :
    PolarTemplateItinerary H z r (G.vertexPath ξ) := by
  classical
  set R := r / 100 with hRdef
  have hR : 0 < R := by positivity
  set δ := waypointProofStep G H.cell wp s₀ R with hδdef
  set B := waypointProofEvent G H.cell wp s₀ R with hBdef
  set A := waypointProofEntrance G H.cell wp s₀ R with hAdef
  have hBfinite : ∀ n ω, ω ∈ B n → δ n ω < ⊤ := fun n ω hω =>
    waypointProofTime_lt_top (lt_of_lt_of_le hω.1 le_top)
  have hBentry : ∀ n ω, ω ∈ B n → stopState (δ n) ω ∈ A (n + 1) := fun n ω hω =>
    waypointProof_entry G H hR hs₀ hs₀le hd hdiam (hwpball n) (hwpstep n) hω
  have hfin := waypointProof_restart_lt_top (S := G.State) (Sum.inl x) δ B hBfinite hξ
  have hentry := waypointProof_prefix_entry (S := G.State) (Sum.inl x) δ B A hx0 hBfinite hBentry hξ
  have hξ0 : ξ 0 = Sum.inl x := waypointProof_prefix_start (S := G.State) (Sum.inl x) δ B hξ
  let T : ℕ → ℕ := fun i => (iteratedRestartTime δ i ξ).toNat
  have hTeq : ∀ i ≤ m, iteratedRestartTime δ i ξ = (T i : ℕ∞) := fun i hi =>
    (ENat.natCast_toNat (hfin i hi).ne).symm
  have hT0 : T 0 = 0 := by simp [T, iteratedRestartTime]
  have hstep : ∀ i < m, walkShift (T i) ξ ∈ B i ∧
      T (i + 1) = T i + (δ i (walkShift (T i) ξ)).toNat := by
    intro i hi
    obtain ⟨_, hgood⟩ := waypointProof_prefix_step (S := G.State) (Sum.inl x) δ B hi hξ
    have hTi := hTeq i hi.le
    rw [stopShift_eq_of_eq (τ := iteratedRestartTime δ i) hTi] at hgood
    refine ⟨hgood, ?_⟩
    have hsucc : iteratedRestartTime δ (i + 1) ξ = (T i : ℕ∞) + δ i (walkShift (T i) ξ) := by
      change thenTime (iteratedRestartTime δ i) (δ i) ξ = _
      exact thenTime_eq_of_eq hTi
    have hfinδ : δ i (walkShift (T i) ξ) ≠ ⊤ := (hBfinite i _ hgood).ne
    change (iteratedRestartTime δ (i + 1) ξ).toNat = T i + (δ i (walkShift (T i) ξ)).toNat
    rw [hsucc, ENat.toNat_add (ENat.natCast_ne_top _) hfinδ, ENat.toNat_natCast]
  have hNpos : ∀ i < m, 1 ≤ (δ i (walkShift (T i) ξ)).toNat := by
    intro i hi
    have hfinδ : δ i (walkShift (T i) ξ) ≠ ⊤ := (hBfinite i _ (hstep i hi).1).ne
    have h1 : (1 : ℕ∞) ≤ δ i (walkShift (T i) ξ) := one_le_waypointProofTime _ _
    have h2 := ENat.toNat_le_toNat h1 hfinδ
    simpa using h2
  have hconfStage : ∀ i < m, ∀ j, T i ≤ j → j ≤ T (i + 1) →
      H.cell (G.vertexPath ξ j) ⊆ ball (wp (i + 1)) R := by
    intro i hi j hj1 hj2
    obtain ⟨hgood, hTsucc⟩ := hstep i hi
    have hηstart : walkShift (T i) ξ 0 ∈ A i := by
      have h := hentry i hi.le
      rw [stopState_eq_of_eq (hTeq i hi.le)] at h
      simpa [walkShift] using h
    have hηadj : ∀ j', G.adj.Adj (G.vertexPath (walkShift (T i) ξ) j')
        (G.vertexPath (walkShift (T i) ξ) (j' + 1)) := by
      intro j'
      have h := hadj (T i + j')
      simpa [walkShift, LFMultigraph.vertexPath, Nat.add_assoc] using h
    have hconf := waypointProof_stage_confined G H hR hs₀ hs₀le hd hdiam (hwpball i) hηstart hgood
      hηadj
    have hj' : j - T i ≤ (δ i (walkShift (T i) ξ)).toNat := by omega
    have h := hconf (j - T i) hj'
    have heq : G.vertexPath (walkShift (T i) ξ) (j - T i) = G.vertexPath ξ j := by
      simp only [LFMultigraph.vertexPath, walkShift, Nat.add_sub_cancel' hj1]
    rw [heq] at h
    exact h
  let τN : ℕ → ℕ := fun i => if i ≤ m then T i else T m + (i - m)
  have hτNle : ∀ i ≤ m, τN i = T i := fun i hi => by simp [τN, hi]
  have hτN0 : τN 0 = 0 := by rw [hτNle 0 (Nat.zero_le m), hT0]
  have hτNstrict : ∀ i, τN i < τN (i + 1) := by
    intro i
    by_cases hi : i < m
    · rw [hτNle i hi.le, hτNle (i + 1) hi, (hstep i hi).2]
      have := hNpos i hi
      omega
    · have hmi : m ≤ i := Nat.le_of_not_lt hi
      have h1 : ¬ (i + 1 ≤ m) := by omega
      by_cases him : i ≤ m
      · have him' : i = m := le_antisymm him hmi
        simp only [τN, h1, him, ↓reduceIte]
        rw [him']
        omega
      · simp only [τN, h1, him, ↓reduceIte]
        omega
  have hn : τN m = T m := hτNle m le_rfl
  have hmpos : 0 < m := by omega
  have hstart' : ∀ q ∈ H.cell (G.vertexPath ξ 0),
      ‖q - CellularEmbedding.movedTemplate z r ϑ 0‖ < r / 60 := by
    intro q hq
    have hx : G.vertexPath ξ 0 = x := by
      simp only [LFMultigraph.vertexPath, hξ0]
      rfl
    rw [hx] at hq
    exact hstart q hq
  have hconf' : ∀ j ≤ T m, 0 < waypointStageWithin τN m (T m) hn j →
      H.cell (G.vertexPath ξ j) ⊆ ball (wp (waypointStageWithin τN m (T m) hn j)) (r / 100) := by
    intro j hj hpos
    obtain ⟨hle, hupper, hlower⟩ := waypointProof_stage_bounds τN m (T m) hn hj hpos
    set i₀ := waypointStageWithin τN m (T m) hn j with hi₀
    have hi : i₀ - 1 < m := by omega
    have hsucc : i₀ - 1 + 1 = i₀ := by omega
    have hlo : T (i₀ - 1) ≤ j := by
      rw [← hτNle (i₀ - 1) hi.le]
      exact hlower.le
    have hhi : j ≤ T (i₀ - 1 + 1) := by
      rw [hsucc, ← hτNle i₀ hle]
      exact hupper
    have h := hconfStage (i₀ - 1) hi j hlo hhi
    rw [hsucc] at h
    exact h
  have hLip : ∀ s t, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 →
      ‖CellularEmbedding.movedTemplate z r ϑ s - CellularEmbedding.movedTemplate z r ϑ t‖ ≤
        29 * r * |s - t| := fun s t _ _ =>
    waypointProof_movedTemplate_lipschitz z hr.le ϑ s t
  have hW := waypoint_isTemplateWalk_of_stage_confinement H z r ϑ (s₀ * r / 100) (G.vertexPath ξ)
    m (T m) τN wp hr (by positivity) (by nlinarith) hm hmpos hmvar hτN0 hτNstrict hn
    (fun j _ => hadj j) hstart' hconf' hwpnear hLip
  exact waypoint_polarTemplateItinerary_of_templateWalk H z r (G.vertexPath ξ) hr hW hadj

end MatedCRTHarmonic.CellFamily
