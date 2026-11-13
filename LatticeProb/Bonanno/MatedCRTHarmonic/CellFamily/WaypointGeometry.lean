/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.CellFamily.WaypointGeometry at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.Interfaces
import LatticeProb.Bonanno.MatedCRTHarmonic.Markov.StrongMarkov

/-!
# Deterministic geometry for the scaled-grid estimate waypoint construction

This module records the cell-level confinement argument used between successive waypoint hits. A connected
cell cannot pass from the inside of a circle to its outside without meeting the circle; the walk event excludes
such a meeting.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.CellFamily

open MatedCRTHarmonic.Markov

/-- A successful inner-before-outer hit has avoided the outer target at every time through the
inner hitting time. This is the pathwise premise used to confine the connected union of visited
cells to the waypoint disk. -/
theorem waypoint_hitBefore_avoids_outer
    {S : Type*} {A B : Set S} {X : ℕ → S} {n : ℕ}
    (hsuccess : hitTime A X < hitTime B X)
    (hinner : hitTime A X = n) :
    ∀ j ≤ n, X j ∉ B := by
  apply coe_lt_hitTime_iff.mp
  rw [← hinner]
  exact hsuccess

/-- The event that a target is hit before a disjoint outer target is visible at the inner hit time,
and hence at the later time `max 1 τ_inner`. This supplies the stopped-event measurability needed by the
iterated strong-Markov lemma while ensuring every waypoint segment advances at least one step. -/
theorem waypoint_hitBefore_measurableAt_max_one
    {S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S]
    {A B : Set S} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    MeasurableSet[(isStoppingTime_hitTime hA).measurableSpace]
      {ω : ℕ → S | hitTime A ω < hitTime B ω} := by
  have hglobal : MeasurableSet {ω : ℕ → S | hitTime A ω < hitTime B ω} := by
    have hEq (n : ℕ) : MeasurableSet {ω : ℕ → S | hitTime A ω = n} :=
      measurableSet_of_measurableSet_piLE (measurableSet_hitTime_eq_coe_piLE hA n)
    have hAfter (n : ℕ) : MeasurableSet {ω : ℕ → S | (n : ℕ∞) < hitTime B ω} := by
      have heq : {ω : ℕ → S | (n : ℕ∞) < hitTime B ω} =
          ⋂ j, ⋂ (_ : j ≤ n), (fun ω : ℕ → S => ω j) ⁻¹' Bᶜ := by
        ext ω
        simp [coe_lt_hitTime_iff]
      rw [heq]
      exact MeasurableSet.iInter fun j => MeasurableSet.iInter fun hj =>
        measurable_pi_apply j hB.compl
    have hdecomp : {ω : ℕ → S | hitTime A ω < hitTime B ω} =
        ⋃ n : ℕ, {ω | hitTime A ω = n} ∩ {ω | (n : ℕ∞) < hitTime B ω} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · intro hlt
        have hfin : hitTime A ω ≠ ⊤ := ne_top_of_lt (lt_of_lt_of_le hlt le_top)
        obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
        refine ⟨n, hn.symm, ?_⟩
        simpa [hn] using hlt
      · rintro ⟨n, hn, hlt⟩
        exact lt_of_eq_of_lt hn hlt
    rw [hdecomp]
    exact MeasurableSet.iUnion fun n : ℕ => (hEq n).inter (hAfter n)
  apply measurableSet_stopping_of_forall_eq (isStoppingTime_hitTime hA) hglobal
  intro ω ω' hfinite hagree hsuccess
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (lt_top_iff_ne_top.mp hfinite)
  have htimeA : hitTime A ω = n := hn.symm
  have htimeA' : hitTime A ω' = n :=
    eq_of_isStoppingTime_of_forall_eq (isStoppingTime_hitTime hA) htimeA
      (fun j hj => hagree j (by rw [htimeA]; exact_mod_cast hj))
  have hsuccess' : (n : ℕ∞) < hitTime B ω := by
    rw [← htimeA]
    exact hsuccess
  have havoid := (coe_lt_hitTime_iff.mp hsuccess')
  have havoid' : ∀ j ≤ n, ω' j ∉ B := by
    intro j hj hjB
    have hsame := hagree j (by rw [htimeA]; exact_mod_cast hj)
    exact havoid j hj (hsame ▸ hjB)
  have hsuccess'' : (n : ℕ∞) < hitTime B ω' := coe_lt_hitTime_iff.mpr havoid'
  change hitTime A ω' < hitTime B ω'
  rw [htimeA']
  exact hsuccess''

private theorem waypoint_norm_le_diam {E : Type*} {G : LFMultigraph ℤ E} {o : ℤ}
    (H : CellularEmbedding G o) {v : ℤ} {d : ℝ}
    (hdiam : Metric.diam (H.cell v) ≤ d) {a b : ℂ}
    (ha : a ∈ H.cell v) (hb : b ∈ H.cell v) : ‖a - b‖ ≤ d := by
  have h := (Metric.dist_le_diam_of_mem (H.isCompact_cell v).isBounded ha hb).trans hdiam
  simpa [dist_eq_norm] using h

/-- A connected cell with an interior point and no point on the boundary circle lies inside that circle. -/
theorem waypoint_connected_cell_subset_ball_of_avoiding_sphere
    {S : Set ℂ} {z : ℂ} {R : ℝ} (hconn : IsConnected S)
    (hinside : ∃ x ∈ S, ‖x - z‖ < R)
    (havoid : Disjoint S (sphere z R)) : S ⊆ ball z R := by
  intro y hy
  rw [mem_ball, dist_eq_norm]
  by_contra hnot
  have hR : R ≤ ‖y - z‖ := le_of_not_gt hnot
  obtain ⟨x, hxS, hxR⟩ := hinside
  have hcont : ContinuousOn (fun w : ℂ => ‖w - z‖) S := by fun_prop
  have hcross := hconn.isPreconnected.intermediate_value hxS hy hcont ⟨le_of_lt hxR, hR⟩
  obtain ⟨q, hqS, hq⟩ := hcross
  have hqsphere : q ∈ sphere z R := by
    rw [mem_sphere, dist_eq_norm]
    simpa [hq, norm_sub_rev] using (show ‖q - z‖ = R from hq)
  exact (Set.disjoint_left.mp havoid) hqS hqsphere

/-- A diameter estimate transfers a distance bound from one point of a cell to all its points. -/
theorem waypoint_cell_subset_ball_of_diam
    {E : Type*} {G : LFMultigraph ℤ E} {o : ℤ} (H : CellularEmbedding G o)
    {v : ℤ} {z : ℂ} {d a R : ℝ}
    (hdiam : Metric.diam (H.cell v) ≤ d) (x : ℂ) (hx : x ∈ H.cell v)
    (hnear : ‖x - z‖ ≤ a) (hbound : d + a < R) : H.cell v ⊆ ball z R := by
  intro y hy
  rw [mem_ball, dist_eq_norm]
  have hxy := waypoint_norm_le_diam H hdiam hx hy
  have htri := norm_sub_le_norm_sub_add_norm_sub y x z
  have hrev : ‖y - x‖ ≤ d := by simpa [norm_sub_rev] using hxy
  linarith

/-- A confined first cell propagates confinement along a finite adjacent cell segment as long as no visited cell
meets the boundary sphere. Connectedness of each cell prevents a single step from crossing that boundary unseen. -/
theorem waypoint_segment_confined_of_avoiding_sphere
    {E : Type*} {G : LFMultigraph ℤ E} {o : ℤ} (H : CellularEmbedding G o)
    (z : ℂ) (R r₀ d ρ : ℝ) (X : ℕ → ℤ) (N : ℕ)
    (hstep : ∀ j < N, G.adj.Adj (X j) (X (j + 1)))
    (hstart : ∃ q ∈ H.cell (X 0), ‖q - z‖ < 4 * r₀)
    (hdiam : ∀ v, (H.cell v ∩ closedBall (0 : ℂ) ρ).Nonempty → diam (H.cell v) ≤ d)
    (hstartIn : ball z (4 * r₀) ⊆ ball (0 : ℂ) ρ)
    (hballIn : ball z R ⊆ ball (0 : ℂ) ρ)
    (hsmall : 4 * r₀ + d < R)
    (hno : ∀ j ≤ N, X j ∉ verticesMeeting H.cell (sphere z R)) :
    ∀ j ≤ N, H.cell (X j) ⊆ ball z R := by
  intro j hj
  induction j with
  | zero =>
      obtain ⟨q, hqcell, hqdist⟩ := hstart
      have hqball : q ∈ ball z (4 * r₀) := by simpa [Metric.mem_ball, dist_eq_norm] using hqdist
      have hqρ : q ∈ ball (0 : ℂ) ρ := hstartIn hqball
      have hdm := hdiam (X 0) ⟨q, hqcell, ball_subset_closedBall hqρ⟩
      have hqnear : ‖q - z‖ ≤ 4 * r₀ := le_of_lt hqdist
      have hbound : d + 4 * r₀ < R := by nlinarith [hsmall]
      exact waypoint_cell_subset_ball_of_diam H hdm q hqcell hqnear hbound
  | succ j ih =>
      have hjlt : j < N := by omega
      have hprev := ih (by omega)
      obtain ⟨q, hqprev, hqnext⟩ := H.inter_of_adj _ _ (hstep j hjlt)
      have hqball : q ∈ ball z R := hprev hqprev
      have hqρ : q ∈ ball (0 : ℂ) ρ := hballIn hqball
      have havoid : Disjoint (H.cell (X (j + 1))) (sphere z R) := by
        apply Set.disjoint_left.mpr
        intro u huCell huSphere
        exact hno (j + 1) (by omega) ⟨u, huCell, huSphere⟩
      exact waypoint_connected_cell_subset_ball_of_avoiding_sphere
        (H.isConnected_cell (X (j + 1))) ⟨q, hqnext, by
          simpa [Metric.mem_ball, dist_eq_norm] using hqball⟩ havoid

/-- The first waypoint boundary time not earlier than a given vertex index. -/
noncomputable def waypointStage (τ : ℕ → ℕ) (m j : ℕ) (hj : j ≤ τ m) : ℕ :=
  Nat.find (p := fun i => j ≤ τ i) ⟨m, hj⟩

theorem waypointStage_spec (τ : ℕ → ℕ) (m j : ℕ) (hj : j ≤ τ m) :
    j ≤ τ (waypointStage τ m j hj) := Nat.find_spec (p := fun i => j ≤ τ i) ⟨m, hj⟩

theorem waypointStage_le (τ : ℕ → ℕ) (m j : ℕ) (hj : j ≤ τ m) :
    waypointStage τ m j hj ≤ m := Nat.find_le hj

theorem waypointStage_mono (τ : ℕ → ℕ) (m j j' : ℕ)
    (hj : j ≤ τ m) (hj' : j' ≤ τ m) (hjj' : j ≤ j') :
    waypointStage τ m j hj ≤ waypointStage τ m j' hj' := by
  apply Nat.find_le
  exact hjj'.trans (waypointStage_spec τ m j' hj')

theorem waypointStage_zero (τ : ℕ → ℕ) (m : ℕ) (hτ0 : τ 0 = 0) :
    waypointStage τ m 0 (Nat.zero_le _) = 0 := by
  apply Nat.le_antisymm
  · apply Nat.find_le
    rw [hτ0]
  · exact Nat.zero_le _

theorem waypointStage_succ_gap (τ : ℕ → ℕ) (m j : ℕ) (hj : j + 1 ≤ τ m)
    (hτ : ∀ i, τ i < τ (i + 1)) :
    waypointStage τ m (j + 1) hj ≤ waypointStage τ m j (Nat.le_trans (Nat.le_succ j) hj) + 1 := by
  let a := waypointStage τ m j (Nat.le_trans (Nat.le_succ j) hj)
  let b := waypointStage τ m (j + 1) hj
  have hmono : StrictMono τ := strictMono_nat_of_lt_succ hτ
  have hab : a ≤ b := by
    apply Nat.find_le
    exact (Nat.le_succ j).trans (waypointStage_spec τ m (j + 1) hj)
  by_contra hbad
  have hba : a + 2 ≤ b := by omega
  have hbpos : 0 < b := by omega
  have hbm : b - 1 < b := by omega
  have hmin : ¬ j + 1 ≤ τ (b - 1) :=
    Nat.find_min (⟨m, hj⟩ : ∃ i, j + 1 ≤ τ i) hbm
  have hτlt : τ (b - 1) < j + 1 := by
    by_contra hnot
    exact hmin (Nat.le_of_not_gt hnot)
  have halower : j ≤ τ a := waypointStage_spec τ m j (Nat.le_trans (Nat.le_succ j) hj)
  have hab' : a < b - 1 := by omega
  have htimes : τ a < τ (b - 1) := hmono hab'
  omega

/-- Stage index, clamped to the terminal index so it is defined on every vertex time. -/
noncomputable def waypointStageWithin (τ : ℕ → ℕ) (m n : ℕ) (hn : τ m = n) (j : ℕ) : ℕ :=
  waypointStage τ m (min j n) (by rw [hn]; exact Nat.min_le_right j n)

/-- Turn nonempty, strictly advancing waypoint segments into the `RouteM.IsTemplateWalk` interval data.
The parameter stays at the current waypoint between segment endpoints and advances by one mesh interval at
each endpoint; the endpoint cell is close to both adjacent template pieces. -/
theorem waypoint_isTemplateWalk_of_stage_confinement
    {E : Type*} {G : LFMultigraph ℤ E} {o : ℤ} (H : CellularEmbedding G o)
    (z : ℂ) (r ϑ r₀ : ℝ) (X : ℕ → ℤ) (m n : ℕ) (τ : ℕ → ℕ) (w : ℕ → ℂ)
    (hr : 0 < r) (hr₀ : 0 ≤ r₀) (hr₀small : r₀ ≤ r / 1000)
    (hm : 50 ≤ m) (hmpos : 0 < m) (hmvariation : 29 * r / (m : ℝ) ≤ r₀ / 4)
    (hτ0 : τ 0 = 0) (hτstrict : ∀ i, τ i < τ (i + 1)) (hn : τ m = n)
    (hadj : ∀ j < n, G.adj.Adj (X j) (X (j + 1)))
    (hstart : ∀ q ∈ H.cell (X 0),
      ‖q - CellularEmbedding.movedTemplate z r ϑ 0‖ < r / 60)
    (hconf : ∀ j ≤ n, 0 < waypointStageWithin τ m n hn j →
      H.cell (X j) ⊆ ball (w (waypointStageWithin τ m n hn j)) (r / 100))
    (hwapprox : ∀ i, 1 ≤ i → i ≤ m →
      ‖w i - CellularEmbedding.movedTemplate z r ϑ ((i : ℝ) / m)‖ ≤ r₀ / 2)
    (hLip : ∀ s t, s ∈ Set.Icc (0 : ℝ) 1 → t ∈ Set.Icc (0 : ℝ) 1 →
      ‖CellularEmbedding.movedTemplate z r ϑ s -
        CellularEmbedding.movedTemplate z r ϑ t‖ ≤ 29 * r * |s - t|) :
    RouteM.IsTemplateWalk H z r ϑ n X
      (fun j => if j = 0 then 0 else
        ((waypointStageWithin τ m n hn (j - 1) : ℕ) : ℝ) / m)
      (fun j => ((waypointStageWithin τ m n hn j : ℕ) : ℝ) / m) := by
  classical
  let stage : ℕ → ℕ := fun j => waypointStageWithin τ m n hn j
  let p : ℕ → ℝ := fun j => (stage j : ℝ) / m
  let α : ℕ → ℝ := fun j => if j = 0 then 0 else p (j - 1)
  let β : ℕ → ℝ := p
  have hstage0 : stage 0 = 0 := by
    simpa [stage, waypointStageWithin] using waypointStage_zero τ m hτ0
  have hstageLe (j : ℕ) : stage j ≤ m := by
    dsimp [stage]
    exact waypointStage_le τ m (min j n) (by rw [hn]; exact Nat.min_le_right _ _)
  have hstageMono : Monotone stage := by
    intro a b hab
    dsimp [stage, waypointStageWithin]
    exact waypointStage_mono τ m (min a n) (min b n)
      (by rw [hn]; exact Nat.min_le_right _ _) (by rw [hn]; exact Nat.min_le_right _ _)
      (min_le_min_right _ hab)
  have hpMono : Monotone p := by
    intro a b hab
    dsimp [p]
    exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (hstageMono hab)) (by positivity)
  have hstageGap (j : ℕ) (hj : j < n) : stage (j + 1) ≤ stage j + 1 := by
    have hjn : j + 1 ≤ n := Nat.succ_le_of_lt hj
    have hleft : stage (j + 1) = waypointStage τ m (j + 1)
        (by rw [hn]; exact hjn) := by
      simp [stage, waypointStageWithin, Nat.min_eq_left hjn]
    have hright : stage j = waypointStage τ m j (by rw [hn]; exact Nat.le_of_lt hj) := by
      simp [stage, waypointStageWithin, Nat.min_eq_left (Nat.le_of_lt hj)]
    rw [hleft, hright]
    have hjn' : j + 1 ≤ τ m := by simpa [hn] using hjn
    exact waypointStage_succ_gap τ m j hjn' hτstrict
  have hp0 : p 0 = 0 := by simp [p, hstage0]
  have hα0 : α 0 = 0 := by simp [α]
  have hβn : β n = 1 := by
    have hstageN : stage n = m := by
      have hspec : n ≤ τ (stage n) := by
        simpa [stage, waypointStageWithin] using
          (waypointStage_spec τ m (min n n)
            (by rw [hn]; exact Nat.min_le_right _ _))
      have hle : stage n ≤ m := hstageLe n
      by_contra hneq
      have hlt : stage n < m := by omega
      have hstrict := (strictMono_nat_of_lt_succ hτstrict) hlt
      omega
    dsimp [β, p]
    rw [hstageN]
    field_simp [show (m : ℝ) ≠ 0 by exact_mod_cast hmpos.ne']
  have hαmono : Monotone α := by
    intro a b hab
    by_cases ha : a = 0
    · subst a
      by_cases hb : b = 0
      · simp [α, hb]
      · simp only [α, hb, ↓reduceIte]
        have hbpos : 0 < b := Nat.pos_of_ne_zero hb
        have hidx : b - 1 ≤ b := Nat.sub_le _ _
        have : p 0 ≤ p (b - 1) := hpMono (by omega)
        simpa [hp0] using this
    · by_cases hb : b = 0
      · subst b
        exact False.elim (ha (Nat.eq_zero_of_le_zero hab))
      · simp only [α, ha, hb, ↓reduceIte]
        exact hpMono (Nat.sub_le_sub_right hab 1)
  have hβmono : Monotone β := hpMono
  have hov : ∀ j < n, α (j + 1) ≤ β j := by
    intro j hj
    simp [α, β, Nat.succ_ne_zero]
  have hparamBounds : ∀ j ≤ n, 0 ≤ α j ∧ α j ≤ β j ∧ β j ≤ 1 ∧ β j - α j ≤ 1 / 50 := by
    intro j hj
    by_cases hj0 : j = 0
    · subst j
      simp only [α, β, hα0, hp0]
      constructor <;> norm_num
    · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
      have hidx : j - 1 + 1 = j := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hj0)
      have hgap : stage j ≤ stage (j - 1) + 1 := by
        have := hstageGap (j - 1) (by omega)
        simpa [hidx] using this
      have hmon : stage (j - 1) ≤ stage j := hstageMono (Nat.sub_le j 1)
      have hstagele : stage j ≤ m := hstageLe j
      have hstagemon : 0 ≤ (stage (j - 1) : ℝ) ∧ (stage j : ℝ) ≤ (m : ℝ) := by
        exact ⟨Nat.cast_nonneg _, Nat.cast_le.mpr hstagele⟩
      have hmreal : (50 : ℝ) ≤ m := by exact_mod_cast hm
      have hwidth : ((stage j : ℝ) / m) - ((stage (j - 1) : ℝ) / m) ≤ 1 / 50 := by
        have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
        rw [div_sub_div_same]
        apply (div_le_iff₀ hmR).2
        have hdiff : (stage j : ℝ) - stage (j - 1) ≤ 1 := by exact_mod_cast (by omega : stage j - stage (j - 1) ≤ 1)
        nlinarith
      simp only [α, β, hj0, ↓reduceIte]
      refine ⟨div_nonneg (by positivity) (by positivity), ?_, ?_, ?_⟩
      · exact div_le_div_of_nonneg_right (Nat.cast_le.mpr hmon) (by positivity)
      · exact div_le_one_of_le₀ (Nat.cast_le.mpr hstagele) (by positivity)
      · exact hwidth
  have hnear : ∀ j ≤ n, ∀ s ∈ Set.Icc (α j) (β j), ∀ q ∈ H.cell (X j),
      ‖q - CellularEmbedding.movedTemplate z r ϑ s‖ < r / 60 := by
    intro j hj s hs q hq
    by_cases hj0 : j = 0
    · subst j
      have hs0 : s = 0 := by simpa [α, β, hp0] using hs
      simpa [hs0] using hstart q hq
    · have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
      let i := stage j
      have hi0 : 0 < i := by
        by_contra hi
        have hi' : i = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_not_gt hi)
        have hspec : j ≤ τ i := by
          simpa [i, stage, waypointStageWithin, Nat.min_eq_left hj] using
            waypointStage_spec τ m j (by rw [hn]; exact hj)
        rw [hi', hτ0] at hspec
        omega
      have him : i ≤ m := hstageLe j
      have hidx : j - 1 + 1 = j := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hj0)
      have hgap : i ≤ stage (j - 1) + 1 := by
        have := hstageGap (j - 1) (by omega)
        simpa [i, hidx] using this
      have hprev : stage (j - 1) ≤ i := by
        dsimp [i]
        exact hstageMono (Nat.sub_le j 1)
      have hparamlo : ((i : ℝ) - 1) / m ≤ s := by
        have hslo : (stage (j - 1) : ℝ) / m ≤ s := by
          simpa [α, hj0, p] using hs.1
        have hcastNat : i - 1 ≤ stage (j - 1) := by omega
        have hcastSub : (i : ℝ) - 1 = ((i - 1 : ℕ) : ℝ) := by
          rw [Nat.cast_sub (by omega : 1 ≤ i)]
          norm_num
        have hcast : (i : ℝ) - 1 ≤ (stage (j - 1) : ℝ) := by
          rw [hcastSub]
          exact_mod_cast hcastNat
        have hmR : (0 : ℝ) ≤ m := by positivity
        calc
          ((i : ℝ) - 1) / m ≤ (stage (j - 1) : ℝ) / m := div_le_div_of_nonneg_right hcast hmR
          _ ≤ s := hslo
      have hparamhi : s ≤ (i : ℝ) / m := by
        simpa [i, β, p, stage] using hs.2
      have hti : (i : ℝ) / m ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · positivity
        · exact div_le_one_of_le₀ (Nat.cast_le.mpr him) (by positivity)
      have hsrange : s ∈ Set.Icc (0 : ℝ) 1 := by
        exact ⟨(hparamBounds j hj).1.trans hs.1, le_trans hs.2 (hparamBounds j hj).2.2.1⟩
      have hclose := hwapprox i hi0 him
      have hlip := hLip ((i : ℝ) / m) s hti hsrange
      have hdiff : |(i : ℝ) / m - s| ≤ 1 / m := by
        rw [abs_of_nonneg (by linarith : 0 ≤ (i : ℝ) / m - s)]
        have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
        have hnum : (i : ℝ) - m * s ≤ 1 := by
          have hhi := (le_div_iff₀ hmR).1 hparamhi
          have hlo := (div_le_iff₀ hmR).1 hparamlo
          nlinarith [hhi, hlo]
        have heq : (i : ℝ) / m - s = ((i : ℝ) - m * s) / m := by field_simp
        rw [heq]
        apply (div_le_iff₀ hmR).2
        have hcancel : (1 : ℝ) / (m : ℝ) * (m : ℝ) = 1 := by
          field_simp [ne_of_gt hmR]
        nlinarith [hcancel]
      have hvar : ‖CellularEmbedding.movedTemplate z r ϑ ((i : ℝ) / m) -
          CellularEmbedding.movedTemplate z r ϑ s‖ ≤ r₀ / 4 := by
        calc
          _ ≤ 29 * r * |(i : ℝ) / m - s| := hlip
          _ ≤ 29 * r * (1 / m) := mul_le_mul_of_nonneg_left hdiff (by positivity)
          _ = 29 * r / (m : ℝ) := by ring
          _ ≤ r₀ / 4 := hmvariation
      have hcell := hconf j hj (by simpa [i, stage] using hi0) hq
      have hqwi : ‖q - w i‖ < r / 100 := by
        simpa [Metric.mem_ball, dist_eq_norm] using hcell
      have htriangle : ‖q - CellularEmbedding.movedTemplate z r ϑ s‖ ≤
          ‖q - w i‖ + ‖w i - CellularEmbedding.movedTemplate z r ϑ ((i : ℝ) / m)‖ +
            ‖CellularEmbedding.movedTemplate z r ϑ ((i : ℝ) / m) -
              CellularEmbedding.movedTemplate z r ϑ s‖ := by
        calc
          _ = ‖(q - w i) + (w i - CellularEmbedding.movedTemplate z r ϑ ((i : ℝ) / m)) +
              (CellularEmbedding.movedTemplate z r ϑ ((i : ℝ) / m) -
                CellularEmbedding.movedTemplate z r ϑ s)‖ := by congr 1 <;> abel
          _ ≤ ‖(q - w i) + (w i - CellularEmbedding.movedTemplate z r ϑ ((i : ℝ) / m))‖ +
              ‖CellularEmbedding.movedTemplate z r ϑ ((i : ℝ) / m) -
                CellularEmbedding.movedTemplate z r ϑ s‖ := norm_add_le _ _
          _ ≤ ‖q - w i‖ + ‖w i - CellularEmbedding.movedTemplate z r ϑ ((i : ℝ) / m)‖ +
              ‖CellularEmbedding.movedTemplate z r ϑ ((i : ℝ) / m) -
                CellularEmbedding.movedTemplate z r ϑ s‖ := by
            have := norm_add_le (q - w i)
              (w i - CellularEmbedding.movedTemplate z r ϑ ((i : ℝ) / m))
            linarith
      have hr0' : r₀ ≤ r / 1000 := hr₀small
      have hsum : ‖q - w i‖ + ‖w i - CellularEmbedding.movedTemplate z r ϑ ((i : ℝ) / m)‖ +
          ‖CellularEmbedding.movedTemplate z r ϑ ((i : ℝ) / m) -
            CellularEmbedding.movedTemplate z r ϑ s‖ < r / 100 + 3 * r₀ / 4 := by
        linarith [hqwi, hclose, hvar]
      exact lt_of_le_of_lt htriangle (by nlinarith [hr, hr0'])
  exact ⟨hadj, hα0, hβn, hαmono, hβmono, hov, hparamBounds, hnear⟩

private theorem waypoint_mem_annulus_iff {z w : ℂ} {a b : ℝ} :
    w ∈ annulus z a b ↔ a ≤ ‖w - z‖ ∧ ‖w - z‖ < b := by
  rw [annulus, Set.mem_sdiff, mem_ball, mem_ball, dist_eq_norm, not_lt]
  exact and_comm

/-- The `RouteM.IsTemplateWalk` data and the full strict-adjacency path give the itinerary record used by the scaled-grid estimate. -/
theorem waypoint_polarTemplateItinerary_of_templateWalk
    {E : Type*} {G : LFMultigraph ℤ E} {o : ℤ} (H : CellularEmbedding G o)
    (z : ℂ) (r : ℝ) (X : ℕ → ℤ)
    (hr : 0 < r) {n : ℕ} {ϑ : ℝ} {α β : ℕ → ℝ}
    (hW : RouteM.IsTemplateWalk H z r ϑ n X α β)
    (hadj : ∀ j, G.adj.Adj (X j) (X (j + 1))) :
    PolarTemplateItinerary H z r X := by
  refine ⟨n, ϑ, α, β, hW, ?_, hadj⟩
  intro j hj w hw
  rw [waypoint_mem_annulus_iff]
  have hcoord := hW.coord_annulus hr hj hw
  have hnorm := RouteM.norm_tmplCoord hr z ϑ w
  constructor
  ·
    have hmul := mul_lt_mul_of_pos_right hcoord.1 hr
    rw [hnorm, div_mul_cancel₀ _ (ne_of_gt hr)] at hmul
    nlinarith
  ·
    have hmul := mul_lt_mul_of_pos_right hcoord.2 hr
    rw [hnorm, div_mul_cancel₀ _ (ne_of_gt hr)] at hmul
    nlinarith

end MatedCRTHarmonic.CellFamily

