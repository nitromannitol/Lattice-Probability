import LatticeProb.Bonanno.BouRabeeGwynne.SelectedExcursionOscillation

/-! # Oscillation of clocked walk excursions with bounded steps

A clocked excursion of the walk on a finite conductance network, stopped at the exit
of a set `B` of vertices whose positions lie in a ball of radius `r`, stays in the
`(r + s)`-ball about its centre whenever the steps before exit have length at most `s`.
Its oscillation is therefore at most `2 r + s`. -/
set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped unitInterval ENNReal

namespace BouRabeeGwynne

variable {d : ℕ} {V : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]

set_option linter.unusedSectionVars false in
/-- The polygonal interpolation up to time `m` lies in a convex set containing the
first `m + 1` vertices. -/
lemma polygonalCurve_mem_of_convex_of_le (pos : V → Euc d) (ω : ℕ → V)
    {S : Set (Euc d)} (hS : Convex ℝ S) (m : ℕ) (hpos : ∀ k ≤ m, pos (ω k) ∈ S)
    (t : unitInterval) : polygonalCurve pos ω m t ∈ S := by
  cases m with
  | zero => simpa only [polygonalCurve_zero, ContinuousMap.const_apply] using hpos 0 le_rfl
  | succ m =>
    obtain ⟨i, hlo, hhi⟩ := (TimePartition.uniform m).exists_interval t
    have hl : (i.val : ℝ) / ((m + 1 : ℕ) : ℝ) ≤ (t : ℝ) := hlo
    have hu : (t : ℝ) ≤ ((i.val + 1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) := hhi
    have hu' : (t : ℝ) ≤ ((i.val : ℝ) + 1) / ((m + 1 : ℕ) : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hu
    have hi := i.isLt
    rw [polygonalCurve_on_segment pos ω i.isLt t hl hu']
    apply hS.add_smul_sub_mem (hpos i.val (by omega)) (hpos (i.val + 1) (by omega))
    have hm : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    have hl' := (div_le_iff₀ hm).mp hl
    have hu'' := (le_div_iff₀ hm).mp hu'
    constructor <;> nlinarith

namespace FiniteConductanceNetwork

/-- The clocked excursion from `v` out of `B` has oscillation at most `2 r + s` almost
surely, if the positions of the vertices of `B` and of `v` lie in the ball of radius `r`
about `c`, and almost surely every step taken before the exit time has length at most `s`. -/
theorem clockedWalkExcursionKernel_ae_curveOscillationLe_of_steps
    (N : FiniteConductanceNetwork V) (pos : V → Euc d) (B : Set V)
    (hB : ∀ v ∈ B, 0 < N.totalConductance v) (v : V) {c : Euc d} {r s : ℝ} (hs : 0 ≤ s)
    (hBpos : ∀ w ∈ B, pos w ∈ ball c r) (hv : pos v ∈ ball c r)
    (hstep : ∀ᵐ ω ∂N.trajectoryLaw B hB v, ∀ j : ℕ,
      (j : WithTop ℕ) < exitTime B ω → dist (pos (ω (j + 1))) (pos (ω j)) ≤ s) :
    ∀ᵐ e ∂N.clockedWalkExcursionKernel pos B hB v,
      ClockedWalkExcursion.curve e ∈ curveOscillationLe (2 * r + s) := by
  have hm : MeasurableSet {e : ClockedWalkExcursion d |
      ClockedWalkExcursion.curve e ∈ curveOscillationLe (2 * r + s)} :=
    ClockedWalkExcursion.measurable_curve (measurableSet_curveOscillationLe _)
  change ∀ᵐ e ∂((N.trajectoryLaw B hB v).map (ClockedWalkExcursion.ofWalk pos B)), _
  rw [ae_map_iff (ClockedWalkExcursion.measurable_ofWalk pos B).aemeasurable hm]
  filter_upwards [hstep, N.trajectoryLaw_ae_start B hB v] with ω hω h0
  have hball : ∀ x ∈ ball c r, x ∈ closedBall c (r + s) := fun x hx =>
    mem_closedBall.mpr ((mem_ball.mp hx).le.trans (by linarith))
  have hstart : ClockedWalkExcursion.curve (ClockedWalkExcursion.ofWalk pos B ω) 0 ∈
      closedBall c r := by
    rw [ClockedWalkExcursion.curve_start]
    simp only [ClockedWalkExcursion.start_ofWalk, h0]
    exact mem_closedBall.mpr (mem_ball.mp hv).le
  have hvert : ∀ k ≤ (exitTime B ω).untopD 0, pos (ω k) ∈ closedBall c (r + s) := by
    intro k hk
    cases hx : exitTime B ω using WithTop.recTopCoe with
    | top =>
      simp only [hx, WithTop.untopD_top] at hk
      have : k = 0 := by omega
      subst this
      rw [h0]; exact hball _ hv
    | coe m' =>
      simp only [hx, WithTop.untopD_coe] at hk
      have hlt : ∀ j : ℕ, j < m' → pos (ω j) ∈ ball c r := fun j hj =>
        hBpos _ (mem_of_lt_exitTime (by rw [hx]; exact WithTop.coe_lt_coe.mpr hj))
      rcases Nat.lt_or_ge k m' with hk' | hk'
      · exact hball _ (hlt k hk')
      · have hkm : k = m' := le_antisymm hk hk'
        subst hkm
        rcases Nat.eq_zero_or_pos k with h00 | hpos0
        · subst h00; rw [h0]; exact hball _ hv
        · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
          have h1 := hω j (by rw [hx]; exact WithTop.coe_lt_coe.mpr (Nat.lt_succ_self j))
          have h2 := mem_ball.mp (hlt j (Nat.lt_succ_self j))
          rw [mem_closedBall]
          calc dist (pos (ω (j + 1))) c
              ≤ dist (pos (ω (j + 1))) (pos (ω j)) + dist (pos (ω j)) c := dist_triangle _ _ _
            _ ≤ r + s := by linarith
  have hrange : ∀ t, ClockedWalkExcursion.curve (ClockedWalkExcursion.ofWalk pos B ω) t ∈
      closedBall c (r + s) := by
    intro t
    rw [ClockedWalkExcursion.curve_ofWalk]
    exact polygonalCurve_mem_of_convex_of_le pos ω (convex_closedBall c (r + s)) _ hvert t
  have h := mem_curveOscillationLe_of_closedBall hrange hstart
  have hsum : r + s + r = 2 * r + s := by ring
  rw [hsum] at h
  exact h

end FiniteConductanceNetwork
end BouRabeeGwynne
