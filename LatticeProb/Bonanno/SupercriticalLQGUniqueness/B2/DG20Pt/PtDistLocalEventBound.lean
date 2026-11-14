/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistLocalEventBound at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistCentralBridge
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistTerminalGood
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistTwoArm

 



set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_local_selected_site_bound {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (ξ : Ioi (0 : ℝ)) (Q ζ C : ℝ) (n k₀ : ℕ) (hk₀ : k₀ ≤ n)
    (F : ℕ → Finset ℂ) (V U : Set ℂ) (R T : ℝ) (t : ℕ → ℝ)
    (hR : 1 ≤ R) (hT : 0 < T) (ω : Ω)
    (hgood : ω ∈ ptDistAllScalesGood P W ξ Q ζ C n F V R T t)
    (hinside : ∀ k ≤ n, ∀ x ∈ F k, x ∈ V)
    (hcover : ∀ k ≤ n, ∀ v ∈ V, ∃ x ∈ F k,
      dist v x < ((2 : ℝ)⁻¹) ^ (k + 2))
    (z w : ℂ) (hz : z ∈ V) (hw : w ∈ V)
    (hzw : dist z w ≤ 2 * ((2 : ℝ)⁻¹ ^ k₀))
    (hcollarZ : ∀ k, k₀ ≤ k → ∀ x : ℂ,
      dist z x < ((2 : ℝ)⁻¹) ^ k / 4 →
      ball x (17 * ((2 : ℝ)⁻¹ ^ k)) ⊆ U)
    (hcollarW : ∀ k, k₀ ≤ k → ∀ x : ℂ,
      dist w x < ((2 : ℝ)⁻¹) ^ k / 4 →
      ball x (17 * ((2 : ℝ)⁻¹ ^ k)) ⊆ U)
    (hVballZ : closedBall z ((2 : ℝ)⁻¹ ^ n) ⊆ V)
    (hVballW : closedBall w ((2 : ℝ)⁻¹ ^ n) ⊆ V)
    (hUballZ : closedBall z ((2 : ℝ)⁻¹ ^ n) ⊆ U)
    (hUballW : closedBall w ((2 : ℝ)⁻¹ ^ n) ⊆ U) :
    let b (x : ℕ → ℂ) (k : ℕ) : ℝ≥0∞ := ENNReal.ofReal (2 *
      (Real.exp ((ξ : ℝ) * phiMN W P 0 k (x k) ω) *
        (T * ((2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) * (k : ℝ)) * lambdaN ξ W P n))))
    let ell (x : ℕ → ℂ) (k : ℕ) : ℝ≥0∞ := ENNReal.ofReal (T * (C *
      (2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) * (k : ℝ)) * lambdaN ξ W P n) *
      Real.exp ((ξ : ℝ) * phiMN W P 0 k (x k) ω))
    let a (x : ℕ → ℂ) : ℝ≥0∞ := ∑ j ∈ Finset.range (n - k₀),
      (b x (k₀ + (j + 1)) + ell x (k₀ + (j + 1)) + b x (k₀ + j))
    let term (v : ℂ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp ((ξ : ℝ) *
      (phiMN W P 0 n v ω + R * t n)) * (((2 : ℝ)⁻¹ ^ n) / 2))
    ∃ xz xw : ℕ → ℂ,
      (∀ k ≤ n,
        |phiMN W P 0 k (xz k) ω - phiMN W P 0 k z ω| ≤ R * t k ∧
        |phiMN W P 0 k (xw k) ω - phiMN W P 0 k w ω| ≤ R * t k) ∧
      lfppDOn (ξ : ℝ) (fun y => phiMN W P 0 n y ω) U z w ≤
        term z + a xz + (b xz k₀ + ell xz k₀ + b xw k₀) +
          a xw + term w := by
  dsimp
  let f : ℂ → ℝ := fun y => phiMN W P 0 n y ω
  let b (x : ℕ → ℂ) (k : ℕ) : ℝ≥0∞ := ENNReal.ofReal (2 *
      (Real.exp ((ξ : ℝ) * phiMN W P 0 k (x k) ω) *
        (T * ((2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) * (k : ℝ)) * lambdaN ξ W P n))))
  let ell (x : ℕ → ℂ) (k : ℕ) : ℝ≥0∞ := ENNReal.ofReal (T * (C *
      (2 : ℝ) ^ (-((ξ : ℝ) * Q - ζ) * (k : ℝ)) * lambdaN ξ W P n) *
      Real.exp ((ξ : ℝ) * phiMN W P 0 k (x k) ω))
  let a (x : ℕ → ℂ) : ℝ≥0∞ := ∑ j ∈ Finset.range (n - k₀),
      (b x (k₀ + (j + 1)) + ell x (k₀ + (j + 1)) + b x (k₀ + j))
  let term (v : ℂ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp ((ξ : ℝ) *
      (phiMN W P 0 n v ω + R * t n)) * (((2 : ℝ)⁻¹ ^ n) / 2))
  obtain ⟨xz, pz, hxz, hpz, hchainz⟩ :=
    exists_pt_dist_one_arm_paths P W hW ξ Q ζ C n k₀ hk₀ F V U R T t
      (by linarith) hT ω hgood hinside hcover z hz hcollarZ
  obtain ⟨xw, pw, hxw, hpw, hchainw⟩ :=
    exists_pt_dist_one_arm_paths P W hW ξ Q ζ C n k₀ hk₀ F V U R T t
      (by linarith) hT ω hgood hinside hcover w hw hcollarW
  have hcenters : dist (xz k₀) (xw k₀) ≤
      3 * ((2 : ℝ)⁻¹ ^ k₀) :=
    pt_dist_net_centers_close (by positivity)
      (hxz k₀ hk₀).1 (hxw k₀ hk₀).1 hzw
  have hloop : Inputs.HasAroundLoop (ξ : ℝ) f (xz k₀)
      ((2 : ℝ)⁻¹ ^ k₀) (by positivity) (ell xz k₀) :=
    (hxz k₀ hk₀).2.1.2
  have hball8 : ball (xz k₀) (8 * ((2 : ℝ)⁻¹ ^ k₀)) ⊆ U := by
    intro y hy
    apply hcollarZ k₀ le_rfl (xz k₀) (hxz k₀ hk₀).1
    have hr : 0 < ((2 : ℝ)⁻¹ ^ k₀) := by positivity
    have hd : dist y (xz k₀) < 8 * ((2 : ℝ)⁻¹ ^ k₀) := mem_ball.mp hy
    exact mem_ball.mpr (by linarith)
  have hcentral := pt_dist_selected_same_scale_bridge
    (ξ := (ξ : ℝ)) (f := f) (U := U)
    (by positivity : 0 < ((2 : ℝ)⁻¹ ^ k₀)) hcenters
    (pz k₀) (pw k₀) (hpz 0 (by omega)).1
    (hpw 0 (by omega)).1 hloop hball8
  have hvz : pz n 0 ∈ sphere (xz n) (((2 : ℝ)⁻¹ ^ n) / 4) := by
    obtain ⟨u, hu, _, _, hpPath, _⟩ := (hpz (n - k₀) le_rfl).1
    rw [← hpPath.source] at hu
    simpa only [Nat.add_sub_of_le hk₀] using hu
  have hvw : pw n 0 ∈ sphere (xw n) (((2 : ℝ)⁻¹ ^ n) / 4) := by
    obtain ⟨u, hu, _, _, hpPath, _⟩ := (hpw (n - k₀) le_rfl).1
    rw [← hpPath.source] at hu
    simpa only [Nat.add_sub_of_le hk₀] using hu
  have hterminalZ := pt_dist_terminal_of_good P W ξ Q ζ C n F V U R T t hR
    ω hgood z (xz n) (pz n 0) hz (hxz n le_rfl).1
    hvz
    hVballZ hUballZ
  have hterminalW := pt_dist_terminal_of_good P W ξ Q ζ C n F V U R T t hR
    ω hgood w (xw n) (pw n 0) hw (hxw n le_rfl).1
    hvw
    hVballW hUballW
  have hZ : lfppDOn (ξ : ℝ) f U (pz n 0) (pz k₀ 0) ≤ a xz := by
    rw [lfppDOn_comm]
    calc
      _ ≤ ∑ j ∈ Finset.range (n - k₀),
        (lfppLen (ξ : ℝ) f (pz (k₀ + (j + 1))) +
          ell xz (k₀ + (j + 1)) + lfppLen (ξ : ℝ) f (pz (k₀ + j))) := by
        simpa only [f, ell] using hchainz
      _ ≤ a xz := by
        apply Finset.sum_le_sum
        intro j hj
        have hjN : j < n - k₀ := Finset.mem_range.mp hj
        exact add_le_add (add_le_add (hpz (j + 1) (by omega)).2.le le_rfl)
          (hpz j (by omega)).2.le
  have hW : lfppDOn (ξ : ℝ) f U (pw n 0) (pw k₀ 0) ≤ a xw := by
    rw [lfppDOn_comm]
    calc
      _ ≤ ∑ j ∈ Finset.range (n - k₀),
        (lfppLen (ξ : ℝ) f (pw (k₀ + (j + 1))) +
          ell xw (k₀ + (j + 1)) + lfppLen (ξ : ℝ) f (pw (k₀ + j))) := by
        simpa only [f, ell] using hchainw
      _ ≤ a xw := by
        apply Finset.sum_le_sum
        intro j hj
        have hjN : j < n - k₀ := Finset.mem_range.mp hj
        exact add_le_add (add_le_add (hpw (j + 1) (by omega)).2.le le_rfl)
          (hpw j (by omega)).2.le
  have hB : lfppDOn (ξ : ℝ) f U (pz k₀ 0) (pw k₀ 0) ≤
      b xz k₀ + ell xz k₀ + b xw k₀ :=
    hcentral.trans (add_le_add (add_le_add (hpz 0 (by omega)).2.le le_rfl)
      (hpw 0 (by omega)).2.le)
  refine ⟨xz, xw, (fun k hk => ⟨(hxz k hk).2.2, (hxw k hk).2.2⟩), ?_⟩
  exact pt_dist_join_two_arms z w (pz n 0) (pz k₀ 0) (pw n 0) (pw k₀ 0)
    (a xz) (a xw) (b xz k₀ + ell xz k₀ + b xw k₀) (term z) (term w)
    hterminalZ hZ hB hW hterminalW

end SupercriticalLQGUniqueness.B2.DG20Pt
