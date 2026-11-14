/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistTerminalGood at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistTerminal
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistAllScalesEvent

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.WhiteNoise LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_terminal_of_good {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (W : WNSpace → Ω → ℝ)
    (ξ : Ioi (0 : ℝ)) (Q ζ C : ℝ) (n : ℕ)
    (F : ℕ → Finset ℂ) (V U : Set ℂ) (R T : ℝ) (t : ℕ → ℝ)
    (hR : 1 ≤ R) (ω : Ω)
    (hgood : ω ∈ ptDistAllScalesGood P W ξ Q ζ C n F V R T t)
    (z x v : ℂ)
    (hz : z ∈ V)
    (hx : dist z x < ((2 : ℝ)⁻¹ ^ n) / 4)
    (hv : v ∈ sphere x (((2 : ℝ)⁻¹ ^ n) / 4))
    (hVball : closedBall z ((2 : ℝ)⁻¹ ^ n) ⊆ V)
    (hUball : closedBall z ((2 : ℝ)⁻¹ ^ n) ⊆ U) :
    lfppDOn (ξ : ℝ) (fun y => phiMN W P 0 n y ω) U z v ≤
      ENNReal.ofReal (Real.exp ((ξ : ℝ) *
        (phiMN W P 0 n z ω + R * t n)) * (((2 : ℝ)⁻¹ ^ n) / 2)) := by
  let r : ℝ := ((2 : ℝ)⁻¹) ^ n
  have hr : 0 < r := by dsimp [r]; positivity
  have hosc : ∀ y ∈ closedBall z r,
      |phiMN W P 0 n y ω - phiMN W P 0 n z ω| ≤ R * t n := by
    intro y hy
    have hyV : y ∈ V := hVball hy
    have hdist : dist y z ≤ R * ((2 : ℝ) ^ n)⁻¹ := by
      have hpow : ((2 : ℝ) ^ n)⁻¹ = r := by dsimp [r]; rw [inv_pow]
      rw [hpow]
      have h : dist y z ≤ r := by simpa only [dist_comm] using (mem_closedBall.mp hy)
      nlinarith
    exact (hgood n (Finset.mem_range.mpr (Nat.lt_succ_self n))).2 y hyV z hz hdist
  exact pt_dist_terminal_to_crossing (ξ : ℝ) ξ.2.le
    (fun y => phiMN W P 0 n y ω) U z x v r (R * t n)
    hr hx hv hUball hosc

end SupercriticalLQGUniqueness.B2.DG20Pt
