/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistChainOffset at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistChain

 


set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_selected_crossing_chain_offset {ξ : ℝ} {f : ℂ → ℝ}
    {U : Set ℂ} (k₀ N : ℕ) (x : ℕ → ℂ) (p : ℕ → ℝ → ℂ)
    (L : ℕ → ℝ≥0∞)
    (hcross : ∀ j ≤ N,
      AdmPath U (sphere (x (k₀ + j)) (((2 : ℝ)⁻¹ ^ (k₀ + j)) / 4))
        (sphere (x (k₀ + j)) (16 * ((2 : ℝ)⁻¹ ^ (k₀ + j)))) (p (k₀ + j)))
    (hnear : ∀ j < N,
      dist (x (k₀ + (j + 1))) (x (k₀ + j)) ≤
        3 * ((2 : ℝ)⁻¹ ^ (k₀ + (j + 1))) / 4)
    (hloop : ∀ j < N,
      Inputs.HasAroundLoop ξ f (x (k₀ + (j + 1)))
        ((2 : ℝ)⁻¹ ^ (k₀ + (j + 1))) (by positivity) (L j))
    (hball : ∀ j < N,
      ball (x (k₀ + (j + 1)))
        (8 * ((2 : ℝ)⁻¹ ^ (k₀ + (j + 1)))) ⊆ U) :
    lfppDOn ξ f U (p k₀ 0) (p (k₀ + N) 0) ≤
      ∑ j ∈ Finset.range N,
        (lfppLen ξ f (p (k₀ + (j + 1))) + L j +
          lfppLen ξ f (p (k₀ + j))) := by
  have hfirst : p k₀ 0 ∈ U := by
    obtain ⟨_, _, _, _, _, hU⟩ := hcross 0 (Nat.zero_le N)
    simpa only [Nat.add_zero] using hU 0 (by norm_num)
  apply pt_dist_chain_edges (fun j => p (k₀ + j) 0)
    (fun j => lfppLen ξ f (p (k₀ + (j + 1))) + L j +
      lfppLen ξ f (p (k₀ + j))) N hfirst
  intro j hj
  let k : ℕ := k₀ + j
  let r : ℝ := (2 : ℝ)⁻¹ ^ (k + 1)
  have hr : 0 < r := by dsimp [r]; positivity
  have hscale : ((2 : ℝ)⁻¹) ^ k = 2 * r := by
    dsimp [r]
    rw [pow_succ]
    ring
  have hcoarse := hcross j (by omega)
  have hfine := hcross (j + 1) (by omega)
  obtain ⟨a, ha, b, hb, hq, hqU⟩ := hcoarse
  obtain ⟨c, hc, d, hd, hp, hpU⟩ := hfine
  have hkfine : k₀ + (j + 1) = k + 1 := by dsimp [k]; omega
  have hp0 : dist (p (k₀ + (j + 1)) 0) (x (k₀ + (j + 1))) ≤ r / 4 := by
    rw [hp.source]
    rw [hkfine] at hc
    exact (mem_sphere.mp hc).le
  have hp1 : 16 * r ≤ dist (p (k₀ + (j + 1)) 1) (x (k₀ + (j + 1))) := by
    rw [hp.target]
    rw [hkfine] at hd
    exact (mem_sphere.mp hd).ge
  have hq0 : dist (p (k₀ + j) 0) (x (k₀ + j)) ≤ r / 2 := by
    rw [hq.source]
    simpa only [show k₀ + j = k by rfl, hscale,
      show 2 * r / 4 = r / 2 by ring] using (mem_sphere.mp ha).le
  have hq1 : 32 * r ≤ dist (p (k₀ + j) 1) (x (k₀ + j)) := by
    rw [hq.target]
    simpa only [show k₀ + j = k by rfl, hscale,
      show 16 * (2 * r) = 32 * r by ring] using (mem_sphere.mp hb).ge
  have hp' : IsPiecewiseC1Path (p (k₀ + (j + 1)))
      (p (k₀ + (j + 1)) 0) (p (k₀ + (j + 1)) 1) := by
    rw [hp.source, hp.target]
    exact hp
  have hq' : IsPiecewiseC1Path (p (k₀ + j))
      (p (k₀ + j) 0) (p (k₀ + j) 1) := by
    rw [hq.source, hq.target]
    exact hq
  have h := lfppDOn_le_adjacent_of_hasAroundLoop hr (hnear j hj)
    (hloop j hj) (hball j hj) (p (k₀ + (j + 1))) (p (k₀ + j))
    hp' hq' hpU hqU hp0 hp1 hq0 hq1
  rw [lfppDOn_comm] at h
  exact h

end SupercriticalLQGUniqueness.B2.DG20Pt
