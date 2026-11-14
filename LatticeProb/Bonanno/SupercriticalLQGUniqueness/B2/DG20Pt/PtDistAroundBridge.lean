/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistAroundBridge at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.Inputs
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Pt.PtDistLoopMeet

 




set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 



theorem lfppDOn_le_of_hasAroundLoop {ξ : ℝ} {f : ℂ → ℝ}
    {U : Set ℂ} {x w : ℂ} {r : ℝ} (hr : 0 < r)
    (hxw : dist x w ≤ 3 * r) {L : ℝ≥0∞}
    (hshort : Inputs.HasAroundLoop ξ f x r hr L)
    (hball : ball x (8 * r) ⊆ U)
    (p q : ℝ → ℂ)
    (hp : IsPiecewiseC1Path p (p 0) (p 1))
    (hq : IsPiecewiseC1Path q (q 0) (q 1))
    (hpU : ∀ t ∈ Icc (0 : ℝ) 1, p t ∈ U)
    (hqU : ∀ t ∈ Icc (0 : ℝ) 1, q t ∈ U)
    (hp0 : dist (p 0) x ≤ r / 4) (hp1 : 16 * r ≤ dist (p 1) x)
    (hq0 : dist (q 0) w ≤ r / 4) (hq1 : 16 * r ≤ dist (q 1) w) :
    lfppDOn ξ f U (p 0) (q 0) ≤ lfppLen ξ f p + L + lfppLen ξ f q := by
  obtain ⟨γ, a, b, hγ, hann, hsep, hlen⟩ := hshort
  have hγ' : IsPiecewiseC1Path γ (γ 0) (γ 1) := by
    rw [hγ.source, hγ.target]
    exact hγ
  have hγU : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U := by
    intro t ht
    have h := hann t ht
    change γ t ∈ ball x (8 * r) \ closure (ball x (4 * r)) at h
    exact hball h.1
  have hsep' : LQGMetric.Disconnects (γ '' Icc (0 : ℝ) 1)
      (sphere x (4 * r)) (sphere x (8 * r)) := hsep
  calc
    lfppDOn ξ f U (p 0) (q 0) ≤
        lfppLen ξ f p + lfppLen ξ f γ + lfppLen ξ f q :=
      lfppDOn_le_of_around_loop hr hxw p γ q hp hγ' hq hpU hγU hqU hsep'
        hp0 hp1 hq0 hq1
    _ ≤ lfppLen ξ f p + L + lfppLen ξ f q := by
      gcongr

 

theorem lfppDOn_le_adjacent_of_hasAroundLoop {ξ : ℝ} {f : ℂ → ℝ}
    {U : Set ℂ} {x y : ℂ} {r : ℝ} (hr : 0 < r)
    (hxy : dist x y ≤ 3 * r / 4) {L : ℝ≥0∞}
    (hshort : Inputs.HasAroundLoop ξ f x r hr L)
    (hball : ball x (8 * r) ⊆ U)
    (p q : ℝ → ℂ)
    (hp : IsPiecewiseC1Path p (p 0) (p 1))
    (hq : IsPiecewiseC1Path q (q 0) (q 1))
    (hpU : ∀ t ∈ Icc (0 : ℝ) 1, p t ∈ U)
    (hqU : ∀ t ∈ Icc (0 : ℝ) 1, q t ∈ U)
    (hp0 : dist (p 0) x ≤ r / 4) (hp1 : 16 * r ≤ dist (p 1) x)
    (hq0 : dist (q 0) y ≤ r / 2) (hq1 : 32 * r ≤ dist (q 1) y) :
    lfppDOn ξ f U (p 0) (q 0) ≤ lfppLen ξ f p + L + lfppLen ξ f q := by
  obtain ⟨γ, a, b, hγ, hann, hsep, hlen⟩ := hshort
  have hγ' : IsPiecewiseC1Path γ (γ 0) (γ 1) := by
    rw [hγ.source, hγ.target]
    exact hγ
  have hγU : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ U := by
    intro t ht
    have h := hann t ht
    change γ t ∈ ball x (8 * r) \ closure (ball x (4 * r)) at h
    exact hball h.1
  have hsep' : LQGMetric.Disconnects (γ '' Icc (0 : ℝ) 1)
      (sphere x (4 * r)) (sphere x (8 * r)) := hsep
  calc
    lfppDOn ξ f U (p 0) (q 0) ≤
        lfppLen ξ f p + lfppLen ξ f γ + lfppLen ξ f q :=
      lfppDOn_le_adjacent_crossings_loop hr hxy p γ q hp hγ' hq
        hpU hγU hqU hsep' hp0 hp1 hq0 hq1
    _ ≤ lfppLen ξ f p + L + lfppLen ξ f q := by
      gcongr

end SupercriticalLQGUniqueness.B2.DG20Pt
