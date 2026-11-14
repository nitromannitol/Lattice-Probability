/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Pt.PtDistLoopMeet at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.T20EChain
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Toolkit.PlanarSeparation.PathHit

 






set_option autoImplicit false
noncomputable section

open Set Metric
open LQGMetric
open LQGMetric.DDDF
open LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.DG20Pt

 

theorem pt_dist_net_centers_close {z w x y : ℂ} {r : ℝ}
    (hr : 0 < r) (hzx : dist z x < r / 4) (hwy : dist w y < r / 4)
    (hzw : dist z w ≤ 2 * r) : dist x y ≤ 3 * r := by
  have h₁ := dist_triangle x z y
  have h₂ := dist_triangle z w y
  rw [dist_comm x z] at h₁
  linarith

 

theorem pt_dist_adjacent_net_centers_close {z x y : ℂ} {r : ℝ}
    (hzx : dist z x < r / 4) (hzy : dist z y < r / 2) :
    dist x y ≤ 3 * r / 4 := by
  have htri := dist_triangle x z y
  rw [dist_comm x z] at htri
  linarith

 

theorem annular_loop_meets_crossing {K : Set ℂ} {x : ℂ} {r : ℝ}
    (hr : 0 < r)
    (hsep : LQGMetric.Disconnects K (sphere x (4 * r)) (sphere x (8 * r)))
    (p : ℝ → ℂ) (hp : ContinuousOn p (Icc (0 : ℝ) 1))
    (hstart : dist (p 0) x ≤ 4 * r) (hend : 8 * r ≤ dist (p 1) x) :
    ∃ t ∈ Icc (0 : ℝ) 1, p t ∈ K := by
  have hpc : IsPathConnected (p '' Icc (0 : ℝ) 1) := T20E.isPathConnected_image hp
  have hin : ((p '' Icc (0 : ℝ) 1) ∩ closedBall x (4 * r)).Nonempty := by
    refine ⟨p 0, ⟨0, by norm_num, rfl⟩, ?_⟩
    exact mem_closedBall.mpr hstart
  have hout : ((p '' Icc (0 : ℝ) 1) ∩ (ball x (8 * r))ᶜ).Nonempty := by
    refine ⟨p 1, ⟨1, by norm_num, rfl⟩, ?_⟩
    exact not_lt.mpr hend
  obtain ⟨y, hyK, ⟨t, ht, rfl⟩⟩ :=
    Uniqueness.Toolkit.PlanarSeparation.disconnects_meets_pathConnected_crossing
      (by linarith : 4 * r ≤ 8 * r) hsep hpc hin hout
  exact ⟨t, ht, hyK⟩

 



theorem annular_loop_meets_two_crossings {K : Set ℂ} {x w : ℂ} {r : ℝ}
    (hr : 0 < r) (hxw : dist x w ≤ 3 * r)
    (hsep : LQGMetric.Disconnects K (sphere x (4 * r)) (sphere x (8 * r)))
    (p q : ℝ → ℂ)
    (hp : ContinuousOn p (Icc (0 : ℝ) 1))
    (hq : ContinuousOn q (Icc (0 : ℝ) 1))
    (hp0 : dist (p 0) x ≤ r / 4) (hp1 : 16 * r ≤ dist (p 1) x)
    (hq0 : dist (q 0) w ≤ r / 4) (hq1 : 16 * r ≤ dist (q 1) w) :
    (∃ s ∈ Icc (0 : ℝ) 1, p s ∈ K) ∧
      (∃ t ∈ Icc (0 : ℝ) 1, q t ∈ K) := by
  have hq0x : dist (q 0) x ≤ 4 * r := by
    have htri := dist_triangle (q 0) w x
    rw [dist_comm w x] at htri
    linarith
  have hq1x : 8 * r ≤ dist (q 1) x := by
    have htri := dist_triangle (q 1) x w
    linarith
  constructor
  · apply annular_loop_meets_crossing hr hsep p hp
    · linarith
    · linarith
  · exact annular_loop_meets_crossing hr hsep q hq hq0x hq1x

 


theorem annular_loop_meets_adjacent_crossings {K : Set ℂ} {x y : ℂ} {r : ℝ}
    (hr : 0 < r) (hxy : dist x y ≤ 3 * r / 4)
    (hsep : LQGMetric.Disconnects K (sphere x (4 * r)) (sphere x (8 * r)))
    (p q : ℝ → ℂ)
    (hp : ContinuousOn p (Icc (0 : ℝ) 1))
    (hq : ContinuousOn q (Icc (0 : ℝ) 1))
    (hp0 : dist (p 0) x ≤ r / 4) (hp1 : 16 * r ≤ dist (p 1) x)
    (hq0 : dist (q 0) y ≤ r / 2) (hq1 : 32 * r ≤ dist (q 1) y) :
    (∃ s ∈ Icc (0 : ℝ) 1, p s ∈ K) ∧
      (∃ t ∈ Icc (0 : ℝ) 1, q t ∈ K) := by
  have hq0x : dist (q 0) x ≤ 4 * r := by
    have htri := dist_triangle (q 0) y x
    rw [dist_comm y x] at htri
    linarith
  have hq1x : 8 * r ≤ dist (q 1) x := by
    have htri := dist_triangle (q 1) x y
    linarith
  constructor
  · exact annular_loop_meets_crossing hr hsep p hp (by linarith) (by linarith)
  · exact annular_loop_meets_crossing hr hsep q hq hq0x hq1x

 





theorem lfppDOn_le_crossings_add_loop {ξ : ℝ} {f : ℂ → ℝ}
    {U : Set ℂ} (p loop q : ℝ → ℂ)
    (hp : LQGMetric.IsPiecewiseC1Path p (p 0) (p 1))
    (hloop : LQGMetric.IsPiecewiseC1Path loop (loop 0) (loop 1))
    (hq : LQGMetric.IsPiecewiseC1Path q (q 0) (q 1))
    (hpU : ∀ t ∈ Icc (0 : ℝ) 1, p t ∈ U)
    (hloopU : ∀ t ∈ Icc (0 : ℝ) 1, loop t ∈ U)
    (hqU : ∀ t ∈ Icc (0 : ℝ) 1, q t ∈ U)
    {s u v t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (hu : u ∈ Icc (0 : ℝ) 1)
    (hv : v ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hpu : p s = loop u) (hqv : q t = loop v) :
    lfppDOn ξ f U (p 0) (q 0) ≤
      lfppLen ξ f p + lfppLen ξ f loop + lfppLen ξ f q := by
  have h₁ : lfppDOn ξ f U (p 0) (p s) ≤ lfppLen ξ f p :=
    dOn_pt_le hp hpU (by norm_num) hs
  have h₂ : lfppDOn ξ f U (p s) (q t) ≤ lfppLen ξ f loop := by
    rw [hpu, hqv]
    exact dOn_pt_le hloop hloopU hu hv
  have h₃ : lfppDOn ξ f U (q t) (q 0) ≤ lfppLen ξ f q :=
    dOn_pt_le hq hqU ht (by norm_num)
  calc
    lfppDOn ξ f U (p 0) (q 0) ≤
        lfppDOn ξ f U (p 0) (p s) + lfppDOn ξ f U (p s) (q 0) :=
      lfppDOn_triangle _ _ _
    _ ≤ lfppDOn ξ f U (p 0) (p s) +
        (lfppDOn ξ f U (p s) (q t) + lfppDOn ξ f U (q t) (q 0)) :=
      add_le_add le_rfl (lfppDOn_triangle _ _ _)
    _ ≤ lfppLen ξ f p + (lfppLen ξ f loop + lfppLen ξ f q) :=
      add_le_add h₁ (add_le_add h₂ h₃)
    _ = lfppLen ξ f p + lfppLen ξ f loop + lfppLen ξ f q := by
      rw [add_assoc]

 


theorem lfppDOn_le_of_around_loop {ξ : ℝ} {f : ℂ → ℝ} {U : Set ℂ}
    {x w : ℂ} {r : ℝ} (hr : 0 < r) (hxw : dist x w ≤ 3 * r)
    (p loop q : ℝ → ℂ)
    (hp : LQGMetric.IsPiecewiseC1Path p (p 0) (p 1))
    (hloop : LQGMetric.IsPiecewiseC1Path loop (loop 0) (loop 1))
    (hq : LQGMetric.IsPiecewiseC1Path q (q 0) (q 1))
    (hpU : ∀ t ∈ Icc (0 : ℝ) 1, p t ∈ U)
    (hloopU : ∀ t ∈ Icc (0 : ℝ) 1, loop t ∈ U)
    (hqU : ∀ t ∈ Icc (0 : ℝ) 1, q t ∈ U)
    (hsep : LQGMetric.Disconnects (loop '' Icc (0 : ℝ) 1)
      (sphere x (4 * r)) (sphere x (8 * r)))
    (hp0 : dist (p 0) x ≤ r / 4) (hp1 : 16 * r ≤ dist (p 1) x)
    (hq0 : dist (q 0) w ≤ r / 4) (hq1 : 16 * r ≤ dist (q 1) w) :
    lfppDOn ξ f U (p 0) (q 0) ≤
      lfppLen ξ f p + lfppLen ξ f loop + lfppLen ξ f q := by
  obtain ⟨⟨s, hs, hps⟩, ⟨t, ht, hqt⟩⟩ :=
    annular_loop_meets_two_crossings hr hxw hsep p q
      hp.continuousOn hq.continuousOn hp0 hp1 hq0 hq1
  obtain ⟨u, hu, hpu⟩ := hps
  obtain ⟨v, hv, hqv⟩ := hqt
  exact lfppDOn_le_crossings_add_loop p loop q hp hloop hq hpU hloopU hqU
    hs hu hv ht hpu.symm hqv.symm

 


theorem lfppDOn_le_adjacent_crossings_loop {ξ : ℝ} {f : ℂ → ℝ} {U : Set ℂ}
    {x y : ℂ} {r : ℝ} (hr : 0 < r) (hxy : dist x y ≤ 3 * r / 4)
    (p loop q : ℝ → ℂ)
    (hp : LQGMetric.IsPiecewiseC1Path p (p 0) (p 1))
    (hloop : LQGMetric.IsPiecewiseC1Path loop (loop 0) (loop 1))
    (hq : LQGMetric.IsPiecewiseC1Path q (q 0) (q 1))
    (hpU : ∀ t ∈ Icc (0 : ℝ) 1, p t ∈ U)
    (hloopU : ∀ t ∈ Icc (0 : ℝ) 1, loop t ∈ U)
    (hqU : ∀ t ∈ Icc (0 : ℝ) 1, q t ∈ U)
    (hsep : LQGMetric.Disconnects (loop '' Icc (0 : ℝ) 1)
      (sphere x (4 * r)) (sphere x (8 * r)))
    (hp0 : dist (p 0) x ≤ r / 4) (hp1 : 16 * r ≤ dist (p 1) x)
    (hq0 : dist (q 0) y ≤ r / 2) (hq1 : 32 * r ≤ dist (q 1) y) :
    lfppDOn ξ f U (p 0) (q 0) ≤
      lfppLen ξ f p + lfppLen ξ f loop + lfppLen ξ f q := by
  obtain ⟨⟨s, hs, hps⟩, ⟨t, ht, hqt⟩⟩ :=
    annular_loop_meets_adjacent_crossings hr hxy hsep p q
      hp.continuousOn hq.continuousOn hp0 hp1 hq0 hq1
  obtain ⟨u, hu, hpu⟩ := hps
  obtain ⟨v, hv, hqv⟩ := hqt
  exact lfppDOn_le_crossings_add_loop p loop q hp hloop hq hpU hloopU hqU
    hs hu hv ht hpu.symm hqv.symm

end SupercriticalLQGUniqueness.B2.DG20Pt
