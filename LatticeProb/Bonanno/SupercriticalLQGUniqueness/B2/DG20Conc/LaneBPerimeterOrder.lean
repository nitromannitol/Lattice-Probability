/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneBPerimeterOrder at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneBSiteWalkMeet

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric

 

def laneBPerimeterBlock (m : ℤ) (k : ℕ) : ℤ × ℤ :=
  let n := 2 * m + 1
  let q := (k : ℤ)
  if q ≤ n then (-m - 1 + q, -m - 1)
  else if q ≤ 2 * n then (m, -m - 1 + (q - n))
  else if q ≤ 3 * n then (m - (q - 2 * n), m)
  else (-m - 1, m - (q - 3 * n))

 

theorem laneB_perimeterBlock_mem {m : ℤ} (hm : 0 ≤ m) {k : ℕ}
    (hk : (k : ℤ) ≤ 4 * (2 * m + 1)) :
    laneBPerimeterBlock m k ∈ laneBBoundaryBlocks m := by
  rw [laneB_mem_boundaryBlocks_iff]
  unfold laneBPerimeterBlock
  dsimp
  split_ifs <;> simp only [Prod.fst, Prod.snd, true_or, or_true, and_true] <;> omega

 

theorem laneB_perimeterBlock_adj {m : ℤ} (hm : 0 ≤ m) {k : ℕ}
    (hk : (k : ℤ) < 4 * (2 * m + 1)) :
    PercAdj4 (laneBPerimeterBlock m k) (laneBPerimeterBlock m (k + 1)) := by
  unfold PercAdj4 laneBPerimeterBlock
  dsimp
  split_ifs <;> simp only [Prod.fst, Prod.snd, Nat.cast_add, Nat.cast_one,
    true_and, and_true] <;> omega

 

theorem laneB_perimeterBlock_surj {m : ℤ} (hm : 0 ≤ m)
    {b : ℤ × ℤ} (hb : b ∈ laneBBoundaryBlocks m) :
    ∃ k : ℕ, (k : ℤ) ≤ 4 * (2 * m + 1) ∧ laneBPerimeterBlock m k = b := by
  obtain ⟨hxl, hxu, hyl, hyu, hside⟩ := laneB_mem_boundaryBlocks_iff.mp hb
  rcases hside with hr | hl | ht | hb
  · let q : ℤ := (2 * m + 1) + (b.2 + m + 1)
    have hq : 0 ≤ q := by dsimp [q]; omega
    refine ⟨q.toNat, ?_, ?_⟩
    · rw [Int.toNat_of_nonneg hq]
      dsimp [q]
      omega
    · have hcast : ((q.toNat : ℕ) : ℤ) = q := Int.toNat_of_nonneg hq
      simp only [laneBPerimeterBlock, hcast]
      dsimp [q]
      split_ifs <;> apply Prod.ext <;> simp only [Prod.fst, Prod.snd] <;> omega
  · let q : ℤ := 3 * (2 * m + 1) + (m - b.2)
    have hq : 0 ≤ q := by dsimp [q]; omega
    refine ⟨q.toNat, ?_, ?_⟩
    · rw [Int.toNat_of_nonneg hq]
      dsimp [q]
      omega
    · have hcast : ((q.toNat : ℕ) : ℤ) = q := Int.toNat_of_nonneg hq
      simp only [laneBPerimeterBlock, hcast]
      dsimp [q]
      split_ifs <;> apply Prod.ext <;> simp only [Prod.fst, Prod.snd] <;> omega
  · let q : ℤ := 2 * (2 * m + 1) + (m - b.1)
    have hq : 0 ≤ q := by dsimp [q]; omega
    refine ⟨q.toNat, ?_, ?_⟩
    · rw [Int.toNat_of_nonneg hq]
      dsimp [q]
      omega
    · have hcast : ((q.toNat : ℕ) : ℤ) = q := Int.toNat_of_nonneg hq
      simp only [laneBPerimeterBlock, hcast]
      dsimp [q]
      split_ifs <;> apply Prod.ext <;> simp only [Prod.fst, Prod.snd] <;> omega
  · let q : ℤ := b.1 + m + 1
    have hq : 0 ≤ q := by dsimp [q]; omega
    refine ⟨q.toNat, ?_, ?_⟩
    · rw [Int.toNat_of_nonneg hq]
      dsimp [q]
      omega
    · have hcast : ((q.toNat : ℕ) : ℤ) = q := Int.toNat_of_nonneg hq
      simp only [laneBPerimeterBlock, hcast]
      dsimp [q]
      split_ifs <;> apply Prod.ext <;> simp only [Prod.fst, Prod.snd] <;> omega

 
theorem laneB_perimeter_order_length_le {R : ℝ} (hR : 24 ≤ R) :
    (((4 * (2 * laneBGridRadius R + 1) + 1 : ℤ) : ℝ)) ≤ 11 * R := by
  have h := (laneB_grid_radius_bounds hR).2
  push_cast
  linarith

end SupercriticalLQGUniqueness.B2.DG20Conc
