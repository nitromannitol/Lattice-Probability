/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Geom58Fin2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom58Fin1
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom58Paths
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.SepMeas56

/-!
# GM Lemma 5.8: the tube `U_r^{x,y}` of Step 2 (task P2-M2L58b)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, proof of
Lemma 5.8, Step 2 (l. 3079–3092): "Since the `V_r(z_k)`'s are connected, it is clear that
`U_r^{x,y}` is connected and contains `x, y`" and "`U_r^{x,y}` is the interior of a finite union of
squares in `𝓢_{ε₁ρr}(𝔸_{r/2,2r}(0))`" (with D69's closed annulus).

* `L58Data.isConnected_U`, `L58Data.isSquareTube_U`, `L58Data.U_subset_ball`: Step 2.
* used in `l58Geom` (`Geom58T5`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric

namespace LQGMetric.GM
open Blueprint

namespace L58Data

variable (D : L58Data)

/-- every point of `U` lies in the component of `z_{m−1} − 2R` in `U` -/
lemma mem_comp_U (hm : 0 < D.m) {w : ℂ} (hw : w ∈ D.U) :
    w ∈ connectedComponentIn (D.U \ ∅) (D.zs (D.m - 1) - 2 * (D.R : ℂ)) := by
  have hk : D.m - 1 < D.m := by omega
  have hPB : ∀ i ≤ D.m, Disjoint (D.P i) (∅ : Set ℂ) := fun _ _ => disjoint_empty _
  have chainL := D.chain_left hk hPB (fun _ _ => disjoint_empty _)
  have chainR := D.chain_right hk hPB (fun _ _ _ => disjoint_empty _)
  have hVk : D.Vs (D.m - 1) ⊆
      connectedComponentIn (D.U \ ∅) (D.zs (D.m - 1) - 2 * (D.R : ℂ)) :=
    (D.hFc _ hk).subset_connectedComponentIn (D.hFl _ hk)
      (fun v hv => ⟨D.Vs_subset_U hk hv, notMem_empty v⟩)
  have hfar : ∀ g : ℤ × ℤ, ∀ v p, p ∈ gridSquare D.s g → dist v p < 2 * D.s → v ∉ (∅ : Set ℂ) :=
    fun _ v _ _ _ => notMem_empty v
  rcases D.of_mem_G (interior_subset hw) with ⟨j, hj, g, hg, hwg⟩ | ⟨i, hi, g, hg, hwg⟩
  · rcases lt_or_eq_of_le (Nat.le_sub_one_of_lt hj) with h | h
    · exact D.Fsq_mem_comp hj ((chainL (D.m - 1) le_rfl).2 j (by omega) h) (disjoint_empty _)
        hg (hfar g) hw hwg
    · subst h
      exact D.Fsq_mem_comp hj hVk (disjoint_empty _) hg (hfar g) hw hwg
  · rcases lt_or_eq_of_le hi with h | h
    · have hP := (chainL (D.m - 1 - i) (by omega)).1
      rw [show D.m - 1 - (D.m - 1 - i) = i by omega] at hP
      exact D.Qsq_mem_comp hi hP (disjoint_empty _) hg (hfar g) hw hwg
    · subst h
      have hP := (chainR 0 (by omega)).1
      rw [show D.m - 1 + 1 + 0 = D.m by omega] at hP
      rw [connectedComponentIn_eq (hVk (D.hFr _ hk))]
      exact D.Qsq_mem_comp hi hP (disjoint_empty _) hg (hfar g) hw hwg

/-- **GM l. 3091**: `U_r^{x,y}` is connected -/
lemma isConnected_U (hm : 0 < D.m) : IsConnected D.U := by
  have hk : D.m - 1 < D.m := by omega
  have ht : D.zs (D.m - 1) - 2 * (D.R : ℂ) ∈ D.U := D.Vs_subset_U hk (D.hFl _ hk)
  have heq : connectedComponentIn (D.U \ ∅) (D.zs (D.m - 1) - 2 * (D.R : ℂ)) = D.U := by
    apply le_antisymm
    · exact (connectedComponentIn_subset _ _).trans sdiff_subset
    · exact fun w hw => D.mem_comp_U hm hw
  refine ⟨⟨_, ht⟩, ?_⟩
  rw [← heq]
  exact isPreconnected_connectedComponentIn

/-- **GM l. 3089–3090**: `U_r^{x,y}` is a square tube over `A` -/
lemma isSquareTube_U {A : Set ℂ} (hA : ∀ j < D.m, closedBall (D.zs j) (2 * D.R) ⊆ A)
    (hPA : ∀ i ≤ D.m, D.P i ⊆ A) : IsSquareTube D.U D.s A := by
  refine ⟨D.G, fun g hg => ?_, rfl⟩
  rcases Finset.mem_union.1 (Finset.mem_coe.1 hg) with h1 | h1
  · obtain ⟨j, hj, hgj⟩ := Finset.mem_biUnion.1 h1
    obtain ⟨c, hcS, hcB⟩ := D.hF j (Finset.mem_range.1 hj) hgj
    exact ⟨c, hcS, hA j (Finset.mem_range.1 hj) hcB⟩
  · obtain ⟨i, hi, hgi⟩ := Finset.mem_biUnion.1 h1
    have hi' := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    obtain ⟨c, hcS, hcP⟩ := (D.hQ i hi' g).1 hgi
    exact ⟨c, hcS, hPA i hi' hcP⟩

lemma U_subset_ball {ρ : ℝ} (hz : ∀ j < D.m, ‖D.zs j‖ + 2 * D.R + 2 * D.s < ρ)
    (hP : ∀ i ≤ D.m, ∀ p ∈ D.P i, ‖p‖ + 2 * D.s < ρ) : D.U ⊆ ball 0 ρ := by
  intro w hw
  rw [mem_ball, dist_zero_right]
  rcases D.of_mem_G (interior_subset hw) with ⟨j, hj, g, hg, hwg⟩ | ⟨i, hi, g, hg, hwg⟩
  · have h1 := D.dist_le_of_F hj hg hwg
    rw [dist_eq_norm] at h1
    have := norm_le_norm_add_norm_sub' w (D.zs j)
    linarith [hz j hj]
  · obtain ⟨c, hc, -, hwc⟩ := D.Q_near hi hg hwg
    rw [dist_eq_norm] at hwc
    have := norm_le_norm_add_norm_sub' w c
    linarith [hP i hi c hc]

end L58Data

/-- finitely many squares meet a set in `B_ρ(0)` -/
lemma squareSet_finite_of_subset_ball {s ρ : ℝ} (hs : 0 < s) {X : Set ℂ} (hX : X ⊆ ball 0 ρ) :
    (squareSet s X).Finite :=
  (sqBox s ρ 0).finite_toSet.subset
    ((squareSet_mono s hX).trans (squareSet_ball_subset_box hs ρ 0))

end LQGMetric.GM
