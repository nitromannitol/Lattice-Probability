/-
Positivity of the simple-random-walk heat kernel at reachable sites.

`LatticeProb.srwHeat d j x` vanishes off the ball of radius `j`
(`srwHeat_eq_zero_of_lt`) and inside it vanishes unless the parity of the `ℓ¹`
norm of `x` agrees with the parity of `j` (`srwHeat_eq_zero_of_parity`).  This
file proves the converse: those two conditions are also sufficient, so the
kernel is strictly positive exactly on the reachable sites.  The criterion is
what discharges the hypothesis `0 < p_ℓ(x, y)` of the local central limit
theorem quoted in `sandpile.tex:1145-1161`.
-/
import LatticeProb.Walk.SRW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LatticeProb

open Finset

variable {d : ℕ}

theorem exists_dirVec_graphNorm_eq_sub_one {d : ℕ} {x : Site d} (hx : x ≠ 0) :
    ∃ a : Dir d, graphNorm (x + dirVec a) = graphNorm x - 1 := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  refine ⟨(i, decide (x i ≤ 0)), ?_⟩
  simp only [graphNorm]
  have hmem : i ∉ (Finset.univ : Finset (Fin d)).erase i := by simp
  have huniv : (Finset.univ : Finset (Fin d)) = insert i (Finset.univ.erase i) := by
    ext j; simp
  rw [huniv, Finset.sum_insert hmem, Finset.sum_insert hmem]
  have hd : ∀ j : Fin d, j ≠ i → (x + dirVec (i, decide (x i ≤ 0))) j = x j := by
    intro j hj
    simp [dirVec, Pi.add_apply, hj]
  have habs : ((x + dirVec (i, decide (x i ≤ 0))) i).natAbs = (x i).natAbs - 1 := by
    rw [Pi.add_apply]
    by_cases hle : x i ≤ 0
    · simp [dirVec, hle]
      omega
    · have hgt : 0 < x i := by omega
      have hnl : ¬ (x i ≤ 0) := by omega
      simp [dirVec, hnl]
      omega
  rw [habs]
  rw [Finset.sum_congr rfl (fun j hj => by
    rw [hd j (Finset.mem_erase.1 hj).1])]
  omega

/-- Positivity of the simple-random-walk heat kernel at reachable sites. -/
theorem srwHeat_pos {d : ℕ} (hd : 1 ≤ d) {j : ℕ} {x : Site d}
    (hle : graphNorm x ≤ j) (hpar : graphNorm x % 2 = j % 2) :
    0 < srwHeat d j x := by
  induction j generalizing x with
  | zero =>
      have hx : x = 0 := by
        rw [← graphNorm_eq_zero_iff]
        omega
      subst hx
      simp
  | succ j ih =>
      rw [srwHeat_succ_eq_sum_dir]
      by_cases hx : x = 0
      · subst hx
        simp only [graphNorm_zero] at hpar
        have hj : j % 2 = 1 := by omega
        have h1 : 1 ≤ j := Nat.pos_of_ne_zero (fun h => by simp [h] at hj)
        haveI : Nonempty (Dir d) := ⟨(⟨0, hd⟩, true)⟩
        have hpos : 0 < ∑ a : Dir d, srwHeat d j (dirVec a) := by
          apply Finset.sum_pos
          · intro a _
            exact ih (by rw [graphNorm_dirVec]; omega)
              (by rw [graphNorm_dirVec, hj])
          · exact Finset.univ_nonempty
        simpa using div_pos hpos (by positivity)
      · have hgx : 1 ≤ graphNorm x :=
          Nat.pos_of_ne_zero (fun h => hx (graphNorm_eq_zero_iff.mp h))
        obtain ⟨a, ha⟩ := exists_dirVec_graphNorm_eq_sub_one hx
        have hle' : graphNorm (x + dirVec a) ≤ j := by omega
        have hpar' : graphNorm (x + dirVec a) % 2 = j % 2 := by omega
        have hpos := ih hle' hpar'
        have hsum : 0 < ∑ a : Dir d, srwHeat d j (x + dirVec a) :=
          lt_of_lt_of_le hpos
            (Finset.single_le_sum (f := fun b => srwHeat d j (x + dirVec b))
              (fun b _ => srwHeat_nonneg j _) (Finset.mem_univ a))
        exact div_pos hsum (by positivity)

end LatticeProb
