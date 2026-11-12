import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Complex.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Basic

/-!
# Gluing two polygonal rays into a bi-infinite polygonal chain

Let `v, w : ℕ → ℂ` be two simple polygonal rays from the common vertex `v 0 = w 0`, with
`v n → a` and `w n → b`, which meet only at the common vertex (the first edge of `v` and the first
edge of `w` share only `w 0`, and every other pair of edges, one from each ray, is disjoint).
Then the bi-infinite sequence `u n = w n` for `n ≥ 0`, `u n = v (-n)` for `n ≤ 0` is a simple
bi-infinite polygonal chain from `a` (at `-∞`) to `b` (at `+∞`), with the same union of edges.

* `LatticeProb.Topology.exists_biinfinite_of_two_rays`: the gluing.
-/

open Filter
open scoped Topology

namespace LatticeProb.Topology

/-- **Gluing of two simple polygonal rays at a common vertex.**  See the module docstring. -/
theorem exists_biinfinite_of_two_rays {v w : ℕ → ℂ} {a b : ℂ} (h0 : v 0 = w 0)
    (hvne : ∀ n, v n ≠ v (n + 1)) (hwne : ∀ n, w n ≠ w (n + 1))
    (hvadj : ∀ n, segment ℝ (v n) (v (n + 1)) ∩ segment ℝ (v (n + 1)) (v (n + 2)) ⊆ {v (n + 1)})
    (hwadj : ∀ n, segment ℝ (w n) (w (n + 1)) ∩ segment ℝ (w (n + 1)) (w (n + 2)) ⊆ {w (n + 1)})
    (hvfar : ∀ n m, n + 2 ≤ m → Disjoint (segment ℝ (v n) (v (n + 1))) (segment ℝ (v m) (v (m + 1))))
    (hwfar : ∀ n m, n + 2 ≤ m → Disjoint (segment ℝ (w n) (w (n + 1))) (segment ℝ (w m) (w (m + 1))))
    (hjoin : segment ℝ (v 0) (v 1) ∩ segment ℝ (w 0) (w 1) ⊆ {w 0})
    (hcross : ∀ n m, 1 ≤ n + m →
      Disjoint (segment ℝ (v n) (v (n + 1))) (segment ℝ (w m) (w (m + 1))))
    (hva : Tendsto v atTop (𝓝 a)) (hwb : Tendsto w atTop (𝓝 b))
    (hav : ∀ n, a ∉ segment ℝ (v n) (v (n + 1))) (haw : ∀ n, a ∉ segment ℝ (w n) (w (n + 1)))
    (hbv : ∀ n, b ∉ segment ℝ (v n) (v (n + 1))) (hbw : ∀ n, b ∉ segment ℝ (w n) (w (n + 1))) :
    ∃ u : ℤ → ℂ, (∀ n, u n ≠ u (n + 1)) ∧
      (∀ n, segment ℝ (u n) (u (n + 1)) ∩ segment ℝ (u (n + 1)) (u (n + 2)) ⊆ {u (n + 1)}) ∧
      (∀ n m : ℤ, n + 2 ≤ m →
        Disjoint (segment ℝ (u n) (u (n + 1))) (segment ℝ (u m) (u (m + 1)))) ∧
      Tendsto u atBot (𝓝 a) ∧ Tendsto u atTop (𝓝 b) ∧
      (∀ n, a ∉ segment ℝ (u n) (u (n + 1))) ∧ (∀ n, b ∉ segment ℝ (u n) (u (n + 1))) ∧
      (⋃ n : ℤ, segment ℝ (u n) (u (n + 1))) =
        (⋃ n, segment ℝ (v n) (v (n + 1))) ∪ ⋃ n, segment ℝ (w n) (w (n + 1)) := by
  classical
  obtain ⟨u, hun, hvn⟩ : ∃ u : ℤ → ℂ, (∀ k : ℕ, u k = w k) ∧ (∀ k : ℕ, u (-(k : ℤ)) = v k) := by
    refine ⟨fun n => if 0 ≤ n then w n.toNat else v (-n).toNat, fun k => ?_, fun k => ?_⟩
    · simp
    · by_cases hk : k = 0
      · subst hk
        simp [h0]
      · have hneg : ¬ (0 : ℤ) ≤ -(k : ℤ) := by omega
        dsimp only
        split_ifs
        simp
  have hun1 : ∀ k : ℕ, u ((k : ℤ) + 1) = w (k + 1) := fun k => by
    have := hun (k + 1)
    push_cast at this
    exact this
  have hun2 : ∀ k : ℕ, u ((k : ℤ) + 2) = w (k + 2) := fun k => by
    have := hun (k + 2)
    push_cast at this
    exact this
  have hvn1 : ∀ k : ℕ, u (-(k : ℤ) - 1) = v (k + 1) := fun k => by
    have := hvn (k + 1)
    push_cast at this
    rw [← this]
    congr 1
    ring
  have hvn0 : ∀ k : ℕ, u (-(k : ℤ) - 1 + 1) = v k := fun k => by
    rw [← hvn k]
    congr 1
    ring
  have hcase : ∀ n : ℤ, (∃ k : ℕ, n = k) ∨ (∃ k : ℕ, n = -(k : ℤ) - 1) := by
    intro n
    rcases n with k | k
    · exact Or.inl ⟨k, rfl⟩
    · exact Or.inr ⟨k, by rw [Int.negSucc_eq]; ring⟩
  have hEw : ∀ k : ℕ, segment ℝ (u k) (u ((k : ℤ) + 1)) = segment ℝ (w k) (w (k + 1)) :=
    fun k => by rw [hun k, hun1 k]
  have hEv : ∀ k : ℕ, segment ℝ (u (-(k : ℤ) - 1)) (u (-(k : ℤ) - 1 + 1)) =
      segment ℝ (v k) (v (k + 1)) := fun k => by
    rw [hvn1 k, hvn0 k, segment_symm]
  have hcase3 : ∀ n : ℤ, (∃ k : ℕ, n = k) ∨ n = -1 ∨ (∃ j : ℕ, n = -(j : ℤ) - 2) := by
    intro n
    rcases hcase n with ⟨k, hk⟩ | ⟨k, hk⟩
    · exact Or.inl ⟨k, hk⟩
    · rcases Nat.eq_zero_or_pos k with rfl | hk0
      · exact Or.inr (Or.inl (by simpa using hk))
      · exact Or.inr (Or.inr ⟨k - 1, by omega⟩)
  refine ⟨u, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    rcases hcase n with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [hun k, hun1 k]
      exact hwne k
    · rw [hvn1 k, hvn0 k]
      exact (hvne k).symm
  · intro n
    rcases hcase3 n with ⟨k, rfl⟩ | rfl | ⟨j, rfl⟩
    · rw [hEw k, hun1 k, hun2 k]
      exact hwadj k
    · have e1 : u (-1) = v 1 := by simpa using hvn 1
      have e0 : u (-1 + 1) = w 0 := by
        have : (-1 : ℤ) + 1 = ((0 : ℕ) : ℤ) := by norm_num
        rw [this, hun 0]
      have e2 : u (-1 + 2) = w 1 := by
        have : (-1 : ℤ) + 2 = ((1 : ℕ) : ℤ) := by norm_num
        rw [this, hun 1]
      rw [e1, e0, e2]
      intro x hx
      apply hjoin
      refine ⟨?_, hx.2⟩
      have hx1 := hx.1
      rw [segment_symm] at hx1
      rw [h0]
      exact hx1
    · have ea : u (-(j : ℤ) - 2) = v (j + 2) := by
        have := hvn (j + 2)
        push_cast at this
        rw [← this]
        congr 1
        ring
      have eb : u (-(j : ℤ) - 2 + 1) = v (j + 1) := by
        have : -(j : ℤ) - 2 + 1 = -(j : ℤ) - 1 := by ring
        rw [this, hvn1 j]
      have ec : u (-(j : ℤ) - 2 + 2) = v j := by
        have : -(j : ℤ) - 2 + 2 = -(j : ℤ) := by ring
        rw [this, hvn j]
      rw [ea, eb, ec, segment_symm ℝ (v (j + 2)) (v (j + 1)), segment_symm ℝ (v (j + 1)) (v j),
        Set.inter_comm]
      exact hvadj j
  · intro n m hnm
    rcases hcase n with ⟨k, rfl⟩ | ⟨k, rfl⟩ <;> rcases hcase m with ⟨l, rfl⟩ | ⟨l, rfl⟩
    · rw [hEw k, hEw l]
      exact hwfar k l (by omega)
    · exfalso
      omega
    · rw [hEv k, hEw l]
      exact hcross k l (by omega)
    · rw [hEv k, hEv l]
      exact (hvfar l k (by omega)).symm
  · have hbot : Tendsto (fun n : ℤ => (-n).toNat) atBot atTop :=
      Filter.tendsto_atBot_atTop.2 fun N => ⟨-(N : ℤ), fun n hn => by omega⟩
    refine (hva.comp hbot).congr' ?_
    filter_upwards [eventually_le_atBot (0 : ℤ)] with n hn
    have hn' : n = -(((-n).toNat : ℕ) : ℤ) := by omega
    have h := hvn (-n).toNat
    rw [← hn'] at h
    exact h.symm
  · have htop : Tendsto (fun n : ℤ => n.toNat) atTop atTop :=
      Filter.tendsto_atTop_atTop.2 fun N => ⟨N, fun n hn => by omega⟩
    refine (hwb.comp htop).congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℤ)] with n hn
    have hn' : n = ((n.toNat : ℕ) : ℤ) := by omega
    have h := hun n.toNat
    rw [← hn'] at h
    exact h.symm
  · intro n
    rcases hcase n with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [hEw k]
      exact haw k
    · rw [hEv k]
      exact hav k
  · intro n
    rcases hcase n with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [hEw k]
      exact hbw k
    · rw [hEv k]
      exact hbv k
  · ext x
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨n, hn⟩
      rcases hcase n with ⟨k, rfl⟩ | ⟨k, rfl⟩
      · right
        exact ⟨k, by rwa [hEw k] at hn⟩
      · left
        exact ⟨k, by rwa [hEv k] at hn⟩
    · rintro (⟨k, hk⟩ | ⟨k, hk⟩)
      · exact ⟨-(k : ℤ) - 1, by rw [hEv k]; exact hk⟩
      · exact ⟨k, by rw [hEw k]; exact hk⟩

end LatticeProb.Topology
