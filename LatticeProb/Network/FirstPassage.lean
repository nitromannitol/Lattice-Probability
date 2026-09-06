/-
The mean local time is largest at its own base point.

`E_x[L_n(y)] ≤ E_y[L_n(y)]` for every `x`: the walk started elsewhere spends no
more time at `y` before time `n` than the walk started at `y`.  This is the
first-passage decomposition `E_x[L_n(y)] = ∑_{j<n} P_x(T_y = j) E_y[L_{n-j}(y)]`
read as an induction on `n`: the first step of the walk from a vertex other than
`y` averages the same quantity at time `n`, which the induction hypothesis
already bounds by `E_y[L_n(y)]`, so no hitting time has to be constructed.

Combined with reversibility this gives `sup_v g_n(o,v) ≤ g_n(o,o)`, the form the
Green function is used in.
-/
import LatticeProb.Network.Killed
import LatticeProb.Graph.Green
import LatticeProb.Graph.Setting

open Finset
open scoped ENNReal
open scoped Classical

namespace LatticeProb.Network

open LatticeProb.Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

theorem meanLocalTime_nonneg (n : ℕ) (x y : V) : 0 ≤ meanLocalTime G n x y :=
  Finset.sum_nonneg fun k _ => heat_nonneg (G := G) k x y

theorem meanLocalTime_mono (n : ℕ) (x y : V) :
    meanLocalTime G n x y ≤ meanLocalTime G (n + 1) x y := by
  rw [meanLocalTime, meanLocalTime, Finset.sum_range_succ]
  linarith [heat_nonneg (G := G) n x y]

/-- The first step of the walk, in the mean local time. -/
theorem meanLocalTime_succ (n : ℕ) (x y : V) :
    meanLocalTime G (n + 1) x y
      = (if x = y then 1 else 0) + walkOp G (fun z => meanLocalTime G n z y) x := by
  rw [meanLocalTime, Finset.sum_range_succ']
  have h0 : heat G 0 x y = if x = y then 1 else 0 := rfl
  have hstep : ∀ k ∈ Finset.range n, heat G (k + 1) x y
      = walkOp G (fun z => heat G k z y) x := fun k _ => heat_succ k x y
  rw [Finset.sum_congr rfl hstep, h0, add_comm]
  congr 1
  exact (walkOp_sum n (fun k z => heat G k z y) x).symm

/-- The walk started anywhere spends no more time at `y` than the walk started
at `y`. -/
theorem meanLocalTime_le_self : ∀ (n : ℕ) (x y : V),
    meanLocalTime G n x y ≤ meanLocalTime G n y y := by
  intro n
  induction n with
  | zero => intro x y; simp [meanLocalTime]
  | succ n ih =>
      intro x y
      by_cases hxy : x = y
      · rw [hxy]
      · rw [meanLocalTime_succ, if_neg hxy, zero_add]
        have hB : 0 ≤ meanLocalTime G n y y := meanLocalTime_nonneg n y y
        have hle : walkOp G (fun z => meanLocalTime G n z y) x ≤ meanLocalTime G n y y := by
          rw [walkOp]
          by_cases hd : G.degree x = 0
          · rw [neighborFinset_eq_empty_of_degree_zero hd]
            simpa using hB
          · have hdR : (0 : ℝ) < G.degree x := by
              exact_mod_cast Nat.pos_of_ne_zero hd
            rw [div_le_iff₀ hdR]
            calc ∑ z ∈ G.neighborFinset x, meanLocalTime G n z y
                ≤ ∑ _z ∈ G.neighborFinset x, meanLocalTime G n y y :=
                  Finset.sum_le_sum fun z _ => ih z y
              _ = meanLocalTime G n y y * G.degree x := by
                  rw [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
                    nsmul_eq_mul, mul_comm]
        exact hle.trans (meanLocalTime_mono n y y)

/-- Reversibility, summed over time. -/
theorem meanLocalTime_reversible (n : ℕ) (x y : V) :
    (G.degree x : ℝ) * meanLocalTime G n x y = (G.degree y : ℝ) * meanLocalTime G n y x := by
  rw [meanLocalTime, meanLocalTime, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => heat_reversible k x y

/-- The finite-time Green function is largest at the source. -/
theorem greenTime_le_diag [Nontrivial V] (hG : G.Connected) (n : ℕ) (o v : V) :
    greenTime G n o v ≤ greenTime G n o o := by
  obtain ⟨a, b, hab⟩ := exists_pair_ne V
  have hdo : 0 < G.degree o := degree_pos_of_ne hG hab o
  have hdv : 0 < G.degree v := degree_pos_of_ne hG hab v
  have hdoR : (0 : ℝ) < G.degree o := by exact_mod_cast hdo
  have hdvR : (0 : ℝ) < G.degree v := by exact_mod_cast hdv
  have hrev := meanLocalTime_reversible (G := G) n o v
  have hswap : meanLocalTime G n o v / (G.degree v : ℝ)
      = meanLocalTime G n v o / (G.degree o : ℝ) := by
    rw [div_eq_div_iff hdvR.ne' hdoR.ne']
    linarith [hrev]
  rw [greenTime, greenTime, hswap, div_eq_mul_inv, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_right (meanLocalTime_le_self n v o) (by positivity)

/-- `sup_v g_n(o,v) ≤ g_n(o,o)`. -/
theorem supGreenTime_le [Nontrivial V] (hG : G.Connected) (n : ℕ) (o : V) :
    supGreenTime G n o ≤ ENNReal.ofReal (greenTime G n o o) :=
  iSup_le fun v => ENNReal.ofReal_le_ofReal (greenTime_le_diag hG n o v)

end LatticeProb.Network
