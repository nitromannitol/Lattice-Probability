/-
The killed Green function as a voltage.

For a finite `C` with `o ∈ C` and a vertex outside `C`, in a connected locally
finite graph, `v ↦ g_C(o,v)` vanishes off `C`, is harmonic on `C \ {o}`, and has
Laplacian `-1` at `o`.  That is the boundary value problem `eq:gC-PDE`, and it
is the fact from which the rest of the network theory of the killed walk
follows.

The proof reads `g_C(o,v)` in the reversed form `∑_k p^C_k(v,o)/deg(o)`, which
is what `killedKer_symm` provides, and then the defining recursion of
`killedHeat` in the first argument becomes the statement about the Laplacian in
`v`.
-/
import LatticeProb.Network.Killed

open Finset
open scoped ENNReal
open scoped Classical

namespace LatticeProb.Network

open LatticeProb.Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

section
variable (hG : G.Connected) (C : Finset V) {o q : V} (ho : o ∈ C) (hq : q ∉ C)

include hG hq in
theorem killedGreenReal_eq_zero_of_not_mem {v : V} (hv : v ∉ C) (x : V) :
    killedGreenReal G (C : Set V) x v = 0 := by
  rw [killedGreenReal_eq_tsum hG C hq x v]
  have : (fun k => killedHeat G (C : Set V) k x v) = fun _ => (0 : ℝ) := by
    funext k
    exact killedHeat_of_target_not_mem (by exact_mod_cast hv) k x
  rw [this, tsum_zero, zero_div]

include hG hq in
/-- The killed Green function is symmetric in its two arguments. -/
theorem killedGreenReal_symm (x v : V) :
    killedGreenReal G (C : Set V) x v = killedGreenReal G (C : Set V) v x := by
  rw [killedGreenReal_eq_tsum hG C hq x v, killedGreenReal_eq_tsum hG C hq v x,
    ← tsum_div_const, ← tsum_div_const]
  exact tsum_congr fun k => killedKer_symm (G := G) (C : Set V) k x v

include hG hq in
/-- The killed Green function in the reversed form: `g_C(o,v) = ∑_k p^C_k(v,o)/deg(o)`. -/
theorem killedGreenReal_eq_reversed (x v : V) :
    killedGreenReal G (C : Set V) x v
      = (∑' k : ℕ, killedHeat G (C : Set V) k v x) / G.degree x := by
  rw [killedGreenReal_symm hG C hq x v, killedGreenReal_eq_tsum hG C hq v x]

include hG hq in
theorem killedGreenReal_nonneg (x v : V) : 0 ≤ killedGreenReal G (C : Set V) x v := by
  rw [killedGreenReal_eq_tsum hG C hq x v]
  exact div_nonneg (tsum_nonneg fun k => killedHeat_nonneg _ k x v) (Nat.cast_nonneg _)

include hG ho hq in
/-- The neighbour sum of the reversed local times, from the defining recursion. -/
theorem sum_tsum_killedHeat (x : V) {v : V} (hv : v ∈ C) :
    ∑ w ∈ G.neighborFinset v, (∑' k : ℕ, killedHeat G (C : Set V) k w x)
      = (G.degree v : ℝ) *
          ((∑' k : ℕ, killedHeat G (C : Set V) k v x)
            - killedHeat G (C : Set V) 0 v x) := by
  have hdv : 0 < G.degree v := degree_pos_of_ne hG (fun h : o = q => hq (h ▸ ho)) v
  have hsum : ∀ w : V, Summable (fun k => killedHeat G (C : Set V) k w x) := fun w =>
    summable_killedHeat hG C hq w x
  have hex : ∑ w ∈ G.neighborFinset v, (∑' k : ℕ, killedHeat G (C : Set V) k w x)
      = ∑' k : ℕ, ∑ w ∈ G.neighborFinset v, killedHeat G (C : Set V) k w x :=
    (Summable.tsum_finsetSum (fun w _ => hsum w)).symm
  have hstep : ∀ k : ℕ, ∑ w ∈ G.neighborFinset v, killedHeat G (C : Set V) k w x
      = (G.degree v : ℝ) * killedHeat G (C : Set V) (k + 1) v x := by
    intro k
    rw [killedHeat_succ, if_pos (by exact_mod_cast hv : v ∈ (C : Set V)),
      mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hdv.ne')]
  rw [hex, tsum_congr hstep, tsum_mul_left,
    (hsum v).tsum_eq_zero_add]
  ring

end

section
variable (hG : G.Connected) (C : Finset V) {o q : V} (ho : o ∈ C) (hq : q ∉ C)

include hG hq in
/-- The killed Green function vanishes off `C`. -/
theorem killedGreen_vanishes {v : V} (hv : v ∉ (C : Set V)) :
    killedGreenReal G (C : Set V) o v = 0 :=
  killedGreenReal_eq_zero_of_not_mem hG C hq (by exact_mod_cast hv) o

include hG ho hq in
/-- The Laplacian of the killed Green function inside `C`: it is `-1` at the
source and `0` elsewhere. -/
theorem laplacian_killedGreenReal {v : V} (hv : v ∈ (C : Set V)) :
    laplacian G (killedGreenReal G (C : Set V) o) v
      = -(if v = o then (1 : ℝ) else 0) := by
  have hvC : v ∈ C := by exact_mod_cast hv
  have hoq : o ≠ q := fun h => hq (h ▸ ho)
  have hdo : 0 < G.degree o := degree_pos_of_ne hG hoq o
  have hdoR : (G.degree o : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hdo.ne'
  have hu : ∀ w : V, killedGreenReal G (C : Set V) o w
      = (∑' k : ℕ, killedHeat G (C : Set V) k w o) / (G.degree o : ℝ) := fun w =>
    killedGreenReal_eq_reversed hG C hq o w
  have hsum := sum_tsum_killedHeat hG C ho hq o hvC
  have hzero : killedHeat G (C : Set V) 0 v o = if v = o then (1 : ℝ) else 0 := by
    rw [killedHeat_zero, if_pos hv]
  rw [laplacian]
  simp only [hu]
  rw [Finset.sum_sub_distrib, Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree,
    nsmul_eq_mul, ← Finset.sum_div, hsum, hzero]
  by_cases hvo : v = o
  · subst hvo
    rw [if_pos rfl]
    field_simp
    ring
  · rw [if_neg hvo]
    field_simp
    ring

include hG ho hq in
/-- The killed Green function is harmonic on `C` away from the source. -/
theorem harmonic_killedGreenReal {v : V} (hv : v ∈ (C : Set V)) (hvo : v ≠ o) :
    laplacian G (killedGreenReal G (C : Set V) o) v = 0 := by
  rw [laplacian_killedGreenReal hG C ho hq hv, if_neg hvo]
  norm_num

include hG ho hq in
/-- The unit source at `o`. -/
theorem laplacian_killedGreenReal_source :
    laplacian G (killedGreenReal G (C : Set V) o) o = -1 := by
  rw [laplacian_killedGreenReal hG C ho hq (by exact_mod_cast ho), if_pos rfl]

end

end LatticeProb.Network
