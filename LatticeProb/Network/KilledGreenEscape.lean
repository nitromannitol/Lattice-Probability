/-
The killed Green function as a voltage, on a graph that need not be connected.

`LatticeProb/Network/KilledGreen.lean` proves the boundary value problem
`eq:gC-PDE` for `g_C(o,·)` on a CONNECTED graph: it vanishes off `C`, is
harmonic on `C` away from the source, and has Laplacian `-1` at the source.
Connectivity is not what those proofs use.  What they use is that the walk
leaves `C`, and that the vertices of `C` are not isolated.  The two hypotheses

    hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ C
    hdeg : ∀ v ∈ C, 0 < G.degree v

replace connectivity throughout, and every supporting lemma of `Killed.lean`
(`exists_survival_lt`, `survival_add_le`, `survival_le_pow`,
`sum_range_survival_le`, `killedHeat_le_survival`, `killedKer_symm`,
`killedHeat_succ`) is used unchanged, since none of it mentions connectivity.

This is the form a graph with isolated vertices needs.  A vertex carrying no
meaning is isolated, so a graph built by giving an adjacency relation only to
the meaningful vertices of a type is never connected, while every meaningful
vertex still walks out of a finite set and still has a neighbour.

The connected statements are corollaries: `hesc` is `hG.preconnected x q` for a
fixed `q ∉ C`, and `hdeg` is `degree_pos_of_ne hG`.
-/
import LatticeProb.Network.KilledGreen

open Finset
open scoped ENNReal
open scoped Classical

namespace LatticeProb.Network

open LatticeProb.Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

variable (C : Finset V)

/-- A uniform survival bound from escape alone: if every vertex has a walk out
of `C`, then at some common time the survival probability is below one,
uniformly in the starting point. -/
theorem exists_uniform_survival_le_of_escape
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ C) :
    ∃ (N : ℕ) (θ : ℝ), 0 < N ∧ 0 ≤ θ ∧ θ < 1 ∧ ∀ x : V, survival G C N x ≤ θ := by
  classical
  have hlen : ∀ x : V, ∃ n : ℕ, ∃ e : ℝ, 0 < e ∧ survival G C n x ≤ 1 - e := by
    intro x
    obtain ⟨q, p, hq⟩ := hesc x
    obtain ⟨e, he, hle⟩ := exists_survival_lt C p hq
    exact ⟨p.length, e, he, hle⟩
  choose l e he hle using hlen
  by_cases hC : C.Nonempty
  · refine ⟨C.sup l + 1, C.sup' hC (fun x => survival G C (C.sup l + 1) x),
      Nat.succ_pos _, ?_, ?_, ?_⟩
    · obtain ⟨x, hx⟩ := hC
      exact le_trans (survival_nonneg C _ x) (Finset.le_sup' _ hx)
    · rw [Finset.sup'_lt_iff]
      intro x hx
      have h1 : survival G C (C.sup l + 1) x ≤ survival G C (l x) x :=
        survival_antitone C (by have := Finset.le_sup (f := l) hx; omega) x
      linarith [hle x, he x]
    · intro x
      by_cases hx : x ∈ C
      · exact Finset.le_sup' _ hx
      · rw [survival_of_not_mem hx]
        obtain ⟨y, hy⟩ := hC
        exact le_trans (survival_nonneg C _ y) (Finset.le_sup' _ hy)
  · refine ⟨1, 0, Nat.one_pos, le_refl 0, zero_lt_one, ?_⟩
    intro x
    rw [Finset.not_nonempty_iff_eq_empty] at hC
    rw [survival, hC, Finset.sum_empty]

/-- The local time of the walk killed on leaving `C` is summable, from escape
alone. -/
theorem summable_killedHeat_of_escape
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ C) (x v : V) :
    Summable (fun k => killedHeat G (C : Set V) k x v) := by
  classical
  by_cases hv : v ∈ C
  · obtain ⟨N, θ, hN, hθ0, hθ1, hθ⟩ := exists_uniform_survival_le_of_escape C hesc
    refine summable_of_sum_range_le (c := (N : ℝ) / (1 - θ))
      (fun k => killedHeat_nonneg _ k x v) (fun n => ?_)
    calc ∑ k ∈ Finset.range n, killedHeat G (C : Set V) k x v
        ≤ ∑ k ∈ Finset.range n, survival G C k x :=
          Finset.sum_le_sum fun k _ => killedHeat_le_survival C hv k x
      _ ≤ (N : ℝ) / (1 - θ) := sum_range_survival_le hN hθ0 hθ1 hθ x n
  · have : (fun k => killedHeat G (C : Set V) k x v) = fun _ => (0 : ℝ) := by
      funext k
      exact killedHeat_of_target_not_mem (by exact_mod_cast hv) k x
    rw [this]
    exact summable_zero

/-- The survival probability is summable in the time, from escape alone; its
sum is at most `N / (1 - θ)` for the uniform contraction of
`exists_uniform_survival_le_of_escape`. -/
theorem summable_survival_of_escape
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ C) (x : V) :
    Summable (fun k => survival G C k x) := by
  obtain ⟨N, θ, hN, hθ0, hθ1, hθ⟩ := exists_uniform_survival_le_of_escape C hesc
  exact summable_of_sum_range_le (c := (N : ℝ) / (1 - θ))
    (fun k => survival_nonneg C k x) (fun n => sum_range_survival_le hN hθ0 hθ1 hθ x n)

/-- The survival probability tends to zero: the walk leaves `C`. -/
theorem tendsto_survival_atTop_zero
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ C) (x : V) :
    Filter.Tendsto (fun k => survival G C k x) Filter.atTop (nhds 0) :=
  (summable_survival_of_escape C hesc x).tendsto_atTop_zero

/-- The killed Green function is the sum of the local times over the degree of
the target, from escape alone. -/
theorem killedGreenReal_eq_tsum_of_escape
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ C) (x v : V) :
    killedGreenReal G (C : Set V) x v
      = (∑' k : ℕ, killedHeat G (C : Set V) k x v) / G.degree v := by
  have hsum := summable_killedHeat_of_escape C hesc x v
  have hnn : ∀ k, 0 ≤ killedHeat G (C : Set V) k x v := fun k => killedHeat_nonneg _ k x v
  have h1 : (∑' k : ℕ, ENNReal.ofReal (killedHeat G (C : Set V) k x v))
      = ENNReal.ofReal (∑' k : ℕ, killedHeat G (C : Set V) k x v) :=
    (ENNReal.ofReal_tsum_of_nonneg hnn hsum).symm
  rw [killedGreenReal, killedGreen, h1, ENNReal.toReal_div,
    ENNReal.toReal_ofReal (tsum_nonneg hnn), ENNReal.toReal_natCast]

/-- The killed Green function vanishes off `C`, from escape alone. -/
theorem killedGreenReal_eq_zero_of_not_mem_of_escape
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ C) {v : V} (hv : v ∉ C) (x : V) :
    killedGreenReal G (C : Set V) x v = 0 := by
  rw [killedGreenReal_eq_tsum_of_escape C hesc x v]
  have : (fun k => killedHeat G (C : Set V) k x v) = fun _ => (0 : ℝ) := by
    funext k
    exact killedHeat_of_target_not_mem (by exact_mod_cast hv) k x
  rw [this, tsum_zero, zero_div]

theorem killedGreenReal_nonneg_of_escape
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ C) (x v : V) :
    0 ≤ killedGreenReal G (C : Set V) x v := by
  rw [killedGreenReal_eq_tsum_of_escape C hesc x v]
  exact div_nonneg (tsum_nonneg fun k => killedHeat_nonneg _ k x v) (Nat.cast_nonneg _)

/-- The killed Green function is symmetric, from escape alone. -/
theorem killedGreenReal_symm_of_escape
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ C) (x v : V) :
    killedGreenReal G (C : Set V) x v = killedGreenReal G (C : Set V) v x := by
  rw [killedGreenReal_eq_tsum_of_escape C hesc x v,
    killedGreenReal_eq_tsum_of_escape C hesc v x, ← tsum_div_const, ← tsum_div_const]
  exact tsum_congr fun k => killedKer_symm (G := G) (C : Set V) k x v

/-- The killed Green function in the reversed form, from escape alone. -/
theorem killedGreenReal_eq_reversed_of_escape
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ C) (x v : V) :
    killedGreenReal G (C : Set V) x v
      = (∑' k : ℕ, killedHeat G (C : Set V) k v x) / G.degree x := by
  rw [killedGreenReal_symm_of_escape C hesc x v,
    killedGreenReal_eq_tsum_of_escape C hesc v x]

/-- The neighbour sum of the reversed local times, from the defining recursion,
under escape and the absence of isolated vertices in `C`. -/
theorem sum_tsum_killedHeat_of_escape
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ C)
    (hdeg : ∀ v ∈ C, 0 < G.degree v) (x : V) {v : V} (hv : v ∈ C) :
    ∑ w ∈ G.neighborFinset v, (∑' k : ℕ, killedHeat G (C : Set V) k w x)
      = (G.degree v : ℝ) *
          ((∑' k : ℕ, killedHeat G (C : Set V) k v x)
            - killedHeat G (C : Set V) 0 v x) := by
  have hdv : 0 < G.degree v := hdeg v hv
  have hsum : ∀ w : V, Summable (fun k => killedHeat G (C : Set V) k w x) :=
    fun w => summable_killedHeat_of_escape C hesc w x
  have hex : ∑ w ∈ G.neighborFinset v, (∑' k : ℕ, killedHeat G (C : Set V) k w x)
      = ∑' k : ℕ, ∑ w ∈ G.neighborFinset v, killedHeat G (C : Set V) k w x :=
    (Summable.tsum_finsetSum (fun w _ => hsum w)).symm
  have hstep : ∀ k : ℕ, ∑ w ∈ G.neighborFinset v, killedHeat G (C : Set V) k w x
      = (G.degree v : ℝ) * killedHeat G (C : Set V) (k + 1) v x := by
    intro k
    rw [killedHeat_succ, if_pos (by exact_mod_cast hv : v ∈ (C : Set V)),
      mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr hdv.ne')]
  rw [hex, tsum_congr hstep, tsum_mul_left, (hsum v).tsum_eq_zero_add]
  ring

/-- **The boundary value problem `eq:gC-PDE`, without connectivity.**  Inside
`C`, the Laplacian of `g_C(o,·)` is `-1` at the source and `0` elsewhere. -/
theorem laplacian_killedGreenReal_of_escape
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ C)
    (hdeg : ∀ v ∈ C, 0 < G.degree v) {o : V} (ho : o ∈ C) {v : V} (hv : v ∈ C) :
    laplacian G (killedGreenReal G (C : Set V) o) v
      = -(if v = o then (1 : ℝ) else 0) := by
  classical
  have hdo : 0 < G.degree o := hdeg o ho
  have hdoR : (G.degree o : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hdo.ne'
  have hu : ∀ w : V, killedGreenReal G (C : Set V) o w
      = (∑' k : ℕ, killedHeat G (C : Set V) k w o) / (G.degree o : ℝ) :=
    fun w => killedGreenReal_eq_reversed_of_escape C hesc o w
  have hsum := sum_tsum_killedHeat_of_escape C hesc hdeg o hv
  have hzero : killedHeat G (C : Set V) 0 v o = if v = o then (1 : ℝ) else 0 := by
    rw [killedHeat_zero, if_pos (by exact_mod_cast hv : v ∈ (C : Set V))]
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

/-- The killed Green function is harmonic on `C` away from the source, without
connectivity. -/
theorem harmonic_killedGreenReal_of_escape
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ C)
    (hdeg : ∀ v ∈ C, 0 < G.degree v) {o : V} (ho : o ∈ C) {v : V} (hv : v ∈ C)
    (hvo : v ≠ o) :
    laplacian G (killedGreenReal G (C : Set V) o) v = 0 := by
  rw [laplacian_killedGreenReal_of_escape C hesc hdeg ho hv, if_neg hvo]
  norm_num

/-- The unit source at `o`, without connectivity. -/
theorem laplacian_killedGreenReal_source_of_escape
    (hesc : ∀ x : V, ∃ (q : V) (_ : G.Walk x q), q ∉ C)
    (hdeg : ∀ v ∈ C, 0 < G.degree v) {o : V} (ho : o ∈ C) :
    laplacian G (killedGreenReal G (C : Set V) o) o = -1 := by
  rw [laplacian_killedGreenReal_of_escape C hesc hdeg ho ho, if_pos rfl]

end LatticeProb.Network
