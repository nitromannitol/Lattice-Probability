/-
The `n`-step transition probability of the walk on an infinite connected graph
tends to zero, for every pair of vertices.  No bound on the degrees is
needed: the on-diagonal bound is applied at the fixed starting vertex, where the
degree is a constant.

The proof is Cauchy-Schwarz against the on-diagonal bound: writing
`u_n(y) = p_n(x,y)/deg(y)`, the degree-weighted inner product of `u_n` with the
density of the walk started at `v` and stopped at time zero is `p_n(x,v)/deg(v)`,
so that quantity is at most `√(p_{2n}(x,x)/deg(x)) √(1/deg(v))`, and the first
factor tends to zero by `spectralDimensionBound_of_boundedDegree`.

The last section shows that the hypotheses are not decoration: on the perfect
matching of `ℕ × Bool`, an infinite locally finite graph of degree one whose
components are single edges, the walk is back at its starting vertex at every
even time, so the return probability does not tend to zero.
-/
import LatticeProb.Graph.OnDiagonal

open scoped Classical
open Filter Topology

namespace LatticeProb.Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

theorem sum_degree_mul_le (T : Finset V) (p q : V → ℝ) :
    ∑ y ∈ T, (G.degree y : ℝ) * p y * q y
      ≤ Real.sqrt (∑ y ∈ T, (G.degree y : ℝ) * p y * p y)
        * Real.sqrt (∑ y ∈ T, (G.degree y : ℝ) * q y * q y) := by
  have hd : ∀ y : V, Real.sqrt (G.degree y : ℝ) * Real.sqrt (G.degree y : ℝ) = (G.degree y : ℝ) :=
    fun y => Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt T (fun y => Real.sqrt (G.degree y : ℝ) * p y)
    (fun y => Real.sqrt (G.degree y : ℝ) * q y)
  have e1 : ∀ y : V, (Real.sqrt (G.degree y : ℝ) * p y) * (Real.sqrt (G.degree y : ℝ) * q y)
      = (G.degree y : ℝ) * p y * q y := by
    intro y
    rw [show (Real.sqrt (G.degree y : ℝ) * p y) * (Real.sqrt (G.degree y : ℝ) * q y)
      = (Real.sqrt (G.degree y : ℝ) * Real.sqrt (G.degree y : ℝ)) * (p y * q y) by ring, hd y]
    ring
  have e2 : ∀ y : V, (Real.sqrt (G.degree y : ℝ) * p y) ^ 2 = (G.degree y : ℝ) * p y * p y := by
    intro y; rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; ring
  have e3 : ∀ y : V, (Real.sqrt (G.degree y : ℝ) * q y) ^ 2 = (G.degree y : ℝ) * q y * q y := by
    intro y; rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; ring
  simpa only [e1, e2, e3] using hcs

/-- Cauchy-Schwarz for the transition kernel: the kernel at time `a + b` is
controlled by the return probabilities at times `2a` and `2b`. -/
theorem heat_div_le_sqrt_two_time [Infinite V] (hG : G.Connected) (a b : ℕ) (x v : V) :
    heat G (a + b) x v / (G.degree v : ℝ)
      ≤ Real.sqrt (heat G (a + a) x x / (G.degree x : ℝ))
        * Real.sqrt (heat G (b + b) v v / (G.degree v : ℝ)) := by
  have hdeg : ∀ w : V, 0 < G.degree w := fun w => degree_pos hG w
  set T : Finset V := reach G a x ∪ reach G b v with hTdef
  have hTa : reach G a x ⊆ T := Finset.subset_union_left
  have hTb : reach G b v ⊆ T := Finset.subset_union_right
  have key := sum_degree_mul_le (G := G) T (fun y => heat G a x y / (G.degree y : ℝ))
    (fun y => heat G b v y / (G.degree y : ℝ))
  rw [sum_degree_heat_mul hdeg a b x v T hTa, sum_degree_heat_mul hdeg a a x x T hTa,
    sum_degree_heat_mul hdeg b b v v T hTb] at key
  exact key

/-- The transition probability is controlled by the return probability at twice
the time. -/
theorem heat_div_le_sqrt [Infinite V] (hG : G.Connected) (n : ℕ) (x v : V) :
    heat G n x v / (G.degree v : ℝ)
      ≤ Real.sqrt (heat G (n + n) x x / (G.degree x : ℝ))
        * Real.sqrt (1 / (G.degree v : ℝ)) := by
  have h := heat_div_le_sqrt_two_time hG n 0 x v
  have h0 : heat G (0 + 0) v v = 1 := by simp [heat]
  rw [h0] at h
  simpa using h

/-- The off-diagonal bound at even times: `p_{2a}(x,y) ≤ deg(y) √(128/a)`. -/
theorem heat_even_offdiag_le [Infinite V] (hG : G.Connected) {a : ℕ} (ha : 1 ≤ a) (x y : V) :
    heat G (a + a) x y ≤ (G.degree y : ℝ) * Real.sqrt (128 / (a : ℝ)) := by
  have hdeg : ∀ w : V, 0 < G.degree w := fun w => degree_pos hG w
  have hdy : (0:ℝ) < (G.degree y : ℝ) := Nat.cast_pos.mpr (hdeg y)
  have hdx : (0:ℝ) < (G.degree x : ℝ) := Nat.cast_pos.mpr (hdeg x)
  have hx : heat G (a + a) x x / (G.degree x : ℝ) ≤ Real.sqrt (128 / (a : ℝ)) := by
    rw [div_le_iff₀ hdx]
    have := heat_even_le hG x ha
    linarith [this]
  have hy : heat G (a + a) y y / (G.degree y : ℝ) ≤ Real.sqrt (128 / (a : ℝ)) := by
    rw [div_le_iff₀ hdy]
    have := heat_even_le hG y ha
    linarith [this]
  have hs : Real.sqrt (heat G (a + a) x x / (G.degree x : ℝ))
      * Real.sqrt (heat G (a + a) y y / (G.degree y : ℝ)) ≤ Real.sqrt (128 / (a : ℝ)) := by
    have h1 : Real.sqrt (heat G (a + a) x x / (G.degree x : ℝ))
        ≤ Real.sqrt (Real.sqrt (128 / (a : ℝ))) := Real.sqrt_le_sqrt hx
    have h2 : Real.sqrt (heat G (a + a) y y / (G.degree y : ℝ))
        ≤ Real.sqrt (Real.sqrt (128 / (a : ℝ))) := Real.sqrt_le_sqrt hy
    have hnn : (0:ℝ) ≤ Real.sqrt (Real.sqrt (128 / (a : ℝ))) := Real.sqrt_nonneg _
    calc Real.sqrt (heat G (a + a) x x / (G.degree x : ℝ))
          * Real.sqrt (heat G (a + a) y y / (G.degree y : ℝ))
        ≤ Real.sqrt (Real.sqrt (128 / (a : ℝ))) * Real.sqrt (Real.sqrt (128 / (a : ℝ))) :=
          mul_le_mul h1 h2 (Real.sqrt_nonneg _) hnn
      _ = Real.sqrt (128 / (a : ℝ)) := Real.mul_self_sqrt (Real.sqrt_nonneg _)
  have h := le_trans (heat_div_le_sqrt_two_time hG a a x y) hs
  rw [div_le_iff₀ hdy] at h
  calc heat G (a + a) x y ≤ Real.sqrt (128 / (a : ℝ)) * (G.degree y : ℝ) := h
    _ = (G.degree y : ℝ) * Real.sqrt (128 / (a : ℝ)) := by ring

theorem heat_tendsto_zero [Infinite V] (hG : G.Connected) (x v : V) :
    Tendsto (fun n : ℕ => heat G n x v) atTop (𝓝 0) := by
  have hdeg : ∀ w : V, 0 < G.degree w := fun w => degree_pos hG w
  have hdv : (0:ℝ) < (G.degree v : ℝ) := Nat.cast_pos.mpr (hdeg v)
  -- the return probability at even times tends to zero
  have hinv : Tendsto (fun n : ℕ => 128 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hmaj2 : Tendsto (fun n : ℕ => (G.degree x : ℝ) * Real.sqrt (128 / (n : ℝ)))
      atTop (𝓝 0) := by
    have h := (hinv.sqrt).const_mul ((G.degree x : ℝ))
    rw [Real.sqrt_zero, mul_zero] at h
    exact h
  have hdiag : Tendsto (fun n : ℕ => heat G (n + n) x x) atTop (𝓝 0) := by
    refine squeeze_zero' (g := fun n : ℕ => (G.degree x : ℝ) * Real.sqrt (128 / (n : ℝ)))
      (Eventually.of_forall fun n => heat_nonneg _ x x) ?_ hmaj2
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact heat_even_le hG x hn
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (heat G (n + n) x x / (G.degree x : ℝ)))
      atTop (𝓝 0) := by
    have h := (hdiag.div_const ((G.degree x : ℝ))).sqrt
    rw [zero_div, Real.sqrt_zero] at h
    exact h
  set c : ℝ := (G.degree v : ℝ) * Real.sqrt (1 / (G.degree v : ℝ)) with hc
  have hmaj : Tendsto (fun n : ℕ => Real.sqrt (heat G (n + n) x x / (G.degree x : ℝ)) * c)
      atTop (𝓝 0) := by
    have h := hsqrt.mul_const c
    rw [zero_mul] at h
    exact h
  refine squeeze_zero (fun n => heat_nonneg _ x v) (fun n => ?_) hmaj
  have h := heat_div_le_sqrt hG n x v
  rw [div_le_iff₀ hdv] at h
  calc heat G n x v ≤ Real.sqrt (heat G (n + n) x x / (G.degree x : ℝ))
        * Real.sqrt (1 / (G.degree v : ℝ)) * (G.degree v : ℝ) := h
    _ = Real.sqrt (heat G (n + n) x x / (G.degree x : ℝ)) * c := by rw [hc]; ring

/-! ### The hypotheses are needed

On an infinite locally finite graph with a finite connected component the
`n`-step return probability need not tend to zero.  The perfect matching on
`ℕ × Bool`, which joins `(n,b)` to `(n, !b)` and nothing else, is infinite and
has all degrees equal to one, and the walk from any vertex is at that vertex at
every even time. -/

/-- The perfect matching on `ℕ × Bool`. -/
def matchingGraph : SimpleGraph (ℕ × Bool) :=
  SimpleGraph.fromRel (fun p q => p.1 = q.1)

theorem matchingGraph_adj_iff (p q : ℕ × Bool) :
    matchingGraph.Adj p q ↔ q = (p.1, !p.2) := by
  rw [matchingGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨hne, h1⟩
    have h1' : p.1 = q.1 := by rcases h1 with h | h
                               · exact h
                               · exact h.symm
    refine Prod.ext h1'.symm ?_
    have h2 : p.2 ≠ q.2 := by
      intro h2
      exact hne (Prod.ext h1' h2)
    revert h2
    cases hp : p.2 <;> cases hq : q.2 <;> simp
  · rintro rfl
    refine ⟨?_, Or.inl rfl⟩
    intro h
    have := congrArg Prod.snd h
    simp at this

instance : matchingGraph.LocallyFinite := by
  intro p
  have hset : matchingGraph.neighborSet p = {(p.1, !p.2)} := by
    ext q
    rw [SimpleGraph.mem_neighborSet, matchingGraph_adj_iff]
    simp
  rw [hset]
  infer_instance

theorem matchingGraph_neighborFinset (p : ℕ × Bool) :
    matchingGraph.neighborFinset p = {(p.1, !p.2)} := by
  ext q
  rw [SimpleGraph.mem_neighborFinset, matchingGraph_adj_iff, Finset.mem_singleton]

theorem matchingGraph_degree (p : ℕ × Bool) : matchingGraph.degree p = 1 := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, matchingGraph_neighborFinset,
    Finset.card_singleton]

theorem heat_matchingGraph_succ (k : ℕ) (p q : ℕ × Bool) :
    heat matchingGraph (k + 1) p q = heat matchingGraph k (p.1, !p.2) q := by
  rw [heat_succ, walkOp, matchingGraph_neighborFinset, Finset.sum_singleton,
    matchingGraph_degree]
  norm_num

theorem heat_matchingGraph_even (p : ℕ × Bool) :
    ∀ n : ℕ, heat matchingGraph (2 * n) p p = 1 := by
  intro n
  induction n generalizing p with
  | zero => simp [heat]
  | succ n ih =>
      have harith : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
      rw [harith, heat_matchingGraph_succ, heat_matchingGraph_succ]
      have hflip : ((p.1, !p.2).1, !(p.1, !p.2).2) = p := by
        simp
      rw [hflip]
      exact ih p

/-- The return probability of the walk on an infinite locally finite graph need
not tend to zero: the frozen statement of the cited input is false without a
hypothesis making the component of the starting vertex infinite. -/
theorem not_heat_tendsto_zero :
    ¬ ∀ x v : ℕ × Bool, Tendsto (fun n : ℕ => heat matchingGraph n x v) atTop (𝓝 0) := by
  intro h
  have hx := h (0, false) (0, false)
  have hsub : Tendsto (fun n : ℕ => heat matchingGraph (2 * n) (0, false) (0, false))
      atTop (𝓝 0) := by
    refine hx.comp ?_
    exact tendsto_atTop_mono (fun n => by simp only [id_eq]; omega) tendsto_id
  have hone : (fun n : ℕ => heat matchingGraph (2 * n) (0, false) (0, false)) = fun _ => (1:ℝ) :=
    funext fun n => heat_matchingGraph_even (0, false) n
  rw [hone] at hsub
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hsub)

end LatticeProb.Graph
