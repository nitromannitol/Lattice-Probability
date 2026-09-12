/-
The on-diagonal heat kernel bound of spectral dimension one: on an infinite
connected graph of degree bounded by `d`,

  p_n(x,x) ≤ 32 d n^{-1/2}   for every vertex `x` and every `n ≥ 1`.

The proof is the Nash iteration.  Write `u_n(y) = p_n(x,y)/deg(y)` for the
transition density of the walk from `x` against the degree measure and
`s_n = ∑_y deg(y) u_n(y)^2 = p_{2n}(x,x)/deg(x)`.  The Nash inequality of
`LatticeProb/Graph/Nash.lean` is applied not to `u_n` but to `f = u_n + u_{n+1}`,
whose `L^1` norm is `2`: the Dirichlet form of `f` is
`(s_n + 2 t_n + s_{n+1}) - (t_n + 2 s_{n+1} + t_{n+1})` in the return
probabilities `s_n = p_{2n}(x,x)/deg(x)`, `t_n = p_{2n+1}(x,x)/deg(x)`, and the
companion form at `g = u_n - u_{n+1}`, which is a sum of squares and hence
nonnegative, is exactly the inequality `t_n + s_{n+1} ≤ s_n + t_{n+1}` needed to
turn that combination into `2 (s_n - s_{n+1})`.  This is what replaces the
spectral theorem: on a bipartite graph the Dirichlet form of `u_n` alone carries
no decay, because the odd return probabilities vanish.

Nash then gives `s_n - s_{n+1} ≥ s_n^3/256`, and a nonnegative sequence with
that property satisfies `2 c n s_n^2 ≤ 1`, so `s_n ≤ √(128/n)`.  The odd times
are reached by `p_{2j+1}(x,x) ≤ p_{2j}(x,x)`, which is the arithmetic-geometric
mean inequality applied to `u_j` and `u_{j+1}` together with the monotonicity of
the even return probabilities.

No bound on the degrees enters before the last step, where `deg(x) ≤ d` turns
the density `s_n` back into a probability.
-/
import LatticeProb.Graph.Nash

open scoped Classical

namespace LatticeProb.Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

theorem walkOp_heat_div (n : ℕ) (x y : V) :
    walkOp G (fun z => heat G n x z / (G.degree z : ℝ)) y
      = heat G (n + 1) x y / (G.degree y : ℝ) := by
  rw [walkOp, ← heat_forward]

theorem walkOp_add (g h : V → ℝ) (y : V) :
    walkOp G (fun z => g z + h z) y = walkOp G g y + walkOp G h y := by
  rw [walkOp, walkOp, walkOp, Finset.sum_add_distrib, add_div]

theorem walkOp_sub (g h : V → ℝ) (y : V) :
    walkOp G (fun z => g z - h z) y = walkOp G g y - walkOp G h y := by
  rw [walkOp, walkOp, walkOp, Finset.sum_sub_distrib, sub_div]

/-- The window carrying the support of `p_n(x,·) + p_{n+1}(x,·)` and its neighbours. -/
noncomputable def window (G : SimpleGraph V) [G.LocallyFinite] (n : ℕ) (x : V) : Finset V :=
  ((reach G n x) ∪ (reach G (n + 1) x)).biUnion (fun y => insert y (G.neighborFinset y))

theorem reach_subset_window {n m : ℕ} (x : V) (hm : m = n ∨ m = n + 1) :
    reach G m x ⊆ window G n x := by
  intro y hy
  rw [window, Finset.mem_biUnion]
  refine ⟨y, ?_, Finset.mem_insert_self _ _⟩
  rcases hm with h | h
  · exact Finset.mem_union_left _ (h ▸ hy)
  · exact Finset.mem_union_right _ (h ▸ hy)

theorem mem_window_of_heat {n : ℕ} {x y : V}
    (hy : heat G n x y ≠ 0 ∨ heat G (n + 1) x y ≠ 0) : y ∈ window G n x := by
  rcases hy with h | h
  · exact reach_subset_window x (Or.inl rfl)
      (by by_contra hc; exact h (heat_eq_zero_of_notMem_reach n x y hc))
  · exact reach_subset_window x (Or.inr rfl)
      (by by_contra hc; exact h (heat_eq_zero_of_notMem_reach (n + 1) x y hc))

theorem mem_window_of_adj {n : ℕ} {x y v : V}
    (hy : heat G n x y ≠ 0 ∨ heat G (n + 1) x y ≠ 0) (hadj : G.Adj y v) :
    v ∈ window G n x := by
  have hyw : y ∈ (reach G n x) ∪ (reach G (n + 1) x) := by
    rcases hy with h | h
    · exact Finset.mem_union_left _
        (by by_contra hc; exact h (heat_eq_zero_of_notMem_reach n x y hc))
    · exact Finset.mem_union_right _
        (by by_contra hc; exact h (heat_eq_zero_of_notMem_reach (n + 1) x y hc))
  rw [window, Finset.mem_biUnion]
  exact ⟨y, hyw, Finset.mem_insert_of_mem ((SimpleGraph.mem_neighborFinset _ _ _).2 hadj)⟩


theorem heat_step [Infinite V] (hG : G.Connected) (x : V) (n : ℕ) :
    heat G (n + 1 + (n + 1)) x x / (G.degree x : ℝ)
      ≤ heat G (n + n) x x / (G.degree x : ℝ)
        - (1 / 256) * (heat G (n + n) x x / (G.degree x : ℝ)) ^ 3 := by
  classical
  have hdeg : ∀ v : V, 0 < G.degree v := fun v => degree_pos hG v
  set T := window G n x with hTdef
  set u : ℕ → V → ℝ := fun m y => heat G m x y / (G.degree y : ℝ) with hudef
  set f : V → ℝ := fun y => u n y + u (n + 1) y with hfdef
  set g : V → ℝ := fun y => u n y - u (n + 1) y with hgdef
  have hunn : ∀ (m : ℕ) (y : V), 0 ≤ u m y := fun m y =>
    div_nonneg (heat_nonneg m x y) (Nat.cast_nonneg _)
  have hfnn : ∀ y, 0 ≤ f y := fun y => by rw [hfdef]; exact add_nonneg (hunn n y) (hunn (n+1) y)
  have hTf : ∀ y, f y ≠ 0 → y ∈ T := by
    intro y hy
    by_cases h1 : heat G n x y = 0
    · by_cases h2 : heat G (n + 1) x y = 0
      · exact absurd (by simp [hfdef, hudef, h1, h2] : f y = 0) hy
      · exact mem_window_of_heat (Or.inr h2)
    · exact mem_window_of_heat (Or.inl h1)
  have hTNf : ∀ y v : V, f y ≠ 0 → G.Adj y v → v ∈ T := by
    intro y v hy hadj
    by_cases h1 : heat G n x y = 0
    · by_cases h2 : heat G (n + 1) x y = 0
      · exact absurd (by simp [hfdef, hudef, h1, h2] : f y = 0) hy
      · exact mem_window_of_adj (Or.inr h2) hadj
    · exact mem_window_of_adj (Or.inl h1) hadj
  have hTg : ∀ y, g y ≠ 0 → y ∈ T := by
    intro y hy
    by_cases h1 : heat G n x y = 0
    · by_cases h2 : heat G (n + 1) x y = 0
      · exact absurd (by simp [hgdef, hudef, h1, h2] : g y = 0) hy
      · exact mem_window_of_heat (Or.inr h2)
    · exact mem_window_of_heat (Or.inl h1)
  have hTNg : ∀ y v : V, g y ≠ 0 → G.Adj y v → v ∈ T := by
    intro y v hy hadj
    by_cases h1 : heat G n x y = 0
    · by_cases h2 : heat G (n + 1) x y = 0
      · exact absurd (by simp [hgdef, hudef, h1, h2] : g y = 0) hy
      · exact mem_window_of_adj (Or.inr h2) hadj
    · exact mem_window_of_adj (Or.inl h1) hadj
  -- the degree-weighted products are return probabilities
  have hF : ∀ (m k : ℕ), (m = n ∨ m = n + 1) →
      ∑ y ∈ T, (G.degree y : ℝ) * u m y * u k y = heat G (m + k) x x / (G.degree x : ℝ) := by
    intro m k hm
    exact sum_degree_heat_mul hdeg m k x x T (reach_subset_window x hm)
  have e1 : n + (n + 1) = n + n + 1 := by omega
  have e2 : n + 1 + n = n + n + 1 := by omega
  have e3 : n + 1 + (n + 1) = n + n + 2 := by omega
  have e4 : n + (n + 2) = n + n + 2 := by omega
  have e5 : n + 1 + (n + 2) = n + n + 3 := by omega
  set a0 := heat G (n + n) x x / (G.degree x : ℝ) with ha0
  set a1 := heat G (n + n + 1) x x / (G.degree x : ℝ) with ha1
  set a2 := heat G (n + n + 2) x x / (G.degree x : ℝ) with ha2
  set a3 := heat G (n + n + 3) x x / (G.degree x : ℝ) with ha3
  have hA : ∑ y ∈ T, (G.degree y : ℝ) * f y ^ 2 = a0 + 2 * a1 + a2 := by
    have expand : ∀ y ∈ T, (G.degree y : ℝ) * f y ^ 2
        = (G.degree y : ℝ) * u n y * u n y + (G.degree y : ℝ) * u n y * u (n + 1) y
          + ((G.degree y : ℝ) * u (n + 1) y * u n y
            + (G.degree y : ℝ) * u (n + 1) y * u (n + 1) y) := by
      intro y _; rw [hfdef]; ring
    rw [Finset.sum_congr rfl expand, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, hF n n (Or.inl rfl), hF n (n + 1) (Or.inl rfl),
      hF (n + 1) n (Or.inr rfl), hF (n + 1) (n + 1) (Or.inr rfl), e1, e2, e3]
    ring
  have hwf : ∀ y, walkOp G f y = u (n + 1) y + u (n + 2) y := by
    intro y
    rw [hfdef, walkOp_add, walkOp_heat_div, walkOp_heat_div]
  have hWf : ∑ y ∈ T, (G.degree y : ℝ) * f y * walkOp G f y = a1 + 2 * a2 + a3 := by
    have expand : ∀ y ∈ T, (G.degree y : ℝ) * f y * walkOp G f y
        = (G.degree y : ℝ) * u n y * u (n + 1) y + (G.degree y : ℝ) * u n y * u (n + 2) y
          + ((G.degree y : ℝ) * u (n + 1) y * u (n + 1) y
            + (G.degree y : ℝ) * u (n + 1) y * u (n + 2) y) := by
      intro y _; rw [hwf y, hfdef]; ring
    rw [Finset.sum_congr rfl expand, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, hF n (n + 1) (Or.inl rfl), hF n (n + 2) (Or.inl rfl),
      hF (n + 1) (n + 1) (Or.inr rfl), hF (n + 1) (n + 2) (Or.inr rfl), e1, e3, e4, e5]
    ring
  have hM : ∑ y ∈ T, (G.degree y : ℝ) * f y = 2 := by
    have hone : ∀ m : ℕ, (m = n ∨ m = n + 1) → ∑ y ∈ T, (G.degree y : ℝ) * u m y = 1 := by
      intro m hm
      have hcast : ∀ y ∈ T, (G.degree y : ℝ) * u m y = heat G m x y := by
        intro y _
        have hy : (G.degree y : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hdeg y).ne'
        rw [hudef]
        field_simp
      rw [Finset.sum_congr rfl hcast, ← sum_heat_eq_one hdeg m x]
      exact (Finset.sum_subset (reach_subset_window x hm)
        (fun y _ hy => heat_eq_zero_of_notMem_reach m x y hy)).symm
    have expand : ∀ y ∈ T, (G.degree y : ℝ) * f y
        = (G.degree y : ℝ) * u n y + (G.degree y : ℝ) * u (n + 1) y := by
      intro y _; rw [hfdef]; ring
    rw [Finset.sum_congr rfl expand, Finset.sum_add_distrib, hone n (Or.inl rfl),
      hone (n + 1) (Or.inr rfl)]
    norm_num
  -- the companion form at the difference gives the four-term inequality
  have hanti : 0 ≤ a0 - a1 - a2 + a3 := by
    have h0 : (0:ℝ) ≤ ∑ y ∈ T, ∑ v ∈ G.neighborFinset y, (g y + g v) ^ 2 :=
      Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun v _ => sq_nonneg _
    rw [sum_sq_add_eq g T hTg hTNg, ← sum_degree_mul_walkOp hdeg g T] at h0
    have hAg : ∑ y ∈ T, (G.degree y : ℝ) * g y ^ 2 = a0 - 2 * a1 + a2 := by
      have expand : ∀ y ∈ T, (G.degree y : ℝ) * g y ^ 2
          = (G.degree y : ℝ) * u n y * u n y - (G.degree y : ℝ) * u n y * u (n + 1) y
            - ((G.degree y : ℝ) * u (n + 1) y * u n y
              - (G.degree y : ℝ) * u (n + 1) y * u (n + 1) y) := by
        intro y _; rw [hgdef]; ring
      rw [Finset.sum_congr rfl expand, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        Finset.sum_sub_distrib, hF n n (Or.inl rfl), hF n (n + 1) (Or.inl rfl),
        hF (n + 1) n (Or.inr rfl), hF (n + 1) (n + 1) (Or.inr rfl), e1, e2, e3]
      ring
    have hwg : ∀ y, walkOp G g y = u (n + 1) y - u (n + 2) y := by
      intro y
      rw [hgdef, walkOp_sub, walkOp_heat_div, walkOp_heat_div]
    have hWg : ∑ y ∈ T, (G.degree y : ℝ) * g y * walkOp G g y = a1 - 2 * a2 + a3 := by
      have expand : ∀ y ∈ T, (G.degree y : ℝ) * g y * walkOp G g y
          = (G.degree y : ℝ) * u n y * u (n + 1) y - (G.degree y : ℝ) * u n y * u (n + 2) y
            - ((G.degree y : ℝ) * u (n + 1) y * u (n + 1) y
              - (G.degree y : ℝ) * u (n + 1) y * u (n + 2) y) := by
        intro y _; rw [hwg y, hgdef]; ring
      rw [Finset.sum_congr rfl expand, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
        Finset.sum_sub_distrib, hF n (n + 1) (Or.inl rfl), hF n (n + 2) (Or.inl rfl),
        hF (n + 1) (n + 1) (Or.inr rfl), hF (n + 1) (n + 2) (Or.inr rfl), e1, e3, e4, e5]
      ring
    rw [hAg, hWg] at h0
    linarith
  -- Nash
  have hnash := nash_ineq hG hdeg f hfnn T hTf hTNf
  rw [hA, hM, hWf] at hnash
  have ha0nn : 0 ≤ a0 := div_nonneg (heat_nonneg _ x x) (Nat.cast_nonneg _)
  have ha1nn : 0 ≤ a1 := div_nonneg (heat_nonneg _ x x) (Nat.cast_nonneg _)
  have ha2nn : 0 ≤ a2 := div_nonneg (heat_nonneg _ x x) (Nat.cast_nonneg _)
  have hcube : a0 ^ 3 ≤ (a0 + 2 * a1 + a2) ^ 3 := by
    have : a0 ≤ a0 + 2 * a1 + a2 := by linarith
    exact pow_le_pow_left₀ ha0nn this 3
  rw [e3]
  nlinarith [hnash, hcube, hanti]


theorem heat_odd_le [Infinite V] (hG : G.Connected) (x : V) (j : ℕ) :
    heat G (j + j + 1) x x / (G.degree x : ℝ) ≤ heat G (j + j) x x / (G.degree x : ℝ) := by
  classical
  have hdeg : ∀ v : V, 0 < G.degree v := fun v => degree_pos hG v
  set T := window G j x with hTdef
  set u : ℕ → V → ℝ := fun m y => heat G m x y / (G.degree y : ℝ) with hudef
  have hF : ∀ (m k : ℕ), (m = j ∨ m = j + 1) →
      ∑ y ∈ T, (G.degree y : ℝ) * u m y * u k y = heat G (m + k) x x / (G.degree x : ℝ) := by
    intro m k hm
    exact sum_degree_heat_mul hdeg m k x x T (reach_subset_window x hm)
  have e1 : j + (j + 1) = j + j + 1 := by omega
  have e3 : j + 1 + (j + 1) = j + j + 2 := by omega
  have hmid : heat G (j + j + 1) x x / (G.degree x : ℝ)
      ≤ (heat G (j + j) x x / (G.degree x : ℝ)
          + heat G (j + j + 2) x x / (G.degree x : ℝ)) / 2 := by
    have hle : ∑ y ∈ T, (G.degree y : ℝ) * u j y * u (j + 1) y
        ≤ ∑ y ∈ T, ((G.degree y : ℝ) * u j y * u j y
            + (G.degree y : ℝ) * u (j + 1) y * u (j + 1) y) / 2 := by
      refine Finset.sum_le_sum fun y _ => ?_
      have hd : (0:ℝ) ≤ (G.degree y : ℝ) := Nat.cast_nonneg _
      nlinarith [sq_nonneg (u j y - u (j + 1) y), hd]
    rw [hF j (j + 1) (Or.inl rfl), e1] at hle
    have hsplit : ∑ y ∈ T, ((G.degree y : ℝ) * u j y * u j y
        + (G.degree y : ℝ) * u (j + 1) y * u (j + 1) y) / 2
        = (heat G (j + j) x x / (G.degree x : ℝ)
            + heat G (j + j + 2) x x / (G.degree x : ℝ)) / 2 := by
      rw [show (∑ y ∈ T, ((G.degree y : ℝ) * u j y * u j y
          + (G.degree y : ℝ) * u (j + 1) y * u (j + 1) y) / 2)
          = (∑ y ∈ T, ((G.degree y : ℝ) * u j y * u j y
            + (G.degree y : ℝ) * u (j + 1) y * u (j + 1) y)) / 2 from (Finset.sum_div _ _ _).symm]
      rw [Finset.sum_add_distrib, hF j j (Or.inl rfl), hF (j + 1) (j + 1) (Or.inr rfl), e3]
    rw [hsplit] at hle
    exact hle
  have hstep := heat_step hG x j
  rw [e3] at hstep
  have ha0nn : 0 ≤ heat G (j + j) x x / (G.degree x : ℝ) :=
    div_nonneg (heat_nonneg _ x x) (Nat.cast_nonneg _)
  nlinarith [hmid, hstep, ha0nn, pow_nonneg ha0nn 3]


/-- A nonnegative sequence that drops by a fixed multiple of its cube at every
step is of order `n^{-1/2}`. -/
theorem sq_le_of_cube_step (c : ℝ) (hc : 0 < c) (s : ℕ → ℝ) (hs : ∀ n, 0 ≤ s n)
    (hstep : ∀ n, s (n + 1) ≤ s n - c * s n ^ 3) :
    ∀ n : ℕ, 2 * c * (n : ℝ) * s n ^ 2 ≤ 1 := by
  intro n
  induction n with
  | zero => norm_num
  | succ n ih =>
      have ha := hs n
      have hb := hs (n + 1)
      have hab := hstep n
      have hx : c * s n ^ 2 ≤ 1 := by
        rcases eq_or_lt_of_le ha with h0 | hpos
        · rw [← h0]; simp
        · nlinarith [hb, hab, hpos]
      have hxnn : (0:ℝ) ≤ c * s n ^ 2 := by positivity
      have hb2 : s (n + 1) ^ 2 ≤ s n ^ 2 * (1 - c * s n ^ 2) ^ 2 := by
        nlinarith [hb, hab, ha, hxnn]
      have hkey : 2 * c * ((n : ℝ) + 1) * (s n ^ 2 * (1 - c * s n ^ 2) ^ 2) ≤ 1 := by
        nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - 2 * c * (n : ℝ) * s n ^ 2)
            (sq_nonneg (1 - c * s n ^ 2)),
          mul_nonneg (sq_nonneg (c * s n ^ 2)) (by linarith : (0:ℝ) ≤ 3 - 2 * (c * s n ^ 2))]
      have hcpos : (0:ℝ) < 2 * c * ((n : ℝ) + 1) := by positivity
      push_cast
      nlinarith [hb2, hkey, hcpos]

theorem heat_even_le [Infinite V] (hG : G.Connected) (x : V) {n : ℕ} (hn : 1 ≤ n) :
    heat G (n + n) x x ≤ (G.degree x : ℝ) * Real.sqrt (128 / n) := by
  have hdeg : ∀ v : V, 0 < G.degree v := fun v => degree_pos hG v
  have hdx : (0:ℝ) < (G.degree x : ℝ) := Nat.cast_pos.mpr (hdeg x)
  set s : ℕ → ℝ := fun k => heat G (k + k) x x / (G.degree x : ℝ) with hsdef
  have hsnn : ∀ k, 0 ≤ s k := fun k => div_nonneg (heat_nonneg _ x x) (Nat.cast_nonneg _)
  have hstep : ∀ k, s (k + 1) ≤ s k - (1 / 256) * s k ^ 3 := fun k => heat_step hG x k
  have hmain := sq_le_of_cube_step (1 / 256) (by norm_num) s hsnn hstep n
  have hn' : (0:ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsq : s n ^ 2 ≤ 128 / (n : ℝ) := by
    rw [le_div_iff₀ hn']
    nlinarith [hmain]
  have hle : s n ≤ Real.sqrt (128 / (n : ℝ)) := by
    have h := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (hsnn n)] at h
  have hval : heat G (n + n) x x = (G.degree x : ℝ) * s n := by
    rw [hsdef]
    field_simp
  rw [hval]
  exact mul_le_mul_of_nonneg_left hle hdx.le

theorem heat_one_diag (x : V) : heat G 1 x x = 0 := by
  rw [heat_succ, walkOp]
  have hz : ∀ z ∈ G.neighborFinset x, heat G 0 z x = 0 := by
    intro z hz
    have hne : z ≠ x := by
      intro h
      rw [h] at hz
      exact SimpleGraph.irrefl G ((SimpleGraph.mem_neighborFinset _ _ _).1 hz)
    simp [heat, hne]
  rw [Finset.sum_eq_zero hz, zero_div]

theorem heat_diag_le [Infinite V] (hG : G.Connected) {d : ℕ} (hd : BoundedDegree G d)
    (x : V) {m : ℕ} (hm : 1 ≤ m) :
    heat G m x x ≤ 32 * (d : ℝ) / Real.sqrt (m : ℝ) := by
  have hdeg : ∀ v : V, 0 < G.degree v := fun v => degree_pos hG v
  have hdx : (0:ℝ) < (G.degree x : ℝ) := Nat.cast_pos.mpr (hdeg x)
  have hdle : (G.degree x : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd x
  have hm' : (0:ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hsm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr hm'
  rcases eq_or_lt_of_le hm with hm1 | hm2
  · rw [← hm1, heat_one_diag]
    positivity
  · have hm2' : 2 ≤ m := hm2
    set j := m / 2 with hj
    have hj1 : 1 ≤ j := by omega
    have hcase : m = j + j ∨ m = j + j + 1 := by omega
    have hjm : (m : ℝ) ≤ 8 * (j : ℝ) := by
      have : m ≤ 8 * j := by omega
      exact_mod_cast this
    have hj' : (0:ℝ) < (j : ℝ) := by exact_mod_cast hj1
    have hstepeven : heat G m x x ≤ heat G (j + j) x x := by
      rcases hcase with h | h
      · rw [h]
      · rw [h]
        have := heat_odd_le hG x j
        rw [div_le_div_iff_of_pos_right hdx] at this
        exact this
    have heven := heat_even_le hG x hj1
    have hsqrtle : Real.sqrt (128 / (j : ℝ)) ≤ 32 / Real.sqrt (m : ℝ) := by
      have hcmp : 128 / (j : ℝ) ≤ 1024 / (m : ℝ) := by
        rw [div_le_div_iff₀ hj' hm']
        nlinarith [hjm, hm'.le, hj'.le]
      have h1 : Real.sqrt (128 / (j : ℝ)) ≤ Real.sqrt (1024 / (m : ℝ)) := Real.sqrt_le_sqrt hcmp
      have h2 : Real.sqrt (1024 / (m : ℝ)) = 32 / Real.sqrt (m : ℝ) := by
        rw [Real.sqrt_div (by norm_num : (0:ℝ) ≤ 1024)]
        congr 1
        rw [show (1024:ℝ) = 32 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 32)]
      rw [h2] at h1
      exact h1
    calc heat G m x x ≤ heat G (j + j) x x := hstepeven
      _ ≤ (G.degree x : ℝ) * Real.sqrt (128 / (j : ℝ)) := heven
      _ ≤ (d : ℝ) * (32 / Real.sqrt (m : ℝ)) := by
          refine mul_le_mul hdle hsqrtle (Real.sqrt_nonneg _) (le_trans hdx.le hdle)
      _ = 32 * (d : ℝ) / Real.sqrt (m : ℝ) := by ring


/-- The on-diagonal heat kernel bound of spectral dimension one: on an infinite
connected graph of degree bounded by `d`, `p_n(x,x) ≤ 32 d n^{-1/2}` for every
vertex and every `n ≥ 1`. -/
theorem spectralDimensionBound_of_boundedDegree [Infinite V] (hG : G.Connected) {d : ℕ}
    (hd1 : 1 ≤ d) (hd : BoundedDegree G d) :
    ∃ A : ℝ, 0 < A ∧ SpectralDimensionBound G 1 A := by
  have hdpos : (0:ℝ) < (d : ℝ) := by exact_mod_cast hd1
  refine ⟨32 * (d : ℝ), by positivity, ?_⟩
  intro x n hn
  have hmain := heat_diag_le hG hd x hn
  have hrw : (n : ℝ) ^ (-1 / 2 : ℝ) = (Real.sqrt (n : ℝ))⁻¹ := by
    rw [neg_div, Real.rpow_neg (Nat.cast_nonneg n), ← Real.sqrt_eq_rpow]
  rw [hrw, ← div_eq_mul_inv]
  exact hmain

/-- The cited input `HeatKernelBoundedDegree` of the random walk in random
scenery paper, as a theorem on an infinite connected graph. -/
theorem heatKernelBoundedDegree [Infinite V] (hG : G.Connected) :
    ∀ d : ℕ, 1 ≤ d → BoundedDegree G d → ∃ A : ℝ, 0 < A ∧ SpectralDimensionBound G 1 A :=
  fun _ hd1 hd => spectralDimensionBound_of_boundedDegree hG hd1 hd

end LatticeProb.Graph
