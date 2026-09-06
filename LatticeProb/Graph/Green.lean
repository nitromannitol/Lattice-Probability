/-
The walk average of the full payoff as a sum of iterates of the averaging
operator, and the value of such an iterate on a scenery supported at one
vertex.  These are the facts that turn `thm:RW` into a Green-function identity
when the scenery is nonnegative.
-/
import LatticeProb.Graph.Representation

namespace LatticeProb.Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

theorem walkOp_sum (n : ℕ) (g : ℕ → V → ℝ) (x : V) :
    walkOp G (fun y => ∑ k ∈ Finset.range n, g k y) x
      = ∑ k ∈ Finset.range n, walkOp G (g k) x := by
  simp only [walkOp, Finset.sum_div]
  rw [Finset.sum_comm]

theorem payoff_mono {ξ : V → ℝ} (hξ : ∀ v : V, 0 ≤ ξ v / (G.degree v : ℝ)) {m n : ℕ}
    (hmn : m ≤ n) (X : ℕ → V) : payoff G ξ m X ≤ payoff G ξ n X :=
  Finset.sum_le_sum_of_subset_of_nonneg
    (fun _ hj => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hj) hmn))
    (fun j _ _ => hξ (X j))

theorem walkExp_payoff_eq [Infinite V] (hG : G.Connected) (ξ : V → ℝ) :
    ∀ (n : ℕ) (x : V),
      walkExp G n x (payoff G ξ n)
        = ∑ k ∈ Finset.range n, (walkOp G)^[k] (fun v => ξ v / (G.degree v : ℝ)) x := by
  intro n
  induction n with
  | zero => intro x; simp [walkExp, payoff]
  | succ n ih =>
      intro x
      have hcong : ∀ y : V, walkExp G n y (fun X' => payoff G ξ (n + 1) (cons x X'))
          = ξ x / (G.degree x : ℝ) + walkExp G n y (payoff G ξ n) := by
        intro y
        rw [show walkExp G n y (fun X' => payoff G ξ (n + 1) (cons x X'))
            = walkExp G n y (fun X' => ξ x / (G.degree x : ℝ) + payoff G ξ n X') from
          walkExp_congr (fun X' _ => payoff_cons ξ n x X'), walkExp_add, walkExp_const hG]
      rw [walkExp_succ]
      simp only [hcong, ih]
      rw [Finset.sum_add_distrib, Finset.sum_const,
        SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul, add_div]
      have hd : (G.degree x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (degree_pos hG x).ne'
      rw [Finset.sum_range_succ']
      have : (∑ y ∈ G.neighborFinset x,
            ∑ k ∈ Finset.range n, (walkOp G)^[k] (fun v => ξ v / (G.degree v : ℝ)) y)
            / (G.degree x : ℝ)
          = ∑ k ∈ Finset.range n,
              (walkOp G)^[k + 1] (fun v => ξ v / (G.degree v : ℝ)) x := by
        rw [show (∑ y ∈ G.neighborFinset x,
              ∑ k ∈ Finset.range n, (walkOp G)^[k] (fun v => ξ v / (G.degree v : ℝ)) y)
              / (G.degree x : ℝ)
            = walkOp G (fun y => ∑ k ∈ Finset.range n,
                (walkOp G)^[k] (fun v => ξ v / (G.degree v : ℝ)) y) x from rfl,
          walkOp_sum]
        exact Finset.sum_congr rfl fun k _ => by rw [Function.iterate_succ_apply']
      rw [this]
      have : (G.degree x : ℝ) * (ξ x / (G.degree x : ℝ)) / (G.degree x : ℝ)
          = ξ x / (G.degree x : ℝ) := by field_simp
      rw [this]
      simp [Function.iterate_zero_apply]
      ring

theorem odometer_eq_payoff [Infinite V] (hG : G.Connected) (σ : V → ℝ)
    (hpos : ∀ v : V, 0 ≤ excess σ v / (G.degree v : ℝ)) (n : ℕ) (x : V) :
    odometer G σ n x = walkExp G n x (payoff G (excess σ) n) := by
  have hmem : walkExp G n x (payoff G (excess σ) n) ∈ stopValues G (excess σ) n x :=
    ⟨fun _ => n, fun _ _ _ _ h => h, fun _ => le_rfl, rfl⟩
  refine le_antisymm ?_ ((odometer_isLUB hG σ n x).1 _ hmem)
  obtain ⟨τ, -, hle, hval⟩ := (odometer_isLUB hG σ n x).2
  rw [hval]
  exact walkExp_mono fun X => payoff_mono hpos (hle X) X

open scoped Classical in
theorem heat_succ (k : ℕ) (x y : V) :
    heat G (k + 1) x y = walkOp G (fun z => heat G k z y) x := rfl

open scoped Classical in
theorem walkOp_iterate_single (o : V) (c : ℝ) :
    ∀ (k : ℕ) (x : V),
      (walkOp G)^[k] (fun v => if v = o then c else 0) x = heat G k x o * c := by
  intro k
  induction k with
  | zero =>
      intro x
      simp only [Function.iterate_zero_apply, heat]
      split_ifs <;> ring
  | succ k ih =>
      intro x
      rw [Function.iterate_succ_apply', heat_succ]
      simp only [walkOp, ih]
      rw [← Finset.sum_mul]
      ring

end LatticeProb.Graph
