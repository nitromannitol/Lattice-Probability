/-
Elementary facts about the transition kernel: nonnegativity, the
Chapman--Kolmogorov lower bound through one intermediate vertex, positivity
along a walk, and the transfer of a finite Green function from one vertex to
another on a connected graph.
-/
import LatticeProb.Graph.Green

open scoped ENNReal

namespace LatticeProb.Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

theorem heat_nonneg : ∀ (k : ℕ) (x y : V), 0 ≤ heat G k x y := by
  intro k
  induction k with
  | zero => intro x y; by_cases h : x = y <;> simp [heat, h]
  | succ k ih =>
      intro x y
      rw [heat_succ]
      exact div_nonneg (Finset.sum_nonneg fun z _ => ih z y) (Nat.cast_nonneg _)

theorem heat_ge_mul [Infinite V] (hG : G.Connected) :
    ∀ (a b : ℕ) (x y z : V), heat G a x y * heat G b y z ≤ heat G (a + b) x z := by
  intro a
  induction a with
  | zero =>
      intro b x y z
      by_cases h : x = y
      · subst h; simp [heat]
      · simp [heat, h, heat_nonneg]
  | succ a ih =>
      intro b x y z
      have hd : (0 : ℝ) < (G.degree x : ℝ) := Nat.cast_pos.mpr (degree_pos hG x)
      have hle : (∑ w ∈ G.neighborFinset x, heat G a w y) * heat G b y z
          ≤ ∑ w ∈ G.neighborFinset x, heat G (a + b) w z := by
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun w _ => ih b w y z
      rw [show a + 1 + b = (a + b) + 1 by ring, heat_succ, heat_succ, walkOp, walkOp,
        div_mul_eq_mul_div]
      gcongr

theorem heat_pos_of_walk [Infinite V] (hG : G.Connected) :
    ∀ {x y : V} (p : G.Walk x y), 0 < heat G p.length x y := by
  intro x y p
  induction p with
  | nil => simp [heat]
  | @cons u w z h p ih =>
      have hd : (0 : ℝ) < (G.degree u : ℝ) := Nat.cast_pos.mpr (degree_pos hG u)
      rw [SimpleGraph.Walk.length_cons, heat_succ, walkOp]
      refine div_pos (lt_of_lt_of_le ih ?_) hd
      exact Finset.single_le_sum (f := fun s => heat G p.length s z)
        (fun s _ => heat_nonneg _ s z) ((SimpleGraph.mem_neighborFinset _ _ _).mpr h)

theorem green_ne_top_transfer [Infinite V] (hG : G.Connected) {o : V}
    (h : (∑' k : ℕ, ENNReal.ofReal (heat G k o o)) ≠ ⊤) (v : V) :
    (∑' k : ℕ, ENNReal.ofReal (heat G k v o)) ≠ ⊤ := by
  obtain ⟨p⟩ := hG.preconnected o v
  set r := p.length with hr
  have hc : 0 < heat G r o v := heat_pos_of_walk hG p
  have hstep : ∀ k : ℕ,
      ENNReal.ofReal (heat G r o v) * ENNReal.ofReal (heat G k v o)
        ≤ ENNReal.ofReal (heat G (r + k) o o) := by
    intro k
    rw [← ENNReal.ofReal_mul (heat_nonneg _ o v)]
    exact ENNReal.ofReal_le_ofReal (heat_ge_mul hG r k o v o)
  have hsum : ENNReal.ofReal (heat G r o v) * (∑' k : ℕ, ENNReal.ofReal (heat G k v o))
      ≤ ∑' k : ℕ, ENNReal.ofReal (heat G k o o) := by
    rw [← ENNReal.tsum_mul_left]
    refine le_trans (ENNReal.tsum_le_tsum hstep) ?_
    exact ENNReal.tsum_comp_le_tsum_of_injective (add_right_injective r)
      (fun k => ENNReal.ofReal (heat G k o o))
  intro hcon
  rw [hcon, ENNReal.mul_top (by simpa using (ENNReal.ofReal_pos.mpr hc).ne')] at hsum
  exact h (top_le_iff.mp hsum)

theorem green_eq_div (x y : V) :
    green G x y = (∑' k : ℕ, ENNReal.ofReal (heat G k x y)) / (G.degree y : ℝ≥0∞) := rfl

theorem green_ne_top_iff [Infinite V] (hG : G.Connected) (x y : V) :
    green G x y ≠ ⊤ ↔ (∑' k : ℕ, ENNReal.ofReal (heat G k x y)) ≠ ⊤ := by
  have hd : (G.degree y : ℝ≥0∞) ≠ 0 := by
    simpa using (degree_pos hG y).ne'
  have hdt : (G.degree y : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [green_eq_div, Ne, ENNReal.div_eq_top]
  constructor
  · intro h hcon; exact h (Or.inr ⟨hcon, hdt⟩)
  · rintro h (⟨-, hz⟩ | ⟨hc, -⟩)
    · exact hd hz
    · exact h hc

/-- On a recurrent graph the Green function is infinite at every pair of
vertices. -/
theorem green_eq_top_of_recurrent [Infinite V] (hG : G.Connected) {o : V}
    (hrec : Recurrent G o) (v : V) : green G v o = ⊤ := by
  have hoo : (∑' k : ℕ, ENNReal.ofReal (heat G k o o)) = ⊤ := by
    by_contra h
    exact ((green_ne_top_iff hG o o).mpr h) hrec
  have hvo : (∑' k : ℕ, ENNReal.ofReal (heat G k v o)) = ⊤ := by
    obtain ⟨p⟩ := hG.preconnected v o
    set r := p.length with hr
    have hc : 0 < heat G r v o := heat_pos_of_walk hG p
    have hstep : ∀ k : ℕ,
        ENNReal.ofReal (heat G r v o) * ENNReal.ofReal (heat G k o o)
          ≤ ENNReal.ofReal (heat G (r + k) v o) := by
      intro k
      rw [← ENNReal.ofReal_mul (heat_nonneg _ v o)]
      exact ENNReal.ofReal_le_ofReal (heat_ge_mul hG r k v o o)
    have hsum : ENNReal.ofReal (heat G r v o) * (∑' k : ℕ, ENNReal.ofReal (heat G k o o))
        ≤ ∑' k : ℕ, ENNReal.ofReal (heat G (r + k) v o) := by
      rw [← ENNReal.tsum_mul_left]
      exact ENNReal.tsum_le_tsum hstep
    have hle : (∑' k : ℕ, ENNReal.ofReal (heat G (r + k) v o))
        ≤ ∑' k : ℕ, ENNReal.ofReal (heat G k v o) :=
      ENNReal.tsum_comp_le_tsum_of_injective (add_right_injective r)
        (fun k => ENNReal.ofReal (heat G k v o))
    rw [hoo, ENNReal.mul_top (by simpa using (ENNReal.ofReal_pos.mpr hc).ne')] at hsum
    exact top_le_iff.mp (le_trans hsum hle)
  rw [green_eq_div, hvo, ENNReal.top_div]
  simp [ENNReal.natCast_ne_top]

end LatticeProb.Graph
