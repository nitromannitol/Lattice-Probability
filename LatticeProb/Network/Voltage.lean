/-
The voltage function: a bounded nonnegative function with Laplacian `δ_b - δ_a`.

On a transient graph there is no need for hitting probabilities.  Write

    u_a(x) = ∑_k p_k(x,a)

for the expected total local time at `a` of the walk started at `x`.  Summing the
one-step recursion `p_{k+1}(x,a) = deg(x)^{-1} ∑_{y ∼ x} p_k(y,a)` over `k` gives

    ∑_{y ∼ x} u_a(y) = deg(x) (u_a(x) - p_0(x,a)) ,

so `Δu_a = -deg(·) δ_a`, and `u_a / deg(a)` has Laplacian `-δ_a`.  The difference
`u_a/deg(a) - u_b/deg(b)` therefore has Laplacian `δ_b - δ_a`; it is bounded
because `u_a(x) ≤ u_a(a)` (the walk started elsewhere spends no more time at `a`
than the walk started at `a`, which is `LatticeProb.Network.meanLocalTime_le_self`),
and adding the constant `u_b(b)/deg(b)`, which the Laplacian does not see, makes
it nonnegative.

The only hypothesis is that the two diagonal series converge; on a connected
graph this is `g(a,a) < ∞` and `g(b,b) < ∞`, which is the form
`LatticeProb.Network.exists_voltage_of_green_ne_top` takes.  Nothing here needs
the effective resistance, the reciprocity `deg(a)P_a(τ_b < τ_a^+) =
deg(b)P_b(τ_a < τ_b^+)`, or the hitting probabilities that the usual construction
`f(x) = P_x(T_a < T_b)/(deg(a)P_a(T_b < T_a^+))` goes through.
-/
import Mathlib
import LatticeProb.Network.FirstPassage

open Finset
open scoped ENNReal
open scoped Classical

namespace LatticeProb.Network

open LatticeProb.Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- The expected total local time at `a` of the walk started at `x`. -/
noncomputable def greenMass (G : SimpleGraph V) [G.LocallyFinite] (a x : V) : ℝ :=
  ∑' k : ℕ, heat G k x a

theorem summable_heat_of_summable_diag {a : V} (ha : Summable fun k => heat G k a a) (x : V) :
    Summable fun k => heat G k x a := by
  refine summable_of_sum_range_le (c := ∑' k : ℕ, heat G k a a)
    (fun k => heat_nonneg k x a) fun n => ?_
  have h1 : ∑ i ∈ Finset.range n, heat G i x a = meanLocalTime G n x a := rfl
  have h2 : meanLocalTime G n x a ≤ meanLocalTime G n a a := meanLocalTime_le_self n x a
  have h3 : meanLocalTime G n a a ≤ ∑' k : ℕ, heat G k a a :=
    Summable.sum_le_tsum (Finset.range n) (fun k _ => heat_nonneg k a a) ha
  rw [h1]
  exact h2.trans h3

theorem greenMass_nonneg (a x : V) : 0 ≤ greenMass G a x :=
  tsum_nonneg fun k => heat_nonneg k x a

theorem greenMass_le_diag {a : V} (ha : Summable fun k => heat G k a a) (x : V) :
    greenMass G a x ≤ greenMass G a a := by
  refine Real.tsum_le_of_sum_range_le (fun k => heat_nonneg k x a) fun n => ?_
  have h1 : ∑ i ∈ Finset.range n, heat G i x a = meanLocalTime G n x a := rfl
  have h2 : meanLocalTime G n x a ≤ meanLocalTime G n a a := meanLocalTime_le_self n x a
  have h3 : meanLocalTime G n a a ≤ ∑' k : ℕ, heat G k a a :=
    Summable.sum_le_tsum (Finset.range n) (fun k _ => heat_nonneg k a a) ha
  rw [h1]
  exact h2.trans h3

theorem one_le_greenMass_diag {a : V} (ha : Summable fun k => heat G k a a) :
    1 ≤ greenMass G a a := by
  have h := ha.le_tsum 0 (fun j _ => heat_nonneg j a a)
  have h0 : heat G 0 a a = 1 := by simp [heat]
  rw [h0] at h
  exact h


theorem laplacian_greenMass (hdeg : ∀ v : V, 0 < G.degree v) {a : V}
    (ha : Summable fun k => heat G k a a) (x : V) :
    laplacian G (greenMass G a) x = -(G.degree x : ℝ) * (if x = a then (1 : ℝ) else 0) := by
  have hsum : ∀ y : V, Summable fun k => heat G k y a := summable_heat_of_summable_diag ha
  have hdx : (G.degree x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hdeg x).ne'
  have hstep : ∀ k : ℕ, ∑ y ∈ G.neighborFinset x, heat G k y a
      = (G.degree x : ℝ) * heat G (k + 1) x a := by
    intro k
    rw [heat_succ, walkOp]
    field_simp
  have hshift : ∑' k : ℕ, heat G (k + 1) x a
      = (∑' k : ℕ, heat G k x a) - heat G 0 x a := by
    have h := (hsum x).tsum_eq_zero_add
    linarith
  have hnb : ∑ y ∈ G.neighborFinset x, greenMass G a y
      = (G.degree x : ℝ) * ((∑' k : ℕ, heat G k x a) - heat G 0 x a) := by
    have h1 : ∑ y ∈ G.neighborFinset x, greenMass G a y
        = ∑' k : ℕ, ∑ y ∈ G.neighborFinset x, heat G k y a :=
      (Summable.tsum_finsetSum (fun y _ => hsum y)).symm
    have hsucc : Summable fun k : ℕ => heat G (k + 1) x a :=
      (summable_nat_add_iff 1).mpr (hsum x)
    rw [h1, tsum_congr hstep, hsucc.tsum_mul_left, hshift]
  rw [laplacian, Finset.sum_sub_distrib, Finset.sum_const,
    SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul, hnb]
  have h0 : heat G 0 x a = if x = a then (1 : ℝ) else 0 := rfl
  rw [h0, greenMass]
  ring


theorem laplacian_lin (u v : V → ℝ) (c₁ c₂ c₃ : ℝ) (x : V) :
    laplacian G (fun y => c₁ * u y + c₂ * v y + c₃) x
      = c₁ * laplacian G u x + c₂ * laplacian G v x := by
  rw [laplacian, laplacian, laplacian, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- **The voltage function.**  On a graph where the walk started at `a` and at
`b` returns finitely often to its own start, there is a bounded nonnegative
function whose Laplacian is `δ_b - δ_a`.  It is the difference of the two Green
masses, each normalized by the degree of its source, raised by a constant so as
to be nonnegative. -/
theorem exists_voltage (hdeg : ∀ v : V, 0 < G.degree v) {a b : V} (hab : a ≠ b)
    (ha : Summable fun k => heat G k a a) (hb : Summable fun k => heat G k b b) :
    ∃ f : V → ℝ, ∃ M : ℝ, 0 < M ∧ (∀ x, 0 ≤ f x ∧ f x ≤ M) ∧
      ∀ x : V, laplacian G f x
        = (if x = b then (1 : ℝ) else 0) - (if x = a then 1 else 0) := by
  have hda : (0 : ℝ) < (G.degree a : ℝ) := by exact_mod_cast hdeg a
  have hdb : (0 : ℝ) < (G.degree b : ℝ) := by exact_mod_cast hdeg b
  have hA : 1 ≤ greenMass G a a := one_le_greenMass_diag ha
  have hB : 0 ≤ greenMass G b b := greenMass_nonneg b b
  refine ⟨fun x => (1 / (G.degree a : ℝ)) * greenMass G a x
      + (-(1 / (G.degree b : ℝ))) * greenMass G b x
      + greenMass G b b / (G.degree b : ℝ),
    greenMass G a a / (G.degree a : ℝ) + greenMass G b b / (G.degree b : ℝ), ?_, ?_, ?_⟩
  · have h1 : (0 : ℝ) < greenMass G a a / (G.degree a : ℝ) := by
      have : (0 : ℝ) < greenMass G a a := lt_of_lt_of_le zero_lt_one hA
      positivity
    have h2 : (0 : ℝ) ≤ greenMass G b b / (G.degree b : ℝ) := by positivity
    linarith
  · intro x
    have h1 : 0 ≤ greenMass G a x := greenMass_nonneg a x
    have h2 : greenMass G b x ≤ greenMass G b b := greenMass_le_diag hb x
    have h3 : greenMass G a x ≤ greenMass G a a := greenMass_le_diag ha x
    have h4 : 0 ≤ greenMass G b x := greenMass_nonneg b x
    have hbx : greenMass G b x / (G.degree b : ℝ) ≤ greenMass G b b / (G.degree b : ℝ) :=
      (div_le_div_iff_of_pos_right hdb).mpr h2
    have hax : greenMass G a x / (G.degree a : ℝ) ≤ greenMass G a a / (G.degree a : ℝ) :=
      (div_le_div_iff_of_pos_right hda).mpr h3
    have hax0 : (0 : ℝ) ≤ greenMass G a x / (G.degree a : ℝ) := by positivity
    have hbx0 : (0 : ℝ) ≤ greenMass G b x / (G.degree b : ℝ) := by positivity
    constructor
    · show (0:ℝ) ≤ (1 / (G.degree a : ℝ)) * greenMass G a x
        + (-(1 / (G.degree b : ℝ))) * greenMass G b x
        + greenMass G b b / (G.degree b : ℝ)
      have e1 : (1 / (G.degree a : ℝ)) * greenMass G a x
          = greenMass G a x / (G.degree a : ℝ) := by ring
      have e2 : (-(1 / (G.degree b : ℝ))) * greenMass G b x
          = -(greenMass G b x / (G.degree b : ℝ)) := by ring
      rw [e1, e2]
      linarith
    · show (1 / (G.degree a : ℝ)) * greenMass G a x
        + (-(1 / (G.degree b : ℝ))) * greenMass G b x
        + greenMass G b b / (G.degree b : ℝ)
        ≤ greenMass G a a / (G.degree a : ℝ) + greenMass G b b / (G.degree b : ℝ)
      have e1 : (1 / (G.degree a : ℝ)) * greenMass G a x
          = greenMass G a x / (G.degree a : ℝ) := by ring
      have e2 : (-(1 / (G.degree b : ℝ))) * greenMass G b x
          = -(greenMass G b x / (G.degree b : ℝ)) := by ring
      rw [e1, e2]
      linarith
  · intro x
    rw [laplacian_lin (greenMass G a) (greenMass G b), laplacian_greenMass hdeg ha,
      laplacian_greenMass hdeg hb]
    by_cases hxa : x = a
    · subst hxa
      rw [if_neg hab, if_pos rfl]
      field_simp
      ring
    · by_cases hxb : x = b
      · subst hxb
        rw [if_pos rfl, if_neg hxa]
        field_simp
        ring
      · rw [if_neg hxa, if_neg hxb]
        ring


/-- A nonnegative real series with finite `ℝ≥0∞` sum is summable. -/
theorem summable_of_tsum_ofReal_ne_top {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    (h : (∑' n, ENNReal.ofReal (f n)) ≠ ⊤) : Summable f := by
  have h1 : Summable fun n => (f n).toNNReal := by
    rw [← ENNReal.tsum_coe_ne_top_iff_summable]
    simpa [ENNReal.ofReal] using h
  have h2 : Summable fun n => ((f n).toNNReal : ℝ) := NNReal.summable_coe.mpr h1
  refine h2.congr fun n => ?_
  exact Real.coe_toNNReal _ (hf n)

/-- **The voltage function on a transient graph**, in the form the Green
function is stated in: `g(a,a) < ∞` and `g(b,b) < ∞` give a bounded nonnegative
`f` with `Δf = δ_b - δ_a`. -/
theorem exists_voltage_of_green_ne_top [Infinite V] (hG : G.Connected) {a b : V} (hab : a ≠ b)
    (ha : green G a a ≠ ⊤) (hb : green G b b ≠ ⊤) :
    ∃ f : V → ℝ, ∃ M : ℝ, 0 < M ∧ (∀ x, 0 ≤ f x ∧ f x ≤ M) ∧
      ∀ x : V, laplacian G f x
        = (if x = b then (1 : ℝ) else 0) - (if x = a then 1 else 0) := by
  have hdeg : ∀ v : V, 0 < G.degree v := fun v => degree_pos hG v
  refine exists_voltage hdeg hab ?_ ?_
  · exact summable_of_tsum_ofReal_ne_top (fun k => heat_nonneg k a a)
      ((green_ne_top_iff hG a a).mp ha)
  · exact summable_of_tsum_ofReal_ne_top (fun k => heat_nonneg k b b)
      ((green_ne_top_iff hG b b).mp hb)


/-- **The voltage function on a doubly transient graph.**  Double transience
gives `g(o,o) < ∞` at every `o`, which is all the construction needs.  This is
the form the zero-one law of a doubly transient graph uses. -/
theorem exists_voltage_of_doublyTransient [Infinite V] (hG : G.Connected)
    (hDT : DoublyTransient G) {a b : V} (hab : a ≠ b) :
    ∃ f : V → ℝ, ∃ M : ℝ, 0 < M ∧ (∀ x, 0 ≤ f x ∧ f x ≤ M) ∧
      ∀ x : V, laplacian G f x
        = (if x = b then (1 : ℝ) else 0) - (if x = a then 1 else 0) := by
  have hdiag : ∀ o : V, green G o o ≠ ⊤ := by
    intro o
    have h := ENNReal.ne_top_of_tsum_ne_top (hDT o) o
    intro hc
    rw [hc] at h
    simp at h
  exact exists_voltage_of_green_ne_top hG hab (hdiag a) (hdiag b)

end LatticeProb.Network
