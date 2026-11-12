import Mathlib

/-!
# The unit flow of a walk

A finite walk `v₀, v₁, …, vₙ` in a vertex set `V` defines its *net crossing flow*
`θ(a, b) = #{i : (vᵢ, vᵢ₊₁) = (a, b)} - #{i : (vᵢ, vᵢ₊₁) = (b, a)}`. It is antisymmetric, carried by
the steps of the walk, and its divergence at `a` is `1{a = v₀} - 1{a = vₙ}`. Hence a walk from `x`
whose last vertex lies outside a finite set `A` is a unit flow from `x` out of `A`, and so is every
convex combination of such walks (the expected net crossing flow of a random path). For a
self-avoiding walk `|θ(a, b)| ≤ 1{a is visited}`, so the expected flow through an edge at `a` is at
most the probability that the random path visits `a`.
-/

namespace LatticeProb

open Finset

variable {V : Type*} [DecidableEq V]

/-- The *net crossing flow* of a walk: `walkFlow p a b` is the number of steps of `p` from `a` to `b`
minus the number of steps from `b` to `a`. -/
noncomputable def walkFlow : List V → V → V → ℝ
  | [], _, _ => 0
  | [_], _, _ => 0
  | u :: v :: t, a, b =>
      ((if u = a ∧ v = b then 1 else 0) - (if u = b ∧ v = a then 1 else 0)) + walkFlow (v :: t) a b

@[simp] theorem walkFlow_nil (a b : V) : walkFlow ([] : List V) a b = 0 := rfl

@[simp] theorem walkFlow_singleton (u a b : V) : walkFlow [u] a b = 0 := rfl

theorem walkFlow_cons_cons (u v : V) (t : List V) (a b : V) :
    walkFlow (u :: v :: t) a b =
      ((if u = a ∧ v = b then 1 else 0) - (if u = b ∧ v = a then 1 else 0)) + walkFlow (v :: t) a b :=
  rfl

/-- The net crossing flow is antisymmetric. -/
theorem walkFlow_antisymm (p : List V) (a b : V) : walkFlow p a b = -walkFlow p b a := by
  induction p with
  | nil => simp
  | cons u t ih =>
    cases t with
    | nil => simp
    | cons v t => rw [walkFlow_cons_cons, walkFlow_cons_cons, ih]; ring

/-- The net crossing flow is carried by the steps of the walk: if every step `(u, v)` of `p` satisfies
the symmetric relation `R u v`, then `walkFlow p a b = 0` unless `R a b`. -/
theorem walkFlow_eq_zero_of_not_rel {R : V → V → Prop} (hR : ∀ u v, R u v → R v u) {p : List V}
    (hp : p.IsChain R) {a b : V} (hab : ¬ R a b) : walkFlow p a b = 0 := by
  induction p with
  | nil => simp
  | cons u t ih =>
    cases t with
    | nil => simp
    | cons v t =>
      rw [List.isChain_cons_cons] at hp
      have h1 : ¬ (u = a ∧ v = b) := fun h => hab (h.1 ▸ h.2 ▸ hp.1)
      have h2 : ¬ (u = b ∧ v = a) := fun h => hab (hR _ _ (h.1 ▸ h.2 ▸ hp.1))
      rw [walkFlow_cons_cons, ite_eq_right h1, ite_eq_right h2, ih hp.2]
      ring

/-- **Divergence of the net crossing flow of a walk.** If `S` contains every vertex of the walk
`x :: p`, then `∑_{b ∈ S} θ(a, b) = 1{x = a} - 1{last vertex = a}`. -/
theorem sum_walkFlow_eq (S : Finset V) (a : V) (x : V) (p : List V) (hS : ∀ v ∈ x :: p, v ∈ S) :
    ∑ b ∈ S, walkFlow (x :: p) a b =
      (if x = a then 1 else 0) - (if (x :: p).getLast (List.cons_ne_nil x p) = a then 1 else 0) := by
  induction p generalizing x with
  | nil => by_cases h : x = a <;> simp [h]
  | cons v t ih =>
    have hxS : x ∈ S := hS x (by simp)
    have hvS : v ∈ S := hS v (by simp)
    have hstep : ∑ b ∈ S, ((if x = a ∧ v = b then (1 : ℝ) else 0) - (if x = b ∧ v = a then 1 else 0)) =
        (if x = a then 1 else 0) - (if v = a then 1 else 0) := by
      rw [Finset.sum_sub_distrib]
      congr 1
      · by_cases hx : x = a <;> simp [hx, hvS]
      · by_cases hv : v = a <;> simp [hv, hxS]
    rw [Finset.sum_congr rfl fun b _ => walkFlow_cons_cons x v t a b, Finset.sum_add_distrib, hstep,
      ih v fun w hw => hS w (List.mem_cons_of_mem _ hw), List.getLast_cons (List.cons_ne_nil v t)]
    ring

/-- **A walk out of `A` is a unit flow.** If the walk `x :: p` stays in the finite set `S` and its last
vertex lies outside `A`, then its net crossing flow has divergence `1{a = x}` at every `a ∈ A`. -/
theorem sum_walkFlow_eq_ite_of_getLast_notMem {S A : Finset V} {x : V} {p : List V}
    (hS : ∀ v ∈ x :: p, v ∈ S) (hlast : (x :: p).getLast (List.cons_ne_nil x p) ∉ A) :
    ∀ a ∈ A, ∑ b ∈ S, walkFlow (x :: p) a b = if a = x then 1 else 0 := by
  intro a ha
  have hne : ¬ (x :: p).getLast (List.cons_ne_nil x p) = a := fun h => hlast (h ▸ ha)
  rw [sum_walkFlow_eq S a x p hS, ite_eq_right hne, sub_zero]
  by_cases h : a = x
  · simp [h]
  · simp [h, Ne.symm h]

/-- **Convex combinations of unit flows are unit flows**: if each `θ i` has divergence `1{a = x}` on
`A` and the weights sum to one, so does `∑ᵢ w i θ i`. -/
theorem sum_sum_mul_eq_ite {ι : Type*} {I : Finset ι} {w : ι → ℝ} (hw : ∑ i ∈ I, w i = 1)
    {θ : ι → V → V → ℝ} {S A : Finset V} {x : V}
    (hdiv : ∀ i ∈ I, ∀ a ∈ A, ∑ b ∈ S, θ i a b = if a = x then 1 else 0) :
    ∀ a ∈ A, ∑ b ∈ S, ∑ i ∈ I, w i * θ i a b = if a = x then 1 else 0 := by
  intro a ha
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  rw [Finset.sum_congr rfl fun i hi => by rw [hdiv i hi a ha], ← Finset.sum_mul, hw, one_mul]

/-- A walk that never visits `a` carries no flow out of `a`. -/
theorem walkFlow_eq_zero_of_notMem_left {p : List V} {a : V} (ha : a ∉ p) (b : V) :
    walkFlow p a b = 0 := by
  induction p with
  | nil => simp
  | cons u t ih =>
    cases t with
    | nil => simp
    | cons v t =>
      have hu : u ≠ a := fun h => ha (h ▸ List.mem_cons_self)
      have hv : v ≠ a := fun h => ha (h ▸ List.mem_cons_of_mem _ List.mem_cons_self)
      rw [walkFlow_cons_cons, ite_eq_right fun h => hu h.1, ite_eq_right fun h => hv h.2,
        ih fun h => ha (List.mem_cons_of_mem _ h)]
      ring

/-- A walk that never visits `b` carries no flow into `b`. -/
theorem walkFlow_eq_zero_of_notMem_right {p : List V} (a : V) {b : V} (hb : b ∉ p) :
    walkFlow p a b = 0 := by
  rw [walkFlow_antisymm, walkFlow_eq_zero_of_notMem_left hb, neg_zero]

/-- The net crossing flow of a self-avoiding walk is at most one in absolute value. -/
theorem abs_walkFlow_le_one {p : List V} (hp : p.Nodup) (a b : V) : |walkFlow p a b| ≤ 1 := by
  induction p with
  | nil => simp
  | cons u t ih =>
    cases t with
    | nil => simp
    | cons v t =>
      rw [List.nodup_cons] at hp
      rw [walkFlow_cons_cons]
      by_cases hua : u = a
      · subst hua
        have hv : v ≠ u := fun h => hp.1 (h ▸ List.mem_cons_self)
        rw [walkFlow_eq_zero_of_notMem_left hp.1,
          show (if u = b ∧ v = u then (1 : ℝ) else 0) = 0 from ite_eq_right fun h => hv h.2]
        split_ifs <;> norm_num
      · rw [ite_eq_right fun h => hua h.1]
        by_cases hub : u = b ∧ v = a
        · rw [ite_eq_left hub, walkFlow_eq_zero_of_notMem_right a (hub.1 ▸ hp.1)]
          norm_num
        · rw [ite_eq_right hub, sub_zero, zero_add]
          exact ih hp.2

/-- The net crossing flow of a self-avoiding walk through an edge at `a` is at most `1{a is visited}`. -/
theorem abs_walkFlow_le_ite {p : List V} (hp : p.Nodup) (a b : V) :
    |walkFlow p a b| ≤ if a ∈ p then 1 else 0 := by
  split_ifs with ha
  · exact abs_walkFlow_le_one hp a b
  · rw [walkFlow_eq_zero_of_notMem_left ha, abs_zero]

/-- **Flow of a random self-avoiding path through an edge.** For nonnegative weights `w` on
self-avoiding walks `P i`, the expected net crossing flow through an edge at `a` is at most the total
weight of the walks visiting `a`. -/
theorem abs_sum_mul_walkFlow_le {ι : Type*} {I : Finset ι} {w : ι → ℝ} (hw0 : ∀ i ∈ I, 0 ≤ w i)
    {P : ι → List V} (hP : ∀ i ∈ I, (P i).Nodup) (a b : V) :
    |∑ i ∈ I, w i * walkFlow (P i) a b| ≤ ∑ i ∈ I, if a ∈ P i then w i else 0 := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [abs_mul, abs_of_nonneg (hw0 i hi)]
  calc w i * |walkFlow (P i) a b| ≤ w i * (if a ∈ P i then 1 else 0) :=
        mul_le_mul_of_nonneg_left (abs_walkFlow_le_ite (hP i hi) a b) (hw0 i hi)
    _ = if a ∈ P i then w i else 0 := by split_ifs <;> simp

end LatticeProb
