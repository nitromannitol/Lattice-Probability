/-
The Nash inequality of dimension one on an infinite connected locally finite
graph, in the form the on-diagonal heat kernel bound needs.

Write `‖f‖_2^2 = ∑_y deg(y) f(y)^2`, `‖f‖_1 = ∑_y deg(y) f(y)` and
`E(f) = ‖f‖_2^2 - ∑_y deg(y) f(y) (Pf)(y)`, the Dirichlet form of the walk
operator against the degree measure.  For a nonnegative `f` of finite support,

  ‖f‖_2^6 ≤ 8 E(f) ‖f‖_1^4.

The only geometry it uses is that a finite set of vertices of an infinite
connected graph has a vertex outside it: a path from the vertex where `f` is
largest to a vertex where `f` vanishes telescopes `sup f^2` into a sum of edge
increments of `f^2`, and Cauchy-Schwarz turns that sum into the Dirichlet form.
No bound on the degrees is needed.

Every sum runs over a `Finset T` containing the support of `f` together with
the neighbours of that support; the summands vanish off it, so the value does
not depend on the choice.
-/
import LatticeProb.Graph.Reach

namespace LatticeProb.Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

theorem sum_neighbor_sum (h : V → ℝ) (T : Finset V)
    (hT : ∀ y, h y ≠ 0 → y ∈ T) (hTN : ∀ y v : V, h y ≠ 0 → G.Adj y v → v ∈ T) :
    ∑ y ∈ T, ∑ v ∈ G.neighborFinset y, h v = ∑ y ∈ T, (G.degree y : ℝ) * h y := by
  classical
  set S : Finset V := T.filter (fun z => h z ≠ 0) with hSdef
  have hmemS : ∀ z : V, z ∈ S ↔ (z ∈ T ∧ h z ≠ 0) := by
    intro z; rw [hSdef, Finset.mem_filter]
  have h1 : ∀ y ∈ T, ∑ v ∈ G.neighborFinset y, h v = ∑ v ∈ G.neighborFinset y ∩ S, h v := by
    intro y _
    refine (Finset.sum_subset Finset.inter_subset_left ?_).symm
    intro v hv hvn
    by_contra hne
    exact hvn (Finset.mem_inter.2 ⟨hv, (hmemS v).2 ⟨hT v hne, hne⟩⟩)
  rw [Finset.sum_congr rfl h1]
  have h2 : ∑ y ∈ T, ∑ v ∈ G.neighborFinset y ∩ S, h v
      = ∑ v ∈ S, ∑ _y ∈ G.neighborFinset v, h v := by
    refine Finset.sum_comm' ?_
    intro y v
    constructor
    · rintro ⟨_, hv⟩
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hv
      exact ⟨(SimpleGraph.mem_neighborFinset _ _ _).2 hv.1.symm, hv.2⟩
    · rintro ⟨hy, hv⟩
      rw [SimpleGraph.mem_neighborFinset] at hy
      have hvT := (hmemS v).1 hv
      refine ⟨hTN v y hvT.2 hy, ?_⟩
      rw [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨hy.symm, hv⟩
  rw [h2]
  have h3 : ∀ v ∈ S, ∑ _y ∈ G.neighborFinset v, h v = (G.degree v : ℝ) * h v := by
    intro v _
    rw [Finset.sum_const, SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul]
  rw [Finset.sum_congr rfl h3]
  refine Finset.sum_subset (Finset.filter_subset _ _) ?_
  intro y hy hyn
  have hzero : h y = 0 := by
    by_contra hne
    exact hyn ((hmemS y).2 ⟨hy, hne⟩)
  rw [hzero, mul_zero]

theorem sum_degree_mul_walkOp (hdeg : ∀ v : V, 0 < G.degree v) (g : V → ℝ) (T : Finset V) :
    ∑ y ∈ T, (G.degree y : ℝ) * g y * walkOp G g y
      = ∑ y ∈ T, ∑ v ∈ G.neighborFinset y, g y * g v := by
  refine Finset.sum_congr rfl fun y _ => ?_
  have hy : (G.degree y : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hdeg y).ne'
  rw [walkOp, ← Finset.mul_sum]
  field_simp

theorem sum_sq_sub_eq (g : V → ℝ) (T : Finset V)
    (hT : ∀ y, g y ≠ 0 → y ∈ T) (hTN : ∀ y v : V, g y ≠ 0 → G.Adj y v → v ∈ T) :
    ∑ y ∈ T, ∑ v ∈ G.neighborFinset y, (g y - g v) ^ 2
      = 2 * (∑ y ∈ T, (G.degree y : ℝ) * g y ^ 2)
        - 2 * ∑ y ∈ T, ∑ v ∈ G.neighborFinset y, g y * g v := by
  have key : ∑ y ∈ T, ∑ v ∈ G.neighborFinset y, g v ^ 2
      = ∑ y ∈ T, (G.degree y : ℝ) * g y ^ 2 :=
    sum_neighbor_sum (fun z => g z ^ 2) T
      (fun y hy => hT y (fun h0 => hy (by rw [h0]; ring)))
      (fun y v hy hadj => hTN y v (fun h0 => hy (by rw [h0]; ring)) hadj)
  have expand : ∀ y ∈ T, ∑ v ∈ G.neighborFinset y, (g y - g v) ^ 2
      = (G.degree y : ℝ) * g y ^ 2 - 2 * (∑ v ∈ G.neighborFinset y, g y * g v)
        + ∑ v ∈ G.neighborFinset y, g v ^ 2 := by
    intro y _
    rw [Finset.sum_congr rfl (fun v _ =>
      show (g y - g v) ^ 2 = g y ^ 2 - 2 * (g y * g v) + g v ^ 2 by ring)]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, ← Finset.mul_sum,
      SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul]
  rw [Finset.sum_congr rfl expand, Finset.sum_add_distrib, Finset.sum_sub_distrib, key,
    ← Finset.mul_sum]
  ring

theorem sum_sq_add_eq (g : V → ℝ) (T : Finset V)
    (hT : ∀ y, g y ≠ 0 → y ∈ T) (hTN : ∀ y v : V, g y ≠ 0 → G.Adj y v → v ∈ T) :
    ∑ y ∈ T, ∑ v ∈ G.neighborFinset y, (g y + g v) ^ 2
      = 2 * (∑ y ∈ T, (G.degree y : ℝ) * g y ^ 2)
        + 2 * ∑ y ∈ T, ∑ v ∈ G.neighborFinset y, g y * g v := by
  have key : ∑ y ∈ T, ∑ v ∈ G.neighborFinset y, g v ^ 2
      = ∑ y ∈ T, (G.degree y : ℝ) * g y ^ 2 :=
    sum_neighbor_sum (fun z => g z ^ 2) T
      (fun y hy => hT y (fun h0 => hy (by rw [h0]; ring)))
      (fun y v hy hadj => hTN y v (fun h0 => hy (by rw [h0]; ring)) hadj)
  have expand : ∀ y ∈ T, ∑ v ∈ G.neighborFinset y, (g y + g v) ^ 2
      = (G.degree y : ℝ) * g y ^ 2 + 2 * (∑ v ∈ G.neighborFinset y, g y * g v)
        + ∑ v ∈ G.neighborFinset y, g v ^ 2 := by
    intro y _
    rw [Finset.sum_congr rfl (fun v _ =>
      show (g y + g v) ^ 2 = g y ^ 2 + 2 * (g y * g v) + g v ^ 2 by ring)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum,
      SimpleGraph.card_neighborFinset_eq_degree, nsmul_eq_mul]
  rw [Finset.sum_congr rfl expand, Finset.sum_add_distrib, Finset.sum_add_distrib, key,
    ← Finset.mul_sum]
  ring

theorem sum_abs_sub_sq_le (g : V → ℝ) (T : Finset V) :
    ∑ y ∈ T, ∑ v ∈ G.neighborFinset y, |g y ^ 2 - g v ^ 2|
      ≤ Real.sqrt (∑ y ∈ T, ∑ v ∈ G.neighborFinset y, (g y - g v) ^ 2)
        * Real.sqrt (∑ y ∈ T, ∑ v ∈ G.neighborFinset y, (g y + g v) ^ 2) := by
  have inner : ∀ y : V, ∑ v ∈ G.neighborFinset y, |g y ^ 2 - g v ^ 2|
      ≤ Real.sqrt (∑ v ∈ G.neighborFinset y, (g y - g v) ^ 2)
        * Real.sqrt (∑ v ∈ G.neighborFinset y, (g y + g v) ^ 2) := by
    intro y
    have h1 : ∀ v : V, |g y ^ 2 - g v ^ 2| = |g y - g v| * |g y + g v| := by
      intro v; rw [← abs_mul]; congr 1; ring
    simp only [h1]
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt (G.neighborFinset y)
      (fun v => |g y - g v|) (fun v => |g y + g v|)
    simpa [sq_abs] using hcs
  refine le_trans (Finset.sum_le_sum (fun y _ => inner y)) ?_
  exact Real.sum_sqrt_mul_sqrt_le T (fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
    (fun _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem abs_sub_le_sum_abs_sub (a : ℕ → ℝ) : ∀ k : ℕ,
    |a 0 - a k| ≤ ∑ i ∈ Finset.range k, |a i - a (i + 1)| := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ]
      have h := abs_sub_le (a 0) (a k) (a (k + 1))
      linarith

theorem sq_le_sum_abs_sub_sq [Infinite V] (hG : G.Connected) (g : V → ℝ) (T : Finset V)
    (hT : ∀ y, g y ≠ 0 → y ∈ T) (x : V) :
    g x ^ 2 ≤ ∑ y ∈ T, ∑ v ∈ G.neighborFinset y, |g y ^ 2 - g v ^ 2| := by
  classical
  obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset T
  have hgz : g z = 0 := by
    by_contra hne
    exact hz (hT z hne)
  obtain ⟨p0⟩ := hG.preconnected x z
  set p := p0.bypass with hp
  have hpath : p.IsPath := p0.bypass_isPath
  have hlast : g (p.getVert p.length) = 0 := by
    rw [SimpleGraph.Walk.getVert_length]; exact hgz
  have hex : ∃ i, g (p.getVert i) = 0 := ⟨p.length, hlast⟩
  set j := Nat.find hex with hj
  have hjspec : g (p.getVert j) = 0 := Nat.find_spec hex
  have hjle : j ≤ p.length := Nat.find_le hlast
  have hmin : ∀ i, i < j → g (p.getVert i) ≠ 0 := fun i hi => Nat.find_min hex hi
  -- telescoping
  have htel : g x ^ 2
      ≤ ∑ i ∈ Finset.range j, |g (p.getVert i) ^ 2 - g (p.getVert (i + 1)) ^ 2| := by
    have h0 : p.getVert 0 = x := SimpleGraph.Walk.getVert_zero p
    have := abs_sub_le_sum_abs_sub (fun i => g (p.getVert i) ^ 2) j
    rw [h0, hjspec] at this
    simpa using le_trans (le_abs_self _) (by simpa using this)
  refine le_trans htel ?_
  have hterm : ∀ i ∈ Finset.range j, |g (p.getVert i) ^ 2 - g (p.getVert (i + 1)) ^ 2|
      ≤ ∑ v ∈ G.neighborFinset (p.getVert i), |g (p.getVert i) ^ 2 - g v ^ 2| := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hadj : G.Adj (p.getVert i) (p.getVert (i + 1)) :=
      p.adj_getVert_succ (by omega)
    exact Finset.single_le_sum (f := fun v => |g (p.getVert i) ^ 2 - g v ^ 2|)
      (fun v _ => abs_nonneg _) ((SimpleGraph.mem_neighborFinset _ _ _).2 hadj)
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have hinj : Set.InjOn p.getVert ↑(Finset.range j) := by
    intro i hi i' hi' heq
    simp only [Finset.coe_range, Set.mem_Iio] at hi hi'
    exact hpath.getVert_injOn (by simp only [Set.mem_setOf_eq]; omega)
      (by simp only [Set.mem_setOf_eq]; omega) heq
  have himg : (Finset.range j).image p.getVert ⊆ T := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨i, hi, rfl⟩ := hy
    rw [Finset.mem_range] at hi
    exact hT _ (hmin i hi)
  have himage : ∑ y ∈ (Finset.range j).image p.getVert,
      (∑ v ∈ G.neighborFinset y, |g y ^ 2 - g v ^ 2|)
      = ∑ i ∈ Finset.range j,
          ∑ v ∈ G.neighborFinset (p.getVert i), |g (p.getVert i) ^ 2 - g v ^ 2| :=
    Finset.sum_image hinj
  rw [← himage]
  exact Finset.sum_le_sum_of_subset_of_nonneg himg
    (fun y _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)

theorem nash_ineq [Infinite V] (hG : G.Connected) (hdeg : ∀ v : V, 0 < G.degree v)
    (f : V → ℝ) (hf : ∀ y, 0 ≤ f y) (T : Finset V)
    (hT : ∀ y, f y ≠ 0 → y ∈ T) (hTN : ∀ y v : V, f y ≠ 0 → G.Adj y v → v ∈ T) :
    (∑ y ∈ T, (G.degree y : ℝ) * f y ^ 2) ^ 3
      ≤ 8 * (∑ y ∈ T, (G.degree y : ℝ) * f y) ^ 4
        * ((∑ y ∈ T, (G.degree y : ℝ) * f y ^ 2)
            - ∑ y ∈ T, (G.degree y : ℝ) * f y * walkOp G f y) := by
  classical
  have hWeq : ∑ y ∈ T, (G.degree y : ℝ) * f y * walkOp G f y
      = ∑ y ∈ T, ∑ v ∈ G.neighborFinset y, f y * f v := sum_degree_mul_walkOp hdeg f T
  rw [hWeq]
  set A := ∑ y ∈ T, (G.degree y : ℝ) * f y ^ 2 with hAdef
  set M := ∑ y ∈ T, (G.degree y : ℝ) * f y with hMdef
  set W := ∑ y ∈ T, ∑ v ∈ G.neighborFinset y, f y * f v with hWdef
  have hD : ∑ y ∈ T, ∑ v ∈ G.neighborFinset y, (f y - f v) ^ 2 = 2 * A - 2 * W :=
    sum_sq_sub_eq f T hT hTN
  have hP : ∑ y ∈ T, ∑ v ∈ G.neighborFinset y, (f y + f v) ^ 2 = 2 * A + 2 * W :=
    sum_sq_add_eq f T hT hTN
  have hDnn : (0:ℝ) ≤ 2 * A - 2 * W := by
    rw [← hD]
    exact Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun v _ => sq_nonneg _
  have hAnn : (0:ℝ) ≤ A := Finset.sum_nonneg fun y _ => by positivity
  have hMnn : (0:ℝ) ≤ M := Finset.sum_nonneg fun y _ => by
    have := hf y; positivity
  obtain ⟨x0, hx0⟩ : ∃ x0 : V, ∀ y ∈ T, f y ≤ f x0 := by
    rcases Finset.eq_empty_or_nonempty T with hTe | hTne
    · exact ⟨Classical.arbitrary V, by simp [hTe]⟩
    · obtain ⟨x0, _, hx0⟩ := T.exists_max_image f hTne
      exact ⟨x0, hx0⟩
  have hAle : A ≤ f x0 * M := by
    rw [hAdef, hMdef, Finset.mul_sum]
    refine Finset.sum_le_sum fun y hy => ?_
    have h1 : (0:ℝ) ≤ (G.degree y : ℝ) * f y := by have := hf y; positivity
    have h2 : (G.degree y : ℝ) * f y ^ 2 = ((G.degree y : ℝ) * f y) * f y := by ring
    rw [h2, show f x0 * ((G.degree y : ℝ) * f y) = ((G.degree y : ℝ) * f y) * f x0 by ring]
    exact mul_le_mul_of_nonneg_left (hx0 y hy) h1
  have hQ1 : f x0 ^ 2 ≤ ∑ y ∈ T, ∑ v ∈ G.neighborFinset y, |f y ^ 2 - f v ^ 2| :=
    sq_le_sum_abs_sub_sq hG f T hT x0
  have hQ2 := sum_abs_sub_sq_le (G := G) f T
  rw [hD, hP] at hQ2
  have hprod : (2 * A - 2 * W) * (2 * A + 2 * W) ≤ 8 * (A - W) * A := by
    nlinarith [sq_nonneg (A - W)]
  have hsqrt : Real.sqrt (2 * A - 2 * W) * Real.sqrt (2 * A + 2 * W)
      ≤ Real.sqrt (8 * (A - W) * A) := by
    rw [← Real.sqrt_mul hDnn]
    exact Real.sqrt_le_sqrt hprod
  have hkey : f x0 ^ 2 ≤ Real.sqrt (8 * (A - W) * A) := le_trans hQ1 (le_trans hQ2 hsqrt)
  have hEnn : (0:ℝ) ≤ A - W := by linarith
  have hnn8 : (0:ℝ) ≤ 8 * (A - W) * A := by positivity
  have hA2 : A ^ 2 ≤ f x0 ^ 2 * M ^ 2 := by
    have h := mul_le_mul hAle hAle hAnn (by nlinarith [hf x0, hMnn])
    nlinarith [hAle, hAnn]
  have hA4 : A ^ 4 ≤ 8 * (A - W) * A * M ^ 4 := by
    have h1 : (A ^ 2) ^ 2 ≤ (f x0 ^ 2 * M ^ 2) ^ 2 := by
      have : (0:ℝ) ≤ A ^ 2 := sq_nonneg A
      nlinarith [hA2, sq_nonneg A, sq_nonneg (f x0 ^ 2 * M ^ 2)]
    have h2 : (f x0 ^ 2) ^ 2 ≤ 8 * (A - W) * A := by
      have := Real.sq_sqrt hnn8
      nlinarith [hkey, sq_nonneg (f x0), Real.sqrt_nonneg (8 * (A - W) * A)]
    nlinarith [h1, h2, sq_nonneg (M ^ 2), pow_two_nonneg M]
  rcases eq_or_lt_of_le hAnn with hA0 | hApos
  · rw [← hA0]
    have hW0 : W ≤ 0 := by linarith
    have hM4 : (0:ℝ) ≤ M ^ 4 := by positivity
    nlinarith [hW0, hM4]
  · nlinarith [hA4, hApos]

end LatticeProb.Graph
