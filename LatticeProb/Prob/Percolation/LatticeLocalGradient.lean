import LatticeProb.Network.LocalCaccioppoli
import LatticeProb.Prob.Percolation.LatticeEuclideanCutoff
import LatticeProb.Prob.Percolation.RSW
import LatticeProb.Prob.Percolation.LatticeClusterL2
import LatticeProb.Prob.Percolation.RootedHarmonicMeasurableConsumer

/-! # Local energy estimate on an open component

A radial test function localizes the network Caccioppoli inequality to a component ball.
-/

open scoped BigOperators Classical

namespace LatticeProb.Percolation

noncomputable section

/-- Local harmonicity controls the weighted directed energy on the component ball. -/
theorem component_local_caccioppoli {d : ℕ} {ω : Configuration d}
    (C : OpenComponent ω) (x : C) (m : ℝ) (hm : 2 ≤ m) (f : C → ℝ)
    (hf : ∀ z ∈ componentEuclideanBall C x.val (2 * m), componentLaplacian C f z = 0) :
    let η := componentEuclideanCutoff C x ⟨m, by linarith⟩
    ∑ z ∈ componentEuclideanBall C x.val (4 * m),
      ∑ w ∈ (componentGraph C).neighborFinset z,
        Network.unitCond (componentGraph C) z w * (f z - f w) ^ 2 * η z ^ 2 ≤
    4 * ∑ z ∈ componentEuclideanBall C x.val (4 * m),
      ∑ w ∈ (componentGraph C).neighborFinset z,
        Network.unitCond (componentGraph C) z w * (f z ^ 2 + f w ^ 2) *
          (η z - η w) ^ 2 := by
  dsimp only
  apply Network.caccioppoli_of_support (Network.isCond_unitCond)
  · intro z hz
    rw [← componentLaplacian_eq_netLaplacian]
    exact hf z hz
  · intro z hz
    have hd : 2 * m ≤ dist (latticeEuclideanEmbedding z.val)
        (latticeEuclideanEmbedding x.val) := by
      exact le_of_not_gt (fun h => hz ((mem_componentEuclideanBall C x.val _ z).mpr h))
    rw [componentEuclideanCutoff_eq_zero C x z ⟨m, by linarith⟩ hd]
    ring
  · exact componentEuclideanBall_mono C x.val (by linarith)
  · intro z hz w hzw
    apply (mem_componentEuclideanBall C x.val _ w).mpr
    have hz' := (mem_componentEuclideanBall C x.val _ z).mp hz
    have he : dist (latticeEuclideanEmbedding w.val) (latticeEuclideanEmbedding z.val) = 1 :=
      dist_embedding_adj hzw.symm
    have ht := dist_triangle (latticeEuclideanEmbedding w.val)
      (latticeEuclideanEmbedding z.val) (latticeEuclideanEmbedding x.val)
    linarith

/-- A component ball has no more vertices than its containing lattice box. -/
theorem componentEuclideanBall_card_le_box {d : ℕ} {ω : Configuration d}
    (C : OpenComponent ω) (z : Vertex d) (r : ℝ) :
    ((componentEuclideanBall C z r).card : ℝ) ≤ (2 * (⌈r⌉₊ : ℝ) + 1) ^ d := by
  classical
  have hs : (componentEuclideanBall C z r).image Subtype.val ⊆ boxFinset z ⌈r⌉₊ := by
    intro y hy
    rw [mem_image_componentEuclideanBall] at hy
    apply mem_boxFinset_iff.mpr
    intro i
    have hi := PiLp.norm_apply_le (latticeEuclideanEmbedding y - latticeEuclideanEmbedding z) i
    change |(y i : ℝ) - (z i : ℝ)| ≤
      ‖latticeEuclideanEmbedding y - latticeEuclideanEmbedding z‖ at hi
    have hb : |(y i : ℝ) - (z i : ℝ)| ≤ (⌈r⌉₊ : ℝ) :=
      (hi.trans_lt hy.2).le.trans (Nat.le_ceil r)
    exact_mod_cast hb
  have hc : (componentEuclideanBall C z r).card ≤ (boxFinset z ⌈r⌉₊).card := by
    calc
      _ = ((componentEuclideanBall C z r).image Subtype.val).card :=
        (Finset.card_image_of_injective _ Subtype.val_injective).symm
      _ ≤ _ := Finset.card_le_card hs
  rw [card_boxFinset] at hc
  exact_mod_cast hc

/-- The four-radius component ball has polynomial cardinality uniformly in the configuration. -/
theorem componentEuclideanBall_card_four_mul {d : ℕ} {ω : Configuration d}
    (C : OpenComponent ω) (z : Vertex d) (m : ℝ) (hm : 2 ≤ m) :
    ((componentEuclideanBall C z (4 * m)).card : ℝ) ≤ (10 * m) ^ d := by
  have hc := componentEuclideanBall_card_le_box C z (4 * m)
  have hceil := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ 4 * m by linarith)
  have hb : 2 * (⌈4 * m⌉₊ : ℝ) + 1 ≤ 10 * m := by linarith
  exact hc.trans (pow_le_pow_left₀ (by positivity) hb d)

/-- A genuine edge from the center is bounded by the cutoff energy. -/
theorem component_edge_le_cutoff_energy {d : ℕ} {ω : Configuration d}
    (C : OpenComponent ω) (x y : C) (m : ℝ) (hm : 2 ≤ m) (f : C → ℝ)
    (hxy : (componentGraph C).Adj x y)
    (hf : ∀ z ∈ componentEuclideanBall C x.val (2 * m), componentLaplacian C f z = 0) :
    let η := componentEuclideanCutoff C x ⟨m, by linarith⟩
    (f x - f y) ^ 2 ≤
    4 * ∑ z ∈ componentEuclideanBall C x.val (4 * m),
      ∑ w ∈ (componentGraph C).neighborFinset z,
        Network.unitCond (componentGraph C) z w * (f z ^ 2 + f w ^ 2) *
          (η z - η w) ^ 2 := by
  dsimp only
  let η := componentEuclideanCutoff C x ⟨m, by linarith⟩
  have hx : x ∈ componentEuclideanBall C x.val (4 * m) :=
    center_mem_componentEuclideanBall C x (by linarith)
  have hy : y ∈ (componentGraph C).neighborFinset x :=
    (SimpleGraph.mem_neighborFinset _ _ _).mpr hxy
  have hnn (z w : C) : 0 ≤ Network.unitCond (componentGraph C) z w *
      (f z - f w) ^ 2 * η z ^ 2 :=
    mul_nonneg (mul_nonneg (Network.isCond_unitCond.nonneg z w) (sq_nonneg _)) (sq_nonneg _)
  have he : (∑ w ∈ (componentGraph C).neighborFinset x,
      Network.unitCond (componentGraph C) x w * (f x - f w) ^ 2 * η x ^ 2) ≤
      ∑ z ∈ componentEuclideanBall C x.val (4 * m),
        ∑ w ∈ (componentGraph C).neighborFinset z,
          Network.unitCond (componentGraph C) z w * (f z - f w) ^ 2 * η z ^ 2 :=
    Finset.single_le_sum (fun z _ => show 0 ≤ ∑ w ∈ (componentGraph C).neighborFinset z,
      Network.unitCond (componentGraph C) z w * (f z - f w) ^ 2 * η z ^ 2 from
        Finset.sum_nonneg (fun w _ => hnn z w)) hx
  have he' : Network.unitCond (componentGraph C) x y * (f x - f y) ^ 2 * η x ^ 2 ≤
      ∑ w ∈ (componentGraph C).neighborFinset x,
        Network.unitCond (componentGraph C) x w * (f x - f w) ^ 2 * η x ^ 2 :=
    Finset.single_le_sum (fun w _ => hnn x w) hy
  have hη : η x = 1 :=
    componentEuclideanCutoff_eq_one C x x ⟨m, by linarith⟩ (by simp; linarith)
  have hunit : Network.unitCond (componentGraph C) x y = 1 := by
    simp [Network.unitCond, hxy]
  have hpoint : (f x - f y) ^ 2 ≤
      ∑ z ∈ componentEuclideanBall C x.val (4 * m),
        ∑ w ∈ (componentGraph C).neighborFinset z,
          Network.unitCond (componentGraph C) z w * (f z - f w) ^ 2 * η z ^ 2 := by
    simpa only [hunit, hη, one_mul, one_pow, mul_one] using he'.trans he
  exact hpoint.trans (component_local_caccioppoli C x m hm f hf)

/-- The sum of both endpoint weights on internal directed edges is bounded by the degree. -/
theorem directed_endpoint_sum_le {V : Type*} (G : SimpleGraph V) [G.LocallyFinite]
    (S : Finset V) (a : V → ℝ) (D : ℕ) (ha : ∀ x ∈ S, 0 ≤ a x)
    (hD : ∀ x ∈ S, G.degree x ≤ D) :
    (∑ x ∈ S, ∑ y ∈ S, if G.Adj x y then a x + a y else 0) ≤
      2 * D * ∑ x ∈ S, a x := by
  classical
  have hone (x : V) (hx : x ∈ S) :
      (∑ y ∈ S, if G.Adj x y then a x else 0) ≤ D * a x := by
    have hcard : (S.filter (G.Adj x)).card ≤ D := by
      calc
        _ ≤ (G.neighborFinset x).card := Finset.card_le_card (by
          intro y hy
          exact (SimpleGraph.mem_neighborFinset _ _ _).mpr (Finset.mem_filter.mp hy).2)
        _ = G.degree x := SimpleGraph.card_neighborFinset_eq_degree G x
        _ ≤ D := hD x hx
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (ha x hx)
  have hsym : (∑ x ∈ S, ∑ y ∈ S, if G.Adj x y then a y else 0) =
      ∑ x ∈ S, ∑ y ∈ S, if G.Adj x y then a x else 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    rw [G.adj_comm]
  have hsplit : (∑ x ∈ S, ∑ y ∈ S, if G.Adj x y then a x + a y else 0) =
      (∑ x ∈ S, ∑ y ∈ S, if G.Adj x y then a x else 0) +
        ∑ x ∈ S, ∑ y ∈ S, if G.Adj x y then a y else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x hx
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro y hy
    split_ifs <;> ring
  rw [hsplit, hsym]
  have hsum : (∑ x ∈ S, ∑ y ∈ S, if G.Adj x y then a x else 0) ≤
      D * ∑ x ∈ S, a x := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hone
  linarith

/-- The cutoff energy is bounded by the square sum on the four-radius ball. -/
theorem component_cutoff_energy_le {d : ℕ} {ω : Configuration d}
    (C : OpenComponent ω) (x : C) (m : ℝ) (hm : 2 ≤ m) (f : C → ℝ) :
    let η := componentEuclideanCutoff C x ⟨m, by linarith⟩
    ∑ z ∈ componentEuclideanBall C x.val (4 * m),
      ∑ w ∈ (componentGraph C).neighborFinset z,
        Network.unitCond (componentGraph C) z w * (f z ^ 2 + f w ^ 2) *
          (η z - η w) ^ 2 ≤
      (4 * d : ℝ) * (1 / m) ^ 2 *
        ∑ z ∈ componentEuclideanBall C x.val (4 * m), f z ^ 2 := by
  dsimp only
  let S := componentEuclideanBall C x.val (4 * m)
  let η := componentEuclideanCutoff C x ⟨m, by linarith⟩
  let F (z w : C) := if (componentGraph C).Adj z w ∧ w ∈ S then
    (f z ^ 2 + f w ^ 2) * (1 / m) ^ 2 else 0
  have hout (z w : C) (hzw : (componentGraph C).Adj z w) (hw : w ∉ S) :
      η z = 0 ∧ η w = 0 := by
    have hw' : 4 * m ≤ dist (latticeEuclideanEmbedding w.val)
        (latticeEuclideanEmbedding x.val) := by
      exact le_of_not_gt (fun h => hw ((mem_componentEuclideanBall C x.val _ w).mpr h))
    have he : dist (latticeEuclideanEmbedding w.val) (latticeEuclideanEmbedding z.val) = 1 :=
      dist_embedding_adj hzw.symm
    have ht := dist_triangle (latticeEuclideanEmbedding w.val)
      (latticeEuclideanEmbedding z.val) (latticeEuclideanEmbedding x.val)
    constructor
    · exact componentEuclideanCutoff_eq_zero C x z ⟨m, by linarith⟩ (by linarith)
    · exact componentEuclideanCutoff_eq_zero C x w ⟨m, by linarith⟩ (by linarith)
  have hpoint (z w : C) (hzw : (componentGraph C).Adj z w) :
      Network.unitCond (componentGraph C) z w * (f z ^ 2 + f w ^ 2) *
        (η z - η w) ^ 2 ≤ F z w := by
    have hu : Network.unitCond (componentGraph C) z w = 1 := by simp [Network.unitCond, hzw]
    by_cases hw : w ∈ S
    · have hd := componentEuclideanCutoff_adj C x z w ⟨m, by linarith⟩ hzw
      have hs : (η z - η w) ^ 2 ≤ (1 / m) ^ 2 := by
        have hn : 0 ≤ (1 / m : ℝ) := by positivity
        have h := (sq_le_sq₀ (abs_nonneg (η z - η w)) hn).2 hd
        simpa only [sq_abs] using h
      simp only [F, hzw, hw, and_self, if_true, hu, one_mul]
      exact mul_le_mul_of_nonneg_left hs (add_nonneg (sq_nonneg _) (sq_nonneg _))
    · obtain ⟨hz0, hw0⟩ := hout z w hzw hw
      simp [F, hw, hz0, hw0]
  have hinner (z : C) :
      (∑ w ∈ (componentGraph C).neighborFinset z, F z w) = ∑ w ∈ S, F z w := by
    apply Network.sum_neighborFinset_eq_sum
    · intro w hw
      simp [F, hw]
    · intro w hw hn
      by_contra hnot
      exact hn (by simp [F, hnot])
  have hmatrix : (∑ z ∈ S, ∑ w ∈ S, F z w) =
      (∑ z ∈ S, ∑ w ∈ S,
        if (componentGraph C).Adj z w then f z ^ 2 + f w ^ 2 else 0) * (1 / m) ^ 2 := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro z hz
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro w hw
    simp [F, hw]
  calc
    _ ≤ ∑ z ∈ S, ∑ w ∈ (componentGraph C).neighborFinset z, F z w := by
      apply Finset.sum_le_sum
      intro z hz
      apply Finset.sum_le_sum
      intro w hw
      exact hpoint z w ((SimpleGraph.mem_neighborFinset _ _ _).mp hw)
    _ = ∑ z ∈ S, ∑ w ∈ S, F z w := Finset.sum_congr rfl (fun z _ => hinner z)
    _ = _ := hmatrix
    _ ≤ (2 * (2 * d) * ∑ z ∈ S, f z ^ 2) * (1 / m) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        directed_endpoint_sum_le (componentGraph C) S (fun z => f z ^ 2) (2 * d)
          (fun z _ => sq_nonneg _) (fun z _ => componentGraph_degree_le C z)
    _ = _ := by ring

/-- The gradient at an open edge is controlled by the normalized local L² norm. -/
theorem component_local_gradient (d : ℕ) (hd : 2 ≤ d) :
    ∃ K : ℝ, 0 < K ∧ ∀ (ω : Configuration d) (C : OpenComponent ω) (x y : C)
      (m : ℝ), 2 ≤ m → ∀ f : C → ℝ, (componentGraph C).Adj x y →
      (∀ z ∈ componentEuclideanBall C x.val (2 * m), componentLaplacian C f z = 0) →
      (f x - f y) ^ 2 ≤ K * m ^ (d - 2) * (componentBallL2 C x.val (4 * m) f) ^ 2 := by
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  refine ⟨16 * (d : ℝ) * 10 ^ d, by positivity, ?_⟩
  intro ω C x y m hm f hxy hf
  let S := componentEuclideanBall C x.val (4 * m)
  let A := ∑ z ∈ S, f z ^ 2
  let N := componentBallL2 C x.val (4 * m) f
  have hmp : 0 < m := by linarith
  have hcpos : (0 : ℝ) < S.card := by
    exact_mod_cast (Finset.card_pos.mpr
      ⟨x, center_mem_componentEuclideanBall C x (by linarith)⟩)
  have hN : N ^ 2 = A / S.card := by
    dsimp [N, A, S, componentBallL2]
    exact Real.sq_sqrt (div_nonneg (Finset.sum_nonneg (fun z _ => sq_nonneg _))
      (Nat.cast_nonneg _))
  have hsum : A = (S.card : ℝ) * N ^ 2 := by rw [hN]; field_simp
  have hcard : (S.card : ℝ) ≤ (10 * m) ^ d := componentEuclideanBall_card_four_mul C x.val m hm
  have hsum_le : A ≤ (10 * m) ^ d * N ^ 2 := by
    rw [hsum]
    exact mul_le_mul_of_nonneg_right hcard (sq_nonneg N)
  have he := component_edge_le_cutoff_energy C x y m hm f hxy hf
  have hb := component_cutoff_energy_le C x m hm f
  have hgrad : (f x - f y) ^ 2 ≤ (16 * d : ℝ) * (1 / m) ^ 2 * A := by
    dsimp only at he hb
    dsimp [A, S]
    nlinarith
  have hpow : m ^ d = m ^ (d - 2) * m ^ 2 := by
    rw [← pow_add, Nat.sub_add_cancel hd]
  calc
    _ ≤ (16 * d : ℝ) * (1 / m) ^ 2 * A := hgrad
    _ ≤ (16 * d : ℝ) * (1 / m) ^ 2 * ((10 * m) ^ d * N ^ 2) := by
      exact mul_le_mul_of_nonneg_left hsum_le (by positivity)
    _ = (16 * (d : ℝ) * 10 ^ d) * m ^ (d - 2) * N ^ 2 := by
      rw [mul_pow, hpow]
      field_simp

/-- The estimate applies to a nonconstant harmonic function on the fully open plane. -/
theorem allOpen_two_local_gradient_witness :
    let C := (openGraph (allOpen 2)).connectedComponentMk (0 : Vertex 2)
    ∃ (x y : C) (K : ℝ), 0 < K ∧ (componentGraph C).Adj x y ∧
      (∀ z : C, componentLaplacian C (fun w => (w.val (0 : Fin 2) : ℝ)) z = 0) ∧
      ((x.val (0 : Fin 2) : ℝ) - (y.val (0 : Fin 2) : ℝ)) ^ 2 = 1 ∧
      0 < componentBallL2 C x.val 8 (fun w => (w.val (0 : Fin 2) : ℝ)) ∧
      1 ≤ K * (componentBallL2 C x.val 8 (fun w => (w.val (0 : Fin 2) : ℝ))) ^ 2 := by
  dsimp only
  let C := (openGraph (allOpen 2)).connectedComponentMk (0 : Vertex 2)
  have hy : unit (0 : Fin 2) ∈ C.supp :=
    C.mem_supp_of_adj_mem_supp SimpleGraph.ConnectedComponent.connectedComponentMk_mem
      allOpen_two_unit_adj
  let x : C := ⟨0, SimpleGraph.ConnectedComponent.connectedComponentMk_mem⟩
  let y : C := ⟨unit 0, hy⟩
  let f : C → ℝ := fun w => (w.val (0 : Fin 2) : ℝ)
  have hxy : (componentGraph C).Adj x y := allOpen_two_unit_adj
  have hh : ∀ z : C, componentLaplacian C f z = 0 := allOpen_root_component_coordinate_harmonic
  have hyball : y ∈ componentEuclideanBall C x.val 8 := by
    apply (mem_componentEuclideanBall C x.val 8 y).mpr
    have hdist : dist (latticeEuclideanEmbedding y.val) (latticeEuclideanEmbedding x.val) = 1 :=
      dist_embedding_adj hxy.symm
    linarith
  have hnz : componentBallL2 C x.val 8 f ≠ 0 := by
    intro h
    have hv := (componentBallL2_eq_zero_iff C x.val 8 f).mp h y hyball
    norm_num [f, y, unit, Pi.single_apply] at hv
  have hnpos : 0 < componentBallL2 C x.val 8 f :=
    lt_of_le_of_ne (componentBallL2_nonneg C x.val 8 f) (Ne.symm hnz)
  obtain ⟨K, hKpos, hK⟩ := component_local_gradient 2 (by norm_num)
  have hbound := hK (allOpen 2) C x y 2 (by norm_num) f hxy (fun z _ => hh z)
  refine ⟨x, y, K, hKpos, hxy, hh, ?_, hnpos, ?_⟩
  · norm_num [x, y, unit, Pi.single_apply]
  · norm_num [f, x, y, C, unit, Pi.single_apply] at hbound ⊢
    exact hbound

end
end LatticeProb.Percolation
