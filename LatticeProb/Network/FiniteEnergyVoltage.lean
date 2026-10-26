import LatticeProb.Network.VoltageConnected

/-!
# Bounded finite-energy voltages on connected graphs

Finite killed dipoles have ordered gradient energy equal to twice their source-to-sink
voltage drop. Their normalized compactness limit therefore has bounded finite partial
ordered energy, including on recurrent graphs.
-/

open Finset Filter Topology
open scoped Classical

namespace LatticeProb.Network

open LatticeProb.Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- An adjacent ordered-pair sum is bounded by the energy indexed by its first endpoints. -/
theorem sum_sq_sub_le_energyOn (f : V → ℝ) (S : Finset V) (F : Finset (V × V))
    (hF : ∀ e ∈ F, G.Adj e.1 e.2) (hS : ∀ e ∈ F, e.1 ∈ S) :
    ∑ e ∈ F, (f e.1 - f e.2) ^ 2 ≤ energyOn G (unitCond G) S f := by
  let E := S.biUnion fun x => (G.neighborFinset x).image fun y => (x, y)
  have hFE : F ⊆ E := by
    intro e he
    exact Finset.mem_biUnion.mpr ⟨e.1, hS e he,
      Finset.mem_image.mpr ⟨e.2, (SimpleGraph.mem_neighborFinset _ _ _).mpr (hF e he), rfl⟩⟩
  have hdisj : Set.PairwiseDisjoint (↑S : Set V)
      (fun x => (G.neighborFinset x).image fun y => (x, y)) := by
    intro x _ y _ hxy
    apply Finset.disjoint_left.mpr
    intro e hex hey
    obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hex
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hey
    exact hxy (congrArg Prod.fst (hu.trans hv.symm))
  calc
    _ ≤ ∑ e ∈ E, (f e.1 - f e.2) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hFE (fun e _ _ => sq_nonneg _)
    _ = energyOn G (unitCond G) S f := by
      rw [energyOn_eq_sum, Finset.sum_biUnion hdisj]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.sum_image (fun y _ z _ h => (Prod.mk.inj h).2)]
      refine Finset.sum_congr rfl fun y hy => ?_
      rw [unitCond, if_pos ((SimpleGraph.mem_neighborFinset _ _ _).mp hy), one_mul]

/-- The killed dipole's energy counts both orientations of every edge, hence the factor two. -/
theorem energyOn_dipole (hG : G.Connected) (C S : Finset V) {a b q : V}
    (ha : a ∈ C) (hb : b ∈ C) (hq : q ∉ C) (hCS : C ⊆ S)
    (hnb : ∀ x ∈ C, ∀ y, G.Adj x y → y ∈ S) :
    energyOn G (unitCond G) S (dipole G C a b) =
      2 * (dipole G C a b a - dipole G C a b b) := by
  rw [energyOn_eq_neg_two_mul isCond_unitCond S C _
    (fun x hx => dipole_vanishes hG C hq hx) hCS hnb]
  have hlap : ∀ x ∈ C, dipole G C a b x *
      netLaplacian G (unitCond G) (dipole G C a b) x =
      (if x = b then dipole G C a b x else 0) -
        (if x = a then dipole G C a b x else 0) := by
    intro x hx
    rw [netLaplacian_unitCond, laplacian_dipole hG C ha hb hq hx]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl hlap, Finset.sum_sub_distrib,
    Finset.sum_ite_eq' C b, Finset.sum_ite_eq' C a, if_pos hb, if_pos ha]
  ring

/-- Every finite ordered edge sum of a killed dipole is at most twice a fixed walk length. -/
theorem dipole_partial_energy_le (hG : G.Connected) (C : Finset V) {a b q : V}
    (ha : a ∈ C) (hb : b ∈ C) (hq : q ∉ C) (p : G.Walk a b)
    (hp : ∀ z ∈ p.support, z ∈ C) (F : Finset (V × V))
    (hF : ∀ e ∈ F, G.Adj e.1 e.2) :
    ∑ e ∈ F, (dipole G C a b e.1 - dipole G C a b e.2) ^ 2 ≤ 2 * p.length := by
  let S := nbhd G C ∪ F.image Prod.fst
  have hbound := sum_sq_sub_le_energyOn (dipole G C a b) S F hF
    (fun e he => Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, he, rfl⟩))
  rw [energyOn_dipole hG C S ha hb hq
    (fun x hx => Finset.mem_union_left _ (subset_nbhd C hx))
    (fun x hx y hxy => Finset.mem_union_left _ (mem_nbhd_of_adj hx hxy))] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_left (dipole_walk_le hG C ha hb hq p hp)
    (by norm_num))

/-- An infinite connected locally finite graph admits a sink-normalized bounded unit voltage
with uniformly bounded finite ordered gradient energy. No transience hypothesis is needed. -/
theorem exists_finite_energy_voltage_of_connected [Infinite V] (hG : G.Connected)
    {a b : V} (_hab : a ≠ b) :
    ∃ f : V → ℝ, ∃ M : ℝ, 0 < M ∧ f b = 0 ∧
      (∀ x, 0 ≤ f x ∧ f x ≤ M) ∧
      (∀ x, laplacian G f x =
        (if x = b then (1 : ℝ) else 0) - (if x = a then 1 else 0)) ∧
      ∃ K : ℝ, ∀ F : Finset (V × V), (∀ e ∈ F, G.Adj e.1 e.2) →
        ∑ e ∈ F, (f e.1 - f e.2) ^ 2 ≤ K := by
  obtain ⟨p⟩ := hG.preconnected a b
  set n : ℝ := (p.length : ℝ) with hn
  set P : Finset V := p.support.toFinset with hP
  let h : Finset V → V → ℝ := fun C x => dipole G C a b x - dipole G C a b b
  have haP : a ∈ P := List.mem_toFinset.mpr (SimpleGraph.Walk.start_mem_support p)
  have hbP : b ∈ P := List.mem_toFinset.mpr (SimpleGraph.Walk.end_mem_support p)
  have hbox : ∀ C : Finset V, P ⊆ C → ∀ x, 0 ≤ h C x ∧ h C x ≤ n := by
    intro C hPC x
    obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset C
    have ha := hPC haP
    have hb := hPC hbP
    refine ⟨by linarith [sink_le_dipole hG C ha hb hq x], ?_⟩
    have h1 := dipole_le_source hG C ha hb hq x
    have h2 := dipole_walk_le hG C ha hb hq p
      (fun z hz => hPC (List.mem_toFinset.mpr hz))
    show dipole G C a b x - dipole G C a b b ≤ n
    linarith
  set B : Set (V → ℝ) := Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) n
  have hBc : IsCompact B := isCompact_univ_pi fun _ => isCompact_Icc
  have hFB : Filter.map h atTop ≤ 𝓟 B := by
    rw [Filter.le_principal_iff, Filter.mem_map]
    refine Filter.mem_of_superset (Filter.Ici_mem_atTop P) fun C hC => ?_
    intro x _
    exact hbox C hC x
  obtain ⟨f, hfB, hclus⟩ := hBc hFB
  have hclosed : ∀ Z : Set (V → ℝ), IsClosed Z → Z ∈ Filter.map h atTop → f ∈ Z := by
    intro Z hZ hZF
    have hcl : f ∈ closure Z :=
      mem_closure_iff_clusterPt.mpr (hclus.mono (Filter.le_principal_iff.mpr hZF))
    rwa [hZ.closure_eq] at hcl
  refine ⟨f, n + 1, by positivity, ?_, ?_, ?_, 2 * n, ?_⟩
  · apply hclosed {g | g b = 0} (isClosed_eq (continuous_apply b) continuous_const)
    rw [Filter.mem_map]
    exact Filter.Eventually.of_forall fun C => sub_self (dipole G C a b b)
  · intro x
    have := hfB x (Set.mem_univ x)
    exact ⟨this.1, by linarith [this.2]⟩
  · intro x
    apply hclosed {g | laplacian G g x =
      (if x = b then (1 : ℝ) else 0) - (if x = a then 1 else 0)}
    · refine isClosed_eq ?_ continuous_const
      show Continuous fun g : V → ℝ => ∑ y ∈ G.neighborFinset x, (g y - g x)
      exact continuous_finsetSum _ fun y _ => (continuous_apply y).sub (continuous_apply x)
    · rw [Filter.mem_map]
      refine Filter.mem_of_superset (Filter.Ici_mem_atTop (insert x P)) fun C hC => ?_
      obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset C
      show laplacian G (fun v => dipole G C a b v - dipole G C a b b) x = _
      rw [laplacian_sub_const]
      exact laplacian_dipole hG C (hC (Finset.mem_insert_of_mem haP))
        (hC (Finset.mem_insert_of_mem hbP)) hq (hC (Finset.mem_insert_self x P))
  · intro F hF
    apply hclosed {g | ∑ e ∈ F, (g e.1 - g e.2) ^ 2 ≤ 2 * n}
    · apply isClosed_le _ continuous_const
      exact continuous_finsetSum _ fun e _ =>
        ((continuous_apply e.1).sub (continuous_apply e.2)).pow 2
    · rw [Filter.mem_map]
      refine Filter.mem_of_superset (Filter.Ici_mem_atTop P) fun C hC => ?_
      obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset C
      have he := dipole_partial_energy_le hG C (hC haP) (hC hbP) hq p
        (fun z hz => hC (List.mem_toFinset.mpr hz)) F hF
      change ∑ e ∈ F, ((dipole G C a b e.1 - dipole G C a b b) -
        (dipole G C a b e.2 - dipole G C a b b)) ^ 2 ≤ 2 * n
      simpa only [sub_sub_sub_cancel_right] using he

end LatticeProb.Network
