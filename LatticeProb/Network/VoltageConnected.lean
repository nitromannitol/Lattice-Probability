/-
The voltage function on an infinite connected graph, recurrent or not.

`LatticeProb/Network/Voltage.lean` builds a bounded nonnegative `f` with
`Δf = δ_b - δ_a` from the Green function, which needs transience.  This file
removes that hypothesis.  For a finite set `C` containing `a` and `b`, the dipole
potential

    f_C(x) = g_C(a,x) - g_C(b,x)

built from the Green function killed off `C` has Laplacian `δ_b - δ_a` on `C` and
vanishes off `C`.  By the maximum principle it lies between `f_C(b) ≤ 0` and
`f_C(a) ≥ 0`, and by Kirchhoff's node law applied to a superlevel or sublevel set
the current along any edge inside `C` is at most one, so `f_C(a) - f_C(b)` is at
most the length of a fixed walk from `a` to `b`.  The shifted potentials
`f_C - f_C(b)` therefore take values in a fixed compact box `[0,n]^V`; a cluster
point along the exhaustion by finite sets is the voltage function, because the
Laplacian at a vertex is a finite sum and hence continuous in the product topology.
-/
import LatticeProb.Network.Variational
import LatticeProb.Network.MaximumPrinciple
import LatticeProb.Network.Escape

open Finset Filter Topology
open scoped Classical

namespace LatticeProb.Network

open LatticeProb.Graph

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- The dipole potential of the finite set `C`: the difference of the killed Green
functions with sources `a` and `b`. -/
noncomputable def dipole (G : SimpleGraph V) [G.LocallyFinite] (C : Finset V) (a b : V)
    (x : V) : ℝ :=
  killedGreenReal G (C : Set V) a x - killedGreenReal G (C : Set V) b x

theorem laplacian_sub_const (f : V → ℝ) (c : ℝ) (x : V) :
    laplacian G (fun v => f v - c) x = laplacian G f x := by
  rw [laplacian, laplacian]
  exact Finset.sum_congr rfl fun y _ => by ring

section
variable (hG : G.Connected) (C : Finset V) {a b q : V} (ha : a ∈ C) (hb : b ∈ C) (hq : q ∉ C)
include hG ha hb hq

theorem laplacian_dipole {x : V} (hx : x ∈ C) :
    laplacian G (dipole G C a b) x
      = (if x = b then (1 : ℝ) else 0) - (if x = a then 1 else 0) := by
  show laplacian G (fun v => killedGreenReal G (C : Set V) a v
    - killedGreenReal G (C : Set V) b v) x = _
  rw [laplacian_sub, laplacian_killedGreenReal hG C ha hq (by exact_mod_cast hx),
    laplacian_killedGreenReal hG C hb hq (by exact_mod_cast hx)]
  ring

omit hb in
theorem killedGreenReal_le_diag (x : V) :
    killedGreenReal G (C : Set V) a x ≤ killedGreenReal G (C : Set V) a a := by
  refine le_of_harmonicOn hG isCond_unitCond C {a} (killedGreenReal G (C : Set V) a)
    (killedGreenReal G (C : Set V) a a) hq ?_ ?_ ?_ x
  · intro z hz hza
    rw [netLaplacian_unitCond]
    exact harmonic_killedGreenReal hG C ha hq (by exact_mod_cast hz) hza
  · intro z hz
    rw [killedGreen_vanishes hG C hq (by exact_mod_cast hz)]
    exact killedGreenReal_nonneg hG C hq a a
  · intro z hz
    rw [Set.mem_singleton_iff.mp hz]

omit hb in
theorem dipole_source_nonneg : 0 ≤ dipole G C a b a := by
  have h2 := killedGreenReal_le_diag hG C ha hq b
  rw [killedGreenReal_symm hG C hq a b] at h2
  rw [dipole]
  linarith

omit ha in
theorem dipole_sink_nonpos : dipole G C a b b ≤ 0 := by
  have h1 := killedGreenReal_le_diag hG C hb hq a
  rw [killedGreenReal_symm hG C hq b a] at h1
  rw [dipole]
  linarith

omit ha hb in
theorem dipole_vanishes {x : V} (hx : x ∉ C) : dipole G C a b x = 0 := by
  rw [dipole, killedGreen_vanishes hG C hq (by exact_mod_cast hx),
    killedGreen_vanishes hG C hq (by exact_mod_cast hx), sub_zero]

theorem dipole_le_source (x : V) : dipole G C a b x ≤ dipole G C a b a := by
  refine le_of_harmonicOn hG isCond_unitCond C {a, b} (dipole G C a b)
    (dipole G C a b a) hq ?_ ?_ ?_ x
  · intro z hz hzab
    have hza : z ≠ a := fun h => hzab (by simp [h])
    have hzb : z ≠ b := fun h => hzab (by simp [h])
    rw [netLaplacian_unitCond, laplacian_dipole hG C ha hb hq hz, if_neg hza, if_neg hzb]
    ring
  · intro z hz
    rw [dipole_vanishes hG C hq hz]
    exact dipole_source_nonneg (b := b) hG C ha hq
  · intro z hz
    rcases hz with rfl | hz
    · exact le_rfl
    · rw [Set.mem_singleton_iff.mp hz]
      linarith [dipole_source_nonneg (b := b) hG C ha hq, dipole_sink_nonpos (a := a) hG C hb hq]

theorem sink_le_dipole (x : V) : dipole G C a b b ≤ dipole G C a b x := by
  have key := le_of_harmonicOn hG isCond_unitCond C {a, b} (fun v => -dipole G C a b v)
    (-dipole G C a b b) hq ?_ ?_ ?_ x
  · linarith
  · intro z hz hzab
    have hza : z ≠ a := fun h => hzab (by simp [h])
    have hzb : z ≠ b := fun h => hzab (by simp [h])
    rw [netLaplacian_unitCond, laplacian_neg, laplacian_dipole hG C ha hb hq hz, if_neg hza,
      if_neg hzb]
    ring
  · intro z hz
    show -dipole G C a b z ≤ -dipole G C a b b
    rw [dipole_vanishes hG C hq hz]
    linarith [dipole_sink_nonpos (a := a) hG C hb hq]
  · intro z hz
    show -dipole G C a b z ≤ -dipole G C a b b
    rcases hz with h | hz
    · rw [h]
      linarith [dipole_source_nonneg (b := b) hG C ha hq, dipole_sink_nonpos (a := a) hG C hb hq]
    · rw [Set.mem_singleton_iff.mp hz]

end

/-- A single edge current out of a set is at most the total flux when every
current out of the set is nonnegative. -/
theorem sub_le_one_of_flux {f : V → ℝ} {U : Finset V} {o : V} (ho : o ∈ U)
    (hlap : ∀ z ∈ U, netLaplacian G (unitCond G) f z = -(if z = o then (1 : ℝ) else 0))
    (hout : ∀ z ∈ U, ∀ w, G.Adj z w → w ∉ U → f w ≤ f z)
    {x y : V} (hx : x ∈ U) (hy : y ∉ U) (hxy : G.Adj x y) : f x - f y ≤ 1 := by
  have hflux := flux_eq_one isCond_unitCond f U ho hlap
  have hterm : ∀ z ∈ U, ∀ w ∈ (G.neighborFinset z).filter (fun w => w ∉ U),
      0 ≤ current G (unitCond G) f z w := by
    intro z hz w hw
    obtain ⟨hwn, hwU⟩ := Finset.mem_filter.mp hw
    have hadj : G.Adj z w := (SimpleGraph.mem_neighborFinset _ _ _).mp hwn
    rw [current]
    exact mul_nonneg (isCond_unitCond.nonneg z w) (by linarith [hout z hz w hadj hwU])
  have hinner : ∀ z ∈ U,
      0 ≤ ∑ w ∈ (G.neighborFinset z).filter (fun w => w ∉ U), current G (unitCond G) f z w :=
    fun z hz => Finset.sum_nonneg (hterm z hz)
  have hyf : y ∈ (G.neighborFinset x).filter (fun w => w ∉ U) :=
    Finset.mem_filter.mpr ⟨(SimpleGraph.mem_neighborFinset _ _ _).mpr hxy, hy⟩
  have h1 : current G (unitCond G) f x y
      ≤ ∑ w ∈ (G.neighborFinset x).filter (fun w => w ∉ U), current G (unitCond G) f x w :=
    Finset.single_le_sum (hterm x hx) hyf
  have h2 := Finset.single_le_sum hinner hx
  rw [← flux] at h2
  rw [current, unitCond, if_pos hxy, one_mul] at h1
  linarith

section
variable (hG : G.Connected) (C : Finset V) {a b q : V} (ha : a ∈ C) (hb : b ∈ C) (hq : q ∉ C)
include hG ha hb hq

/-- The current of the dipole potential along an edge inside `C` is at most one. -/
theorem dipole_edge_le {x y : V} (hx : x ∈ C) (hy : y ∈ C) (hxy : G.Adj x y) :
    dipole G C a b x - dipole G C a b y ≤ 1 := by
  set f := dipole G C a b with hf
  by_cases hlt : f y < f x
  swap
  · linarith [not_lt.mp hlt]
  have hfa := dipole_le_source hG C ha hb hq x
  have hfb := sink_le_dipole hG C ha hb hq y
  by_cases hsign : 0 ≤ f x
  · -- the superlevel set `{f ≥ f x}` carries the unit flux out of `a`
    set U := C.filter (fun z => f x ≤ f z) with hU
    have haU : a ∈ U := Finset.mem_filter.mpr ⟨ha, hfa⟩
    have hbU : b ∉ U := fun h => by
      have := (Finset.mem_filter.mp h).2
      linarith
    refine sub_le_one_of_flux (o := a) haU ?_ ?_ (Finset.mem_filter.mpr ⟨hx, le_rfl⟩)
      (fun h => by linarith [(Finset.mem_filter.mp h).2]) hxy
    · intro z hz
      have hzb : z ≠ b := fun h => hbU (h ▸ hz)
      rw [netLaplacian_unitCond, laplacian_dipole hG C ha hb hq (Finset.mem_filter.mp hz).1,
        if_neg hzb]
      ring
    · intro z hz w _ hwU
      have hz2 := (Finset.mem_filter.mp hz).2
      by_cases hwC : w ∈ C
      · have : ¬ f x ≤ f w := fun h => hwU (Finset.mem_filter.mpr ⟨hwC, h⟩)
        linarith [not_le.mp this]
      · rw [hf, dipole_vanishes hG C hq hwC]
        rw [hf] at hz2 hsign
        linarith
  · -- otherwise `f y < 0`, and the sublevel set `{f ≤ f y}` carries the unit flux out of `b`
    rw [not_le] at hsign
    set W := C.filter (fun z => f z ≤ f y) with hW
    have hbW : b ∈ W := Finset.mem_filter.mpr ⟨hb, hfb⟩
    have haW : a ∉ W := fun h => by
      have := (Finset.mem_filter.mp h).2
      linarith
    have key := sub_le_one_of_flux (f := fun v => -f v) (U := W) (o := b) hbW ?_ ?_
      (Finset.mem_filter.mpr ⟨hy, le_rfl⟩)
      (fun h => by linarith [(Finset.mem_filter.mp h).2]) hxy.symm
    · have key' : -f y - -f x ≤ 1 := key
      linarith
    · intro z hz
      have hza : z ≠ a := fun h => haW (h ▸ hz)
      rw [netLaplacian_unitCond, laplacian_neg, hf,
        laplacian_dipole hG C ha hb hq (Finset.mem_filter.mp hz).1, if_neg hza]
      ring
    · intro z hz w _ hwW
      have hz2 := (Finset.mem_filter.mp hz).2
      show -f w ≤ -f z
      by_cases hwC : w ∈ C
      · have : ¬ f w ≤ f y := fun h => hwW (Finset.mem_filter.mpr ⟨hwC, h⟩)
        linarith [not_le.mp this]
      · rw [hf, dipole_vanishes hG C hq hwC]
        rw [hf] at hz2
        linarith

/-- Along a walk inside `C` the dipole potential drops by at most the length. -/
theorem dipole_walk_le : ∀ {u v : V} (p : G.Walk u v), (∀ z ∈ p.support, z ∈ C) →
    dipole G C a b u - dipole G C a b v ≤ p.length
  | _, _, .nil, _ => by simp
  | _, _, .cons h p, hsupp => by
    have hu := hsupp _ (SimpleGraph.Walk.start_mem_support _)
    have hw : ∀ z ∈ p.support, z ∈ C := fun z hz =>
      hsupp z (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ hz)
    have h1 := dipole_edge_le hG C ha hb hq hu (hw _ (SimpleGraph.Walk.start_mem_support _)) h
    have h2 := dipole_walk_le p hw
    rw [SimpleGraph.Walk.length_cons]
    push_cast
    linarith

end

/-- **The voltage function on an infinite connected graph** (Lyons and Peres,
*Probability on Trees and Networks*, Cambridge University Press 2016,
Proposition 2.1 and equation (2.4)): for distinct vertices `a` and `b` there is a
bounded nonnegative `f` with `Δf = δ_b - δ_a`.  No transience is assumed; compare
`exists_voltage_of_green_ne_top`. -/
theorem exists_voltage_of_connected [Infinite V] (hG : G.Connected) {a b : V} (_hab : a ≠ b) :
    ∃ f : V → ℝ, ∃ M : ℝ, 0 < M ∧ (∀ x, 0 ≤ f x ∧ f x ≤ M) ∧
      ∀ x : V, laplacian G f x
        = (if x = b then (1 : ℝ) else 0) - (if x = a then 1 else 0) := by
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
  set K : Set (V → ℝ) := Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) n with hK
  have hKc : IsCompact K := isCompact_univ_pi fun _ => isCompact_Icc
  have hFK : Filter.map h atTop ≤ 𝓟 K := by
    rw [Filter.le_principal_iff, Filter.mem_map]
    refine Filter.mem_of_superset (Filter.Ici_mem_atTop P) fun C hC => ?_
    intro x _
    exact hbox C hC x
  obtain ⟨f, hfK, hclus⟩ := hKc hFK
  refine ⟨f, n + 1, by positivity, fun x => ?_, fun x => ?_⟩
  · have := hfK x (Set.mem_univ x)
    exact ⟨this.1, by linarith [this.2]⟩
  · set Z : Set (V → ℝ) := {g | laplacian G g x
        = (if x = b then (1 : ℝ) else 0) - (if x = a then 1 else 0)} with hZ
    have hZc : IsClosed Z := by
      refine isClosed_eq ?_ continuous_const
      show Continuous fun g : V → ℝ => ∑ y ∈ G.neighborFinset x, (g y - g x)
      exact continuous_finsetSum _ fun y _ => (continuous_apply y).sub (continuous_apply x)
    have hZF : Z ∈ Filter.map h atTop := by
      rw [Filter.mem_map]
      refine Filter.mem_of_superset (Filter.Ici_mem_atTop (insert x P)) fun C hC => ?_
      have hC' : insert x P ⊆ C := hC
      obtain ⟨q, hq⟩ := Infinite.exists_notMem_finset C
      show laplacian G (fun v => dipole G C a b v - dipole G C a b b) x = _
      rw [laplacian_sub_const]
      exact laplacian_dipole hG C (hC' (Finset.mem_insert_of_mem haP))
        (hC' (Finset.mem_insert_of_mem hbP)) hq (hC' (Finset.mem_insert_self x P))
    have hcl : f ∈ closure Z :=
      mem_closure_iff_clusterPt.mpr (hclus.mono (Filter.le_principal_iff.mpr hZF))
    rw [hZc.closure_eq] at hcl
    exact hcl

end LatticeProb.Network
