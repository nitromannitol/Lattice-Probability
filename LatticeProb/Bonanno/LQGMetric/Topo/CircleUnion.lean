/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Topo.CircleUnion at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.MetricSpace.Bounded

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
Deterministic plane topology behind

* **LM Lemma 4.3** (`lem-connected`, Gwynne–Miller, *Local metrics of the Gaussian free field*,
  arXiv:1905.00379, `local-metrics-final.tex` lines 858–875), and
* **DFGPS Lemma 3.5** (`lem-connected`, Dubédat–Falconet–Gwynne–Pfeffer–Sun, *Weak LQG metrics and Liouville first passage
  percolation*, arXiv:1905.00380, `lqg-metric-estimates-final.tex` lines 1573–1596).

Both papers give the same argument, which we follow step by step:

1. take a sub-collection `𝓑` of the discs which is minimal for covering a connected set `A`
   (`exists_minimal_ball_cover`); then `⋃ 𝓑` is connected (`isPreconnected_biUnion_ball`) and
   no disc of `𝓑` is contained in the union of the others;
2. if `𝓑 = 𝓑₁ ⊔ 𝓑₂` with `𝓑₁` nonempty and the circle unions of `𝓑₁`, `𝓑₂` disjoint, then
   `𝓑₂` is empty (`subset_of_disjoint_spheres`): a disc of `𝓑₂` is not contained in `⋃ 𝓑₁`,
   and cannot meet both `⋃ 𝓑₁` and its complement without its circle meeting a circle of `𝓑₁`;
   so `⋃ 𝓑₁` and `⋃ 𝓑₂` are disjoint open sets, contradicting connectedness of `⋃ 𝓑`;
3. hence `⋃_{B ∈ 𝓑} ∂B` is connected, and (being a finite union of circles) path-connected
   (`isPathConnected_biUnion_sphere`).

The step "such a disc would have to intersect the boundary of some disc of `𝓑₁`, hence its
circle meets that circle" is made precise in `sphere_inter_sphere_nonempty`: a circle meeting
an open disc but not its boundary circle lies inside the disc, and then (by convexity,
`convexHull_sphere_eq_closedBall`) so does its whole disc, contradicting minimality.
The paper's last step (connected ⇒ contains a path) is done directly with path components:
in step 2 we take `𝓑₁` = the circles inside the path component of a fixed point.
The final statements (endpoints near `z₁, z₂` for LM, on `K₁, K₂` for DFGPS) are in
`exists_joinedIn_biUnion_sphere_of_cover` and `exists_joinedIn_biUnion_sphere_of_path`.
-/

namespace LQGMetric

open Set Metric

namespace TopoCircle

variable {ι : Type*}

/-- A circle contained in an open disc has its whole closed disc in it (convexity). -/
theorem closedBall_subset_ball_of_sphere_subset {a b : ℂ} {r s : ℝ} (hr : 0 ≤ r)
    (h : sphere a r ⊆ ball b s) : closedBall a r ⊆ ball b s := by
  rw [← convexHull_sphere_eq_closedBall a hr]
  exact convexHull_min h (convex_ball b s)

theorem isPreconnected_sphere_complex (a : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    IsPreconnected (sphere a r) :=
  (isConnected_sphere (by simp [Complex.rank_real_complex]) a hr).isPreconnected

theorem isPathConnected_sphere_complex (a : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    IsPathConnected (sphere a r) :=
  isPathConnected_sphere (by simp [Complex.rank_real_complex]) a hr

/-- If the circle `∂B_r(a)` meets the open disc `B_s(b)` and `B_r(a) ⊄ B_s(b)`, then the two
circles meet. -/
theorem sphere_inter_sphere_nonempty {a b x : ℂ} {r s : ℝ} (hr : 0 ≤ r)
    (hnot : ¬ ball a r ⊆ ball b s) (hx : x ∈ sphere a r) (hxb : x ∈ ball b s) :
    (sphere a r ∩ sphere b s).Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have hsub : sphere a r ⊆ ball b s ∪ (closedBall b s)ᶜ := by
    intro y hy
    by_cases h1 : y ∈ ball b s
    · exact Or.inl h1
    · right
      intro h2
      have : y ∈ sphere b s := by
        rw [mem_sphere]; rw [mem_ball, not_lt] at h1; rw [mem_closedBall] at h2
        exact le_antisymm h2 h1
      exact (eq_empty_iff_forall_notMem.1 hne) y ⟨hy, this⟩
  rcases (isPreconnected_sphere_complex a hr).subset_or_subset isOpen_ball
      isClosed_closedBall.isOpen_compl
      (disjoint_compl_right.mono_left ball_subset_closedBall) hsub with h | h
  · exact hnot (ball_subset_closedBall.trans (closedBall_subset_ball_of_sphere_subset hr h))
  · exact h hx (ball_subset_closedBall hxb)

variable (c : ι → ℂ) (r : ι → ℝ)

/-- Step 2 of the papers' argument: for a minimal family of discs with connected union, a
nonempty sub-family whose circles are disjoint from the circles of the rest is everything. -/
theorem subset_of_disjoint_spheres [DecidableEq ι] (S I : Finset ι) (hI : I ⊆ S)
    (hIne : I.Nonempty) (hr : ∀ i ∈ S, 0 < r i)
    (hconn : IsPreconnected (⋃ i ∈ S, ball (c i) (r i)))
    (hmin : ∀ j ∈ S, ¬ ball (c j) (r j) ⊆ ⋃ i ∈ S.erase j, ball (c i) (r i))
    (hdisj : ∀ i ∈ I, ∀ j ∈ S, j ∉ I →
      Disjoint (sphere (c i) (r i)) (sphere (c j) (r j))) :
    S ⊆ I := by
  by_contra hSI
  obtain ⟨j0, hj0S, hj0I⟩ := Finset.not_subset.1 hSI
  set U1 : Set ℂ := ⋃ i ∈ I, ball (c i) (r i) with hU1
  set V : Set ℂ := (⋃ i ∈ I, closedBall (c i) (r i))ᶜ with hV
  have hU1o : IsOpen U1 := isOpen_biUnion fun _ _ => isOpen_ball
  have hVo : IsOpen V := (isClosed_biUnion_finset fun _ _ => isClosed_closedBall).isOpen_compl
  have hUV : Disjoint U1 V := by
    rw [hV]; refine disjoint_compl_right.mono_left ?_
    exact biUnion_mono subset_rfl fun _ _ => ball_subset_closedBall
  -- every disc of the complementary family lies in `V`
  have hball : ∀ j ∈ S, j ∉ I → ball (c j) (r j) ⊆ V := by
    intro j hjS hjI
    have hsub : ball (c j) (r j) ⊆ U1 ∪ V := by
      intro y hy
      by_cases hyV : y ∈ V
      · exact Or.inr hyV
      · left
        rw [hV, notMem_compl_iff, mem_iUnion₂] at hyV
        obtain ⟨i, hiI, hyi⟩ := hyV
        by_cases hyb : y ∈ ball (c i) (r i)
        · exact mem_biUnion hiI hyb
        · exfalso
          have hys : y ∈ sphere (c i) (r i) := by
            rw [mem_sphere]; rw [mem_ball, not_lt] at hyb; rw [mem_closedBall] at hyi
            exact le_antisymm hyi hyb
          have hij : i ≠ j := fun h => hjI (h ▸ hiI)
          have hnot : ¬ ball (c i) (r i) ⊆ ball (c j) (r j) := by
            intro h
            refine hmin i (hI hiI) (h.trans ?_)
            exact subset_biUnion_of_mem (u := fun k => ball (c k) (r k))
              (Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hij.symm, hjS⟩))
          obtain ⟨z, hz⟩ := sphere_inter_sphere_nonempty (hr i (hI hiI)).le hnot hys hy
          exact Set.disjoint_left.1 (hdisj i hiI j hjS hjI) hz.1 hz.2
    rcases (isPreconnected_ball (x := c j) (r := r j)).subset_or_subset hU1o hVo hUV hsub
      with h | h
    · exfalso
      refine hmin j hjS (h.trans ?_)
      refine biUnion_mono ?_ fun _ _ => subset_rfl
      intro k hk
      exact Finset.mem_coe.2 (Finset.mem_erase.2
        ⟨fun h => hjI (h ▸ Finset.mem_coe.1 hk), hI (Finset.mem_coe.1 hk)⟩)
    · exact h
  have hW : (⋃ i ∈ S, ball (c i) (r i)) ⊆ U1 ∪ V := by
    intro y hy
    rw [mem_iUnion₂] at hy
    obtain ⟨i, hiS, hyi⟩ := hy
    by_cases hiI : i ∈ I
    · exact Or.inl (mem_biUnion hiI hyi)
    · exact Or.inr (hball i hiS hiI hyi)
  rcases hconn.subset_or_subset hU1o hVo hUV hW with h | h
  · have hc : c j0 ∈ ball (c j0) (r j0) := mem_ball_self (hr j0 hj0S)
    exact Set.disjoint_left.1 hUV (h (mem_biUnion hj0S hc)) (hball j0 hj0S hj0I hc)
  · obtain ⟨i0, hi0⟩ := hIne
    have hc : c i0 ∈ ball (c i0) (r i0) := mem_ball_self (hr i0 (hI hi0))
    exact Set.disjoint_left.1 hUV (mem_biUnion hi0 hc) (h (mem_biUnion (hI hi0) hc))

/-- Step 3: the union of the circles of a minimal family of discs with connected union is
path-connected. -/
theorem isPathConnected_biUnion_sphere [DecidableEq ι] (S : Finset ι) (hS : S.Nonempty)
    (hr : ∀ i ∈ S, 0 < r i)
    (hconn : IsPreconnected (⋃ i ∈ S, ball (c i) (r i)))
    (hmin : ∀ j ∈ S, ¬ ball (c j) (r j) ⊆ ⋃ i ∈ S.erase j, ball (c i) (r i)) :
    IsPathConnected (⋃ i ∈ S, sphere (c i) (r i)) := by
  classical
  set T : Set ℂ := ⋃ i ∈ S, sphere (c i) (r i) with hT
  obtain ⟨i0, hi0⟩ := hS
  obtain ⟨x0, hx0⟩ := (NormedSpace.sphere_nonempty (x := c i0)).2 (hr i0 hi0).le
  have hsT : ∀ i ∈ S, sphere (c i) (r i) ⊆ T := fun i hi =>
    subset_biUnion_of_mem (u := fun k => sphere (c k) (r k)) (Finset.mem_coe.2 hi)
  have hx0T : x0 ∈ T := hsT i0 hi0 hx0
  let I : Finset ι := S.filter fun i => sphere (c i) (r i) ⊆ pathComponentIn T x0
  have hI : I ⊆ S := Finset.filter_subset _ _
  have hi0I : i0 ∈ I := Finset.mem_filter.2 ⟨hi0,
    (isPathConnected_sphere_complex _ (hr i0 hi0).le).subset_pathComponentIn hx0 (hsT i0 hi0)⟩
  have hdisj : ∀ i ∈ I, ∀ j ∈ S, j ∉ I →
      Disjoint (sphere (c i) (r i)) (sphere (c j) (r j)) := by
    intro i hiI j hjS hjI
    rw [Set.disjoint_left]
    intro z hzi hzj
    apply hjI
    refine Finset.mem_filter.2 ⟨hjS, ?_⟩
    have hz : z ∈ pathComponentIn T x0 := (Finset.mem_filter.1 hiI).2 hzi
    rw [← pathComponentIn_congr hz]
    exact (isPathConnected_sphere_complex _ (hr j hjS).le).subset_pathComponentIn hzj
      (hsT j hjS)
  have hSI := subset_of_disjoint_spheres c r S I hI ⟨i0, hi0I⟩ hr hconn hmin hdisj
  refine isPathConnected_iff_eq.2 ⟨x0, hx0T, subset_antisymm pathComponentIn_subset ?_⟩
  intro y hy
  rw [hT, mem_iUnion₂] at hy
  obtain ⟨i, hiS, hyi⟩ := hy
  exact (Finset.mem_filter.1 (hSI hiS)).2 hyi

/-- Step 1a: a finite cover of `A` by discs has a sub-cover minimal for inclusion; each disc of
it meets `A` and none is contained in the union of the others. -/
theorem exists_minimal_ball_cover [DecidableEq ι] (S0 : Finset ι) (A : Set ℂ)
    (hA : A ⊆ ⋃ i ∈ S0, ball (c i) (r i)) :
    ∃ S ⊆ S0, A ⊆ (⋃ i ∈ S, ball (c i) (r i)) ∧
      (∀ j ∈ S, (ball (c j) (r j) ∩ A).Nonempty) ∧
      ∀ j ∈ S, ¬ ball (c j) (r j) ⊆ ⋃ i ∈ S.erase j, ball (c i) (r i) := by
  classical
  set C : Finset (Finset ι) :=
    S0.powerset.filter fun S => A ⊆ ⋃ i ∈ S, ball (c i) (r i) with hC
  have hCne : C.Nonempty := ⟨S0, Finset.mem_filter.2 ⟨Finset.mem_powerset_self _, hA⟩⟩
  obtain ⟨S, hSC, hSmin⟩ := C.exists_min_image Finset.card hCne
  obtain ⟨hSP, hSA⟩ := Finset.mem_filter.1 hSC
  have herase : ∀ j ∈ S, ¬ A ⊆ ⋃ i ∈ S.erase j, ball (c i) (r i) := by
    intro j hj h
    have hmem : S.erase j ∈ C := Finset.mem_filter.2
      ⟨Finset.mem_powerset.2 ((Finset.erase_subset j S).trans (Finset.mem_powerset.1 hSP)), h⟩
    have := hSmin _ hmem
    have hlt := Finset.card_erase_lt_of_mem hj
    omega
  refine ⟨S, Finset.mem_powerset.1 hSP, hSA, ?_, ?_⟩
  · intro j hj
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    refine herase j hj fun a ha => ?_
    obtain ⟨i, hiS, hai⟩ := mem_iUnion₂.1 (hSA ha)
    by_cases hij : i = j
    · subst hij; exact absurd (show a ∈ ball (c i) (r i) ∩ A from ⟨hai, ha⟩) (hne ▸ id)
    · exact mem_biUnion (Finset.mem_erase.2 ⟨hij, hiS⟩) hai
  · intro j hj hsub
    refine herase j hj fun a ha => ?_
    obtain ⟨i, hiS, hai⟩ := mem_iUnion₂.1 (hSA ha)
    by_cases hij : i = j
    · subst hij; exact hsub hai
    · exact mem_biUnion (Finset.mem_erase.2 ⟨hij, hiS⟩) hai

/-- Step 1b: discs covering a preconnected set `A` and each meeting `A` have preconnected
union ("if this set had two proper disjoint open subsets, then each would have to intersect
`A`"). -/
theorem isPreconnected_biUnion_ball (S : Finset ι) (A : Set ℂ) (hA : IsPreconnected A)
    (hcov : A ⊆ ⋃ i ∈ S, ball (c i) (r i)) (hmeet : ∀ j ∈ S, (ball (c j) (r j) ∩ A).Nonempty) :
    IsPreconnected (⋃ i ∈ S, ball (c i) (r i)) := by
  refine isPreconnected_of_forall_pair fun x hx y hy => ?_
  obtain ⟨i, hiS, hxi⟩ := mem_iUnion₂.1 hx
  obtain ⟨j, hjS, hyj⟩ := mem_iUnion₂.1 hy
  have h1 : IsPreconnected (ball (c i) (r i) ∪ A) :=
    IsPreconnected.union' (hmeet i hiS) isPreconnected_ball hA
  have h2 : IsPreconnected ((ball (c i) (r i) ∪ A) ∪ ball (c j) (r j)) := by
    refine IsPreconnected.union' ?_ h1 isPreconnected_ball
    obtain ⟨z, hz1, hz2⟩ := hmeet j hjS
    exact ⟨z, Or.inr hz2, hz1⟩
  refine ⟨_, ?_, Or.inl (Or.inl hxi), Or.inr hyj, h2⟩
  refine union_subset (union_subset ?_ hcov) ?_
  · exact subset_biUnion_of_mem (u := fun k => ball (c k) (r k)) (Finset.mem_coe.2 hiS)
  · exact subset_biUnion_of_mem (u := fun k => ball (c k) (r k)) (Finset.mem_coe.2 hjS)

/-- A preconnected set meeting the open disc `B_r(a)` and of diameter `> 2r` meets its
circle (DFGPS lines 1594–1595). -/
theorem inter_sphere_nonempty_of_diam {K : Set ℂ} (hK : IsPreconnected K) {a p : ℂ} {r : ℝ}
    (hpK : p ∈ K) (hpb : p ∈ ball a r) (hd : 2 * r < diam K) :
    (K ∩ sphere a r).Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have hsub : K ⊆ ball a r ∪ (closedBall a r)ᶜ := by
    intro y hy
    by_cases h1 : y ∈ ball a r
    · exact Or.inl h1
    · right
      intro h2
      have : y ∈ sphere a r := by
        rw [mem_sphere]; rw [mem_ball, not_lt] at h1; rw [mem_closedBall] at h2
        exact le_antisymm h2 h1
      exact (eq_empty_iff_forall_notMem.1 hne) y ⟨hy, this⟩
  rcases hK.subset_or_subset isOpen_ball isClosed_closedBall.isOpen_compl
      (disjoint_compl_right.mono_left ball_subset_closedBall) hsub with h | h
  · have hr : 0 ≤ r := (dist_nonneg.trans_lt (mem_ball.1 hpb)).le
    have := (diam_mono h isBounded_ball).trans (diam_ball (x := a) hr)
    linarith
  · exact h hpK (ball_subset_closedBall hpb)

/-- **DFGPS Lemma 3.5, deterministic core** (arXiv:1905.00380, tex lines 1573–1596). If a path
`γ` from a preconnected set `K₁` to a preconnected set `K₂` is covered by finitely many discs
whose diameters `2r` are smaller than `diam K₁` and `diam K₂`, then for a sub-collection still
covering `γ`, the union of its circles contains a path from a point of `K₁` to a point of
`K₂`. (Every such circle lies in the union of the closed discs, which gives the paper's
"contained in `𝕣U`" when those lie in `𝕣U`.) -/
theorem exists_joinedIn_biUnion_sphere_of_path [DecidableEq ι] (S0 : Finset ι)
    (hr : ∀ i ∈ S0, 0 < r i) {K₁ K₂ : Set ℂ} (hK₁ : IsPreconnected K₁)
    (hK₂ : IsPreconnected K₂) (hd₁ : ∀ i ∈ S0, 2 * r i < diam K₁)
    (hd₂ : ∀ i ∈ S0, 2 * r i < diam K₂) {p q : ℂ} (γ : Path p q) (hp : p ∈ K₁) (hq : q ∈ K₂)
    (hcov : range γ ⊆ ⋃ i ∈ S0, ball (c i) (r i)) :
    ∃ S ⊆ S0, range γ ⊆ (⋃ i ∈ S, ball (c i) (r i)) ∧
      ∃ x ∈ K₁, ∃ y ∈ K₂, JoinedIn (⋃ i ∈ S, sphere (c i) (r i)) x y := by
  have hA : IsPreconnected (range γ) := (isConnected_range γ.continuous).isPreconnected
  obtain ⟨S, hS0, hSA, hmeet, hmin⟩ := exists_minimal_ball_cover c r S0 (range γ) hcov
  have hrS : ∀ i ∈ S, 0 < r i := fun i hi => hr i (hS0 hi)
  have hpr : p ∈ range γ := ⟨0, γ.source⟩
  have hqr : q ∈ range γ := ⟨1, γ.target⟩
  obtain ⟨i, hiS, hpi⟩ := mem_iUnion₂.1 (hSA hpr)
  obtain ⟨j, hjS, hqj⟩ := mem_iUnion₂.1 (hSA hqr)
  have hpc := isPathConnected_biUnion_sphere c r S ⟨i, hiS⟩ hrS
    (isPreconnected_biUnion_ball c r S _ hA hSA hmeet) hmin
  obtain ⟨x, hxK, hx⟩ := inter_sphere_nonempty_of_diam hK₁ hp hpi (hd₁ i (hS0 hiS))
  obtain ⟨y, hyK, hy⟩ := inter_sphere_nonempty_of_diam hK₂ hq hqj (hd₂ j (hS0 hjS))
  exact ⟨S, hS0, hSA, x, hxK, y, hyK,
    hpc.joinedIn x (mem_biUnion hiS hx) y (mem_biUnion hjS hy)⟩

end TopoCircle

end LQGMetric
