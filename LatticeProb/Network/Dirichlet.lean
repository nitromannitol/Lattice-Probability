module

/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: BouRabeeGwynne/FiniteDirichlet.lean.
-/
public import LatticeProb.Network.HarmonicAlgebra
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

/-!
# The Dirichlet problem on a locally finite network

Let `G` be a locally finite graph with conductance `c` (`IsCond G c`), and let `A` be a finite
set of vertices. The Dirichlet problem asks for a function `f` that is `c`-harmonic at every
vertex of `A` and agrees with prescribed boundary data `g` off `A`.

* `BoundaryAccessible G A`: from every vertex of `A` some vertex outside `A` is reachable.
  This is the only condition on `A`. The graph need not be connected, and the vertex type need
  not be finite.
* `subharmonic_maximum_principle` and `superharmonic_minimum_principle`: a subharmonic
  (resp. superharmonic) function on `A` is bounded by its values off `A`.
* `homogeneous_solution_eq_zero`, `dirichlet_unique`, `existsUnique_dirichlet`: the Dirichlet
  problem has exactly one solution, and `dirichletSolution` selects it.
* `dirichlet_stability` and `dirichletSolution_stability`: a uniform perturbation of the boundary
  data moves the solution by at most the same amount at every vertex.
* `boundaryAccessible_of_strict_subharmonic`: a strictly subharmonic function on `A` forces `A`
  to be accessible.

The existence proof works on the finite-dimensional space of values on `A`, so finiteness of
the vertex type is never used. The bridges at the end cover the connected case
(`boundaryAccessible_of_connected`) and networks given by a symmetric, nonnegative matrix with
zero diagonal (`positiveGraph`).
-/

namespace LatticeProb.Network

variable {V : Type*}

/-! ### Boundary accessibility and the Dirichlet problem -/

/-- Every vertex of `A` reaches, in `G`, some vertex outside `A`. -/
def BoundaryAccessible (G : SimpleGraph V) (A : Finset V) : Prop :=
  ∀ v ∈ A, ∃ w, w ∉ A ∧ G.Reachable v w

/-- On a connected graph, every finite set with a vertex outside it is accessible. -/
theorem boundaryAccessible_of_connected {G : SimpleGraph V} (hG : G.Connected) (A : Finset V)
    (hout : ∃ w, w ∉ A) : BoundaryAccessible G A := by
  obtain ⟨w, hw⟩ := hout
  exact fun v _ => ⟨w, hw, hG.preconnected v w⟩

/-- The Dirichlet problem on `A` with boundary data `g`: `f` is `c`-harmonic at every vertex
of `A` and equals `g` at every vertex outside `A`. -/
def SolvesDirichlet (G : SimpleGraph V) [G.LocallyFinite] (c : V → V → ℝ) (A : Finset V)
    (g f : V → ℝ) : Prop :=
  (∀ v ∈ A, netLaplacian G c f v = 0) ∧ ∀ v, v ∉ A → f v = g v

section Laplacian

variable {G : SimpleGraph V} [G.LocallyFinite]

theorem netLaplacian_neg (c : V → V → ℝ) (f : V → ℝ) (x : V) :
    netLaplacian G c (fun v => -f v) x = -netLaplacian G c f x := by
  simpa using netLaplacian_smul c (-1) f x

theorem netLaplacian_sub (c : V → V → ℝ) (f g : V → ℝ) (x : V) :
    netLaplacian G c (fun v => f v - g v) x = netLaplacian G c f x - netLaplacian G c g x := by
  simp only [netLaplacian]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- A function that is largest at `x` among all vertices has nonpositive Laplacian at `x`. -/
theorem netLaplacian_nonpos_of_max {c : V → V → ℝ} (hc : IsCond G c) (f : V → ℝ) (x : V)
    (hmax : ∀ z, f z ≤ f x) : netLaplacian G c f x ≤ 0 := by
  simp only [netLaplacian]
  exact Finset.sum_nonpos fun y _ =>
    mul_nonpos_of_nonneg_of_nonpos (hc.nonneg x y) (sub_nonpos.mpr (hmax y))

/-! ### Maximum and minimum principles -/

/-- **Maximum principle.** A function that is subharmonic on the finite set `A` and bounded by
`M` off `A` is bounded by `M` everywhere. -/
theorem subharmonic_maximum_principle {c : V → V → ℝ} (hc : IsCond G c) (A : Finset V)
    (haccess : BoundaryAccessible G A) (f : V → ℝ) (M : ℝ)
    (hsub : ∀ v ∈ A, 0 ≤ netLaplacian G c f v) (hboundary : ∀ v, v ∉ A → f v ≤ M) :
    ∀ v, f v ≤ M := by
  classical
  intro x
  by_contra hx
  have hxM : M < f x := not_le.mp hx
  have hxA : x ∈ A := by
    by_contra h
    exact absurd (hboundary x h) (not_le.mpr hxM)
  -- the set where `f` exceeds `M` lies in `A`, so it is finite and has a largest element
  obtain ⟨m, hmK, hmax⟩ :=
    Finset.exists_max_image (A.filter fun z => M < f z) f
      ⟨x, Finset.mem_filter.mpr ⟨hxA, hxM⟩⟩
  obtain ⟨hmA, hMm⟩ := Finset.mem_filter.mp hmK
  have hglobal : ∀ z, f z ≤ f m := by
    intro z
    by_cases hz : z ∈ A ∧ M < f z
    · exact hmax z (Finset.mem_filter.mpr hz)
    · have hzM : f z ≤ M := by
        by_cases hzA : z ∈ A
        · exact not_lt.mp fun h => hz ⟨hzA, h⟩
        · exact hboundary z hzA
      exact hzM.trans hMm.le
  -- the maximum propagates along every walk from `m`
  have hwalk : ∀ {u w : V} (p : G.Walk u w), f u = f m → f w = f m := by
    intro u w p
    induction p with
    | nil => exact id
    | @cons a b _ hab p ih =>
      intro h
      have haA : a ∈ A := by
        by_contra haA
        have h1 := hboundary a haA
        rw [h] at h1
        exact absurd h1 (not_le.mpr hMm)
      have hle : ∀ z, f z ≤ f a := fun z => (hglobal z).trans h.ge
      have hzero : netLaplacian G c f a = 0 :=
        le_antisymm (netLaplacian_nonpos_of_max hc f a hle) (hsub a haA)
      exact ih ((maximum_neighbors hc a hzero (fun y _ => hle y) b hab).trans h)
  obtain ⟨w, hwA, hreach⟩ := haccess m hmA
  obtain ⟨p⟩ := hreach
  have h1 := hboundary w hwA
  rw [hwalk p rfl] at h1
  exact absurd h1 (not_le.mpr hMm)

/-- **Minimum principle.** A function that is superharmonic on the finite set `A` and bounded
below by `m` off `A` is bounded below by `m` everywhere. -/
theorem superharmonic_minimum_principle {c : V → V → ℝ} (hc : IsCond G c) (A : Finset V)
    (haccess : BoundaryAccessible G A) (f : V → ℝ) (m : ℝ)
    (hsuper : ∀ v ∈ A, netLaplacian G c f v ≤ 0) (hboundary : ∀ v, v ∉ A → m ≤ f v) :
    ∀ v, m ≤ f v := by
  intro v
  have h := subharmonic_maximum_principle hc A haccess (fun z => -f z) (-m)
    (fun z hz => by
      rw [netLaplacian_neg]
      exact neg_nonneg.mpr (hsuper z hz))
    (fun z hz => neg_le_neg (hboundary z hz))
  have h' : -f v ≤ -m := h v
  linarith

/-- A harmonic function on `A` that vanishes off `A` vanishes everywhere. -/
theorem homogeneous_solution_eq_zero {c : V → V → ℝ} (hc : IsCond G c) (A : Finset V)
    (haccess : BoundaryAccessible G A) (f : V → ℝ) (hL : ∀ v ∈ A, netLaplacian G c f v = 0)
    (hboundary : ∀ v, v ∉ A → f v = 0) : f = 0 := by
  funext v
  have hu := subharmonic_maximum_principle hc A haccess f 0 (fun z hz => (hL z hz).ge)
    (fun z hz => (hboundary z hz).le)
  have hl := superharmonic_minimum_principle hc A haccess f 0 (fun z hz => (hL z hz).le)
    (fun z hz => (hboundary z hz).ge)
  exact le_antisymm (hu v) (hl v)

/-! ### Uniqueness, existence and the chosen solution -/

/-- Two solutions of the Dirichlet problem with the same boundary data agree. -/
theorem dirichlet_unique {c : V → V → ℝ} (hc : IsCond G c) (A : Finset V)
    (haccess : BoundaryAccessible G A) {g f₁ f₂ : V → ℝ}
    (h₁ : SolvesDirichlet G c A g f₁) (h₂ : SolvesDirichlet G c A g f₂) : f₁ = f₂ := by
  have h0 := homogeneous_solution_eq_zero hc A haccess (fun v => f₁ v - f₂ v)
    (fun v hv => by rw [netLaplacian_sub, h₁.1 v hv, h₂.1 v hv, sub_self])
    (fun v hv => by rw [h₁.2 v hv, h₂.2 v hv, sub_self])
  funext v
  have h1 : f₁ v - f₂ v = 0 := congrFun h0 v
  exact sub_eq_zero.mp h1

open scoped Classical in
/-- Extension by zero from the finite set `A` to the whole vertex type. -/
noncomputable def extendByZero (A : Finset V) : (A → ℝ) →ₗ[ℝ] (V → ℝ) where
  toFun u z := if h : z ∈ A then u ⟨z, h⟩ else 0
  map_add' u u' := by
    funext z
    by_cases h : z ∈ A <;> simp [h]
  map_smul' a u := by
    funext z
    by_cases h : z ∈ A <;> simp [h]

theorem extendByZero_apply_of_mem {A : Finset V} (u : A → ℝ) {z : V} (h : z ∈ A) :
    extendByZero A u z = u ⟨z, h⟩ := by
  simp [extendByZero, h]

theorem extendByZero_apply_of_not_mem {A : Finset V} (u : A → ℝ) {z : V} (h : z ∉ A) :
    extendByZero A u z = 0 := by
  simp [extendByZero, h]

open scoped Classical in
/-- The network Laplacian at the vertices of `A`, as a linear map of the values on `A`, when
the values off `A` are taken to be zero. -/
noncomputable def interiorLaplacian (G : SimpleGraph V) [G.LocallyFinite] (c : V → V → ℝ)
    (A : Finset V) : (A → ℝ) →ₗ[ℝ] (A → ℝ) where
  toFun u v := netLaplacian G c (extendByZero A u) v
  map_add' u u' := by
    funext v
    change netLaplacian G c (extendByZero A (u + u')) v =
      netLaplacian G c (extendByZero A u) v + netLaplacian G c (extendByZero A u') v
    rw [map_add, netLaplacian_add]
  map_smul' a u := by
    funext v
    change netLaplacian G c (extendByZero A (a • u)) v = a * netLaplacian G c (extendByZero A u) v
    rw [map_smul]
    exact netLaplacian_smul c a _ v

theorem interiorLaplacian_injective {G : SimpleGraph V} [G.LocallyFinite] {c : V → V → ℝ}
    (hc : IsCond G c) (A : Finset V) (haccess : BoundaryAccessible G A) :
    Function.Injective (interiorLaplacian G c A) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  have hzero : extendByZero A u = 0 :=
    homogeneous_solution_eq_zero hc A haccess (extendByZero A u)
      (fun v hv => congrFun hu ⟨v, hv⟩)
      (fun v hv => extendByZero_apply_of_not_mem u hv)
  funext x
  obtain ⟨v, hv⟩ := x
  have h1 := congrFun hzero v
  rw [extendByZero_apply_of_mem u hv] at h1
  exact h1

theorem interiorLaplacian_surjective {G : SimpleGraph V} [G.LocallyFinite] {c : V → V → ℝ}
    (hc : IsCond G c) (A : Finset V) (haccess : BoundaryAccessible G A) :
    Function.Surjective (interiorLaplacian G c A) :=
  LinearMap.injective_iff_surjective.mp (interiorLaplacian_injective hc A haccess)

/-- The Dirichlet problem has exactly one solution for every boundary data. -/
theorem existsUnique_dirichlet {G : SimpleGraph V} [G.LocallyFinite] {c : V → V → ℝ}
    (hc : IsCond G c) (A : Finset V) (haccess : BoundaryAccessible G A) (g : V → ℝ) :
    ∃! f : V → ℝ, SolvesDirichlet G c A g f := by
  classical
  -- the boundary data, with the values on `A` set to zero
  let e : V → ℝ := fun z => if z ∈ A then 0 else g z
  obtain ⟨u, hu⟩ := interiorLaplacian_surjective hc A haccess (fun v => -netLaplacian G c e v)
  have hsol : SolvesDirichlet G c A g (extendByZero A u + e) := by
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · have h1 : netLaplacian G c (extendByZero A u) v = -netLaplacian G c e v :=
        congrFun hu ⟨v, hv⟩
      rw [netLaplacian_add, h1, neg_add_cancel]
    · simp [extendByZero_apply_of_not_mem u hv, e, hv]
  exact ⟨extendByZero A u + e, hsol, fun f hf => dirichlet_unique hc A haccess hf hsol⟩

/-- The solution of the Dirichlet problem, chosen from `existsUnique_dirichlet`. -/
noncomputable def dirichletSolution {G : SimpleGraph V} [G.LocallyFinite] {c : V → V → ℝ}
    (hc : IsCond G c) (A : Finset V) (haccess : BoundaryAccessible G A) (g : V → ℝ) :
    V → ℝ :=
  Classical.choose (existsUnique_dirichlet hc A haccess g).exists

theorem dirichletSolution_spec {G : SimpleGraph V} [G.LocallyFinite] {c : V → V → ℝ}
    (hc : IsCond G c) (A : Finset V) (haccess : BoundaryAccessible G A) (g : V → ℝ) :
    SolvesDirichlet G c A g (dirichletSolution hc A haccess g) :=
  Classical.choose_spec (existsUnique_dirichlet hc A haccess g).exists

/-! ### Stability -/

/-- Uniform perturbations of the boundary data cause no larger perturbation of the solutions,
at any vertex. -/
theorem dirichlet_stability {c : V → V → ℝ} (hc : IsCond G c) (A : Finset V)
    (haccess : BoundaryAccessible G A) {g₁ g₂ f₁ f₂ : V → ℝ}
    (h₁ : SolvesDirichlet G c A g₁ f₁) (h₂ : SolvesDirichlet G c A g₂ f₂) {η : ℝ}
    (hboundary : ∀ v, v ∉ A → |g₁ v - g₂ v| ≤ η) :
    ∀ v, |f₁ v - f₂ v| ≤ η := by
  have hu := subharmonic_maximum_principle hc A haccess (fun v => f₁ v - f₂ v) η
    (fun v hv => le_of_eq (by rw [netLaplacian_sub, h₁.1 v hv, h₂.1 v hv, sub_self]))
    (fun v hv => by
      show f₁ v - f₂ v ≤ η
      rw [h₁.2 v hv, h₂.2 v hv]
      exact (abs_le.mp (hboundary v hv)).2)
  have hl := subharmonic_maximum_principle hc A haccess (fun v => f₂ v - f₁ v) η
    (fun v hv => le_of_eq (by rw [netLaplacian_sub, h₁.1 v hv, h₂.1 v hv, sub_self]))
    (fun v hv => by
      show f₂ v - f₁ v ≤ η
      rw [h₂.2 v hv, h₁.2 v hv]
      linarith [(abs_le.mp (hboundary v hv)).1])
  intro v
  have hu' : f₁ v - f₂ v ≤ η := hu v
  have hl' : f₂ v - f₁ v ≤ η := hl v
  rw [abs_le]
  constructor <;> linarith

/-- The chosen solutions for two boundary data differ by at most their uniform difference. -/
theorem dirichletSolution_stability {c : V → V → ℝ} (hc : IsCond G c) (A : Finset V)
    (haccess : BoundaryAccessible G A) (g₁ g₂ : V → ℝ) {η : ℝ}
    (hboundary : ∀ v, v ∉ A → |g₁ v - g₂ v| ≤ η) :
    ∀ v, |dirichletSolution hc A haccess g₁ v - dirichletSolution hc A haccess g₂ v| ≤ η :=
  dirichlet_stability hc A haccess (dirichletSolution_spec hc A haccess g₁)
    (dirichletSolution_spec hc A haccess g₂) hboundary

/-! ### Accessibility from strict subharmonicity -/

/-- A strictly subharmonic function on a finite set `A` forces `A` to be accessible: otherwise
the vertices reachable from a point of `A` all lie in `A`, so the largest of them is an interior
maximum with nonpositive Laplacian. -/
theorem boundaryAccessible_of_strict_subharmonic {c : V → V → ℝ} (hc : IsCond G c)
    (A : Finset V) (f : V → ℝ) (hstrict : ∀ v ∈ A, 0 < netLaplacian G c f v) :
    BoundaryAccessible G A := by
  classical
  intro v hvA
  by_contra hno
  have hinside : ∀ w, G.Reachable v w → w ∈ A := fun w hw => by
    by_contra hwA
    exact hno ⟨w, hwA, hw⟩
  have hvR : v ∈ A.filter fun w => G.Reachable v w :=
    Finset.mem_filter.mpr ⟨hvA, SimpleGraph.Reachable.refl v⟩
  obtain ⟨m, hmR, hmax⟩ := Finset.exists_max_image (A.filter fun w => G.Reachable v w) f
    ⟨v, hvR⟩
  obtain ⟨hmA, hmreach⟩ := Finset.mem_filter.mp hmR
  have hnb : ∀ w, G.Adj m w → f w ≤ f m := fun w hmw =>
    hmax w (Finset.mem_filter.mpr ⟨hinside w (hmreach.trans hmw.reachable),
      hmreach.trans hmw.reachable⟩)
  have hnonpos : netLaplacian G c f m ≤ 0 := by
    simp only [netLaplacian]
    exact Finset.sum_nonpos fun w hw =>
      mul_nonpos_of_nonneg_of_nonpos (hc.nonneg m w)
        (sub_nonpos.mpr (hnb w ((SimpleGraph.mem_neighborFinset G m w).mp hw)))
  exact (not_lt.mpr hnonpos) (hstrict m hmA)

end Laplacian

/-! ### Networks given by a weight matrix -/

/-- The graph whose edges are the ordered pairs of positive weight `a`. -/
def positiveGraph (a : V → V → ℝ) : SimpleGraph V :=
  SimpleGraph.fromRel fun v w => 0 < a v w

theorem positiveGraph_adj_iff {a : V → V → ℝ} (hsymm : ∀ v w, a v w = a w v)
    (hloop : ∀ v, a v v = 0) (v w : V) : (positiveGraph a).Adj v w ↔ 0 < a v w := by
  rw [positiveGraph, SimpleGraph.fromRel_adj]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · rw [hsymm]
      exact h
  · intro h
    refine ⟨?_, Or.inl h⟩
    rintro rfl
    rw [hloop] at h
    exact lt_irrefl _ h

noncomputable instance positiveGraph_locallyFinite [Fintype V] (a : V → V → ℝ) :
    (positiveGraph a).LocallyFinite :=
  fun _ => Fintype.ofFinite _

theorem isCond_positiveGraph {a : V → V → ℝ} (hsymm : ∀ v w, a v w = a w v)
    (hnonneg : ∀ v w, 0 ≤ a v w) (hloop : ∀ v, a v v = 0) : IsCond (positiveGraph a) a where
  symm := hsymm
  pos := fun v w h => (positiveGraph_adj_iff hsymm hloop v w).mp h
  zero_of_not_adj := fun v w h => by
    have hnot : ¬ 0 < a v w := fun hp => h ((positiveGraph_adj_iff hsymm hloop v w).mpr hp)
    exact le_antisymm (not_lt.mp hnot) (hnonneg v w)

theorem reachable_positiveGraph_iff {a : V → V → ℝ} (hsymm : ∀ v w, a v w = a w v)
    (hloop : ∀ v, a v v = 0) (v w : V) :
    (positiveGraph a).Reachable v w ↔ Relation.ReflTransGen (fun x y => 0 < a x y) v w := by
  have hrel : (positiveGraph a).Adj = fun x y => 0 < a x y :=
    funext fun x => funext fun y => propext (positiveGraph_adj_iff hsymm hloop x y)
  rw [SimpleGraph.reachable_iff_reflTransGen, hrel]

/-- Accessibility by positive-weight paths is accessibility in the positive-weight graph.
This is the form in which networks given by a weight matrix are stated. -/
theorem accessible_iff_boundaryAccessible {a : V → V → ℝ} (hsymm : ∀ v w, a v w = a w v)
    (hloop : ∀ v, a v v = 0) (A : Finset V) :
    (∀ v ∈ A, ∃ w, w ∉ A ∧ Relation.ReflTransGen (fun x y => 0 < a x y) v w) ↔
      BoundaryAccessible (positiveGraph a) A := by
  simp only [BoundaryAccessible, reachable_positiveGraph_iff hsymm hloop]

/-- Over a finite vertex type, the network Laplacian of the positive-weight graph is the signed
weighted sum over all vertices. -/
theorem netLaplacian_positiveGraph [Fintype V] {a : V → V → ℝ}
    (hsymm : ∀ v w, a v w = a w v) (hnonneg : ∀ v w, 0 ≤ a v w) (hloop : ∀ v, a v v = 0)
    (f : V → ℝ) (x : V) :
    netLaplacian (positiveGraph a) a f x = ∑ w, a x w * (f w - f x) := by
  have hc := isCond_positiveGraph hsymm hnonneg hloop
  unfold netLaplacian
  exact sum_neighborFinset_eq_sum x Finset.univ (fun w => a x w * (f w - f x))
    (fun y hy => by simp [hc.zero_of_not_adj hy]) (fun y _ _ => Finset.mem_univ y)

/-! ### Nonvacuity examples

The path `0 – 1 – 2` with unit conductance, the disconnected graph with one edge `0 – 1`
and `2` isolated, and a strictly subharmonic function on the path. -/

namespace DirichletExamples

open SimpleGraph

@[reducible] noncomputable def pathLocallyFinite : (pathGraph 3).LocallyFinite :=
  fun _ => Fintype.ofFinite _

attribute [local instance] pathLocallyFinite

/-- The boundary data: `0` at vertex `0` and `1` at vertex `2`. -/
def pathBoundary : Fin 3 → ℝ := fun v => if v = 2 then 1 else 0

/-- The linear function `v ↦ v / 2` on the path. -/
noncomputable def pathHalf : Fin 3 → ℝ := fun v => ((v : ℕ) : ℝ) / 2

lemma pathGraph_three_neighborFinset_one : (pathGraph 3).neighborFinset 1 = {0, 2} := by
  ext j
  rw [mem_neighborFinset, pathGraph_adj]
  fin_cases j <;> simp

/-- `A = {1}` is accessible in the path, since `0` and `2` lie outside it. -/
theorem pathGraph_accessible : BoundaryAccessible (pathGraph 3) ({1} : Finset (Fin 3)) :=
  boundaryAccessible_of_connected (pathGraph_connected 2) _ ⟨0, by decide⟩

/-- In the solved example, the harmonic function `pathHalf` has zero Laplacian at `1`. -/
lemma pathHalf_harmonic_one :
    netLaplacian (pathGraph 3) (unitCond (pathGraph 3)) pathHalf 1 = 0 := by
  rw [netLaplacian, pathGraph_three_neighborFinset_one,
    Finset.sum_pair (show (0 : Fin 3) ≠ 2 by decide)]
  norm_num [unitCond, pathHalf, pathGraph_adj]

/-- **Solved example.** For the path `0 – 1 – 2` with unit conductance, `A = {1}`, and boundary
values `0` at `0` and `1` at `2`, the solution at `1` is `1/2`. -/
theorem pathGraph_dirichletSolution_one :
    dirichletSolution (isCond_unitCond (G := pathGraph 3)) ({1} : Finset (Fin 3))
      pathGraph_accessible pathBoundary 1 = 1 / 2 := by
  have hsol : SolvesDirichlet (pathGraph 3) (unitCond (pathGraph 3)) {1} pathBoundary pathHalf := by
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · rw [Finset.mem_singleton] at hv
      subst hv
      exact pathHalf_harmonic_one
    · fin_cases v <;> simp_all [pathBoundary, pathHalf]
  have huniq := dirichlet_unique (isCond_unitCond (G := pathGraph 3)) {1} pathGraph_accessible
    (dirichletSolution_spec (isCond_unitCond (G := pathGraph 3)) {1} pathGraph_accessible
      pathBoundary) hsol
  rw [huniq]
  norm_num [pathHalf]

/-- **Maximum principle, nonvacuous.** On the path, `pathHalf` is subharmonic on `{1}` and
bounded by `1` off `{1}`, so it is bounded by `1` everywhere. -/
theorem pathHalf_le_one : ∀ v, pathHalf v ≤ 1 := by
  refine subharmonic_maximum_principle (isCond_unitCond (G := pathGraph 3)) {1} pathGraph_accessible
    pathHalf 1 (fun v hv => ?_) (fun v hv => ?_)
  · rw [Finset.mem_singleton] at hv
    subst hv
    exact le_of_eq pathHalf_harmonic_one.symm
  · fin_cases v <;> simp_all [pathHalf]

/-- The single edge `0 – 1` on `Fin 3`; the vertex `2` is isolated. -/
def edgeGraph : SimpleGraph (Fin 3) := fromEdgeSet {s(0, 1)}

/-- `edgeGraph` is not connected: every walk that starts outside `2` stays outside `2`, so no
walk leads from `0` to `2`. -/
theorem edgeGraph_not_connected : ¬ edgeGraph.Connected := by
  intro h
  obtain ⟨p⟩ := h.preconnected 0 2
  have key : ∀ {u w : Fin 3} (q : edgeGraph.Walk u w), u ≠ 2 → w ≠ 2 := by
    intro u w q
    induction q with
    | nil => exact id
    | @cons a b _ hab q ih =>
      intro ha
      apply ih
      rintro rfl
      fin_cases a <;> simp_all [edgeGraph, fromEdgeSet_adj]
  exact key p (by decide) rfl

/-- **Accessibility on a disconnected graph.** In `edgeGraph`, `{0}` is accessible through the
edge to `1`, although the graph is not connected. -/
theorem edgeGraph_accessible : BoundaryAccessible edgeGraph ({0} : Finset (Fin 3)) := by
  intro v hv
  rw [Finset.mem_singleton] at hv
  subst hv
  exact ⟨1, by decide, SimpleGraph.Adj.reachable (by simp [edgeGraph, fromEdgeSet_adj])⟩

/-- **Strictly subharmonic witness.** On the path, `v ↦ v²` has positive Laplacian at `1`, so
`{1}` is accessible by `boundaryAccessible_of_strict_subharmonic`. -/
theorem pathGraph_accessible_of_strict :
    BoundaryAccessible (pathGraph 3) ({1} : Finset (Fin 3)) := by
  refine boundaryAccessible_of_strict_subharmonic (isCond_unitCond (G := pathGraph 3))
    {1} (fun v => ((v : ℕ) : ℝ) ^ 2) (fun v hv => ?_)
  rw [Finset.mem_singleton] at hv
  subst hv
  rw [netLaplacian, pathGraph_three_neighborFinset_one,
    Finset.sum_pair (show (0 : Fin 3) ≠ 2 by decide)]
  norm_num [unitCond, pathGraph_adj]

end DirichletExamples

end LatticeProb.Network
