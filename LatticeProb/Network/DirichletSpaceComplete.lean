/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: ReflectedWalk/DirichletSpace.lean.
-/
import LatticeProb.Network.DirichletSpace
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Completeness of the Dirichlet space

Let `G` be a conductance graph on `V` whose underlying simple graph is connected, and let `a₀ : V`.
This file proves that the Dirichlet space `D₀` of `LatticeProb.Network.ConductanceGraph.DirichletSpace`
is complete for the energy norm. It also shows that, for every finite set `A ⊆ V` (not necessarily
containing `a₀`), the subspace of `D₀` of functions vanishing on `A` is closed, hence complete.

* `ConductanceGraph.walkBound` is a constant such that `|f x| ≤ walkBound · √(2 Energy f)` on `D₀`.
* `DirichletSpace.abs_apply_le` and `DirichletSpace.abs_apply_le_norm` are this bound, the second in
  terms of the norm of `D₀`.
* `ConductanceGraph.evalCLM` is evaluation at a vertex as a bounded linear functional on `D₀`.
* `DirichletSpace.instCompleteSpace` is the completeness of `D₀`.
* `ConductanceGraph.zeroOn` is the subspace of `D₀` of functions vanishing on a finite set `A`;
  `isClosed_zeroOn` and `zeroOn.instCompleteSpace` show that it is closed and complete.
* `ConductanceGraph.DirichletSpaceComplete.Example` instantiates these on the path `0 – 1 – 2`.
-/

namespace LatticeProb.Network

namespace ConductanceGraph

variable {V : Type*} (G : ConductanceGraph V)

/-- A walk-dependent constant: for a connected graph, `walkBound hG a₀ x` is the walk constant of a
chosen walk from `a₀` to `x`. It satisfies `|f x| ≤ walkBound hG a₀ x * √(2 * Energy f)` for every
`f` in the Dirichlet space based at `a₀` (`DirichletSpace.abs_apply_le`). -/
noncomputable def walkBound (hG : G.toSimpleGraph.Connected) (a₀ x : V) : ℝ :=
  G.walkConst (hG.preconnected a₀ x).some

namespace DirichletSpace

variable {G} {hG : G.toSimpleGraph.Connected} {a₀ : V}

/-- Evaluation at a vertex is bounded by the walk constant times the square root of twice the
energy. -/
lemma abs_apply_le (f : G.DirichletSpace hG a₀) (x : V) :
    |f x| ≤ G.walkBound hG a₀ x * Real.sqrt (2 * G.Energy f) := by
  have hb := G.abs_sub_le_walkConst_mul f.hasFiniteEnergy (hG.preconnected a₀ x).some
  rwa [f.apply_base, sub_zero] at hb

/-- Evaluation at a vertex is bounded by the energy norm. -/
lemma abs_apply_le_norm (f : G.DirichletSpace hG a₀) (x : V) :
    |f x| ≤ (G.walkBound hG a₀ x * Real.sqrt 2) * ‖f‖ := by
  rw [norm_eq_sqrt_energy, mul_assoc, ← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  exact f.abs_apply_le x

end DirichletSpace

/-- Evaluation at `x` as a bounded linear functional on the Dirichlet space `D₀` based at `a₀`. -/
noncomputable def evalCLM (hG : G.toSimpleGraph.Connected) (a₀ x : V) :
    G.DirichletSpace hG a₀ →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => f x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    (G.walkBound hG a₀ x * Real.sqrt 2)
    (fun f => by rw [Real.norm_eq_abs]; exact f.abs_apply_le_norm x)

/-- The value of `evalCLM` at `f` is the value of `f` at `x`. -/
@[simp] lemma evalCLM_apply (hG : G.toSimpleGraph.Connected) (a₀ x : V)
    (f : G.DirichletSpace hG a₀) : G.evalCLM hG a₀ x f = f x := rfl

/-! ### Completeness of the Dirichlet space -/

open Filter Topology

/-- A Cauchy sequence in the Dirichlet space converges at every vertex, because evaluation at a
vertex is a continuous linear functional. -/
lemma exists_pointwise_limit {hG : G.toSimpleGraph.Connected} {a₀ : V}
    {u : ℕ → G.DirichletSpace hG a₀} (hu : CauchySeq u) (x : V) :
    ∃ l : ℝ, Tendsto (fun n => u n x) atTop (𝓝 l) :=
  cauchySeq_tendsto_of_complete ((G.evalCLM hG a₀ x).uniformContinuous.comp_cauchySeq hu)

/-- Fatou-type bound: if the finite partial energy sums of `g − u m` are bounded by `C` for all
`m ≥ N` and `u m → f` pointwise, then `g − f` has finite energy with ordered-pair energy sum
at most `C`. -/
lemma summable_gradSq_sub_limit_of_le {hG : G.toSimpleGraph.Connected} {a₀ : V}
    {u : ℕ → G.DirichletSpace hG a₀} {f : V → ℝ}
    (hf : ∀ x, Tendsto (fun m => u m x) atTop (𝓝 (f x))) (g : G.DirichletSpace hG a₀)
    {C : ℝ} {N : ℕ}
    (hC : ∀ m ≥ N, ∀ S : Finset (V × V), ∑ p ∈ S, G.gradSq (g - u m) p ≤ C) :
    Summable (G.gradSq (⇑g - f)) ∧ ∑' p, G.gradSq (⇑g - f) p ≤ C := by
  have key : ∀ S : Finset (V × V), ∑ p ∈ S, G.gradSq (⇑g - f) p ≤ C := by
    intro S
    have hlim : Tendsto (fun m => ∑ p ∈ S, G.gradSq (g - u m) p) atTop
        (𝓝 (∑ p ∈ S, G.gradSq (⇑g - f) p)) := by
      apply tendsto_finsetSum
      intro p _
      simp only [gradSq, Pi.sub_apply]
      exact (((tendsto_const_nhds.sub (hf p.2)).sub
        (tendsto_const_nhds.sub (hf p.1))).pow 2).const_mul _
    exact le_of_tendsto hlim (eventually_atTop.2 ⟨N, fun m hm => hC m hm S⟩)
  exact ⟨summable_of_sum_le (fun p => G.gradSq_nonneg _ p) key,
    Real.tsum_le_of_sum_le (fun p => G.gradSq_nonneg _ p) key⟩

/-- **The Dirichlet space is complete.** A Cauchy sequence converges pointwise by
`exists_pointwise_limit`; the pointwise limit has finite energy, and it is the energy-norm limit by
the bound `summable_gradSq_sub_limit_of_le`. -/
instance DirichletSpace.instCompleteSpace {hG : G.toSimpleGraph.Connected} {a₀ : V} :
    CompleteSpace (G.DirichletSpace hG a₀) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  choose f hf using fun x => G.exists_pointwise_limit hu x
  have hbound : ∀ δ > 0, ∃ N, ∀ n ≥ N, ∀ m ≥ N, ∀ S : Finset (V × V),
      ∑ p ∈ S, G.gradSq (⇑(u n - u m)) p ≤ 2 * δ ^ 2 := by
    intro δ hδ
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hu δ hδ
    refine ⟨N, fun n hn m hm S => ?_⟩
    have h1 : dist (u n) (u m) < δ := hN n hn m hm
    rw [dist_eq_norm, DirichletSpace.norm_eq_sqrt_energy, Real.sqrt_lt' hδ] at h1
    have h3 := (u n - u m).hasFiniteEnergy.sum_le_tsum S (fun p _ => G.gradSq_nonneg _ p)
    rw [G.tsum_gradSq_eq] at h3
    linarith
  obtain ⟨N₀, hN₀⟩ := hbound 1 one_pos
  have hfin : G.HasFiniteEnergy f := by
    have h1 := (G.summable_gradSq_sub_limit_of_le hf (u N₀)
      (fun m hm S => hN₀ N₀ le_rfl m hm S)).1
    have h2 : f = ⇑(u N₀) - (⇑(u N₀) - f) := by ext x; simp
    rw [h2]
    exact (u N₀).hasFiniteEnergy.sub h1
  have hf0 : f a₀ = 0 := by
    refine tendsto_nhds_unique (hf a₀) ?_
    simp only [DirichletSpace.apply_base]
    exact tendsto_const_nhds
  refine ⟨DirichletSpace.mk (hG := hG) f hfin hf0, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := hbound (ε / 2) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  rw [dist_eq_norm, DirichletSpace.norm_eq_sqrt_energy]
  have h1 := (G.summable_gradSq_sub_limit_of_le hf (u n) (fun m hm S => hN n hn m hm S)).2
  have hE : G.Energy (⇑(u n - DirichletSpace.mk (hG := hG) f hfin hf0)) ≤ (ε / 2) ^ 2 := by
    show (∑' p, G.gradSq (⇑(u n) - f) p) / 2 ≤ (ε / 2) ^ 2
    linarith
  calc Real.sqrt (G.Energy (⇑(u n - DirichletSpace.mk (hG := hG) f hfin hf0)))
      ≤ Real.sqrt ((ε / 2) ^ 2) := Real.sqrt_le_sqrt hE
    _ = ε / 2 := Real.sqrt_sq (by positivity)
    _ < ε := by linarith

/-! ### The subspaces `D_A` of functions vanishing on a finite set -/

/-- For a finite set `A ⊆ V`, `zeroOn hG a₀ A` is the submodule of the Dirichlet space `D₀` of
functions vanishing at every point of `A`. The set `A` is arbitrary: it need not contain `a₀`. -/
def zeroOn (hG : G.toSimpleGraph.Connected) (a₀ : V) (A : Finset V) :
    Submodule ℝ (G.DirichletSpace hG a₀) where
  carrier := {f | ∀ a ∈ A, f a = 0}
  add_mem' := fun {f g} hf hg a ha => by
    rw [DirichletSpace.add_apply, hf a ha, hg a ha, add_zero]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun r {f} hf a ha => by
    rw [DirichletSpace.smul_apply, hf a ha, mul_zero]

/-- Membership in `zeroOn hG a₀ A`: the function vanishes at every point of `A`. -/
lemma mem_zeroOn {hG : G.toSimpleGraph.Connected} {a₀ : V} {A : Finset V}
    {f : G.DirichletSpace hG a₀} : f ∈ G.zeroOn hG a₀ A ↔ ∀ a ∈ A, f a = 0 := Iff.rfl

/-- For every finite set `A ⊆ V`, not necessarily containing `a₀`, the subspace `zeroOn hG a₀ A`
of the Dirichlet space is closed. It is the intersection of the kernels of the evaluation
functionals at the points of `A`, which are continuous. -/
lemma isClosed_zeroOn (hG : G.toSimpleGraph.Connected) (a₀ : V) (A : Finset V) :
    IsClosed (G.zeroOn hG a₀ A : Set (G.DirichletSpace hG a₀)) := by
  have h : (G.zeroOn hG a₀ A : Set (G.DirichletSpace hG a₀)) =
      ⋂ a, ⋂ (_ : a ∈ A), {f : G.DirichletSpace hG a₀ | f a = 0} := by
    ext f
    simp only [SetLike.mem_coe, mem_zeroOn, Set.mem_iInter, Set.mem_setOf_eq]
  rw [h]
  exact isClosed_iInter fun a => isClosed_iInter fun _ =>
    isClosed_eq (G.evalCLM hG a₀ a).continuous continuous_const

/-- For every finite set `A ⊆ V`, the subspace `zeroOn hG a₀ A` of the Dirichlet space is complete,
being closed in a complete space (`isClosed_zeroOn`). -/
instance zeroOn.instCompleteSpace (hG : G.toSimpleGraph.Connected) (a₀ : V) (A : Finset V) :
    CompleteSpace (G.zeroOn hG a₀ A) :=
  (G.isClosed_zeroOn hG a₀ A).completeSpace_coe

end ConductanceGraph

/-! ## Nonvacuity: the path `0 – 1 – 2`

On the path `0 – 1 – 2` the Dirichlet space based at `0` contains the nonzero function `ramp`, and
the bounds and subspaces above can be evaluated at it. -/

namespace ConductanceGraph.DirichletSpaceComplete.Example

open ConductanceGraph.DirichletSpace.Example

/-- The bound `abs_apply_le_norm` applied to `ramp` at the vertex `1`. -/
example : |ramp 1| ≤
    (ConductanceGraph.Example.path3.walkBound path3_connected 0 1 * Real.sqrt 2) * ‖ramp‖ :=
  ramp.abs_apply_le_norm 1

/-- `evalCLM` at the vertex `1` applied to `ramp` is the value `1`. -/
example : ConductanceGraph.Example.path3.evalCLM path3_connected 0 1 ramp = 1 := by
  simp [evalCLM_apply, ramp]

/-- The zero element of the Dirichlet space lies in `zeroOn` for the set `A = {2}`. -/
example : (0 : ConductanceGraph.Example.path3.DirichletSpace path3_connected 0) ∈
    ConductanceGraph.Example.path3.zeroOn path3_connected 0 ({2} : Finset (Fin 3)) :=
  (ConductanceGraph.Example.path3.zeroOn path3_connected 0 ({2} : Finset (Fin 3))).zero_mem

end ConductanceGraph.DirichletSpaceComplete.Example

end LatticeProb.Network
