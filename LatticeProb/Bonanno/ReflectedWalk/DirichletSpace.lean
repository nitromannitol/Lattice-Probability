/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedWalk.DirichletSpace at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.Energy
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.Tactic.Linarith

/-!
# The Dirichlet space (Gwynne–Sung, Lemma 2.1 in function-space form)

Fix a connected conductance graph `G` and a basepoint `a₀`.  The **Dirichlet space**

  `D₀ := {f : V → ℝ | Energy(f) < ∞ ∧ f a₀ = 0}`

carries the Dirichlet form

  `⟪f, g⟫ = ½ ∑_{(x,y) ∈ V × V} c(x,y) (f y − f x)(g y − g x)`,

whose quadratic form is `Energy` (1.4).  This file shows that `D₀` is a real Hilbert space
and that, for a finite set `A ∋ a₀`, the subspace `D_A := {f ∈ D₀ | f|_A ≡ 0}` is closed.

## Relation to Lemma 2.1 of the paper

Gwynne–Sung prove Proposition 1.3 by orthogonal projection in the *edge* Hilbert space
`Θ ⊆ ℓ²(→EG, c⁻¹)` of antisymmetric finite-energy edge functions, and their Lemma 2.1
asserts that `Θ̊_A = {∇f : f|_A ≡ 0}` is a closed subspace of `Θ`.  The gradient
`∇ : D₀ → Θ` is an isometry (by definition of the two inner products), and it is injective
because `G` is connected and functions in `D₀` vanish at `a₀`; the paper's closedness proof
is exactly the observation that `ℓ²`-convergence of `∇fₙ` forces pointwise convergence of
`fₙ` along any finite path from `A`.  We work directly on the function side:

* completeness of `D₀` (`DirichletSpace.instCompleteSpace`) is the statement that the image
  `∇(D₀) ⊆ Θ` is closed, proved by the same path argument in the quantitative form
  `abs_sub_le_walkConst_mul` of `Energy.lean`;
* closedness of `D_A` (`isClosed_zeroOn`) is the closedness half of Lemma 2.1 transported
  through `∇`.

**Deviation from the printed statement.**  The Lean development formalizes Lemma 2.1 in the
function-space model (`D₀`, `D_A`) rather than in the edge-space model (`Θ`, `Θ̊_A`).  The
second half of Lemma 2.1 — the description of `Θ̊_A^⊥` as the closed span of the cycles
modulo `A` — is *not* formalized: nothing downstream (Proposition 1.3, Section 2.2, or
Section 3) consumes it.
-/

namespace ReflectedWalk

namespace ConductanceGraph

variable {V : Type*} (G : ConductanceGraph V)

/-! ### Algebra of finite-energy functions -/

lemma gradSq_add_le (f g : V → ℝ) (p : V × V) :
    G.gradSq (f + g) p ≤ 2 * G.gradSq f p + 2 * G.gradSq g p := by
  simp only [gradSq, Pi.add_apply]
  have hc := G.c_nonneg p.1 p.2
  nlinarith [mul_nonneg hc (sq_nonneg ((f p.2 - f p.1) - (g p.2 - g p.1)))]

lemma gradSq_smul (a : ℝ) (f : V → ℝ) (p : V × V) :
    G.gradSq (a • f) p = a ^ 2 * G.gradSq f p := by
  simp only [gradSq, Pi.smul_apply, smul_eq_mul]; ring

lemma gradSq_neg (f : V → ℝ) (p : V × V) : G.gradSq (-f) p = G.gradSq f p := by
  simp only [gradSq, Pi.neg_apply]; ring

/-- Adding a constant does not change the gradient. -/
lemma gradSq_add_const (f : V → ℝ) (a : ℝ) (p : V × V) :
    G.gradSq (fun x => f x + a) p = G.gradSq f p := by
  simp only [gradSq]; ring

lemma gradSq_sub_const (f : V → ℝ) (a : ℝ) (p : V × V) :
    G.gradSq (fun x => f x - a) p = G.gradSq f p := by
  simp only [gradSq]; ring

lemma gradSq_const (a : ℝ) (p : V × V) : G.gradSq (fun _ => a) p = 0 := by
  simp [gradSq]

lemma hasFiniteEnergy_const (a : ℝ) : G.HasFiniteEnergy (fun _ => a) :=
  summable_zero.congr fun p => (G.gradSq_const a p).symm

lemma hasFiniteEnergy_zero : G.HasFiniteEnergy (0 : V → ℝ) := G.hasFiniteEnergy_const 0

section FiniteEnergyAlgebra

variable {G}

lemma HasFiniteEnergy.add {f g : V → ℝ} (hf : G.HasFiniteEnergy f)
    (hg : G.HasFiniteEnergy g) : G.HasFiniteEnergy (f + g) :=
  Summable.of_nonneg_of_le (fun p => G.gradSq_nonneg _ p) (fun p => G.gradSq_add_le f g p)
    ((hf.mul_left 2).add (hg.mul_left 2))

lemma HasFiniteEnergy.smul {f : V → ℝ} (hf : G.HasFiniteEnergy f) (a : ℝ) :
    G.HasFiniteEnergy (a • f) :=
  (hf.mul_left (a ^ 2)).congr fun p => (G.gradSq_smul a f p).symm

lemma HasFiniteEnergy.neg {f : V → ℝ} (hf : G.HasFiniteEnergy f) :
    G.HasFiniteEnergy (-f) :=
  hf.congr fun p => (G.gradSq_neg f p).symm

lemma HasFiniteEnergy.sub {f g : V → ℝ} (hf : G.HasFiniteEnergy f)
    (hg : G.HasFiniteEnergy g) : G.HasFiniteEnergy (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

lemma HasFiniteEnergy.add_const {f : V → ℝ} (hf : G.HasFiniteEnergy f) (a : ℝ) :
    G.HasFiniteEnergy (fun x => f x + a) :=
  hf.congr fun p => (G.gradSq_add_const f a p).symm

lemma HasFiniteEnergy.sub_const {f : V → ℝ} (hf : G.HasFiniteEnergy f) (a : ℝ) :
    G.HasFiniteEnergy (fun x => f x - a) :=
  hf.congr fun p => (G.gradSq_sub_const f a p).symm

end FiniteEnergyAlgebra

/-- Energy is translation invariant. -/
lemma Energy_add_const (f : V → ℝ) (a : ℝ) : G.Energy (fun x => f x + a) = G.Energy f := by
  unfold Energy
  simp_rw [G.gradSq_add_const f a]

lemma Energy_sub_const (f : V → ℝ) (a : ℝ) : G.Energy (fun x => f x - a) = G.Energy f := by
  unfold Energy
  simp_rw [G.gradSq_sub_const f a]

lemma Energy_const (a : ℝ) : G.Energy (fun _ => a) = 0 := by
  unfold Energy
  simp_rw [G.gradSq_const a]
  simp

lemma Energy_neg (f : V → ℝ) : G.Energy (-f) = G.Energy f := by
  unfold Energy
  simp_rw [G.gradSq_neg f]

/-! ### The Dirichlet form -/

/-- The contribution of one ordered pair to the Dirichlet form
`½ ∑ c(x,y)(f y − f x)(g y − g x)`. -/
noncomputable def gradProd (f g : V → ℝ) (p : V × V) : ℝ :=
  G.c p.1 p.2 * ((f p.2 - f p.1) * (g p.2 - g p.1))

lemma gradProd_self (f : V → ℝ) (p : V × V) : G.gradProd f f p = G.gradSq f p := by
  simp only [gradProd, gradSq, sq]

lemma gradProd_comm (f g : V → ℝ) (p : V × V) : G.gradProd f g p = G.gradProd g f p := by
  simp only [gradProd, mul_comm]

lemma gradProd_add_left (f g k : V → ℝ) (p : V × V) :
    G.gradProd (f + g) k p = G.gradProd f k p + G.gradProd g k p := by
  simp only [gradProd, Pi.add_apply]; ring

lemma gradProd_smul_left (a : ℝ) (f g : V → ℝ) (p : V × V) :
    G.gradProd (a • f) g p = a * G.gradProd f g p := by
  simp only [gradProd, Pi.smul_apply, smul_eq_mul]; ring

/-- The pointwise Cauchy–Schwarz bound `|c·ab| ≤ c(a² + b²)/2`. -/
lemma abs_gradProd_le (f g : V → ℝ) (p : V × V) :
    |G.gradProd f g p| ≤ (G.gradSq f p + G.gradSq g p) / 2 := by
  simp only [gradProd, gradSq]
  have hc := G.c_nonneg p.1 p.2
  rw [abs_mul, abs_of_nonneg hc, abs_mul]
  have h1 : |f p.2 - f p.1| * |g p.2 - g p.1|
      ≤ ((f p.2 - f p.1) ^ 2 + (g p.2 - g p.1) ^ 2) / 2 := by
    nlinarith [sq_nonneg (|f p.2 - f p.1| - |g p.2 - g p.1|), sq_abs (f p.2 - f p.1),
      sq_abs (g p.2 - g p.1)]
  calc G.c p.1 p.2 * (|f p.2 - f p.1| * |g p.2 - g p.1|)
      ≤ G.c p.1 p.2 * (((f p.2 - f p.1) ^ 2 + (g p.2 - g p.1) ^ 2) / 2) :=
        mul_le_mul_of_nonneg_left h1 hc
    _ = _ := by ring

/-- The Dirichlet form of two finite-energy functions is absolutely summable. -/
lemma summable_gradProd {f g : V → ℝ} (hf : G.HasFiniteEnergy f) (hg : G.HasFiniteEnergy g) :
    Summable (G.gradProd f g) :=
  Summable.of_norm_bounded ((Summable.add hf hg).div_const 2) (fun p => by
    rw [Real.norm_eq_abs]; exact G.abs_gradProd_le f g p)

/-- The Dirichlet form `⟪f, g⟫ = ½ ∑_{(x,y)} c(x,y)(f y − f x)(g y − g x)`, whose quadratic
form is the Dirichlet energy (1.4). -/
noncomputable def dirichletForm (f g : V → ℝ) : ℝ := (∑' p : V × V, G.gradProd f g p) / 2

lemma dirichletForm_self (f : V → ℝ) : G.dirichletForm f f = G.Energy f := by
  unfold dirichletForm Energy
  simp_rw [G.gradProd_self f]

lemma dirichletForm_comm (f g : V → ℝ) : G.dirichletForm f g = G.dirichletForm g f := by
  unfold dirichletForm
  simp_rw [G.gradProd_comm f g]

lemma dirichletForm_add_left {f g k : V → ℝ} (hf : G.HasFiniteEnergy f)
    (hg : G.HasFiniteEnergy g) (hk : G.HasFiniteEnergy k) :
    G.dirichletForm (f + g) k = G.dirichletForm f k + G.dirichletForm g k := by
  unfold dirichletForm
  simp_rw [G.gradProd_add_left f g k]
  rw [(G.summable_gradProd hf hk).tsum_add (G.summable_gradProd hg hk), add_div]

lemma dirichletForm_smul_left (a : ℝ) (f g : V → ℝ) :
    G.dirichletForm (a • f) g = a * G.dirichletForm f g := by
  unfold dirichletForm
  simp_rw [G.gradProd_smul_left a f g]
  rw [tsum_mul_left, mul_div_assoc]

/-! ### The Dirichlet space `D₀` -/

/-- The finite-energy functions vanishing at `a₀`, as a submodule of `V → ℝ`.  Only the
algebraic structure of `D₀` is taken from here; its topology comes from the energy norm. -/
def dirichletSubmodule (a₀ : V) : Submodule ℝ (V → ℝ) where
  carrier := {f | G.HasFiniteEnergy f ∧ f a₀ = 0}
  add_mem' := fun {f g} hf hg =>
    ⟨hf.1.add hg.1, by simp only [Pi.add_apply, hf.2, hg.2, add_zero]⟩
  zero_mem' := ⟨G.hasFiniteEnergy_zero, rfl⟩
  smul_mem' := fun a {f} hf => ⟨hf.1.smul a, by simp only [Pi.smul_apply, hf.2, smul_zero]⟩

set_option linter.unusedVariables false in
/-- **The Dirichlet space** `D₀ = {f : V → ℝ | Energy(f) < ∞, f a₀ = 0}` of a connected
conductance graph, the function-space model of the paper's `Θ` restricted to gradients
(Gwynne–Sung Section 2.1).

This is a `def`, not an `abbrev`, so that `D₀` does not inherit the product topology of
`V → ℝ`; its topology is the one induced by the energy norm defined below.  The
connectedness hypothesis is part of the type because completeness depends on it (it is
otherwise unused by the definition, hence the silenced linter). -/
def DirichletSpace (hG : G.toSimpleGraph.Connected) (a₀ : V) := ↥(G.dirichletSubmodule a₀)

namespace DirichletSpace

variable {G} {hG : G.toSimpleGraph.Connected} {a₀ : V}

instance : AddCommGroup (G.DirichletSpace hG a₀) :=
  inferInstanceAs (AddCommGroup (G.dirichletSubmodule a₀))

instance : Module ℝ (G.DirichletSpace hG a₀) :=
  inferInstanceAs (Module ℝ (G.dirichletSubmodule a₀))

instance : FunLike (G.DirichletSpace hG a₀) V ℝ where
  coe f := Subtype.val f
  coe_injective := Subtype.val_injective

/-- Build an element of `D₀` from a finite-energy function vanishing at `a₀`. -/
def mk (f : V → ℝ) (hf : G.HasFiniteEnergy f) (h0 : f a₀ = 0) : G.DirichletSpace hG a₀ :=
  ⟨f, hf, h0⟩

@[simp] lemma coe_mk (f : V → ℝ) (hf : G.HasFiniteEnergy f) (h0 : f a₀ = 0) :
    ⇑(mk f hf h0 : G.DirichletSpace hG a₀) = f := rfl

@[ext] lemma ext {f g : G.DirichletSpace hG a₀} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

lemma hasFiniteEnergy (f : G.DirichletSpace hG a₀) : G.HasFiniteEnergy f :=
  (Subtype.prop f).1

lemma apply_base (f : G.DirichletSpace hG a₀) : f a₀ = 0 := (Subtype.prop f).2

@[simp] lemma coe_add (f g : G.DirichletSpace hG a₀) : ⇑(f + g) = ⇑f + ⇑g := rfl
@[simp] lemma coe_sub (f g : G.DirichletSpace hG a₀) : ⇑(f - g) = ⇑f - ⇑g := rfl
@[simp] lemma coe_neg (f : G.DirichletSpace hG a₀) : ⇑(-f) = -⇑f := rfl
@[simp] lemma coe_smul (a : ℝ) (f : G.DirichletSpace hG a₀) : ⇑(a • f) = a • ⇑f := rfl
@[simp] lemma coe_zero : ⇑(0 : G.DirichletSpace hG a₀) = 0 := rfl

lemma add_apply (f g : G.DirichletSpace hG a₀) (x : V) : (f + g) x = f x + g x := rfl
lemma sub_apply (f g : G.DirichletSpace hG a₀) (x : V) : (f - g) x = f x - g x := rfl
lemma neg_apply (f : G.DirichletSpace hG a₀) (x : V) : (-f) x = -f x := rfl
lemma smul_apply (a : ℝ) (f : G.DirichletSpace hG a₀) (x : V) : (a • f) x = a * f x := rfl
lemma zero_apply (x : V) : (0 : G.DirichletSpace hG a₀) x = 0 := rfl

/-- The Dirichlet form is a genuine inner product on `D₀`: definiteness uses connectedness
(`abs_sub_le_walkConst_mul`) together with the normalisation `f a₀ = 0`. -/
noncomputable instance instInnerProductSpaceCore :
    InnerProductSpace.Core ℝ (G.DirichletSpace hG a₀) where
  inner f g := G.dirichletForm f g
  conj_inner_symm f g := by
    simp only [RCLike.conj_to_real]
    exact G.dirichletForm_comm g f
  re_inner_nonneg f := by
    simp only [RCLike.re_to_real]
    rw [G.dirichletForm_self]
    exact G.Energy_nonneg _
  add_left f g k :=
    G.dirichletForm_add_left f.hasFiniteEnergy g.hasFiniteEnergy k.hasFiniteEnergy
  smul_left f g r := by
    simp only [RCLike.conj_to_real]
    exact G.dirichletForm_smul_left r f g
  definite f h := by
    have hE : G.Energy f = 0 := by rw [← G.dirichletForm_self]; exact h
    ext x
    have hb := G.abs_sub_le_walkConst_mul f.hasFiniteEnergy (hG.preconnected a₀ x).some
    rw [hE, mul_zero, Real.sqrt_zero, mul_zero, f.apply_base, sub_zero] at hb
    rw [zero_apply]
    exact abs_nonpos_iff.mp hb

noncomputable instance : NormedAddCommGroup (G.DirichletSpace hG a₀) :=
  InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ)

noncomputable instance : InnerProductSpace ℝ (G.DirichletSpace hG a₀) :=
  InnerProductSpace.ofCore _

lemma inner_def (f g : G.DirichletSpace hG a₀) : inner ℝ f g = G.dirichletForm f g := rfl

/-- The norm of `D₀` is the square root of the Dirichlet energy. -/
lemma norm_eq_sqrt_energy (f : G.DirichletSpace hG a₀) : ‖f‖ = Real.sqrt (G.Energy f) := by
  rw [norm_eq_sqrt_real_inner, inner_def, G.dirichletForm_self]

lemma norm_sq_eq_energy (f : G.DirichletSpace hG a₀) : ‖f‖ ^ 2 = G.Energy f := by
  rw [norm_eq_sqrt_energy, Real.sq_sqrt (G.Energy_nonneg _)]

end DirichletSpace

/-- A walk-dependent constant with `|f x| ≤ walkBound x · √(2 Energy f)` for every `f ∈ D₀`
(Gwynne–Sung, proof of Lemma 2.1: the value at `x` is controlled along a path from `A`). -/
noncomputable def walkBound (hG : G.toSimpleGraph.Connected) (a₀ x : V) : ℝ :=
  G.walkConst (hG.preconnected a₀ x).some

namespace DirichletSpace

variable {G} {hG : G.toSimpleGraph.Connected} {a₀ : V}

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

/-- Evaluation at `x` as a bounded linear functional on `D₀`. -/
noncomputable def evalCLM (hG : G.toSimpleGraph.Connected) (a₀ x : V) :
    G.DirichletSpace hG a₀ →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => f x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    (G.walkBound hG a₀ x * Real.sqrt 2)
    (fun f => by rw [Real.norm_eq_abs]; exact f.abs_apply_le_norm x)

@[simp] lemma evalCLM_apply (hG : G.toSimpleGraph.Connected) (a₀ x : V)
    (f : G.DirichletSpace hG a₀) : G.evalCLM hG a₀ x f = f x := rfl

/-! ### Completeness of `D₀` (Gwynne–Sung Lemma 2.1, closedness half) -/

open Filter Topology

/-- Energy-norm Cauchy sequences converge pointwise: the "pointwise convergence along a
path" step in the proof of Lemma 2.1. -/
lemma exists_pointwise_limit {hG : G.toSimpleGraph.Connected} {a₀ : V}
    {u : ℕ → G.DirichletSpace hG a₀} (hu : CauchySeq u) (x : V) :
    ∃ l : ℝ, Tendsto (fun n => u n x) atTop (𝓝 l) :=
  cauchySeq_tendsto_of_complete ((G.evalCLM hG a₀ x).uniformContinuous.comp_cauchySeq hu)

/-- Fatou-type step: if the finite partial energy sums of `g − u m` are bounded by `C` for all
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

/-- **`D₀` is complete** (Gwynne–Sung Lemma 2.1, closedness of `∇(D₀)` in `Θ`).  A Cauchy
sequence converges pointwise by `exists_pointwise_limit`; the pointwise limit has finite
energy and is the energy-norm limit by the Fatou-type bound `summable_gradSq_sub_limit_of_le`. -/
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

/-! ### The closed subspace `D_A` (Gwynne–Sung (2.3), function-space form) -/

/-- `D_A ⊆ D₀`: the finite-energy functions vanishing on `A` (and at `a₀`).  This is the
function-space form of the paper's `Θ̊_A` (2.3): `∇` maps it isometrically onto `Θ̊_A`. -/
def zeroOn (hG : G.toSimpleGraph.Connected) (a₀ : V) (A : Finset V) :
    Submodule ℝ (G.DirichletSpace hG a₀) where
  carrier := {f | ∀ a ∈ A, f a = 0}
  add_mem' := fun {f g} hf hg a ha => by
    rw [DirichletSpace.add_apply, hf a ha, hg a ha, add_zero]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun r {f} hf a ha => by
    rw [DirichletSpace.smul_apply, hf a ha, mul_zero]

lemma mem_zeroOn {hG : G.toSimpleGraph.Connected} {a₀ : V} {A : Finset V}
    {f : G.DirichletSpace hG a₀} : f ∈ G.zeroOn hG a₀ A ↔ ∀ a ∈ A, f a = 0 := Iff.rfl

/-- **`D_A` is closed in `D₀`** (Gwynne–Sung Lemma 2.1, closedness of `Θ̊_A`): it is the
intersection of the kernels of the continuous evaluation functionals at the points of `A`. -/
lemma isClosed_zeroOn (hG : G.toSimpleGraph.Connected) (a₀ : V) (A : Finset V) :
    IsClosed (G.zeroOn hG a₀ A : Set (G.DirichletSpace hG a₀)) := by
  have h : (G.zeroOn hG a₀ A : Set (G.DirichletSpace hG a₀)) =
      ⋂ a, ⋂ (_ : a ∈ A), {f : G.DirichletSpace hG a₀ | f a = 0} := by
    ext f
    simp only [SetLike.mem_coe, mem_zeroOn, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [h]
  exact isClosed_iInter fun a => isClosed_iInter fun _ =>
    isClosed_eq (G.evalCLM hG a₀ a).continuous continuous_const

instance zeroOn.instCompleteSpace (hG : G.toSimpleGraph.Connected) (a₀ : V) (A : Finset V) :
    CompleteSpace (G.zeroOn hG a₀ A) :=
  (G.isClosed_zeroOn hG a₀ A).isComplete.completeSpace_coe

end ConductanceGraph

end ReflectedWalk
