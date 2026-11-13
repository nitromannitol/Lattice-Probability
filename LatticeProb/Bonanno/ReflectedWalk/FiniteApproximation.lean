/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedWalk.FiniteApproximation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedWalk.HarmonicMeasure
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Set.Countable
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Finite approximation (Gwynne–Sung, Section 2.3, p. 16)

Section 2.3 of arXiv:2506.18827 consists of a single statement, **Proposition 2.5**: for an
increasing family `{Gₙ}` of finite connected subgraphs of `G` whose union is `G`, the
`Gₙ`-discrete harmonic extension `hₙ^φ` of `φ|_A` converges pointwise to the energy-minimizing
extension `h_φ` of Proposition 1.3.  This file formalizes it, together with the objects the
statement presupposes (the finite subgraphs, their energies and Laplacians, and the existence and
uniqueness of `hₙ^φ`) and two immediate consequences (convergence of the finite harmonic
measures, and convergence of the finite energies).

## Subgraphs

The paper (p. 12) equips every subgraph of `G` with the restriction of `c`.  A finite subgraph is
carried by its vertex set `S : Finset V`; the subgraph `G_S` is the subgraph *induced* on `S`,
i.e. `G.induce ↑S : ConductanceGraph ↥S` with conductance `c` restricted.  Everything that only
depends on the vertex set is stated for functions on `V` with restricted sums:

* `energyOn S f = ½ ∑_{(x,y) ∈ S × S} c(x,y)(f y − f x)²` is `Energy_{G_S}(f|_S)`
  (`Energy_induce` identifies it with the `Energy` of `G.induce ↑S`);
* `lapWithin S f x = ∑_{y ∈ S} c(x,y)(f y − f x)` is the `G_S`-Laplacian, and
  `IsHarmonicWithinAt S f x` is "`f` is `G_S`-discrete harmonic at `x`".

**Footnote 4 (p. 16) is respected**: `lapWithin` sums only over neighbours *inside* `S`, so at a
vertex of `S` with neighbours outside `S` it differs from the `G`-Laplacian `lapTerm`-sum of
`Harmonic.lean`, and `IsHarmonicWithinAt` is not `IsHarmonicAt`.  The two notions are related
only through the induced graph (`isHarmonicAt_induce_iff`).  No local finiteness is assumed
anywhere: `S` is finite, `G` need not be.

## The exhaustion

`Exhaustion G` packages the family `{Gₙ}_{n ≥ 1}` (indexed by `ℕ`): a monotone
`Gsub : ℕ → Finset V`, each inducing a connected subgraph, with union all of `V`.  It is the
object Section 3 consumes (`Gₙ`, `V Gₙ`, `hm^x_{Gₙ}`), so it is defined once here.

## The proof

The paper argues by compactness (bounded sequences have pointwise convergent subsequences) and
identifies every subsequential limit through the energy bound and uniqueness.  We give a
compactness-free version of the same argument that produces the limit directly.  Writing
`eₙ := Energy_{Gₙ}(hₙ)`, the minimality of `hₙ` in `Gₙ` (a Pythagoras identity for the
`Gₙ`-energy, `energyOn_add_of_isHarmonicWithin`) gives

  `eₙ ≤ e_m ≤ Energy_G(h_φ)`  for `n ≤ m`,   and   `Energy_{G_k}(h_m − hₙ) ≤ e_m − eₙ`  for `k ≤ n ≤ m`,

so `eₙ` converges and, by the walk estimate of `Energy.lean` inside the connected graph `G_k`,
`(hₙ(x))ₙ` is Cauchy for every `x`.  The pointwise limit `h̃` agrees with `φ` on `A`, and the
paper's monotone-convergence step (`hasFiniteEnergy_and_Energy_le_of_energyOn_le`) gives
`Energy_G(h̃) ≤ lim eₙ ≤ Energy_G(h_φ)`, whence `h̃ = h_φ` by uniqueness (Proposition 1.3).
As a by-product `eₙ → Energy_G(h_φ)` (`tendsto_energyOn_of_isHarmonicWithin`).
-/

namespace ReflectedWalk

namespace ConductanceGraph

open Classical Filter Topology

variable {V : Type*} (G : ConductanceGraph V)

/-! ### Induced subgraphs (p. 12: subgraphs carry the restriction of `c`) -/

/-- The subgraph of `G` induced on the vertex set `s`, with conductances given by the
restriction of `c` (Gwynne–Sung p. 12, "all subgraphs of `G` are equipped with conductances given
by the restriction of `c`").  Its underlying simple graph is mathlib's `SimpleGraph.induce`
(`induce_toSimpleGraph`). -/
def induce (s : Set V) : ConductanceGraph s where
  c x y := G.c x y
  c_symm x y := G.c_symm x y
  c_nonneg x y := G.c_nonneg x y
  c_self x := G.c_self x
  summable_c x := (G.summable_c x).comp_injective Subtype.val_injective

@[simp] lemma induce_c (s : Set V) (x y : s) : (G.induce s).c x y = G.c x y := rfl

/-- The simple graph underlying `G.induce s` is the induced subgraph of `G.toSimpleGraph`. -/
lemma induce_toSimpleGraph (s : Set V) :
    (G.induce s).toSimpleGraph = G.toSimpleGraph.induce s := rfl

/-- Connectedness of the induced simple graph, transported to `G.induce ↑S`. -/
lemma induce_connected {S : Finset V} (hS : (G.toSimpleGraph.induce ↑S).Connected) :
    (G.induce ↑S).toSimpleGraph.Connected := by
  rw [G.induce_toSimpleGraph]; exact hS

/-! ### Energy and Laplacian of a finite subgraph (Section 2.3, footnote 4) -/

/-- `Energy_{G_S}(f)` (Gwynne–Sung p. 16): the Dirichlet energy of `f` computed in the subgraph
induced on the finite vertex set `S`, as half the sum over ordered pairs in `S × S` (the same
convention as `Energy`). -/
noncomputable def energyOn (S : Finset V) (f : V → ℝ) : ℝ := (∑ p ∈ S ×ˢ S, G.gradSq f p) / 2

lemma energyOn_nonneg (S : Finset V) (f : V → ℝ) : 0 ≤ G.energyOn S f :=
  div_nonneg (Finset.sum_nonneg fun p _ => G.gradSq_nonneg f p) (by norm_num)

/-- `Energy_{G_S} ≤ Energy_{G_T}` for `S ⊆ T` (the first inequality in the proof of
Proposition 2.5, p. 16). -/
lemma energyOn_mono {S T : Finset V} (hST : S ⊆ T) (f : V → ℝ) :
    G.energyOn S f ≤ G.energyOn T f := by
  unfold energyOn
  have := Finset.sum_le_sum_of_subset_of_nonneg (Finset.product_subset_product hST hST)
    fun p _ _ => G.gradSq_nonneg f p
  linarith

/-- `Energy_{G_S}(f|_S) ≤ Energy_G(f)` for finite-energy `f` (the last inequality in the proof
of Proposition 2.5, p. 16). -/
lemma energyOn_le_Energy {f : V → ℝ} (hf : G.HasFiniteEnergy f) (S : Finset V) :
    G.energyOn S f ≤ G.Energy f := by
  unfold energyOn Energy
  have := hf.sum_le_tsum (S ×ˢ S) fun p _ => G.gradSq_nonneg f p
  linarith

lemma energyOn_neg (S : Finset V) (f : V → ℝ) : G.energyOn S (-f) = G.energyOn S f := by
  unfold energyOn
  simp_rw [G.gradSq_neg f]

/-- The subgraph energy is the energy of the induced conductance graph (p. 16). -/
lemma Energy_induce (S : Finset V) (f : V → ℝ) :
    (G.induce ↑S).Energy (f ∘ Subtype.val) = G.energyOn S f := by
  unfold Energy energyOn
  congr 1
  rw [tsum_fintype, Fintype.sum_prod_type, Finset.sum_product,
    ← Finset.sum_finset_coe (fun x => ∑ y ∈ S, G.gradSq f (x, y)) S]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Finset.sum_finset_coe (fun y => G.gradSq f (↑x, y)) S]
  rfl

/-- The `G_S`-Laplacian of `f` at `x`: `∑_{y ∈ S} c(x,y)(f y − f x)`, summing only over
neighbours inside `S`.  This is the quantity in footnote 4 of Gwynne–Sung (p. 16); at a vertex
of `S` with neighbours outside `S` it differs from the `G`-Laplacian. -/
noncomputable def lapWithin (S : Finset V) (f : V → ℝ) (x : V) : ℝ := ∑ y ∈ S, G.lapTerm f x y

/-- `f` is `G_S`-discrete harmonic at `x` (Gwynne–Sung, Proposition 2.5 and footnote 4, p. 16):
the `G_S`-Laplacian vanishes.  The sum is finite, so no summability clause is needed. -/
def IsHarmonicWithinAt (S : Finset V) (f : V → ℝ) (x : V) : Prop := G.lapWithin S f x = 0

/-- `G_S`-harmonicity of `f` at `x ∈ S` is exactly harmonicity of `f|_S` in the induced
conductance graph `G.induce ↑S` (Definition 1.2 applied to the finite graph `G_S`). -/
lemma isHarmonicAt_induce_iff (S : Finset V) (f : V → ℝ) {x : V} (hx : x ∈ S) :
    (G.induce ↑S).IsHarmonicAt (f ∘ Subtype.val) ⟨x, Finset.mem_coe.2 hx⟩ ↔
      G.IsHarmonicWithinAt S f x := by
  have h : (∑' y : ↥(↑S : Set V),
      (G.induce ↑S).lapTerm (f ∘ Subtype.val) ⟨x, Finset.mem_coe.2 hx⟩ y) = G.lapWithin S f x := by
    rw [tsum_fintype]
    exact Finset.sum_finset_coe (fun y => G.lapTerm f x y) S
  unfold IsHarmonicAt IsHarmonicWithinAt
  rw [h]
  exact ⟨fun h' => h'.2, fun h' => ⟨Summable.of_finite, h'⟩⟩

/-! ### The Pythagoras identity on a finite subgraph

On the finite graph `G_S`, a function `h` that is `G_S`-harmonic off `A` is orthogonal (for the
`G_S`-Dirichlet form) to every `g` vanishing on `A`: `Energy_{G_S}(h + g) = Energy_{G_S}(h) +
Energy_{G_S}(g)`.  This is the finite-graph form of the projection argument of Section 2.1, and
it is what makes `hₙ^φ` the energy minimizer on `Gₙ` ("since `hₙ^φ` minimizes Dirichlet energy on
`Gₙ` among all functions on `V Gₙ` which agree with `φ` on `A`", p. 16). -/

/-- The cross term of the `G_S`-energy of `h + g` vanishes when `h` is `G_S`-harmonic off `A`
and `g` vanishes on `A` (summation by parts on the finite graph `G_S`). -/
lemma sum_cross_eq_zero {S A : Finset V} {h g : V → ℝ}
    (hh : ∀ x ∈ S, x ∉ A → G.IsHarmonicWithinAt S h x) (hg : ∀ a ∈ A, g a = 0) :
    ∑ p ∈ S ×ˢ S, G.c p.1 p.2 * (h p.2 - h p.1) * (g p.2 - g p.1) = 0 := by
  have hT : ∑ x ∈ S, ∑ y ∈ S, G.c x y * (h y - h x) * g x = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    have : ∑ y ∈ S, G.c x y * (h y - h x) * g x = g x * G.lapWithin S h x := by
      unfold lapWithin lapTerm
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    rw [this]
    by_cases hxA : x ∈ A
    · rw [hg x hxA, zero_mul]
    · rw [(hh x hx hxA : G.lapWithin S h x = 0), mul_zero]
  have hswap : ∑ x ∈ S, ∑ y ∈ S, G.c x y * (h y - h x) * g y =
      -∑ x ∈ S, ∑ y ∈ S, G.c x y * (h y - h x) * g x := by
    conv_lhs => rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [G.c_symm]; ring
  rw [Finset.sum_product]
  have hsplit : ∀ x y, G.c x y * (h y - h x) * (g y - g x) =
      G.c x y * (h y - h x) * g y - G.c x y * (h y - h x) * g x := fun x y => by ring
  simp_rw [hsplit, Finset.sum_sub_distrib]
  rw [hswap, hT]
  ring

/-- **Pythagoras on `G_S`**: `Energy_{G_S}(h + g) = Energy_{G_S}(h) + Energy_{G_S}(g)` when `h` is
`G_S`-discrete harmonic at every vertex of `S ∖ A` and `g` vanishes on `A`. -/
lemma energyOn_add_of_isHarmonicWithin {S A : Finset V} {h g : V → ℝ}
    (hh : ∀ x ∈ S, x ∉ A → G.IsHarmonicWithinAt S h x) (hg : ∀ a ∈ A, g a = 0) :
    G.energyOn S (h + g) = G.energyOn S h + G.energyOn S g := by
  have hcross := G.sum_cross_eq_zero hh hg
  unfold energyOn
  have hpt : ∀ p : V × V, G.gradSq (h + g) p =
      G.gradSq h p + G.gradSq g p + 2 * (G.c p.1 p.2 * (h p.2 - h p.1) * (g p.2 - g p.1)) :=
    fun p => by simp only [gradSq, Pi.add_apply]; ring
  simp_rw [hpt]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hcross]
  ring

/-- **Minimality on `G_S`** (p. 16): a function `G_S`-harmonic off `A` has the least `G_S`-energy
among functions with the same values on `A`. -/
lemma energyOn_le_of_isHarmonicWithin {S A : Finset V} {h : V → ℝ}
    (hh : ∀ x ∈ S, x ∉ A → G.IsHarmonicWithinAt S h x) {f : V → ℝ} (hf : ∀ a ∈ A, f a = h a) :
    G.energyOn S h ≤ G.energyOn S f := by
  have hsum := G.energyOn_add_of_isHarmonicWithin hh (g := f - h)
    fun a ha => by simp [hf a ha]
  have hfh : h + (f - h) = f := by ext v; simp
  rw [hfh] at hsum
  rw [hsum]
  linarith [G.energyOn_nonneg S (f - h)]

/-- The walk estimate of `Energy.lean` inside a connected finite subgraph: for `a, x ∈ S` there is
a constant `C` (depending on a walk from `a` to `x` in `G_S`) with
`|f x − f a| ≤ C √(2 Energy_{G_S}(f))` for every `f` (Lemma 2.1's path argument on `G_S`). -/
lemma exists_bound_of_induce_connected {S : Finset V}
    (hS : (G.toSimpleGraph.induce ↑S).Connected) {a x : V} (ha : a ∈ S) (hx : x ∈ S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : V → ℝ, |f x - f a| ≤ C * Real.sqrt (2 * G.energyOn S f) := by
  obtain ⟨w⟩ := (G.induce_connected hS).preconnected ⟨a, Finset.mem_coe.2 ha⟩
    ⟨x, Finset.mem_coe.2 hx⟩
  refine ⟨(G.induce ↑S).walkConst w, (G.induce ↑S).walkConst_nonneg w, fun f => ?_⟩
  have := (G.induce ↑S).abs_sub_le_walkConst_mul (f := f ∘ Subtype.val) Summable.of_finite w
  rwa [G.Energy_induce] at this

/-- **Uniqueness on a finite connected subgraph** (the "unique function" of Proposition 2.5,
p. 16): two functions that are `G_S`-harmonic on `S ∖ A` and agree on the non-empty set
`A ⊆ S` agree on `S`.  Their difference has zero `G_S`-energy by the Pythagoras identity, hence
is constant on the connected graph `G_S`, hence zero. -/
lemma eqOn_of_isHarmonicWithin {S A : Finset V} (hS : (G.toSimpleGraph.induce ↑S).Connected)
    (hA : A.Nonempty) (hAS : A ⊆ S) {h h' : V → ℝ}
    (hh : ∀ x ∈ S, x ∉ A → G.IsHarmonicWithinAt S h x)
    (hh' : ∀ x ∈ S, x ∉ A → G.IsHarmonicWithinAt S h' x)
    (heq : ∀ a ∈ A, h a = h' a) : Set.EqOn h h' ↑S := by
  have h1 : G.energyOn S (h' - h) = 0 := by
    have e1 := G.energyOn_add_of_isHarmonicWithin hh (g := h' - h)
      fun a ha => by simp [heq a ha]
    have e2 := G.energyOn_add_of_isHarmonicWithin hh' (g := h - h')
      fun a ha => by simp [heq a ha]
    have f1 : h + (h' - h) = h' := by ext v; simp
    have f2 : h' + (h - h') = h := by ext v; simp
    rw [f1] at e1
    rw [f2] at e2
    have e3 : G.energyOn S (h - h') = G.energyOn S (h' - h) := by
      have : h - h' = -(h' - h) := (neg_sub h' h).symm
      rw [this, G.energyOn_neg]
    linarith
  obtain ⟨a, ha⟩ := hA
  intro x hx
  obtain ⟨C, -, hC⟩ := G.exists_bound_of_induce_connected hS (hAS ha) (Finset.mem_coe.1 hx)
  have hb := hC (h' - h)
  rw [h1, mul_zero, Real.sqrt_zero, mul_zero] at hb
  have h0 : (h' - h) a = 0 := by simp [heq a ha]
  rw [h0, sub_zero, Pi.sub_apply] at hb
  exact (sub_eq_zero.1 (abs_nonpos_iff.1 hb)).symm

/-! ### The `Gₙ`-harmonic extension `hₙ^φ` (Proposition 2.5, p. 16) -/

/-- The finite set `A ∩ S`, viewed inside the vertex type of the subgraph induced on `S`. -/
noncomputable def subtypeOn (S A : Finset V) : Finset ↥(↑S : Set V) :=
  A.subtype fun v => v ∈ (↑S : Set V)

lemma mem_subtypeOn {S A : Finset V} {v : ↥(↑S : Set V)} :
    v ∈ subtypeOn S A ↔ (v : V) ∈ A := Finset.mem_subtype

lemma subtypeOn_nonempty {S A : Finset V} (hA : A.Nonempty) (hAS : A ⊆ S) :
    (subtypeOn S A).Nonempty :=
  let ⟨a, ha⟩ := hA; ⟨⟨a, Finset.mem_coe.2 (hAS ha)⟩, mem_subtypeOn.2 ha⟩

/-- **The function `hₙ^φ` of Proposition 2.5** (p. 16) for the finite connected subgraph
`G_S`: the function on `V G_S = S` which agrees with `φ` on `A` and is `G_S`-discrete harmonic on
`S ∖ A`.  It is constructed as the energy minimizer of Proposition 1.3 applied to the finite
conductance graph `G.induce ↑S`; existence of the harmonic extension is
`harmonicExt_isHarmonicWithin` and its uniqueness is `harmonicExt_unique`.  Outside `S` the
value is the junk value `0`; no statement depends on it. -/
noncomputable def harmonicExt (S : Finset V) (hS : (G.toSimpleGraph.induce ↑S).Connected)
    (A : Finset V) (φ : V → ℝ) : V → ℝ :=
  fun x => if hx : x ∈ S then
    (G.induce ↑S).energyMin (G.induce_connected hS) (subtypeOn S A) (φ ∘ Subtype.val)
      ⟨x, Finset.mem_coe.2 hx⟩
  else 0

/-- On `S`, `hₙ^φ` is the Proposition 1.3 minimizer of the induced graph. -/
lemma harmonicExt_comp_val (S : Finset V) (hS : (G.toSimpleGraph.induce ↑S).Connected)
    (A : Finset V) (φ : V → ℝ) :
    G.harmonicExt S hS A φ ∘ Subtype.val =
      (G.induce ↑S).energyMin (G.induce_connected hS) (subtypeOn S A) (φ ∘ Subtype.val) := by
  funext y
  simp only [Function.comp_apply, harmonicExt, dite_eq_left (Finset.mem_coe.1 y.2)]

/-- Proposition 2.5 (p. 16): `hₙ^φ` agrees with `φ` on `A` (for `A ⊆ V Gₙ`). -/
lemma harmonicExt_eqOn (S : Finset V) (hS : (G.toSimpleGraph.induce ↑S).Connected)
    {A : Finset V} (hA : A.Nonempty) (hAS : A ⊆ S) (φ : V → ℝ) :
    Set.EqOn (G.harmonicExt S hS A φ) φ ↑A := by
  intro a ha
  have ha' : a ∈ A := Finset.mem_coe.1 ha
  have h1 := congrFun (G.harmonicExt_comp_val S hS A φ) ⟨a, Finset.mem_coe.2 (hAS ha')⟩
  have hmem : (⟨a, Finset.mem_coe.2 (hAS ha')⟩ : ↥(↑S : Set V)) ∈
      (↑(subtypeOn S A) : Set ↥(↑S : Set V)) :=
    Finset.mem_coe.2 (mem_subtypeOn.2 ha')
  have h2 := (G.induce ↑S).energyMin_eqOn (G.induce_connected hS) (subtypeOn_nonempty hA hAS)
    (φ ∘ Subtype.val) hmem
  exact h1.trans h2

/-- Proposition 2.5 (p. 16): `hₙ^φ` is `Gₙ`-discrete harmonic on `V Gₙ ∖ A` (existence of the
harmonic extension, from the harmonicity clause of Proposition 1.3 on the finite graph `Gₙ`). -/
lemma harmonicExt_isHarmonicWithin (S : Finset V) (hS : (G.toSimpleGraph.induce ↑S).Connected)
    {A : Finset V} (hA : A.Nonempty) (hAS : A ⊆ S) (φ : V → ℝ) :
    ∀ x ∈ S, x ∉ A → G.IsHarmonicWithinAt S (G.harmonicExt S hS A φ) x := by
  intro x hx hxA
  have hmem : (⟨x, Finset.mem_coe.2 hx⟩ : ↥(↑S : Set V)) ∈
      (↑(subtypeOn S A) : Set ↥(↑S : Set V))ᶜ :=
    fun h => hxA (mem_subtypeOn.1 (Finset.mem_coe.1 h))
  have h := (G.induce ↑S).energyMin_isHarmonicOn (G.induce_connected hS)
    (subtypeOn_nonempty hA hAS) (φ ∘ Subtype.val) _ hmem
  rw [← G.harmonicExt_comp_val S hS A φ] at h
  exact (G.isHarmonicAt_induce_iff S _ hx).1 h

/-- Proposition 2.5 (p. 16): `hₙ^φ` is **the unique** function on `V Gₙ` agreeing with `φ` on `A`
and `Gₙ`-discrete harmonic on `V Gₙ ∖ A`. -/
lemma harmonicExt_unique (S : Finset V) (hS : (G.toSimpleGraph.induce ↑S).Connected)
    {A : Finset V} (hA : A.Nonempty) (hAS : A ⊆ S) (φ : V → ℝ) {f : V → ℝ}
    (hf : Set.EqOn f φ ↑A) (hharm : ∀ x ∈ S, x ∉ A → G.IsHarmonicWithinAt S f x) :
    Set.EqOn f (G.harmonicExt S hS A φ) ↑S :=
  G.eqOn_of_isHarmonicWithin hS hA hAS hharm (G.harmonicExt_isHarmonicWithin S hS hA hAS φ)
    fun a ha => by
      rw [hf (Finset.mem_coe.2 ha), G.harmonicExt_eqOn S hS hA hAS φ (Finset.mem_coe.2 ha)]

/-! ### Exhaustions (Proposition 2.5 and Section 3, p. 16–17) -/

/-- **An increasing family `{Gₙ}_{n ≥ 1}` of finite, connected subgraphs of `G` whose union is
all of `G`** (Gwynne–Sung, Proposition 2.5 p. 16 and Section 3.1 p. 17), indexed by `ℕ`.

`Gₙ` is the subgraph of `G` induced on the finite vertex set `Gsub n`, with the conductances of
`G` (p. 12); as a conductance graph it is `G.induce ↑(Gsub n)`.  The fields are:

* `mono`: `V Gₙ ⊆ V G_m` for `n ≤ m` (the family is increasing);
* `connected`: each `Gₙ` is connected, as a simple graph;
* `exists_mem`: every vertex of `G` lies in some `Gₙ` (the union is all of `G`; since the
  `Gₙ` are induced subgraphs this also exhausts the edges).

`V` is then a countable union of finite sets, so countability of `V` (p. 2) is automatic. -/
structure Exhaustion (G : ConductanceGraph V) where
  /-- The vertex set `V Gₙ` of the `n`-th subgraph. -/
  Gsub : ℕ → Finset V
  /-- The family is increasing: `V Gₙ ⊆ V G_m` for `n ≤ m`. -/
  mono : Monotone Gsub
  /-- Each `Gₙ` (the subgraph induced on `V Gₙ`) is connected. -/
  connected : ∀ n, (G.toSimpleGraph.induce ↑(Gsub n)).Connected
  /-- The union of the `Gₙ` is all of `G`. -/
  exists_mem : ∀ x, ∃ n, x ∈ Gsub n

namespace Exhaustion

variable {G} (E : G.Exhaustion)

lemma subset_of_le {n m : ℕ} (h : n ≤ m) : E.Gsub n ⊆ E.Gsub m := E.mono h

/-- Each `V Gₙ` is non-empty (a connected graph has a vertex). -/
lemma nonempty (n : ℕ) : (E.Gsub n).Nonempty :=
  let ⟨⟨x, hx⟩⟩ := (E.connected n).nonempty; ⟨x, Finset.mem_coe.1 hx⟩

/-- `V` is a countable union of finite sets, hence countable: the standing assumption of
Section 1.1 (p. 2) that `G` is countable is automatic in the presence of an exhaustion. -/
lemma countable (E : G.Exhaustion) : Countable V := by
  have huniv : (Set.univ : Set V) = ⋃ n, (↑(E.Gsub n) : Set V) := by
    ext x
    simp only [Set.mem_univ, Set.mem_iUnion, Finset.mem_coe, true_iff]
    exact E.exists_mem x
  rw [← Set.countable_univ_iff, huniv]
  exact Set.countable_iUnion fun n => (E.Gsub n).countable_toSet

/-- Every finite set of vertices is eventually contained in `V Gₙ` (used to reduce to the
paper's hypothesis `A ⊆ V Gₙ` for every `n`, e.g. via `shift`). -/
lemma exists_subset (A : Finset V) : ∃ N, ∀ n, N ≤ n → A ⊆ E.Gsub n := by
  choose N hN using E.exists_mem
  exact ⟨A.sup N, fun n hn a ha => E.subset_of_le ((Finset.le_sup ha).trans hn) (hN a)⟩

/-- Every finite set of ordered pairs is contained in `V G_k × V G_k` for some `k`: the
"sending `k → ∞`" step of Proposition 2.5 (p. 16). -/
lemma exists_subset_product (T : Finset (V × V)) : ∃ k, T ⊆ E.Gsub k ×ˢ E.Gsub k := by
  choose N hN using E.exists_mem
  refine ⟨T.sup fun p => max (N p.1) (N p.2), fun p hp => ?_⟩
  have hle : max (N p.1) (N p.2) ≤ T.sup fun p => max (N p.1) (N p.2) :=
    Finset.le_sup (f := fun p => max (N p.1) (N p.2)) hp
  rw [Finset.mem_product]
  exact ⟨E.subset_of_le ((le_max_left _ _).trans hle) (hN p.1),
    E.subset_of_le ((le_max_right _ _).trans hle) (hN p.2)⟩

/-- The exhaustion `{G_{n+N}}_n`: dropping the first `N` subgraphs.  Combined with
`exists_subset` it produces an exhaustion satisfying the paper's hypothesis `A ⊆ V Gₙ` for
every `n`. -/
def shift (N : ℕ) : G.Exhaustion where
  Gsub n := E.Gsub (n + N)
  mono _ _ h := E.mono (Nat.add_le_add_right h N)
  connected n := E.connected (n + N)
  exists_mem x := let ⟨n, hn⟩ := E.exists_mem x; ⟨n, E.subset_of_le (Nat.le_add_right n N) hn⟩

@[simp] lemma shift_Gsub (N n : ℕ) : (E.shift N).Gsub n = E.Gsub (n + N) := rfl

/-- The function `hₙ^φ : V Gₙ → ℝ` of Proposition 2.5 (p. 16) for the `n`-th subgraph of the
exhaustion (junk `0` outside `V Gₙ`). -/
noncomputable def harmonicExt (n : ℕ) (A : Finset V) (φ : V → ℝ) : V → ℝ :=
  G.harmonicExt (E.Gsub n) (E.connected n) A φ

end Exhaustion

/-! ### Proposition 2.5 -/

/-- In the proof of Proposition 2.5 (p. 16): the finite energies `Energy_{Gₙ}(hₙ)` are
non-decreasing in `n`, since `hₙ` minimizes `Energy_{Gₙ}` among functions agreeing with `φ` on `A`
and `Energy_{Gₙ} ≤ Energy_{G_m}` for `n ≤ m`. -/
lemma energyOn_harmonic_mono (E : G.Exhaustion) {A : Finset V} (φ : V → ℝ) (hn : ℕ → V → ℝ)
    (hn_eqOn : ∀ n, Set.EqOn (hn n) φ ↑A)
    (hn_harm : ∀ n, ∀ x ∈ E.Gsub n, x ∉ A → G.IsHarmonicWithinAt (E.Gsub n) (hn n) x) :
    Monotone fun n => G.energyOn (E.Gsub n) (hn n) := by
  intro n m hnm
  calc G.energyOn (E.Gsub n) (hn n) ≤ G.energyOn (E.Gsub n) (hn m) :=
        G.energyOn_le_of_isHarmonicWithin (hn_harm n) fun a ha => by
          rw [hn_eqOn m (Finset.mem_coe.2 ha), hn_eqOn n (Finset.mem_coe.2 ha)]
    _ ≤ G.energyOn (E.Gsub m) (hn m) := G.energyOn_mono (E.subset_of_le hnm) _

/-- In the proof of Proposition 2.5 (p. 16):
`Energy_{Gₙ}(hₙ) ≤ Energy_{Gₙ}(h_φ|_{V Gₙ}) ≤ Energy_G(h_φ)`. -/
lemma energyOn_harmonic_le_Energy (hG : G.toSimpleGraph.Connected) (E : G.Exhaustion)
    {A : Finset V} (hA : A.Nonempty) (φ : V → ℝ) (hn : ℕ → V → ℝ)
    (hn_eqOn : ∀ n, Set.EqOn (hn n) φ ↑A)
    (hn_harm : ∀ n, ∀ x ∈ E.Gsub n, x ∉ A → G.IsHarmonicWithinAt (E.Gsub n) (hn n) x) (n : ℕ) :
    G.energyOn (E.Gsub n) (hn n) ≤ G.Energy (G.energyMin hG A φ) :=
  (G.energyOn_le_of_isHarmonicWithin (hn_harm n) fun a ha => by
      rw [G.energyMin_eqOn hG hA φ (Finset.mem_coe.2 ha), hn_eqOn n (Finset.mem_coe.2 ha)]).trans
    (G.energyOn_le_Energy (G.energyMin_hasFiniteEnergy hG hA φ) _)

/-- The monotone convergence step of Proposition 2.5 (p. 16): if `Energy_{G_k}(f) ≤ C` for
every `k`, then `Energy_G(f) ≤ C` (in particular `f` has finite energy), because every finite
partial sum of the energy of `f` is a partial sum over some `V G_k × V G_k`. -/
lemma hasFiniteEnergy_and_Energy_le_of_energyOn_le (E : G.Exhaustion) {f : V → ℝ} {C : ℝ}
    (hC : ∀ k, G.energyOn (E.Gsub k) f ≤ C) : G.HasFiniteEnergy f ∧ G.Energy f ≤ C := by
  have hpartial : ∀ T : Finset (V × V), ∑ p ∈ T, G.gradSq f p ≤ 2 * C := by
    intro T
    obtain ⟨k, hk⟩ := E.exists_subset_product T
    calc ∑ p ∈ T, G.gradSq f p ≤ ∑ p ∈ E.Gsub k ×ˢ E.Gsub k, G.gradSq f p :=
          Finset.sum_le_sum_of_subset_of_nonneg hk fun p _ _ => G.gradSq_nonneg f p
      _ = 2 * G.energyOn (E.Gsub k) f := by unfold energyOn; ring
      _ ≤ 2 * C := by linarith [hC k]
  refine ⟨summable_of_sum_le (fun p => G.gradSq_nonneg f p) hpartial, ?_⟩
  unfold Energy
  linarith [Real.tsum_le_of_sum_le (fun p => G.gradSq_nonneg f p) hpartial]

/-- The `G_S`-energy is continuous under pointwise convergence (it is a finite sum): the
"sending `n → ∞`" step of Proposition 2.5 (p. 16). -/
lemma tendsto_energyOn_of_tendsto (S : Finset V) {u : ℕ → V → ℝ} {f : V → ℝ}
    (hu : ∀ y, Tendsto (fun n => u n y) atTop (𝓝 (f y))) :
    Tendsto (fun n => G.energyOn S (u n)) atTop (𝓝 (G.energyOn S f)) := by
  unfold energyOn
  refine Tendsto.div_const ?_ 2
  refine tendsto_finsetSum _ fun p _ => ?_
  simp only [gradSq]
  exact (((hu p.2).sub (hu p.1)).pow 2).const_mul _

/-- **Proposition 2.5** (Gwynne–Sung, Section 2.3, p. 16), for an arbitrary choice of the
functions `hₙ`.  Let `G` be connected, `A` non-empty and finite, `φ : V → ℝ` (only `φ|_A`
matters), and `{Gₙ}` an exhaustion of `G` by finite connected subgraphs.  If `hₙ : V → ℝ` agrees
with `φ` on `A` and is `Gₙ`-discrete harmonic at every vertex of `V Gₙ ∖ A` (footnote 4: this
is harmonicity in `Gₙ`, not in `G`), then `hₙ(x) → h_φ(x)` for every `x ∈ V`, where `h_φ` is the
energy-minimizing extension of Proposition 1.3.

The values of `hₙ` outside `V Gₙ` are never used (the hypotheses only constrain `hₙ` on
`V Gₙ ∪ A`, and `x ∈ V Gₙ` for all large `n`), so this is the paper's statement about functions
`hₙ : V Gₙ → ℝ`.  The paper's hypothesis `A ⊆ V Gₙ` for every `n` is not needed; it is used
only to make sense of `hₙ` as the harmonic extension of `φ|_A`, see `tendsto_harmonicExt`.

The proof is the compactness-free version of the paper's argument described in the module
docstring. -/
theorem tendsto_of_isHarmonicWithin (hG : G.toSimpleGraph.Connected) (E : G.Exhaustion)
    {A : Finset V} (hA : A.Nonempty) (φ : V → ℝ) (hn : ℕ → V → ℝ)
    (hn_eqOn : ∀ n, Set.EqOn (hn n) φ ↑A)
    (hn_harm : ∀ n, ∀ x ∈ E.Gsub n, x ∉ A → G.IsHarmonicWithinAt (E.Gsub n) (hn n) x)
    (x : V) : Tendsto (fun n => hn n x) atTop (𝓝 (G.energyMin hG A φ x)) := by
  obtain ⟨e, he⟩ : ∃ e : ℕ → ℝ, ∀ n, e n = G.energyOn (E.Gsub n) (hn n) := ⟨_, fun _ => rfl⟩
  have he_mono : Monotone e := fun n m hnm => by
    rw [he, he]; exact G.energyOn_harmonic_mono E φ hn hn_eqOn hn_harm hnm
  have he_le : ∀ n, e n ≤ G.Energy (G.energyMin hG A φ) := fun n => by
    rw [he]; exact G.energyOn_harmonic_le_Energy hG E hA φ hn hn_eqOn hn_harm n
  have hbdd : BddAbove (Set.range e) :=
    ⟨G.Energy (G.energyMin hG A φ), by rintro _ ⟨n, rfl⟩; exact he_le n⟩
  have he_tend : Tendsto e atTop (𝓝 (⨆ n, e n)) := tendsto_atTop_ciSup he_mono hbdd
  have he_le_sup : ∀ n, e n ≤ ⨆ n, e n := fun n => le_ciSup hbdd n
  have hsup_le : (⨆ n, e n) ≤ G.Energy (G.energyMin hG A φ) := ciSup_le he_le
  -- The Cauchy estimate `Energy_{G_k}(h_m − hₙ) ≤ e_m − eₙ` for `k ≤ n ≤ m`.
  have hcauchy : ∀ k n m, k ≤ n → n ≤ m →
      G.energyOn (E.Gsub k) (hn m - hn n) ≤ e m - e n := by
    intro k n m hkn hnm
    have h1 := G.energyOn_add_of_isHarmonicWithin (hn_harm n) (g := hn m - hn n)
      fun a ha => by simp [hn_eqOn m (Finset.mem_coe.2 ha), hn_eqOn n (Finset.mem_coe.2 ha)]
    have hfh : hn n + (hn m - hn n) = hn m := by ext v; simp
    rw [hfh] at h1
    have h2 : G.energyOn (E.Gsub n) (hn m) ≤ e m := by
      rw [he]; exact G.energyOn_mono (E.subset_of_le hnm) _
    have h3 := G.energyOn_mono (E.subset_of_le hkn) (hn m - hn n)
    rw [he n]
    linarith
  -- Pointwise convergence at every vertex, via the walk estimate in a `G_k` containing `y`
  -- and a point of `A`.
  have hlim : ∀ y : V, ∃ L : ℝ, Tendsto (fun n => hn n y) atTop (𝓝 L) := by
    intro y
    obtain ⟨a, ha⟩ := hA
    obtain ⟨k₁, hk₁⟩ := E.exists_mem y
    obtain ⟨k₂, hk₂⟩ := E.exists_mem a
    have hyk : y ∈ E.Gsub (max k₁ k₂) := E.subset_of_le (le_max_left _ _) hk₁
    have hak : a ∈ E.Gsub (max k₁ k₂) := E.subset_of_le (le_max_right _ _) hk₂
    obtain ⟨C, hC0, hC⟩ := G.exists_bound_of_induce_connected (E.connected _) hak hyk
    set k := max k₁ k₂ with hk
    have hcs : CauchySeq fun n => hn (n + k) y := by
      refine cauchySeq_of_le_tendsto_0 (fun N => C * Real.sqrt (2 * ((⨆ n, e n) - e (N + k))))
        ?_ ?_
      · have key : ∀ n m N, N ≤ n → n ≤ m → dist (hn (n + k) y) (hn (m + k) y) ≤
            C * Real.sqrt (2 * ((⨆ n, e n) - e (N + k))) := by
          intro n m N hNn hnm
          rw [Real.dist_eq]
          have hzero : (hn (m + k) - hn (n + k)) a = 0 := by
            simp [hn_eqOn (m + k) (Finset.mem_coe.2 ha), hn_eqOn (n + k) (Finset.mem_coe.2 ha)]
          have h1 := hC (hn (m + k) - hn (n + k))
          rw [hzero, sub_zero, Pi.sub_apply] at h1
          rw [abs_sub_comm]
          refine h1.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hC0)
          have h2 := hcauchy k (n + k) (m + k) (Nat.le_add_left k n) (Nat.add_le_add_right hnm k)
          have h3 := he_le_sup (m + k)
          have h4 := he_mono (Nat.add_le_add_right hNn k)
          linarith
        intro n m N hNn hNm
        rcases le_total n m with hnm | hmn
        · exact key n m N hNn hnm
        · rw [dist_comm]; exact key m n N hNm hmn
      · have h1 : Tendsto (fun N => e (N + k)) atTop (𝓝 (⨆ n, e n)) :=
          he_tend.comp (tendsto_add_atTop_nat k)
        have h2 : Tendsto (fun N => C * Real.sqrt (2 * ((⨆ n, e n) - e (N + k)))) atTop
            (𝓝 (C * Real.sqrt (2 * ((⨆ n, e n) - ⨆ n, e n)))) :=
          ((tendsto_const_nhds.sub h1).const_mul 2).sqrt.const_mul C
        simpa using h2
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcs
    exact ⟨L, (tendsto_add_atTop_iff_nat k).1 hL⟩
  choose L hL using hlim
  -- The limit agrees with `φ` on `A`.
  have hLA : Set.EqOn L φ ↑A := by
    intro a ha
    refine tendsto_nhds_unique (hL a) ?_
    have : (fun n => hn n a) = fun _ => φ a := funext fun n => hn_eqOn n ha
    rw [this]; exact tendsto_const_nhds
  -- `Energy_{G_k}(L) ≤ sup eₙ` for every `k`, by sending `n → ∞` in `Energy_{G_k}(hₙ) ≤ eₙ`.
  have hLk : ∀ k, G.energyOn (E.Gsub k) L ≤ ⨆ n, e n := by
    intro k
    refine le_of_tendsto (G.tendsto_energyOn_of_tendsto (E.Gsub k) hL)
      (eventually_atTop.2 ⟨k, fun n hkn => ?_⟩)
    calc G.energyOn (E.Gsub k) (hn n) ≤ G.energyOn (E.Gsub n) (hn n) :=
          G.energyOn_mono (E.subset_of_le hkn) _
      _ = e n := (he n).symm
      _ ≤ ⨆ n, e n := he_le_sup n
  -- Monotone convergence: `L` has finite energy and `Energy_G(L) ≤ sup eₙ ≤ Energy_G(h_φ)`.
  obtain ⟨hLfin, hLE⟩ := G.hasFiniteEnergy_and_Energy_le_of_energyOn_le E hLk
  -- Uniqueness in Proposition 1.3: `L = h_φ`.
  have hLh : L = G.energyMin hG A φ :=
    G.energyMin_unique hG hA φ hLfin hLA fun g hg hgA =>
      hLE.trans (hsup_le.trans (G.energyMin_le_energy hG hA φ hg hgA))
  rw [← hLh]
  exact hL x

/-- **Proposition 2.5** (Gwynne–Sung, Section 2.3, p. 16), verbatim: with `{Gₙ}` an exhaustion of
the connected graph `G` by finite connected subgraphs such that `A ⊆ V Gₙ` for every `n`, and
`hₙ^φ` (`Exhaustion.harmonicExt`) the unique function on `V Gₙ` which agrees with `φ` on `A` and is
`Gₙ`-discrete harmonic on `V Gₙ ∖ A`, one has `lim_{n → ∞} hₙ^φ(x) = h_φ(x)` for each `x ∈ V`. -/
theorem tendsto_harmonicExt (hG : G.toSimpleGraph.Connected) (E : G.Exhaustion)
    {A : Finset V} (hA : A.Nonempty) (hAE : ∀ n, A ⊆ E.Gsub n) (φ : V → ℝ) (x : V) :
    Tendsto (fun n => E.harmonicExt n A φ x) atTop (𝓝 (G.energyMin hG A φ x)) :=
  G.tendsto_of_isHarmonicWithin hG E hA φ (fun n => E.harmonicExt n A φ)
    (fun n => G.harmonicExt_eqOn _ _ hA (hAE n) φ)
    (fun n => G.harmonicExt_isHarmonicWithin _ _ hA (hAE n) φ) x

/-- Proposition 2.5 applied to `φ = 1_y` (Definition 1.5): the harmonic measure on `A` viewed
from `x` computed in the finite subgraph `Gₙ` — the value at `x` of the `Gₙ`-harmonic extension
of `1_y` — converges to the energy-minimizing harmonic measure `hm^x_A(y)` on `G`. -/
theorem tendsto_harmonicExt_indic (hG : G.toSimpleGraph.Connected) (E : G.Exhaustion)
    {A : Finset V} (hA : A.Nonempty) (hAE : ∀ n, A ⊆ E.Gsub n) (x y : V) :
    Tendsto (fun n => E.harmonicExt n A (G.indic y) x) atTop (𝓝 (G.harmonicMeasure hG A x y)) :=
  G.tendsto_harmonicExt hG E hA hAE (G.indic y) x

/-- Convergence of the finite energies: in the setting of `tendsto_of_isHarmonicWithin`,
`Energy_{Gₙ}(hₙ) → Energy_G(h_φ)`.  This is a by-product of the proof of Proposition 2.5 (the
sequence `Energy_{Gₙ}(hₙ)` is non-decreasing and bounded by `Energy_G(h_φ)`, and its limit
dominates `Energy_{G_k}(h_φ)` for every `k`). -/
theorem tendsto_energyOn_of_isHarmonicWithin (hG : G.toSimpleGraph.Connected) (E : G.Exhaustion)
    {A : Finset V} (hA : A.Nonempty) (φ : V → ℝ) (hn : ℕ → V → ℝ)
    (hn_eqOn : ∀ n, Set.EqOn (hn n) φ ↑A)
    (hn_harm : ∀ n, ∀ x ∈ E.Gsub n, x ∉ A → G.IsHarmonicWithinAt (E.Gsub n) (hn n) x) :
    Tendsto (fun n => G.energyOn (E.Gsub n) (hn n)) atTop
      (𝓝 (G.Energy (G.energyMin hG A φ))) := by
  have he_mono := G.energyOn_harmonic_mono E φ hn hn_eqOn hn_harm
  have he_le := G.energyOn_harmonic_le_Energy hG E hA φ hn hn_eqOn hn_harm
  have hbdd : BddAbove (Set.range fun n => G.energyOn (E.Gsub n) (hn n)) :=
    ⟨_, by rintro _ ⟨n, rfl⟩; exact he_le n⟩
  have he_tend := tendsto_atTop_ciSup he_mono hbdd
  suffices hsup : (⨆ n, G.energyOn (E.Gsub n) (hn n)) = G.Energy (G.energyMin hG A φ) by
    rwa [hsup] at he_tend
  refine le_antisymm (ciSup_le he_le) ?_
  refine (G.hasFiniteEnergy_and_Energy_le_of_energyOn_le E fun k => ?_).2
  refine le_of_tendsto (G.tendsto_energyOn_of_tendsto (E.Gsub k)
    (G.tendsto_of_isHarmonicWithin hG E hA φ hn hn_eqOn hn_harm))
    (eventually_atTop.2 ⟨k, fun n hkn => ?_⟩)
  exact (G.energyOn_mono (E.subset_of_le hkn) _).trans (le_ciSup hbdd n)

/-- Convergence of the finite energies for the canonical `hₙ^φ` of Proposition 2.5:
`Energy_{Gₙ}(hₙ^φ) → Energy_G(h_φ)`. -/
theorem tendsto_energyOn_harmonicExt (hG : G.toSimpleGraph.Connected) (E : G.Exhaustion)
    {A : Finset V} (hA : A.Nonempty) (hAE : ∀ n, A ⊆ E.Gsub n) (φ : V → ℝ) :
    Tendsto (fun n => G.energyOn (E.Gsub n) (E.harmonicExt n A φ)) atTop
      (𝓝 (G.Energy (G.energyMin hG A φ))) :=
  G.tendsto_energyOn_of_isHarmonicWithin hG E hA φ (fun n => E.harmonicExt n A φ)
    (fun n => G.harmonicExt_eqOn _ _ hA (hAE n) φ)
    (fun n => G.harmonicExt_isHarmonicWithin _ _ hA (hAE n) φ)

end ConductanceGraph

end ReflectedWalk
