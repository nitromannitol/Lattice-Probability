import Mathlib.Combinatorics.Graph.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact

/-!
# The mated-CRT graph associated with two continuous paths

These are the literal deterministic formulas in Definition 1.1 of
[Internal DLA on mated-CRT maps](https://arxiv.org/abs/2211.04891v2).
The two possible edge labels retain parallel edges. Brownian laws, planar
embeddings and almost-sure local finiteness are separate probabilistic results.
-/

noncomputable section

namespace LatticeProb.MatedCRT

/-- A continuous real path on all real times whose value at zero is zero. -/
def RootedPath : Type :=
  {X : C(ℝ, ℝ) // X 0 = 0}

/-- The real lattice with spacing `ε`, including its actual integer-coordinate witness. -/
def Vertex (ε : Set.Ioi (0 : ℝ)) : Type :=
  {x : ℝ // ∃ n : ℤ, x = ε.val * (n : ℝ)}

/-- Two vertices in strictly increasing real order. -/
def OrderedPair (ε : Set.Ioi (0 : ℝ)) : Type :=
  {p : Vertex ε × Vertex ε // p.1.val < p.2.val}

/-- The infimum inequality for one coordinate in Definition 1.1 of arXiv:2211.04891v2. -/
def coordinateCondition (ε : Set.Ioi (0 : ℝ))
    (X : RootedPath) (p : OrderedPair ε) : Prop :=
  let a : ℝ := p.val.1.val
  let b : ℝ := p.val.2.val
  max
    (sInf ((X.val : ℝ → ℝ) '' Set.Icc (a - ε.val) a))
    (sInf ((X.val : ℝ → ℝ) '' Set.Icc (b - ε.val) b))
    ≤ sInf ((X.val : ℝ → ℝ) '' Set.Icc a (b - ε.val))

/-- An ordered endpoint pair with one of two distinct possible edge labels. -/
def PotentialEdge (ε : Set.Ioi (0 : ℝ)) : Type :=
  OrderedPair ε × Fin 2

/-- The exact rule for one edge or two nonconsecutive parallel edges. -/
def edgeEnabled (ε : Set.Ioi (0 : ℝ))
    (L R : RootedPath) (e : PotentialEdge ε) : Prop :=
  (e.2 = 0 ∧
    (coordinateCondition ε L e.1 ∨ coordinateCondition ε R e.1)) ∨
  (e.2 = 1 ∧
    ε.val < e.1.val.2.val - e.1.val.1.val ∧
    coordinateCondition ε L e.1 ∧ coordinateCondition ε R e.1)

/-- The uncoloured deterministic multigraph specified by the two coordinate paths. -/
def fromPaths (ε : Set.Ioi (0 : ℝ)) (L R : RootedPath) :
    Graph (Vertex ε) (PotentialEdge ε) where
  vertexSet := Set.univ
  edgeSet := {e | edgeEnabled ε L R e}
  IsLink := fun e a b =>
    edgeEnabled ε L R e ∧
      ((a = e.1.val.1 ∧ b = e.1.val.2) ∨
       (a = e.1.val.2 ∧ b = e.1.val.1))
  isLink_symm := by
    intro e he
    constructor
    intro a b h
    rcases h with ⟨hen, hab | hab⟩
    · exact ⟨hen, Or.inr ⟨hab.2, hab.1⟩⟩
    · exact ⟨hen, Or.inl ⟨hab.2, hab.1⟩⟩
  eq_or_eq_of_isLink_of_isLink := by
    intro e a b v w hab hvw
    rcases hab.2 with hab | hab
    · rcases hvw.2 with hvw | hvw
      · exact Or.inl (hab.1.trans hvw.1.symm)
      · exact Or.inr (hab.1.trans hvw.2.symm)
    · rcases hvw.2 with hvw | hvw
      · exact Or.inr (hab.1.trans hvw.2.symm)
      · exact Or.inl (hab.1.trans hvw.1.symm)
  edge_mem_iff_exists_isLink := by
    intro e
    constructor
    · intro he
      exact ⟨e.1.val.1, e.1.val.2, he, Or.inl ⟨rfl, rfl⟩⟩
    · rintro ⟨a, b, h⟩
      exact h.1
  left_mem_of_isLink := by
    intro e a b h
    exact Set.mem_univ a

/-- The next real lattice vertex, at distance `ε` to the right. -/
def successor (ε : Set.Ioi (0 : ℝ)) (a : Vertex ε) : Vertex ε :=
  ⟨a.val + ε.val, by
    rcases a.property with ⟨n, hn⟩
    exact ⟨n + 1, by
      simpa only [Int.cast_add, Int.cast_one, mul_add, mul_one] using
        congrArg (fun x : ℝ => x + ε.val) hn⟩⟩

end LatticeProb.MatedCRT
