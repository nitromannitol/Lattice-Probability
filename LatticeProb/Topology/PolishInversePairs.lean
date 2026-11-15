import LatticeProb.Topology.PolishContinuousMap

/-! # Continuous inverse pairs

Mutually inverse continuous self-maps form a closed, hence Polish, subspace
of the product of compact-open function spaces.
-/

set_option autoImplicit false

open Set
open scoped Topology

namespace LatticeProb

variable {X : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [T2Space X]

/-- Pairs of continuous self-maps which are mutually inverse. -/
def inversePairs : Set (C(X, X) × C(X, X)) :=
  {p | (∀ x, p.1 (p.2 x) = x) ∧ ∀ x, p.2 (p.1 x) = x}

/-- Mutual inverse equations define a closed subset in the compact-open topology. -/
theorem isClosed_inversePairs : IsClosed (inversePairs (X := X)) := by
  have hf (x : X) : Continuous (fun p : C(X, X) × C(X, X) => p.1 (p.2 x)) :=
    continuous_eval.comp (continuous_fst.prodMk ((continuous_eval_const x).comp continuous_snd))
  have hg (x : X) : Continuous (fun p : C(X, X) × C(X, X) => p.2 (p.1 x)) :=
    continuous_eval.comp (continuous_snd.prodMk ((continuous_eval_const x).comp continuous_fst))
  change IsClosed ({p : C(X, X) × C(X, X) | ∀ x, p.1 (p.2 x) = x} ∩
    {p | ∀ x, p.2 (p.1 x) = x})
  simpa only [Set.ofPred_forall] using
    (isClosed_iInter fun x => isClosed_eq (hf x) (continuous_const : Continuous fun _ => x)).inter
      (isClosed_iInter fun x => isClosed_eq (hg x) (continuous_const : Continuous fun _ => x))

/-- The inverse-pair carrier is Polish whenever the underlying space is. -/
theorem polishSpace_inversePairs [PolishSpace X] :
    PolishSpace (inversePairs (X := X)) := by
  let := polishSpace_continuousMap X X
  exact isClosed_inversePairs.polishSpace

/-- An inverse pair gives the corresponding homeomorphism. -/
def inversePairHomeomorph (p : inversePairs (X := X)) : X ≃ₜ X where
  toFun := p.1.1
  invFun := p.1.2
  left_inv := p.2.2
  right_inv := p.2.1
  continuous_toFun := p.1.1.continuous
  continuous_invFun := p.1.2.continuous

/-- Every homeomorphism determines an inverse pair. -/
def homeomorphInversePair (f : X ≃ₜ X) : inversePairs (X := X) :=
  ⟨(⟨f, f.continuous⟩, ⟨f.symm, f.symm.continuous⟩), f.right_inv, f.left_inv⟩

end LatticeProb
