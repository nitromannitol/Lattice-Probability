import LatticeProb.Prob.FiniteConductanceRestriction
import LatticeProb.Bonanno.BouRabeeGwynne.FiniteDirichlet

/-! # Boundary accessibility of finite restrictions -/

set_option autoImplicit false

namespace LatticeProb

/-- If every active vertex has an ambient positive-conductance path to the
exterior, and every neighbor of an active vertex is retained, the restricted
network has accessible boundary. -/
theorem finiteConductanceRestriction_boundaryAccessible_of_ambient_paths
    {V : Type*} (c : V → V → ℝ)
    (hsymm : ∀ v w, c v w = c w v)
    (hnonneg : ∀ v w, 0 ≤ c v w) (hloop : ∀ v, c v v = 0)
    (R : Set V) [Fintype R] (A : Set R) (B : Set V)
    (hAB : ∀ v : R, v ∈ A ↔ (v : V) ∈ B)
    (hretain : ∀ v ∈ A, ∀ w, w ∉ R → c v w = 0)
    (hpaths : ∀ v ∈ A, ∃ w, w ∉ B ∧
      Relation.ReflTransGen (fun x y => 0 < c x y) (v : V) w) :
    (finiteConductanceRestriction c hsymm hnonneg hloop R).BoundaryAccessible A := by
  classical
  intro v hv
  obtain ⟨y, hy, hpath⟩ := hpaths v hv
  have hprefix : ∀ {x : V}, Relation.ReflTransGen (fun x y => 0 < c x y) x y →
      ∀ hx : x ∈ R, ∃ w : R, w ∉ A ∧
        Relation.ReflTransGen (fun a b : R =>
          0 < (finiteConductanceRestriction c hsymm hnonneg hloop R).a a b) ⟨x, hx⟩ w := by
    intro x hp
    induction hp using Relation.ReflTransGen.head_induction_on with
    | refl =>
        intro hx
        exact ⟨⟨y, hx⟩, fun h => hy ((hAB ⟨y, hx⟩).1 h), .refl⟩
    | @head a b hab hby ih =>
        intro ha
        let x : R := ⟨a, ha⟩
        by_cases hx : x ∈ A
        · have hb : b ∈ R := by
            by_contra hb
            have hzero := hretain x hx b hb
            exact (ne_of_gt hab) hzero
          obtain ⟨w, hw, hreach⟩ := ih hb
          have hstep : 0 < (finiteConductanceRestriction c hsymm hnonneg hloop R).a
              x ⟨b, hb⟩ := hab
          exact ⟨w, hw, hreach.head hstep⟩
        · exact ⟨x, hx, .refl⟩
  exact hprefix hpath v.property

end LatticeProb
