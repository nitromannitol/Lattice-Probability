/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.DGFFPositive at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.DGFFCore

 


set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.QPos

namespace WiredConductances

variable {V : Type*} [Fintype V] [DecidableEq V] (G : WiredConductances V)

 

def ReachesBoundary : Prop :=
  ∀ i : V, ∃ b : V, 0 < G.boundary b ∧
    Relation.ReflTransGen (fun u v : V => 0 < G.edge u v) i b

 

theorem precision_posDef_of_reachesBoundary (hconn : G.ReachesBoundary) :
    G.precision.PosDef := by
  classical
  apply Matrix.PosDef.of_dotProduct_mulVec_pos G.precision_isHermitian
  intro x hx
  change 0 < dotProduct x (Matrix.mulVec G.precision x)
  have hbnonneg : 0 ≤ (∑ i : V, G.boundary i * (x i) ^ 2) := by
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (G.boundary_nonneg i) (sq_nonneg _)
  have henonneg : 0 ≤ (∑ i : V, ∑ j : V,
      G.edge i j * (x i - x j) ^ 2) := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (G.edge_nonneg i j) (sq_nonneg _)
  have hnonneg : 0 ≤ dotProduct x (Matrix.mulVec G.precision x) :=
    G.precision_posSemidef.dotProduct_mulVec_nonneg x
  by_contra hnot
  have hzero : dotProduct x (Matrix.mulVec G.precision x) = 0 := by
    exact le_antisymm (le_of_not_gt hnot) hnonneg
  rw [G.precision_energy] at hzero
  have hbzero : (∑ i : V, G.boundary i * (x i) ^ 2) = 0 := by
    nlinarith only [hzero, hbnonneg, henonneg]
  have hezero : (∑ i : V, ∑ j : V,
      G.edge i j * (x i - x j) ^ 2) = 0 := by
    nlinarith only [hzero, hbnonneg, henonneg]
  have hbpoint (i : V) : G.boundary i * (x i) ^ 2 = 0 := by
    have h := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ (Finset.univ : Finset V)) =>
        mul_nonneg (G.boundary_nonneg j) (sq_nonneg _))).mp hbzero
    exact h i (Finset.mem_univ i)
  have hepoint (i j : V) : G.edge i j * (x i - x j) ^ 2 = 0 := by
    have hrow : (∑ j : V, G.edge i j * (x i - x j) ^ 2) = 0 := by
      have h := (Finset.sum_eq_zero_iff_of_nonneg
        (fun k (_ : k ∈ (Finset.univ : Finset V)) =>
          Finset.sum_nonneg (fun j _ =>
            mul_nonneg (G.edge_nonneg k j) (sq_nonneg _)))).mp hezero
      exact h i (Finset.mem_univ i)
    have h := (Finset.sum_eq_zero_iff_of_nonneg
      (fun k (_ : k ∈ (Finset.univ : Finset V)) =>
        mul_nonneg (G.edge_nonneg i k) (sq_nonneg _))).mp hrow
    exact h j (Finset.mem_univ j)
  have hedge (i j : V) (hij : 0 < G.edge i j) : x i = x j := by
    have h := hepoint i j
    have hsq : (x i - x j) ^ 2 = 0 :=
      (mul_eq_zero.mp h).resolve_left (ne_of_gt hij)
    nlinarith only [hsq]
  have hbound (i : V) (hi : 0 < G.boundary i) : x i = 0 := by
    have h := hbpoint i
    have hsq : (x i) ^ 2 = 0 :=
      (mul_eq_zero.mp h).resolve_left (ne_of_gt hi)
    nlinarith only [hsq]
  have hprop (i b : V)
      (h : Relation.ReflTransGen (fun u v : V => 0 < G.edge u v) i b) :
      x i = x b := by
    induction h using Relation.ReflTransGen.head_induction_on with
    | refl => rfl
    | @head a c hac hcb ih => exact (hedge a c hac).trans ih
  have hxzero : x = 0 := by
    funext i
    obtain ⟨b, hb, hib⟩ := hconn i
    exact (hprop i b hib).trans (hbound b hb)
  exact hx hxzero

end WiredConductances

end SupercriticalLQGUniqueness.B2.QPos
