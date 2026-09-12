/- Adapted from nitromannitol/rotor-23, Apache-2.0; copyright 2026 Ahmed Bou-Rabee and Yuval Peres. -/
import LatticeProb.Lattice.Planar.Basic
import LatticeProb.Lattice.Planar.Periodic
import LatticeProb.Lattice.Planar.RotorOrder

open Fin.NatCast

namespace LatticeProb.Lattice.Planar

/-- The square lattice as a simple graph on `ℤ × ℤ`: `x ∼ y` when they differ
by a unit step. -/
def squareGraph : SimpleGraph Site where
  Adj := fun x y : Site => |x.1 - y.1| + |x.2 - y.2| = 1
  symm := ⟨fun x y h => by
    show |y.1 - x.1| + |y.2 - x.2| = 1
    rw [abs_sub_comm y.1, abs_sub_comm y.2]; exact h⟩
  loopless := ⟨fun x h => by simp at h⟩

theorem squareGraph_adj (x y : Site) : squareGraph.Adj x y ↔ |x.1 - y.1| + |x.2 - y.2| = 1 :=
  Iff.rfl

instance instDecidableRelSiteAdjSquareGraph : DecidableRel squareGraph.Adj := fun x y => by
  unfold squareGraph; exact inferInstanceAs (Decidable (_ = _))

theorem adj_add_dirVec (v : Site) (a : Dir) : squareGraph.Adj v (v + dirVec a) := by
  rw [squareGraph_adj]
  fin_cases a <;> simp [dirVec]

/-- The direction of a unit step `d`: the inverse of `dirVec` on unit steps. -/
def dirOf (d : Site) : Dir :=
  if d = (0, 1) then 0 else if d = (1, 0) then 1 else if d = (0, -1) then 2 else 3

theorem dirOf_dirVec (a : Dir) : dirOf (dirVec a) = a := by
  fin_cases a <;> simp [dirOf, dirVec]

theorem dirVec_dirOf_of_adj {v w : Site} (h : squareGraph.Adj v w) :
    v + dirVec (dirOf (w - v)) = w := by
  rw [squareGraph_adj] at h
  obtain ⟨a, b⟩ := v
  obtain ⟨c, d⟩ := w
  simp only [Prod.mk_sub_mk, dirOf, dirVec, Prod.mk.injEq] at h ⊢
  rcases abs_cases (a - c) with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
  rcases abs_cases (b - d) with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;>
  · split_ifs <;> simp_all <;> omega

/-- The four neighbors of a lattice site, indexed by direction. -/
def nbr (v : Site) : Dir ≃ squareGraph.neighborSet v where
  toFun a := ⟨v + dirVec a, adj_add_dirVec v a⟩
  invFun w := dirOf (w.1 - v)
  left_inv a := by simp [dirOf_dirVec]
  right_inv w := Subtype.ext (dirVec_dirOf_of_adj w.2)

instance instLocallyFiniteSiteSquareGraph : squareGraph.LocallyFinite := fun v => Fintype.ofEquiv Dir (nbr v)

/-- Turning by one direction, transported to the neighbors of `v`. -/
def turnAt (v : Site) : Equiv.Perm (squareGraph.neighborSet v) :=
  (nbr v).symm.trans ((Equiv.addRight (1 : Dir)).trans (nbr v))

theorem turnAt_nbr (v : Site) (a : Dir) : turnAt v (nbr v a) = nbr v (a + 1) := by
  simp [turnAt]

theorem turnAt_pow_nbr (v : Site) (k : ℕ) (a : Dir) :
    ((turnAt v) ^ k) (nbr v a) = nbr v (a + (k : Dir)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply, ih, turnAt_nbr]
    congr 1
    rw [Nat.cast_succ, add_assoc]

/-- The clockwise rotor mechanism on the square lattice: turn by one direction. -/
def clockwise : Mechanism squareGraph where
  next v := turnAt v
  cyclic v a b := by
    obtain ⟨i, rfl⟩ := (nbr v).surjective a
    obtain ⟨j, rfl⟩ := (nbr v).surjective b
    refine ⟨(j - i).val, ?_⟩
    rw [turnAt_pow_nbr, Fin.cast_val_eq_self]
    congr 1
    exact add_sub_cancel i j
  nonempty v := ⟨nbr v 0⟩

/-- The standard embedding of `ℤ²` in the plane. -/
def squareEmb (v : Site) : Plane := WithLp.toLp 2 ![(v.1 : ℝ), (v.2 : ℝ)]

theorem squareEmb_injective : Function.Injective squareEmb := by
  intro v w h
  have h' : (![(v.1 : ℝ), (v.2 : ℝ)] : Fin 2 → ℝ) = ![(w.1 : ℝ), (w.2 : ℝ)] := by
    have := congrArg WithLp.ofLp h
    simpa [squareEmb] using this
  have h0 := congrFun h' 0
  have h1 := congrFun h' 1
  simp at h0 h1
  exact Prod.ext h0 h1

/-- The square lattice as a doubly periodic graph: the lattice `ℤ²` acts on
itself by translation, with the standard basis. -/
noncomputable def squarePeriodic : DoublyPeriodic squareGraph where
  emb := squareEmb
  emb_injective := squareEmb_injective
  shift z v := v + z
  shift_zero v := by simp
  shift_add z w v := by simp [add_comm, add_left_comm]
  b := fun i => WithLp.toLp 2 (Pi.single i 1)
  b_indep := by
    have hb : (fun i => WithLp.toLp 2 (Pi.single i 1) : Fin 2 → EuclideanSpace ℝ (Fin 2)) =
        ⇑(EuclideanSpace.basisFun (Fin 2) ℝ).toBasis := by
      funext i
      rw [OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply]
      rfl
    rw [hb]
    exact (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.linearIndependent
  emb_shift z v := by
    ext i
    fin_cases i <;> simp [squareEmb]
  adj_shift z u v := by
    simp [squareGraph_adj]
  rep _ := 0
  coord v := v
  shift_coord_rep v := by simp
  rep_shift _ _ := rfl
  finite_orbits := by rw [Set.range_const]; exact Set.finite_singleton _

end LatticeProb.Lattice.Planar
