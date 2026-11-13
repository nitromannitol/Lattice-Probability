/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.DGFFCore at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import Mathlib

 





set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory

namespace SupercriticalLQGUniqueness.B2.QPos

 

structure WiredConductances (V : Type*) [Fintype V] where
  edge : V → V → ℝ
  boundary : V → ℝ
  edge_symm : ∀ i j, edge i j = edge j i
  edge_self : ∀ i, edge i i = 0
  edge_nonneg : ∀ i j, 0 ≤ edge i j
  boundary_nonneg : ∀ i, 0 ≤ boundary i

namespace WiredConductances

variable {V : Type*} [Fintype V] [DecidableEq V] (G : WiredConductances V)

 
def precision : Matrix V V ℝ := fun i j =>
  if i = j then G.boundary i + ∑ k, G.edge i k else -G.edge i j

theorem precision_isHermitian : G.precision.IsHermitian := by
  classical
  apply Matrix.IsHermitian.ext
  intro i j
  by_cases hij : i = j
  · subst j
    simp [precision]
  · simp [precision, hij, Ne.symm hij, G.edge_symm]

 

theorem precision_mulVec_one (i : V) :
    (Matrix.mulVec G.precision (fun _ => (1 : ℝ))) i = G.boundary i := by
  classical
  simp only [Matrix.mulVec, dotProduct, mul_one, precision]
  rw [← Finset.add_sum_erase Finset.univ
    (fun j : V => if i = j then G.boundary i + ∑ k, G.edge i k else -G.edge i j)
    (Finset.mem_univ i)]
  simp only [↓reduceIte]
  have hsum : (∑ j ∈ Finset.univ.erase i,
      if i = j then G.boundary i + ∑ k, G.edge i k else -G.edge i j) =
      ∑ j ∈ Finset.univ.erase i, -G.edge i j := by
    apply Finset.sum_congr rfl
    intro j hj
    have hji : i ≠ j := (Finset.mem_erase.mp hj).1.symm
    simp [hji]
  rw [hsum]
  rw [Finset.sum_neg_distrib]
  have herase : (∑ j ∈ Finset.univ.erase i, G.edge i j) =
      ∑ j : V, G.edge i j := Finset.sum_erase Finset.univ (G.edge_self i)
  rw [herase]
  ring

 
theorem precision_mulVec (x : V → ℝ) (i : V) :
    (Matrix.mulVec G.precision x) i =
      G.boundary i * x i + ∑ j, G.edge i j * (x i - x j) := by
  classical
  simp only [Matrix.mulVec, dotProduct]
  rw [← Finset.add_sum_erase Finset.univ
    (fun j : V => G.precision i j * x j) (Finset.mem_univ i)]
  have hsum : (∑ j ∈ Finset.univ.erase i, G.precision i j * x j) =
      -∑ j : V, G.edge i j * x j := by
    have hterm : ∀ j ∈ Finset.univ.erase i,
        G.precision i j * x j = -(G.edge i j * x j) := by
      intro j hj
      have hji : i ≠ j := (Finset.mem_erase.mp hj).1.symm
      simp [precision, hji]
    have hzero : G.edge i i * x i = 0 := by simp [G.edge_self]
    calc
      _ = ∑ j ∈ Finset.univ.erase i, -(G.edge i j * x j) :=
        Finset.sum_congr rfl hterm
      _ = -(∑ j ∈ Finset.univ.erase i, G.edge i j * x j) := by
        rw [Finset.sum_neg_distrib]
      _ = -∑ j : V, G.edge i j * x j := by
        rw [Finset.sum_erase (Finset.univ : Finset V)
          (a := i) (f := fun j => G.edge i j * x j) hzero]
  rw [hsum]
  simp only [precision, ↓reduceIte]
  have hright : (∑ j : V, G.edge i j * (x i - x j)) =
      (∑ j : V, G.edge i j) * x i - ∑ j : V, G.edge i j * x j := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [hright]
  ring

 
theorem precision_energy (x : V → ℝ) :
    dotProduct x (Matrix.mulVec G.precision x) =
      (∑ i : V, G.boundary i * (x i) ^ 2) +
        (1 / 2 : ℝ) *
          (∑ i : V, ∑ j : V, G.edge i j * (x i - x j) ^ 2) := by
  classical
  let S : ℝ := ∑ i : V, ∑ j : V, G.edge i j * x i * (x i - x j)
  let T : ℝ := ∑ i : V, ∑ j : V, G.edge i j * (x i - x j) ^ 2
  have hswap : (∑ i : V, ∑ j : V,
      G.edge i j * x j * (x j - x i)) = S := by
    calc
      _ = ∑ j : V, ∑ i : V, G.edge i j * x j * (x j - x i) :=
        Finset.sum_comm
      _ = ∑ j : V, ∑ i : V, G.edge j i * x j * (x j - x i) := by
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro i _
        rw [G.edge_symm]
      _ = S := rfl
  have hT : T = S + S := by
    dsimp [T]
    calc
      _ = ∑ i : V, ∑ j : V,
          (G.edge i j * x i * (x i - x j) +
            G.edge i j * x j * (x j - x i)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = S + ∑ i : V, ∑ j : V,
          G.edge i j * x j * (x j - x i) := by
        simp only [Finset.sum_add_distrib, S]
      _ = S + S := by rw [hswap]
  have hleft : dotProduct x (Matrix.mulVec G.precision x) =
      (∑ i : V, G.boundary i * (x i) ^ 2) + S := by
    simp only [dotProduct, G.precision_mulVec, mul_add, Finset.sum_add_distrib]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      ring
    · dsimp [S]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
  rw [hleft]
  dsimp [T] at hT
  linarith only [hT]

theorem precision_posSemidef : G.precision.PosSemidef := by
  classical
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg G.precision_isHermitian
  intro x
  change 0 ≤ dotProduct x (Matrix.mulVec G.precision x)
  rw [G.precision_energy]
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (G.boundary_nonneg i) (sq_nonneg _)
  · apply mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (G.edge_nonneg i j) (sq_nonneg _)

end WiredConductances

end SupercriticalLQGUniqueness.B2.QPos
