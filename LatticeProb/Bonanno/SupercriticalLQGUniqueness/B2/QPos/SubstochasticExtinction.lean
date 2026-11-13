/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.SubstochasticExtinction at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.DGFFBoxDegree

 


set_option autoImplicit false
noncomputable section

open Filter Topology Matrix

namespace SupercriticalLQGUniqueness.B2.QPos

variable {V : Type*} [Fintype V] [DecidableEq V]

 
private def survivalMass (P : Matrix V V ℝ) (k : ℕ) (i : V) : ℝ :=
  ∑ j, (P ^ k) i j

private theorem survivalMass_nonneg (P : Matrix V V ℝ)
    (hP : ∀ i j, 0 ≤ P i j) (k : ℕ) (i : V) :
    0 ≤ survivalMass P k i := by
  exact Finset.sum_nonneg (fun j _ => Matrix.pow_apply_nonneg hP k i j)

private theorem survivalMass_succ_le (P : Matrix V V ℝ)
    (hP : ∀ i j, 0 ≤ P i j)
    (hrow : ∀ i, ∑ j, P i j ≤ 1) (k : ℕ) (i : V) :
    survivalMass P (k + 1) i ≤ survivalMass P k i := by
  unfold survivalMass
  rw [pow_succ]
  simp only [Matrix.mul_apply]
  calc
    (∑ j : V, ∑ l : V, (P ^ k) i l * P l j) =
      ∑ l : V, (P ^ k) i l * ∑ j : V, P l j := by
        rw [Finset.sum_comm]
        simp only [Finset.mul_sum]
    _ ≤ ∑ l : V, (P ^ k) i l := by
      apply Finset.sum_le_sum
      intro l _
      have hp := Matrix.pow_apply_nonneg hP k i l
      calc
        (P ^ k) i l * (∑ j : V, P l j) ≤ (P ^ k) i l * 1 :=
          mul_le_mul_of_nonneg_left (hrow l) hp
        _ = (P ^ k) i l := mul_one _

private theorem survivalMass_tendsto (P : Matrix V V ℝ)
    (hP : ∀ i j, 0 ≤ P i j)
    (hrow : ∀ i, ∑ j, P i j ≤ 1) (i : V) :
    Tendsto (fun k => survivalMass P k i) atTop
      (𝓝 (⨅ k, survivalMass P k i)) := by
  have hanti : Antitone (fun k => survivalMass P k i) :=
    antitone_nat_of_succ_le (survivalMass_succ_le P hP hrow · i)
  apply tendsto_atTop_ciInf hanti
  exact ⟨0, by rintro x ⟨k, rfl⟩; exact survivalMass_nonneg P hP k i⟩

private theorem survivalMass_succ_eq (P : Matrix V V ℝ) (k : ℕ) (i : V) :
    survivalMass P (k + 1) i =
      ∑ j : V, P i j * survivalMass P k j := by
  unfold survivalMass
  rw [pow_succ']
  simp only [Matrix.mul_apply]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

 

theorem substochastic_pow_tendsto_zero (P : Matrix V V ℝ)
    (hP : ∀ i j, 0 ≤ P i j)
    (hrow : ∀ i, ∑ j, P i j ≤ 1)
    (hunit : IsUnit (1 - P)) :
    Tendsto (fun k : ℕ => P ^ k) atTop (𝓝 0) := by
  let L : V → ℝ := fun i => ⨅ k, survivalMass P k i
  have hlim (i : V) : Tendsto (fun k => survivalMass P k i) atTop (𝓝 (L i)) :=
    survivalMass_tendsto P hP hrow i
  have hfix (i : V) : L i = ∑ j : V, P i j * L j := by
    have hshift : Tendsto (fun k => survivalMass P (k + 1) i) atTop (𝓝 (L i)) :=
      (hlim i).comp (tendsto_add_atTop_nat 1)
    have hright : Tendsto (fun k => ∑ j : V, P i j * survivalMass P k j)
        atTop (𝓝 (∑ j : V, P i j * L j)) := by
      convert tendsto_finsetSum Finset.univ (fun j _ =>
        (tendsto_const_nhds (x := P i j)).mul (hlim j)) using 1
    have heq (k : ℕ) := survivalMass_succ_eq P k i
    exact tendsto_nhds_unique hshift (by simpa only [heq] using hright)
  have hzero : L = 0 := by
    apply (Matrix.mulVec_injective_of_isUnit hunit)
    have hz : (1 - P) *ᵥ L = 0 := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      ext i
      simp only [Pi.sub_apply, Pi.zero_apply, Matrix.mulVec, dotProduct]
      exact sub_eq_zero.mpr (hfix i)
    simpa using hz
  have hentry (i j : V) : Tendsto (fun k => (P ^ k) i j) atTop (𝓝 0) := by
    have hbound (k : ℕ) : (P ^ k) i j ≤ survivalMass P k i :=
      Finset.single_le_sum (fun l _ => Matrix.pow_apply_nonneg hP k i l)
        (Finset.mem_univ j)
    have hnon (k : ℕ) : 0 ≤ (P ^ k) i j := Matrix.pow_apply_nonneg hP k i j
    have hlim0 : Tendsto (fun k => survivalMass P k i) atTop (𝓝 0) := by
      simpa [hzero] using hlim i
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hlim0 hnon hbound
  exact tendsto_pi_nhds.2 (fun i => tendsto_pi_nhds.2 (fun j => hentry i j))

end SupercriticalLQGUniqueness.B2.QPos
