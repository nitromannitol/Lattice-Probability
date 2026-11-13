/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P2PathSum at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports.
   Changed for Lean v4.35: in hasSum_excursionWeight, the last bullet `· simp` after `convert this using 1` is removed (the newer `convert` already closes that goal). -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.SubstochasticExtinction
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.DGFFCore
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.DGFFPositive

 












set_option autoImplicit false
noncomputable section

open Filter Topology Matrix

namespace SupercriticalLQGUniqueness.B2.QPos

 

abbrev Excursion (V : Type*) := Σ k : ℕ, Fin (k + 1) → V

 
def visitProduct {V R : Type*} [CommMonoid R] (m : V → R) (γ : Excursion V) : R :=
  ∏ j : Fin (γ.1 + 1), m (γ.2 j)

 
theorem sum_path_eq_dotProduct_pow {V R : Type*} [Fintype V] [DecidableEq V]
    [CommSemiring R] (A : Matrix V V R) (k : ℕ) (u v : V → R) :
    ∑ γ : Fin (k + 1) → V, u (γ 0) * (∏ j : Fin k, A (γ j.castSucc) (γ j.succ)) *
      v (γ (Fin.last k)) = u ⬝ᵥ (A ^ k *ᵥ v) := by
  induction k generalizing u with
  | zero =>
    rw [← (Equiv.funUnique (Fin 1) V).symm.sum_comp]
    simp [dotProduct]
  | succ k ih =>
    rw [← (Fin.consEquiv (fun _ : Fin (k + 2) => V)).sum_comp, Fintype.sum_prod_type]
    have hterm : ∀ (x : V) (γ : Fin (k + 1) → V),
        u ((Fin.consEquiv (fun _ : Fin (k + 2) => V)) (x, γ) 0) *
          (∏ j : Fin (k + 1), A ((Fin.consEquiv (fun _ : Fin (k + 2) => V)) (x, γ)
            j.castSucc) ((Fin.consEquiv (fun _ : Fin (k + 2) => V)) (x, γ) j.succ)) *
          v ((Fin.consEquiv (fun _ : Fin (k + 2) => V)) (x, γ) (Fin.last (k + 1))) =
        (u x * A x (γ 0)) * (∏ j : Fin k, A (γ j.castSucc) (γ j.succ)) *
          v (γ (Fin.last k)) := by
      intro x γ
      simp only [Fin.consEquiv_apply]
      rw [Fin.prod_univ_succ]
      simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.succ_zero_eq_one, Fin.cons_one,
        Fin.cons_succ]
      have hlast : (Fin.last (k + 1)) = (Fin.last k).succ := (Fin.succ_last k).symm
      rw [hlast, Fin.cons_succ]
      have hcs : ∀ j : Fin k, (j.succ.castSucc : Fin (k + 2)) = j.castSucc.succ :=
        fun j => (Fin.succ_castSucc j).symm
      simp only [hcs, Fin.cons_succ]
      ring
    simp_rw [hterm]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    have := ih (fun y => ∑ x : V, u x * A x y)
    rw [this]
    rw [pow_succ', ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u A]
    rfl

namespace WiredConductances

variable {V : Type*} [Fintype V] [DecidableEq V] (G : WiredConductances V)

theorem totalRate_nonneg (i : V) : 0 ≤ G.totalRate i := by
  unfold totalRate
  exact add_nonneg (G.boundary_nonneg i)
    (Finset.sum_nonneg (fun j _ => G.edge_nonneg i j))

theorem precision_diag (i : V) : G.precision i i = G.totalRate i := by
  simp [precision, totalRate]

theorem totalRate_pos (hK : G.precision.PosDef) (i : V) : 0 < G.totalRate i := by
  rw [← G.precision_diag]
  exact hK.diag_pos

theorem killedTransition_nonneg (i j : V) : 0 ≤ G.killedTransition i j :=
  div_nonneg (G.edge_nonneg i j) (G.totalRate_nonneg i)

theorem killedTransition_row_le (i : V) : ∑ j, G.killedTransition i j ≤ 1 := by
  unfold killedTransition
  rw [← Finset.sum_div]
  rcases (G.totalRate_nonneg i).eq_or_lt with h | h
  · rw [← h, div_zero]; norm_num
  · rw [div_le_one h]
    unfold totalRate
    linarith [G.boundary_nonneg i]

 
theorem one_sub_killedTransition (hK : G.precision.PosDef) :
    1 - G.killedTransition =
      Matrix.diagonal (fun i => (G.totalRate i)⁻¹) * G.precision := by
  ext i j
  rw [Matrix.diagonal_mul, G.precision_eq_totalRate_sub_edge]
  have hr := (G.totalRate_pos hK i).ne'
  by_cases hij : i = j
  · subst j
    simp [killedTransition, G.edge_self, hr]
  · simp [hij, killedTransition]
    field_simp

theorem isUnit_one_sub_killedTransition (hK : G.precision.PosDef) :
    IsUnit (1 - G.killedTransition) := by
  rw [G.one_sub_killedTransition hK]
  refine (Matrix.isUnit_diagonal.mpr (Pi.isUnit_iff.mpr fun i => ?_)).mul ?_
  · exact (inv_pos.mpr (G.totalRate_pos hK i)).ne'.isUnit
  · exact (Matrix.isUnit_iff_isUnit_det _).mpr hK.det_pos.ne'.isUnit

theorem killedTransition_pow_tendsto_zero (hK : G.precision.PosDef) :
    Tendsto (fun k : ℕ => G.killedTransition ^ k) atTop (𝓝 0) :=
  substochastic_pow_tendsto_zero G.killedTransition G.killedTransition_nonneg
    G.killedTransition_row_le (G.isUnit_one_sub_killedTransition hK)

 
def excursionWeight (γ : Excursion V) : ℝ :=
  G.boundary (γ.2 0) * (∏ j : Fin γ.1, G.killedTransition (γ.2 j.castSucc) (γ.2 j.succ)) *
    (G.boundary (γ.2 (Fin.last γ.1)) / G.totalRate (γ.2 (Fin.last γ.1)))

theorem excursionWeight_nonneg (γ : Excursion V) : 0 ≤ G.excursionWeight γ := by
  unfold excursionWeight
  refine mul_nonneg (mul_nonneg (G.boundary_nonneg _) ?_)
    (div_nonneg (G.boundary_nonneg _) (G.totalRate_nonneg _))
  exact Finset.prod_nonneg (fun j _ => G.killedTransition_nonneg _ _)

 
theorem sum_excursion_slice (m : V → ℂ) (k : ℕ) :
    ∑ γ : Fin (k + 1) → V, (G.excursionWeight ⟨k, γ⟩ : ℂ) * visitProduct m ⟨k, γ⟩ =
      (fun i => (G.boundary i : ℂ)) ⬝ᵥ
        ((Matrix.of fun i j => m i * (G.killedTransition i j : ℂ)) ^ k *ᵥ
          fun i => m i * ((G.boundary i / G.totalRate i : ℝ) : ℂ)) := by
  rw [← sum_path_eq_dotProduct_pow]
  apply Finset.sum_congr rfl
  intro γ _
  simp only [excursionWeight, visitProduct, Complex.ofReal_mul, Complex.ofReal_prod,
    Matrix.of_apply]
  rw [Fin.prod_univ_castSucc, Finset.prod_mul_distrib]
  ring

 
theorem norm_multiplier_pow_le (m : V → ℂ) (hm : ∀ i, ‖m i‖ ≤ 1) (k : ℕ) (i j : V) :
    ‖((Matrix.of fun i j => m i * (G.killedTransition i j : ℂ)) ^ k) i j‖ ≤
      (G.killedTransition ^ k) i j := by
  induction k generalizing j with
  | zero =>
    by_cases h : i = j
    · subst j; simp
    · simp [h]
  | succ k ih =>
    rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
    rw [norm_mul]
    refine mul_le_mul (ih l) ?_ (norm_nonneg _) (Matrix.pow_apply_nonneg
      G.killedTransition_nonneg k i l)
    simp only [Matrix.of_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (G.killedTransition_nonneg l j)]
    exact mul_le_of_le_one_left (G.killedTransition_nonneg l j) (hm l)

theorem killedTransition_pow_apply_tendsto_zero (hK : G.precision.PosDef) (i j : V) :
    Tendsto (fun k : ℕ => (G.killedTransition ^ k) i j) atTop (𝓝 0) := by
  have h := ((continuous_id.matrix_elem i j).tendsto 0).comp
    (G.killedTransition_pow_tendsto_zero hK)
  simpa [Function.comp_def] using h

 
theorem fixedPoint_iterate (m : V → ℂ) (Y : V → ℂ)
    (hY : ∀ i, Y i = m i * (((G.boundary i / G.totalRate i : ℝ) : ℂ) +
      ∑ j, (G.killedTransition i j : ℂ) * Y j)) (N : ℕ) :
    (∑ i, (G.boundary i : ℂ) * Y i) =
      (∑ k ∈ Finset.range N, ∑ γ : Fin (k + 1) → V,
          (G.excursionWeight ⟨k, γ⟩ : ℂ) * visitProduct m ⟨k, γ⟩) +
        (fun i => (G.boundary i : ℂ)) ⬝ᵥ
          ((Matrix.of fun i j => m i * (G.killedTransition i j : ℂ)) ^ N *ᵥ Y) := by
  set A : Matrix V V ℂ := Matrix.of fun i j => m i * (G.killedTransition i j : ℂ)
  set v : V → ℂ := fun i => m i * ((G.boundary i / G.totalRate i : ℝ) : ℂ)
  have hYv : Y = v + A *ᵥ Y := by
    funext i
    rw [hY i]
    simp only [v, A, Pi.add_apply, Matrix.mulVec, dotProduct, Matrix.of_apply]
    rw [mul_add, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hiter : ∀ N : ℕ, Y = (∑ k ∈ Finset.range N, A ^ k *ᵥ v) + A ^ N *ᵥ Y := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ]
      conv_lhs => rw [ih]
      conv_lhs => rw [hYv]
      rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, ← pow_succ]
      abel
  have hc : (∑ i, (G.boundary i : ℂ) * Y i) = (fun i => (G.boundary i : ℂ)) ⬝ᵥ Y := rfl
  rw [hc]
  conv_lhs => rw [hiter N]
  rw [dotProduct_add, dotProduct_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  exact (G.sum_excursion_slice m k).symm

 
theorem tendsto_slice_sum (hK : G.precision.PosDef) (m : V → ℂ) (hm : ∀ i, ‖m i‖ ≤ 1)
    (Y : V → ℂ)
    (hY : ∀ i, Y i = m i * (((G.boundary i / G.totalRate i : ℝ) : ℂ) +
      ∑ j, (G.killedTransition i j : ℂ) * Y j)) :
    Tendsto (fun N => ∑ k ∈ Finset.range N, ∑ γ : Fin (k + 1) → V,
        (G.excursionWeight ⟨k, γ⟩ : ℂ) * visitProduct m ⟨k, γ⟩) atTop
      (𝓝 (∑ i, (G.boundary i : ℂ) * Y i)) := by
  have hrem : Tendsto (fun N => (fun i => (G.boundary i : ℂ)) ⬝ᵥ
      ((Matrix.of fun i j => m i * (G.killedTransition i j : ℂ)) ^ N *ᵥ Y)) atTop (𝓝 0) := by
    have hbound : ∀ N, ‖(fun i => (G.boundary i : ℂ)) ⬝ᵥ
        ((Matrix.of fun i j => m i * (G.killedTransition i j : ℂ)) ^ N *ᵥ Y)‖ ≤
        ∑ i, ∑ j, G.boundary i * ((G.killedTransition ^ N) i j * ‖Y j‖) := by
      intro N
      simp only [dotProduct, Matrix.mulVec]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (G.boundary_nonneg i),
        ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
        (Finset.sum_le_sum fun j _ => ?_)) (G.boundary_nonneg i)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (G.norm_multiplier_pow_le m hm N i j) (norm_nonneg _)
    apply squeeze_zero_norm hbound
    have : Tendsto (fun N => ∑ i, ∑ j, G.boundary i * ((G.killedTransition ^ N) i j * ‖Y j‖))
        atTop (𝓝 (∑ i : V, ∑ j : V, G.boundary i * (0 * ‖Y j‖))) :=
      tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ =>
        (tendsto_const_nhds.mul ((G.killedTransition_pow_apply_tendsto_zero hK i j).mul
          tendsto_const_nhds))
    simpa using this
  have heq : ∀ N, (∑ k ∈ Finset.range N, ∑ γ : Fin (k + 1) → V,
        (G.excursionWeight ⟨k, γ⟩ : ℂ) * visitProduct m ⟨k, γ⟩) =
      (∑ i, (G.boundary i : ℂ) * Y i) - (fun i => (G.boundary i : ℂ)) ⬝ᵥ
        ((Matrix.of fun i j => m i * (G.killedTransition i j : ℂ)) ^ N *ᵥ Y) := by
    intro N
    rw [G.fixedPoint_iterate m Y hY N]
    ring
  simp_rw [heq]
  simpa using (tendsto_const_nhds (x := ∑ i, (G.boundary i : ℂ) * Y i)).sub hrem

 
theorem one_fixedPoint (hK : G.precision.PosDef) (i : V) :
    (1 : ℂ) = 1 * (((G.boundary i / G.totalRate i : ℝ) : ℂ) +
      ∑ j, (G.killedTransition i j : ℂ) * 1) := by
  have hr := (G.totalRate_pos hK i).ne'
  simp only [one_mul, mul_one, killedTransition]
  rw [← Complex.ofReal_sum, ← Complex.ofReal_add, ← Finset.sum_div, ← add_div]
  have : G.boundary i + ∑ j, G.edge i j = G.totalRate i := rfl
  rw [this, div_self hr, Complex.ofReal_one]

 

theorem hasSum_excursionWeight (hK : G.precision.PosDef) :
    HasSum G.excursionWeight (∑ i, G.boundary i) := by
  have hslice : ∀ k, ∑ γ : Fin (k + 1) → V, G.excursionWeight ⟨k, γ⟩ =
      (∑ γ : Fin (k + 1) → V, (G.excursionWeight ⟨k, γ⟩ : ℂ) *
        visitProduct (fun _ => (1 : ℂ)) ⟨k, γ⟩).re := by
    intro k
    simp [visitProduct, Complex.re_sum]
  have hpart := G.tendsto_slice_sum hK (fun _ => 1) (by simp) (fun _ => 1)
    (fun i => G.one_fixedPoint hK i)
  have hpart' : Tendsto (fun N => ∑ k ∈ Finset.range N, ∑ γ : Fin (k + 1) → V,
      G.excursionWeight ⟨k, γ⟩) atTop (𝓝 (∑ i, G.boundary i)) := by
    have := (Complex.continuous_re.tendsto _).comp hpart
    simp only [Function.comp_def, Complex.re_sum, mul_one] at this
    convert this using 1
    · funext N
      apply Finset.sum_congr rfl
      intro k _
      rw [hslice k, Complex.re_sum]
  have hfib : ∀ k, HasSum (fun γ : Fin (k + 1) → V => G.excursionWeight ⟨k, γ⟩)
      (∑ γ : Fin (k + 1) → V, G.excursionWeight ⟨k, γ⟩) := fun k => hasSum_fintype _
  have hnat : HasSum (fun k => ∑ γ : Fin (k + 1) → V, G.excursionWeight ⟨k, γ⟩)
      (∑ i, G.boundary i) :=
    (hasSum_iff_tendsto_nat_of_nonneg (fun k => Finset.sum_nonneg
      (fun γ _ => G.excursionWeight_nonneg _)) _).mpr hpart'
  exact HasSum.sigma_of_hasSum hnat hfib
    (summable_sigma_of_nonneg (fun γ => G.excursionWeight_nonneg γ) |>.mpr
      ⟨fun k => (hfib k).summable, by simpa [tsum_fintype] using hnat.summable⟩)

theorem summable_excursionWeight (hK : G.precision.PosDef) :
    Summable G.excursionWeight := (G.hasSum_excursionWeight hK).summable

 

theorem hasSum_excursion_visitProduct (hK : G.precision.PosDef) (m : V → ℂ)
    (hm : ∀ i, ‖m i‖ ≤ 1) (Y : V → ℂ)
    (hY : ∀ i, Y i = m i * (((G.boundary i / G.totalRate i : ℝ) : ℂ) +
      ∑ j, (G.killedTransition i j : ℂ) * Y j)) :
    HasSum (fun γ : Excursion V => (G.excursionWeight γ : ℂ) * visitProduct m γ)
      (∑ i, (G.boundary i : ℂ) * Y i) := by
  have hnorm : ∀ γ : Excursion V,
      ‖(G.excursionWeight γ : ℂ) * visitProduct m γ‖ ≤ G.excursionWeight γ := by
    intro γ
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (G.excursionWeight_nonneg γ)]
    refine mul_le_of_le_one_right (G.excursionWeight_nonneg γ) ?_
    unfold visitProduct
    rw [norm_prod]
    exact Finset.prod_le_one₀ (fun j _ => norm_nonneg _) (fun j _ => hm _)
  have hsum : Summable (fun γ : Excursion V => (G.excursionWeight γ : ℂ) * visitProduct m γ) :=
    Summable.of_norm_bounded (G.summable_excursionWeight hK) hnorm
  have hnat : HasSum (fun k => ∑ γ : Fin (k + 1) → V,
      (G.excursionWeight ⟨k, γ⟩ : ℂ) * visitProduct m ⟨k, γ⟩)
      (∑' γ : Excursion V, (G.excursionWeight γ : ℂ) * visitProduct m γ) := by
    have := hsum.hasSum.sigma (fun k => hasSum_fintype _)
    exact this
  have hlim := G.tendsto_slice_sum hK m hm Y hY
  have heq := tendsto_nhds_unique hnat.tendsto_sum_nat hlim
  rw [← heq]
  exact hsum.hasSum

end WiredConductances

end SupercriticalLQGUniqueness.B2.QPos
