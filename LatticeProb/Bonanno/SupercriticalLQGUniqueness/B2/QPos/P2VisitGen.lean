/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P2VisitGen at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2LocalTime

 








set_option autoImplicit false
noncomputable section

open Matrix Complex

namespace SupercriticalLQGUniqueness.B2.QPos

namespace WiredConductances

variable {V : Type*} [Fintype V] [DecidableEq V] (G : WiredConductances V)

 
def green : Matrix V V ℝ := G.precision⁻¹

theorem precision_mul_green (hK : G.precision.PosDef) : G.precision * G.green = 1 :=
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hK.isUnit)

theorem green_mul_precision (hK : G.precision.PosDef) : G.green * G.precision = 1 :=
  Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hK.isUnit)

theorem green_symm (hK : G.precision.PosDef) (i j : V) : G.green i j = G.green j i := by
  have h := hK.inv.isHermitian.eq
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  show G.precision⁻¹ i j = G.precision⁻¹ j i
  simpa only [Matrix.transpose_apply] using congrFun (congrFun h j) i

theorem green_diag_pos (hK : G.precision.PosDef) (x : V) : 0 < G.green x x :=
  hK.inv.diag_pos

 
theorem green_mulVec_boundary (hK : G.precision.PosDef) :
    G.green *ᵥ G.boundary = fun _ => 1 := by
  have h1 : G.precision *ᵥ (fun _ => (1 : ℝ)) = G.boundary := funext (G.precision_mulVec_one)
  rw [← h1, Matrix.mulVec_mulVec, G.green_mul_precision hK, Matrix.one_mulVec]

theorem sum_boundary_mul_green (hK : G.precision.PosDef) (x : V) :
    ∑ i, G.boundary i * G.green i x = 1 := by
  have h := congrFun (G.green_mulVec_boundary hK) x
  simp only [Matrix.mulVec, dotProduct] at h
  rw [← h]
  apply Finset.sum_congr rfl
  intro i _
  rw [G.green_symm hK, mul_comm]

 
def oneVertexMult (x : V) (r : ℝ) (v : V) : ℂ := if v = x then (r : ℂ) else 1

theorem oneVertexMult_norm_le (x : V) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (v : V) :
    ‖oneVertexMult x r v‖ ≤ 1 := by
  unfold oneVertexMult
  split_ifs
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]; exact hr1
  · simp

 
theorem precision_mulVec_rankOne (hK : G.precision.PosDef) (x : V) (β : ℝ) (v : V) :
    (G.precision *ᵥ fun w => 1 - β * G.green w x) v = G.boundary v - β * (if v = x then 1 else 0) := by
  have hsplit : (fun w => 1 - β * G.green w x) = (fun _ => (1 : ℝ)) - β • (fun w => G.green w x) := by
    funext w; simp
  rw [hsplit, Matrix.mulVec_sub, Matrix.mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    G.precision_mulVec_one]
  congr 2
  have := congrFun (congrFun (G.precision_mul_green hK) v) x
  rw [Matrix.mul_apply] at this
  rw [Matrix.mulVec, dotProduct, this, Matrix.one_apply]

 

theorem fixedPoint_of_precision_at (hK : G.precision.PosDef) (m : V → ℝ) (Y : V → ℝ) (v : V)
    (hmv : m v ≠ 0)
    (h : (G.precision *ᵥ Y) v + G.totalRate v * (1 / m v - 1) * Y v = G.boundary v) :
    ((Y v : ℝ) : ℂ) = (m v : ℂ) * (((G.boundary v / G.totalRate v : ℝ) : ℂ) +
      ∑ j, (G.killedTransition v j : ℂ) * (Y j : ℂ)) := by
  have hr := (G.totalRate_pos hK v).ne'
  have hKY : (G.precision *ᵥ Y) v = G.totalRate v * Y v - ∑ j, G.edge v j * Y j := by
    rw [G.precision_mulVec]
    unfold totalRate
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
    ring
  rw [hKY] at h
  have hS : ∑ j, G.killedTransition v j * Y j = (∑ j, G.edge v j * Y j) / G.totalRate v := by
    unfold killedTransition
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hreal : Y v = m v * (G.boundary v / G.totalRate v + ∑ j, G.killedTransition v j * Y j) := by
    rw [hS, ← add_div]
    have h' : G.totalRate v * Y v / m v = G.boundary v + ∑ j, G.edge v j * Y j := by
      have : G.totalRate v * Y v / m v =
          G.totalRate v * Y v + G.totalRate v * (1 / m v - 1) * Y v := by
        field_simp; ring
      rw [this]; linarith
    rw [← h']
    field_simp
  exact_mod_cast hreal

theorem fixedPoint_of_precision (hK : G.precision.PosDef) (m : V → ℝ) (Y : V → ℝ)
    (hm : ∀ v, m v ≠ 0)
    (hY : ∀ v, (G.precision *ᵥ Y) v + G.totalRate v * (1 / m v - 1) * Y v = G.boundary v)
    (v : V) :
    ((Y v : ℝ) : ℂ) = (m v : ℂ) * (((G.boundary v / G.totalRate v : ℝ) : ℂ) +
      ∑ j, (G.killedTransition v j : ℂ) * (Y j : ℂ)) :=
  G.fixedPoint_of_precision_at hK m Y v (hm v) (hY v)

 
theorem hasSum_soupMass_pow_visit (hK : G.precision.PosDef) {t : ℝ} (ht : 0 ≤ t) (x : V)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    HasSum (fun s => G.soupMassAt t s * r ^ soupVisitCount s x)
      (Real.exp (-(t * ((G.totalRate x * (1 - r) / r) /
        (1 + (G.totalRate x * (1 - r) / r) * G.green x x))))) := by
  obtain ⟨α, hαdef⟩ : ∃ α, α = G.totalRate x * (1 - r) / r := ⟨_, rfl⟩
  rw [← hαdef]
  have hα : 0 ≤ α := by
    rw [hαdef]; exact div_nonneg (mul_nonneg (G.totalRate_pos hK x).le (by linarith)) hr0.le
  have hG := G.green_diag_pos hK x
  obtain ⟨β, hβdef⟩ : ∃ β, β = α / (1 + α * G.green x x) := ⟨_, rfl⟩
  rw [← hβdef]
  have hden : 1 + α * G.green x x ≠ 0 := by positivity
  have hβ : β * (1 + α * G.green x x) = α := by rw [hβdef]; field_simp
  set Y : V → ℝ := fun w => 1 - β * G.green w x
  have hfix : ∀ v, ((Y v : ℝ) : ℂ) = oneVertexMult x r v * (((G.boundary v / G.totalRate v : ℝ) : ℂ) +
      ∑ j, (G.killedTransition v j : ℂ) * (Y j : ℂ)) := by
    intro v
    have hm : (oneVertexMult x r v) = ((if v = x then r else 1 : ℝ) : ℂ) := by
      unfold oneVertexMult; split_ifs <;> simp
    rw [hm]
    refine G.fixedPoint_of_precision hK (fun v => if v = x then r else 1) Y
      (fun v => by split_ifs; exact hr0.ne'; exact one_ne_zero) ?_ v
    intro w
    rw [G.precision_mulVec_rankOne hK x β w]
    by_cases hw : w = x
    · subst hw
      simp only [if_true, mul_one]
      have : G.totalRate w * (1 / r - 1) = α := by
        rw [hαdef]; field_simp
      rw [this]
      simp only [Y]
      linear_combination -hβ
    · simp [hw]
  have hsum := hasSum_soupMass_mul_prod G.excursionWeight_nonneg (G.hasSum_excursionWeight hK) ht
    (visitProduct (oneVertexMult x r)) (by
      intro γ
      unfold visitProduct
      rw [norm_prod]
      exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
        (fun j _ => oneVertexMult_norm_le x hr0.le hr1 _))
  have hF := G.hasSum_excursion_visitProduct hK (oneVertexMult x r)
    (oneVertexMult_norm_le x hr0.le hr1) (fun v => ((Y v : ℝ) : ℂ)) hfix
  rw [hF.tsum_eq] at hsum
  have hval : ∑ i, (G.boundary i : ℂ) * ((Y i : ℝ) : ℂ) = ((∑ i, G.boundary i - β : ℝ) : ℂ) := by
    have hr : ∑ i, G.boundary i * Y i = ∑ i, G.boundary i - β := by
      simp only [Y, mul_sub, mul_one, Finset.sum_sub_distrib]
      rw [show ∑ i, G.boundary i * (β * G.green i x) = β * ∑ i, G.boundary i * G.green i x by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring,
        G.sum_boundary_mul_green hK x, mul_one]
    rw [← hr]
    push_cast
    rfl
  rw [hval] at hsum
  have hre := Complex.hasSum_re hsum
  have htarget : (Complex.exp (-(t * ((∑ i, G.boundary i : ℝ) : ℂ))) *
      Complex.exp (t * ((∑ i, G.boundary i - β : ℝ) : ℂ))).re = Real.exp (-(t * β)) := by
    rw [← Complex.exp_add]
    rw [show -( (t : ℂ) * ((∑ i, G.boundary i : ℝ) : ℂ)) + t * ((∑ i, G.boundary i - β : ℝ) : ℂ) =
      ((-(t * β) : ℝ) : ℂ) by push_cast; ring, ← Complex.ofReal_exp, Complex.ofReal_re]
  rw [htarget] at hre
  convert hre using 1
  funext s
  have hprod : ∏ i, visitProduct (oneVertexMult x r) (s.2 i) = ((r ^ soupVisitCount s x : ℝ) : ℂ) := by
    rw [prod_visitProduct_eq_prod_pow]
    rw [Finset.prod_eq_single x]
    · simp [oneVertexMult]
    · intro v _ hv
      simp [oneVertexMult, hv]
    · simp
  rw [hprod, ← Complex.ofReal_mul, Complex.ofReal_re]
  rfl

end WiredConductances

end SupercriticalLQGUniqueness.B2.QPos
