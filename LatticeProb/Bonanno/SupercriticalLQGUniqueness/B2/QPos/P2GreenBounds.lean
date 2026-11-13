/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P2GreenBounds at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P2SubdivGreen

 







set_option autoImplicit false
noncomputable section

open Matrix

namespace SupercriticalLQGUniqueness.B2.QPos

namespace WiredConductances

variable {V : Type*} [Fintype V] [DecidableEq V] (G : WiredConductances V)

 
theorem precision_mulVec_green_col (hK : G.precision.PosDef) (x : V) :
    G.precision *ᵥ (fun y => G.green y x) = Pi.single x 1 := by
  funext v
  have := congrFun (congrFun (G.precision_mul_green hK) v) x
  rw [Matrix.mul_apply] at this
  simp only [Matrix.mulVec, dotProduct, this, Matrix.one_apply, Pi.single_apply]

 
theorem sq_le_energy_mul_green (hK : G.precision.PosDef) (x : V) (f : V → ℝ) :
    (f x) ^ 2 ≤ (f ⬝ᵥ (G.precision *ᵥ f)) * G.green x x := by
  set g : V → ℝ := fun y => G.green y x
  have hKg := G.precision_mulVec_green_col hK x
  have hfx : f x = f ⬝ᵥ (G.precision *ᵥ g) := by
    rw [hKg]; simp [dotProduct, Pi.single_apply]
  have hgg : g ⬝ᵥ (G.precision *ᵥ g) = G.green x x := by
    rw [hKg]; simp [dotProduct, Pi.single_apply, g]
  have hsym : g ⬝ᵥ (G.precision *ᵥ f) = f ⬝ᵥ (G.precision *ᵥ g) := by
    have h := G.precision_isHermitian.eq
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, h, dotProduct_comm]
  have hG := G.green_diag_pos hK x
  have hpsd := G.precision_posSemidef
  
  set t := (f ⬝ᵥ (G.precision *ᵥ g)) / G.green x x
  have h0 := hpsd.dotProduct_mulVec_nonneg (f - t • g)
  simp only [star_trivial] at h0
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub, dotProduct_sub,
    smul_dotProduct, dotProduct_smul, dotProduct_smul, smul_dotProduct, hsym, hgg] at h0
  simp only [smul_eq_mul] at h0
  rw [hfx]
  have ht : t * G.green x x = f ⬝ᵥ (G.precision *ᵥ g) := by
    simp only [t]; field_simp
  nlinarith [ht]

 
theorem green_le_of_energy_ge (hK : G.precision.PosDef) (x : V) {L : ℝ} (hL : 0 < L)
    (h : ∀ f : V → ℝ, f x = 1 → L ≤ f ⬝ᵥ (G.precision *ᵥ f)) : G.green x x ≤ 1 / L := by
  set g : V → ℝ := fun y => G.green y x
  have hG := G.green_diag_pos hK x
  have hKg := G.precision_mulVec_green_col hK x
  have hf := h ((G.green x x)⁻¹ • g) (by simp [g, hG.ne'])
  rw [Matrix.mulVec_smul, hKg, smul_dotProduct, dotProduct_smul] at hf
  simp only [smul_eq_mul, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, g] at hf
  rw [le_div_iff₀ hL]
  have : (G.green x x)⁻¹ * ((G.green x x)⁻¹ * G.green x x) = (G.green x x)⁻¹ := by
    field_simp
  rw [this] at hf
  have := mul_le_mul_of_nonneg_left hf hG.le
  rw [mul_inv_cancel₀ hG.ne'] at this
  linarith

 
theorem energy_indicator_le (A : Finset V) :
    (fun v => if v ∈ A then (1 : ℝ) else 0) ⬝ᵥ
        (G.precision *ᵥ fun v => if v ∈ A then (1 : ℝ) else 0) ≤
      ∑ v ∈ A, G.precision v v := by
  have hite : ∀ g : V → ℝ, (∑ x, if x ∈ A then g x else 0) = ∑ x ∈ A, g x := fun g => by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  simp only [dotProduct, Matrix.mulVec]
  simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero]
  rw [hite]
  apply Finset.sum_le_sum
  intro v hv
  rw [hite, ← Finset.add_sum_erase _ _ hv]
  have : ∑ w ∈ A.erase v, G.precision v w ≤ 0 := by
    apply Finset.sum_nonpos
    intro w hw
    have hvw : v ≠ w := (Finset.ne_of_mem_erase hw).symm
    simp only [precision, hvw, if_false]
    linarith [G.edge_nonneg v w]
  linarith

end WiredConductances

namespace EdgeGraph

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (Γ : EdgeGraph V E) (M : ℕ)

 
theorem energy_interpVec (hM : 2 ≤ M) (y : V → ℝ) :
    Γ.interpVec M y ⬝ᵥ ((Γ.subdiv M hM).toWired.precision *ᵥ Γ.interpVec M y) =
      y ⬝ᵥ (Γ.toWired.precision *ᵥ y) := by
  have hM1 : 1 ≤ M := by omega
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
  rw [Γ.energy_subdiv_eq M hM, energy_eq_edge_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [Γ.ext_interpVec]
  have hterm : ∀ k ∈ Finset.range M, (M : ℝ) * Γ.cond e *
      (Γ.interp M (ext 0 y) (Γ.subPos M e k) - Γ.interp M (ext 0 y) (Γ.subPos M e (k + 1))) ^ 2 =
      Γ.cond e * (ext 0 y (Γ.tail e) - ext 0 y (Γ.head e)) ^ 2 / M := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [Γ.interp_subPos M _ e (by omega) hM1, Γ.interp_subPos M _ e (by omega) hM1]
    push_cast
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

 
theorem energy_subdiv_ge_tail (hM : 2 ≤ M) (y : SubV V E M → ℝ) (e : E)
    (hh : Γ.head e = none) {q : ℕ} (hq : q ≤ M) :
    (M : ℝ) * Γ.cond e / (M - q) * (ext 0 y (Γ.subPos M e q)) ^ 2 ≤
      y ⬝ᵥ ((Γ.subdiv M hM).toWired.precision *ᵥ y) := by
  have hM1 : 1 ≤ M := by omega
  rcases Nat.eq_or_lt_of_le hq with hqM | hqM
  · rw [hqM, sub_self, div_zero, zero_mul]
    have := (Γ.subdiv M hM).toWired.precision_posSemidef.dotProduct_mulVec_nonneg y
    simpa using this
  rw [Γ.energy_subdiv_eq M hM]
  have hnn : ∀ e' ∈ Finset.univ, 0 ≤ ∑ k ∈ Finset.range M, (M : ℝ) * Γ.cond e' *
      (ext 0 y (Γ.subPos M e' k) - ext 0 y (Γ.subPos M e' (k + 1))) ^ 2 :=
    fun e' _ => Finset.sum_nonneg fun k _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Γ.cond_pos e').le) (sq_nonneg _)
  refine le_trans ?_ (Finset.single_le_sum hnn (Finset.mem_univ e))
  have hcs := sq_sub_le_mul_sum_sq (fun k => ext 0 y (Γ.subPos M e k)) q (M - q)
  have hMq : q + (M - q) = M := by omega
  simp only [hMq] at hcs
  rw [Γ.subPos_M M e hM1, hh] at hcs
  simp only [Option.map_none, ext_none, sub_zero] at hcs
  have hsub : ∑ k ∈ Finset.range (M - q), (ext 0 y (Γ.subPos M e (q + k)) -
      ext 0 y (Γ.subPos M e (q + k + 1))) ^ 2 ≤
      ∑ k ∈ Finset.range M, (ext 0 y (Γ.subPos M e k) - ext 0 y (Γ.subPos M e (k + 1))) ^ 2 := by
    have h1 : ∑ k ∈ Finset.range (M - q), (ext 0 y (Γ.subPos M e (q + k)) -
        ext 0 y (Γ.subPos M e (q + k + 1))) ^ 2 =
        ∑ k ∈ Finset.Ico q M, (ext 0 y (Γ.subPos M e k) - ext 0 y (Γ.subPos M e (k + 1))) ^ 2 := by
      rw [Finset.sum_Ico_eq_sum_range]
    rw [h1]
    exact Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => by
      simp only [Finset.mem_Ico] at hk; exact Finset.mem_range.mpr hk.2) (fun _ _ _ => sq_nonneg _)
  have hpos : (0 : ℝ) < M - q := by
    have : (q : ℝ) < M := by exact_mod_cast hqM
    linarith
  have hc := Γ.cond_pos e
  rw [← Finset.mul_sum]
  have hcast : ((M - q : ℕ) : ℝ) = (M : ℝ) - q := by rw [Nat.cast_sub hq]
  rw [hcast] at hcs
  calc (M : ℝ) * Γ.cond e / (M - q) * (ext 0 y (Γ.subPos M e q)) ^ 2
      ≤ (M : ℝ) * Γ.cond e / (M - q) * ((M - q) * ∑ k ∈ Finset.range M,
          (ext 0 y (Γ.subPos M e k) - ext 0 y (Γ.subPos M e (k + 1))) ^ 2) :=
        mul_le_mul_of_nonneg_left (hcs.trans (mul_le_mul_of_nonneg_left hsub hpos.le))
          (by positivity)
    _ = (M : ℝ) * Γ.cond e * ∑ k ∈ Finset.range M,
          (ext 0 y (Γ.subPos M e k) - ext 0 y (Γ.subPos M e (k + 1))) ^ 2 := by
        field_simp

end EdgeGraph

end SupercriticalLQGUniqueness.B2.QPos
