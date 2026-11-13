/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P3Hitting at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P3WalkMass

 









set_option autoImplicit false
noncomputable section

open Finset Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.QPos.P3

open Classical

variable (n : ℕ) (T : Set (DGFFSite n))

 
def hitP : ℕ → DGFFSite n → ℝ
  | 0, y => if y ∈ T then 1 else 0
  | K + 1, y => if y ∈ T then 1 else
      ∑ y', (boxConductances n).killedTransition y y' * hitP K y'

theorem hitP_nonneg : ∀ K y, 0 ≤ hitP n T K y
  | 0, y => by unfold hitP; split_ifs <;> norm_num
  | K + 1, y => by
    unfold hitP
    split_ifs
    · norm_num
    · exact sum_nonneg fun y' _ =>
        mul_nonneg ((boxConductances n).killedTransition_nonneg _ _) (hitP_nonneg K y')

theorem hitP_le_one : ∀ K y, hitP n T K y ≤ 1
  | 0, y => by unfold hitP; split_ifs <;> norm_num
  | K + 1, y => by
    unfold hitP
    split_ifs
    · exact le_rfl
    · calc ∑ y', (boxConductances n).killedTransition y y' * hitP n T K y'
          ≤ ∑ y', (boxConductances n).killedTransition y y' * 1 := by
            apply sum_le_sum; intro y' _
            exact mul_le_mul_of_nonneg_left (hitP_le_one K y')
              ((boxConductances n).killedTransition_nonneg _ _)
        _ ≤ 1 := by simpa using (boxConductances n).killedTransition_row_le y

theorem hitP_mono_succ : ∀ K y, hitP n T K y ≤ hitP n T (K + 1) y
  | 0, y => by
    show (if y ∈ T then 1 else 0) ≤ (if y ∈ T then 1 else _)
    split_ifs
    · exact le_rfl
    · exact sum_nonneg fun y' _ =>
        mul_nonneg ((boxConductances n).killedTransition_nonneg _ _) (hitP_nonneg n T 0 y')
  | K + 1, y => by
    show (if y ∈ T then 1 else _) ≤ (if y ∈ T then 1 else _)
    split_ifs
    · exact le_rfl
    · apply sum_le_sum; intro y' _
      exact mul_le_mul_of_nonneg_left (hitP_mono_succ K y')
        ((boxConductances n).killedTransition_nonneg _ _)

theorem hitP_monotone (y : DGFFSite n) : Monotone (fun K => hitP n T K y) :=
  monotone_nat_of_le_succ (fun K => hitP_mono_succ n T K y)

 
def hitLim (y : DGFFSite n) : ℝ := ⨆ K, hitP n T K y

theorem tendsto_hitP (y : DGFFSite n) :
    Tendsto (fun K => hitP n T K y) atTop (𝓝 (hitLim n T y)) :=
  tendsto_atTop_ciSup (hitP_monotone n T y) ⟨1, by
    rintro _ ⟨K, rfl⟩; exact hitP_le_one n T K y⟩

theorem hitLim_of_mem (y : DGFFSite n) (hy : y ∈ T) : hitLim n T y = 1 := by
  have h : ∀ K, hitP n T K y = 1 := by
    intro K; cases K <;> simp [hitP, hy]
  exact tendsto_nhds_unique (tendsto_hitP n T y) (by simp [h])

theorem hitLim_harmonic (y : DGFFSite n) (hy : y ∉ T) :
    hitLim n T y = ∑ y', (boxConductances n).killedTransition y y' * hitLim n T y' := by
  have h1 : Tendsto (fun K => hitP n T (K + 1) y) atTop (𝓝 (hitLim n T y)) :=
    (tendsto_hitP n T y).comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun K => hitP n T (K + 1) y) atTop
      (𝓝 (∑ y', (boxConductances n).killedTransition y y' * hitLim n T y')) := by
    have : (fun K => hitP n T (K + 1) y) =
        fun K => ∑ y', (boxConductances n).killedTransition y y' * hitP n T K y' := by
      funext K; simp [hitP, hy]
    rw [this]
    exact tendsto_finset_sum _ fun y' _ => (tendsto_hitP n T y').const_mul _
  exact tendsto_nhds_unique h1 h2

theorem hitLim_nonneg (y : DGFFSite n) : 0 ≤ hitLim n T y :=
  ge_of_tendsto' (tendsto_hitP n T y) (fun K => hitP_nonneg n T K y)

theorem encircles_consExc (y : DGFFSite n) (γ : Excursion (DGFFSite n))
    (h : ExcursionEncircles n γ) : ExcursionEncircles n (consExc y γ) := by
  obtain ⟨p, hp, hv⟩ := h
  exact ⟨p, hp, fun z hz => by obtain ⟨j, hj⟩ := hv z hz; exact ⟨j.succ, by rw [← hj]; rfl⟩⟩

 
theorem pathMass_ge_hitP (p₀ : ℝ) (hp₀ : 0 ≤ p₀)
    (hT : ∀ x ∈ T, ENNReal.ofReal p₀ ≤ pathMass n (ExcursionEncircles n) x) :
    ∀ K y, ENNReal.ofReal (p₀ * hitP n T K y) ≤ pathMass n (ExcursionEncircles n) y
  | 0, y => by
    unfold hitP
    split_ifs with hy
    · simpa using hT y hy
    · simp
  | K + 1, y => by
    unfold hitP
    split_ifs with hy
    · simpa using hT y hy
    · calc ENNReal.ofReal (p₀ * ∑ y', (boxConductances n).killedTransition y y' * hitP n T K y')
          = ∑ y', ENNReal.ofReal ((boxConductances n).killedTransition y y') *
              ENNReal.ofReal (p₀ * hitP n T K y') := by
            rw [mul_sum, ENNReal.ofReal_sum_of_nonneg]
            · apply sum_congr rfl; intro y' _
              rw [← ENNReal.ofReal_mul ((boxConductances n).killedTransition_nonneg _ _)]
              ring_nf
            · intro y' _
              exact mul_nonneg hp₀ (mul_nonneg ((boxConductances n).killedTransition_nonneg _ _)
                (hitP_nonneg n T K y'))
        _ ≤ ∑ y', ENNReal.ofReal ((boxConductances n).killedTransition y y') *
              pathMass n (fun γ => ExcursionEncircles n (consExc y γ)) y' := by
            apply sum_le_sum; intro y' _
            gcongr
            exact (pathMass_ge_hitP p₀ hp₀ hT K y').trans
              (pathMass_mono n (fun γ h => encircles_consExc n y γ h) y')
        _ ≤ _ := pathMass_first_step n _ y

theorem pathMass_ge_hitLim (p₀ : ℝ) (hp₀ : 0 ≤ p₀)
    (hT : ∀ x ∈ T, ENNReal.ofReal p₀ ≤ pathMass n (ExcursionEncircles n) x) (y : DGFFSite n) :
    ENNReal.ofReal (p₀ * hitLim n T y) ≤ pathMass n (ExcursionEncircles n) y := by
  have ht : Tendsto (fun K => ENNReal.ofReal (p₀ * hitP n T K y)) atTop
      (𝓝 (ENNReal.ofReal (p₀ * hitLim n T y))) :=
    ENNReal.tendsto_ofReal ((tendsto_hitP n T y).const_mul p₀)
  exact le_of_tendsto' ht (fun K => pathMass_ge_hitP n T p₀ hp₀ hT K y)

end SupercriticalLQGUniqueness.B2.QPos.P3
