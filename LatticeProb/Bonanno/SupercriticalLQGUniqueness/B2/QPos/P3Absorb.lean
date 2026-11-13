/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P3Absorb at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.InputsP2
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.DGFFBoxDegree
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.DGFFBoxConnected

 










set_option autoImplicit false
noncomputable section

open Finset Filter Topology Matrix
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.QPos.P3

open Classical

 

def exitW (n : ℕ) (γ : Excursion (DGFFSite n)) : ℝ :=
  (∏ j : Fin γ.1, (boxConductances n).killedTransition (γ.2 j.castSucc) (γ.2 j.succ)) *
    ((boxConductances n).boundary (γ.2 (Fin.last γ.1)) /
      (boxConductances n).totalRate (γ.2 (Fin.last γ.1)))

theorem excursionWeight_eq (n : ℕ) (γ : Excursion (DGFFSite n)) :
    (boxConductances n).excursionWeight γ = (boxConductances n).boundary (γ.2 0) * exitW n γ := by
  unfold WiredConductances.excursionWeight exitW; ring

theorem exitW_nonneg (n : ℕ) (γ : Excursion (DGFFSite n)) : 0 ≤ exitW n γ := by
  unfold exitW
  refine mul_nonneg (prod_nonneg fun j _ => ?_)
    (div_nonneg ((boxConductances n).boundary_nonneg _) ((boxConductances n).totalRate_nonneg _))
  exact (boxConductances n).killedTransition_nonneg _ _

 
def pathMass (n : ℕ) (Φ : Excursion (DGFFSite n) → Prop) (y : DGFFSite n) : ℝ≥0∞ :=
  ∑' γ : Excursion (DGFFSite n), if γ.2 0 = y ∧ Φ γ then ENNReal.ofReal (exitW n γ) else 0

theorem pathMass_mono (n : ℕ) {Φ Ψ : Excursion (DGFFSite n) → Prop} (h : ∀ γ, Φ γ → Ψ γ)
    (y : DGFFSite n) : pathMass n Φ y ≤ pathMass n Ψ y := by
  unfold pathMass
  apply ENNReal.tsum_le_tsum
  intro γ
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd ⟨h1.1, h γ h1.2⟩ h2
  · exact bot_le
  · exact le_rfl

 

theorem box_hK (n : ℕ) : (boxConductances n).precision.PosDef := box_precision_posDef n

 
theorem exit_vec_eq (n : ℕ) :
    (fun i => (boxConductances n).boundary i / (boxConductances n).totalRate i) =
      (fun _ => (1 : ℝ)) - (boxConductances n).killedTransition *ᵥ (fun _ => (1 : ℝ)) := by
  funext i
  have hr := ((boxConductances n).totalRate_pos (box_hK n) i).ne'
  simp only [Pi.sub_apply, mulVec, dotProduct, mul_one, WiredConductances.killedTransition]
  rw [← sum_div, eq_sub_iff_add_eq, ← add_div, div_eq_one_iff_eq hr]
  rfl

theorem slice_sum_eq (n : ℕ) (y : DGFFSite n) (k : ℕ) :
    ∑ f : Fin (k + 1) → DGFFSite n, (if f 0 = y then exitW n ⟨k, f⟩ else 0) =
      ((boxConductances n).killedTransition ^ k *ᵥ
        (fun i => (boxConductances n).boundary i / (boxConductances n).totalRate i)) y := by
  have h := sum_path_eq_dotProduct_pow (boxConductances n).killedTransition k
    (fun x => if x = y then (1 : ℝ) else 0)
    (fun i => (boxConductances n).boundary i / (boxConductances n).totalRate i)
  have hl : ∀ f : Fin (k + 1) → DGFFSite n,
      (if f 0 = y then (1 : ℝ) else 0) *
        (∏ j : Fin k, (boxConductances n).killedTransition (f j.castSucc) (f j.succ)) *
        ((boxConductances n).boundary (f (Fin.last k)) /
          (boxConductances n).totalRate (f (Fin.last k))) =
      if f 0 = y then exitW n ⟨k, f⟩ else 0 := by
    intro f; split_ifs <;> simp [exitW]
  simp_rw [hl] at h
  rw [h]
  simp [dotProduct]

theorem hasSum_slices (n : ℕ) (y : DGFFSite n) :
    HasSum (fun k => ((boxConductances n).killedTransition ^ k *ᵥ
        (fun i => (boxConductances n).boundary i / (boxConductances n).totalRate i)) y) 1 := by
  set P := (boxConductances n).killedTransition with hP
  have hterm : ∀ k, (P ^ k *ᵥ
      (fun i => (boxConductances n).boundary i / (boxConductances n).totalRate i)) y =
      (P ^ k *ᵥ (fun _ => (1 : ℝ))) y - (P ^ (k + 1) *ᵥ (fun _ => (1 : ℝ))) y := by
    intro k
    rw [exit_vec_eq, mulVec_sub, mulVec_mulVec, ← pow_succ]
    rfl
  have hnn : ∀ k, 0 ≤ (P ^ k *ᵥ
      (fun i => (boxConductances n).boundary i / (boxConductances n).totalRate i)) y := by
    intro k
    rw [← slice_sum_eq]
    exact sum_nonneg fun f _ => by split_ifs; exact exitW_nonneg n _; exact le_rfl
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  simp_rw [hterm]
  simp_rw [sum_range_sub' (fun k => (P ^ k *ᵥ (fun _ => (1 : ℝ))) y)]
  have h0 : Tendsto (fun N => (P ^ N *ᵥ (fun _ => (1 : ℝ))) y) atTop (𝓝 0) := by
    have : ∀ N, (P ^ N *ᵥ (fun _ => (1 : ℝ))) y = ∑ j, (P ^ N) y j := by
      intro N; simp [mulVec, dotProduct]
    simp_rw [this]
    rw [show (0 : ℝ) = ∑ _j : DGFFSite n, (0 : ℝ) by simp]
    exact tendsto_finset_sum _ fun j _ =>
      (boxConductances n).killedTransition_pow_apply_tendsto_zero (box_hK n) y j
  have h1 : (P ^ 0 *ᵥ (fun _ => (1 : ℝ))) y = 1 := by simp
  rw [h1]
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub h0

 
theorem pathMass_true (n : ℕ) (y : DGFFSite n) : pathMass n (fun _ => True) y = 1 := by
  have e : pathMass n (fun _ => True) y = ∑' γ : Excursion (DGFFSite n),
      if γ.2 0 = y then ENNReal.ofReal (exitW n γ) else 0 := by
    unfold pathMass; congr 1; funext γ; by_cases h : γ.2 0 = y <;> simp [h]
  rw [e, ENNReal.tsum_sigma']
  have hk : ∀ k, ∑' f : Fin (k + 1) → DGFFSite n,
      (if f 0 = y then ENNReal.ofReal (exitW n ⟨k, f⟩) else 0) =
      ENNReal.ofReal (((boxConductances n).killedTransition ^ k *ᵥ
        (fun i => (boxConductances n).boundary i / (boxConductances n).totalRate i)) y) := by
    intro k
    rw [tsum_fintype, ← slice_sum_eq, ENNReal.ofReal_sum_of_nonneg]
    · apply sum_congr rfl; intro f _; by_cases h : f 0 = y <;> simp [h]
    · intro f _; split_ifs; exact exitW_nonneg n _; exact le_rfl
  refine (tsum_congr hk).trans ?_
  rw [← ENNReal.ofReal_tsum_of_nonneg _ (hasSum_slices n y).summable, (hasSum_slices n y).tsum_eq]
  · simp
  · intro k
    rw [← slice_sum_eq]
    exact sum_nonneg fun f _ => by split_ifs; exact exitW_nonneg n _; exact le_rfl

 

 
def consExc {V : Type*} (y : V) (γ : Excursion V) : Excursion V := ⟨γ.1 + 1, Fin.cons y γ.2⟩

theorem consExc_injective {V : Type*} (y : V) : Function.Injective (consExc y) := by
  rintro ⟨k, f⟩ ⟨k', f'⟩ h
  simp only [consExc, Sigma.mk.injEq] at h
  obtain ⟨hk, hf⟩ := h
  have hk' : k = k' := by omega
  subst hk'
  have := (Fin.cons_right_injective (α := fun _ => V) y) (eq_of_heq hf)
  rw [this]

theorem prod_cons_path {V : Type*} (A : Matrix V V ℝ) (y : V) (k : ℕ) (f : Fin (k + 1) → V) :
    ∏ j : Fin (k + 1), A ((Fin.cons y f : Fin (k + 2) → V) j.castSucc)
        ((Fin.cons y f : Fin (k + 2) → V) j.succ) =
      A y (f 0) * ∏ j : Fin k, A (f j.castSucc) (f j.succ) := by
  rw [Fin.prod_univ_succ]
  simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.succ_zero_eq_one, Fin.cons_one, Fin.cons_succ]
  have hcs : ∀ j : Fin k, (j.succ.castSucc : Fin (k + 2)) = j.castSucc.succ :=
    fun j => (Fin.succ_castSucc j).symm
  simp only [hcs, Fin.cons_succ]

theorem exitW_consExc (n : ℕ) (y : DGFFSite n) (γ : Excursion (DGFFSite n)) :
    exitW n (consExc y γ) = (boxConductances n).killedTransition y (γ.2 0) * exitW n γ := by
  obtain ⟨k, f⟩ := γ
  show (∏ j : Fin (k + 1), (boxConductances n).killedTransition
        ((Fin.cons y f : Fin (k + 2) → DGFFSite n) j.castSucc)
        ((Fin.cons y f : Fin (k + 2) → DGFFSite n) j.succ)) *
      ((boxConductances n).boundary ((Fin.cons y f : Fin (k + 2) → DGFFSite n) (Fin.last (k + 1))) /
        (boxConductances n).totalRate ((Fin.cons y f : Fin (k + 2) → DGFFSite n) (Fin.last (k + 1)))) =
    (boxConductances n).killedTransition y (f 0) * exitW n ⟨k, f⟩
  rw [prod_cons_path]
  have hlast : (Fin.last (k + 1)) = (Fin.last k).succ := (Fin.succ_last k).symm
  rw [hlast, Fin.cons_succ]
  simp only [exitW]
  ring

 
theorem pathMass_first_step (n : ℕ) (Φ : Excursion (DGFFSite n) → Prop) (y : DGFFSite n) :
    ∑ y' : DGFFSite n, ENNReal.ofReal ((boxConductances n).killedTransition y y') *
        pathMass n (fun γ => Φ (consExc y γ)) y' ≤ pathMass n Φ y := by
  unfold pathMass
  simp_rw [← ENNReal.tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  have hpt : ∀ γ : Excursion (DGFFSite n),
      ∑ y' : DGFFSite n, ENNReal.ofReal ((boxConductances n).killedTransition y y') *
        (if γ.2 0 = y' ∧ Φ (consExc y γ) then ENNReal.ofReal (exitW n γ) else 0) =
      (if (consExc y γ).2 0 = y ∧ Φ (consExc y γ) then
        ENNReal.ofReal (exitW n (consExc y γ)) else 0) := by
    intro γ
    have h0 : (consExc y γ).2 0 = y := rfl
    rw [sum_eq_single (γ.2 0)]
    · by_cases hΦ : Φ (consExc y γ)
      · rw [if_pos ⟨rfl, hΦ⟩, if_pos ⟨h0, hΦ⟩, exitW_consExc,
          ENNReal.ofReal_mul ((boxConductances n).killedTransition_nonneg _ _)]
      · rw [if_neg (fun h => hΦ h.2), if_neg (fun h => hΦ h.2)]; simp
    · intro b _ hb; rw [if_neg (fun h => hb h.1.symm)]; simp
    · intro h; exact absurd (mem_univ _) h
  simp_rw [hpt]
  exact ENNReal.tsum_comp_le_tsum_of_injective (consExc_injective y)
    (fun γ' : Excursion (DGFFSite n) =>
      if γ'.2 0 = y ∧ Φ γ' then ENNReal.ofReal (exitW n γ') else 0)

 

 
theorem circuitSum_eq (n : ℕ) :
    ENNReal.ofReal (∑' γ : Excursion (DGFFSite n),
        {γ | ExcursionEncircles n γ}.indicator (boxConductances n).excursionWeight γ) =
      ∑ y : DGFFSite n, ENNReal.ofReal ((boxConductances n).boundary y) *
        pathMass n (ExcursionEncircles n) y := by
  have hsum : Summable fun γ : Excursion (DGFFSite n) =>
      {γ | ExcursionEncircles n γ}.indicator (boxConductances n).excursionWeight γ :=
    ((boxConductances n).summable_excursionWeight (box_hK n)).indicator _
  rw [ENNReal.ofReal_tsum_of_nonneg (fun γ => Set.indicator_nonneg
    (fun γ _ => (boxConductances n).excursionWeight_nonneg γ) γ) hsum]
  unfold pathMass
  simp_rw [← ENNReal.tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  congr 1
  funext γ
  rw [sum_eq_single (γ.2 0)]
  · simp only [true_and]
    by_cases hE : ExcursionEncircles n γ
    · rw [Set.indicator_of_mem (show γ ∈ {γ | ExcursionEncircles n γ} from hE), if_pos hE,
        excursionWeight_eq, ENNReal.ofReal_mul ((boxConductances n).boundary_nonneg _)]
    · rw [Set.indicator_of_notMem (show γ ∉ {γ | ExcursionEncircles n γ} from hE), if_neg hE]
      simp
  · intro b _ hb; simp [Ne.symm hb]
  · intro h; exact absurd (mem_univ _) h

end SupercriticalLQGUniqueness.B2.QPos.P3
