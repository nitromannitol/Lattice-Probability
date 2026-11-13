/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P7SupBound at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P7Compare2D
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.FieldMax
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.LenObs

 









set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Real Finset Filter Topology
open scoped ENNReal
open LQGMetric LQGMetric.WhiteNoise LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.QPos.P7

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

lemma cKer_pos : 0 < cKer := by
  unfold cKer; have := cSlice_nonneg; have := Real.pi_pos; positivity

 
lemma tail_of_norm_le (hW : IsWhiteNoise P W) (f : WNSpace) {C : ℝ} (hC : 0 < C)
    (hf : ‖f‖ ^ 2 ≤ C) {y : ℝ} (hy : 0 < y) :
    P {ω | y ≤ |W f ω|} ≤ ENNReal.ofReal (2 * Real.exp (-y ^ 2 / (2 * C))) := by
  haveI := hW.isProbabilityMeasure
  by_cases h0 : ‖f‖ = 0
  · have hz : f = 0 := norm_eq_zero.mp h0
    have hae := hW.ae_eq_zero_of_norm_eq_zero (fun _ : Unit => f) (fun _ => 1) (by simp [hz])
    have hnull : P {ω | y ≤ |W f ω|} = 0 := by
      refine measure_mono_null ?_ (ae_iff.mp hae)
      intro ω hω
      simp only [Set.mem_setOf_eq, Fintype.univ_unit, Finset.sum_singleton, one_mul,
        Pi.zero_apply] at hω ⊢
      intro h; rw [h, abs_zero] at hω; linarith
    rw [hnull]; exact zero_le
  · have hv : 0 < ((‖f‖ ^ 2).toNNReal : ℝ) := by
      rw [Real.coe_toNNReal _ (sq_nonneg _)]; positivity
    have h := tail_abs_of_hasLaw hv (hW.hasLaw_single f) hy.le
    rw [Real.coe_toNNReal _ (sq_nonneg _)] at h
    have hfpos : 0 < ‖f‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    have harg : -y ^ 2 / (2 * ‖f‖ ^ 2) ≤ -y ^ 2 / (2 * C) := by
      rw [neg_div, neg_div, neg_le_neg_iff]
      exact div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by linarith)
    have hmono : 2 * Real.exp (-y ^ 2 / (2 * ‖f‖ ^ 2)) ≤ 2 * Real.exp (-y ^ 2 / (2 * C)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr harg) (by norm_num)
    rw [← ofReal_measureReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal (h.trans hmono)

 
lemma site_tail (hW : IsWhiteNoise P W) {n : ℕ} (hn : 4 ≤ n) (v : DGFFSite n)
    (hv1 : |(v.1.1 : ℝ)| ≤ 4 / 5 * Nn n) (hv2 : |(v.1.2 : ℝ)| ≤ 4 / 5 * Nn n)
    {y : ℝ} (hy : 0 < y) :
    P {ω | y < |W (fKerL2 n v) ω - phiMN W P 0 n (siteZ n v) ω|} ≤
      ENNReal.ofReal (2 * Real.exp (-y ^ 2 / (2 * cKer))) := by
  set k := phiKernelL2 ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ 0) (siteZ n v)
  have hφ := (isPhiVersion_phiMN hW (Nat.zero_le n)).ae_eq (siteZ n v)
  have hzero : ‖∑ i, (![1, -1, Real.sqrt π] : Fin 3 → ℝ) i •
      (![fKerL2 n v - Real.sqrt π • k, fKerL2 n v, k] : Fin 3 → WNSpace) i‖ = 0 := by
    rw [norm_eq_zero]
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, one_smul, neg_smul]
    abel
  have hlin := hW.ae_eq_zero_of_norm_eq_zero ![fKerL2 n v - Real.sqrt π • k, fKerL2 n v, k]
    ![1, -1, Real.sqrt π] hzero
  have hsub : {ω | y < |W (fKerL2 n v) ω - phiMN W P 0 n (siteZ n v) ω|} ⊆
      {ω | y ≤ |W (fKerL2 n v - Real.sqrt π • k) ω|} ∪
        ({ω | ¬ phiMN W P 0 n (siteZ n v) ω = phi W ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ 0) (siteZ n v) ω} ∪
          {ω | ¬ (∑ i, ![1, -1, Real.sqrt π] i *
            W (![fKerL2 n v - Real.sqrt π • k, fKerL2 n v, k] i) ω) = 0}) := by
    intro ω hω
    by_contra hnot
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not, not_le] at hnot hω
    obtain ⟨h1, h2, h3⟩ := hnot
    simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h3
    rw [h2] at hω
    simp only [phi] at hω
    have : W (fKerL2 n v) ω - Real.sqrt π * W k ω = W (fKerL2 n v - Real.sqrt π • k) ω := by
      linarith
    rw [this] at hω
    linarith
  have hk : ‖fKerL2 n v - Real.sqrt π • k‖ ^ 2 ≤ cKer := norm_fKer_sub_phi_sq_le hn v hv1 hv2
  calc P {ω | y < |W (fKerL2 n v) ω - phiMN W P 0 n (siteZ n v) ω|}
      ≤ P ({ω | y ≤ |W (fKerL2 n v - Real.sqrt π • k) ω|} ∪
        ({ω | ¬ phiMN W P 0 n (siteZ n v) ω = phi W ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ 0) (siteZ n v) ω} ∪
          {ω | ¬ (∑ i, ![1, -1, Real.sqrt π] i *
            W (![fKerL2 n v - Real.sqrt π • k, fKerL2 n v, k] i) ω) = 0})) := measure_mono hsub
    _ ≤ P {ω | y ≤ |W (fKerL2 n v - Real.sqrt π • k) ω|} +
        (P {ω | ¬ phiMN W P 0 n (siteZ n v) ω =
            phi W ((2 : ℝ)⁻¹ ^ n) ((2 : ℝ)⁻¹ ^ 0) (siteZ n v) ω} +
          P {ω | ¬ (∑ i, ![1, -1, Real.sqrt π] i *
            W (![fKerL2 n v - Real.sqrt π • k, fKerL2 n v, k] i) ω) = 0}) :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
    _ = P {ω | y ≤ |W (fKerL2 n v - Real.sqrt π • k) ω|} := by
        rw [ae_iff.mp hφ, show P {ω | ¬ (∑ i, ![1, -1, Real.sqrt π] i *
            W (![fKerL2 n v - Real.sqrt π • k, fKerL2 n v, k] i) ω) = 0} = 0 from by
          have := ae_iff.mp hlin; simpa using this]
        simp
    _ ≤ _ := tail_of_norm_le hW _ cKer_pos hk hy

lemma card_dgffSite_le (n : ℕ) : (Fintype.card (DGFFSite n) : ℝ) ≤ 4 ^ (n + 1) := by
  have hc : Fintype.card (DGFFSite n) = (interiorSites n).card := by
    simp [DGFFSite]
  rw [hc]
  simp only [interiorSites, interiorRadius]
  rw [Finset.product_eq_sprod, Finset.card_product, Int.card_Icc]
  have : (2 : ℤ) ^ n - 1 + 1 - -((2 : ℤ) ^ n - 1) = 2 ^ (n + 1) - 1 := by ring
  rw [this]
  have h1 : ((2 : ℤ) ^ (n + 1) - 1).toNat ≤ 2 ^ (n + 1) := by
    have h0 : (0 : ℤ) ≤ 2 ^ (n + 1) - 1 := by
      have : (1 : ℤ) ≤ 2 ^ (n + 1) := one_le_pow₀ (by norm_num)
      linarith
    have ht := Int.toNat_of_nonneg h0
    have h2 : (((2 : ℤ) ^ (n + 1) - 1).toNat : ℤ) ≤ ((2 ^ (n + 1) : ℕ) : ℤ) := by
      rw [ht]; push_cast; linarith
    exact_mod_cast h2
  have h2 : (((2 : ℤ) ^ (n + 1) - 1).toNat * ((2 : ℤ) ^ (n + 1) - 1).toNat : ℝ) ≤
      (2 ^ (n + 1) : ℕ) * (2 ^ (n + 1) : ℕ) := by
    have h1' : (((2 : ℤ) ^ (n + 1) - 1).toNat : ℝ) ≤ (2 ^ (n + 1) : ℕ) := by exact_mod_cast h1
    exact mul_le_mul h1' h1' (by positivity) (by positivity)
  calc ((((2 : ℤ) ^ (n + 1) - 1).toNat * ((2 : ℤ) ^ (n + 1) - 1).toNat : ℕ) : ℝ)
      = (((2 : ℤ) ^ (n + 1) - 1).toNat * ((2 : ℤ) ^ (n + 1) - 1).toNat : ℝ) := by push_cast; rfl
    _ ≤ (2 ^ (n + 1) : ℕ) * (2 ^ (n + 1) : ℕ) := h2
    _ = 4 ^ (n + 1) := by push_cast; rw [← mul_pow]; norm_num

 
lemma tendsto_pow_four_mul_exp {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n : ℕ => (4 : ℝ) ^ (n + 1) * Real.exp (-a * (n : ℝ) ^ 2)) atTop (𝓝 0) := by
  have h4 : ∀ n : ℕ, (4 : ℝ) ^ (n + 1) = 4 * Real.exp (n * Real.log 4) := by
    intro n
    rw [pow_succ, mul_comm, ← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
    ring_nf
  have hexp : Tendsto (fun n : ℕ => (n : ℝ) * Real.log 4 - a * (n : ℝ) ^ 2) atTop atBot := by
    have hlin : Tendsto (fun n : ℕ => -(n : ℝ)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop
    refine tendsto_atBot_mono' atTop ?_ hlin
    filter_upwards [eventually_ge_atTop ⌈(Real.log 4 + 1) / a⌉₊] with n hn
    have hn' : (Real.log 4 + 1) / a ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hn)
    rw [div_le_iff₀ ha] at hn'
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith
  have := (Real.tendsto_exp_atBot.comp hexp).const_mul 4
  simp only [mul_zero] at this
  refine this.congr fun n => ?_
  simp only [Function.comp, h4]
  rw [mul_assoc, ← Real.exp_add]; ring_nf

 
theorem tendsto_dgff_phi_sup (hW : IsWhiteNoise P W) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => P {ω | ∃ v : DGFFSite n, |(v.1.1 : ℝ)| ≤ 4 / 5 * Nn n ∧
      |(v.1.2 : ℝ)| ≤ 4 / 5 * Nn n ∧
        δ * n < |W (fKerL2 n v) ω - phiMN W P 0 n (siteZ n v) ω|}) atTop (𝓝 0) := by
  set a := δ ^ 2 / (2 * cKer)
  have ha : 0 < a := by have := cKer_pos; positivity
  have hbound : ∀ n : ℕ, 4 ≤ n → 1 ≤ n →
      P {ω | ∃ v : DGFFSite n, |(v.1.1 : ℝ)| ≤ 4 / 5 * Nn n ∧
        |(v.1.2 : ℝ)| ≤ 4 / 5 * Nn n ∧
          δ * n < |W (fKerL2 n v) ω - phiMN W P 0 n (siteZ n v) ω|} ≤
        ENNReal.ofReal (2 * ((4 : ℝ) ^ (n + 1) * Real.exp (-a * (n : ℝ) ^ 2))) := by
    intro n hn hn1
    have hy : 0 < δ * n := by have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
                              positivity
    have hset : {ω | ∃ v : DGFFSite n, |(v.1.1 : ℝ)| ≤ 4 / 5 * Nn n ∧
        |(v.1.2 : ℝ)| ≤ 4 / 5 * Nn n ∧
          δ * n < |W (fKerL2 n v) ω - phiMN W P 0 n (siteZ n v) ω|} ⊆
        ⋃ v : DGFFSite n, {ω | |(v.1.1 : ℝ)| ≤ 4 / 5 * Nn n ∧ |(v.1.2 : ℝ)| ≤ 4 / 5 * Nn n ∧
          δ * n < |W (fKerL2 n v) ω - phiMN W P 0 n (siteZ n v) ω|} := by
      intro ω ⟨v, hv⟩; exact Set.mem_iUnion.mpr ⟨v, hv⟩
    have hsite : ∀ v : DGFFSite n, P {ω | |(v.1.1 : ℝ)| ≤ 4 / 5 * Nn n ∧
        |(v.1.2 : ℝ)| ≤ 4 / 5 * Nn n ∧
          δ * n < |W (fKerL2 n v) ω - phiMN W P 0 n (siteZ n v) ω|} ≤
        ENNReal.ofReal (2 * Real.exp (-(δ * n) ^ 2 / (2 * cKer))) := by
      intro v
      by_cases hv : |(v.1.1 : ℝ)| ≤ 4 / 5 * Nn n ∧ |(v.1.2 : ℝ)| ≤ 4 / 5 * Nn n
      · refine (measure_mono fun ω hω => hω.2.2).trans (site_tail hW hn v hv.1 hv.2 hy)
      · have : {ω | |(v.1.1 : ℝ)| ≤ 4 / 5 * Nn n ∧ |(v.1.2 : ℝ)| ≤ 4 / 5 * Nn n ∧
            δ * n < |W (fKerL2 n v) ω - phiMN W P 0 n (siteZ n v) ω|} = ∅ := by
          ext ω; simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
          intro h; exact hv ⟨h.1, h.2.1⟩
        rw [this, measure_empty]; exact zero_le
    calc _ ≤ P (⋃ v : DGFFSite n, {ω | |(v.1.1 : ℝ)| ≤ 4 / 5 * Nn n ∧
          |(v.1.2 : ℝ)| ≤ 4 / 5 * Nn n ∧
            δ * n < |W (fKerL2 n v) ω - phiMN W P 0 n (siteZ n v) ω|}) := measure_mono hset
      _ ≤ ∑ v : DGFFSite n, P {ω | |(v.1.1 : ℝ)| ≤ 4 / 5 * Nn n ∧
          |(v.1.2 : ℝ)| ≤ 4 / 5 * Nn n ∧
            δ * n < |W (fKerL2 n v) ω - phiMN W P 0 n (siteZ n v) ω|} := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _v : DGFFSite n, ENNReal.ofReal (2 * Real.exp (-(δ * n) ^ 2 / (2 * cKer))) :=
          Finset.sum_le_sum fun v _ => hsite v
      _ = ENNReal.ofReal ((Fintype.card (DGFFSite n) : ℝ) *
            (2 * Real.exp (-(δ * n) ^ 2 / (2 * cKer)))) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      _ ≤ ENNReal.ofReal (2 * ((4 : ℝ) ^ (n + 1) * Real.exp (-a * (n : ℝ) ^ 2))) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have he : Real.exp (-(δ * n) ^ 2 / (2 * cKer)) = Real.exp (-a * (n : ℝ) ^ 2) := by
            congr 1; simp only [a]; ring
          rw [he]
          have hc := card_dgffSite_le n
          nlinarith [Real.exp_pos (-a * (n : ℝ) ^ 2)]
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (2 * ((4 : ℝ) ^ (n + 1) *
      Real.exp (-a * (n : ℝ) ^ 2)))) atTop (𝓝 0) := by
    have := (tendsto_pow_four_mul_exp ha).const_mul 2
    rw [mul_zero] at this
    have h := ENNReal.tendsto_ofReal this
    rwa [ENNReal.ofReal_zero] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun n => zero_le) ?_
  filter_upwards [eventually_ge_atTop 4] with n hn
  exact hbound n hn (by omega)

end SupercriticalLQGUniqueness.B2.QPos.P7
