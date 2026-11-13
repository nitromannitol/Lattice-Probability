/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P8Charge at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P8Chord
import Mathlib.Data.ZMod.Basic

 










set_option autoImplicit false
noncomputable section

open MeasureTheory Set Finset
open scoped ENNReal
open LQGMetric LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.QPos.P8

 
def cpt (N : ℕ) (u : ℤ × ℤ) : ℂ := ⟨(u.1 : ℝ) / N, (u.2 : ℝ) / N⟩

 
def cls (u : ℤ × ℤ) : ZMod 8 × ZMod 8 := ((u.1 : ZMod 8), (u.2 : ZMod 8))

lemma norm_cpt_sub_ge {N : ℕ} (hN : 0 < N) {u u' : ℤ × ℤ} (hcls : cls u = cls u') (hne : u ≠ u') :
    8 / (N : ℝ) ≤ ‖cpt N u - cpt N u'‖ := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  simp only [cls, Prod.mk.injEq] at hcls
  have h1 : (8 : ℤ) ∣ u.1 - u'.1 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (u.1 - u'.1) 8).mp (by
      push_cast; rw [hcls.1, sub_self])
    exact_mod_cast this
  have h2 : (8 : ℤ) ∣ u.2 - u'.2 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (u.2 - u'.2) 8).mp (by
      push_cast; rw [hcls.2, sub_self])
    exact_mod_cast this
  have hbig : 8 ≤ |u.1 - u'.1| ∨ 8 ≤ |u.2 - u'.2| := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨k1, hk1⟩ := h1
    obtain ⟨k2, hk2⟩ := h2
    have e1 : k1 = 0 := by
      have := hcon.1; rw [hk1, abs_mul] at this; norm_num at this
      rcases lt_trichotomy k1 0 with h | h | h
      · have : 1 ≤ |k1| := Int.one_le_abs h.ne; omega
      · exact h
      · have : 1 ≤ |k1| := Int.one_le_abs h.ne'; omega
    have e2 : k2 = 0 := by
      have := hcon.2; rw [hk2, abs_mul] at this; norm_num at this
      rcases lt_trichotomy k2 0 with h | h | h
      · have : 1 ≤ |k2| := Int.one_le_abs h.ne; omega
      · exact h
      · have : 1 ≤ |k2| := Int.one_le_abs h.ne'; omega
    apply hne
    rw [e1, mul_zero] at hk1
    rw [e2, mul_zero] at hk2
    exact Prod.ext (by omega) (by omega)
  rcases hbig with h | h
  · have hre : |(cpt N u - cpt N u').re| ≤ ‖cpt N u - cpt N u'‖ := Complex.abs_re_le_norm _
    have : (cpt N u - cpt N u').re = ((u.1 - u'.1 : ℤ) : ℝ) / N := by
      simp only [cpt, Complex.sub_re]; push_cast; ring
    rw [this, abs_div, abs_of_pos hNp] at hre
    have h' : (8 : ℝ) ≤ |((u.1 - u'.1 : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast h
    calc 8 / (N : ℝ) ≤ |((u.1 - u'.1 : ℤ) : ℝ)| / N := div_le_div_of_nonneg_right h' hNp.le
      _ ≤ _ := hre
  · have him : |(cpt N u - cpt N u').im| ≤ ‖cpt N u - cpt N u'‖ := Complex.abs_im_le_norm _
    have : (cpt N u - cpt N u').im = ((u.2 - u'.2 : ℤ) : ℝ) / N := by
      simp only [cpt, Complex.sub_im]; push_cast; ring
    rw [this, abs_div, abs_of_pos hNp] at him
    have h' : (8 : ℝ) ≤ |((u.2 - u'.2 : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast h
    calc 8 / (N : ℝ) ≤ |((u.2 - u'.2 : ℤ) : ℝ)| / N := div_le_div_of_nonneg_right h' hNp.le
      _ ≤ _ := him

 
theorem charge {P : ℝ → ℂ} {z w : ℂ} (hP : IsPiecewiseC1Path P z w) {N : ℕ} (hN : 0 < N)
    (hzw : 6 / (N : ℝ) < ‖w - z‖) (φ : ℂ → ℝ) {ξ θ : ℝ} (hξ : 0 ≤ ξ) (T : Finset (ℤ × ℤ))
    (hT : ∀ u ∈ T, ∃ s ∈ Icc (0 : ℝ) 1, ‖cpt N u - P s‖ ≤ 2 / N)
    (hosc : ∀ u ∈ T, ∀ t ∈ Icc (0 : ℝ) 1, ‖cpt N u - P t‖ ≤ 3 / N →
      φ (cpt N u) ≤ φ (P t) + θ) :
    ∑ u ∈ T, ENNReal.ofReal (Real.exp (ξ * φ (cpt N u))) ≤
      ENNReal.ofReal (64 * N * Real.exp (ξ * θ)) * lfppLen ξ φ P := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hr : 2 / (N : ℝ) < 3 / N := div_lt_div_of_pos_right (by norm_num) hNp
  choose s hs hsd using hT
  have hfar : ∀ u (hu : u ∈ T), 3 / (N : ℝ) ≤ ‖P 0 - cpt N u‖ ∨ 3 / (N : ℝ) ≤ ‖P 1 - cpt N u‖ := by
    intro u hu
    by_contra hcon
    push_neg at hcon
    have h := norm_add_le (P 1 - cpt N u) (cpt N u - P 0)
    rw [show P 1 - cpt N u + (cpt N u - P 0) = P 1 - P 0 by ring,
      norm_sub_rev (cpt N u) (P 0)] at h
    rw [hP.source, hP.target] at h hcon
    have e6 : (6 : ℝ) / N = 3 / N + 3 / N := by ring
    linarith [hcon.1, hcon.2]
  have hex : ∀ u (hu : u ∈ T), ∃ a b : ℝ, 0 ≤ a ∧ a ≤ b ∧ b ≤ 1 ∧
      (∀ t ∈ Ioo a b, ‖P t - cpt N u‖ < 3 / N) ∧ 3 / (N : ℝ) - 2 / N ≤ ‖P b - P a‖ := by
    intro u hu
    refine exit_interval hP hr (hs u hu) ?_ (hfar u hu)
    rw [norm_sub_rev]; exact hsd u hu
  choose a b ha hab hb hin hchord using hex
  set F : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (ξ * φ (P t)) * ‖deriv P t‖)
  set I : ℤ × ℤ → Set ℝ := fun u => if hu : u ∈ T then Ioo (a u hu) (b u hu) else ∅
  
  have hper : ∀ u ∈ T, ENNReal.ofReal (Real.exp (ξ * φ (cpt N u))) ≤
      ENNReal.ofReal (N * Real.exp (ξ * θ)) * ∫⁻ t in I u, F t := by
    intro u hu
    simp only [I, dif_pos hu]
    have hlow : ∀ t ∈ Ioo (a u hu) (b u hu),
        ENNReal.ofReal (Real.exp (ξ * φ (cpt N u) - ξ * θ)) * ENNReal.ofReal ‖deriv P t‖ ≤ F t := by
      intro t ht
      have htI : t ∈ Icc (0 : ℝ) 1 := ⟨le_trans (ha u hu) ht.1.le, le_trans ht.2.le (hb u hu)⟩
      have hd : ‖cpt N u - P t‖ ≤ 3 / N := by rw [norm_sub_rev]; exact (hin u hu t ht).le
      have hφ := hosc u hu t htI hd
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      exact Real.exp_le_exp.mpr (by nlinarith)
    have hint : ENNReal.ofReal (Real.exp (ξ * φ (cpt N u) - ξ * θ)) *
        ∫⁻ t in Ioo (a u hu) (b u hu), ENNReal.ofReal ‖deriv P t‖ ≤
        ∫⁻ t in Ioo (a u hu) (b u hu), F t := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      exact setLIntegral_mono' measurableSet_Ioo hlow
    have hch := ofReal_chord_le_sub hP (ha u hu) (hab u hu) (hb u hu)
    have hch' : ENNReal.ofReal (1 / N) ≤ ENNReal.ofReal ‖P (b u hu) - P (a u hu)‖ := by
      refine ENNReal.ofReal_le_ofReal ?_
      have := hchord u hu
      have e : 3 / (N : ℝ) - 2 / N = 1 / N := by ring
      linarith
    calc ENNReal.ofReal (Real.exp (ξ * φ (cpt N u)))
        = ENNReal.ofReal (N * Real.exp (ξ * θ) *
            (Real.exp (ξ * φ (cpt N u) - ξ * θ) * (1 / N))) := by
          congr 1; rw [Real.exp_sub]; field_simp
      _ = ENNReal.ofReal (N * Real.exp (ξ * θ)) *
            (ENNReal.ofReal (Real.exp (ξ * φ (cpt N u) - ξ * θ)) * ENNReal.ofReal (1 / N)) := by
          rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ N * Real.exp (ξ * θ) by positivity),
            ENNReal.ofReal_mul (show (0 : ℝ) ≤ Real.exp (ξ * φ (cpt N u) - ξ * θ) by
              positivity)]
      _ ≤ ENNReal.ofReal (N * Real.exp (ξ * θ)) *
            (ENNReal.ofReal (Real.exp (ξ * φ (cpt N u) - ξ * θ)) *
              ∫⁻ t in Ioo (a u hu) (b u hu), ENNReal.ofReal ‖deriv P t‖) := by
          gcongr; exact hch'.trans hch
      _ ≤ _ := by gcongr
  
  have hdisj : ∀ r : ZMod 8 × ZMod 8, Set.PairwiseDisjoint
      (↑(T.filter fun u => cls u = r) : Set (ℤ × ℤ)) I := by
    intro r u hu u' hu' hne
    simp only [coe_filter, Set.mem_setOf_eq] at hu hu'
    show Disjoint (I u) (I u')
    simp only [I, dif_pos hu.1, dif_pos hu'.1]
    rw [Set.disjoint_left]
    intro t ht ht'
    have h1 := hin u hu.1 t ht
    have h2 := hin u' hu'.1 t ht'
    have h3 := norm_cpt_sub_ge hN (hu.2.trans hu'.2.symm) hne
    have h4 := norm_add_le (cpt N u - P t) (P t - cpt N u')
    rw [show cpt N u - P t + (P t - cpt N u') = cpt N u - cpt N u' by ring,
      norm_sub_rev (cpt N u) (P t)] at h4
    have : 3 / (N : ℝ) + 3 / N < 8 / N := by
      rw [← add_div]; exact div_lt_div_of_pos_right (by norm_num) hNp
    linarith
  have hmeas : ∀ u, MeasurableSet (I u) := by
    intro u; simp only [I]; split_ifs
    · exact measurableSet_Ioo
    · exact MeasurableSet.empty
  have hsub : ∀ u, I u ⊆ Icc (0 : ℝ) 1 := by
    intro u t ht; simp only [I] at ht; split_ifs at ht with hu
    · exact ⟨le_trans (ha u hu) ht.1.le, le_trans ht.2.le (hb u hu)⟩
    · exact absurd ht (Set.notMem_empty t)
  
  have hclass : ∀ r : ZMod 8 × ZMod 8, ∑ u ∈ T.filter (fun u => cls u = r),
      ENNReal.ofReal (Real.exp (ξ * φ (cpt N u))) ≤
      ENNReal.ofReal (N * Real.exp (ξ * θ)) * lfppLen ξ φ P := by
    intro r
    calc ∑ u ∈ T.filter (fun u => cls u = r), ENNReal.ofReal (Real.exp (ξ * φ (cpt N u)))
        ≤ ∑ u ∈ T.filter (fun u => cls u = r),
            ENNReal.ofReal (N * Real.exp (ξ * θ)) * ∫⁻ t in I u, F t :=
          Finset.sum_le_sum fun u hu => hper u (mem_filter.mp hu).1
      _ = ENNReal.ofReal (N * Real.exp (ξ * θ)) *
            ∫⁻ t in ⋃ u ∈ T.filter (fun u => cls u = r), I u, F t := by
          rw [← Finset.mul_sum, lintegral_biUnion_finset (hdisj r) (fun u _ => hmeas u)]
      _ ≤ ENNReal.ofReal (N * Real.exp (ξ * θ)) * ∫⁻ t in Icc (0 : ℝ) 1, F t := by
          gcongr
          exact Set.iUnion₂_subset fun u _ => hsub u
      _ = ENNReal.ofReal (N * Real.exp (ξ * θ)) * lfppLen ξ φ P := rfl
  rw [← Finset.sum_fiberwise T cls]
  calc ∑ r : ZMod 8 × ZMod 8, ∑ u ∈ T.filter (fun u => cls u = r),
        ENNReal.ofReal (Real.exp (ξ * φ (cpt N u)))
      ≤ ∑ _r : ZMod 8 × ZMod 8, ENNReal.ofReal (N * Real.exp (ξ * θ)) * lfppLen ξ φ P :=
        Finset.sum_le_sum fun r _ => hclass r
    _ = ENNReal.ofReal (64 * N * Real.exp (ξ * θ)) * lfppLen ξ φ P := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have hc : Fintype.card (ZMod 8 × ZMod 8) = 64 := by simp [Fintype.card_prod]
        rw [hc, ← mul_assoc]
        congr 1
        rw [show (64 : ℝ) * N * Real.exp (ξ * θ) = 64 * (N * Real.exp (ξ * θ)) by ring,
          ENNReal.ofReal_mul (by norm_num)]
        simp

end SupercriticalLQGUniqueness.B2.QPos.P8
