/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.K3.MixedPoincare at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.GFF.Defs
import LatticeProb.Bonanno.QuantumZipper.Common.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.RealDeriv

/-!
# K3-M3: Poincaré inequality for the mixed space

For a bounded open `D ⊆ ℍ` and `S ⊆ ℝ`, every `f ∈ mixedSpace D S` satisfies
`∫_D f² ≤ C ∫_D ‖Df‖²`. Proof: the upward vertical ray from `z ∈ D` first leaves `D` at a
point of `frontier D ∩ ℍ`, where `f = 0`; FTC and Cauchy–Schwarz along the ray, then Tonelli.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace QuantumZipper.K3

/-- Cauchy–Schwarz on `[0,T]`. -/
lemma mixedPoincare_cs {φ : ℝ → ℝ} (hφ : Continuous φ) {T : ℝ} (hT : 0 < T) :
    (∫ t in (0:ℝ)..T, φ t) ^ 2 ≤ T * ∫ t in (0:ℝ)..T, φ t ^ 2 := by
  set m := ∫ t in (0:ℝ)..T, φ t
  set S := ∫ t in (0:ℝ)..T, φ t ^ 2
  have e : ∀ t, (T * φ t - m) ^ 2 = T ^ 2 * φ t ^ 2 - (2 * T * m) * φ t + m ^ 2 := by
    intro t; ring
  have h0 : 0 ≤ ∫ t in (0:ℝ)..T, (T * φ t - m) ^ 2 :=
    intervalIntegral.integral_nonneg hT.le (fun t _ => sq_nonneg _)
  have hi1 : IntervalIntegrable (fun t => φ t ^ 2) volume 0 T :=
    (hφ.pow 2).intervalIntegrable _ _
  have hi2 : IntervalIntegrable φ volume 0 T := hφ.intervalIntegrable _ _
  simp_rw [e] at h0
  rw [intervalIntegral.integral_add ((hi1.const_mul _).sub (hi2.const_mul _))
      intervalIntegrable_const, intervalIntegral.integral_sub (hi1.const_mul _)
      (hi2.const_mul _), intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at h0
  simp only [sub_zero, smul_eq_mul] at h0
  have : 0 ≤ T * (T * S - m ^ 2) := by nlinarith
  nlinarith [(mul_nonneg_iff_of_pos_left hT).1 this]

theorem mixed_poincare {D S : Set ℂ} (hD : IsOpen D) (hDH : D ⊆ H)
    (hb : Bornology.IsBounded D) (hS : S ⊆ {z : ℂ | z.im = 0}) :
    ∃ C, ∀ f ∈ mixedSpace D S, ∫ z in D, f z ^ 2 ≤ C * ∫ z in D, ‖fderiv ℝ f z‖ ^ 2 := by
  obtain ⟨R₀, hR₀⟩ := (Metric.isBounded_iff_subset_ball (0 : ℂ)).1 hb
  set R : ℝ := |R₀| + 1 with hRdef
  have hRpos : 0 < R := by positivity
  have hDR : ∀ w ∈ D, |w.im| < R := fun w hw => by
    have := hR₀ hw
    rw [Metric.mem_ball, dist_zero_right] at this
    exact (Complex.abs_im_le_norm w).trans_lt (this.trans_le (by rw [hRdef]; linarith [le_abs_self R₀]))
  refine ⟨ENNReal.toReal (ENNReal.ofReal (2 * R)) * ENNReal.toReal (ENNReal.ofReal (2 * R)), ?_⟩
  rintro f ⟨hf, hint, N, hNo, hN, hfN⟩
  have hn : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp
  have hdiff := hf.differentiable hn
  have hcf : Continuous (fderiv ℝ f) := hf.continuous_fderiv hn
  set g : ℂ → ℝ := fun w => ‖fderiv ℝ f w‖ ^ 2 with hg
  have hgc : Continuous g := hcf.norm.pow 2
  set F : ℂ → ℝ≥0∞ := D.indicator (fun w => ENNReal.ofReal (g w)) with hF
  have hFm : Measurable F :=
    (ENNReal.measurable_ofReal.comp hgc.measurable).indicator hD.measurableSet
  set G : ℝ → ℝ≥0∞ := fun x => ∫⁻ s, F ⟨x, s⟩ with hG
  have hFm' : Measurable fun p : ℝ × ℝ => F ⟨p.1, p.2⟩ :=
    hFm.comp (Complex.measurableEquivRealProd.symm.measurable)
  have hGm : Measurable G := hFm'.lintegral_prod_right'
  -- pointwise 1-D estimate
  have hpt : ∀ z ∈ D, ENNReal.ofReal (f z ^ 2) ≤ ENNReal.ofReal (2 * R) * G z.re := by
    intro z hz
    set γ : ℝ → ℂ := fun t => z + (t : ℂ) * Complex.I with hγ
    have hγc : Continuous γ := by fun_prop
    have hγd : ∀ t, HasDerivAt γ (((1 : ℝ) : ℂ) * Complex.I) t := fun t =>
      ((hasDerivAt_id t).ofReal_comp.mul_const Complex.I).const_add z
    have hγim : ∀ t, (γ t).im = z.im + t := fun t => by simp [hγ]
    have hγeq : ∀ t, γ t = ⟨z.re, z.im + t⟩ := fun t => Complex.ext (by simp [hγ]) (hγim t)
    have hzim : 0 < z.im := hDH hz
    set A : Set ℝ := Ici 0 ∩ γ ⁻¹' Dᶜ with hA
    have hAc : IsClosed A := isClosed_Ici.inter (hD.isClosed_compl.preimage hγc)
    have h2R : 2 * R ∈ A := by
      refine ⟨by simp; linarith, fun hmem => ?_⟩
      have := hDR _ hmem
      rw [hγim] at this
      linarith [le_abs_self (z.im + 2 * R)]
    have hbdd : BddBelow A := ⟨0, fun t ht => ht.1⟩
    set T := sInf A with hTdef
    have hTA : T ∈ A := hAc.csInf_mem ⟨_, h2R⟩ hbdd
    have hT2R : T ≤ 2 * R := csInf_le hbdd h2R
    have hin : ∀ t, 0 ≤ t → t < T → γ t ∈ D := fun t ht0 htT => by
      by_contra hc
      exact notMem_of_lt_csInf htT hbdd ⟨ht0, hc⟩
    have hTpos : 0 < T := by
      rcases (show (0:ℝ) ≤ T from hTA.1).lt_or_eq with h | h
      · exact h
      · exfalso; apply hTA.2; rw [← h]; simpa [hγ] using hz
    have hfr : γ T ∈ frontier D := by
      rw [frontier, hD.interior_eq]
      have htend : Tendsto γ (𝓝[<] T) (𝓝 (γ T)) := (hγc.tendsto T).mono_left nhdsWithin_le_nhds
      refine ⟨mem_closure_of_tendsto htend ?_, hTA.2⟩
      filter_upwards [Ioo_mem_nhdsLT hTpos] with t ht using hin t ht.1.le ht.2
    have hnS : γ T ∉ S := fun h => by
      have := hS h; simp only [mem_ofPred_eq, hγim] at this; linarith
    have hfT : f (γ T) = 0 := hfN _ (hN ⟨hfr, hnS⟩)
    set φ' : ℝ → ℝ := fun t => fderiv ℝ f (γ t) (((1 : ℝ) : ℂ) * Complex.I) with hφ'
    have hφc : Continuous φ' := (hcf.comp hγc).clm_apply continuous_const
    have hderiv : ∀ t, HasDerivAt (fun t => f (γ t)) (φ' t) t := fun t =>
      (hdiff (γ t)).hasFDerivAt.comp_hasDerivAt t (hγd t)
    have hftc : ∫ t in (0:ℝ)..T, φ' t = f (γ T) - f (γ 0) :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hderiv t)
        (hφc.intervalIntegrable _ _)
    have hγ0 : γ 0 = z := by simp [hγ]
    rw [hfT, hγ0, zero_sub] at hftc
    have hφle : ∀ t, φ' t ^ 2 ≤ g (γ t) := fun t => by
      have h1 : ‖φ' t‖ ≤ ‖fderiv ℝ f (γ t)‖ := by
        have := (fderiv ℝ f (γ t)).le_opNorm (((1 : ℝ) : ℂ) * Complex.I)
        simpa [hφ'] using this
      have h2 : |φ' t| ≤ ‖fderiv ℝ f (γ t)‖ := by rw [← Real.norm_eq_abs]; exact h1
      simpa [hg, sq_abs] using pow_le_pow_left₀ (abs_nonneg _) h2 2
    have hgγc : Continuous fun t => g (γ t) := hgc.comp hγc
    have hreal : f z ^ 2 ≤ 2 * R * ∫ t in (0:ℝ)..T, g (γ t) := by
      have e : f z ^ 2 = (∫ t in (0:ℝ)..T, φ' t) ^ 2 := by rw [hftc]; ring
      have hmono : ∫ t in (0:ℝ)..T, φ' t ^ 2 ≤ ∫ t in (0:ℝ)..T, g (γ t) :=
        intervalIntegral.integral_mono_on hTpos.le ((hφc.pow 2).intervalIntegrable _ _)
          (hgγc.intervalIntegrable _ _) (fun t _ => hφle t)
      have hnn : 0 ≤ ∫ t in (0:ℝ)..T, g (γ t) :=
        intervalIntegral.integral_nonneg hTpos.le (fun t _ => by positivity)
      rw [e]
      calc _ ≤ T * ∫ t in (0:ℝ)..T, φ' t ^ 2 := mixedPoincare_cs hφc hTpos
        _ ≤ T * ∫ t in (0:ℝ)..T, g (γ t) := mul_le_mul_of_nonneg_left hmono hTpos.le
        _ ≤ _ := mul_le_mul_of_nonneg_right hT2R hnn
    have hlin : ENNReal.ofReal (∫ t in (0:ℝ)..T, g (γ t)) ≤ G z.re := by
      rw [intervalIntegral.integral_of_le hTpos.le, integral_Ioc_eq_integral_Ioo,
        ofReal_integral_eq_lintegral_ofReal
          ((hgγc.integrableOn_Icc).mono_set Ioo_subset_Icc_self)
          (Eventually.of_forall fun t => by positivity)]
      calc ∫⁻ t in Ioo 0 T, ENNReal.ofReal (g (γ t))
          = ∫⁻ t in Ioo 0 T, F (γ t) := by
            refine setLIntegral_congr_fun measurableSet_Ioo (fun t ht => ?_)
            simp [hF, indicator_of_mem (hin t ht.1.le ht.2)]
        _ ≤ ∫⁻ t, F (γ t) := setLIntegral_le_lintegral _ _
        _ = ∫⁻ t, (fun s : ℝ => F ⟨z.re, s⟩) (z.im + t) := by simp_rw [hγeq]
        _ = G z.re := lintegral_add_left_eq_self (fun s : ℝ => F ⟨z.re, s⟩) z.im
    calc ENNReal.ofReal (f z ^ 2) ≤ ENNReal.ofReal (2 * R * ∫ t in (0:ℝ)..T, g (γ t)) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (2 * R) * ENNReal.ofReal (∫ t in (0:ℝ)..T, g (γ t)) :=
          ENNReal.ofReal_mul (by positivity)
      _ ≤ _ := by gcongr
  -- 2-D estimate
  set c := ENNReal.ofReal (2 * R)
  set I := Icc (-R) R
  have hGint : ∫⁻ x, G x = ∫⁻ z in D, ENNReal.ofReal (g z) := by
    rw [← lintegral_indicator hD.measurableSet]
    change ∫⁻ x, ∫⁻ s, F ⟨x, s⟩ = ∫⁻ z, F z
    rw [← lintegral_prod _ hFm'.aemeasurable, ← Measure.volume_eq_prod]
    exact (Complex.volume_preserving_equiv_real_prod.symm).lintegral_comp_emb
      Complex.measurableEquivRealProd.symm.measurableEmbedding F
  have hmain : ∫⁻ z in D, ENNReal.ofReal (f z ^ 2) ≤
      c * (∫⁻ z in D, ENNReal.ofReal (g z)) * c := by
    calc ∫⁻ z in D, ENNReal.ofReal (f z ^ 2)
        = ∫⁻ z, D.indicator (fun z => ENNReal.ofReal (f z ^ 2)) z :=
          (lintegral_indicator hD.measurableSet _).symm
      _ ≤ ∫⁻ z : ℂ, (c * G z.re) * I.indicator 1 z.im := by
          refine lintegral_mono fun z => ?_
          by_cases hz : z ∈ D
          · have hzI : z.im ∈ I := abs_le.1 (hDR z hz).le
            simpa [indicator_of_mem hz, indicator_of_mem hzI] using hpt z hz
          · simp [indicator_of_notMem hz]
      _ = ∫⁻ p : ℝ × ℝ, (c * G p.1) * I.indicator 1 p.2 := by
          rw [← (Complex.volume_preserving_equiv_real_prod.symm).lintegral_comp_emb
            Complex.measurableEquivRealProd.symm.measurableEmbedding]
          rfl
      _ = (∫⁻ x, c * G x) * ∫⁻ y, I.indicator 1 y := by
          rw [Measure.volume_eq_prod]
          exact lintegral_prod_mul (hGm.const_mul c).aemeasurable
            ((measurable_one.indicator measurableSet_Icc).aemeasurable)
      _ = c * (∫⁻ z in D, ENNReal.ofReal (g z)) * c := by
          rw [lintegral_const_mul _ hGm, hGint, lintegral_indicator_one measurableSet_Icc,
            Real.volume_Icc]
          congr 2; ring_nf
  have hfin : ∫⁻ z in D, ENNReal.ofReal (g z) < ∞ := hint.lintegral_lt_top
  have hgi : ∫ z in D, g z = (∫⁻ z in D, ENNReal.ofReal (g z)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun z => by positivity)
      hgc.aestronglyMeasurable
  have hfi : ∫ z in D, f z ^ 2 = (∫⁻ z in D, ENNReal.ofReal (f z ^ 2)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun z => by positivity)
      (hf.continuous.pow 2).aestronglyMeasurable
  rw [hfi, show (∫ z in D, ‖fderiv ℝ f z‖ ^ 2) = ∫ z in D, g z from rfl, hgi]
  have := ENNReal.toReal_mono (by
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin.ne)
      ENNReal.ofReal_ne_top) hmain
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul] at this
  exact this.trans_eq (by ring)

end QuantumZipper.K3
