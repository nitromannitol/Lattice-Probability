/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Polylog.P4Transport at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P4Costs

 













set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal Pointwise

namespace SupercriticalLQGUniqueness.B2.Polylog

open Uniqueness.Toolkit.CompactPathInfimum (compactPathInf)

section Transport

variable {m M : LSCMetric} {k : ℝ≥0∞} {T : ℂ → ℂ}

lemma isCurve_comp_mul_iff (hk0 : k ≠ 0) (hkt : k ≠ ∞)
    (hm : ∀ x y, m (x, y) = k * M (T x, T y)) (P : ℝ → ℂ) (a b : ℝ) :
    m.IsCurve P a b ↔ M.IsCurve (T ∘ P) a b := by
  unfold LSCMetric.IsCurve
  refine and_congr_right fun _ => ?_
  have he : ∀ s t, edist (m.pt (P s)) (m.pt (P t)) = k * edist (M.pt (T (P s))) (M.pt (T (P t))) :=
    fun s t => hm (P s) (P t)
  simp only [ContinuousOn, ContinuousWithinAt, tendsto_iff_edist_tendsto_0,
    Function.comp_apply, he]
  refine forall₂_congr fun t _ => ⟨fun h => ?_, fun h => ?_⟩
  · have := ENNReal.Tendsto.const_mul h (Or.inr (ENNReal.inv_ne_top.2 hk0))
    simpa only [← mul_assoc, ENNReal.inv_mul_cancel hk0 hkt, one_mul, mul_zero] using this
  · simpa only [mul_zero] using ENNReal.Tendsto.const_mul h (Or.inr hkt)

lemma len_comp_mul (hm : ∀ x y, m (x, y) = k * M (T x, T y)) (P : ℝ → ℂ) (a b : ℝ) :
    m.len P a b = k * M.len (T ∘ P) a b := by
  unfold LSCMetric.len
  exact LQGMetric.MetricGeometry.eVariationOn_eq_mul_of_edist (F := m.pt ∘ P)
    (G := M.pt ∘ (T ∘ P)) (c := k) (fun s t => hm (P s) (P t)) (Icc a b)

 
theorem compactPathInf_comp_mul (hk0 : k ≠ 0) (hkt : k ≠ ∞) (T : ℂ ≃ₜ ℂ)
    (hm : ∀ x y, m (x, y) = k * M (T x, T y)) (K E F : Set ℂ) :
    compactPathInf m K E F = k * compactPathInf M (T '' K) (T '' E) (T '' F) := by
  have hmem : ∀ (A : Set ℂ) (x : ℂ), T x ∈ T '' A ↔ x ∈ A := fun A x => T.injective.mem_set_image
  unfold compactPathInf
  simp only [ENNReal.mul_iInf_of_ne hk0 hkt]
  apply le_antisymm
  · refine le_iInf fun Q => le_iInf fun a => le_iInf fun b => le_iInf fun hQ =>
      le_iInf fun hQK => le_iInf fun hE => le_iInf fun hF => ?_
    have hQ' : (T ∘ (T.symm ∘ Q)) = Q := funext fun t => T.apply_symm_apply (Q t)
    have hP : m.IsCurve (T.symm ∘ Q) a b :=
      (isCurve_comp_mul_iff hk0 hkt hm _ a b).2 (by rwa [hQ'])
    have hPK : ∀ t ∈ Icc a b, (T.symm ∘ Q) t ∈ K := fun t ht => by
      rw [← hmem]; simpa only [Function.comp_apply, T.apply_symm_apply] using hQK t ht
    have hPE : (T.symm ∘ Q) a ∈ E := by
      rw [← hmem]; simpa only [Function.comp_apply, T.apply_symm_apply] using hE
    have hPF : (T.symm ∘ Q) b ∈ F := by
      rw [← hmem]; simpa only [Function.comp_apply, T.apply_symm_apply] using hF
    have hlen : m.len (T.symm ∘ Q) a b = k * M.len Q a b := by rw [len_comp_mul hm, hQ']
    exact iInf_le_of_le (T.symm ∘ Q) (iInf_le_of_le a (iInf_le_of_le b (iInf_le_of_le hP
      (iInf_le_of_le hPK (iInf_le_of_le hPE (iInf_le_of_le hPF hlen.le))))))
  · refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP =>
      le_iInf fun hPK => le_iInf fun hE => le_iInf fun hF => ?_
    exact iInf_le_of_le (T ∘ P) (iInf_le_of_le a (iInf_le_of_le b (iInf_le_of_le
      ((isCurve_comp_mul_iff hk0 hkt hm P a b).1 hP) (iInf_le_of_le
      (fun t ht => (hmem K _).2 (hPK t ht))
      (iInf_le_of_le ((hmem E _).2 hE) (iInf_le_of_le ((hmem F _).2 hF)
        (len_comp_mul hm P a b).ge))))))

lemma disconnects_image_homeomorph (T : ℂ ≃ₜ ℂ) {K E F : Set ℂ} (h : Disconnects K E F) :
    Disconnects (T '' K) (T '' E) (T '' F) := by
  rintro ⟨S, hS, hSK, ⟨x, hxS, hxE⟩, ⟨y, hyS, hyF⟩⟩
  refine h ⟨T.symm '' S, hS.image _ T.symm.continuous.continuousOn, ?_, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩ hK
    exact hSK hs ⟨T.symm s, hK, T.apply_symm_apply s⟩
  · obtain ⟨e, he, rfl⟩ := hxE
    exact ⟨e, ⟨T e, hxS, T.symm_apply_apply e⟩, he⟩
  · obtain ⟨e, he, rfl⟩ := hyF
    exact ⟨e, ⟨T e, hyS, T.symm_apply_apply e⟩, he⟩

lemma image_symm_image (T : ℂ ≃ₜ ℂ) (S : Set ℂ) : T.symm '' (T '' S) = S := by
  rw [image_image]; simp

 
theorem aroundDist_comp_mul (hk0 : k ≠ 0) (hkt : k ≠ ∞) (T : ℂ ≃ₜ ℂ)
    (hm : ∀ x y, m (x, y) = k * M (T x, T y)) (A A' : EuclideanAnnulus)
    (hset : T '' A.toSet = A'.toSet) (hin : T '' A.innerBoundary = A'.innerBoundary)
    (hout : T '' A.outerBoundary = A'.outerBoundary) :
    aroundDist m A = k * aroundDist M A' := by
  have hmem : ∀ (S : Set ℂ) (x : ℂ), T x ∈ T '' S ↔ x ∈ S := fun S x => T.injective.mem_set_image
  unfold aroundDist
  simp only [ENNReal.mul_iInf_of_ne hk0 hkt]
  apply le_antisymm
  · refine le_iInf fun Q => le_iInf fun a => le_iInf fun b => le_iInf fun hQ =>
      le_iInf fun hQA => le_iInf fun hQD => ?_
    have hQ' : (T ∘ (T.symm ∘ Q)) = Q := funext fun t => T.apply_symm_apply (Q t)
    have hP : m.IsCurve (T.symm ∘ Q) a b :=
      (isCurve_comp_mul_iff hk0 hkt hm _ a b).2 (by rwa [hQ'])
    have hPA : ∀ t ∈ Icc a b, (T.symm ∘ Q) t ∈ A.toSet := fun t ht => by
      rw [← hmem, hset]; simpa only [Function.comp_apply, T.apply_symm_apply] using hQA t ht
    have himg : (T.symm ∘ Q) '' Icc a b = T.symm '' (Q '' Icc a b) := by rw [image_comp]
    have hPD : Disconnects ((T.symm ∘ Q) '' Icc a b) A.innerBoundary A.outerBoundary := by
      have := disconnects_image_homeomorph T.symm hQD
      rwa [← hin, ← hout, image_symm_image, image_symm_image, ← himg] at this
    have hlen : m.len (T.symm ∘ Q) a b = k * M.len Q a b := by rw [len_comp_mul hm, hQ']
    exact iInf_le_of_le (T.symm ∘ Q) (iInf_le_of_le a (iInf_le_of_le b (iInf_le_of_le hP
      (iInf_le_of_le hPA (iInf_le_of_le hPD hlen.le)))))
  · refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP =>
      le_iInf fun hPA => le_iInf fun hPD => ?_
    have hQA : ∀ t ∈ Icc a b, (T ∘ P) t ∈ A'.toSet := fun t ht => by
      rw [← hset]; exact (hmem _ _).2 (hPA t ht)
    have hQD : Disconnects ((T ∘ P) '' Icc a b) A'.innerBoundary A'.outerBoundary := by
      rw [image_comp, ← hin, ← hout]; exact disconnects_image_homeomorph T hPD
    exact iInf_le_of_le (T ∘ P) (iInf_le_of_le a (iInf_le_of_le b (iInf_le_of_le
      ((isCurve_comp_mul_iff hk0 hkt hm P a b).1 hP) (iInf_le_of_le hQA
      (iInf_le_of_le hQD (len_comp_mul hm P a b).ge)))))

end Transport

 

lemma annAt_toSet (z : ℂ) (r₁ r₂ : ℝ) (h₁ : 0 < r₁) (h₁₂ : r₁ < r₂) :
    (annAt z r₁ r₂ h₁ h₁₂).toSet = {w | r₁ < ‖w - z‖ ∧ ‖w - z‖ < r₂} := by
  rw [EuclideanAnnulus.toSet_eq]
  ext w; simp only [annAt_center, annAt_innerRadius, annAt_outerRadius, dist_eq_norm]

lemma image_translate_annAt (z c : ℂ) (r₁ r₂ : ℝ) (h₁ : 0 < r₁) (h₁₂ : r₁ < r₂) :
    (Homeomorph.addRight z) '' (annAt c r₁ r₂ h₁ h₁₂).toSet = (annAt (c + z) r₁ r₂ h₁ h₁₂).toSet ∧
    (Homeomorph.addRight z) '' (annAt c r₁ r₂ h₁ h₁₂).innerBoundary =
      (annAt (c + z) r₁ r₂ h₁ h₁₂).innerBoundary ∧
    (Homeomorph.addRight z) '' (annAt c r₁ r₂ h₁ h₁₂).outerBoundary =
      (annAt (c + z) r₁ r₂ h₁ h₁₂).outerBoundary := by
  have himg : ∀ S : Set ℂ, (Homeomorph.addRight z) '' S = (fun x => x + z) '' S := fun _ => rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [himg, annAt_toSet, annAt_toSet]
    ext w
    simp only [mem_image, mem_ofPred_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩; rwa [add_sub_add_right_eq_sub]
    · intro hw; exact ⟨w - z, by rwa [sub_sub, add_comm z c], sub_add_cancel w z⟩
  · rw [himg]; exact image_add_sphere z c r₁
  · rw [himg]; exact image_add_sphere z c r₂

 
def dilateHomeo {r : ℝ} (hr : 0 < r) : ℂ ≃ₜ ℂ := Homeomorph.smulOfNeZero r hr.ne'

lemma dilateHomeo_apply {r : ℝ} (hr : 0 < r) (x : ℂ) : dilateHomeo hr x = r • x := rfl

lemma image_dilate_annAt {r : ℝ} (hr : 0 < r) (c : ℂ) (r₁ r₂ : ℝ) (h₁ : 0 < r₁) (h₁₂ : r₁ < r₂) :
    (dilateHomeo hr) '' (annAt c r₁ r₂ h₁ h₁₂).toSet =
      (annAt (r • c) (r * r₁) (r * r₂) (mul_pos hr h₁) (mul_lt_mul_of_pos_left h₁₂ hr)).toSet ∧
    (dilateHomeo hr) '' (annAt c r₁ r₂ h₁ h₁₂).innerBoundary =
      (annAt (r • c) (r * r₁) (r * r₂) (mul_pos hr h₁)
        (mul_lt_mul_of_pos_left h₁₂ hr)).innerBoundary ∧
    (dilateHomeo hr) '' (annAt c r₁ r₂ h₁ h₁₂).outerBoundary =
      (annAt (r • c) (r * r₁) (r * r₂) (mul_pos hr h₁)
        (mul_lt_mul_of_pos_left h₁₂ hr)).outerBoundary := by
  have himg : ∀ S : Set ℂ, (dilateHomeo hr) '' S = (fun x => r • x) '' S := fun _ => rfl
  have hnorm : ∀ x : ℂ, ‖r • x - r • c‖ = r * ‖x - c‖ := fun x => by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  refine ⟨?_, ?_, ?_⟩
  · rw [himg, annAt_toSet, annAt_toSet]
    ext w
    simp only [mem_image, mem_ofPred_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hnorm]
      exact ⟨mul_lt_mul_of_pos_left hx.1 hr, mul_lt_mul_of_pos_left hx.2 hr⟩
    · intro hw
      refine ⟨r⁻¹ • w, ?_, by rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]⟩
      have hw' : ‖w - r • c‖ = r * ‖r⁻¹ • w - c‖ := by
        rw [← hnorm, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      rw [hw'] at hw
      exact ⟨lt_of_mul_lt_mul_left hw.1 hr.le, lt_of_mul_lt_mul_left hw.2 hr.le⟩
  · rw [himg]; exact image_smul_sphere hr c r₁
  · rw [himg]; exact image_smul_sphere hr c r₂

end SupercriticalLQGUniqueness.B2.Polylog
