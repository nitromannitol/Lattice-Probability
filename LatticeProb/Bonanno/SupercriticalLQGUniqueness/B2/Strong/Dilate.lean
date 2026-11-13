/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Strong.Dilate at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Strong.Annulus
import LatticeProb.Bonanno.LQGMetric.Metric.WeylScaling

 








set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology
open scoped ENNReal Pointwise

namespace SupercriticalLQGUniqueness.B2.Strong

theorem disconnects_smul {K E F : Set ℂ} {r : ℝ} (hr : r ≠ 0) (h : Disconnects K E F) :
    Disconnects (r • K) (r • E) (r • F) := by
  rintro ⟨S, hS, hSK, ⟨x, hxS, hxE⟩, ⟨y, hyS, hyF⟩⟩
  refine h ⟨r⁻¹ • S, hS.image _ (continuous_const_smul _).continuousOn, ?_, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩ hK
    exact hSK hs (by
      have := smul_mem_smul_set (a := r) hK
      rwa [smul_smul, mul_inv_cancel₀ hr, one_smul] at this)
  · obtain ⟨e, he, rfl⟩ := hxE
    exact ⟨e, ⟨r • e, hxS, by simp only [smul_smul, inv_mul_cancel₀ hr, one_smul]⟩, he⟩
  · obtain ⟨e, he, rfl⟩ := hyF
    exact ⟨e, ⟨r • e, hyS, by simp only [smul_smul, inv_mul_cancel₀ hr, one_smul]⟩, he⟩

theorem image_smul_comp {P : ℝ → ℂ} (r : ℝ) (I : Set ℝ) :
    (fun t => r • P t) '' I = r • (P '' I) := by
  rw [← image_smul, image_image]

 
theorem aroundDist_le_of_dilate (m M : LSCMetric) {r : ℝ} (hr : r ≠ 0)
    (hm : ∀ x y, m (x, y) = M (r • x, r • y)) (A A' : EuclideanAnnulus)
    (hA : A'.toSet = r • A.toSet) (hin : A'.innerBoundary = r • A.innerBoundary)
    (hout : A'.outerBoundary = r • A.outerBoundary) :
    aroundDist M A' ≤ aroundDist m A := by
  unfold aroundDist
  refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP =>
    le_iInf fun hPA => le_iInf fun hdisc => ?_
  set Q : ℝ → ℂ := fun t => r • P t
  have hedist : ∀ s t, edist (M.pt (Q s)) (M.pt (Q t)) = edist (m.pt (P s)) (m.pt (P t)) :=
    fun s t => (hm (P s) (P t)).symm
  have hQ : M.IsCurve Q a b := by
    refine ⟨hP.1, fun t ht => ?_⟩
    have hlim := tendsto_iff_edist_tendsto_0.mp (hP.2 t ht)
    refine tendsto_iff_edist_tendsto_0.mpr ?_
    simpa only [Function.comp, hedist] using hlim
  have hlen : M.len Q a b = m.len P a b := by
    have := LQGMetric.MetricGeometry.eVariationOn_eq_mul_of_edist (F := M.pt ∘ Q)
      (G := m.pt ∘ P) (c := 1) (fun s t => by rw [one_mul]; exact hedist s t) (Icc a b)
    rw [one_mul] at this
    exact this
  have hQA : ∀ t ∈ Icc a b, Q t ∈ A'.toSet := fun t ht => by
    rw [hA]; exact smul_mem_smul_set (hPA t ht)
  have hQd : Disconnects (Q '' Icc a b) A'.innerBoundary A'.outerBoundary := by
    rw [image_smul_comp, hin, hout]; exact disconnects_smul hr hdisc
  rw [← hlen]
  exact iInf_le_of_le Q (iInf_le_of_le a (iInf_le_of_le b (iInf_le_of_le hQ
    (iInf_le_of_le hQA (iInf_le_of_le hQd le_rfl)))))

theorem smul_inv_smul_set {r : ℝ} (hr : r ≠ 0) (S : Set ℂ) : r⁻¹ • r • S = S := by
  rw [smul_smul, inv_mul_cancel₀ hr, one_smul]

 
theorem aroundDist_eq_of_dilate (m M : LSCMetric) {r : ℝ} (hr : 0 < r)
    (hm : ∀ x y, m (x, y) = M (r • x, r • y)) (A : EuclideanAnnulus) :
    aroundDist m A = aroundDist M (A.dilate r hr) := by
  refine le_antisymm ?_ (aroundDist_le_of_dilate m M hr.ne' hm A _
    (EuclideanAnnulus.toSet_dilate A r hr) (EuclideanAnnulus.innerBoundary_dilate A r hr)
    (EuclideanAnnulus.outerBoundary_dilate A r hr))
  refine aroundDist_le_of_dilate M m (inv_ne_zero hr.ne') (fun x y => ?_) (A.dilate r hr) A
    ?_ ?_ ?_
  · rw [hm, smul_smul, smul_smul, mul_inv_cancel₀ hr.ne', one_smul, one_smul]
  · rw [EuclideanAnnulus.toSet_dilate A r hr, smul_inv_smul_set hr.ne']
  · rw [EuclideanAnnulus.innerBoundary_dilate A r hr, smul_inv_smul_set hr.ne']
  · rw [EuclideanAnnulus.outerBoundary_dilate A r hr, smul_inv_smul_set hr.ne']

 
theorem acrossDist_eq_of_dilate (m M : LSCMetric) {r : ℝ} (hr : 0 < r)
    (hm : ∀ x y, m (x, y) = M (r • x, r • y)) (A : EuclideanAnnulus) :
    acrossDist m A = acrossDist M (A.dilate r hr) := by
  unfold acrossDist
  rw [EuclideanAnnulus.innerBoundary_dilate A r hr, EuclideanAnnulus.outerBoundary_dilate A r hr]
  apply le_antisymm
  · refine le_iInf₂ fun x' hx' => le_iInf₂ fun y' hy' => ?_
    obtain ⟨x, hx, rfl⟩ := hx'
    obtain ⟨y, hy, rfl⟩ := hy'
    rw [← hm]
    exact iInf₂_le_of_le x hx (iInf₂_le y hy)
  · refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
    rw [hm]
    exact iInf₂_le_of_le _ (smul_mem_smul_set hx) (iInf₂_le _ (smul_mem_smul_set hy))

end SupercriticalLQGUniqueness.B2.Strong
