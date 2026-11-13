/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Strong.AroundFinite at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.LSCMetricInternalSetDist
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.AroundDist
import LatticeProb.Bonanno.SLUMetricAPI2
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Strong.PolarSets

 










set_option autoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Strong

 
def annL (A : EuclideanAnnulus) : ℝ := Real.log A.innerRadius

 
def annΔ (A : EuclideanAnnulus) : ℝ := (Real.log A.outerRadius - Real.log A.innerRadius) / 16

theorem annΔ_pos (A : EuclideanAnnulus) : 0 < annΔ A := by
  unfold annΔ
  have := Real.log_lt_log A.innerRadius_pos A.innerRadius_lt_outerRadius
  linarith

theorem exp_annL (A : EuclideanAnnulus) : Real.exp (annL A) = A.innerRadius :=
  Real.exp_log A.innerRadius_pos

theorem exp_annL_add (A : EuclideanAnnulus) :
    Real.exp (annL A + 16 * annΔ A) = A.outerRadius := by
  have : annL A + 16 * annΔ A = Real.log A.outerRadius := by unfold annL annΔ; ring
  rw [this]
  exact Real.exp_log (A.innerRadius_pos.trans A.innerRadius_lt_outerRadius)

 
def cfgOpens (A : EuclideanAnnulus) (k : Fin 4) : TopologicalSpace.Opens ℂ :=
  ⟨polarOpen A.center (cfgU (annL A) (annΔ A) k), isOpen_polarOpen _ _⟩

 
def cfgSet₁ (A : EuclideanAnnulus) (k : Fin 4) : Set ℂ :=
  polarClosed A.center (cfgK₁ (annL A) (annΔ A) k)

 
def cfgSet₂ (A : EuclideanAnnulus) (k : Fin 4) : Set ℂ :=
  polarClosed A.center (cfgK₂ (annL A) (annΔ A) k)

theorem cfgOpens_subset_toSet (A : EuclideanAnnulus) (k : Fin 4) :
    ((cfgOpens A k : Set ℂ)) ⊆ A.toSet := by
  intro z hz
  have h := norm_sub_of_mem_polarOpen (annΔ_pos A) k hz
  rw [exp_annL, exp_annL_add] at h
  rw [EuclideanAnnulus.toSet_eq]
  exact ⟨by rw [dist_eq_norm]; exact h.1, by rw [dist_eq_norm]; exact h.2⟩

 
theorem exists_curve_of_internalSetDist_lt_top (D : LSCMetric) (U : Set ℂ) (K₁ K₂ : Set ℂ)
    (h : D.internalSetDist U (Subtype.val ⁻¹' K₁) (Subtype.val ⁻¹' K₂) < ∞) :
    ∃ (P : ℝ → ℂ) (a b : ℝ), D.IsCurve P a b ∧ (∀ t ∈ Icc a b, P t ∈ U) ∧ P a ∈ K₁ ∧
      P b ∈ K₂ ∧ D.len P a b < ∞ := by
  unfold LSCMetric.internalSetDist at h
  simp only [iInf_lt_iff] at h
  obtain ⟨x, hx, y, hy, hxy⟩ := h
  unfold LSCMetric.internal at hxy
  simp only [iInf_lt_iff] at hxy
  obtain ⟨P, a, b, hP, hPU, hPa, hPb, hlen⟩ := hxy
  exact ⟨P, a, b, hP, hPU, hPa ▸ hx, hPb ▸ hy, hlen⟩

theorem pathIn_of_curve (D : LSCMetric) (A : EuclideanAnnulus) (k : Fin 4) {P : ℝ → ℂ}
    {a b : ℝ} (hP : D.IsCurve P a b) (hU : ∀ t ∈ Icc a b, P t ∈ (cfgOpens A k : Set ℂ))
    (ha : P a ∈ cfgSet₁ A k) (hb : P b ∈ cfgSet₂ A k) :
    PathIn A.center (cfgU (annL A) (annΔ A) k) (cfgK₁ (annL A) (annΔ A) k)
      (cfgK₂ (annL A) (annΔ A) k) P a b := by
  refine ⟨hP.1, hP.continuousOn_of_mapsTo (isCompact_closedBall A.center A.outerRadius)
    (fun t ht => ?_), hU, ha, hb⟩
  have := cfgOpens_subset_toSet A k (hU t ht)
  rw [EuclideanAnnulus.toSet_eq] at this
  exact Metric.mem_closedBall.2 this.2.le

 
theorem aroundDist_lt_top_of_internalSetDist (D : LSCMetric) (A : EuclideanAnnulus)
    (h : ∀ k : Fin 4, D.internalSetDist (cfgOpens A k : Set ℂ)
      (Subtype.val ⁻¹' cfgSet₁ A k) (Subtype.val ⁻¹' cfgSet₂ A k) < ∞) :
    aroundDist D A < ⊤ := by
  choose P a b hP hU ha hb hlen using fun k =>
    exists_curve_of_internalSetDist_lt_top D _ _ _ (h k)
  obtain ⟨s₀, hs₀, s₀', hs₀', s₁, hs₁, s₁', hs₁', s₂, hs₂, s₂', hs₂', s₃, hs₃, s₃', hs₃',
      z₁, z₂, z₃, hdisc⟩ := exists_around_loop A.center (annΔ_pos A)
    (pathIn_of_curve D A 0 (hP 0) (hU 0) (ha 0) (hb 0))
    (pathIn_of_curve D A 1 (hP 1) (hU 1) (ha 1) (hb 1))
    (pathIn_of_curve D A 2 (hP 2) (hU 2) (ha 2) (hb 2))
    (pathIn_of_curve D A 3 (hP 3) (hU 3) (ha 3) (hb 3))
  set Q := glue4 (seg (P 0) s₀ s₀') (seg (P 1) s₁ s₁') (seg (P 2) s₂ s₂') (seg (P 3) s₃ s₃')
  have hQpt : D.pt ∘ Q = glue4 (seg (D.pt ∘ P 0) s₀ s₀') (seg (D.pt ∘ P 1) s₁ s₁')
      (seg (D.pt ∘ P 2) s₂ s₂') (seg (D.pt ∘ P 3) s₃ s₃') := by
    funext t
    simp only [Function.comp, Q, glue4, seg]
    split_ifs <;> rfl
  have hcurve : D.IsCurve Q 0 4 := by
    refine ⟨by norm_num, ?_⟩
    rw [hQpt]
    exact continuousOn_glue4 _ _ _ _ (continuousOn_seg (hP 0).2 hs₀ hs₀')
      (continuousOn_seg (hP 1).2 hs₁ hs₁') (continuousOn_seg (hP 2).2 hs₂ hs₂')
      (continuousOn_seg (hP 3).2 hs₃ hs₃')
      (by simp only [seg_one, seg_zero, Function.comp]; rw [z₁])
      (by simp only [seg_one, seg_zero, Function.comp]; rw [z₂])
      (by simp only [seg_one, seg_zero, Function.comp]; rw [z₃])
  have hlenQ : D.len Q 0 4 < ⊤ := by
    have e : D.len Q 0 4 = eVariationOn (D.pt ∘ Q) (Icc 0 4) := rfl
    rw [e, hQpt, eVariationOn_glue4 _ _ _ _
      (by simp only [seg_one, seg_zero, Function.comp]; rw [z₁])
      (by simp only [seg_one, seg_zero, Function.comp]; rw [z₂])
      (by simp only [seg_one, seg_zero, Function.comp]; rw [z₃])]
    have b := fun (k : Fin 4) (s s' : ℝ) (hs : s ∈ Icc (a k) (b k)) (hs' : s' ∈ Icc (a k) (b k)) =>
      (eVariationOn_seg_le (D.pt ∘ P k) hs hs').trans_lt (hlen k)
    exact ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2 ⟨ENNReal.add_lt_top.2
      ⟨b 0 _ _ hs₀ hs₀', b 1 _ _ hs₁ hs₁'⟩, b 2 _ _ hs₂ hs₂'⟩, b 3 _ _ hs₃ hs₃'⟩
  have hinA : ∀ t ∈ Icc (0 : ℝ) 4, Q t ∈ A.toSet :=
    mapsTo_glue4 _ _ _ _
      (mapsTo_seg (fun t ht => cfgOpens_subset_toSet A 0 (hU 0 t ht)) hs₀ hs₀')
      (mapsTo_seg (fun t ht => cfgOpens_subset_toSet A 1 (hU 1 t ht)) hs₁ hs₁')
      (mapsTo_seg (fun t ht => cfgOpens_subset_toSet A 2 (hU 2 t ht)) hs₂ hs₂')
      (mapsTo_seg (fun t ht => cfgOpens_subset_toSet A 3 (hU 3 t ht)) hs₃ hs₃')
  have hdisc' : Disconnects (Q '' Icc 0 4) A.innerBoundary A.outerBoundary := by
    rw [disconnects_iff_lqgMetric_disconnects hcurve.isClosed_image]
    rw [exp_annL, exp_annL_add] at hdisc
    exact hdisc
  unfold aroundDist
  refine lt_of_le_of_lt ?_ hlenQ
  exact iInf_le_of_le Q (iInf_le_of_le 0 (iInf_le_of_le 4 (iInf_le_of_le hcurve
    (iInf_le_of_le hinA (iInf_le_of_le hdisc' le_rfl)))))

end SupercriticalLQGUniqueness.B2.Strong
