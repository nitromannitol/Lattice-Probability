/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Strong.Annulus at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Strong.AroundFinite
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Frozen.AcrossDist
import LatticeProb.Bonanno.LQGMetric.Topo.CircleUnion

 













set_option autoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Strong

 
theorem setDist_pos (D : LSCMetric) {K₁ K₂ : Set ℂ} (h₁ : IsCompact K₁) (h₂ : IsCompact K₂)
    (hd : Disjoint K₁ K₂) : 0 < ⨅ x ∈ K₁, ⨅ y ∈ K₂, D (x, y) := by
  rcases (K₁ ×ˢ K₂).eq_empty_or_nonempty with he | hne
  · have : (⨅ x ∈ K₁, ⨅ y ∈ K₂, D (x, y)) = ⊤ := by
      refine eq_top_iff.2 (le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_)
      exact absurd (he ▸ (mk_mem_prod hx hy : (x, y) ∈ K₁ ×ˢ K₂)) (notMem_empty _)
    rw [this]; exact ENNReal.zero_lt_top
  · obtain ⟨p, hp, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn hne (h₁.prod h₂)
      (D.lowerSemicontinuous.lowerSemicontinuousOn _)
    have hne' : p.1 ≠ p.2 := fun h => Set.disjoint_left.1 hd hp.1 (h ▸ hp.2)
    have hpos : 0 < D (p.1, p.2) := by
      refine pos_iff_ne_zero.2 fun h0 => hne' ?_
      exact D.isExtMetric.2.1 _ _ h0
    refine lt_of_lt_of_le hpos (le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_)
    exact (hmin (mk_mem_prod hx hy) : D p ≤ D (x, y))

theorem isCompact_innerBoundary (A : EuclideanAnnulus) : IsCompact A.innerBoundary :=
  isCompact_sphere _ _

theorem isCompact_outerBoundary (A : EuclideanAnnulus) : IsCompact A.outerBoundary :=
  isCompact_sphere _ _

theorem disjoint_boundaries (A : EuclideanAnnulus) :
    Disjoint A.innerBoundary A.outerBoundary := by
  rw [Set.disjoint_left]
  intro z h₁ h₂
  have e₁ : dist z A.center = A.innerRadius := mem_sphere.1 h₁
  have e₂ : dist z A.center = A.outerRadius := mem_sphere.1 h₂
  exact A.innerRadius_lt_outerRadius.ne (e₁.symm.trans e₂)

 
theorem acrossDist_pos (D : LSCMetric) (A : EuclideanAnnulus) : 0 < acrossDist D A :=
  setDist_pos D (isCompact_innerBoundary A) (isCompact_outerBoundary A) (disjoint_boundaries A)

 
def radialSeg (A : EuclideanAnnulus) (σ : ℝ) : Set ℂ :=
  (fun s : ℝ => A.center + ((σ * s : ℝ) : ℂ)) '' Icc A.innerRadius A.outerRadius

theorem isCompact_radialSeg (A : EuclideanAnnulus) (σ : ℝ) : IsCompact (radialSeg A σ) :=
  isCompact_Icc.image (by fun_prop)

theorem disjoint_radialSeg (A : EuclideanAnnulus) :
    Disjoint (radialSeg A 1) (radialSeg A (-1)) := by
  rw [Set.disjoint_left]
  rintro z ⟨s, hs, rfl⟩ ⟨t, ht, he⟩
  have := congrArg Complex.re he
  simp at this
  linarith [A.innerRadius_pos, hs.1, ht.1]

 
theorem disconnects_meets_radialSeg {K : Set ℂ} (A : EuclideanAnnulus) {σ : ℝ} (hσ : |σ| = 1)
    (hK : Disconnects K A.innerBoundary A.outerBoundary) : (K ∩ radialSeg A σ).Nonempty := by
  by_contra hemp
  rw [Set.not_nonempty_iff_eq_empty] at hemp
  have hr := A.innerRadius_lt_outerRadius
  have hmem : ∀ s, 0 ≤ s → dist (A.center + ((σ * s : ℝ) : ℂ)) A.center = s := by
    intro s hs
    rw [dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs, abs_mul, hσ,
      one_mul, abs_of_nonneg hs]
  refine hK ⟨radialSeg A σ, isPreconnected_Icc.image _ (by fun_prop), fun z hz hzK => ?_,
    ⟨_, ⟨A.innerRadius, left_mem_Icc.2 hr.le, rfl⟩, ?_⟩,
    ⟨_, ⟨A.outerRadius, right_mem_Icc.2 hr.le, rfl⟩, ?_⟩⟩
  · exact (Set.eq_empty_iff_forall_notMem.1 hemp) z ⟨hzK, hz⟩
  · exact mem_sphere.2 (hmem _ A.innerRadius_pos.le)
  · exact mem_sphere.2 (hmem _ (A.innerRadius_pos.trans hr).le)

 
theorem aroundDist_pos (D : LSCMetric) (A : EuclideanAnnulus) : 0 < aroundDist D A := by
  refine lt_of_lt_of_le (setDist_pos D (isCompact_radialSeg A 1) (isCompact_radialSeg A (-1))
    (disjoint_radialSeg A)) ?_
  unfold aroundDist
  refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP =>
    le_iInf fun _ => le_iInf fun hdisc => ?_
  obtain ⟨_, ⟨s, hs, rfl⟩, hsp⟩ := disconnects_meets_radialSeg A (σ := 1) (by norm_num) hdisc
  obtain ⟨_, ⟨t, ht, rfl⟩, htm⟩ := disconnects_meets_radialSeg A (σ := -1) (by norm_num) hdisc
  calc (⨅ x ∈ radialSeg A 1, ⨅ y ∈ radialSeg A (-1), D (x, y)) ≤ D (P s, P t) :=
        iInf₂_le_of_le _ hsp (iInf₂_le _ htm)
    _ = edist (D.pt (P s)) (D.pt (P t)) := rfl
    _ ≤ D.len P a b := eVariationOn.edist_le (D.pt ∘ P) hs ht

 

theorem acrossDist_lt_top_of_internalSetDist (D : LSCMetric) (A : EuclideanAnnulus)
    (h : D.internalSetDist ((⊤ : TopologicalSpace.Opens ℂ) : Set ℂ)
      (Subtype.val ⁻¹' A.innerBoundary) (Subtype.val ⁻¹' A.outerBoundary) < ∞) :
    acrossDist D A < ⊤ := by
  obtain ⟨P, a, b, hP, -, ha, hb, hlen⟩ := exists_curve_of_internalSetDist_lt_top D _ _ _ h
  refine lt_of_le_of_lt ?_ hlen
  calc acrossDist D A ≤ D (P a, P b) := iInf₂_le_of_le _ ha (iInf₂_le _ hb)
    _ ≤ D.len P a b := LSCMetric.apply_le_len D P hP.1

theorem nontrivial_sphere (c : ℂ) {r : ℝ} (hr : 0 < r) : (sphere c r).Nontrivial := by
  refine ⟨c + r, ?_, c - r, ?_, fun h => ?_⟩
  · simp [abs_of_pos hr]
  · simp [abs_of_pos hr]
  · have := congrArg Complex.re h
    simp at this
    linarith

 
theorem boundary_axiomV_data (A : EuclideanAnnulus) :
    IsConnected (((⊤ : TopologicalSpace.Opens ℂ)) : Set ℂ) ∧ IsCompact A.innerBoundary ∧
      IsCompact A.outerBoundary ∧ IsConnected A.innerBoundary ∧ IsConnected A.outerBoundary ∧
      A.innerBoundary.Nontrivial ∧ A.outerBoundary.Nontrivial ∧
      A.innerBoundary ⊆ ((⊤ : TopologicalSpace.Opens ℂ) : Set ℂ) ∧
      A.outerBoundary ⊆ ((⊤ : TopologicalSpace.Opens ℂ) : Set ℂ) ∧
      Disjoint A.innerBoundary A.outerBoundary := by
  have h₁ := A.innerRadius_pos
  have h₂ := h₁.trans A.innerRadius_lt_outerRadius
  refine ⟨by simpa using isConnected_univ, isCompact_innerBoundary A, isCompact_outerBoundary A,
    ⟨(nontrivial_sphere _ h₁).nonempty, LQGMetric.TopoCircle.isPreconnected_sphere_complex _ h₁.le⟩,
    ⟨(nontrivial_sphere _ h₂).nonempty, LQGMetric.TopoCircle.isPreconnected_sphere_complex _ h₂.le⟩,
    nontrivial_sphere _ h₁, nontrivial_sphere _ h₂, by simp, by simp, disjoint_boundaries A⟩

end SupercriticalLQGUniqueness.B2.Strong
