/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SLUMetricAPI2 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.SLUMetricAPI
import LatticeProb.Bonanno.LQGMetric.Topo.Disconnect
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import LatticeProb.Bonanno.LQGMetric.Metric.CurveNatural
import LatticeProb.Bonanno.LQGMetric.Metric.Internal
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

 




















set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal NNReal Pointwise

namespace SupercriticalLQGUniqueness

namespace LSCMetric


theorem apply_le_len (D : LSCMetric) (P : ℝ → ℂ) {a b : ℝ} (hab : a ≤ b) :
    D (P a, P b) ≤ D.len P a b :=
  eVariationOn.edist_le (D.pt ∘ P) (left_mem_Icc.2 hab) (right_mem_Icc.2 hab)

 
theorem internal_eq_internalEDist (D : LSCMetric) (Y : Set ℂ) (p : Y × Y) :
    D.internal Y p =
      LQGMetric.MetricGeometry.internalEDist (D.pt '' Y) (D.pt p.1) (D.pt p.2) := by
  refine le_antisymm ?_ ?_
  · refine le_iInf fun γ => ?_
    have htr : ∀ t ∈ Icc (0 : ℝ) 1, (γ.1.extend t : ℂ) ∈ Y := by
      intro t ht
      obtain ⟨x, hx, hxt⟩ := γ.2 ⟨t, ht⟩
      rw [Path.extend_apply γ.1 ht, ← hxt]
      exact hx
    exact iInf_le_of_le (fun t => (γ.1.extend t : ℂ)) <| iInf_le_of_le 0 <| iInf_le_of_le 1 <|
      iInf_le_of_le ⟨zero_le_one, γ.1.continuous_extend.continuousOn⟩ <| iInf_le_of_le htr <|
      iInf_le_of_le γ.1.extend_zero <| iInf_le_of_le γ.1.extend_one le_rfl
  · refine le_iInf fun P => le_iInf fun a => le_iInf fun b => le_iInf fun hP => le_iInf fun hY =>
      le_iInf fun ha => le_iInf fun hb => ?_
    have h := LQGMetric.MetricGeometry.internalEDist_le_curveLength (X := D.Space)
      (Y := D.pt '' Y) (P := D.pt ∘ P) hP.1 hP.2 (fun t ht => ⟨P t, hY t ht, rfl⟩)
    have ha' : (D.pt ∘ P) a = D.pt p.1 := congrArg D.pt ha
    have hb' : (D.pt ∘ P) b = D.pt p.2 := congrArg D.pt hb
    rw [ha', hb'] at h
    exact h

 

theorem isExtMetric_internal (D : LSCMetric) (Y : Set ℂ) : IsExtMetric (D.internal Y) := by
  refine ⟨fun x => ?_, fun x y h => ?_, fun x y => ?_, fun x y z => ?_⟩
  · rw [internal_eq_internalEDist]
    exact LQGMetric.MetricGeometry.internalEDist_self ⟨x.1, x.2, rfl⟩
  · rw [internal_eq_internalEDist] at h
    have h1 := (LQGMetric.MetricGeometry.edist_le_internalEDist _ _ _).trans h.le
    exact Subtype.ext (D.isExtMetric.eq_of_eq_zero _ _ (le_antisymm h1 bot_le))
  · simp only [internal_eq_internalEDist]
    exact LQGMetric.MetricGeometry.internalEDist_comm _ _ _
  · simp only [internal_eq_internalEDist]
    exact LQGMetric.MetricGeometry.internalEDist_triangle _ _ _ _

 

end LSCMetric

 

section CurveEuclidean

variable {D : LSCMetric} {P : ℝ → ℂ} {a b : ℝ}

 


theorem LSCMetric.IsCurve.isClosed_inter_preimage (hP : D.IsCurve P a b) {F : Set ℂ}
    (hF : IsCompact F) : IsClosed (Icc a b ∩ P ⁻¹' F) := by
  refine IsSeqClosed.isClosed fun t t₀ ht htt₀ => ?_
  have ht₀ : t₀ ∈ Icc a b :=
    isClosed_Icc.mem_of_tendsto htt₀ (Eventually.of_forall fun n => (ht n).1)
  obtain ⟨y, hyF, φ, hφ, hy⟩ := hF.tendsto_subseq (fun n => (ht n).2)
  have hcont : Tendsto (fun k => D.pt (P (t (φ k)))) atTop (𝓝 (D.pt (P t₀))) :=
    (hP.2 t₀ ht₀).tendsto.comp (tendsto_nhdsWithin_iff.2
      ⟨htt₀.comp hφ.tendsto_atTop, Eventually.of_forall fun k => (ht (φ k)).1⟩)
  have hD0 : Tendsto (fun k => D (P (t (φ k)), P t₀)) atTop (𝓝 0) :=
    tendsto_iff_edist_tendsto_0.1 hcont
  have hlsc := (lowerSemicontinuous_iff_seq.1 D.lowerSemicontinuous)
    (fun k => (P (t (φ k)), P t₀)) (y, P t₀) (hy.prodMk_nhds tendsto_const_nhds)
  rw [hD0.liminf_eq] at hlsc
  have hy0 : y = P t₀ := D.isExtMetric.eq_of_eq_zero _ _ (le_antisymm hlsc bot_le)
  refine ⟨ht₀, ?_⟩
  rw [Set.mem_preimage, ← hy0]
  exact hyF
theorem LSCMetric.IsCurve.measurable_restrict (hP : D.IsCurve P a b) :
    Measurable ((Icc a b).domRestrict P) := by
  refine measurable_of_isClosed fun s hs => ?_
  have hrw : (Icc a b).domRestrict P ⁻¹' s =
      ⋃ n : ℕ, Subtype.val ⁻¹' (Icc a b ∩ P ⁻¹' (s ∩ Metric.closedBall 0 n)) := by
    ext t
    simp only [Set.mem_preimage, Set.domRestrict_apply, Set.mem_iUnion, Set.mem_inter_iff,
      Metric.mem_closedBall, dist_zero_right]
    constructor
    · intro h
      obtain ⟨n, hn⟩ := exists_nat_ge ‖P t‖
      exact ⟨n, t.2, h, hn⟩
    · rintro ⟨n, -, h, -⟩
      exact h
  rw [hrw]
  exact MeasurableSet.iUnion fun n =>
    (hP.isClosed_inter_preimage ((isCompact_closedBall 0 (n : ℝ)).inter_left hs)).measurableSet.preimage
      measurable_subtype_coe

theorem LSCMetric.IsCurve.aemeasurable (hP : D.IsCurve P a b) :
    AEMeasurable P (volume.restrict (Icc a b)) :=
  (aemeasurable_restrict_iff_comap_subtype measurableSet_Icc).2 hP.measurable_restrict.aemeasurable

 



 
theorem LSCMetric.IsCurve.continuousOn_of_mapsTo (hP : D.IsCurve P a b) {B : Set ℂ}
    (hB : IsCompact B) (hPB : MapsTo P (Icc a b) B) : ContinuousOn P (Icc a b) := by
  rw [continuousOn_iff_isClosed]
  intro F hF
  refine ⟨Icc a b ∩ P ⁻¹' (F ∩ B), hP.isClosed_inter_preimage (hB.inter_left hF), ?_⟩
  ext t
  simp only [Set.mem_inter_iff, Set.mem_preimage]
  constructor
  · rintro ⟨hF', ht⟩
    exact ⟨⟨ht, hF', hPB ht⟩, ht⟩
  · rintro ⟨⟨-, hF', -⟩, ht⟩
    exact ⟨hF', ht⟩

 

theorem LSCMetric.IsCurve.isClosed_image (hP : D.IsCurve P a b) : IsClosed (P '' Icc a b) := by
  refine IsSeqClosed.isClosed fun y y₀ hy hyy₀ => ?_
  choose t ht hty using hy
  obtain ⟨t₀, ht₀, φ, hφ, htφ⟩ := isCompact_Icc.tendsto_subseq ht
  have hcont : Tendsto (fun k => D.pt (P (t (φ k)))) atTop (𝓝 (D.pt (P t₀))) :=
    (hP.2 t₀ ht₀).tendsto.comp
      (tendsto_nhdsWithin_iff.2 ⟨htφ, Eventually.of_forall fun k => ht (φ k)⟩)
  have hD0 : Tendsto (fun k => D (P (t (φ k)), P t₀)) atTop (𝓝 0) :=
    tendsto_iff_edist_tendsto_0.1 hcont
  have hyφ : Tendsto (fun k => P (t (φ k))) atTop (𝓝 y₀) := by
    simp only [hty]
    exact hyy₀.comp hφ.tendsto_atTop
  have hlsc := (lowerSemicontinuous_iff_seq.1 D.lowerSemicontinuous)
    (fun k => (P (t (φ k)), P t₀)) (y₀, P t₀) (hyφ.prodMk_nhds tendsto_const_nhds)
  rw [hD0.liminf_eq] at hlsc
  exact ⟨t₀, ht₀, (D.isExtMetric.eq_of_eq_zero _ _ (le_antisymm hlsc bot_le)).symm⟩

end CurveEuclidean

 


theorem disconnects_iff_lqgMetric_disconnects {K E F : Set ℂ} (hK : IsClosed K) :
    Disconnects K E F ↔ LQGMetric.Disconnects K E F := by
  constructor
  · intro h x y γ hx hy
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    exact h ⟨range γ, isPreconnected_range γ.continuous,
      fun z hz hzK => (Set.eq_empty_iff_forall_notMem.1 hne) z ⟨hz, hzK⟩,
      ⟨x, ⟨0, γ.source⟩, hx⟩, ⟨y, ⟨1, γ.target⟩, hy⟩⟩
  · rintro h ⟨S, hS, hSK, ⟨x, hxS, hxE⟩, ⟨y, hyS, hyF⟩⟩
    have hC : IsPathConnected (connectedComponentIn Kᶜ x) :=
      (hK.isOpen_compl.connectedComponentIn.isConnected_iff_isPathConnected).1
        (isConnected_connectedComponentIn_iff.2 (hSK hxS))
    have hSC : S ⊆ connectedComponentIn Kᶜ x := hS.subset_connectedComponentIn hxS hSK
    obtain ⟨γ, hγ⟩ := hC.joinedIn x (hSC hxS) y (hSC hyS)
    obtain ⟨z, ⟨t, rfl⟩, hzK⟩ := h x y γ hxE hyF
    exact connectedComponentIn_subset _ _ (hγ t) hzK

 

namespace EuclideanAnnulus

variable (A : EuclideanAnnulus)

theorem toSet_eq :
    A.toSet = {z | A.innerRadius < dist z A.center ∧ dist z A.center < A.outerRadius} := by
  ext z
  simp only [toSet, closure_ball _ A.innerRadius_pos.ne', Set.mem_sdiff,
    Metric.mem_ball, Metric.mem_closedBall, not_le, Set.mem_ofPred_eq]
  exact and_comm

theorem toSet_dilate (r : ℝ) (hr : 0 < r) : (A.dilate r hr).toSet = r • A.toSet := by
  have hr0 : r ≠ 0 := hr.ne'
  have h1 : 0 < A.innerRadius := A.2.1
  have hinj : Function.Injective (fun x : ℂ => r • x) := smul_right_injective ℂ hr0
  have hc : (A.dilate r hr).center = r • A.center := rfl
  have hi : (A.dilate r hr).innerRadius = r * A.innerRadius := rfl
  have ho : (A.dilate r hr).outerRadius = r * A.outerRadius := rfl
  rw [← Set.image_smul]
  unfold EuclideanAnnulus.toSet
  rw [hc, hi, ho, Set.image_sdiff hinj, Set.image_smul, Set.image_smul,
    closure_ball _ h1.ne', closure_ball _ (mul_pos hr h1).ne', smul_closedBall _ _ h1.le,
    smul_ball hr0, Real.norm_eq_abs, abs_of_pos hr]

theorem innerBoundary_dilate (r : ℝ) (hr : 0 < r) :
    (A.dilate r hr).innerBoundary = r • A.innerBoundary := by
  rw [innerBoundary, innerBoundary, smul_sphere' hr.ne', Real.norm_of_nonneg hr.le]
  rfl

theorem outerBoundary_dilate (r : ℝ) (hr : 0 < r) :
    (A.dilate r hr).outerBoundary = r • A.outerBoundary := by
  rw [outerBoundary, outerBoundary, smul_sphere' hr.ne', Real.norm_of_nonneg hr.le]
  rfl

 
end EuclideanAnnulus

 

 

end SupercriticalLQGUniqueness

