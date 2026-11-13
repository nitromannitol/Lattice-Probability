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

