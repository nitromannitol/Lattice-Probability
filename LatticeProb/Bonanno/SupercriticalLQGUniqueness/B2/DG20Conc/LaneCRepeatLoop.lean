/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.DG20Conc.LaneCRepeatLoop at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCEssentialLoop
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Strong.LoopSep
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.DG20Conc.LaneCPhysicalScaleEventually
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6DGOsc
import LatticeProb.Bonanno.LQGMetric.Topo.Shortcut
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Strong.Glue
import Mathlib.Topology.Order.IntermediateValue

 

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set
namespace SupercriticalLQGUniqueness.B2.DG20Conc
open LQGMetric

 

def laneCRepeatLoop (τ : ℝ → ℂ) : ℝ → ℂ :=
  SupercriticalLQGUniqueness.B2.Strong.glue4 τ τ
    (fun _ => τ 0) (fun _ => τ 0)

theorem laneC_repeatLoop_continuousOn
    {τ : ℝ → ℂ} (hτ : ContinuousOn τ (Icc (0 : ℝ) 1))
    (hc : τ 0 = τ 1) :
    ContinuousOn (laneCRepeatLoop τ) (Icc (0 : ℝ) 2) := by
  have hG := SupercriticalLQGUniqueness.B2.Strong.continuousOn_glue4
    τ τ (fun _ => τ 0) (fun _ => τ 0)
    hτ hτ continuousOn_const continuousOn_const hc.symm hc.symm rfl
  exact hG.mono (Icc_subset_Icc (by norm_num) (by norm_num))

theorem laneC_repeatLoop_first
    (τ : ℝ → ℂ) : EqOn (laneCRepeatLoop τ) τ (Icc (0 : ℝ) 1) :=
  SupercriticalLQGUniqueness.B2.Strong.glue4_eqOn₀ _ _ _ _

theorem laneC_repeatLoop_second
    {τ : ℝ → ℂ} (hc : τ 0 = τ 1) :
    EqOn (laneCRepeatLoop τ) (fun x => τ (x - 1)) (Icc (1 : ℝ) 2) := by
  simpa only [laneCRepeatLoop] using
    (SupercriticalLQGUniqueness.B2.Strong.glue4_eqOn₁
      τ τ (fun _ => τ 0) (fun _ => τ 0) hc.symm)

theorem laneC_repeatLoop_mapsTo {τ : ℝ → ℂ}
    (hc : τ 0 = τ 1) {A : Set ℂ}
    (hτ : ∀ u ∈ Icc (0 : ℝ) 1, τ u ∈ A) :
    ∀ x ∈ Icc (0 : ℝ) 2, laneCRepeatLoop τ x ∈ A := by
  intro x hx
  by_cases hx1 : x ≤ 1
  · rw [(laneC_repeatLoop_first τ) (x := x) ⟨hx.1, hx1⟩]
    exact hτ x ⟨hx.1, hx1⟩
  · have hx12 : x ∈ Icc (1 : ℝ) 2 := ⟨le_of_not_ge hx1, hx.2⟩
    rw [(laneC_repeatLoop_second hc) (x := x) hx12]
    exact hτ (x - 1) (by constructor <;> linarith [hx12.1, hx12.2])

theorem laneC_repeatLoop_shift {τ : ℝ → ℂ} (hc : τ 0 = τ 1)
    {u : ℝ} (hu : u ∈ Icc (0 : ℝ) 1) :
    laneCRepeatLoop τ (u + 1) = τ u := by
  by_cases h0 : u = 0
  · subst u
    have h := (laneC_repeatLoop_first τ) (x := (1 : ℝ)) (by norm_num)
    simpa [hc] using h
  · have hu0 : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm h0)
    have hmem : u + 1 ∈ Icc (1 : ℝ) 2 := ⟨by linarith, by linarith [hu.2]⟩
    simpa using (laneC_repeatLoop_second hc) (x := u + 1) hmem

 

theorem laneC_repeatLoop_segment_cost
    (D : ContMetric) {τ : ℝ → ℂ} (hc : τ 0 = τ 1)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hst : s ≤ t) (hts : t ≤ s + 1) :
    D.len (SupercriticalLQGUniqueness.B2.Strong.seg
      (laneCRepeatLoop τ) s t) 0 1 ≤ D.len τ 0 1 := by
  have ht2 : t ≤ 2 := by linarith [hs.2]
  
  have hseg' := SupercriticalLQGUniqueness.B2.Strong.eVariationOn_seg_le
    (D.pt ∘ laneCRepeatLoop τ)
    (show s ∈ Icc s t from ⟨le_rfl, hst⟩)
    (show t ∈ Icc s t from ⟨hst, le_rfl⟩)
  have hsegCost : D.len (SupercriticalLQGUniqueness.B2.Strong.seg
      (laneCRepeatLoop τ) s t) 0 1 ≤ D.len (laneCRepeatLoop τ) s t := hseg'
  apply hsegCost.trans
  by_cases ht1 : t ≤ 1
  · have heq : D.len (laneCRepeatLoop τ) s t = D.len τ s t := by
      apply MetricGeometry.curveLength_congr
      intro x hx
      exact congrArg D.pt ((laneC_repeatLoop_first τ) (x := x)
        ⟨hs.1.trans hx.1, hx.2.trans ht1⟩)
    rw [heq]
    exact MetricGeometry.curveLength_mono (D.pt ∘ τ) hs.1 (ht1)
  · have h1t : 1 ≤ t := le_of_not_ge ht1
    have hfirst : D.len (laneCRepeatLoop τ) s 1 = D.len τ s 1 := by
      apply MetricGeometry.curveLength_congr
      intro x hx
      exact congrArg D.pt ((laneC_repeatLoop_first τ) (x := x)
        ⟨hs.1.trans hx.1, hx.2⟩)
    have hsecond : D.len (laneCRepeatLoop τ) 1 t =
        D.len (fun x => τ (x - 1)) 1 t := by
      apply MetricGeometry.curveLength_congr
      intro x hx
      exact congrArg D.pt ((laneC_repeatLoop_second hc) (x := x)
        ⟨hx.1, hx.2.trans ht2⟩)
    have hshift : D.len (fun x => τ (x - 1)) 1 t =
        D.len τ 0 (t - 1) := by
      change MetricGeometry.curveLength ((D.pt ∘ τ) ∘ (fun x => x - 1)) 1 t =
        MetricGeometry.curveLength (D.pt ∘ τ) 0 (t - 1)
      simpa using
        (MetricGeometry.curveLength_comp_of_continuousOn_monotoneOn
          (D.pt ∘ τ) h1t (φ := fun x : ℝ => x - 1)
          (by fun_prop) (by intro x _ y _ hxy; linarith))
    calc
      D.len (laneCRepeatLoop τ) s t =
          D.len (laneCRepeatLoop τ) s 1 + D.len (laneCRepeatLoop τ) 1 t :=
        (MetricGeometry.curveLength_add _ hs.2 h1t).symm
      _ = D.len τ s 1 + D.len τ 0 (t - 1) := by rw [hfirst, hsecond, hshift]
      _ ≤ D.len τ s 1 + D.len τ 0 s := by
        have hmono : D.len τ 0 (t - 1) ≤ D.len τ 0 s :=
          MetricGeometry.curveLength_mono (D.pt ∘ τ) le_rfl (by linarith)
        exact add_le_add (le_refl _) hmono
      _ = D.len τ 0 1 := by
        rw [add_comm]
        exact MetricGeometry.curveLength_add (D.pt ∘ τ) hs.1 hs.2

 

theorem laneC_repeatLoop_segment_cost_any
    (D : ContMetric) {τ : ℝ → ℂ} (hc : τ 0 = τ 1)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 2)
    (hst : s ≤ t) (ht2 : t ≤ 2) (hts : t ≤ s + 1) :
    D.len (SupercriticalLQGUniqueness.B2.Strong.seg
      (laneCRepeatLoop τ) s t) 0 1 ≤ D.len τ 0 1 := by
  by_cases hs1 : s ≤ 1
  · exact laneC_repeatLoop_segment_cost D hc ⟨hs.1, hs1⟩ hst hts
  · have h1s : 1 ≤ s := le_of_not_ge hs1
    have hss : s ∈ Icc (1 : ℝ) 2 := ⟨h1s, hs.2⟩
    have htt : t ∈ Icc (1 : ℝ) 2 := ⟨h1s.trans hst, ht2⟩
    have hseg := SupercriticalLQGUniqueness.B2.Strong.eVariationOn_seg_le
      (D.pt ∘ laneCRepeatLoop τ) hss htt
    have hsegCost : D.len (SupercriticalLQGUniqueness.B2.Strong.seg
        (laneCRepeatLoop τ) s t) 0 1 ≤
        D.len (laneCRepeatLoop τ) 1 2 := hseg
    apply hsegCost.trans
    have heq : D.len (laneCRepeatLoop τ) 1 2 =
        D.len (fun x => τ (x - 1)) 1 2 := by
      apply MetricGeometry.curveLength_congr
      intro x hx
      exact congrArg D.pt ((laneC_repeatLoop_second hc) (x := x) hx)
    rw [heq]
    have hshift : D.len (fun x => τ (x - 1)) 1 2 = D.len τ 0 1 := by
      change eVariationOn (fun x : ℝ => (D.pt ∘ τ) (x - 1)) (Icc 1 2) =
        eVariationOn (D.pt ∘ τ) (Icc 0 1)
      simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using
        (SupercriticalLQGUniqueness.B2.Strong.eVariationOn_shift
          (D.pt ∘ τ) 1)
    exact hshift.le

end SupercriticalLQGUniqueness.B2.DG20Conc
