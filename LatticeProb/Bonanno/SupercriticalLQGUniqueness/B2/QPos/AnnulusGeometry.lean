/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.AnnulusGeometry at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.P18Geom
import LatticeProb.Bonanno.LQGMetric.Topo.RectCross
import Mathlib.Topology.MetricSpace.Bounded

 







set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open scoped ENNReal
open LQGMetric LQGMetric.DDDF LQGMetric.LFPP

namespace SupercriticalLQGUniqueness.B2.QPos

 
def squareRadius (z : ℂ) : ℝ := max |z.re| |z.im|

 
def upperAnnulus : Set ℂ := {z | (9 / 20 : ℝ) ≤ squareRadius z ∧ squareRadius z ≤ 3 / 4}

def upperAnnulusInner : Set ℂ := {z | squareRadius z = 9 / 20}
def upperAnnulusOuter : Set ℂ := {z | squareRadius z = 3 / 4}

theorem upperAnnulus_isCompact : IsCompact upperAnnulus := by
  have hc : Continuous squareRadius :=
    (continuous_abs.comp Complex.continuous_re).max
      (continuous_abs.comp Complex.continuous_im)
  have hclosed : IsClosed upperAnnulus := by
    change IsClosed (squareRadius ⁻¹' Icc (9 / 20 : ℝ) (3 / 4))
    exact isClosed_Icc.preimage hc
  have hb : Bornology.IsBounded upperAnnulus := by
    apply (isBounded_iff_forall_norm_le).2
    refine ⟨2, fun z hz => ?_⟩
    have hz' : squareRadius z ≤ 3 / 4 := hz.2
    have hr : |z.re| ≤ 3 / 4 := (le_max_left _ _).trans hz'
    have hi : |z.im| ≤ 3 / 4 := (le_max_right _ _).trans hz'
    exact (Complex.norm_le_abs_re_add_abs_im z).trans (by linarith)
  exact Metric.isCompact_iff_isClosed_bounded.mpr ⟨hclosed, hb⟩

 
def eastCorridor : MarkedRect := ⟨2 / 5, -1 / 16, 3 / 8, 1 / 8, true⟩

 

theorem upperAnnulus_crossLen_le_eastCorridor (ξ : ℝ) (f : ℂ → ℝ) :
    crossLenIn ξ f upperAnnulus upperAnnulusInner upperAnnulusOuter ≤
      rectLen ξ f eastCorridor := by
  unfold rectLen
  apply le_crossLenIn
  intro P hP
  obtain ⟨z, hz, w, hw, hpath, htrace⟩ := hP
  have hzre : (P 0).re = 2 / 5 := by
    rw [hpath.source]
    simpa [eastCorridor, MarkedRect.side₁, Complex.mem_reProdIm] using hz.1
  have hwre : (P 1).re = 31 / 40 := by
    rw [hpath.target]
    have h : w.re = 2 / 5 + 3 / 8 := by
      simpa [eastCorridor, MarkedRect.side₂, Complex.mem_reProdIm] using hw.1
    linarith
  have hcont : ContinuousOn (fun t => (P t).re) (Icc (0 : ℝ) 1) :=
    Complex.continuous_re.comp_continuousOn hpath.continuousOn
  obtain ⟨s, t, hs, hst, ht, hsre, htre, hbetween⟩ :=
    RectCross.exists_sub_crossing (f := fun u => (P u).re) zero_le_one
      hcont (by norm_num : (9 / 20 : ℝ) ≤ 3 / 4)
      (by rw [hzre]; norm_num) (by rw [hwre]; norm_num)
  have hstrip : ∀ u ∈ Icc s t,
      (9 / 20 : ℝ) ≤ (P u).re ∧ (P u).re ≤ 3 / 4 ∧
      -(1 / 16 : ℝ) ≤ (P u).im ∧ (P u).im ≤ 1 / 16 := by
    intro u hu
    have hre := hbetween u hu
    have hrect := htrace u ⟨hs.trans hu.1, hu.2.trans ht⟩
    simp only [eastCorridor, MarkedRect.toSet, Complex.mem_reProdIm, mem_Icc] at hrect
    norm_num at hrect
    exact ⟨hre.1, hre.2, hrect.2.1, hrect.2.2⟩
  have hradius : ∀ u ∈ Icc s t, squareRadius (P u) = (P u).re := by
    intro u hu
    obtain ⟨hre0, _, him0, him1⟩ := hstrip u hu
    have hre : 0 ≤ (P u).re := by linarith
    have him : |(P u).im| ≤ (P u).re := by
      apply abs_le.mpr
      constructor <;> linarith
    simp only [squareRadius, abs_of_nonneg hre, max_eq_left him]
  have hK : ∀ u ∈ Icc s t, P u ∈ upperAnnulus := by
    intro u hu
    have hr := hradius u hu
    have hs' := hstrip u hu
    exact ⟨hr ▸ hs'.1, hr ▸ hs'.2.1⟩
  have hA : P s ∈ upperAnnulusInner := by
    change squareRadius (P s) = 9 / 20
    rw [hradius s ⟨le_rfl, hst⟩, hsre]
  have hB : P t ∈ upperAnnulusOuter := by
    change squareRadius (P t) = 3 / 4
    rw [hradius t ⟨hst, le_rfl⟩, htre]
  calc
    crossLenIn ξ f upperAnnulus upperAnnulusInner upperAnnulusOuter ≤
        ∫⁻ u in Ioo s t, lenDens ξ f P u :=
      crossLenIn_le_setLIntegral_Ioo hpath hs hst ht hK hA hB
    _ ≤ lfppLen ξ f P := by
      rw [lfppLen_eq]
      apply lintegral_mono_set
      intro u hu
      exact ⟨hs.trans hu.1.le, hu.2.le.trans ht⟩

end SupercriticalLQGUniqueness.B2.QPos
