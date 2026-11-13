/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4b.L46SWindow at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46SAsymptotic
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.Window

/-!
# Superpolynomial containment of local windows

For every interior radius `ρ<1` and every requested failure power, choose
The small diameter exponent in [18] Lemma 2.7 to make all two-mesh windows
rooted in `B_ρ` lie in `B₁` outside an `O(ε^s)` event.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4b

open MatedCRTHarmonic.GMSLemma27

/-- The small-window localization used in [18] Lemma 4.6, uniformly in
all root times and with an arbitrary polynomial failure power. -/
theorem l46s_window_in_unit_ball_superpoly {γ : ℝ}
    (M : CellModel γ) (hγ : 0 < γ)
    (hSLE : SegmentsContainBalls M) (hGMC : GMCLowerTail γ)
    (hdom : AreaDominatesWholePlaneGFF M)
    {ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1) (s : ℝ) :
    ∃ C : ℝ, ∀ ε ∈ Ioo (0 : ℝ) 1,
      M.P {ω | ∃ t : ℝ, M.curve ω t ∈ ball (0 : ℂ) ρ ∧
        ¬ locWindow ε (M.curve ω) t ⊆ ball (0 : ℂ) 1} ≤
        ENNReal.ofReal (C * ε ^ s) := by
  obtain ⟨q, hq0, hq1, hsα⟩ := l46s_exists_lemma27_q_for_power hγ s
  obtain ⟨C, hC⟩ := lemma27_segments M hSLE hGMC hdom hγ hq0 hq1 hρ.1 hρ.2 hsα
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ q < (1 - ρ) / 2 :=
    eventually_rpow_lt hq0 (by linarith [hρ.2])
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      M.P {ω | ∃ t : ℝ, M.curve ω t ∈ ball (0 : ℂ) ρ ∧
        ¬ locWindow ε (M.curve ω) t ⊆ ball (0 : ℂ) 1} ≤
        ENNReal.ofReal (C * ε ^ s) := by
    filter_upwards [hsmall, self_mem_nhdsWithin, eventually_lt_nhdsGT_zero one_pos]
      with ε hsmall hε0 hε1
    have hεpos : 0 < ε := hε0
    have hsub : {ω | ∃ t : ℝ, M.curve ω t ∈ ball (0 : ℂ) ρ ∧
        ¬ locWindow ε (M.curve ω) t ⊆ ball (0 : ℂ) 1} ≤ᵐ[M.P]
          (segmentDiamGood M ε q ρ)ᶜ := by
      filter_upwards [M.ae_continuous_curve] with ω hc
      rintro ⟨t, ht, hbad⟩ hgood
      apply hbad
      have hd := diam_locWindow_le_two_mul hεpos.le
        (fun a b hab hmeet => hgood a b hab hmeet) ht
      intro z hz
      have htW : M.curve ω t ∈ locWindow ε (M.curve ω) t :=
        ⟨t, ⟨by linarith, by linarith⟩, rfl⟩
      have hb : Bornology.IsBounded (locWindow ε (M.curve ω) t) :=
        (isCompact_Icc.image hc).isBounded
      have hdist := Metric.dist_le_diam_of_mem hb hz htW
      have hρ' : dist (M.curve ω t) (0 : ℂ) < ρ := ht
      have hsmall' : 2 * ε ^ q < 1 - ρ := by linarith
      rw [Metric.mem_ball]
      calc
        dist z (0 : ℂ) ≤ dist z (M.curve ω t) + dist (M.curve ω t) 0 := dist_triangle _ _ _
        _ < 1 := by linarith
    exact (measure_mono_ae hsub).trans (hC ε ⟨hε0, hε1⟩)
  exact exists_bound_of_eventually (fun _ => prob_le_one) hev

end MatedCRTHarmonic.GMS4b
