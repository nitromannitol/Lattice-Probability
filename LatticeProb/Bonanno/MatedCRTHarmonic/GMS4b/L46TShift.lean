/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4b.L46TShift at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46SCount
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46STail
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46SWindow
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.CellModel
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.CurveAdapters
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46SCoverageTail
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46SPolylog
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.Segments
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.AreaDominates
import LatticeProb.Bonanno.MatedCRTHarmonic.GMCFacts.LowerTail
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.L46SAsymptotic
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.Window

/-!
# Translation of the gamma-cone estimates

For the local law comparison the gamma-cone singularity is placed outside the
observation disk. Translation does not change the quantum-time mesh or the
localized degree.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4b

open MatedCRTHarmonic.GMSLemma27

/-- Translate a curve while leaving its time parameter unchanged. -/
def l46tTranslateCurve (z₀ : ℂ) (c : ℝ → ℂ) : ℝ → ℂ :=
  fun t => c t + z₀

/-- The degree ball translates with the curve. -/
theorem l46t_locBall_translate (z₀ : ℂ) (c : ℝ → ℂ) (ε t : ℝ) :
    locBall ε (l46tTranslateCurve z₀ c) t =
      (fun z : ℂ => z + z₀) '' locBall ε c t := by
  have hcurve : l46tTranslateCurve z₀ c = simC 1 z₀ one_ne_zero ∘ c := by
    funext u
    simp [l46tTranslateCurve, simC_apply]
  rw [hcurve, locBall_simC]
  congr 1
  funext z
  simp [simC_apply]

/-- A smaller observation disk can be placed away from the translated
cone's root. This is the form of Lemma 2.7 needed by (4.16). -/
theorem l46t_localization_shifted_disk {γ : ℝ}
    (M : GMSLemma27.CellModel γ) (hγ : 0 < γ)
    (hSLE : GMSLemma27.SegmentsContainBalls M)
    (hGMC : GMSLemma27.GMCLowerTail γ)
    (hdom : GMSLemma27.AreaDominatesWholePlaneGFF M)
    (z₀ w : ℂ) {ρ r R : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) 1)
    (hsub : ball w r ⊆ ball z₀ ρ) (hrR : r < R) (s : ℝ) :
    ∃ C : ℝ, ∀ ε ∈ Ioo (0 : ℝ) 1,
      M.P {ω | ∃ t : ℝ,
        l46tTranslateCurve z₀ (M.curve ω) t ∈ ball w r ∧
        ¬ locBall ε (l46tTranslateCurve z₀ (M.curve ω)) t ⊆ ball w R} ≤
        ENNReal.ofReal (C * ε ^ s) := by
  obtain ⟨q, hq0, hq1, hsα⟩ := l46s_exists_lemma27_q_for_power hγ s
  obtain ⟨C, hC⟩ := GMSLemma27.lemma27_segments M hSLE hGMC hdom hγ
    hq0 hq1 hρ.1 hρ.2 hsα
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ^ q < (R - r) / 8 :=
    eventually_rpow_lt hq0 (by linarith)
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      M.P {ω | ∃ t : ℝ,
        l46tTranslateCurve z₀ (M.curve ω) t ∈ ball w r ∧
        ¬ locBall ε (l46tTranslateCurve z₀ (M.curve ω)) t ⊆ ball w R} ≤
        ENNReal.ofReal (C * ε ^ s) := by
    filter_upwards [hsmall, self_mem_nhdsWithin,
      eventually_lt_nhdsGT_zero one_pos] with ε hsmall hε0 hε1
    have hbad : {ω | ∃ t : ℝ,
        l46tTranslateCurve z₀ (M.curve ω) t ∈ ball w r ∧
        ¬ locBall ε (l46tTranslateCurve z₀ (M.curve ω)) t ⊆ ball w R} ≤ᵐ[M.P]
        (GMSLemma27.segmentDiamGood M ε q ρ)ᶜ := by
      filter_upwards [M.ae_continuous_curve] with ω hc
      rintro ⟨t, ht, hnot⟩ hgood
      apply hnot
      have htz₀ : l46tTranslateCurve z₀ (M.curve ω) t ∈ ball z₀ ρ := hsub ht
      have htc : M.curve ω t ∈ ball (0 : ℂ) ρ := by
        simpa [Metric.mem_ball, dist_eq_norm, l46tTranslateCurve] using htz₀
      have hd := diam_locWindow_le_two_mul hε0.le
        (fun a b hab hmeet => hgood a b hab hmeet) htc
      intro z hz
      rw [l46t_locBall_translate] at hz
      obtain ⟨u, hu, rfl⟩ := hz
      have hdist : dist u (M.curve ω t) ≤ 4 * diam (locWindow ε (M.curve ω) t) := hu
      have hroot : dist (l46tTranslateCurve z₀ (M.curve ω) t) w < r := ht
      rw [Metric.mem_ball]
      calc
        dist (u + z₀) w ≤ dist (u + z₀) (l46tTranslateCurve z₀ (M.curve ω) t) +
            dist (l46tTranslateCurve z₀ (M.curve ω) t) w := dist_triangle _ _ _
        _ < R := by
          have heq : dist (u + z₀) (l46tTranslateCurve z₀ (M.curve ω) t) =
              dist u (M.curve ω t) := by
            simp [l46tTranslateCurve, dist_add_right]
          rw [heq]
          linarith
    exact (measure_mono_ae hbad).trans (hC ε ⟨hε0, hε1⟩)
  exact exists_bound_of_eventually (fun _ => prob_le_one) hev

end MatedCRTHarmonic.GMS4b
