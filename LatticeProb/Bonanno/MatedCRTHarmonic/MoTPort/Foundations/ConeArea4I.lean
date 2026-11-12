/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTPort.Foundations.ConeArea4I at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
/- Provenance: ported from an earlier mating-of-trees formalization; only imports and namespace names were changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea4H

/-!
* `eventually_lt_top_add_ofFunC` (deterministic): if the approximations of `x` are eventually
  finite on compacts and `g` is locally integrable and continuous off `0`, then the
  approximations of `x + g` are eventually finite on every compact `K ∌ 0` (on `K`, at small
  scales, `(x+g)_r(z) = x_r(z) + g_r(z)` with `|g_r(z)| ≤ sup_L |g|`, `L` a compact annulus);
* `ae_fin_away_coneField`: this for the cone field (inputs (R1)–(R3), ConeArea4D–G);
* `fin_of_away_of_tight`: (b2) on all compacts follows from (b2) away from `0` and (b3);
* **`coneRefMeas_of_tight`**: `ConeRefMeas γ W` for `0 < γ < 2` from (b3) (tightness of the
  cone-field approximations at `0`) alone.

Own elementary glue (density comparison, as in ConeArea3 / ConeArea4B).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace MatedCRTHarmonic.MoTPort
namespace ConeArea4

open QuantumZipper LQGMetric

/-- **finiteness away from `0` after adding a function continuous off `0`** -/
theorem eventually_lt_top_add_ofFunC {γ : ℝ} {x : Field} (hc : ConeArea.HasCircleAvgs x)
    {g : ℂ → ℝ} (hgl : LocallyIntegrable g volume) (hg : ContinuousOn g (univ \ {0}))
    (hfin : ∀ K, IsCompact K → ∀ᶠ k in atTop, areaApproxC γ x k K < ⊤)
    {K : Set ℂ} (hK : IsCompact K) (h0 : (0 : ℂ) ∉ K) :
    ∀ᶠ k in atTop, areaApproxC γ (x + ofFunC g) k K < ⊤ := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact Eventually.of_forall fun k => by simp
  obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hne continuous_norm.continuousOn
  set δ := ‖z₀‖
  have hδ : 0 < δ := norm_pos_iff.2 fun h => h0 (h ▸ hz₀)
  obtain ⟨M, hM⟩ := hK.isBounded.subset_closedBall 0
  set L : Set ℂ := {w : ℂ | δ / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ M + 1}
  have hLc : IsCompact L :=
    (isCompact_closedBall (0 : ℂ) (M + 1)).of_isClosed_subset
      ((isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const))
      fun w hw => by simpa [mem_closedBall, dist_zero_right] using hw.2
  have hLU : L ⊆ univ \ {0} := fun w hw =>
    ⟨mem_univ _, fun h => by
      rw [mem_singleton_iff] at h
      have := hw.1; rw [h, norm_zero] at this; linarith⟩
  obtain ⟨C, hC⟩ := hLc.exists_bound_of_continuousOn (hg.mono hLU)
  have hr : Tendsto radius atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hUo : IsOpen (univ \ {(0 : ℂ)}) := isOpen_univ.sdiff isClosed_singleton
  filter_upwards [hfin K hK, hr.eventually (gt_mem_nhds (show (0 : ℝ) < min (δ / 2) 1 by
    positivity))] with k hk hrk
  have hrk1 : radius k < δ / 2 := lt_of_lt_of_le hrk (min_le_left _ _)
  have hrk2 : radius k < 1 := lt_of_lt_of_le hrk (min_le_right _ _)
  have hrpos := QuantumZipper.radius_pos k
  have hsph : ∀ z ∈ K, sphere z (radius k) ⊆ L := fun z hz w hw => by
    rw [mem_sphere, dist_eq_norm] at hw
    have h1 : δ ≤ ‖z‖ := hmin hz
    have h2 : ‖z‖ ≤ M := by simpa [mem_closedBall, dist_zero_right] using hM hz
    have h3 : ‖z‖ ≤ ‖w‖ + ‖w - z‖ := by
      have := norm_sub_le w (w - z); simp only [sub_sub_cancel] at this; linarith [norm_sub_rev w z]
    have h4 : ‖w‖ ≤ ‖z‖ + ‖w - z‖ := by
      have := norm_add_le z (w - z); simp only [add_sub_cancel] at this; linarith
    exact ⟨by linarith, by linarith⟩
  have hbd : ∀ᵐ z ∂(volume.restrict K),
      ENNReal.ofReal (radius k ^ (γ ^ 2 / 2) *
        Real.exp (γ * circleAvg (x + ofFunC g) (radius k) z)) ≤
      ENNReal.ofReal (Real.exp (|γ| * C)) * ENNReal.ofReal (radius k ^ (γ ^ 2 / 2) *
        Real.exp (γ * circleAvg x (radius k) z)) := by
    filter_upwards [ae_restrict_of_ae (hc k), ae_restrict_mem hKm] with z ⟨a, ha⟩ hzK
    have hs : sphere z (radius k) ⊆ univ \ {0} := (hsph z hzK).trans hLU
    rw [ConeArea3.circleAvg_add_ofFunC hgl hUo hg hrpos hs ha,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    have hca : |Real.circleAverage g z (radius k)| ≤ C := by
      refine (Real.abs_circleAverage_le_circleAverage_abs).trans ?_
      refine Real.circleAverage_mono_on_of_le_circle ?_ fun w hw => ?_
      · exact ContinuousOn.circleIntegrable hrpos.le ((hg.mono hs).abs)
      · rw [abs_of_pos hrpos] at hw
        simpa [Real.norm_eq_abs] using hC w (hsph z hzK hw)
    have hγc : γ * Real.circleAverage g z (radius k) ≤ |γ| * C := by
      calc γ * Real.circleAverage g z (radius k)
          ≤ |γ * Real.circleAverage g z (radius k)| := le_abs_self _
        _ = |γ| * |Real.circleAverage g z (radius k)| := abs_mul _ _
        _ ≤ |γ| * C := mul_le_mul_of_nonneg_left hca (abs_nonneg γ)
    have he : Real.exp (γ * (circleAvg x (radius k) z + Real.circleAverage g z (radius k))) ≤
        Real.exp (|γ| * C) * Real.exp (γ * circleAvg x (radius k) z) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by nlinarith)
    have hr0 : 0 ≤ radius k ^ (γ ^ 2 / 2) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left he hr0]
  unfold areaApproxC
  rw [withDensity_apply _ hKm]
  refine (lintegral_mono_ae hbd).trans_lt ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  unfold areaApproxC at hk
  rwa [withDensity_apply _ hKm] at hk

/-- (b2) on all compacts from (b2) away from `0` and tightness (b3) -/
theorem fin_of_away_of_tight {μs : ℕ → Measure ℂ}
    (haway : ∀ K, IsCompact K → (0 : ℂ) ∉ K → ∀ᶠ k in atTop, μs k K < ⊤)
    (htight : ∀ ε : ℝ, 0 < ε → ∃ δ > 0, ∀ᶠ k in atTop, μs k (ball 0 δ) ≤ ENNReal.ofReal ε)
    {K : Set ℂ} (hK : IsCompact K) : ∀ᶠ k in atTop, μs k K < ⊤ := by
  obtain ⟨δ, hδ, hδt⟩ := htight 1 one_pos
  have hK' : IsCompact (K ∩ (ball (0 : ℂ) δ)ᶜ) := hK.inter_right isOpen_ball.isClosed_compl
  have h0 : (0 : ℂ) ∉ K ∩ (ball (0 : ℂ) δ)ᶜ := fun h => h.2 (mem_ball_self hδ)
  filter_upwards [hδt, haway _ hK' h0] with k h1 h2
  calc μs k K ≤ μs k (ball 0 δ ∪ K ∩ (ball (0 : ℂ) δ)ᶜ) := measure_mono fun z hz => by
          by_cases hb : z ∈ ball (0 : ℂ) δ
          · exact Or.inl hb
          · exact Or.inr ⟨hz, hb⟩
    _ ≤ μs k (ball 0 δ) + μs k (K ∩ (ball (0 : ℂ) δ)ᶜ) := measure_union_le _ _
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨h1.trans_lt ENNReal.ofReal_lt_top, h2⟩

/-- **(b2) away from `0` for the cone field** -/
theorem ae_fin_away_coneField {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X : Ω → Field} {A : ℝ → Ω → ℝ} {γ α Q : ℝ}
    (hX : IsWholePlaneGFF X P) (hA : IsConeProcess α Q A P) (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∀ᵐ ω ∂P, ∀ K, IsCompact K → (0 : ℂ) ∉ K → ∀ᶠ k in atTop,
      areaApproxC γ (coneField (lateralPartC (X ω)) (fun t => A t ω) Q) k K < ⊤ := by
  filter_upwards [ae_areaGood_univ hX hγ hγ2, ae_radial_R2 hX,
    ae_locallyIntegrable_coneProfile hA, ConeArea3.ae_hasCircleAvgs hX,
    (ConeMeas2.aemeasurable_conePath hA).2] with ω hgood ⟨R, hRc, hRm, hxR, hRl⟩ hAl hc hAc
    K hK h0
  rw [ConeArea3.coneField_eq_add_ofFunC hxR hRl hAl]
  exact eventually_lt_top_add_ofFunC hc (hAl.sub hRl)
    (ConeArea3.continuousOn_coneShift hAc Q hRc) (fun K hK => hgood.2 K hK (subset_univ K)) hK h0

end ConeArea4
end MatedCRTHarmonic.MoTPort
