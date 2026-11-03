/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S2.SpatialIndepOsc at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndepMoment

/-!
# GM Lemma 2.7: tightness of the oscillation of the harmonic part, uniformly in the configuration

GM l. 979–988 (`literature/src/1905.00383/uniqueness-final.tex`): `𝔐_z = sup_{B_{1+s/2}(z)}
|𝔥 − 𝔥(z)|` satisfies `P[𝔐_z ≤ A] ≥ 1 − ε` with `A` independent of `z` and of the configuration.
Own argument (see `SpatialIndepTight`): with `δ = (1−ρ₂)R/3`, `ρ = ρ₂R + δ`,
`|g(u) − g(z)| ≤ c ∫_{B̄(z,ρ)} |G(ψ_y − ψ_z)| dy` (mean value, `abs_sub_le_integral_of_harmonic`,
`pair_radBump_of_harmonic`), then Tonelli, Cauchy–Schwarz and `integral_sq_radDiff_le`, and
Markov's inequality.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set TopologicalSpace Metric InnerProductSpace
open scoped ENNReal

namespace LQGMetric.GM

open Blueprint

/-- the oscillation event: `G` is given on `B(z,R)` by a harmonic `g` with
`sup_{B(z,ρ₂R)} |g − g(z)| > A` -/
def oscEv {Ω : Type} (G : Ω → DistC) (z : ℂ) (R ρ₂ A : ℝ) : Set Ω :=
  {ω | ∃ g : ℂ → ℝ, HarmonicOnNhd g (ball z R) ∧
    (∀ φ : TestOn (ballO z R), restrictTo (ballO z R) (G ω) φ = ∫ x, g x * φ x) ∧
    ∃ u ∈ ball z (ρ₂ * R), A < |g u - g z|}

/-- the constant `c = e(δ²)/(∫ radProf δ)²` -/
def oscC (δ : ℝ) : ℝ := expNegInvGlue (δ ^ 2) / (∫ y, radProf δ y) / (∫ y, radProf δ y)

/-- **Uniform tightness of `𝔐_z`** (own argument replacing GM l. 985–986). -/
theorem prob_oscEv_le {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h hz G : Ω → DistC} (hh : IsWholePlaneGFF h P) {V : Opens ℂ}
    (hzb : IsZeroBoundaryGFF V (fun ω => restrictTo V (hz ω)) P)
    (hind : Indep (MeasurableSpace.comap hz inferInstance) (MeasurableSpace.comap G inferInstance) P)
    (hdec : ∀ᵐ ω ∂P, h ω = G ω + hz ω) (hGm : Measurable G) {z : ℂ} {R ρ₂ : ℝ} (hR : 0 < R)
    (hρ₂0 : 0 ≤ ρ₂) (hρ₂ : ρ₂ < 1) (hBV : ball z R ⊆ V) {A : ℝ} (hA : 0 < A) :
    P (oscEv G z R ρ₂ A) ≤ volume (closedBall z (ρ₂ * R + (1 - ρ₂) * R / 3)) *
      ENNReal.ofReal (√(radK ((1 - ρ₂) * R / 3) (ρ₂ * R + (1 - ρ₂) * R / 3))) /
      ENNReal.ofReal (A / oscC ((1 - ρ₂) * R / 3)) := by
  set δ := (1 - ρ₂) * R / 3 with hδdef
  set ρ := ρ₂ * R + δ with hρdef
  have hpos : 0 < (1 - ρ₂) * R := mul_pos (sub_pos.2 hρ₂) hR
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hρ : 0 ≤ ρ := by rw [hρdef]; exact add_nonneg (mul_nonneg hρ₂0 hR.le) hδ.le
  have hρR : ρ + δ < R := by rw [hρdef, hδdef]; nlinarith
  have hI := integral_radProf_pos hδ
  set I := ∫ y, radProf δ y
  have hc : 0 < oscC δ := by
    unfold oscC; have := expNegInvGlue.pos_of_pos (by positivity : 0 < δ ^ 2); positivity
  set X : Ω → ℂ → ℝ := fun ω y => G ω (radDiff hδ.le y z).1 with hXdef
  have hXy : ∀ ω y, X ω y = G ω (radBump δ hδ.le y) - G ω (radBump δ hδ.le z) := fun ω y => by
    simp only [hXdef, radDiff, map_sub]
  have hXm : Measurable (Function.uncurry X) := by
    have h1 := measurable_apply_radBump δ hδ.le
    have hm1 : Measurable fun p : Ω × ℂ => G p.1 (radBump δ hδ.le p.2) :=
      h1.comp ((hGm.comp measurable_fst).prodMk measurable_snd)
    have hm2 : Measurable fun p : Ω × ℂ => G p.1 (radBump δ hδ.le z) :=
      h1.comp ((hGm.comp measurable_fst).prodMk measurable_const)
    have : Function.uncurry X = fun p : Ω × ℂ => G p.1 (radBump δ hδ.le p.2) -
        G p.1 (radBump δ hδ.le z) := by funext p; exact hXy p.1 p.2
    rw [this]; exact hm1.sub hm2
  have hXc : ∀ ω, Continuous (X ω) := fun ω => by
    have : X ω = fun y => G ω (radBump δ hδ.le y) - G ω (radBump δ hδ.le z) := funext (hXy ω)
    rw [this]
    exact ((map_continuous (G ω)).comp (continuous_radBump δ hδ.le)).sub continuous_const
  set Φ : Ω → ℝ≥0∞ := fun ω => ∫⁻ y in closedBall z ρ, ENNReal.ofReal |X ω y|
  -- the event is contained in a Markov event
  have hsub : oscEv G z R ρ₂ A ⊆ {ω | ENNReal.ofReal (A / oscC δ) ≤ Φ ω} := by
    rintro ω ⟨g, hg, hrep, u, hu, hlt⟩
    have hgc : ∀ y ∈ closedBall z ρ, closedBall y δ ⊆ ball z R := fun y hy w hw => by
      rw [mem_closedBall] at hy hw; rw [mem_ball]
      linarith [dist_triangle w y z]
    have hval : ∀ y ∈ closedBall z ρ, |g y - g z| = |X ω y| / I := by
      intro y hy
      have e1 := pair_radBump_of_harmonic (V := ballO z R) hg hrep hδ (hgc y hy)
      have e2 := pair_radBump_of_harmonic (V := ballO z R) hg hrep hδ
        (hgc z (mem_closedBall_self hρ))
      rw [hXy, e1, e2, ← sub_mul, abs_mul, abs_of_pos hI, mul_div_cancel_right₀ _ hI.ne']
    have hint : IntegrableOn (fun y => |X ω y|) (closedBall z ρ) :=
      (hXc ω).abs.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
    have hub : closedBall u δ ⊆ closedBall z ρ := fun w hw => by
      rw [mem_closedBall] at hw ⊢; rw [mem_ball] at hu
      linarith [dist_triangle w u z]
    have hstep := abs_sub_le_integral_of_harmonic isOpen_ball hg hδ
      (hub.trans (closedBall_subset_ball (by linarith))) (g z)
    have hmono : ∫ y in closedBall u δ, |g y - g z| ≤ ∫ y in closedBall z ρ, |X ω y| / I := by
      calc ∫ y in closedBall u δ, |g y - g z| = ∫ y in closedBall u δ, |X ω y| / I :=
            setIntegral_congr_fun measurableSet_closedBall fun y hy => hval y (hub hy)
        _ ≤ _ := setIntegral_mono_set (hint.div_const I)
            (Eventually.of_forall fun y => div_nonneg (abs_nonneg _) hI.le)
            (Eventually.of_forall hub)
    rw [integral_div] at hmono
    have hmain : A < oscC δ * ∫ y in closedBall z ρ, |X ω y| := by
      calc A < |g u - g z| := hlt
        _ ≤ expNegInvGlue (δ ^ 2) / I * ((∫ y in closedBall z ρ, |X ω y|) / I) :=
            hstep.trans (mul_le_mul_of_nonneg_left hmono (by
              have := expNegInvGlue.nonneg (δ ^ 2); positivity))
        _ = _ := by unfold oscC; ring
    show ENNReal.ofReal (A / oscC δ) ≤ ∫⁻ y in closedBall z ρ, ENNReal.ofReal |X ω y|
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun y => abs_nonneg _)]
    exact ENNReal.ofReal_le_ofReal ((div_lt_iff₀' hc).2 hmain).le
  -- Markov and Tonelli
  have hΦm : Measurable Φ := (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp hXm)).lintegral_prod_right'
  have hne : ENNReal.ofReal (A / oscC δ) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  refine (measure_mono hsub).trans ((meas_ge_le_lintegral_div hΦm.aemeasurable hne
    ENNReal.ofReal_ne_top).trans ?_)
  refine ENNReal.div_le_div_right ?_ _
  have hjm : Measurable (Function.uncurry fun ω y => ENNReal.ofReal |X ω y|) :=
    ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp hXm)
  show ∫⁻ ω, (∫⁻ y in closedBall z ρ, ENNReal.ofReal |X ω y|) ∂P ≤ _
  rw [lintegral_lintegral_swap hjm.aemeasurable]
  calc ∫⁻ y in closedBall z ρ, ∫⁻ ω, ENNReal.ofReal |X ω y| ∂P
      ≤ ∫⁻ _y in closedBall z ρ, ENNReal.ofReal (√(radK δ ρ)) := by
        refine setLIntegral_mono measurable_const fun y hy => ?_
        have hyz : ‖y - z‖ ≤ ρ := by rw [← dist_eq_norm]; exact mem_closedBall.1 hy
        obtain ⟨hL, hK⟩ := integral_sq_radDiff_le hh hzb hind hdec hδ hρ hyz
          (closedBall_subset_closedBall le_rfl |>.trans
            ((closedBall_subset_ball hρR).trans hBV))
        have hpq : (2 : ℝ).HolderConjugate 2 := Real.HolderConjugate.two_two
        have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq P hpq
          (f := fun ω => ENNReal.ofReal |X ω y|) (g := fun _ => 1)
          (ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
            (hXm.comp (measurable_id.prodMk measurable_const)))).aemeasurable aemeasurable_const
        simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, measure_univ] at hcs
        refine hcs.trans ?_
        have hsq : ∫⁻ ω, ENNReal.ofReal |X ω y| ^ (2 : ℝ) ∂P = ENNReal.ofReal (∫ ω, X ω y ^ 2 ∂P) := by
          rw [ofReal_integral_eq_lintegral_ofReal hL.integrable_sq
            (Eventually.of_forall fun ω => sq_nonneg _)]
          congr 1; funext ω
          rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
          congr 1; rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
        have h0 : 0 ≤ ∫ ω, X ω y ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg _
        rw [hsq, ENNReal.ofReal_rpow_of_nonneg h0 (by norm_num), Real.sqrt_eq_rpow]
        exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow h0 hK (by norm_num))
    _ = _ := by rw [setLIntegral_const, mul_comm]

end LQGMetric.GM
