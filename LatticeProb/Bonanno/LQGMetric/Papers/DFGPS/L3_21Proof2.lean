/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L3_21Proof2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_21Proof

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 3.21, steps 2–3: negative moments and the factorization with exponent `−p`

DFGPS arXiv:1905.00380, `lqg-metric-estimates-final.tex` ("T"), proof of Lemma 3.21,
T:2349–2352: "Proposition 3.1 implies that `𝔠_{ε𝕣}⁻¹ e^{−ξ h_{ε𝕣}(z)} D_h(B_{ε𝕣}(z), ∂B_{2ε𝕣}(z))`
has finite moments of all negative orders which are bounded above uniformly over all `z ∈ ℂ` and
`𝕣 > 0`. By the same calculation as in (3.31), …"

* `cross_neg_moment`: the negative moments, from the lower bound of Prop 3.1 (at the centre `z`,
  `prop3_1_centre`) with `K₁ = B̄_{1/3}(0)`, `K₂ = ∂B_{2/3}(0)`, `U = B_1(0)` at scale `3ρ`, and the
  tail-to-moment lemma `lintegral_rpow_neg_le_of_tail` (as in `prop3_9_nonpos`, T:1766).
  We normalize at the scale `3ρ` of the open set `B_{3ρ}(z)` in which the distance is local
  (`L321.setDist_eq_setDistIn`), instead of `ε𝕣` in the paper; the scale enters only through
  Theorem 1.5 (`DFGPSScaling`, applied with `3ε`).
* `moment_of_local_inv`: (3.31) with exponent `−p` (the "same calculation", T:2352–2355).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped ENNReal

namespace LQGMetric.DFGPS
open Blueprint

namespace L321

variable {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}

lemma ball_subset_scale {ρ : ℝ} (hρ : 0 < ρ) (z : ℂ) :
    ball z ρ ⊆ scaleSet (3 * ρ) z (closedBall 0 (1 / 3)) := by
  intro w hw
  rw [mem_scaleSet_iff (by positivity) z w, mem_closedBall, dist_zero_right, norm_div,
    Complex.norm_real, Real.norm_of_nonneg (by positivity), div_le_iff₀ (by positivity)]
  have := mem_ball_iff_norm.1 hw
  linarith

lemma sphere_subset_scale {ρ : ℝ} (hρ : 0 < ρ) (z : ℂ) :
    sphere z (2 * ρ) ⊆ scaleSet (3 * ρ) z (sphere 0 (2 / 3)) := by
  intro w hw
  rw [mem_scaleSet_iff (by positivity) z w, mem_sphere_zero_iff_norm, norm_div,
    Complex.norm_real, Real.norm_of_nonneg (by positivity), mem_sphere_iff_norm.1 hw]
  field_simp

lemma setDistIn_anti {d : ContMetric} {A A' B B' V : Set ℂ} (hA : A ⊆ A') (hB : B ⊆ B') :
    setDistIn d A' B' V ≤ setDistIn d A B V := by
  unfold setDistIn
  exact iInf₂_mono' fun x hx => ⟨x, hA hx, iInf₂_mono' fun y hy => ⟨y, hB hy, le_rfl⟩⟩

lemma not_subsingleton_sphere : ¬ (sphere (0 : ℂ) (2 / 3)).Subsingleton := by
  intro hs
  have h1 : ((2 / 3 : ℝ) : ℂ) ∈ sphere (0 : ℂ) (2 / 3) := by
    rw [mem_sphere_zero_iff_norm, Complex.norm_real, Real.norm_of_nonneg (by norm_num)]
  have h2 : (-((2 / 3 : ℝ) : ℂ)) ∈ sphere (0 : ℂ) (2 / 3) := by
    rw [mem_sphere_zero_iff_norm, norm_neg, Complex.norm_real, Real.norm_of_nonneg (by norm_num)]
  have := congrArg Complex.re (hs h1 h2)
  simp at this
  linarith

/-- **T:2349–2351**: uniform negative moments of
`𝔠_{3ρ}⁻¹ e^{−ξ h_{3ρ}(z)} D_h(B_ρ(z), ∂B_{2ρ}(z); B_{3ρ}(z))` (Prop 3.1, lower bound). -/
theorem cross_neg_moment (h31 : Prop3_1) (hγ0 : 0 < γ) (hγ2 : γ < 2)
    (hD : IsWeakLQGMetric γ D c) {p : ℝ} (hp : 0 < p) :
    ∃ Cp : ℝ, ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsNormalizedWPGFF h P → ∀ ρ : ℝ, 0 < ρ → ∀ z : ℂ,
        ∫⁻ ω, ((ENNReal.ofReal (scaleFac (xiGamma γ) c (h ω) (3 * ρ) z)⁻¹ *
          setDistIn (D (h ω)) (ball z ρ) (sphere z (2 * ρ)) (ball z (3 * ρ)))⁻¹) ^ p ∂P ≤
            ENNReal.ofReal Cp := by
  obtain ⟨μ, hμP, hμ⟩ := exists_canonical_normGFF
  have hrank : 1 < Module.rank ℝ ℂ := by rw [Complex.rank_real_complex]; norm_num
  have hdisj : Disjoint (closedBall (0 : ℂ) (1 / 3)) (sphere 0 (2 / 3)) := by
    refine Set.disjoint_left.2 fun x h1 h2 => ?_
    rw [mem_closedBall, dist_zero_right] at h1
    rw [mem_sphere_zero_iff_norm] at h2
    linarith
  obtain ⟨C, A₀, hC⟩ := prop3_1_centre h31 hγ0 hγ2 hD (U := ball 0 1)
    (K₁ := closedBall 0 (1 / 3)) (K₂ := sphere 0 (2 / 3)) isOpen_ball
    ((convex_ball 0 1).isConnected (nonempty_ball.2 one_pos)) (isCompact_closedBall _ _)
    (isCompact_sphere _ _) ((convex_closedBall _ _).isConnected
      (nonempty_closedBall.2 (by norm_num))) (isConnected_sphere hrank 0 (by norm_num))
    (closedBall_subset_ball (by norm_num))
    (sphere_subset_closedBall.trans (closedBall_subset_ball (by norm_num))) hdisj
    (not_subsingleton_closedBall 0 (by norm_num)) not_subsingleton_sphere hμ (p + 1)
    (by linarith)
  set t₀ := max 1 (A₀ + 1)
  refine ⟨momBd p (p + 1) (max C 0) t₀, fun P _ h hh ρ hρ z => ?_⟩
  have hX : ∀ x : ℝ≥0∞, x⁻¹ ^ p = x ^ (-p) := fun x => by
    rw [ENNReal.inv_rpow, ENNReal.rpow_neg]
  simp_rw [hX]
  have h3ρ : 0 < 3 * ρ := by positivity
  refine (lintegral_rpow_neg_le_of_tail P _ (a := p + 1) (C := max C 0) (t₀ := t₀) (by linarith)
    (by rw [neg_neg]; linarith) (le_max_right _ _)
    (le_max_left _ _) fun t ht => ?_).trans (by rw [neg_neg])
  have hA : A₀ < t := by have := le_max_right 1 (A₀ + 1); linarith
  have ht0 : 0 < t := by have := le_max_left 1 (A₀ + 1); linarith
  refine le_trans ?_ ((hC t hA (3 * ρ) h3ρ z).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg ht0.le _))))
  refine le_trans (measure_mono fun ω hω => ?_) (prob_le_canonical hμ P h hh _)
  simp only [mem_ofPred_eq, mem_compl_iff] at hω ⊢
  set s := scaleFac (xiGamma γ) c (h ω) (3 * ρ) z
  have hs : 0 < s := mul_pos (hD.tightness.1 _ h3ρ) (Real.exp_pos _)
  rintro ⟨hcon, -⟩
  have hmono : setDistIn (D (h ω)) (scaleSet (3 * ρ) z (closedBall 0 (1 / 3)))
      (scaleSet (3 * ρ) z (sphere 0 (2 / 3))) (scaleSet (3 * ρ) z (ball 0 1)) ≤
      setDistIn (D (h ω)) (ball z ρ) (sphere z (2 * ρ)) (ball z (3 * ρ)) := by
    rw [L319.scaleSet_ball _ h3ρ z]
    exact setDistIn_anti (ball_subset_scale hρ z) (sphere_subset_scale hρ z)
  refine absurd hω (not_lt.2 ?_)
  calc ENNReal.ofReal t⁻¹ = ENNReal.ofReal s⁻¹ * ENNReal.ofReal (t⁻¹ * s) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1; field_simp
    _ ≤ _ := mul_le_mul_right (hcon.trans hmono) _

/-- **(3.31) with exponent `−p`** (T:2352–2355): with `Y` independent of
`X = h_ρ(z) − h_r(z)` and `Y = e^{−ξ h_ρ(z)} Dm` a.s.,
`E[(𝔠_r⁻¹ e^{−ξ h_r(z)} Dm)^{−p}] ≤ (𝔠_r/𝔠_ρ)^p e^{ξ²p² log(r/ρ)/2} E[(𝔠_ρ⁻¹ e^{−ξ h_ρ(z)} Dm)^{−p}]`. -/
theorem moment_of_local_inv (hD : IsWeakLQGMetric γ D c) {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC} (hh : IsWholePlaneGFF h P) (z : ℂ)
    {ρ r : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ r) (Dm : Ω → ℝ≥0∞) {Y : Ω → ℝ≥0∞} (hYm : Measurable Y)
    (hI : IndepFun (fun ω => circleAvg (h ω) ρ z - circleAvg (h ω) r z) Y P)
    (hYae : ∀ᵐ ω ∂P, Y ω = ENNReal.ofReal (Real.exp (-(xiGamma γ * circleAvg (h ω) ρ z))) * Dm ω)
    {p C : ℝ} (hp0 : 0 ≤ p)
    (hloc : ∫⁻ ω, ((ENNReal.ofReal (scaleFac (xiGamma γ) c (h ω) ρ z)⁻¹ * Dm ω)⁻¹) ^ p ∂P ≤
      ENNReal.ofReal C) :
    AEMeasurable (fun ω => (ENNReal.ofReal (scaleFac (xiGamma γ) c (h ω) r z)⁻¹ * Dm ω)⁻¹) P ∧
    ∫⁻ ω, ((ENNReal.ofReal (scaleFac (xiGamma γ) c (h ω) r z)⁻¹ * Dm ω)⁻¹) ^ p ∂P ≤
      ENNReal.ofReal ((c r / c ρ) ^ p *
        Real.exp ((Real.log r - Real.log ρ) * (p * xiGamma γ) ^ 2 / 2) * C) := by
  have hr : 0 < r := hρ.trans_le hρr
  set ξ := xiGamma γ with hξ_def
  set Y' : Ω → ℝ≥0∞ := fun ω => (ENNReal.ofReal (c ρ)⁻¹ * Y ω)⁻¹ with hY'_def
  have hψ : Measurable fun y : ℝ≥0∞ => (ENNReal.ofReal (c ρ)⁻¹ * y)⁻¹ :=
    (measurable_const.mul measurable_id).inv
  have hY'm : Measurable Y' := hψ.comp hYm
  have hI' : IndepFun (fun ω => circleAvg (h ω) ρ z - circleAvg (h ω) r z) Y' P :=
    hI.comp (φ := id) measurable_id hψ
  have hfac := L319.lintegral_factor hh z hρ hρr hY'm hI' (-ξ) p hp0
  have hsq : (p * -ξ) ^ 2 = (p * ξ) ^ 2 := by ring
  rw [hsq] at hfac
  have hcρ : 0 < c ρ := hD.tightness.1 ρ hρ
  have hcr : 0 < c r := hD.tightness.1 r hr
  set X : Ω → ℝ := fun ω => circleAvg (h ω) ρ z - circleAvg (h ω) r z with hX_def
  have hXm : Measurable X := CircleAvg.measurable_cInc hh ρ z r z
  have hae : ∀ᵐ ω ∂P, (ENNReal.ofReal (scaleFac ξ c (h ω) r z)⁻¹ * Dm ω)⁻¹ =
      ENNReal.ofReal (c r / c ρ) * (ENNReal.ofReal (Real.exp (-ξ * X ω)) * Y' ω) := by
    filter_upwards [hYae] with ω hω
    have key : ENNReal.ofReal (scaleFac ξ c (h ω) r z)⁻¹ * Dm ω =
        ENNReal.ofReal (c ρ / c r) * (ENNReal.ofReal (Real.exp (ξ * X ω)) *
          (ENNReal.ofReal (c ρ)⁻¹ * Y ω)) := by
      rw [hω, ← mul_assoc, ← mul_assoc, ← mul_assoc,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      rw [scaleFac, hX_def]
      simp only
      rw [mul_sub, Real.exp_sub, Real.exp_neg]
      field_simp
    rw [key, hY'_def]
    simp only
    rw [ENNReal.mul_inv (Or.inl (ENNReal.ofReal_pos.2 (by positivity)).ne')
        (Or.inl ENNReal.ofReal_ne_top),
      ENNReal.mul_inv (Or.inl (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne')
        (Or.inl ENNReal.ofReal_ne_top),
      ← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_inv_of_pos (Real.exp_pos _),
      inv_div, ← Real.exp_neg, neg_mul]
  have hae2 : ∀ᵐ ω ∂P, Y' ω = (ENNReal.ofReal (scaleFac ξ c (h ω) ρ z)⁻¹ * Dm ω)⁻¹ := by
    filter_upwards [hYae] with ω hω
    rw [hY'_def]
    simp only
    congr 1
    rw [hω, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
    congr 2
    rw [scaleFac, Real.exp_neg, mul_inv]
  have hmeasW : Measurable fun ω => ENNReal.ofReal (c r / c ρ) *
      (ENNReal.ofReal (Real.exp (-ξ * X ω)) * Y' ω) :=
    measurable_const.mul ((ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul hXm))).mul hY'm)
  refine ⟨hmeasW.aemeasurable.congr (hae.mono fun ω hω => hω.symm), ?_⟩
  rw [lintegral_congr_ae (hae.mono fun ω hω => by rw [hω])]
  set W : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Real.exp (-ξ * X ω)) * Y' ω with hW_def
  have hWm : Measurable W := (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul hXm))).mul hY'm
  rw [show (fun ω => (ENNReal.ofReal (c r / c ρ) * W ω) ^ p) =
      fun ω => ENNReal.ofReal (c r / c ρ) ^ p * W ω ^ p from
    funext fun ω => ENNReal.mul_rpow_of_nonneg _ _ hp0, lintegral_const_mul _ (hWm.pow_const p)]
  rw [hfac, lintegral_congr_ae (hae2.mono fun ω hω => by rw [hω])]
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0, ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_mul (by positivity), mul_assoc]
  gcongr

end L321
end LQGMetric.DFGPS
