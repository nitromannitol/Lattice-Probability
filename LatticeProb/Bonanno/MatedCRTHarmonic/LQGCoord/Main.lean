/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.LQGCoord.Main at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.LQGCoord.ConeRadial

/-!
# The simultaneous coordinate change of the whole-plane LQG area of the quantum cone

For the circle-average embedding
`h = coneField X (coneRadial γ α B B')` of the α-quantum cone (DMS Def. 4.10 and
Rem. 4.4; `CellScaling.coneField`), built from a whole-plane GFF `X` and Brownian motions `B, B'`, with
`0 < γ < 2` and `α < Q`, **almost surely, simultaneously for all `r > 0`, `c ∈ ℝ`, `z ∈ ℂ` and every
set `A ⊆ ℂ`**,

  `lqgArea γ (h(r · + z) + Q log r + c) A = e^{γc} · lqgArea γ h (r A + z)`

(`ae_lqgArea_affine_coneField_holds`; the γ-cone of the cell model is `α = γ`,
`ae_lqgArea_affine_coneFieldOf_holds`). In particular, for the random dilation `R_b` of
the cone scaling identity (any `R > 0`, chosen after `ω`), `μ_{h_b}(A) = b⁻¹ μ_h(R_b A)`
(`ae_lqgArea_coneRescaleField_holds`; [17] gives the inverse form).

Literature: Sheffield–Wang arXiv:1605.06171 Thm 1.1 (a.s. convergence along all ε → 0) and Thm 1.4
(coordinate change for all conformal maps simultaneously); Duplantier–Sheffield arXiv:0808.1560
Prop. 2.1 (fixed maps). No independence between `X`, `B`, `B'` is needed. SLE-free.

Structure of the proof (files `LQGCoord/*`):
* `ScaleBump`, `ScaleCont`, `ScaleKolm`: a.s. the circle averages of `X` are limits of the mollified
  circle averages along **every** mollifier scale (four-parameter Kolmogorov–Čentsov);
* `Transform`: the deterministic coordinate change given that and continuum area limits;
* `WPCirc`–`WPArea`: continuum area limits for the whole-plane GFF (QuantumZipper's grid-plus-
  modulus argument, ported to `ℂ`);
* `ConeOfFun`, `ConeArea`, `ConeTight`, `ConeRadial`: the cone field = GFF + functions continuous
  off `0` with an α-log singularity; tightness at the cone point from fractional moments.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric Real
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.LQGCoord

open LQGMetric MatedCRTHarmonic.CellScaling

/-- the growth exponent used for the α-cone: `max(0, (α + Q)/2) < Q` -/
def coneExp (γ α : ℝ) : ℝ := max 0 ((α + lqgQ γ) / 2)

lemma lqgQ_pos {γ : ℝ} (hγ : 0 < γ) : 0 < lqgQ γ := by unfold lqgQ; positivity

lemma coneExp_lt {γ α : ℝ} (hγ : 0 < γ) (hαQ : α < lqgQ γ) : coneExp γ α < lqgQ γ :=
  max_lt (lqgQ_pos hγ) (by linarith)

/-- **the deterministic hypotheses hold for the cone field** on the good event -/
theorem coneGood_of {γ α : ℝ} (hαQ : α < lqgQ γ) {X : DistC} {b b' : ℝ≥0 → ℝ}
    {μX : Measure ℂ} (hr : RadialGood γ α X b b') (hs : HasScaleCircleAvgs X)
    (ha : HasAreaLimitS γ X μX)
    (ht : ∀ ε : ℝ, 0 < ε → ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ s : ℝ, 0 < s → s ≤ r₀ →
      ∫⁻ w in ball 0 r₀, ENNReal.ofReal (max ‖w‖ s ^ (-(γ * coneExp γ α))) ∂areaS γ X s ≤
        ENNReal.ofReal ε) :
    ConeGood γ X (radialAvg X) (coneProfile γ α b b') μX (coneExp γ α) := by
  have hm₂ := measurable_coneProfile hr
  have hc₁ := continuousOn_radialAvg hr.good
  have hc₂ := continuousOn_coneProfile hr
  obtain ⟨C₁, hC₁⟩ := abs_radialAvg_le hr one_pos
  obtain ⟨C₂, hC₂⟩ := abs_coneProfile_le hr one_pos
  refine
    { good := hr.good
      scale := hs
      area := ha
      meas₁ := measurable_radialAvg X
      meas₂ := hm₂
      li₁ := locallyIntegrable_of_logBound (measurable_radialAvg X) hc₁ hC₁
      li₂ := locallyIntegrable_of_logBound hm₂ hc₂ fun w h0 h1 => (hC₂ w h0 h1).1
      cont₁ := hc₁
      cont₂ := hc₂
      c_nonneg := le_max_left _ _
      growth := ?_
      tight := ht }
  set η := (lqgQ γ - α) / 4 with hη
  have hη0 : 0 < η := by rw [hη]; linarith
  obtain ⟨D₁, hD₁⟩ := abs_radialAvg_le hr hη0
  obtain ⟨D₂, hD₂⟩ := abs_coneProfile_le hr hη0
  refine ⟨D₁ + D₂, 1, one_pos, fun w h0 h1 => ?_⟩
  have ht0 := neg_log_pos h0 h1
  have a1 := hD₁ w h0 h1
  have a2 := (hD₂ w h0 h1).2
  have a3 := neg_abs_le (radialAvg X w)
  have hexp : α + η + η ≤ coneExp γ α := by
    refine le_trans (le_of_eq ?_) (le_max_right _ _); rw [hη]; ring
  have : (α + η + η) * -Real.log ‖w‖ ≤ coneExp γ α * -Real.log ‖w‖ :=
    mul_le_mul_of_nonneg_right hexp ht0.le
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Coordinate covariance for the α-quantum cone** (all `r > 0`, `c`, `z`, `A` on one almost-sure event). -/
theorem ae_lqgArea_affine_coneField_holds {X : Ω → DistC} {B B' : ℝ≥0 → Ω → ℝ} {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ) (hX : IsWholePlaneGFF X P)
    (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P) :
    ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r → ∀ (c : ℝ) (z : ℂ) (A : Set ℂ),
      lqgArea γ (addConst (affineComp r z
          (coneField (X ω) (coneRadial γ α (fun t => B t ω) (fun t => B' t ω))))
          (lqgQ γ * Real.log r + c)) A =
        ENNReal.ofReal (Real.exp (γ * c)) *
          lqgArea γ (coneField (X ω) (coneRadial γ α (fun t => B t ω) (fun t => B' t ω)))
            ((fun w => (r : ℂ) * w + z) '' A) := by
  filter_upwards [ae_radialGood hX hB hB' hαQ, ae_hasScaleCircleAvgs_wp hX,
    ae_hasAreaLimitS_wp hX hγ hγ2,
    ae_tight_wp hX hγ hγ2 (le_max_left _ _) (coneExp_lt hγ hαQ)] with ω hr hs ha ht
  have hc := coneGood_of hαQ hr hs ha ht
  intro r hr0 c z A
  rw [coneField_eq_cone]
  exact lqgArea_affine_apply hγ.ne'
    (hasScaleCircleAvgs_cone hs hc.li₁ hc.li₂ hc.cont₁ hc.cont₂) (hasAreaLimitS_cone hγ hc)
    hr0 z c A

/-- **Coordinate covariance, measure form**: `lqgArea γ (h(r · + z) + Q log r + c) = e^{γc} · (w ↦ (w − z)/r)_* μ_h`. -/
theorem ae_lqgArea_affine_coneField_eq_holds {X : Ω → DistC} {B B' : ℝ≥0 → Ω → ℝ} {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hαQ : α < lqgQ γ) (hX : IsWholePlaneGFF X P)
    (hB : IsBrownianReal B P) (hB' : IsBrownianReal B' P) :
    ∀ᵐ ω ∂P, ∀ r : ℝ, ∀ hr : 0 < r, ∀ (c : ℝ) (z : ℂ),
      lqgArea γ (addConst (affineComp r z
          (coneField (X ω) (coneRadial γ α (fun t => B t ω) (fun t => B' t ω))))
          (lqgQ γ * Real.log r + c)) =
        ENNReal.ofReal (Real.exp (γ * c)) •
          (lqgArea γ (coneField (X ω) (coneRadial γ α (fun t => B t ω) (fun t => B' t ω)))).map
            (affT hr z).symm := by
  filter_upwards [ae_radialGood hX hB hB' hαQ, ae_hasScaleCircleAvgs_wp hX,
    ae_hasAreaLimitS_wp hX hγ hγ2,
    ae_tight_wp hX hγ hγ2 (le_max_left _ _) (coneExp_lt hγ hαQ)] with ω hr hs ha ht
  have hc := coneGood_of hαQ hr hs ha ht
  intro r hr0 c z
  rw [coneField_eq_cone, lqgArea_eq_of_hasAreaLimitS (hasAreaLimitS_cone hγ hc)]
  exact lqgArea_affine_eq hγ.ne' (hasScaleCircleAvgs_cone hs hc.li₁ hc.li₂ hc.cont₁ hc.cont₂)
    (hasAreaLimitS_cone hγ hc) hr0 z c

lemma lt_lqgQ {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : γ < lqgQ γ := by
  have := CellScaling.lqgQ_sub_pos hγ hγ2; linarith

/-- **Coordinate covariance for the γ-quantum cone of the cell model** (`CellScaling.coneFieldOf`). -/
theorem ae_lqgArea_affine_coneFieldOf_holds {X : Ω → DistC} {B B' : ℝ≥0 → Ω → ℝ} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hX : IsWholePlaneGFF X P) (hB : IsBrownianReal B P)
    (hB' : IsBrownianReal B' P) :
    ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r → ∀ (c : ℝ) (z : ℂ) (A : Set ℂ),
      lqgArea γ (addConst (affineComp r z
          (coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω)))
          (lqgQ γ * Real.log r + c)) A =
        ENNReal.ofReal (Real.exp (γ * c)) *
          lqgArea γ (coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω))
            ((fun w => (r : ℂ) * w + z) '' A) :=
  ae_lqgArea_affine_coneField_holds hγ hγ2 (lt_lqgQ hγ hγ2) hX hB hB'

/-- **The area at the random scale** (the cone scaling identity, area part): almost surely,
for every `R > 0` (in particular `R = R_b(ω)`), every `b > 0` and every set `A`,
`μ_{h_b}(A) = b⁻¹ μ_h(R A)` where `h_b = h(R ·) + Q log R − γ⁻¹ log b`
(`CellScaling.coneRescaleField`). -/
theorem ae_lqgArea_coneRescaleField_holds {X : Ω → DistC} {B B' : ℝ≥0 → Ω → ℝ} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hX : IsWholePlaneGFF X P) (hB : IsBrownianReal B P)
    (hB' : IsBrownianReal B' P) :
    ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R → ∀ b₀ : ℝ, 0 < b₀ → ∀ A : Set ℂ,
      lqgArea γ (coneRescaleField γ R b₀
          (coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω))) A =
        ENNReal.ofReal b₀⁻¹ *
          lqgArea γ (coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω))
            ((fun w => (R : ℂ) * w) '' A) := by
  filter_upwards [ae_lqgArea_affine_coneFieldOf_holds hγ hγ2 hX hB hB'] with ω h R hR b₀ hb₀ A
  have e1 : coneRescaleField γ R b₀ (coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω)) =
      addConst (affineComp R 0 (coneFieldOf γ (X ω) (fun t => B t ω) (fun t => B' t ω)))
        (lqgQ γ * Real.log R + -(γ⁻¹ * Real.log b₀)) := by
    rw [coneRescaleField, sub_eq_add_neg]
  have e2 : Real.exp (γ * -(γ⁻¹ * Real.log b₀)) = b₀⁻¹ := by
    rw [show γ * -(γ⁻¹ * Real.log b₀) = -Real.log b₀ by field_simp, Real.exp_neg,
      Real.exp_log hb₀]
  rw [e1, h R hR _ 0 A, e2]
  congr 2
  ext w
  simp

end MatedCRTHarmonic.LQGCoord
