import Mathlib
import LatticeProb.Gauss.GFFAffineInvariance
import LatticeProb.LQG.LQGMeasureNonatomicMassAffine
import LatticeProb.LQG.LQGMeasureNonatomicMassMixture
import LatticeProb.LQG.LQGMeasureNonatomicMassTail
import LatticeProb.LQG.LQGMeasureNonatomicMassPoly
import LatticeProb.LQG.LQGMeasureNonatomicMassScaled
import LatticeProb.LQG.LQGMeasureInputs

/-!
# Ding-Gwynne Lemma 3.8 for the rescaled fields, uniformly in the scale

Adapted from the Lean formalization accompanying [Harmonic balls in Liouville quantum gravity, arXiv:2208.11795],
Lemma 2.4. The uniform rescaled ball-mass step is proved from the literature input `WholePlaneLQGBallMassBoundsLP`
(Ding-Gwynne 2020, Lemma 3.8; module `LatticeProb.LQG.LQGMeasureInputs`, used as a hypothesis), the affine invariance
`wholePlaneGFFAffineInvariance_lp`, the coordinate change `LQGMeasureCoordChangeLP` at `α₀ = 0` (hypothesis), and the proved
mixture `wholePlaneGFFMixtureStep_lp`.

Argument: (1) for `τ = 2^{-k}`, `h^{(k)} = h^ℂ(τ ·) - h^ℂ_τ(0)` is a whole-plane GFF with LQG measure
`e^{-γ(h^ℂ_τ(0) + Q log τ)} μ₀(τ ·)`; (2) the mixture over `k` with weights `∝ (k+1)⁻²` is a whole-plane GFF; (3) its image
under `x ↦ 2R x - R(1+i)`, which maps the unit square onto `[-R, R]² ⊇ closedBall 0 R`, satisfies Ding-Gwynne Lemma 3.8 on
`closedBall 0 R`; (4) a slice `k` costs `ν{k}⁻¹ = S (k+1)²`.

This file contains the Gaussian tail, the square map and the preimage of the closed ball.
-/

namespace LatticeProb.LQG.LQGMeasureNonatomicMass

open MeasureTheory ProbabilityTheory Metric Filter Set Topology LatticeProb.Gauss LatticeProb.LQG
open scoped ENNReal
open LatticeProb.LQG.ProfileDerived (dyadicScale_pos)
open LatticeProb.LQG.AffineDerived (wholePlaneGFFAffineInvariance_lp)

universe u

/-- Gaussian tail: for a centred Gaussian `X` with `Var X ≤ V`, `P[|X| ≥ L] ≤ 2 exp(-L²/(2V))`. -/
theorem measure_le_abs_le_of_hasGaussianLaw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    (hG : HasGaussianLaw X P) (hmean : ∫ ω, X ω ∂P = 0) {V : ℝ} (hV : Var[X; P] ≤ V) (hV0 : 0 < V)
    {L : ℝ} (hL : 0 ≤ L) : P {ω | L ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-(L ^ 2) / (2 * V))) := by
  have hP := hG.isProbabilityMeasure
  set v : NNReal := (Var[X; P]).toNNReal with hv_def
  have hv : (v : ℝ) = Var[X; P] := Real.coe_toNNReal _ (variance_nonneg X P)
  have hlaw : HasLaw X (gaussianReal 0 v) P := ⟨hG.aemeasurable, by rw [hG.map_eq_gaussianReal, hmean]⟩
  have hint : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) P := by
    intro t
    have h := integrable_exp_mul_gaussianReal (μ := 0) (v := v) t
    rw [← hlaw.map_eq] at h
    exact (integrable_map_measure (by fun_prop) hG.aemeasurable).1 h
  have hvV : (v : ℝ) ≤ V := by rw [hv]; exact hV
  set s : ℝ := L / V with hs
  have hs0 : 0 ≤ s := by positivity
  have hbound : Real.exp (-s * L) * Real.exp (0 * s + v * s ^ 2 / 2) ≤ Real.exp (-(L ^ 2) / (2 * V)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    calc -s * L + (0 * s + v * s ^ 2 / 2) ≤ -s * L + V * s ^ 2 / 2 := by nlinarith [sq_nonneg s]
      _ = -(L ^ 2) / (2 * V) := by rw [hs]; field_simp; ring
  have hup : P.real {ω | L ≤ X ω} ≤ Real.exp (-(L ^ 2) / (2 * V)) := by
    refine (measure_ge_le_exp_mul_mgf L hs0 (hint s)).trans ?_
    rw [mgf_gaussianReal hlaw]; exact hbound
  have hlow : P.real {ω | X ω ≤ -L} ≤ Real.exp (-(L ^ 2) / (2 * V)) := by
    refine (measure_le_le_exp_mul_mgf (-L) (neg_nonpos.2 hs0) (hint (-s))).trans ?_
    rw [mgf_gaussianReal hlaw]
    convert hbound using 3 <;> ring
  have hsub : {ω | L ≤ |X ω|} ⊆ {ω | L ≤ X ω} ∪ {ω | X ω ≤ -L} := by
    intro ω hω
    rcases le_abs'.1 (show L ≤ |X ω| from hω) with h | h
    · exact Or.inr h
    · exact Or.inl h
  calc P {ω | L ≤ |X ω|} ≤ P {ω | L ≤ X ω} + P {ω | X ω ≤ -L} :=
        (measure_mono hsub).trans (measure_union_le _ _)
    _ = ENNReal.ofReal (P.real {ω | L ≤ X ω}) + ENNReal.ofReal (P.real {ω | X ω ≤ -L}) := by
        rw [ofReal_measureReal, ofReal_measureReal]
    _ ≤ ENNReal.ofReal (Real.exp (-(L ^ 2) / (2 * V))) + ENNReal.ofReal (Real.exp (-(L ^ 2) / (2 * V))) :=
        add_le_add (ENNReal.ofReal_le_ofReal hup) (ENNReal.ofReal_le_ofReal hlow)
    _ = ENNReal.ofReal (2 * Real.exp (-(L ^ 2) / (2 * V))) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

/-- The affine map `x ↦ 2R x - R(1+i)` of the unit square onto `[-R, R]²`: its linear part. -/
noncomputable def squareA (R : ℝ) : ℂ := ((2 * R : ℝ) : ℂ)

/-- The affine map `x ↦ 2R x - R(1+i)`: its translation part. -/
noncomputable def squareB (R : ℝ) : ℂ := -((R : ℂ) + (R : ℂ) * Complex.I)

theorem norm_squareA {R : ℝ} (hR : 0 < R) : ‖squareA R‖ = 2 * R := by
  rw [squareA, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

theorem squareA_ne_zero {R : ℝ} (hR : 0 < R) : squareA R ≠ 0 := by
  rw [← norm_pos_iff, norm_squareA hR]; positivity

/-- Every point of `closedBall 0 R` is the image of a point of the unit square under `squareA R · + squareB R`. -/
theorem exists_square_preimage {R : ℝ} (hR : 0 < R) {w : ℂ} (hw : w ∈ closedBall (0 : ℂ) R) :
    ∃ z ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1, squareA R * z + squareB R = w := by
  rw [mem_closedBall_zero_iff] at hw
  have hre := (abs_le.1 ((Complex.abs_re_le_norm w).trans hw))
  have him := (abs_le.1 ((Complex.abs_im_le_norm w).trans hw))
  refine ⟨⟨(w.re + R) / (2 * R), (w.im + R) / (2 * R)⟩, ?_, ?_⟩
  · rw [Complex.mem_reProdIm]
    refine ⟨⟨div_nonneg (by linarith) (by positivity), ?_⟩, ⟨div_nonneg (by linarith) (by positivity), ?_⟩⟩
    · show (w.re + R) / (2 * R) ≤ 1
      rw [div_le_one (by positivity)]; linarith
    · show (w.im + R) / (2 * R) ≤ 1
      rw [div_le_one (by positivity)]; linarith
  · apply Complex.ext
    · simp [squareA, squareB]
      field_simp
      ring
    · simp [squareA, squareB]
      field_simp
      ring


/-- Ding-Gwynne Lemma 3.8 on `closedBall 0 R`, from the bound on the unit square for the affine image of the field. The additive constant `h_{2R}(-R(1+i))` is centred
Gaussian, so `e^{γ h_{2R}(-R(1+i))} ∈ [r^{γc₀}, r^{-γc₀}]` with polynomially high probability; the slack `β⁺ < β⁺'`,
`β⁻' < β⁻` absorbs it and the constants. -/
theorem polyHighProb_closedBall_of_square {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {γ R βp βm βp' βm' : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hR : 0 < R)
    (hpp : βp < βp') (hmm : βm' < βm) (hβp' : 0 < βp') (hβm' : 0 < βm')
    (hDG : PolyHighProb P fun ε => {ω | (∀ z ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1,
          ENNReal.ofReal ε ≤ affineMeasure γ hcirc μ (squareA R) (squareB R) ω (ball z (ε ^ (1 / βm')))) ∧
        ∀ z ∈ Icc (0 : ℝ) 1 ×ℂ Icc (0 : ℝ) 1,
          affineMeasure γ hcirc μ (squareA R) (squareB R) ω (ball z (ε ^ (1 / βp'))) ≤ ENNReal.ofReal ε}) :
    PolyHighProb P fun r => {ω | ∀ w ∈ closedBall (0 : ℂ) R,
      ENNReal.ofReal (r ^ βm) ≤ μ ω (ball w r) ∧ μ ω (ball w r) ≤ ENNReal.ofReal (r ^ βp)} := by
  have hP := hGFF.isProbabilityMeasure
  have ha := squareA_ne_zero hR
  have han := norm_squareA hR
  set Y : Ω → ℝ := fun ω => hcirc ω ‖squareA R‖ (squareB R) with hY_def
  have hapos : 0 < ‖squareA R‖ := by rw [han]; positivity
  have hYG : HasGaussianLaw Y P := hGFF.hasGaussianLaw_circle hapos _
  have hYm : ∫ ω, Y ω ∂P = 0 := hGFF.integral_eq_zero (.circle ‖squareA R‖ (squareB R)) hapos
  set V := Var[Y; P] + 1 with hV
  have hV0 : 0 < V := by have := variance_nonneg Y P; linarith
  set c₀ := min (βm - βm') (βp' - βp) / (2 * γ) with hc₀_def
  have hmin0 : 0 < min (βm - βm') (βp' - βp) := lt_min (by linarith) (by linarith)
  have hc₀ : 0 < c₀ := div_pos hmin0 (by positivity)
  have hγc₀ : γ * c₀ = min (βm - βm') (βp' - βp) / 2 := by rw [hc₀_def]; field_simp
  have hγc₀m : γ * c₀ < βm - βm' := by
    rw [hγc₀]; linarith [min_le_left (βm - βm') (βp' - βp)]
  have hγc₀p : γ * c₀ < βp' - βp := by
    rw [hγc₀]; linarith [min_le_right (βm - βm') (βp' - βp)]
  -- the Gaussian additive constant
  set GY : ℝ → Set Ω := fun r => {ω | |Y ω| < c₀ * Real.log r⁻¹} with hGY_def
  have hGY : PolyHighProb P GY := by
    have hev : ∀ᶠ r in 𝓝[>] (0 : ℝ), P (GY r)ᶜ ≤ ENNReal.ofReal (2 * r ^ (1 : ℝ)) := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < Real.exp (-(2 * V / c₀ ^ 2)) by positivity)]
        with r hr
      obtain ⟨hr0, hrexp⟩ := hr
      set ℓ := Real.log r⁻¹ with hℓ
      have hℓV : 2 * V / c₀ ^ 2 ≤ ℓ := by
        have := Real.log_lt_log hr0 hrexp
        rw [Real.log_exp] at this
        rw [hℓ, Real.log_inv]; linarith
      have hℓ0 : 0 ≤ ℓ := le_trans (by positivity) hℓV
      have hcompl : (GY r)ᶜ = {ω | c₀ * ℓ ≤ |Y ω|} := by
        ext ω; simp only [hGY_def, mem_compl_iff, Set.mem_ofPred_eq, not_lt, hℓ]
      rw [hcompl]
      refine (measure_le_abs_le_of_hasGaussianLaw hYG hYm (by linarith : Var[Y; P] ≤ V) hV0
        (by positivity)).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [Real.rpow_one]
      have h2V : 2 * V ≤ ℓ * c₀ ^ 2 := (div_le_iff₀ (by positivity)).1 hℓV
      have : Real.exp (-((c₀ * ℓ) ^ 2) / (2 * V)) ≤ r := by
        calc Real.exp (-((c₀ * ℓ) ^ 2) / (2 * V)) ≤ Real.exp (-ℓ) := by
              apply Real.exp_le_exp.2
              rw [neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]
              nlinarith [mul_nonneg hℓ0 (sub_nonneg.2 h2V)]
          _ = r := by rw [hℓ, Real.log_inv, neg_neg, Real.exp_log hr0]
      linarith
    obtain ⟨r₁, hr₁, h'⟩ := exists_pos_of_eventually_nhdsGT hev
    exact ⟨1, one_pos, 2, r₁, hr₁, h'⟩
  -- the bound of Ding-Gwynne at the scales `ε = ((2R)⁻¹ r)^{β}`
  have hl := polyHighProb_comp_mul (polyHighProb_comp_rpow hDG hβm') (c := (2 * R)⁻¹) (by positivity)
  have hu := polyHighProb_comp_mul (polyHighProb_comp_rpow hDG hβp') (c := (2 * R)⁻¹) (by positivity)
  set K₁ := (2 * R) ^ (γ * lqgQ γ) * ((2 * R) ^ βm')⁻¹ with hK₁
  set K₂ := (2 * R) ^ (γ * lqgQ γ) * ((2 * R) ^ βp')⁻¹ with hK₂
  refine polyHighProb_mono_of_eventually (polyHighProb_inter (polyHighProb_inter hl hu) hGY) ?_
  filter_upwards [Ioo_mem_nhdsGT one_pos,
    eventually_rpow_le_mul (c := K₁) (by positivity) (a := γ * c₀ + βm') (b := βm) (by linarith),
    eventually_mul_rpow_le K₂ (a := βp' - γ * c₀) (b := βp) (by linarith)] with r hr hK₁r hK₂r
  obtain ⟨hr0, hr1⟩ := hr
  rintro ω ⟨⟨⟨hlow, -⟩, ⟨-, hup⟩⟩, hYω⟩ w hw
  obtain ⟨z, hz, hzw⟩ := exists_square_preimage hR hw
  have hρ0 : 0 < (2 * R)⁻¹ * r := by positivity
  have hρl : (((2 * R)⁻¹ * r) ^ βm') ^ (1 / βm') = (2 * R)⁻¹ * r := by
    rw [← Real.rpow_mul hρ0.le, mul_one_div_cancel hβm'.ne', Real.rpow_one]
  have hρu : (((2 * R)⁻¹ * r) ^ βp') ^ (1 / βp') = (2 * R)⁻¹ * r := by
    rw [← Real.rpow_mul hρ0.le, mul_one_div_cancel hβp'.ne', Real.rpow_one]
  have hball : affineMeasure γ hcirc μ (squareA R) (squareB R) ω (ball z ((2 * R)⁻¹ * r)) =
      ENNReal.ofReal (Real.exp (γ * (-(Y ω + lqgQ γ * Real.log ‖squareA R‖)))) * μ ω (ball w r) := by
    have hrad : ‖squareA R‖ * ((2 * R)⁻¹ * r) = r := by
      rw [han, mul_inv_cancel_left₀ (by positivity : (2 * R) ≠ 0)]
    rw [affineMeasure_ball _ _ _ ha, hzw, hrad]
  have hl' := hlow z hz
  rw [hρl, hball] at hl'
  have hu' := hup z hz
  rw [hρu, hball] at hu'
  set E1 := ENNReal.ofReal (Real.exp (γ * (-(Y ω + lqgQ γ * Real.log ‖squareA R‖)))) with hE1
  set F := ENNReal.ofReal (Real.exp (γ * (Y ω + lqgQ γ * Real.log ‖squareA R‖))) with hF
  have hFE : F * E1 = 1 := by
    rw [hF, hE1, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    rw [show γ * (Y ω + lqgQ γ * Real.log ‖squareA R‖) + γ * (-(Y ω + lqgQ γ * Real.log ‖squareA R‖)) = 0
      by ring, Real.exp_zero, ENNReal.ofReal_one]
  have hYb := abs_lt.1 (show |Y ω| < c₀ * Real.log r⁻¹ from hYω)
  have hlogr : Real.log r = -Real.log r⁻¹ := by rw [Real.log_inv, neg_neg]
  have hexpY1 : r ^ (γ * c₀) ≤ Real.exp (γ * Y ω) := by
    rw [Real.rpow_def_of_pos hr0]
    apply Real.exp_le_exp.2
    have := mul_lt_mul_of_pos_left hYb.1 hγ
    rw [hlogr]; linarith
  have hexpY2 : Real.exp (γ * Y ω) ≤ r ^ (-(γ * c₀)) := by
    rw [Real.rpow_def_of_pos hr0]
    apply Real.exp_le_exp.2
    have := mul_lt_mul_of_pos_left hYb.2 hγ
    rw [hlogr]; linarith
  have hFval : Real.exp (γ * (Y ω + lqgQ γ * Real.log ‖squareA R‖)) =
      Real.exp (γ * Y ω) * (2 * R) ^ (γ * lqgQ γ) := by
    rw [han, mul_add, Real.exp_add, Real.rpow_def_of_pos (by positivity)]
    ring_nf
  have hρm : ((2 * R)⁻¹ * r) ^ βm' = ((2 * R) ^ βm')⁻¹ * r ^ βm' := by
    rw [Real.mul_rpow (by positivity) hr0.le, Real.inv_rpow (by positivity)]
  have hρp : ((2 * R)⁻¹ * r) ^ βp' = ((2 * R) ^ βp')⁻¹ * r ^ βp' := by
    rw [Real.mul_rpow (by positivity) hr0.le, Real.inv_rpow (by positivity)]
  constructor
  · calc ENNReal.ofReal (r ^ βm) ≤ F * ENNReal.ofReal (((2 * R)⁻¹ * r) ^ βm') := by
          rw [hF, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
          apply ENNReal.ofReal_le_ofReal
          rw [hFval, hρm]
          calc r ^ βm ≤ K₁ * r ^ (γ * c₀ + βm') := hK₁r
            _ = r ^ (γ * c₀) * (2 * R) ^ (γ * lqgQ γ) * (((2 * R) ^ βm')⁻¹ * r ^ βm') := by
                rw [Real.rpow_add hr0, hK₁]; ring
            _ ≤ Real.exp (γ * Y ω) * (2 * R) ^ (γ * lqgQ γ) * (((2 * R) ^ βm')⁻¹ * r ^ βm') := by
                gcongr
      _ ≤ F * (E1 * μ ω (ball w r)) := by gcongr
      _ = μ ω (ball w r) := by rw [← mul_assoc, hFE, one_mul]
  · calc μ ω (ball w r) = F * (E1 * μ ω (ball w r)) := by rw [← mul_assoc, hFE, one_mul]
      _ ≤ F * ENNReal.ofReal (((2 * R)⁻¹ * r) ^ βp') := by gcongr
      _ = ENNReal.ofReal (Real.exp (γ * (Y ω + lqgQ γ * Real.log ‖squareA R‖)) *
            ((2 * R)⁻¹ * r) ^ βp') := by rw [hF, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
      _ ≤ ENNReal.ofReal (r ^ βp) := by
          apply ENNReal.ofReal_le_ofReal
          rw [hFval, hρp]
          calc Real.exp (γ * Y ω) * (2 * R) ^ (γ * lqgQ γ) * (((2 * R) ^ βp')⁻¹ * r ^ βp')
              ≤ r ^ (-(γ * c₀)) * (2 * R) ^ (γ * lqgQ γ) * (((2 * R) ^ βp')⁻¹ * r ^ βp') := by gcongr
            _ = K₂ * r ^ (βp' - γ * c₀) := by
                rw [sub_eq_add_neg, Real.rpow_add hr0, hK₂]; ring
            _ ≤ r ^ βp := hK₂r

section Rescaled

variable {Ω : Type*}

/-- Circle averages of `h^{(k)}`. -/
noncomputable def rescaledCirc (hcirc : Ω → ℝ → ℂ → ℝ) (k : ℕ) : Ω → ℝ → ℂ → ℝ :=
  affineCircle hcirc ((dyadicScale k : ℝ) : ℂ) 0

/-- Pairings of `h^{(k)}`. -/
noncomputable def rescaledPair (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (k : ℕ) :
    Ω → (ℂ → ℝ) → ℝ :=
  affinePairing hC hcirc ((dyadicScale k : ℝ) : ℂ) 0

/-- The LQG measure of `h^{(k)}`: `e^{-γ(h^ℂ_τ(0) + Q log τ)} μ₀(τ ·)`, `τ = 2^{-k}`. -/
noncomputable def rescaledMeas (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ₀ : Ω → Measure ℂ) (k : ℕ) :
    Ω → Measure ℂ :=
  affineMeasure γ hcirc μ₀ ((dyadicScale k : ℝ) : ℂ) 0

theorem dyadicScale_ne_zero' (k : ℕ) : ((dyadicScale k : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.2 (dyadicScale_pos k).ne'

theorem norm_dyadicScale (k : ℕ) : ‖((dyadicScale k : ℝ) : ℂ)‖ = dyadicScale k := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (dyadicScale_pos k)]

theorem rescaledMeas_ball (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ₀ : Ω → Measure ℂ) (k : ℕ) (ω : Ω)
    (w : ℂ) (r : ℝ) :
    rescaledMeas γ hcirc μ₀ k ω (ball w r) =
      ENNReal.ofReal (Real.exp (γ * (-(hcirc ω (dyadicScale k) 0 + lqgQ γ * Real.log (dyadicScale k))))) *
        μ₀ ω (ball ((dyadicScale k : ℂ) * w) (dyadicScale k * r)) := by
  rw [rescaledMeas, affineMeasure_ball _ _ _ (dyadicScale_ne_zero' k), add_zero, norm_dyadicScale]

end Rescaled

/-- **Reduction**: `RescaledBallMassUniformStepLP` from the
literature inputs `WholePlaneLQGBallMassBoundsLP` (Ding-Gwynne 2020, Lemma 3.8; module `LatticeProb.LQG.LQGMeasureInputs`) and
`LQGMeasureCoordChangeLP` at `α₀ = 0` (Duplantier-Sheffield 2011, Prop. 2.1; Sheffield-Wang 2016, Thm. 1.1), used only as
hypotheses. The whole-plane affine invariance is PROVED (`wholePlaneGFFAffineInvariance_lp`), and the mixture
`wholePlaneGFFMixtureStep_lp` is proved, so neither is a hypothesis here. -/
theorem rescaledBallMassUniformStep_lp
    (hDG : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), WholePlaneLQGBallMassBoundsLP P γ hC hcirc)
    (hCC : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureCoordChangeLP P γ 0 hC hcirc) :
    RescaledBallMassUniformStepLP.{u} := by
  intro γ hγ hγ2 Ω _ P hC hcirc μ₀ hGFF hμ₀ R hR βp βm hβp hβpA hβm
  have hP := hGFF.isProbabilityMeasure
  have hGk : ∀ k, IsWholePlaneGFF P (rescaledPair hC hcirc k) (rescaledCirc hcirc k) := fun k =>
    wholePlaneGFFAffineInvariance_lp P hC hcirc hGFF _ (dyadicScale_ne_zero' k) 0
  have hMk : ∀ k, IsLQGMeasureOfField P γ 0 (rescaledCirc hcirc k) (rescaledMeas γ hcirc μ₀ k) := fun k =>
    isLQGMeasureOfField_affine (hCC Ω P γ hC hcirc) hGFF hγ hγ2 hμ₀ (dyadicScale_ne_zero' k) 0
  have hG' : IsWholePlaneGFF (mixMeasure.prod P) (fun x => rescaledPair hC hcirc x.1 x.2)
      (fun x => rescaledCirc hcirc x.1 x.2) :=
    wholePlaneGFFMixtureStep_lp Ω P (rescaledPair hC hcirc) (rescaledCirc hcirc) mixMeasure inferInstance hGk
  have hM' : IsLQGMeasureOfField (mixMeasure.prod P) γ 0 (fun x => rescaledCirc hcirc x.1 x.2)
      (fun x => rescaledMeas γ hcirc μ₀ x.1 x.2) :=
    ae_mix_of_forall (p := fun k ω => IsLQGLimit γ (fieldCircleAverage 0 (rescaledCirc hcirc k ω))
      (rescaledMeas γ hcirc μ₀ k ω)) hMk
  have ha := squareA_ne_zero hR
  have hG'' := wholePlaneGFFAffineInvariance_lp (mixMeasure.prod P) _ _ hG' (squareA R) ha (squareB R)
  have hM'' := isLQGMeasureOfField_affine (hCC (ℕ × Ω) (mixMeasure.prod P) γ _ _) hG' hγ hγ2 hM' ha
    (squareB R)
  have hA0 : 0 < (2 + γ) ^ 2 / 2 := by positivity
  have h1 : (2 + γ) ^ 2 / 2 < ((2 + γ) ^ 2 / 2 + βm) / 2 := by linarith
  have h2 : ((2 + γ) ^ 2 / 2 + βm) / 2 < βm := by linarith
  have h3 : βp < (βp + (2 - γ) ^ 2 / 2) / 2 := by linarith
  have h4 : (βp + (2 - γ) ^ 2 / 2) / 2 < (2 - γ) ^ 2 / 2 := by linarith
  have hβp'0 : 0 < (βp + (2 - γ) ^ 2 / 2) / 2 := by linarith
  have hβm'0 : 0 < ((2 + γ) ^ 2 / 2 + βm) / 2 := by linarith
  have hl : 1 / (((2 + γ) ^ 2 / 2 + βm) / 2) < 2 / (2 + γ) ^ 2 := by
    rw [show (2 : ℝ) / (2 + γ) ^ 2 = 1 / ((2 + γ) ^ 2 / 2) by rw [one_div_div]]
    exact one_div_lt_one_div_of_lt hA0 h1
  have hu : 2 / (2 - γ) ^ 2 < 1 / ((βp + (2 - γ) ^ 2 / 2) / 2) := by
    rw [show (2 : ℝ) / (2 - γ) ^ 2 = 1 / ((2 - γ) ^ 2 / 2) by rw [one_div_div]]
    exact one_div_lt_one_div_of_lt hβp'0 h4
  have hD := hDG (ℕ × Ω) (mixMeasure.prod P) γ _ _ hG'' hγ hγ2 _ hM'' _ _ (by positivity) hl hu
  obtain ⟨p, hp, C, r₀, hr₀, hb⟩ := polyHighProb_closedBall_of_square hG' hγ hR h3 h2 hβp'0 hβm'0 hD
  refine ⟨p, hp, max C 0 * mixMass.toReal, r₀, hr₀, fun k r hr hrr => ?_⟩
  have hsub : (rescaledBallMassEvent γ hcirc μ₀ R βp βm k r)ᶜ ⊆
      {ω | (k, ω) ∈ {x : ℕ × Ω | ∀ w ∈ closedBall (0 : ℂ) R,
        ENNReal.ofReal (r ^ βm) ≤ rescaledMeas γ hcirc μ₀ x.1 x.2 (ball w r) ∧
          rescaledMeas γ hcirc μ₀ x.1 x.2 (ball w r) ≤ ENNReal.ofReal (r ^ βp)}ᶜ} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, mem_compl_iff]
    intro hk
    apply hω
    simp only [rescaledBallMassEvent, Set.mem_ofPred_eq]
    intro w hw
    obtain ⟨hlo, hhi⟩ := hk w hw
    rw [rescaledMeas_ball] at hlo hhi
    set E0 := ENNReal.ofReal (Real.exp (γ * (-(hcirc ω (dyadicScale k) 0 +
      lqgQ γ * Real.log (dyadicScale k))))) with hE0
    set F0 := ENNReal.ofReal (dyadicScale k ^ (γ * lqgQ γ) * Real.exp (γ * hcirc ω (dyadicScale k) 0))
      with hF0
    have hτr : 0 ≤ dyadicScale k ^ (γ * lqgQ γ) * Real.exp (γ * hcirc ω (dyadicScale k) 0) :=
      mul_nonneg (Real.rpow_nonneg (dyadicScale_pos k).le _) (Real.exp_pos _).le
    have hFE : F0 * E0 = 1 := by
      rw [hF0, hE0, ← ENNReal.ofReal_mul hτr, Real.rpow_def_of_pos (dyadicScale_pos k),
        ← Real.exp_add, ← Real.exp_add]
      rw [show Real.log (dyadicScale k) * (γ * lqgQ γ) + γ * hcirc ω (dyadicScale k) 0 +
        γ * -(hcirc ω (dyadicScale k) 0 + lqgQ γ * Real.log (dyadicScale k)) = 0 by ring,
        Real.exp_zero, ENNReal.ofReal_one]
    constructor
    · calc ENNReal.ofReal (dyadicScale k ^ (γ * lqgQ γ) * Real.exp (γ * hcirc ω (dyadicScale k) 0) *
            r ^ βm) = F0 * ENNReal.ofReal (r ^ βm) := ENNReal.ofReal_mul hτr
        _ ≤ F0 * (E0 * μ₀ ω (ball ((dyadicScale k : ℂ) * w) (dyadicScale k * r))) := by gcongr
        _ = μ₀ ω (ball ((dyadicScale k : ℂ) * w) (dyadicScale k * r)) := by
            rw [← mul_assoc, hFE, one_mul]
    · calc μ₀ ω (ball ((dyadicScale k : ℂ) * w) (dyadicScale k * r))
          = F0 * (E0 * μ₀ ω (ball ((dyadicScale k : ℂ) * w) (dyadicScale k * r))) := by
            rw [← mul_assoc, hFE, one_mul]
        _ ≤ F0 * ENNReal.ofReal (r ^ βp) := by gcongr
        _ = ENNReal.ofReal (dyadicScale k ^ (γ * lqgQ γ) * Real.exp (γ * hcirc ω (dyadicScale k) 0) *
            r ^ βp) := (ENNReal.ofReal_mul hτr).symm
  calc P (rescaledBallMassEvent γ hcirc μ₀ R βp βm k r)ᶜ
      ≤ P {ω | (k, ω) ∈ {x : ℕ × Ω | ∀ w ∈ closedBall (0 : ℂ) R,
        ENNReal.ofReal (r ^ βm) ≤ rescaledMeas γ hcirc μ₀ x.1 x.2 (ball w r) ∧
          rescaledMeas γ hcirc μ₀ x.1 x.2 (ball w r) ≤ ENNReal.ofReal (r ^ βp)}ᶜ} := measure_mono hsub
    _ ≤ ENNReal.ofReal (mixMass.toReal * ((k : ℝ) + 1) ^ 2) * (mixMeasure.prod P)
        {x : ℕ × Ω | ∀ w ∈ closedBall (0 : ℂ) R,
          ENNReal.ofReal (r ^ βm) ≤ rescaledMeas γ hcirc μ₀ x.1 x.2 (ball w r) ∧
            rescaledMeas γ hcirc μ₀ x.1 x.2 (ball w r) ≤ ENNReal.ofReal (r ^ βp)}ᶜ := measure_slice_le _ k
    _ ≤ ENNReal.ofReal (mixMass.toReal * ((k : ℝ) + 1) ^ 2) * ENNReal.ofReal (C * r ^ p) := by
        gcongr; exact hb r hr hrr
    _ ≤ ENNReal.ofReal (max C 0 * mixMass.toReal * ((k : ℝ) + 1) ^ 2 * r ^ p) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        calc mixMass.toReal * ((k : ℝ) + 1) ^ 2 * (C * r ^ p)
            ≤ mixMass.toReal * ((k : ℝ) + 1) ^ 2 * (max C 0 * r ^ p) := by
              gcongr; exact le_max_left _ _
          _ = max C 0 * mixMass.toReal * ((k : ℝ) + 1) ^ 2 * r ^ p := by ring

end LatticeProb.LQG.LQGMeasureNonatomicMass


