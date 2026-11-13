/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cP.IGHalf at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cP.IGBundle
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cP.AffineExcursion
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cP.ConfigParts
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.LocalCircleProcess

/-!
# The IG half of measurable Lemma 4.3 on the transfer's disks

Source: [18] Lemma 2.4, the imaginary-geometry coordinate
change (IG1) and the IG field modulo `2πχ` (IG4).

On the observation disk `V = B_a(w)` (`a = (1−ρ)/4`) pick a rational circle `∂B_{s₀}(w')` inside `V`
(`s₀ ∈ ℚ`, `w' ∈ ℚ + iℚ`). The observed IG circle averages (with phase) are pulled back by `ψ(v) = w' + s₀ v` and
renormalized at the unit circle (`l43pNorm`); one fixed S7 map `g` of the bundle, for the region
`U' = ψ⁻¹(U)` (`U = B_{a/2}(w)`), applied to this input returns the excursions of the re-rooted curve
`affineReroot z s₀ 0 η_L` (`ae_excursionSegment_of_l43pNorm`), with `z = w'` for the zero-cone side (IG field
`h^IG`) and `z = w' − z₀` for the translated side (IG field `h^IG(· − z₀)`). Undoing `ψ`
(`excursionSegment_of_affineReroot`) gives the excursion segments into `U` at rational points of
`η_L`, resp. of `η_L + z₀`: this is `L43PZeroConeIGInput`, proved for every transfer disk
(`l43pZeroConeIGInput_holds`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open LQGMetric MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.IGLaw

namespace MatedCRTHarmonic.GMS4cP

open MatedCRTHarmonic.GMS4b

/-- A curve agreeing at rational times with a continuous one has it as continuous version. -/
theorem contVersion_eq_of_rat {f : ℝ → ℂ} {c : C(ℝ, ℂ)} (h : ∀ t : ℚ, f t = c t) :
    GMS4c.contVersion f = c := by
  unfold GMS4c.contVersion
  have e : (fun q : ℚ => f q) = GMS4c.ratRestrict c := funext h
  rw [e]
  exact GMS4c.ratRestrict_injective.extend_apply id (fun _ => 0) c

/-- Pulling back by an affine map and renormalizing at the unit circle only reads the circles inside `V` when
The pulled-back circles inside `W` and the reference circle map into `V`. -/
theorem restrictCircles_l43pNorm_restrictCircles (r : ℝ) [Fact (0 < r)] (γ : ℝ)
    {V W : Set ℂ} {z : ℂ} {s : ℝ} (hs : 0 < s)
    (hW : ∀ v ρ, 0 < ρ → closedBall v ρ ⊆ W → closedBall (z + s * v) (s * ρ) ⊆ V)
    (hR : closedBall z s ⊆ V) (K : ℝ → ℂ → ℝ) :
    restrictCircles W (l43pNorm r (igPullback γ z s 0 (restrictCircles V K))) =
      restrictCircles W (l43pNorm r (igPullback γ z s 0 K)) := by
  classical
  have hev : ∀ v ρ, 0 < ρ → closedBall (z + s * v) (s * ρ) ⊆ V →
      igPullback γ z s 0 (restrictCircles V K) ρ v = igPullback γ z s 0 K ρ v := by
    intro v ρ hρ hsub
    simp only [igPullback, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one,
      restrictCircles]
    rw [ite_eq_left ⟨mul_pos hs hρ, hsub⟩]
  have h10 : igPullback γ z s 0 (restrictCircles V K) 1 0 = igPullback γ z s 0 K 1 0 :=
    hev 0 1 one_pos (by simpa using hR)
  funext ρ v
  show (if 0 < ρ ∧ closedBall v ρ ⊆ W then _ else 0) =
    (if 0 < ρ ∧ closedBall v ρ ⊆ W then _ else 0)
  split_ifs with h
  · rw [l43pNorm, l43pNorm, posIn_apply_of_pos h.1, posIn_apply_of_pos h.1]
    rw [h10, hev v ρ h.1 (hW v ρ h.1 h.2)]
  · rfl

/-- Composition of a translation pullback and an affine pullback. -/
theorem igPullback_comp_translate (γ : ℝ) (z z₀ : ℂ) (s : ℝ) (K : ℝ → ℂ → ℝ) :
    igPullback γ z s 0 (igPullback γ (-z₀) 1 0 K) = igPullback γ (z - z₀) s 0 K := by
  funext ρ v
  simp only [igPullback, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one,
    Complex.ofReal_one, one_mul, mul_zero, sub_zero]
  congr 1
  ring

/-- Re-rooting the translated curve. -/
theorem affineReroot_translateC (z z₀ : ℂ) (s : ℝ) (c : C(ℝ, ℂ)) :
    affineReroot z s 0 (translateC z₀ c) = affineReroot (z - z₀) s 0 c := by
  have hfh : firstHit (translateC z₀ c) z = firstHit c (z - z₀) := by
    unfold firstHit
    congr 1
    ext t
    simp only [translateC, ContinuousMap.coe_mk, mem_ofPred_eq]
    constructor <;> intro h <;> linear_combination h
  ext t
  rw [affineReroot_zero_apply, affineReroot_zero_apply, hfh]
  simp only [translateC, ContinuousMap.coe_mk]
  ring

section geometry

/-- The rational reference data on the transfer's observation disk. -/
theorem exists_rational_reference {a : ℝ} (ha : 0 < a) (w : ℂ) :
    ∃ (s₀ : ℚ) (qc : ℚ × ℚ), 0 < (s₀ : ℝ) ∧ (s₀ : ℝ) < a / 8 ∧
      ‖GMS4c.ratPt qc - w‖ < a / 8 := by
  obtain ⟨s₀, hs₀, hs₀'⟩ := exists_rat_btwn (show (0 : ℝ) < a / 8 by positivity)
  obtain ⟨x, hx, hx'⟩ := exists_rat_btwn (show w.re - a / 16 < w.re by linarith)
  obtain ⟨y, hy, hy'⟩ := exists_rat_btwn (show w.im - a / 16 < w.im by linarith)
  refine ⟨s₀, (x, y), hs₀, hs₀', ?_⟩
  have h := Complex.norm_le_abs_re_add_abs_im (GMS4c.ratPt (x, y) - w)
  have hre : (GMS4c.ratPt (x, y) - w).re = x - w.re := by simp [GMS4c.ratPt]
  have him : (GMS4c.ratPt (x, y) - w).im = y - w.im := by simp [GMS4c.ratPt]
  rw [hre, him] at h
  have h1 : |(x : ℝ) - w.re| < a / 16 := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
  have h2 : |(y : ℝ) - w.im| < a / 16 := abs_sub_lt_iff.2 ⟨by linarith, by linarith⟩
  linarith

end geometry

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : NNReal → Ω → ℝ} {T : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- **The IG half of measurable Lemma 4.3 on every transfer disk.** -/
theorem l43pZeroConeIGInput_holds
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' T ηL η η₀ bm)
    {ρ : ℝ} (hρ : ρ < 1) (w : ℂ) : L43PZeroConeIGInput D ρ w := by
  have hP := D.isProbabilityMeasure
  set a : ℝ := (1 - ρ) / 4 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  set z₀ : ℂ := w + ((1 - ρ) / 2 : ℝ) with hz₀
  set r : ℝ := 2 * Real.pi * igChi γ with hr
  have : Fact (0 < r) := ⟨igPeriod_pos D⟩
  obtain ⟨s₀q, qc, hs₀, hs₀a, hqc⟩ := exists_rational_reference ha w
  set s₀ : ℝ := (s₀q : ℝ)
  set w' : ℂ := GMS4c.ratPt qc
  -- the regions
  set V : TopologicalSpace.Opens ℂ := l46tObservation ρ w
  set U : Set ℂ := ((l46tLocalRegion ρ w : TopologicalSpace.Opens ℂ) : Set ℂ)
  have hU : U = ball w (a / 2) := by
    simp only [U, l46tLocalRegion, TopologicalSpace.Opens.coe_mk, ha_def]
    congr 1
    ring
  have hV : (V : Set ℂ) = ball w a := rfl
  have hUo : IsOpen U := (l46tLocalRegion ρ w).isOpen
  have hUb : Bornology.IsBounded U := hU ▸ isBounded_ball
  set U' : Set ℂ := {v : ℂ | w' + (s₀ : ℂ) * v ∈ U}
  set c' : ℂ := (w - w') / s₀
  have hs₀' : (s₀ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hs₀.ne'
  have hnorm_aff : ∀ v : ℂ, ‖w' + (s₀ : ℂ) * v - w‖ = s₀ * ‖v - c'‖ := by
    intro v
    have : w' + (s₀ : ℂ) * v - w = (s₀ : ℂ) * (v - c') := by
      simp only [c']
      field_simp
      ring
    rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs₀]
  have hU'ball : U' = ball c' (a / 2 / s₀) := by
    ext v
    simp only [U', mem_ofPred_eq, hU, mem_ball, dist_eq_norm, hnorm_aff]
    rw [lt_div_iff₀ hs₀, mul_comm]
  have hU'o : IsOpen U' := hU'ball ▸ isOpen_ball
  have hU'b : Bornology.IsBounded U' := hU'ball ▸ isBounded_ball
  set δ' : ℝ := a / (4 * s₀)
  have hδ' : 0 < δ' := by positivity
  obtain ⟨g, hg, hgS⟩ := ae_excursionSegment_of_l43pNorm D hU'o hU'b hδ'
  -- geometry of the pulled-back circles
  have hW : ∀ v ρ', 0 < ρ' → closedBall v ρ' ⊆ thickening δ' U' →
      closedBall (w' + (s₀ : ℂ) * v) (s₀ * ρ') ⊆ (V : Set ℂ) := by
    intro v ρ' _ hsub x hx
    set y : ℂ := (x - w') / s₀
    have hxy : x = w' + (s₀ : ℂ) * y := by
      simp only [y]
      field_simp
      ring
    have hy : y ∈ closedBall v ρ' := by
      rw [mem_closedBall, dist_eq_norm]
      rw [mem_closedBall, dist_eq_norm, hxy, show w' + (s₀ : ℂ) * y - (w' + (s₀ : ℂ) * v) =
        (s₀ : ℂ) * (y - v) by ring, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hs₀] at hx
      exact le_of_mul_le_mul_left hx hs₀
    obtain ⟨u, hu, hdu⟩ := mem_thickening_iff.1 (hsub hy)
    rw [hU'ball, mem_ball] at hu
    have hyc : dist y c' < a / 2 / s₀ + δ' := by
      linarith [dist_triangle y u c']
    rw [hV, mem_ball, dist_eq_norm, hxy, hnorm_aff]
    rw [dist_eq_norm] at hyc
    have : s₀ * ‖y - c'‖ < s₀ * (a / 2 / s₀ + δ') := mul_lt_mul_of_pos_left hyc hs₀
    have e : s₀ * (a / 2 / s₀ + δ') = 3 * a / 4 := by
      simp only [δ']
      field_simp
      ring
    linarith
  have hRef : closedBall w' s₀ ⊆ (V : Set ℂ) := by
    intro x hx
    rw [hV, mem_ball]
    rw [mem_closedBall] at hx
    have := dist_triangle x w' w
    rw [dist_eq_norm w' w] at this
    linarith
  -- the observation map
  let Λ : LQGMetric.DistOn V × ℝ → ℝ → ℂ → ℝ := fun x =>
    restrictCircles (thickening δ' U')
      (l43pNorm r (igPullback γ w' s₀ 0 (GMS4c.localIGCircleProcess V x)))
  have hΛ : Measurable Λ :=
    (measurable_restrictCircles _).comp ((measurable_l43pNorm r).comp
      ((measurable_igPullback γ w' s₀ 0).comp (GMS4c.measurable_localIGCircleProcess V)))
  let lab : ℚ × ℚ → ℚ × ℚ := fun q => ((q.1 - qc.1) / s₀q, (q.2 - qc.2) / s₀q)
  have hlab : ∀ q, w' + (s₀ : ℂ) * GMS4c.ratPt (lab q) = GMS4c.ratPt q := by
    intro q
    have hsq : ((s₀q : ℚ) : ℂ) ≠ 0 := by exact_mod_cast (show (s₀q : ℝ) ≠ 0 from hs₀.ne')
    simp only [lab, w', s₀, GMS4c.ratPt, Complex.ofReal_ratCast]
    push_cast
    field_simp
    ring_nf
  let G : LQGMetric.DistOn V × ℝ → (ℚ × ℚ → ℝ → ℂ) := fun x q u =>
    (s₀ : ℂ) * GMS4c.contVersion (g (Λ x) (lab q)) (u / s₀ ^ 2) + w'
  have hG : Measurable G := by
    refine measurable_pi_iff.2 fun q => measurable_pi_iff.2 fun u => ?_
    have h1 : Measurable fun x : LQGMetric.DistOn V × ℝ =>
        GMS4c.contVersion (g (Λ x) (lab q)) :=
      GMS4c.measurable_contVersion.comp ((measurable_pi_apply (lab q)).comp (hg.comp hΛ))
    exact ((ContinuousMap.measurable_eval (u / s₀ ^ 2)).comp h1).const_mul _ |>.add_const _
  -- reading the excursions from the transported S7 identity
  have hread : ∀ (c : C(ℝ, ℂ)) (x : LQGMetric.DistOn V × ℝ),
      Function.Surjective c → Tendsto c (cocompact ℝ) (cocompact ℂ) →
      (∀ q : ℚ × ℚ, GMS4c.ratPt q ∈ U' → ∀ t : ℚ,
        g (Λ x) q t = excursionSegment (affineReroot w' s₀ 0 c) U' (GMS4c.ratPt q) t) →
      ∀ q : ℚ × ℚ, GMS4c.ratPt q ∈ U → G x q = excursionSegment c U (GMS4c.ratPt q) := by
    intro c x hsurj htr hx q hq
    have hq' : GMS4c.ratPt (lab q) ∈ U' := by
      change w' + (s₀ : ℂ) * GMS4c.ratPt (lab q) ∈ U
      rw [hlab]
      exact hq
    have hcv : GMS4c.contVersion (g (Λ x) (lab q)) =
        ⟨excursionSegment (affineReroot w' s₀ 0 c) U' (GMS4c.ratPt (lab q)), by
          unfold excursionSegment
          fun_prop⟩ :=
      contVersion_eq_of_rat fun t => hx (lab q) hq' t
    funext u
    simp only [G, hcv, ContinuousMap.coe_mk]
    have := excursionSegment_of_affineReroot hUo hUb hsurj htr hs₀
      (show w' + (s₀ : ℂ) * GMS4c.ratPt (lab q) ∈ U by rw [hlab]; exact hq) u
    rw [this, hlab]
  refine ⟨G, hG, ?_, ?_⟩
  · -- the translated side
    have hcirc := ae_circleAvg_affineComp_all D.igField.1.1 one_pos (-z₀)
    filter_upwards [hgS (w' - z₀) s₀ hs₀, hcirc, D.spaceFilling] with ω hgω hcω hspace
    have hsurj : Function.Surjective (translateC z₀ (ηL ω)) := by
      intro y
      obtain ⟨t, ht⟩ := hspace.1 (y - z₀)
      exact ⟨t, by simp [translateC, ht]⟩
    have htr : Tendsto (translateC z₀ (ηL ω)) (cocompact ℝ) (cocompact ℂ) := by
      have h1 : Tendsto (Homeomorph.addRight z₀) (cocompact ℂ) (cocompact ℂ) :=
        (Homeomorph.addRight z₀).map_cocompact.le
      exact h1.comp hspace.2.1
    have hobs : GMS4c.localIGCircleProcess V
        (restrictTo V (l46tTranslatedField z₀ hIG₀ ω), T ω) =
        restrictCircles V (igPullback γ (-z₀) 1 0 (igCircleAvgInput (hIG₀ ω, T ω))) := by
      rw [GMS4c.localIGCircleProcess_restrictTo]
      funext ρ' v
      unfold restrictCircles
      split_ifs with h
      · simp only [l46tTranslatedField, igPullback, igCircleAvgInput, Complex.ofReal_zero,
          zero_mul, Complex.exp_zero, mul_one, Complex.ofReal_one, one_mul, mul_zero, sub_zero]
        rw [hcω ρ' h.1 v]
        simp only [Complex.ofReal_one, one_mul]
        ring_nf
      · rfl
    have hΛω : Λ (restrictTo V (l46tTranslatedField z₀ hIG₀ ω), T ω) =
        restrictCircles (thickening δ' U') (l43pNorm r (igPullback γ (w' - z₀) s₀ 0
          (igCircleAvgInput (hIG₀ ω, T ω)))) := by
      simp only [Λ]
      rw [hobs, restrictCircles_l43pNorm_restrictCircles r γ hs₀ hW hRef,
        igPullback_comp_translate]
    refine hread (translateC z₀ (ηL ω)) _ hsurj htr ?_
    intro q hq t
    rw [hΛω, affineReroot_translateC]
    exact hgω q hq t
  · -- the zero-cone side
    filter_upwards [hgS w' s₀ hs₀, D.spaceFilling] with ω hgω hspace
    have hΛω : Λ (restrictTo V (hIG₀ ω), T ω) =
        restrictCircles (thickening δ' U') (l43pNorm r (igPullback γ w' s₀ 0
          (igCircleAvgInput (hIG₀ ω, T ω)))) := by
      simp only [Λ]
      rw [GMS4c.localIGCircleProcess_restrictTo,
        restrictCircles_l43pNorm_restrictCircles r γ hs₀ hW hRef]
      rfl
    refine hread (ηL ω) _ hspace.1 hspace.2.1 ?_
    intro q hq t
    rw [hΛω]
    exact hgω q hq t

end MatedCRTHarmonic.GMS4cP
