/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Complex.PolygonDixon at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.PolygonDixonCore
import Mathlib.Analysis.Complex.Liouville

/-!
# Dixon's theorem (EXT-CA node H3, final assembly)

Blueprint `blueprint/EXT_CA_BLUEPRINT.md`, §3 "H. Homology Cauchy", node H3.

**Dixon's theorem.** A closed polygon `p` in an open set `U` whose winding number vanishes at
every point of the complement of `U` integrates the 1-form `f dz` of any function `f` holomorphic
on `U` to zero.

The proof (Dixon 1971) glues the two holomorphic functions
`h z = ∮_p (F z - F w)/(z - w) dw` (holomorphic on `U`, `PolygonDixonCore`) and
`h₂ z = ∮_p F w/(w - z) dw` (holomorphic off the carrier, `PolygonDixonCore`) along the open set
`V = {z ∉ |p| : wind p z = 0}`: on `U ∩ V` the identity `∮_p dw/(z - w) = -2πi wind p z = 0`
gives `h = h₂`.  Since `|p| ⊆ U` and `wind p a = 0` for `a ∉ U`, the open sets `U` and `V`
cover `ℂ`, so the glued function is entire; it is bounded, because far out it equals `h₂`, where
`‖h₂ z‖ ≤ l(p) sup|F| / dist(z,|p|) ≤ l(p) sup|F|`.  Liouville's theorem makes it constant, and
the same estimate at arbitrarily distant points makes that constant `0`.  Restricting to `z ∈ V`
gives the two-variable Cauchy kernel lemma, and `walkIntegral_eq_zero_of_cauchyKernel` (Dixon's
algebraic finishing step, `PolygonDixonReduce`) yields the theorem.

## Sources

J. D. Dixon, *A brief proof of Cauchy's integral theorem*, Proc. Amer. Math. Soc. **29** (1971)
625-626.  R. B. Burckel, *Classical Analysis in the Complex Plane* (Birkhäuser 2021), Thm 7.22
(homology form of Cauchy's theorem), printed pp. 477–478, and Ch. 4.  The statement proved here is
the special case of Burckel Thm 7.22 (i)⇒(ii) for one closed polygon; part (iii) is not stated
(weaker statement, unused parts omitted; the earlier citation "Theorem 10.11" was to an exercise).
-/

noncomputable section

open Set Metric Filter Complex Real AffineMap MeasureTheory
open scoped Topology Convex Interval

namespace QuantumZipper.CA.Homology

/-! ## The winding number as the integral of `dw/(z - w)` -/

/-- `∮_p dw/(w - z) = 2πi · wind p z`. -/
theorem walkIntegral_inv_sub_eq (p : Polygon) (z : ℂ) :
    walkIntegral (fun w => (w - z)⁻¹) p.head p.rest = 2 * π * I * wind p z := by
  have h : (2 * π * I) * wind p z = walkIntegral (fun w => (w - z)⁻¹) p.head p.rest := by
    rw [wind_def, ← mul_assoc, mul_inv_cancel₀ twoPiI_ne_zero, one_mul]
  exact h.symm

/-- `∮_p dw/(z - w) = -2πi · wind p z`, hence `0` where the winding number vanishes. -/
theorem walkIntegral_sub_inv_eq_zero {p : Polygon} {z : ℂ} (hz : z ∉ p.carrier)
    (hzw : wind p z = 0) :
    walkIntegral (fun w => (z - w)⁻¹) p.head p.rest = 0 := by
  have hc : ContinuousOn (fun w : ℂ => (w - z)⁻¹) p.carrier :=
    (continuous_id.sub continuous_const).continuousOn.inv₀ fun w hw =>
      (sub_ne_zero (a := w) (b := z)).mpr fun h => hz (h ▸ hw)
  have h1 : walkIntegral (fun w => (z - w)⁻¹) p.head p.rest
      = -walkIntegral (fun w => (w - z)⁻¹) p.head p.rest := by
    rw [← walkIntegral_neg p.head p.rest hc]
    exact walkIntegral_congr fun w _ => by rw [← neg_sub w z, inv_neg]
  rw [h1, walkIntegral_inv_sub_eq, hzw, mul_zero, neg_zero]

/-! ## Agreement of the two parametric integrals on `U ∩ V` -/

/-- **Dixon's identity.**  Off the carrier, where the winding number of `p` about `z` vanishes,
the parametric integral of the difference quotient equals the Cauchy-type integral. -/
theorem walkIntegral_sec_eq_walkIntegral_cauchy {U : Set ℂ} {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F U) {p : Polygon} (hpU : p.carrier ⊆ U)
    {z : ℂ} (hz : z ∉ p.carrier) (hzw : wind p z = 0) :
    walkIntegral (fun w => sec F z w) p.head p.rest
      = walkIntegral (fun w => F w / (w - z)) p.head p.rest := by
  have hcontF : ContinuousOn F p.carrier := hF.continuousOn.mono hpU
  have hcinv : ContinuousOn (fun w : ℂ => (z - w)⁻¹) p.carrier :=
    (continuous_const.sub continuous_id).continuousOn.inv₀ fun w hw =>
      (sub_ne_zero (a := z) (b := w)).mpr fun h => hz (h ▸ hw)
  have hcA : ContinuousOn (fun w => F z * (z - w)⁻¹) p.carrier := continuousOn_const.mul hcinv
  have hcB : ContinuousOn (fun w => F w / (w - z)) p.carrier :=
    hcontF.div (continuous_id.sub continuous_const).continuousOn fun w hw =>
      (sub_ne_zero (a := w) (b := z)).mpr fun h => hz (h ▸ hw)
  have hpoint : ∀ w ∈ p.carrier, sec F z w = F z * (z - w)⁻¹ + F w / (w - z) := by
    intro w hw
    have hwz : w ≠ z := fun h => hz (h ▸ hw)
    have hneg : (w - z)⁻¹ = -(z - w)⁻¹ := by rw [← neg_sub w z, inv_neg, neg_neg]
    rw [sec_of_ne (Ne.symm hwz), div_eq_mul_inv (F z - F w) (z - w),
      div_eq_mul_inv (F w) (w - z), hneg]
    ring
  have hzero := walkIntegral_sub_inv_eq_zero hz hzw
  calc walkIntegral (fun w => sec F z w) p.head p.rest
      = walkIntegral (fun w => F z * (z - w)⁻¹ + F w / (w - z)) p.head p.rest :=
        walkIntegral_congr hpoint
    _ = walkIntegral (fun w => F z * (z - w)⁻¹) p.head p.rest
          + walkIntegral (fun w => F w / (w - z)) p.head p.rest :=
        walkIntegral_add _ _ hcA hcB
    _ = F z * walkIntegral (fun w => (z - w)⁻¹) p.head p.rest
          + walkIntegral (fun w => F w / (w - z)) p.head p.rest := by
        rw [walkIntegral_const_mul (F z) p.head p.rest hcinv]
    _ = walkIntegral (fun w => F w / (w - z)) p.head p.rest := by
        rw [hzero, mul_zero, zero_add]

/-! ## The two-variable Cauchy kernel lemma -/

theorem polyIntegral_cauchyKernel_eq_zero {U : Set ℂ} (hU : IsOpen U) {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F U) {p : Polygon} (hcl : p.last = p.head) (hpU : p.carrier ⊆ U)
    (hw : ∀ a ∉ U, wind p a = 0) {z : ℂ} (hz : z ∉ p.carrier) (hzw : wind p z = 0) :
    walkIntegral (fun w => F w / (w - z)) p.head p.rest = 0 := by
  classical
  set V : Set ℂ := {a | a ∉ p.carrier ∧ wind p a = 0} with hV
  have hVopen : IsOpen V := by
    rw [isOpen_iff_mem_nhds]
    rintro a ⟨hac, haw⟩
    obtain ⟨ε, hε, hloc⟩ := wind_locallyConstant p hcl a hac
    obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1
      (((Polygon.isCompact_carrier p).isClosed.isOpen_compl).mem_nhds hac)
    refine Filter.mem_of_superset (Metric.ball_mem_nhds a (lt_min hε hr)) fun b hb => ?_
    have hbε : ‖b - a‖ < ε :=
      lt_of_lt_of_le (by simpa [dist_eq_norm] using mem_ball.mp hb) (min_le_left _ _)
    obtain ⟨hbcar, hbw⟩ := hloc b hbε
    exact ⟨hbcar, by rw [hbw, haw]⟩
  obtain ⟨M, hM⟩ := (Polygon.isCompact_carrier p).exists_bound_of_continuousOn
    (hF.continuousOn.mono hpU)
  have hlen : (0 : ℝ) ≤ p.length := by
    rw [Polygon.length_def]
    exact walkLength_nonneg _ _
  have hM0 : (0 : ℝ) ≤ max M 0 := le_max_right _ _
  have hbig : (0 : ℝ) ≤ p.length * ‖(2 * π * I)⁻¹‖ := mul_nonneg hlen (norm_nonneg _)
  -- a ball containing the carrier, and a threshold beyond which `V` and the estimates apply
  set Rc : ℝ := 1 + (‖p.head‖ + walkLength p.head p.rest) with hRcdef
  have hRc1 : 1 ≤ Rc := by
    have h1 : (0 : ℝ) ≤ ‖p.head‖ + walkLength p.head p.rest :=
      add_nonneg (norm_nonneg _) (walkLength_nonneg _ _)
    simp only [hRcdef]
    linarith
  have hRc0 : (0 : ℝ) ≤ Rc := le_trans zero_le_one hRc1
  have hRcball : p.carrier ⊆ Metric.ball 0 Rc := by
    rw [hRcdef]
    exact carrier_subset_ball p
  set R : ℝ := Rc + p.length * ‖(2 * π * I)⁻¹‖ + 2 with hRdef
  have hRge : Rc + 1 ≤ R := by
    simp only [hRdef]
    linarith
  have hfar : ∀ a : ℂ, R ≤ ‖a‖ →
      ‖(if a ∈ V then walkIntegral (fun w => F w / (w - a)) p.head p.rest
        else walkIntegral (fun w => sec F a w) p.head p.rest)‖
        ≤ p.length * max M 0 / (‖a‖ - Rc) := by
    intro a ha
    have ha_big : Rc + p.length * ‖(2 * π * I)⁻¹‖ + 1 < ‖a‖ := by
      simp only [hRdef] at ha
      linarith
    have hain : a ∉ p.carrier := fun hmem => by
      have h1 := hRcball hmem
      rw [Metric.mem_ball, dist_zero_right] at h1
      have h3 : Rc ≤ R := by
        simp only [hRdef]
        linarith
      linarith
    have haV : a ∈ V := ⟨hain, wind_eq_zero_of_large p hcl hRcball ha_big⟩
    rw [ite_eq_left haV]
    have hden : Rc < ‖a‖ := by linarith
    have hbd : ∀ w ∈ p.carrier, ‖F w / (w - a)‖ ≤ max M 0 / (‖a‖ - Rc) := by
      intro w hw'
      have hwR : ‖w‖ < Rc := by
        have h1 := hRcball hw'
        rwa [Metric.mem_ball, dist_zero_right] at h1
      have h4 : ‖a‖ ≤ ‖w - a‖ + ‖w‖ := by
        calc ‖a‖ = ‖(a - w) + w‖ := by ring_nf
          _ ≤ ‖a - w‖ + ‖w‖ := norm_add_le _ _
          _ = ‖w - a‖ + ‖w‖ := by rw [norm_sub_rev]
      have h5 : ‖a‖ - Rc ≤ ‖w - a‖ := by linarith
      rw [norm_div]
      refine le_trans (div_le_div_of_nonneg_right
        (le_trans (hM w hw') (le_max_left M 0)) (norm_nonneg _)) ?_
      exact div_le_div_of_nonneg_left hM0 (by linarith) h5
    exact (norm_walkIntegral_le (fun w => F w / (w - a)) p.head p.rest
      (C := max M 0 / (‖a‖ - Rc)) hbd).trans_eq (by rw [Polygon.length_def, mul_div_assoc])
  have hGdiff : Differentiable ℂ (fun a => if a ∈ V
      then walkIntegral (fun w => F w / (w - a)) p.head p.rest
      else walkIntegral (fun w => sec F a w) p.head p.rest) := by
    refine differentiable_of_differentiableOn_union_of_isOpen ?_ ?_ ?_ hU hVopen
    · refine (differentiableOn_walkIntegral_sec hU hF hpU).congr fun a ha => ?_
      by_cases haV : a ∈ V
      · rw [ite_eq_left haV]
        exact (walkIntegral_sec_eq_walkIntegral_cauchy hF hpU haV.1 haV.2).symm
      · exact ite_eq_right haV
    · exact ((differentiableOn_walkIntegral_cauchy hU hF hpU).mono
        (fun a ha => ha.1)).congr fun a ha => ite_eq_left ha
    · rw [eq_univ_iff_forall]
      intro a
      by_cases ha : a ∈ U
      · exact Or.inl ha
      · exact Or.inr ⟨fun h => ha (hpU h), hw a ha⟩
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    hGdiff.continuous.continuousOn
  have hglob : ∀ a : ℂ, ‖(if a ∈ V
      then walkIntegral (fun w => F w / (w - a)) p.head p.rest
      else walkIntegral (fun w => sec F a w) p.head p.rest)‖ ≤ max C (p.length * max M 0) := by
    intro a
    by_cases h : ‖a‖ ≤ R
    · exact le_trans (hC a (by simpa [dist_eq_norm] using h)) (le_max_left _ _)
    · refine le_trans (le_trans (hfar a (le_of_lt (not_le.mp h)))
        (div_le_self (mul_nonneg hlen hM0) (by linarith [hRge, not_le.mp h]))) (le_max_right _ _)
  set G : ℂ → ℂ := fun a => if a ∈ V
      then walkIntegral (fun w => F w / (w - a)) p.head p.rest
      else walkIntegral (fun w => sec F a w) p.head p.rest with hGdef
  have hbdd : Bornology.IsBounded (range G) := by
    rw [Metric.isBounded_range_iff]
    refine ⟨2 * max C (p.length * max M 0), fun x y => ?_⟩
    rw [dist_eq_norm]
    calc ‖G x - G y‖ ≤ ‖G x‖ + ‖G y‖ := norm_sub_le _ _
      _ ≤ max C (p.length * max M 0) + max C (p.length * max M 0) := add_le_add (hglob x) (hglob y)
      _ = 2 * max C (p.length * max M 0) := by ring
  have hGfar : ∀ a : ℂ, R ≤ ‖a‖ → ‖G a‖ ≤ p.length * max M 0 / (‖a‖ - Rc) := by
    intro a ha
    rw [hGdef]
    exact hfar a ha
  have hzero : ∀ a : ℂ, G a = 0 := by
    have hconst : ∀ x y : ℂ, G x = G y :=
      Differentiable.apply_eq_apply_of_bounded hGdiff hbdd
    have hkey : G 0 = 0 := by
      by_contra hne
      have hpos : 0 < ‖G 0‖ := norm_pos_iff.mpr hne
      obtain ⟨n, hn⟩ := exists_nat_gt (R + p.length * max M 0 / ‖G 0‖ + 1)
      have hX : (0 : ℝ) ≤ p.length * max M 0 := mul_nonneg hlen hM0
      have hR1 : 1 ≤ R := by linarith
      have h4 : (0 : ℝ) ≤ p.length * max M 0 / ‖G 0‖ := div_nonneg hX hpos.le
      have hnR : R ≤ (n : ℝ) := by linarith
      have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
      have hnorm : ‖((n : ℝ) : ℂ)‖ = (n : ℝ) := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnpos.le]
      have h1 := hGfar ((n : ℝ) : ℂ) (by rw [hnorm]; exact hnR)
      rw [hnorm] at h1
      rw [← hconst 0 ((n : ℝ) : ℂ)] at h1
      have hden : 0 < (n : ℝ) - Rc := by linarith
      have h2 : p.length * max M 0 / ((n : ℝ) - Rc) < ‖G 0‖ := by
        have hXd : p.length * max M 0 / ‖G 0‖ < (n : ℝ) - Rc := by linarith
        rcases eq_or_lt_of_le hX with hX0 | hXpos
        · rw [← hX0]
          simp [hpos]
        · rw [div_lt_iff₀ hden]
          calc p.length * max M 0 = ‖G 0‖ * (p.length * max M 0 / ‖G 0‖) := by
                field_simp
            _ < ‖G 0‖ * ((n : ℝ) - Rc) := mul_lt_mul_of_pos_left hXd hpos
      linarith
    intro a
    rw [hconst a 0, hkey]
  have hzV : z ∈ V := ⟨hz, hzw⟩
  have hzG : walkIntegral (fun w => F w / (w - z)) p.head p.rest = G z := by
    rw [hGdef]
    show walkIntegral (fun w => F w / (w - z)) p.head p.rest
      = if z ∈ V then walkIntegral (fun w => F w / (w - z)) p.head p.rest
        else walkIntegral (fun w => sec F z w) p.head p.rest
    exact (ite_eq_left hzV).symm
  rw [hzG, hzero]

/-! ## Dixon's theorem -/

theorem walkIntegral_eq_zero_of_wind {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) {p : Polygon} (hcl : p.last = p.head) (hpU : p.carrier ⊆ U)
    (hw : ∀ a ∉ U, wind p a = 0) : walkIntegral f p.head p.rest = 0 :=
  walkIntegral_eq_zero_of_cauchyKernel hU hf hcl hpU hw fun _F hF _z hz hzw =>
    polyIntegral_cauchyKernel_eq_zero hU hF hcl hpU hw hz hzw

end QuantumZipper.CA.Homology
