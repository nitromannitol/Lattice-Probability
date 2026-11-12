/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L3_19ProofMom at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_19Proof
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P3_9Trans

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 3.19, step 2: Prop 3.9 at every centre (general probability space)

DFGPS T:2282–2283 apply "Proposition 3.9 (with `ε𝕣` in place of `𝕣`)" at the centre `z`. Prop 3.9
(`Prop3_9`) is stated at the centre `0`; as in `P3_9Trans.diam_square_tail` we move it to `z`
with the field `T_z h = h(· + z) − h_1(z)` (Axiom IV′ and Axiom III, `ae_transField_ident`),
here on an arbitrary probability space.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS
open Blueprint

namespace L319

variable {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ} {Ω : Type} [MeasurableSpace Ω]
  {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}

/-- `ae_transField_ident` on an arbitrary probability space -/
lemma ae_transField (hD : IsWeakLQGMetric γ D c) (hh : IsWholePlaneGFF h P) (z : ℂ) {r : ℝ}
    (hr : 0 < r) :
    ∀ᵐ ω ∂P, (∀ u v, (D (transField z (h ω))).1 (u, v) =
        Real.exp (-(xiGamma γ * circleAvg (h ω) 1 z)) * (D (h ω)).1 (u + z, v + z)) ∧
      circleAvg (transField z (h ω)) r 0 = circleAvg (h ω) r z - circleAvg (h ω) 1 z := by
  have hw : IsWholePlaneGFF (fun ω => affineComp 1 z (h ω)) P := hh.affineComp one_pos z
  filter_upwards [hD.translation P h (GM.Tight.isGFFPlusCont_of_wp hh) z,
    hD.ae_dist_addConst (GM.Tight.isGFFPlusCont_of_wp hw),
    CircleAvg.ae_circleAvg_addConst hw 0 hr] with ω h1 h2 h3
  refine ⟨fun u v => ?_, ?_⟩
  · rw [transField, h2, mul_neg]
    exact congrArg _ (h1 u v)
  · rw [transField, h3, GM.Tight.circleAvg_affineComp_one, sub_eq_add_neg]

lemma isNormalized_transField (hh : IsWholePlaneGFF h P) (z : ℂ) :
    IsNormalizedWPGFF (fun ω => transField z (h ω)) P := by
  refine ⟨(hh.affineComp one_pos z).addConst
    ((measurable_circleAvg_left 1 z).comp hh.measurable).neg, ?_⟩
  have hw : IsWholePlaneGFF (fun ω => affineComp 1 z (h ω)) P := hh.affineComp one_pos z
  filter_upwards [CircleAvg.ae_circleAvg_addConst hw 0 one_pos] with ω h3
  rw [transField, h3, GM.Tight.circleAvg_affineComp_one, add_neg_cancel]

lemma scaleSet_ball (ρ : ℝ) (hρ : 0 < ρ) (z : ℂ) : scaleSet ρ z (ball 0 1) = ball z ρ := by
  ext x
  simp only [scaleSet, mem_image, mem_ball, dist_eq_norm, sub_zero]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [add_sub_cancel_right, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ]
    nlinarith [norm_nonneg y]
  · intro hx
    refine ⟨(x - z) / ρ, ?_, ?_⟩
    · rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ, div_lt_one hρ]
      exact hx
    · have : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hρ.ne'
      field_simp
      ring

lemma ball_subset_scaleSet (ρ : ℝ) (hρ : 0 < ρ) (z : ℂ) :
    ball z (ρ / 2) ⊆ scaleSet ρ z (closedBall 0 (1 / 2)) := by
  intro x hx
  rw [mem_ball, dist_eq_norm] at hx
  refine ⟨(x - z) / ρ, ?_, ?_⟩
  · rw [mem_closedBall, dist_zero_right, norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hρ, div_le_iff₀ hρ]
    linarith
  · have : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hρ.ne'
    show (ρ : ℂ) * ((x - z) / ρ) + z = x
    field_simp
    ring

/-- **Prop 3.9 at the centre `z`** (T:2282): uniform moments of
`𝔠_ρ⁻¹ e^{−ξ h_ρ(z)} diam(B_{ρ/2}(z); B_ρ(z))`. -/
theorem moment_ball (h39 : Prop3_9) (hγ0 : 0 < γ) (hγ2 : γ < 2) (hD : IsWeakLQGMetric γ D c)
    {p : ℝ} (hp0 : 0 ≤ p) (hp : p < 4 * dGamma γ / γ ^ 2) :
    ∃ C : ℝ, ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsNormalizedWPGFF h P → ∀ ρ : ℝ, 0 < ρ → ∀ z : ℂ,
        ∫⁻ ω, (ENNReal.ofReal (scaleFac (xiGamma γ) c (h ω) ρ z)⁻¹ *
          internalDiam (D (h ω)) (ball z (ρ / 2)) (ball z ρ)) ^ p ∂P ≤ ENNReal.ofReal C := by
  have hnot : ¬ (closedBall (0 : ℂ) (1 / 2)).Subsingleton := fun hs => by
    have := hs (mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 1 / 2))
      (show ((1 / 2 : ℝ) : ℂ) ∈ closedBall (0 : ℂ) (1 / 2) by
        rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]; norm_num)
    norm_num at this
  obtain ⟨C, hC⟩ := h39 γ hγ0 hγ2 D c hD (ball 0 1) (closedBall 0 (1 / 2)) isOpen_ball
    (isCompact_closedBall _ _) ((convex_closedBall _ _).isConnected
      (nonempty_closedBall.2 (by norm_num))) (closedBall_subset_ball (by norm_num)) hnot p hp
  refine ⟨C, fun P _ h hh ρ hρ z => ?_⟩
  refine le_trans (lintegral_mono_ae ?_) (hC P (fun ω => transField z (h ω))
    (isNormalized_transField hh.1 z) ρ hρ)
  filter_upwards [ae_transField hD hh.1 z hρ] with ω ⟨hd1, hd2⟩
  refine ENNReal.rpow_le_rpow ?_ hp0
  set e := Real.exp (-(xiGamma γ * circleAvg (h ω) 1 z)) with he_def
  have he : 0 < e := Real.exp_pos _
  have hS : scaleFac (xiGamma γ) c (transField z (h ω)) ρ 0 =
      e * scaleFac (xiGamma γ) c (h ω) ρ z := by
    unfold scaleFac
    rw [hd2, mul_sub, sub_eq_add_neg, Real.exp_add, he_def]
    ring
  have hX : internalDiam (D (transField z (h ω))) (scaleSet ρ 0 (closedBall 0 (1 / 2)))
      (scaleSet ρ 0 (ball 0 1)) = ENNReal.ofReal e *
        internalDiam (D (h ω)) (scaleSet ρ z (closedBall 0 (1 / 2))) (ball z ρ) := by
    rw [scaleSet_zero_eq_image ρ z, scaleSet_zero_eq_image ρ z, ← scaleSet_ball ρ hρ z]
    exact internalDiam_transl_smul he z hd1 _ _
  have hs : 0 < scaleFac (xiGamma γ) c (h ω) ρ z :=
    mul_pos (hD.tightness.1 ρ hρ) (Real.exp_pos _)
  have hk : ENNReal.ofReal (e * scaleFac (xiGamma γ) c (h ω) ρ z)⁻¹ * ENNReal.ofReal e =
      ENNReal.ofReal (scaleFac (xiGamma γ) c (h ω) ρ z)⁻¹ := by
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    field_simp
  rw [hS, hX, ← mul_assoc, hk]
  gcongr
  exact iSup₂_le fun u hu => iSup₂_le fun v hv =>
    le_iSup₂_of_le u (ball_subset_scaleSet ρ hρ z hu)
      (le_iSup₂_of_le v (ball_subset_scaleSet ρ hρ z hv) le_rfl)

end L319
end LQGMetric.DFGPS
