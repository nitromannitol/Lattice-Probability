/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.L214Count at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Complex.CircleArcBall
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.KernelBasic
import LatticeProb.Bonanno.QuantumZipper.Proofs.Analysis.Pushforward
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CONF Lemma 2.14, counting half: few arcs have `φ(w_I)` far from `∂U`

Gwynne–Miller, *Confluence of geodesics in Liouville quantum gravity for γ ∈ (0,2)*
(arXiv:1905.00381), Lemma 2.14 (`lem-disconnect-set`, confluence-final.tex 832–894), second
half of the proof (C:873–891): with `B_I := B_{r_I/100}(w_I)` disjoint,

* (2.14) `inf_{B_I} |φ'| ≥ A₀⁻¹ |φ'(w_I)|` and `dist(φ(w_I), ∂U) ≤ A₀ |φ'(w_I)| r_I`
  (Koebe distortion and Koebe 1/4, C:878–881): `confL214_koebe_lower`, `confL214_koebe_dist`;
* `area(U) = ∫_𝔻 |φ'|² ≥ A₀⁻² Σ_I |φ'(w_I)|² π r_I²/100²` (C:883–887);
* Chebyshev (2.15): `#{I : dist(φ(w_I), ∂U) ≥ t} · t² ≤ A · area(U)` (C:889–891):
  `confL214_count`.

Sources reused: Koebe distortion `QuantumZipper.CA.Koebe.distortion_le_norm_deriv`
(Garnett–Marshall Thm I.4.5, non-sharp exponent `koebeDistExp`); the upper bound
`dist(φ(w), ∂U) ≤ (1 − |w|²)|φ'(w)|` is `QuantumZipper.CA.Kernel.infDist_compl_le_schwarzPick`
(Schwarz lemma; CONF cites Koebe 1/4 for it, either works); the area formula is
`QuantumZipper.lintegral_comp_holo` (change of variables, `|det Dφ| = |φ'|²`).

Here `U = φ(𝔻)` for an injective holomorphic `φ` on `𝔻`, distances to `∂U` are
`infDist · Uᶜ` (equal to `dist(·, ∂U)` for points of `U`), and the arc `φ⁻¹(I)` is
`circArc (θ I) (ℓ I)` with `r_I = ℓ I ≤ π/4` (CONF reduces to this case, C:855).
-/

namespace LQGMetric
namespace CONF

open Set Metric Complex MeasureTheory
open scoped ENNReal

/-- `A₀⁻¹ = (99/100)^p`, `p = koebeDistExp`: the distortion factor on `B_{r/100}(w)` relative to
`B_r(w) ⊆ 𝔻`. -/
noncomputable def confL214Kappa : ℝ := (99 / 100 : ℝ) ^ QuantumZipper.CA.Koebe.koebeDistExp

theorem confL214Kappa_pos : 0 < confL214Kappa := Real.rpow_pos_of_pos (by norm_num) _

/-- The constant `A` of (2.15): `#{I : dist(φ(w_I), ∂U) ≥ t} · t² ≤ A · area(U)`. -/
noncomputable def confL214CountConst : ℝ := (Real.pi * confL214Kappa ^ 2 / (4 * 100 ^ 2))⁻¹

theorem confL214CountConst_pos : 0 < confL214CountConst := by
  have := confL214Kappa_pos
  unfold confL214CountConst; have := Real.pi_pos; positivity

theorem ball_arcPt_subset {θ ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) :
    ball (arcPt θ ℓ) ℓ ⊆ ball (0 : ℂ) 1 := by
  intro z hz
  rw [mem_ball_zero_iff]
  have h1 := norm_arcPt (θ := θ) hℓ1
  have h2 : ‖z - arcPt θ ℓ‖ < ℓ := by rw [← dist_eq_norm]; exact mem_ball.1 hz
  have := norm_le_norm_add_norm_sub' z (arcPt θ ℓ)
  linarith

/-- **CONF (2.14), first inequality** (C:878–880, Koebe distortion): on `B_{ℓ/100}(w_I)`,
`|φ'| ≥ κ |φ'(w_I)|`. -/
theorem confL214_koebe_lower {φ : ℂ → ℂ} (hd : DifferentiableOn ℂ φ (ball 0 1))
    (hinj : InjOn φ (ball 0 1)) {θ ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) {z : ℂ}
    (hz : z ∈ ball (arcPt θ ℓ) (ℓ / 100)) :
    confL214Kappa * ‖deriv φ (arcPt θ ℓ)‖ ≤ ‖deriv φ z‖ := by
  have hsub := ball_arcPt_subset (θ := θ) hℓ hℓ1
  have hz' : z ∈ ball (arcPt θ ℓ) ℓ := ball_subset_ball (by linarith) hz
  have h := QuantumZipper.CA.Koebe.distortion_le_norm_deriv (hd.mono hsub) (hinj.mono hsub) hz'
  refine le_trans ?_ h
  rw [mul_comm]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.rpow_le_rpow (by norm_num) _ QuantumZipper.CA.Koebe.koebeDistExp_pos.le
  have : dist z (arcPt θ ℓ) / ℓ ≤ 1 / 100 := by
    rw [div_le_iff₀ hℓ]; have := mem_ball.1 hz; linarith
  linarith

/-- **CONF (2.14), second inequality** (C:878–880): `dist(φ(w_I), ∂U) ≤ 2 ℓ |φ'(w_I)|`
(Schwarz lemma bound `(1 − |w|²)|φ'(w)|`, QZ `infDist_compl_le_schwarzPick`). -/
theorem confL214_koebe_dist {φ : ℂ → ℂ} (hd : DifferentiableOn ℂ φ (ball 0 1))
    (hinj : InjOn φ (ball 0 1)) {θ ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) :
    infDist (φ (arcPt θ ℓ)) (φ '' ball 0 1)ᶜ ≤ 2 * ℓ * ‖deriv φ (arcPt θ ℓ)‖ := by
  have hw : arcPt θ ℓ ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff, norm_arcPt hℓ1]; linarith
  refine (QuantumZipper.CA.Kernel.infDist_compl_le_schwarzPick hd hinj hw).trans ?_
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  rw [norm_arcPt hℓ1]; nlinarith

/-- One ball's contribution to `∫_𝔻 |φ'|²` (C:883–887): if `dist(φ(w_I), ∂U) ≥ t ≥ 0` then
`∫_{B_I} |φ'|² ≥ π κ² t² / (4·100²)`. -/
theorem confL214_ball_integral {φ : ℂ → ℂ} (hd : DifferentiableOn ℂ φ (ball 0 1))
    (hinj : InjOn φ (ball 0 1)) {θ ℓ : ℝ} (hℓ : 0 < ℓ) (hℓ1 : ℓ ≤ 1) {t : ℝ} (ht : 0 ≤ t)
    (htd : t ≤ infDist (φ (arcPt θ ℓ)) (φ '' ball 0 1)ᶜ) :
    ENNReal.ofReal (Real.pi * confL214Kappa ^ 2 / (4 * 100 ^ 2) * t ^ 2) ≤
      ∫⁻ z in ball (arcPt θ ℓ) (ℓ / 100), ENNReal.ofReal (‖deriv φ z‖ ^ 2) := by
  set D := ‖deriv φ (arcPt θ ℓ)‖ with hD
  have hk := confL214Kappa_pos
  have hmono : ∫⁻ _ in ball (arcPt θ ℓ) (ℓ / 100), ENNReal.ofReal ((confL214Kappa * D) ^ 2) ≤
      ∫⁻ z in ball (arcPt θ ℓ) (ℓ / 100), ENNReal.ofReal (‖deriv φ z‖ ^ 2) := by
    apply setLIntegral_mono' measurableSet_ball
    intro z hz
    apply ENNReal.ofReal_le_ofReal
    have := confL214_koebe_lower hd hinj hℓ hℓ1 hz
    have h0 : 0 ≤ confL214Kappa * D := by positivity
    exact pow_le_pow_left₀ h0 this 2
  refine le_trans ?_ hmono
  rw [setLIntegral_const, Complex.volume_ball, ← ENNReal.ofReal_pow (by positivity),
    ← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal.symm, NNReal.coe_real_pi,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have h2 : t ≤ 2 * ℓ * D := htd.trans (confL214_koebe_dist hd hinj hℓ hℓ1)
  have h3 : t ^ 2 ≤ (2 * ℓ * D) ^ 2 := pow_le_pow_left₀ ht h2 2
  have hpi := Real.pi_pos
  have hc : 0 ≤ Real.pi * confL214Kappa ^ 2 / (4 * 100 ^ 2) := by positivity
  calc Real.pi * confL214Kappa ^ 2 / (4 * 100 ^ 2) * t ^ 2
      ≤ Real.pi * confL214Kappa ^ 2 / (4 * 100 ^ 2) * (2 * ℓ * D) ^ 2 :=
        mul_le_mul_of_nonneg_left h3 hc
    _ = (confL214Kappa * D) ^ 2 * ((ℓ / 100) ^ 2 * Real.pi) := by ring

/-- **CONF Lemma 2.14, (2.15)** (C:883–891): for an injective holomorphic `φ` on `𝔻`, finitely
many arcs `circArc (θ i) (ℓ i)` of `∂𝔻` with `0 < ℓ i ≤ π/4` and pairwise disjoint interiors, and
`t > 0`, `#{i : dist(φ(w_i), ∂U) ≥ t} · t² ≤ A · area(U)` with `U = φ(𝔻)`, `w_i = arcPt`, and
`A = confL214CountConst` universal. -/
theorem confL214_count {ι : Type*} (s : Finset ι) (θ ℓ : ι → ℝ) {φ : ℂ → ℂ}
    (hd : DifferentiableOn ℂ φ (ball 0 1)) (hinj : InjOn φ (ball 0 1))
    (hℓ : ∀ i ∈ s, 0 < ℓ i ∧ ℓ i ≤ Real.pi / 4)
    (hdisj : (s : Set ι).PairwiseDisjoint fun i => circArcOpen (θ i) (ℓ i)) {t : ℝ}
    (ht : 0 < t) :
    ((s.filter fun i => t ≤ infDist (φ (arcPt (θ i) (ℓ i))) (φ '' ball 0 1)ᶜ).card : ℝ≥0∞) *
        ENNReal.ofReal (t ^ 2) ≤
      ENNReal.ofReal confL214CountConst * volume (φ '' ball 0 1) := by
  have hpi := Real.pi_gt_three
  set c : ℝ := Real.pi * confL214Kappa ^ 2 / (4 * 100 ^ 2) with hc
  have hk := confL214Kappa_pos
  have hc0 : 0 < c := by positivity
  set s' := s.filter fun i => t ≤ infDist (φ (arcPt (θ i) (ℓ i))) (φ '' ball 0 1)ᶜ with hs'
  set B : ι → Set ℂ := fun i => ball (arcPt (θ i) (ℓ i)) (ℓ i / 100) with hB
  have hℓ' : ∀ i ∈ s', 0 < ℓ i ∧ ℓ i ≤ 1 := fun i hi => by
    have := hℓ i (Finset.mem_filter.1 hi).1; exact ⟨this.1, by linarith [this.2, Real.pi_le_four]⟩
  have hBdisj : (s' : Set ι).PairwiseDisjoint B := by
    intro i hi j hj hij
    have hi' := (Finset.mem_filter.1 hi).1
    have hj' := (Finset.mem_filter.1 hj).1
    exact disjoint_ball_arcPt (hℓ i hi').1 (hℓ i hi').2 (hℓ j hj').1 (hℓ j hj').2
      (hdisj hi' hj' hij)
  have hBsub : (⋃ i ∈ s', B i) ⊆ ball (0 : ℂ) 1 := by
    refine iUnion₂_subset fun i hi => ?_
    exact (ball_subset_ball (by linarith [(hℓ' i hi).1])).trans
      (ball_arcPt_subset (hℓ' i hi).1 (hℓ' i hi).2)
  have hmeas : MeasurableSet (⋃ i ∈ s', B i) :=
    Finset.measurableSet_biUnion _ fun i _ => measurableSet_ball
  have hderiv : ∀ z ∈ ball (0 : ℂ) 1, deriv φ z ≠ 0 := fun z hz =>
    QuantumZipper.CA.Koebe.deriv_ne_zero_of_injOn isOpen_ball hd hinj hz
  have harea := QuantumZipper.lintegral_comp_holo isOpen_ball hd hinj hderiv hmeas hBsub
    (fun _ => 1)
  simp only [mul_one, lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    one_mul] at harea
  -- `#s' · c t² ≤ Σ_{s'} ∫_{B_i} |φ'|² = ∫_{⋃ B_i} |φ'|² = area(φ(⋃ B_i)) ≤ area(U)`
  have hsum : (s'.card : ℝ≥0∞) * ENNReal.ofReal (c * t ^ 2) ≤ volume (φ '' ball 0 1) := by
    calc (s'.card : ℝ≥0∞) * ENNReal.ofReal (c * t ^ 2)
        = ∑ _i ∈ s', ENNReal.ofReal (c * t ^ 2) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ i ∈ s', ∫⁻ z in B i, ENNReal.ofReal (‖deriv φ z‖ ^ 2) := by
          refine Finset.sum_le_sum fun i hi => ?_
          exact confL214_ball_integral hd hinj (hℓ' i hi).1 (hℓ' i hi).2 ht.le
            (Finset.mem_filter.1 hi).2
      _ = ∫⁻ z in ⋃ i ∈ s', B i, ENNReal.ofReal (‖deriv φ z‖ ^ 2) :=
          (lintegral_biUnion_finset hBdisj (fun i _ => measurableSet_ball) _).symm
      _ = volume (φ '' ⋃ i ∈ s', B i) := harea.symm
      _ ≤ volume (φ '' ball 0 1) := measure_mono (image_mono hBsub)
  have hconst : ENNReal.ofReal confL214CountConst * ENNReal.ofReal (c * t ^ 2) =
      ENNReal.ofReal (t ^ 2) := by
    rw [← ENNReal.ofReal_mul confL214CountConst_pos.le, confL214CountConst, ← hc, ← mul_assoc,
      inv_mul_cancel₀ hc0.ne', one_mul]
  calc (s'.card : ℝ≥0∞) * ENNReal.ofReal (t ^ 2)
      = ENNReal.ofReal confL214CountConst * ((s'.card : ℝ≥0∞) * ENNReal.ofReal (c * t ^ 2)) := by
        rw [← hconst]; ring
    _ ≤ ENNReal.ofReal confL214CountConst * volume (φ '' ball 0 1) := by gcongr

/-- Variant of `confL214_long_arcs` with any threshold `ℓ₀ ∈ (0, π/4]`:
`#{i : ℓ i ≥ ℓ₀} ≤ (100/ℓ₀)²` (used with `ℓ₀ = 1/10`, the range of `l214_minorant`). -/
theorem confL214_long_arcs_of_le {ι : Type*} (s : Finset ι) (θ ℓ : ι → ℝ)
    {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀) (hℓ₀' : ℓ₀ ≤ Real.pi / 4) (hℓ : ∀ i ∈ s, ℓ₀ ≤ ℓ i)
    (hdisj : (s : Set ι).PairwiseDisjoint fun i => circArcOpen (θ i) (ℓ i)) :
    (s.card : ℝ) ≤ (100 / ℓ₀) ^ 2 := by
  have hpi := Real.pi_pos
  have hpi4 := Real.pi_le_four
  set r : ℝ := ℓ₀ / 100 with hr
  have hr0 : 0 < r := by positivity
  set B : ι → Set ℂ := fun i => ball (arcPt (θ i) ℓ₀) r with hB
  have hsub : ∀ i ∈ s, circArcOpen (θ i) ℓ₀ ⊆ circArcOpen (θ i) (ℓ i) :=
    fun i hi => image_mono (Ioo_subset_Ioo_right (by linarith [hℓ i hi]))
  have hBdisj : (s : Set ι).PairwiseDisjoint B := by
    intro i hi j hj hij
    exact disjoint_ball_arcPt hℓ₀ hℓ₀' hℓ₀ hℓ₀'
      ((hdisj hi hj hij).mono (hsub i hi) (hsub j hj))
  have hBsub : (⋃ i ∈ s, B i) ⊆ ball (0 : ℂ) 1 := by
    refine iUnion₂_subset fun i _ => ?_
    exact (ball_subset_ball (by rw [hr]; linarith)).trans
      (ball_arcPt_subset hℓ₀ (by linarith))
  have hvol := measure_mono (μ := volume) hBsub
  rw [measure_biUnion_finset hBdisj (fun i _ => measurableSet_ball)] at hvol
  simp only [hB, Complex.volume_ball, Finset.sum_const, nsmul_eq_mul] at hvol
  have hpiE : ((NNReal.pi : NNReal) : ℝ≥0∞) = ENNReal.ofReal Real.pi := by
    rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_real_pi]
  rw [hpiE, ← ENNReal.ofReal_pow hr0.le, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_one, one_pow,
    one_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_le_ofReal_iff hpi.le] at hvol
  have h1 : (s.card : ℝ) * r ^ 2 ≤ 1 := by
    have : (s.card : ℝ) * (r ^ 2 * Real.pi) = ((s.card : ℝ) * r ^ 2) * Real.pi := by ring
    rw [this] at hvol
    exact (mul_le_iff_le_one_left hpi).1 hvol
  have h2 : (100 / ℓ₀) ^ 2 = 1 / r ^ 2 := by rw [hr]; field_simp
  rw [h2, le_div_iff₀ (by positivity)]
  exact h1

end CONF
end LQGMetric
