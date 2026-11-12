/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D127C4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3D127C3
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L33M

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D127 N4a, part 4: the domains `confU r δ z T` (packet P-127C)

* `extCorkscrew_confU`: `confU r δ z T` satisfies the exterior corkscrew condition at scales
  `≤ min (δ r) r` (every point of the complement lies in the closed disc `B̄(z, 3r)`, outside the
  open disc `B(z, 4r)`, or in one of the closed squares `confSq (δ r) z k`; each of these
  contains a ball of radius `ρ/4` within `ρ` of the point);
* `integrable_killedGreen` (bounded open `U`): `y ↦ G_U(x, y)` is integrable;
* `integral_killedGreen_confU_le` (**D127 N4(a)** at `confU`) and
  `closure_superlevel_subset_confU` (the superlevel sets of a function dominated by the
  Green potential of a constant have compact closure in `confU`; the form N3 needs).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set
open scoped NNReal ENNReal

namespace LQGMetric
namespace CONF
namespace ZBM

open KilledHeat Blueprint

lemma norm_radial_confU (z p : ℂ) (l : ℝ) :
    ‖(z + (l : ℂ) * (p - z)) - z‖ = |l| * ‖p - z‖ ∧
      ‖(z + (l : ℂ) * (p - z)) - p‖ = |l - 1| * ‖p - z‖ := by
  constructor
  · rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  · rw [show z + (l : ℂ) * (p - z) - p = ((l - 1 : ℝ) : ℂ) * (p - z) by push_cast; ring,
      norm_mul, Complex.norm_real, Real.norm_eq_abs]

/-- **The exterior corkscrew condition for `confU`.** -/
theorem extCorkscrew_confU {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (z : ℂ) (T : Finset (ℤ × ℤ)) :
    ExtCorkscrew (confU r δ z T) (min (δ * r) r) := by
  intro p hp ρ hρ hρL
  have hρδ : ρ ≤ δ * r := hρL.trans (min_le_left _ _)
  have hρr : ρ ≤ r := hρL.trans (min_le_right _ _)
  have hann : ∀ w : ℂ, w ∈ (annulus z (3 * r) (4 * r) : Set ℂ) ↔
      3 * r < ‖w - z‖ ∧ ‖w - z‖ < 4 * r := fun w ↦ Iff.rfl
  by_cases ha : p ∈ (annulus z (3 * r) (4 * r) : Set ℂ)
  · -- `p` lies in a removed closed square
    have hpU : p ∈ ⋃ k ∈ T, confSq (δ * r) z k := by
      by_contra h; exact hp ⟨ha, h⟩
    obtain ⟨k, hk, hpk⟩ := mem_iUnion₂.mp hpU
    set ε := δ * r
    set a := z.re + k.1 * ε
    set b := z.im + k.2 * ε
    obtain ⟨h1, h2, h3, h4⟩ := hpk
    set c : ℂ := ⟨max (a + ρ / 4) (min p.re (a + (k.1 + 1) * ε - k.1 * ε - ρ / 4)),
      max (b + ρ / 4) (min p.im (b + (k.2 + 1) * ε - k.2 * ε - ρ / 4))⟩ with hc
    have hε : (k.1 + 1 : ℝ) * ε - k.1 * ε = ε := by ring
    have hε2 : (k.2 + 1 : ℝ) * ε - k.2 * ε = ε := by ring
    have hre1 : a + ρ / 4 ≤ c.re := le_max_left _ _
    have hre2 : c.re ≤ a + ε - ρ / 4 := by
      simp only [hc]; rw [add_sub_assoc a, hε]
      exact max_le (by linarith) (min_le_right _ _)
    have him1 : b + ρ / 4 ≤ c.im := le_max_left _ _
    have him2 : c.im ≤ b + ε - ρ / 4 := by
      simp only [hc]; rw [add_sub_assoc b, hε2]
      exact max_le (by linarith) (min_le_right _ _)
    have hdre : |c.re - p.re| ≤ ρ / 4 := by
      simp only [hc]; rw [add_sub_assoc a, hε]
      refine abs_le.mpr ⟨?_, ?_⟩
      · have : p.re - ρ / 4 ≤ min p.re (a + ε - ρ / 4) :=
          le_min (by linarith) (by linarith)
        linarith [le_max_right (a + ρ / 4) (min p.re (a + ε - ρ / 4))]
      · have : max (a + ρ / 4) (min p.re (a + ε - ρ / 4)) ≤ p.re + ρ / 4 :=
          max_le (by linarith) ((min_le_left _ _).trans (by linarith))
        linarith
    have hdim : |c.im - p.im| ≤ ρ / 4 := by
      simp only [hc]; rw [add_sub_assoc b, hε2]
      refine abs_le.mpr ⟨?_, ?_⟩
      · have : p.im - ρ / 4 ≤ min p.im (b + ε - ρ / 4) :=
          le_min (by linarith) (by linarith)
        linarith [le_max_right (b + ρ / 4) (min p.im (b + ε - ρ / 4))]
      · have : max (b + ρ / 4) (min p.im (b + ε - ρ / 4)) ≤ p.im + ρ / 4 :=
          max_le (by linarith) ((min_le_left _ _).trans (by linarith))
        linarith
    refine ⟨c, ?_, fun w hw hwU ↦ ?_⟩
    · rw [dist_eq_norm]
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      simp only [Complex.sub_re, Complex.sub_im]
      linarith
    · have hwc : ‖w - c‖ < ρ / 4 := by rw [← dist_eq_norm]; exact mem_ball.mp hw
      have hr1 := (Complex.abs_re_le_norm (w - c)).trans_lt hwc
      have hi1 := (Complex.abs_im_le_norm (w - c)).trans_lt hwc
      simp only [Complex.sub_re, Complex.sub_im] at hr1 hi1
      rw [abs_lt] at hr1 hi1
      refine hwU.2 (mem_iUnion₂.mpr ⟨k, hk, ?_⟩)
      refine ⟨by linarith, ?_, by linarith, ?_⟩
      · have : z.re + (k.1 + 1) * ε = a + ε := by simp only [a]; ring
        rw [this]; linarith
      · have : z.im + (k.2 + 1) * ε = b + ε := by simp only [b]; ring
        rw [this]; linarith
  · -- `p` lies outside the annulus
    rw [hann, not_and_or, not_lt, not_lt] at ha
    have hcompl : ∀ w : ℂ, ¬(3 * r < ‖w - z‖ ∧ ‖w - z‖ < 4 * r) → w ∈ (confU r δ z T)ᶜ :=
      fun w hw hwU ↦ hw hwU.1
    rcases ha with hin | hout
    · by_cases hpz : ‖p - z‖ ≤ ρ
      · refine ⟨z, by rw [dist_comm, dist_eq_norm]; exact hpz, fun w hw ↦ hcompl w ?_⟩
        rw [mem_ball, dist_eq_norm] at hw
        intro h; linarith [h.1]
      · push_neg at hpz
        have hn : 0 < ‖p - z‖ := hρ.trans hpz
        set l : ℝ := 1 - ρ / (2 * ‖p - z‖)
        have hl0 : 0 ≤ l := by
          simp only [l]; rw [sub_nonneg, div_le_one (by positivity)]; linarith
        obtain ⟨hcz, hcp⟩ := norm_radial_confU z p l
        have hcz' : ‖(z + (l : ℂ) * (p - z)) - z‖ = ‖p - z‖ - ρ / 2 := by
          rw [hcz, abs_of_nonneg hl0]; simp only [l]; field_simp
        have hcp' : ‖(z + (l : ℂ) * (p - z)) - p‖ = ρ / 2 := by
          rw [hcp, show l - 1 = -(ρ / (2 * ‖p - z‖)) by simp only [l]; ring, abs_neg,
            abs_of_nonneg (by positivity)]
          field_simp
        refine ⟨z + (l : ℂ) * (p - z), by rw [dist_eq_norm, hcp']; linarith,
          fun w hw ↦ hcompl w ?_⟩
        rw [mem_ball, dist_eq_norm] at hw
        intro h
        have := norm_sub_le_norm_sub_add_norm_sub w (z + (l : ℂ) * (p - z)) z
        linarith [h.1]
    · have hn : 0 < ‖p - z‖ := by linarith
      set l : ℝ := 1 + ρ / (2 * ‖p - z‖)
      have hl0 : 0 ≤ l := by simp only [l]; positivity
      obtain ⟨hcz, hcp⟩ := norm_radial_confU z p l
      have hcz' : ‖(z + (l : ℂ) * (p - z)) - z‖ = ‖p - z‖ + ρ / 2 := by
        rw [hcz, abs_of_nonneg hl0]; simp only [l]; field_simp
      have hcp' : ‖(z + (l : ℂ) * (p - z)) - p‖ = ρ / 2 := by
        rw [hcp, show l - 1 = ρ / (2 * ‖p - z‖) by simp only [l]; ring,
          abs_of_nonneg (by positivity)]
        field_simp
      refine ⟨z + (l : ℂ) * (p - z), by rw [dist_eq_norm, hcp']; linarith,
        fun w hw ↦ hcompl w ?_⟩
      rw [mem_ball, dist_eq_norm] at hw
      intro h
      have := norm_sub_norm_le (z + (l : ℂ) * (p - z) - z) (z + (l : ℂ) * (p - z) - w)
      rw [show z + (l : ℂ) * (p - z) - z - (z + (l : ℂ) * (p - z) - w) = w - z by ring,
        norm_sub_rev (z + (l : ℂ) * (p - z)) w] at this
      linarith [h.2]

lemma confU_subset_ball (r δ : ℝ) (z : ℂ) (T : Finset (ℤ × ℤ)) :
    confU r δ z T ⊆ ball z (4 * r) := fun w hw ↦ by
  rw [mem_ball, dist_eq_norm]; exact hw.1.2

/-- `y ↦ G_U(x, y)` is integrable for bounded open `U` (`∫ G_U(x, ·) = π E^x τ_U < ∞`). -/
theorem integrable_killedGreen {U : Set ℂ} (hU : IsOpen U) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hUR : U ⊆ ball c R) (x : ℂ) : Integrable fun y ↦ killedGreen U x y := by
  have hmeas : StronglyMeasurable fun q : ℂ × ℝ ↦ killedHeat U q.2.toNNReal x q.1 :=
    ((measurable_killedHeat hU).comp ((measurable_real_toNNReal.comp measurable_snd).prodMk
      (measurable_const.prodMk measurable_fst))).stronglyMeasurable
  have hsm : StronglyMeasurable fun y ↦ killedGreen U x y :=
    (hmeas.integral_prod_right' (ν := volume.restrict (Ioi (0 : ℝ)))).const_mul Real.pi
  refine ⟨hsm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun y ↦ killedGreen_nonneg U x y)]
  have h1 : (1 : ℝ≥0) ≠ 0 := one_ne_zero
  refine ((lintegral_killedGreen_le hU x).trans
    (mul_le_mul' le_rfl (lintegral_killedSurv_le hU hR hUR h1 x))).trans_lt ?_
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.mpr
    ⟨ENNReal.ofReal_lt_top, ENNReal.mul_lt_top ?_ ENNReal.ofReal_lt_top⟩)
  exact (killedSurv_le_one U h1 x).trans_lt ENNReal.one_lt_top

/-- **D127 N4(a) at `confU`**: `∫ G_U(x, y) dy → 0` uniformly as `x → ∂U`. -/
theorem integral_killedGreen_confU_le {r δ : ℝ} (hr : 0 < r) (hδ : 0 < δ) (z : ℂ)
    (T : Finset (ℤ × ℤ)) :
    ∀ ε > 0, ∃ η > 0, ∀ x : ℂ, infDist x (confU r δ z T)ᶜ < η →
      ∫ y, killedGreen (confU r δ z T) x y ≤ ε :=
  integral_killedGreen_le_of_corkscrew (isOpen_confU r δ z T) (by positivity)
    (confU_subset_ball r δ z T) (lt_min (by positivity) hr) (extCorkscrew_confU hr hδ z T)

/-- **Compact superlevel sets** (the form D127 N3 needs): if `f ≤ M ∫ G_U(·, y) dy` on `U`
(e.g. `f = G_U ρ` with `|ρ| ≤ M`), then `cl {x ∈ U | ε ≤ f x}` is compact and contained in `U`,
for `U` bounded open with an exterior corkscrew condition. -/
theorem closure_superlevel_subset {U : Set ℂ} (hU : IsOpen U) {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hUR : U ⊆ ball c R) {L : ℝ} (hL : 0 < L) (hcork : ExtCorkscrew U L) {f : ℂ → ℝ} {M : ℝ}
    (hf : ∀ x ∈ U, f x ≤ M * ∫ y, killedGreen U x y) {ε : ℝ} (hε : 0 < ε) :
    IsCompact (closure {x | x ∈ U ∧ ε ≤ f x}) ∧ closure {x | x ∈ U ∧ ε ≤ f x} ⊆ U := by
  set M' := max M 1 with hM'
  have hM'0 : 0 < M' := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨η, hη, hG⟩ := integral_killedGreen_le_of_corkscrew hU hR hUR hL hcork
    (ε / (2 * M')) (by positivity)
  set K : Set ℂ := {x | η ≤ infDist x Uᶜ} ∩ closedBall c R with hK
  have hKc : IsCompact K :=
    (isCompact_closedBall c R).of_isClosed_subset
      ((isClosed_le continuous_const (continuous_infDist_pt _)).inter isClosed_closedBall)
      inter_subset_right
  have hSK : {x | x ∈ U ∧ ε ≤ f x} ⊆ K := by
    rintro x ⟨hxU, hfx⟩
    refine ⟨?_, ball_subset_closedBall (hUR hxU)⟩
    show η ≤ infDist x Uᶜ
    by_contra hlt
    have h1 := hG x (lt_of_not_ge hlt)
    have h2 := hf x hxU
    have hint0 : 0 ≤ ∫ y, killedGreen U x y :=
      integral_nonneg fun y ↦ killedGreen_nonneg U x y
    have : M * ∫ y, killedGreen U x y ≤ M' * (ε / (2 * M')) :=
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hint0).trans
        (mul_le_mul_of_nonneg_left h1 hM'0.le)
    rw [show M' * (ε / (2 * M')) = ε / 2 by field_simp] at this
    linarith
  have hKU : K ⊆ U := fun x hx ↦ by
    by_contra hxU
    have := infDist_zero_of_mem (s := Uᶜ) hxU
    have h1 : η ≤ infDist x Uᶜ := hx.1
    linarith
  have hcl : closure {x | x ∈ U ∧ ε ≤ f x} ⊆ K := closure_minimal hSK hKc.isClosed
  exact ⟨hKc.of_isClosed_subset isClosed_closure hcl, hcl.trans hKU⟩

end ZBM
end CONF
end LQGMetric
