/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Lemma38Source.Admissible at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.Lemma38Source.FiveTests
import LatticeProb.Bonanno.MatedCRTHarmonic.MesoModel.RecAdmissible

/-!
# Source test admissibility for the translated Lemma 3.8 annuli

HADM's recurrence admissibility arguments are centered at zero. Here the domains have
an arbitrary center `z`; the geometric and test-function estimates are separated from
the later uniform mesh margins.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Real
open scoped ENNReal

namespace MatedCRTHarmonic.Lemma38Source

private theorem annulusConnected {z : ℂ} {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    IsConnected (GMS3.annulusSet z a b) := by
  let S : Set (ℝ × ℂ) := Ioo a b ×ˢ sphere (0 : ℂ) 1
  let f : ℝ × ℂ → ℂ := fun p => z + (p.1 : ℂ) * p.2
  have hRank : 1 < Module.rank ℝ ℂ := by
    rw [Complex.rank_real_complex]
    norm_num
  have hS : IsConnected S :=
    (isConnected_Ioo hab).prod
      (isConnected_sphere hRank 0 (by norm_num : 0 ≤ (1 : ℝ)))
  have hf : Continuous f := by fun_prop
  have himage : f '' S = GMS3.annulusSet z a b := by
    ext w
    constructor
    · rintro ⟨⟨t, u⟩, ⟨ht, hu⟩, rfl⟩
      have huNorm : ‖u‖ = 1 := mem_sphere_zero_iff_norm.mp hu
      have htNorm : ‖(t : ℂ)‖ = t := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (lt_trans ha ht.1)]
      change a < ‖z + (t : ℂ) * u - z‖ ∧ ‖z + (t : ℂ) * u - z‖ < b
      simpa only [add_sub_cancel_left, norm_mul, htNorm, huNorm, mul_one, mem_Ioo] using ht
    · intro hw
      have hwne : w - z ≠ 0 := by
        intro h
        have : a < 0 := by simpa only [h, norm_zero] using hw.1
        linarith
      let t : ℝ := ‖w - z‖
      have htpos : 0 < t := norm_pos_iff.mpr hwne
      let u : ℂ := (t : ℂ)⁻¹ * (w - z)
      have hu : u ∈ sphere (0 : ℂ) 1 := by
        rw [mem_sphere_zero_iff_norm]
        dsimp [u]
        rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos htpos]
        exact inv_mul_cancel₀ htpos.ne'
      refine ⟨(t, u), ⟨⟨?_, ?_⟩, hu⟩, ?_⟩
      · exact hw.1
      · exact hw.2
      · dsimp [f, u, t]
        rw [← mul_assoc, mul_inv_cancel₀]
        · simp
        · exact_mod_cast (norm_ne_zero_iff.mpr hwne)
  rw [← himage]
  exact hS.image f hf.continuousOn

private theorem annulusFrontierVolume {z : ℂ} {a b C : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1)
    (hC : 16 * π ≤ C) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    volume (thickening t (frontier (GMS3.annulusSet z a b))) ≤
      ENNReal.ofReal (C * t) := by
  have ht0 : 0 ≤ t := ht.1.le
  have ht1 : t < 1 := ht.2
  have hb0 : 0 ≤ b := ha.trans hab
  have hsub : thickening t (frontier (GMS3.annulusSet z a b)) ⊆
      {u : ℂ | |‖u - z‖ - a| < t} ∪ {u : ℂ | |‖u - z‖ - b| < t} := by
    intro u hu
    obtain ⟨v, hv, huv⟩ := mem_thickening_iff.mp hu
    have hn : |‖u - z‖ - ‖v - z‖| ≤ ‖u - v‖ := by
      simpa only [sub_sub_sub_cancel_right] using
        (abs_norm_sub_norm_le (u - z) (v - z))
    have hd : ‖u - v‖ < t := by simpa only [dist_eq_norm] using huv
    rcases GMS3.frontier_annulusSet_subset z a b hv with h | h
    · left
      have hv' : ‖v - z‖ = a := h
      simpa only [mem_ofPred_eq, hv'] using lt_of_le_of_lt hn hd
    · right
      have hv' : ‖v - z‖ = b := h
      simpa only [mem_ofPred_eq, hv'] using lt_of_le_of_lt hn hd
  calc
    volume (thickening t (frontier (GMS3.annulusSet z a b))) ≤
        volume ({u : ℂ | |‖u - z‖ - a| < t} ∪
          {u : ℂ | |‖u - z‖ - b| < t}) := measure_mono hsub
    _ ≤ volume {u : ℂ | |‖u - z‖ - a| < t} +
        volume {u : ℂ | |‖u - z‖ - b| < t} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (4 * π * t * (a + t)) +
        ENNReal.ofReal (4 * π * t * (b + t)) :=
      add_le_add (GMS3.volume_radialShell_le z ha ht.1.le)
        (GMS3.volume_radialShell_le z (ha.trans hab) ht.1.le)
    _ ≤ ENNReal.ofReal (C * t) := by
      have hp0 : 0 ≤ 4 * π * t * (a + t) := by positivity
      have hp1 : 0 ≤ 4 * π * t * (b + t) := by positivity
      rw [← ENNReal.ofReal_add hp0] <;> try exact hp1
      apply ENNReal.ofReal_le_ofReal
      have hfac : 0 ≤ 4 * π * t := by positivity
      calc
        4 * π * t * (a + t) + 4 * π * t * (b + t) ≤
            4 * π * t * 2 + 4 * π * t * 2 :=
          add_le_add
            (mul_le_mul_of_nonneg_left (by linarith) hfac)
            (mul_le_mul_of_nonneg_left (by linarith) hfac)
        _ = 16 * π * t := by ring
        _ ≤ C * t := mul_le_mul_of_nonneg_right hC ht.1.le

private theorem ballFrontierVolume {z : ℂ} {b C : ℝ}
    (hb : 0 ≤ b) (hb1 : b < 1) (hC : 16 * π ≤ C)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    volume (thickening t (frontier (ball z b))) ≤ ENNReal.ofReal (C * t) := by
  have ht0 : 0 ≤ t := ht.1.le
  have ht1 : t < 1 := ht.2
  have hsub : thickening t (frontier (ball z b)) ⊆
      {u : ℂ | |‖u - z‖ - b| < t} := by
    intro u hu
    obtain ⟨v, hv, huv⟩ := mem_thickening_iff.mp hu
    have hv' : ‖v - z‖ = b := by
      simpa only [mem_sphere_iff_norm] using (frontier_ball_subset_sphere hv)
    have hn : |‖u - z‖ - ‖v - z‖| ≤ ‖u - v‖ := by
      simpa only [sub_sub_sub_cancel_right] using
        (abs_norm_sub_norm_le (u - z) (v - z))
    have hd : ‖u - v‖ < t := by simpa only [dist_eq_norm] using huv
    simpa only [mem_ofPred_eq, hv'] using lt_of_le_of_lt hn hd
  calc
    volume (thickening t (frontier (ball z b))) ≤
        volume {u : ℂ | |‖u - z‖ - b| < t} := measure_mono hsub
    _ ≤ ENNReal.ofReal (4 * π * t * (b + t)) :=
      GMS3.volume_radialShell_le z hb ht.1.le
    _ ≤ ENNReal.ofReal (C * t) := by
      apply ENNReal.ofReal_le_ofReal
      have hfac : 0 ≤ 4 * π * t := by positivity
      calc
        4 * π * t * (b + t) ≤ 4 * π * t * 2 :=
          mul_le_mul_of_nonneg_left (by linarith) hfac
        _ = 8 * π * t := by ring
        _ ≤ C * t := mul_le_mul_of_nonneg_right
          (by nlinarith [Real.pi_pos]) ht.1.le

/-- For Euclidean disks, inclusion of open balls forces the sharp center-plus-radius
inequality. This supplies the spare radius needed by G3 even at tangency. -/
theorem center_add_radius_le_of_ball_subset {z : ℂ} {r ρ : ℝ}
    (hr : 0 < r) (hball : ball z r ⊆ ball (0 : ℂ) ρ) :
    ‖z‖ + r ≤ ρ := by
  have hρ : 0 < ρ := by
    have hz : z ∈ ball z r := by simpa using hr
    have hz' := hball hz
    have : ‖z‖ < ρ := by simpa [Metric.mem_ball, dist_eq_norm] using hz'
    linarith [norm_nonneg z]
  have hclosed : closedBall z r ⊆ closedBall (0 : ℂ) ρ := by
    rw [← closure_ball z hr.ne', ← closure_ball (0 : ℂ) hρ.ne']
    exact closure_mono hball
  by_cases hz : z = 0
  · subst z
    have hu : (r : ℂ) ∈ closedBall (0 : ℂ) r := by
      rw [mem_closedBall, dist_zero_right, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos hr]
    have hu' := hclosed hu
    rw [mem_closedBall, dist_zero_right, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr] at hu'
    simpa using hu'
  · have hzNorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
    let u : ℂ := z + (r / ‖z‖) • z
    have hratio : 0 ≤ r / ‖z‖ := (div_pos hr hzNorm).le
    have hfactor : u = (1 + r / ‖z‖) • z := by
      dsimp [u]
      simp only [Complex.ofReal_add, Complex.ofReal_one]
      ring
    have hnormU : ‖u‖ = ‖z‖ + r := by
      rw [hfactor, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by linarith : 0 ≤ 1 + r / ‖z‖)]
      field_simp
    have hdistU : dist u z = r := by
      rw [dist_eq_norm]
      have heq : u - z = (r / ‖z‖) • z := by simp [u]
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hratio]
      field_simp
    have hu : u ∈ closedBall z r := by
      rw [mem_closedBall]
      exact hdistU.le
    have hu' := hclosed hu
    rw [mem_closedBall, dist_zero_right, hnormU] at hu'
    exact hu'

/-- A fixed fraction of the gap between the requested radius and G4's ambient
radius supplies G3's larger closed ball, uniformly over `z` and `r`. -/
theorem outerBallMargins {z : ℂ} {r ρ rhoG4 δ : ℝ}
    (hr : 0 < r) (hball : ball z r ⊆ ball (0 : ℂ) ρ)
    (hρgap : ρ < rhoG4) (hrho1 : rhoG4 < 1)
    (hδ : δ < (rhoG4 - ρ) / 2) :
    let R₁ := r + (rhoG4 - ρ) / 2
    r + δ < R₁ ∧ r ≤ R₁ ∧ R₁ < 1 ∧
      ball z R₁ ⊆ ball (0 : ℂ) rhoG4 ∧
      closedBall z R₁ ⊆ ball (0 : ℂ) rhoG4 := by
  dsimp
  have hcenter := center_add_radius_le_of_ball_subset hr hball
  have hgap : 0 < (rhoG4 - ρ) / 2 := by linarith
  have hsum : r + (rhoG4 - ρ) / 2 + ‖z‖ < rhoG4 := by linarith
  refine ⟨by linarith, by linarith, by linarith [norm_nonneg z], ?_, ?_⟩
  · apply Metric.ball_subset_ball'
    simpa only [dist_zero_right] using hsum.le
  · intro u hu
    rw [mem_closedBall] at hu
    rw [mem_ball]
    have htri := dist_triangle u z (0 : ℂ)
    simp only [dist_zero_right] at htri ⊢
    linarith

/-- Shifted logarithmic-gradient test, with its two exact numerical margins. -/
theorem annulusSqGrad_admissible {ε a b rho C beta : ℝ} {z : ℂ}
    (hε : 0 < ε) (hε1 : ε < 1) (ha : 0 < a) (hab : a < b)
    (hb1 : b < 1) (hD : GMS3.annulusSet z a b ⊆ ball 0 rho)
    (hrho0 : 0 < rho) (hrho1 : rho < 1) (hC : 16 * π ≤ C) (hbeta : 0 < beta)
    (hM : ((Real.log (b / a)) ^ 2 * a ^ 2)⁻¹ ≤ C * ε ^ (-beta))
    (hL : 2 * ((Real.log (b / a)) ^ 2 * a ^ 3)⁻¹ ≤ C * ε ^ (-beta)) :
    GMS4.Prop210Admissible ε rho C beta (GMS3.annulusSet z a b)
      (fun u => ‖fderiv ℝ (GMS3.logRad z a b) u‖ ^ 2) := by
  have hC1 : 1 < C := by nlinarith [Real.pi_gt_three]
  refine ⟨hε, hε1, hrho0, hrho1, hC1, hbeta,
    GMS3.isOpen_annulusSet z a b, annulusConnected ha hab, hD,
    ?_, ?_, ?_⟩
  · intro t ht
    exact annulusFrontierVolume ha.le hab.le hb1 hC t ht
  · intro u hu
    have hu' : a ≤ ‖u - z‖ := hu.1.le
    have hbound := GMS3.sqGrad_le (z := z) (a := a) (b := b)
      (c := a) ha hu'
    exact ⟨by positivity, hbound.trans hM⟩
  · intro u hu v hv
    have hu' : a ≤ ‖u - z‖ := hu.1.le
    have hv' : a ≤ ‖v - z‖ := hv.1.le
    have hcoef :
        2 * ((Real.log (b / a)) ^ 2 * a ^ 3)⁻¹ * dist u v ≤
          (C * ε ^ (-beta)) * dist u v :=
      mul_le_mul_of_nonneg_right hL dist_nonneg
    have huv := GMS3.sqGrad_le_add (z := z) (a := a) (b := b)
      (c := a) ha hu' hv'
    have hvu := GMS3.sqGrad_le_add (z := z) (a := a) (b := b)
      (c := a) ha hv' hu'
    rw [dist_comm] at hvu
    apply abs_le.mpr
    constructor <;> linarith

/-- Shifted constant test on either Lemma 3.8 annulus. -/
theorem annulusOne_admissible {ε a b rho C beta : ℝ} {z : ℂ}
    (hε : 0 < ε) (hε1 : ε < 1) (ha : 0 < a) (hab : a < b)
    (hb1 : b < 1) (hD : GMS3.annulusSet z a b ⊆ ball 0 rho)
    (hrho0 : 0 < rho) (hrho1 : rho < 1) (hC : 16 * π ≤ C) (hbeta : 0 < beta)
    (hOne : 1 ≤ C * ε ^ (-beta)) :
    GMS4.Prop210Admissible ε rho C beta (GMS3.annulusSet z a b)
      (fun _ => 1) := by
  have hC1 : 1 < C := by nlinarith [Real.pi_gt_three]
  refine ⟨hε, hε1, hrho0, hrho1, hC1, hbeta,
    GMS3.isOpen_annulusSet z a b, annulusConnected ha hab, hD,
    ?_, ?_, ?_⟩
  · intro t ht
    exact annulusFrontierVolume ha.le hab.le hb1 hC t ht
  · intro u hu
    exact ⟨by norm_num, hOne⟩
  · intro u hu v hv
    simp only [sub_self, abs_zero]
    positivity

/-- Shifted two-circle boundary layer on a ball. -/
theorem ballAnnLayer_admissible {ε b a₁ a₂ w rho C beta : ℝ} {z : ℂ}
    (hε : 0 < ε) (hε1 : ε < 1) (hb : 0 < b) (hb1 : b < 1)
    (hD : ball z b ⊆ ball 0 rho)
    (hrho0 : 0 < rho) (hrho1 : rho < 1) (hC : 16 * π ≤ C)
    (hbeta : 0 < beta) (hw : 0 < w)
    (hOne : 1 ≤ C * ε ^ (-beta)) (hLip : w⁻¹ ≤ C * ε ^ (-beta)) :
    GMS4.Prop210Admissible ε rho C beta (ball z b)
      (GMS3.annLayer z a₁ a₂ w) := by
  have hC1 : 1 < C := by nlinarith [Real.pi_gt_three]
  have hLips : LipschitzWith (Real.toNNReal w⁻¹)
      (GMS3.annLayer z a₁ a₂ w) := by
    unfold GMS3.annLayer
    simpa only [max_self] using
      (GMS3.lipschitzWith_radialBump z a₁ hw).max
        (GMS3.lipschitzWith_radialBump z a₂ hw)
  refine ⟨hε, hε1, hrho0, hrho1, hC1, hbeta,
    isOpen_ball, isConnected_ball hb, hD,
    ?_, ?_, ?_⟩
  · intro t ht
    exact ballFrontierVolume hb.le hb1 hC t ht
  · intro u hu
    have hnonneg : 0 ≤ GMS3.annLayer z a₁ a₂ w u := by
      unfold GMS3.annLayer
      exact le_trans (GMS3.radialBump_nonneg z a₁ w u) (le_max_left _ _)
    have hle : GMS3.annLayer z a₁ a₂ w u ≤ 1 := by
      unfold GMS3.annLayer
      exact max_le (GMS3.radialBump_le_one z a₁ w u)
        (GMS3.radialBump_le_one z a₂ w u)
    exact ⟨hnonneg, hle.trans hOne⟩
  · intro u hu v hv
    have hdist := hLips.dist_le_mul u v
    rw [Real.dist_eq, Real.coe_toNNReal _ (inv_nonneg.mpr hw.le)] at hdist
    exact hdist.trans (mul_le_mul_of_nonneg_right hLip dist_nonneg)

/-- All five source pairs are admissible once the geometric containment and
the four explicit test-growth margins hold. -/
theorem fiveAdmissible_of_margins
    {ε ι r R₁ w rho C beta : ℝ} {z : ℂ}
    (hε : 0 < ε) (hε1 : ε < 1) (hι : 0 < ι)
    (h10 : 10 * ι ≤ r) (hR : r ≤ R₁) (hR1 : R₁ < 1)
    (hball : ball z R₁ ⊆ ball 0 rho)
    (hrho0 : 0 < rho) (hrho1 : rho < 1) (hC : 16 * π ≤ C)
    (hbeta : 0 < beta) (hw : 0 < w)
    (hM : ((Real.log (r / ι)) ^ 2 * ι ^ 2)⁻¹ ≤ C * ε ^ (-beta))
    (hL : 2 * ((Real.log (r / ι)) ^ 2 * ι ^ 3)⁻¹ ≤ C * ε ^ (-beta))
    (hOne : 1 ≤ C * ε ^ (-beta)) (hLip : w⁻¹ ≤ C * ε ^ (-beta)) :
    ∀ i : Fin 5, GMS4.Prop210Admissible ε rho C beta
      (fiveDomain z ι r R₁ i) (fiveTest z ι r w i) := by
  have hr : 0 < r := by linarith
  have hr1 : r < 1 := hR.trans_lt hR1
  have hιr : ι < r := by linarith
  have hι2 : 0 < ι / 2 := by positivity
  have h9 : ι / 2 < 9 * ι := by linarith
  have h9r : 9 * ι ≤ r := by linarith
  have h9one : 9 * ι < 1 := h9r.trans_lt hr1
  have hballr : ball z r ⊆ ball 0 rho :=
    (ball_subset_ball hR).trans hball
  have hD1 : GMS3.annulusSet z ι r ⊆ ball 0 rho :=
    (GMS3.annulusSet_subset_ball z ι r).trans hballr
  have hD2 : GMS3.annulusSet z (ι / 2) (9 * ι) ⊆ ball 0 rho :=
    (GMS3.annulusSet_subset_ball z (ι / 2) (9 * ι)).trans
      ((ball_subset_ball h9r).trans hballr)
  intro i
  fin_cases i
  · simpa [fiveDomain, fiveTest] using
      annulusSqGrad_admissible hε hε1 hι hιr hr1 hD1 hrho0 hrho1
        hC hbeta hM hL
  · simpa [fiveDomain, fiveTest] using
      annulusOne_admissible hε hε1 hι hιr hr1 hD1 hrho0 hrho1
        hC hbeta hOne
  · simpa [fiveDomain, fiveTest] using
      ballAnnLayer_admissible hε hε1 (lt_of_lt_of_le hr hR) hR1 hball
        hrho0 hrho1 hC hbeta hw hOne hLip
  · simpa [fiveDomain, fiveTest] using
      annulusOne_admissible hε hε1 hι2 h9 h9one hD2 hrho0 hrho1
        hC hbeta hOne
  · simpa [fiveDomain, fiveTest] using
      ballAnnLayer_admissible hε hε1 hr hr1 hballr hrho0 hrho1
        hC hbeta hw hOne hLip

/-- HADM's inverse-power argument with the Lemma 3.8 inner radius, which is
bounded below by `ε^(2β)` because both `s` and `r` exceed `ε^β`. -/
private theorem invPow_le_of_innerLower {ε ι β betaG4 : ℝ} (n : ℕ)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hinner : ε ^ (2 * β) ≤ ι)
    (hbeta : (n : ℝ) * (2 * β) ≤ betaG4) :
    (ι ^ n)⁻¹ ≤ ε ^ (-betaG4) := by
  have hinnerpos : 0 < ε ^ (2 * β) := Real.rpow_pos_of_pos hε _
  have hpow : (ε ^ (2 * β)) ^ n ≤ ι ^ n :=
    pow_le_pow_left₀ hinnerpos.le hinner n
  have hinv : (ι ^ n)⁻¹ ≤ ((ε ^ (2 * β)) ^ n)⁻¹ :=
    inv_anti₀ (pow_pos hinnerpos n) hpow
  have heq : ((ε ^ (2 * β)) ^ n)⁻¹ = ε ^ (-(n : ℝ) * (2 * β)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le, ← Real.rpow_neg hε.le]
    congr 1
    ring
  calc
    (ι ^ n)⁻¹ ≤ ((ε ^ (2 * β)) ^ n)⁻¹ := hinv
    _ = ε ^ (-(n : ℝ) * (2 * β)) := heq
    _ ≤ ε ^ (-betaG4) :=
      Real.rpow_le_rpow_of_exponent_ge hε hε1 (by linarith)

/-- Uniform source-growth margins for the logarithmic-gradient test. The
first-scale logarithm is bounded below by `log 10`, since `s ≤ 1/10`. -/
theorem gradientMargins {ε s r β betaG4 C : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) (hs : 0 < s) (hs10 : s ≤ 1 / 10)
    (hr : 0 < r) (hslow : ε ^ β ≤ s) (hrlow : ε ^ β ≤ r)
    (hβ : 0 ≤ β)
    (hbeta : 6 * β ≤ betaG4)
    (hC : 2 * ((Real.log 10) ^ 2)⁻¹ ≤ C) :
    ((Real.log (r / (s * r))) ^ 2 * (s * r) ^ 2)⁻¹ ≤
      C * ε ^ (-betaG4) ∧
    2 * ((Real.log (r / (s * r))) ^ 2 * (s * r) ^ 3)⁻¹ ≤
      C * ε ^ (-betaG4) := by
  have hε1' : ε ≤ 1 := hε1.le
  have hpowpos : 0 < ε ^ β := Real.rpow_pos_of_pos hε β
  have hι : 0 < s * r := mul_pos hs hr
  have hinner : ε ^ (2 * β) ≤ s * r := by
    rw [show 2 * β = β + β by ring, Real.rpow_add hε]
    exact mul_le_mul hslow hrlow hpowpos.le hs.le
  have hratio : r / (s * r) = s⁻¹ := by field_simp
  have hsinv : (10 : ℝ) ≤ s⁻¹ := by
    simpa only [show (1 / 10 : ℝ)⁻¹ = 10 by norm_num] using
      (inv_anti₀ hs hs10)
  have hlog0 : 0 < Real.log 10 := Real.log_pos (by norm_num)
  have hlog : Real.log 10 ≤ Real.log (r / (s * r)) := by
    rw [hratio]
    exact Real.log_le_log (by norm_num) hsinv
  have hlogSq : (Real.log 10) ^ 2 ≤ (Real.log (r / (s * r))) ^ 2 := by
    nlinarith
  have hloginv : ((Real.log (r / (s * r))) ^ 2)⁻¹ ≤
      ((Real.log 10) ^ 2)⁻¹ :=
    inv_anti₀ (sq_pos_of_pos hlog0) hlogSq
  have hloginv0 : 0 ≤ ((Real.log 10) ^ 2)⁻¹ := by positivity
  have hC2 : ((Real.log 10) ^ 2)⁻¹ ≤ C := by
    linarith [hloginv0]
  have hpow2 : ((s * r) ^ 2)⁻¹ ≤ ε ^ (-betaG4) :=
    invPow_le_of_innerLower 2 hε hε1' hinner (by norm_num; linarith)
  have hpow3 : ((s * r) ^ 3)⁻¹ ≤ ε ^ (-betaG4) :=
    invPow_le_of_innerLower 3 hε hε1' hinner (by norm_num; linarith)
  constructor
  · calc
      ((Real.log (r / (s * r))) ^ 2 * (s * r) ^ 2)⁻¹ =
          ((Real.log (r / (s * r))) ^ 2)⁻¹ * ((s * r) ^ 2)⁻¹ := by
        rw [mul_inv_rev]
        ring
      _ ≤ ((Real.log 10) ^ 2)⁻¹ * ε ^ (-betaG4) := by
        exact mul_le_mul hloginv hpow2 (by positivity) hloginv0
      _ ≤ C * ε ^ (-betaG4) :=
        mul_le_mul_of_nonneg_right hC2 (Real.rpow_nonneg hε.le _)
  · calc
      2 * ((Real.log (r / (s * r))) ^ 2 * (s * r) ^ 3)⁻¹ =
          2 * (((Real.log (r / (s * r))) ^ 2)⁻¹ * ((s * r) ^ 3)⁻¹) := by
        rw [mul_inv_rev]
        ring
      _ ≤ 2 * (((Real.log 10) ^ 2)⁻¹ * ε ^ (-betaG4)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul hloginv hpow3 (by positivity) hloginv0) (by norm_num)
      _ = (2 * ((Real.log 10) ^ 2)⁻¹) * ε ^ (-betaG4) := by ring
      _ ≤ C * ε ^ (-betaG4) :=
        mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hε.le _)

/-- A clamped representative still lies above the mesh cutoff when that
cutoff is at most `1/10`. -/
theorem representative_lower {k j : ℕ} {β : ℝ}
    (hlow : CellFamily.mesh k ^ β ≤ 1 / 10) :
    CellFamily.mesh k ^ β ≤ MesoModel.annulus38ScaleRepresentative k β j := by
  unfold MesoModel.annulus38ScaleRepresentative
  apply le_min
  have hpow : (1 : ℝ) ≤ (5 / 4 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have hbase : 0 ≤ CellFamily.mesh k ^ β :=
    Real.rpow_nonneg (GMSLemma27.mesh_pos k).le β
  calc
    CellFamily.mesh k ^ β = CellFamily.mesh k ^ β * 1 := by ring
    _ ≤ CellFamily.mesh k ^ β * (5 / 4 : ℝ) ^ j :=
      mul_le_mul_of_nonneg_left hpow hbase
  exact hlow

/-- Uniform admissibility of all five tests, at every positive dyadic mesh
and every clamped representative, from explicit source-scale margins. -/
theorem fiveAdmissible_uniform
    {k : ℕ} (hk : 1 ≤ k) (j : ℕ) (z : ℂ)
    {r R₁ ρG4 C betaG4 β β' : ℝ}
    (hβ : 0 < β) (hlow : CellFamily.mesh k ^ β ≤ 1 / 10)
    (hrlow : CellFamily.mesh k ^ β ≤ r)
    (hR : r ≤ R₁) (hR1 : R₁ < 1)
    (hball : ball z R₁ ⊆ ball 0 ρG4)
    (hρG4 : 0 < ρG4) (hρG41 : ρG4 < 1)
    (hC : 16 * π ≤ C)
    (hClog : 2 * ((Real.log 10) ^ 2)⁻¹ ≤ C)
    (hbetaG4 : 0 < betaG4) (hbeta6 : 6 * β ≤ betaG4)
    (hβ' : β' ≤ betaG4) :
    ∀ i : Fin 5,
      GMS4.Prop210Admissible (CellFamily.mesh k) ρG4 C betaG4
        (fiveDomain z (MesoModel.annulus38ScaleRepresentative k β j * r) r R₁ i)
        (fiveTest z (MesoModel.annulus38ScaleRepresentative k β j * r) r
          (CellFamily.mesh k ^ β') i) := by
  have hε := GMSLemma27.mesh_pos k
  have hε1 := GMSLemma27.mesh_lt_one (by omega : k ≠ 0)
  have hspos : 0 < MesoModel.annulus38ScaleRepresentative k β j := by
    have hbase : 0 < CellFamily.mesh k ^ β := Real.rpow_pos_of_pos hε β
    exact hbase.trans_le (representative_lower hlow)
  have hs10 : MesoModel.annulus38ScaleRepresentative k β j ≤ 1 / 10 := by
    unfold MesoModel.annulus38ScaleRepresentative
    exact min_le_right _ _
  have hrpos : 0 < r := (Real.rpow_pos_of_pos hε β).trans_le hrlow
  have h10 : 10 * (MesoModel.annulus38ScaleRepresentative k β j * r) ≤ r := by
    nlinarith [mul_nonneg (show 0 ≤ 1 - 10 * MesoModel.annulus38ScaleRepresentative k β j
      by linarith) hrpos.le]
  have hw : 0 < CellFamily.mesh k ^ β' := Real.rpow_pos_of_pos hε β'
  have hgrad := gradientMargins hε hε1 hspos hs10 hrpos
    (representative_lower hlow) hrlow hβ.le hbeta6 hClog
  have hC1 : 1 ≤ C := by nlinarith [Real.pi_gt_three]
  have hOneAndLayer := MesoModel.recMeshOneAndLayer hC1 hbetaG4.le hβ'
  exact fiveAdmissible_of_margins hε hε1 (mul_pos hspos hrpos) h10 hR hR1
    hball hρG4 hρG41 hC hbetaG4 hw hgrad.1 hgrad.2
    (hOneAndLayer.1 k hk) (hOneAndLayer.2 k hk)

end MatedCRTHarmonic.Lemma38Source
