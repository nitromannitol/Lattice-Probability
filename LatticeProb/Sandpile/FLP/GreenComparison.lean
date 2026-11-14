import LatticeProb.Sandpile.FLP.Basic
import LatticeProb.Walk.PotentialKernel
import LatticeProb.Walk.ExteriorDirichlet
import LatticeProb.Walk.GreenAsymptotic
import LatticeProb.Network.Dirichlet

/-!
# Green functions for sandpile comparisons

The Green function and planar potential kernel satisfy the lattice Poisson equation and
provide uniformly bounded comparisons near the boundary of a Euclidean ball.
-/

namespace LatticeProb.Sandpile.FLP
open LatticeProb MeasureTheory

private theorem omegaD_two : omegaD 2 = Real.pi := by
  simp [omegaD, EuclideanSpace.volume_ball_fin_two, Real.pi_nonneg]

private noncomputable def ballBound (d : ℕ) (g : Site d → ℝ) (R : ℝ) : ℝ :=
  ∑ x ∈ ballFinset d R, |g x|

private theorem ballBound_nonneg (d : ℕ) (g : Site d → ℝ) (R : ℝ) :
    0 ≤ ballBound d g R := by
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

private theorem abs_le_ballBound (d : ℕ) (g : Site d → ℝ) (R : ℝ) (x : Site d)
    (hx : euclidNorm x ≤ R) : |g x| ≤ ballBound d g R := by
  apply Finset.single_le_sum (fun y _ => abs_nonneg (g y))
  exact mem_ballFinset_iff.mpr hx


private theorem small_mass_lower (d : ℕ) (g : Site d → ℝ) (C M R : ℝ)
    (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hg : ∀ x, -C * (1 + euclidNorm x) ≤ g x)
    (m : ℝ) (hm : 0 ≤ m) (hmM : m ≤ M) (p x : Site d) (hp : euclidNorm p ≤ R) :
    -(M * C + (M * C) ^ 2 + R ^ 2 + M * ballBound d g R) ≤
      euclidNorm x ^ 2 + m * g x - (euclidNorm p ^ 2 + m * g p) := by
  have hx0 := euclidNorm_nonneg x
  have hp0 := euclidNorm_nonneg p
  have hnorm := abs_le_ballBound d g R p hp
  have hbp := ballBound_nonneg d g R
  have hgp : g p ≤ ballBound d g R := (le_abs_self _).trans hnorm
  have hgx := hg x
  have hcx : 0 ≤ C * (1 + euclidNorm x) := by positivity
  have hmain : -(M * (C * (1 + euclidNorm x))) ≤ m * g x := by
    calc
      -(M * (C * (1 + euclidNorm x))) ≤ -(m * (C * (1 + euclidNorm x))) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hmM) hcx]
      _ = m * (-C * (1 + euclidNorm x)) := by ring
      _ ≤ m * g x := mul_le_mul_of_nonneg_left hgx hm
  have htop : m * g p ≤ M * ballBound d g R := by
    calc
      m * g p ≤ m * ballBound d g R := mul_le_mul_of_nonneg_left hgp hm
      _ ≤ M * ballBound d g R := mul_le_mul_of_nonneg_right hmM hbp
  have hp2 : euclidNorm p ^ 2 ≤ R ^ 2 := by nlinarith
  have hsq := sq_nonneg (euclidNorm x - M * C)
  nlinarith


private theorem small_mass_upper (d : ℕ) (g : Site d → ℝ) (M R : ℝ)
    (hR : 0 ≤ R) (m : ℝ) (hm : 0 ≤ m) (hmM : m ≤ M) (p x : Site d)
    (hp : euclidNorm p ≤ R) (hx : euclidNorm x ≤ R) :
    euclidNorm x ^ 2 + m * g x - (euclidNorm p ^ 2 + m * g p) ≤
      R ^ 2 + 2 * M * ballBound d g R := by
  have hx0 := euclidNorm_nonneg x
  have hboundx := abs_le_ballBound d g R x hx
  have hboundp := abs_le_ballBound d g R p hp
  have hB := ballBound_nonneg d g R
  have h1 : g x ≤ ballBound d g R := (le_abs_self _).trans hboundx
  have h2 : -ballBound d g R ≤ g p := by
    have := neg_abs_le (g p)
    linarith
  have ha : m * g x ≤ M * ballBound d g R :=
    (mul_le_mul_of_nonneg_left h1 hm).trans (mul_le_mul_of_nonneg_right hmM hB)
  have hb : -(M * ballBound d g R) ≤ m * g p := by
    calc
      -(M * ballBound d g R) ≤ -(m * ballBound d g R) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hmM) hB]
      _ = m * (-ballBound d g R) := by ring
      _ ≤ m * g p := mul_le_mul_of_nonneg_left h2 hm
  have hs : euclidNorm x ^ 2 ≤ R ^ 2 := by nlinarith
  nlinarith [sq_nonneg (euclidNorm p)]


private theorem potentialKernel_linear_lower :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Site 2, -C * (1 + euclidNorm x) ≤ -potentialKernel x := by
  obtain ⟨κ, D, R, hR, h⟩ := exists_abs_potentialKernel_sub_log_le
  let C := 2 / Real.pi + |κ| + |D| + ballBound 2 (fun x => -potentialKernel x) R + 1
  have hc0 : 0 ≤ 2 / Real.pi := by positivity
  have hc : 0 ≤ C := by
    dsimp [C]
    have := ballBound_nonneg 2 (fun x => -potentialKernel x) R
    positivity
  refine ⟨C, hc, fun x => ?_⟩
  have hu := euclidNorm_nonneg x
  by_cases hx : R ≤ euclidNorm x
  · have hu1 : 1 ≤ euclidNorm x := le_trans hR hx
    have hlog := Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one hu1)
    have hp0 : 0 ≤ euclidNorm x ^ (-2 : ℝ) := Real.rpow_nonneg (le_of_lt (lt_of_lt_of_le zero_lt_one hu1)) _
    have hp1 : euclidNorm x ^ (-2 : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hu1 (by norm_num)
    have hpow : D * euclidNorm x ^ (-2 : ℝ) ≤ |D| := by
      have h1 := mul_le_mul_of_nonneg_right (le_abs_self D) hp0
      have h2 := mul_le_mul_of_nonneg_left hp1 (abs_nonneg D)
      linarith
    have hasym := (le_abs_self (potentialKernel x -
      (2 / Real.pi * Real.log (euclidNorm x) + κ))).trans (h x hx)
    have hcoeff := mul_le_mul_of_nonneg_left hlog hc0
    have hB := ballBound_nonneg 2 (fun x => -potentialKernel x) R
    dsimp [C]
    nlinarith [abs_nonneg κ, abs_nonneg D, le_abs_self κ,
      mul_nonneg (abs_nonneg κ) hu, mul_nonneg (abs_nonneg D) hu, mul_nonneg hB hu]
  · have hxR : euclidNorm x ≤ R := le_of_lt (lt_of_not_ge hx)
    have hsmall := abs_le_ballBound 2 (fun x => -potentialKernel x) R x hxR
    have hlower := neg_abs_le (-potentialKernel x)
    have hB := ballBound_nonneg 2 (fun x => -potentialKernel x) R
    dsimp [C]
    nlinarith [abs_nonneg κ, abs_nonneg D, mul_nonneg hc0 hu,
      mul_nonneg (abs_nonneg κ) hu, mul_nonneg (abs_nonneg D) hu, mul_nonneg hB hu]


private theorem small_radius_comparison (d : ℕ) (g : Site d → ℝ) (R C : ℝ)
    (hR : 1 ≤ R) (hC : 0 ≤ C)
    (hg : ∀ x, -C * (1 + euclidNorm x) ≤ g x) :
    ∃ a : ℝ, ∀ K : ℝ, ∃ D : ℝ, ∀ r : ℝ, 1 ≤ r → r ≤ R → ∀ p x : Site d,
      |euclidNorm p - r| ≤ 1 →
      -a ≤ euclidNorm x ^ 2 + omegaD d * r ^ d * g x -
        (euclidNorm p ^ 2 + omegaD d * r ^ d * g p) ∧
      (|euclidNorm x - r| ≤ K →
        euclidNorm x ^ 2 + omegaD d * r ^ d * g x -
        (euclidNorm p ^ 2 + omegaD d * r ^ d * g p) ≤ D) := by
  let M := omegaD d * R ^ d
  let a := M * C + (M * C) ^ 2 + (R + 1) ^ 2 + M * ballBound d g (R + 1)
  refine ⟨a, fun K => ⟨(R + max K 1) ^ 2 + 2 * M * ballBound d g (R + max K 1), ?_⟩⟩
  intro r hr hrR p x hp
  have hm : 0 ≤ omegaD d * r ^ d := mul_nonneg (omegaD_pos d).le (pow_nonneg (by linarith) _)
  have hmM : omegaD d * r ^ d ≤ M := by
    dsimp [M]
    apply mul_le_mul_of_nonneg_left ?_ (le_of_lt (omegaD_pos d))
    exact pow_le_pow_left₀ (by linarith) hrR d
  have hp' : euclidNorm p ≤ R + 1 := by
    have := (abs_le.mp hp).2
    linarith
  constructor
  · exact small_mass_lower d g C M (R + 1) hC (by linarith) hg _ hm hmM p x hp'
  · intro hx
    have hpU : euclidNorm p ≤ R + max K 1 := by
      have := le_max_right K (1 : ℝ)
      linarith
    have hxU : euclidNorm x ≤ R + max K 1 := by
      have := (abs_le.mp hx).2
      have := le_max_left K (1 : ℝ)
      linarith
    exact small_mass_upper d g M (R + max K 1) (by have := le_max_right K (1 : ℝ); linarith)
      _ hm hmM p x hpU hxU


private theorem quadratic_bound (f df ddf : ℝ → ℝ) (r u M : ℝ)
    (hM : 0 ≤ M) (hzero : df r = 0)
    (hf : ∀ t ∈ Set.uIcc r u, HasDerivAt f (df t) t)
    (hdf : ∀ t ∈ Set.uIcc r u, HasDerivAt df (ddf t) t)
    (hddf : ∀ t ∈ Set.uIcc r u, |ddf t| ≤ M) :
    |f u - f r| ≤ M * |u-r| ^ 2 := by
  have hmemr : r ∈ Set.uIcc r u := Set.left_mem_uIcc
  have hmemu : u ∈ Set.uIcc r u := Set.right_mem_uIcc
  have hdist : ∀ t ∈ Set.uIcc r u, |t-r| ≤ |u-r| := by
    intro t ht
    by_cases hru : r ≤ u
    · rw [Set.uIcc_of_le hru] at ht
      rw [abs_of_nonneg (by linarith [ht.1]), abs_of_nonneg (sub_nonneg.mpr hru)]
      linarith [ht.2]
    · have hur : u ≤ r := le_of_not_ge hru
      rw [Set.uIcc_of_ge hur] at ht
      rw [abs_of_nonpos (by linarith [ht.2]), abs_of_nonpos (sub_nonpos.mpr hur)]
      linarith [ht.1]
  have hdfbound : ∀ t ∈ Set.uIcc r u, ‖df t‖ ≤ M * |u-r| := by
    intro t ht
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (s := Set.uIcc r u) (f := df) (f' := ddf)
      (fun z hz => (hdf z hz).hasDerivWithinAt)
      (fun z hz => by simpa only [Real.norm_eq_abs] using hddf z hz)
      (convex_uIcc r u) hmemr ht
    rw [hzero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at h
    exact h.trans (mul_le_mul_of_nonneg_left (hdist t ht) hM)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (s := Set.uIcc r u) (f := f) (f' := df)
    (fun z hz => (hf z hz).hasDerivWithinAt) hdfbound
    (convex_uIcc r u) hmemr hmemu
  simp only [Real.norm_eq_abs] at h
  nlinarith [sq_abs (u-r)]

private theorem planar_phi_bound (t : ℝ) (ht : (1 : ℝ) / 2 ≤ t) :
    (t - 1) ^ 2 ≤ t ^ 2 - 1 - 2 * Real.log t ∧
      t ^ 2 - 1 - 2 * Real.log t ≤ 5 * (t - 1) ^ 2 := by
  have ht0 : 0 < t := by linarith
  have hlog := Real.log_le_sub_one_of_pos ht0
  have hinv := Real.log_le_sub_one_of_pos (inv_pos.mpr ht0)
  rw [Real.log_inv] at hinv
  constructor
  · nlinarith
  · have hbound : t ^ 2 - 1 - 2 * Real.log t ≤ t ^ 2 - 3 + 2 / t := by
      simp only [div_eq_mul_inv] at *
      linarith
    have hid : t ^ 2 - 3 + 2 / t = (t - 1) ^ 2 * (t + 2) / t := by
      field_simp
      ring
    have hcoef : (t + 2) / t ≤ 5 := by
      rw [div_le_iff₀ ht0]
      linarith
    rw [hid] at hbound
    have hs := sq_nonneg (t - 1)
    have hmul := mul_le_mul_of_nonneg_left hcoef hs
    rw [← mul_div_assoc] at hmul
    linarith

private theorem planar_scaled_asymptotic :
    ∃ κ C R : ℝ, 0 ≤ C ∧ 1 ≤ R ∧ ∀ r : ℝ, 0 ≤ r → ∀ x : Site 2, R ≤ euclidNorm x →
      |(euclidNorm x ^ 2 + omegaD 2 * r ^ 2 * (-potentialKernel x)) -
        (euclidNorm x ^ 2 - 2 * r ^ 2 * Real.log (euclidNorm x) - Real.pi * r ^ 2 * κ)|
        ≤ C * r ^ 2 * euclidNorm x ^ (-2 : ℝ) := by
  obtain ⟨κ, D, R, hR, h⟩ := exists_abs_potentialKernel_sub_log_le
  refine ⟨κ, Real.pi * max D 0, R, by positivity, hR, ?_⟩
  intro r hr x hx
  have hRpos : 0 < euclidNorm x := by linarith
  have hp : 0 ≤ euclidNorm x ^ (-2 : ℝ) := Real.rpow_nonneg hRpos.le _
  have hh := h x hx
  have hh' : |potentialKernel x - (2 / Real.pi * Real.log (euclidNorm x) + κ)| ≤
      max D 0 * euclidNorm x ^ (-2 : ℝ) :=
    hh.trans (mul_le_mul_of_nonneg_right (le_max_left D 0) hp)
  have hmul := mul_le_mul_of_nonneg_left hh' (show 0 ≤ Real.pi * r ^ 2 by positivity)
  have heq : (euclidNorm x ^ 2 + omegaD 2 * r ^ 2 * (-potentialKernel x)) -
      (euclidNorm x ^ 2 - 2 * r ^ 2 * Real.log (euclidNorm x) - Real.pi * r ^ 2 * κ) =
      -(Real.pi * r ^ 2) * (potentialKernel x - (2 / Real.pi * Real.log (euclidNorm x) + κ)) := by
    rw [omegaD_two]
    field_simp
    ring
  rw [heq, abs_mul, abs_neg, abs_of_nonneg (show 0 ≤ Real.pi * r ^ 2 by positivity)]
  nlinarith


private theorem transient_scaled_asymptotic (d : ℕ) (hd : 3 ≤ d) :
    ∃ C R : ℝ, 0 ≤ C ∧ 1 ≤ R ∧ ∀ r : ℝ, 0 ≤ r → ∀ x : Site d, R ≤ euclidNorm x →
      |(euclidNorm x ^ 2 + omegaD d * r ^ d * srwGreenInf d x) -
        (euclidNorm x ^ 2 + 2 / ((d : ℝ) - 2) * r ^ d * euclidNorm x ^ (2 - (d : ℝ)))|
        ≤ C * r ^ d * euclidNorm x ^ (-(d : ℝ)) := by
  obtain ⟨D, R, hR, h⟩ := exists_abs_srwGreenInf_sub_le hd
  refine ⟨omegaD d * max D 0, R, mul_nonneg (omegaD_pos d).le (le_max_right D 0), hR, ?_⟩
  intro r hr x hx
  have hRpos : 0 < euclidNorm x := by linarith
  have hp : 0 ≤ euclidNorm x ^ (-(d : ℝ)) := Real.rpow_nonneg hRpos.le _
  have hh := h x hx
  change |srwGreenInf d x - 2 / (((d : ℝ) - 2) * omegaD d) *
    euclidNorm x ^ (2 - (d : ℝ))| ≤ D * euclidNorm x ^ (-(d : ℝ)) at hh
  have hh' : |srwGreenInf d x - 2 / (((d : ℝ) - 2) * omegaD d) *
    euclidNorm x ^ (2 - (d : ℝ))| ≤ max D 0 * euclidNorm x ^ (-(d : ℝ)) :=
    hh.trans (mul_le_mul_of_nonneg_right (le_max_left D 0) hp)
  have hmul := mul_le_mul_of_nonneg_left hh'
    (show 0 ≤ omegaD d * r ^ d from mul_nonneg (omegaD_pos d).le (pow_nonneg hr _))
  have hd' : (d : ℝ) - 2 ≠ 0 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have heq : (euclidNorm x ^ 2 + omegaD d * r ^ d * srwGreenInf d x) -
      (euclidNorm x ^ 2 + 2 / ((d : ℝ) - 2) * r ^ d * euclidNorm x ^ (2 - (d : ℝ))) =
      (omegaD d * r ^ d) * (srwGreenInf d x - 2 / (((d : ℝ) - 2) * omegaD d) *
        euclidNorm x ^ (2 - (d : ℝ))) := by
    field_simp [(omegaD_pos d).ne', hd']
    ring
  rw [heq, abs_mul, abs_of_nonneg (show 0 ≤ omegaD d * r ^ d from
    mul_nonneg (omegaD_pos d).le (pow_nonneg hr _))]
  nlinarith


private theorem scaled_error_le (d : ℕ) (r u B : ℝ) (hr : 0 ≤ r) (hu : 0 < u)
    (hru : r ≤ B * u) :
    r ^ d * u ^ (-(d : ℝ)) ≤ B ^ d := by
  rw [Real.rpow_neg hu.le, Real.rpow_natCast, ← div_eq_mul_inv, ← div_pow]
  apply pow_le_pow_left₀ (div_nonneg hr hu.le) ?_ d
  exact (div_le_iff₀ hu).2 hru


private theorem transient_phi_lower (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : 0 < t) :
    (t - 1) ^ 2 ≤ t ^ 2 - 1 + (2 / (n : ℝ)) * (t ^ (-(n : ℝ)) - 1) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hinv0 : 0 ≤ t⁻¹ := le_of_lt (inv_pos.mpr ht)
  have hbern := one_add_mul_sub_le_pow (a := t⁻¹) (by linarith) n
  have hprod : t * t⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
  have hsq : 0 ≤ (t - 1) ^ 2 := sq_nonneg _
  have hinv : 1 - t ≤ t⁻¹ - 1 := by
    have h := mul_nonneg hsq (inv_nonneg.mpr ht.le)
    nlinarith
  have hbern' : 1 + (n : ℝ) * (1 - t) ≤ (t⁻¹) ^ n := by
    have := mul_le_mul_of_nonneg_left hinv hn0.le
    linarith
  rw [Real.rpow_neg ht.le, Real.rpow_natCast, ← inv_pow]
  have hh : 2 * ((1 : ℝ) - t) ≤ (2 / (n : ℝ)) * ((t⁻¹) ^ n - 1) := by
    have hh' : 1 - t ≤ ((t⁻¹) ^ n - 1) / (n : ℝ) :=
      (le_div_iff₀ hn0).2 (by nlinarith [hbern'])
    simp only [div_eq_mul_inv] at hh' ⊢
    nlinarith
  nlinarith

private theorem transient_phi_upper (n : ℕ) (hn : 1 ≤ n) (t : ℝ)
    (ht : (1 : ℝ) / 2 ≤ t) (ht2 : t ≤ 2) :
    t ^ 2 - 1 + (2 / (n : ℝ)) * (t ^ (-(n : ℝ)) - 1) ≤
      (2 + 2 * ((n : ℝ) + 1) * ((1 : ℝ) / 2) ^ (-(n : ℝ) - 2)) * (t - 1) ^ 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  let f : ℝ → ℝ := fun x => x ^ 2 - 1 + (2 / (n : ℝ)) * (x ^ (-(n : ℝ)) - 1)
  let df : ℝ → ℝ := fun x => 2 * x - 2 * x ^ (-(n : ℝ) - 1)
  let ddf : ℝ → ℝ := fun x => 2 + 2 * ((n : ℝ) + 1) * x ^ (-(n : ℝ) - 2)
  let M : ℝ := 2 + 2 * ((n : ℝ) + 1) * ((1 : ℝ) / 2) ^ (-(n : ℝ) - 2)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hs : Set.uIcc (1 : ℝ) t ⊆ Set.Icc (1 / 2) 2 :=
    Set.uIcc_subset_Icc (by norm_num) ⟨ht, ht2⟩
  have hz : df 1 = 0 := by simp [df]
  have hf : ∀ z ∈ Set.uIcc (1 : ℝ) t, HasDerivAt f (df z) z := by
    intro z hz
    have hz0 : z ≠ 0 := by have := (hs hz).1; linarith
    have hpow := Real.hasDerivAt_rpow_const (x := z) (p := -(n : ℝ)) (Or.inl hz0)
    have h : HasDerivAt (fun x : ℝ => x ^ 2 - 1 + (2 / (n : ℝ)) * (x ^ (-(n : ℝ)) - 1)) _ z :=
      (((hasDerivAt_id z).pow 2).sub_const 1).add ((hpow.sub_const 1).const_mul (2 / (n : ℝ)))
    change HasDerivAt (fun x : ℝ => x ^ 2 - 1 + (2 / (n : ℝ)) * (x ^ (-(n : ℝ)) - 1)) (df z) z
    convert h using 1
    dsimp [df]
    field_simp [hn0.ne']
    ring
  have hdf : ∀ z ∈ Set.uIcc (1 : ℝ) t, HasDerivAt df (ddf z) z := by
    intro z hz
    have hz0 : z ≠ 0 := by have := (hs hz).1; linarith
    have hpow := Real.hasDerivAt_rpow_const (x := z) (p := -(n : ℝ) - 1) (Or.inl hz0)
    have h : HasDerivAt (fun x : ℝ => 2 * x - 2 * x ^ (-(n : ℝ) - 1)) _ z :=
      ((hasDerivAt_id z).const_mul 2).sub (hpow.const_mul 2)
    change HasDerivAt (fun x : ℝ => 2 * x - 2 * x ^ (-(n : ℝ) - 1)) (ddf z) z
    convert h using 1
    dsimp [ddf]
    ring
  have hddf : ∀ z ∈ Set.uIcc (1 : ℝ) t, |ddf z| ≤ M := by
    intro z hz
    have hz' := (hs hz).1
    have hp := Real.rpow_le_rpow_of_nonpos (show (0 : ℝ) < 1 / 2 by norm_num) hz' (show -(n : ℝ) - 2 ≤ 0 by linarith)
    have hp0 : 0 ≤ z ^ (-(n : ℝ) - 2) := Real.rpow_nonneg (by linarith) _
    have hcoef : 0 ≤ 2 * ((n : ℝ) + 1) := by positivity
    have := mul_le_mul_of_nonneg_left hp hcoef
    have hd0 : 0 ≤ ddf z := by dsimp [ddf]; positivity
    rw [abs_of_nonneg hd0]
    dsimp [ddf, M]
    linarith
  have h := quadratic_bound f df ddf 1 t M hM hz hf hdf hddf
  have h' : f t - f 1 ≤ M * |t - 1| ^ 2 := (le_abs_self _).trans h
  dsimp [f, M] at h'
  norm_num only [Real.one_rpow, sub_self, mul_zero, one_pow, add_zero, sub_zero] at h'
  rw [sq_abs] at h'
  exact h'

private theorem transient_scale (n : ℕ) (hn : 1 ≤ n) (r u : ℝ) (hr : 0 < r) (hu : 0 < u) :
    (u ^ 2 + (2 / (n : ℝ)) * r ^ (n + 2) * u ^ (-(n : ℝ))) -
      (r ^ 2 + (2 / (n : ℝ)) * r ^ 2) =
    r ^ 2 * ((u / r) ^ 2 - 1 + (2 / (n : ℝ)) * ((u / r) ^ (-(n : ℝ)) - 1)) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < n))
  have hur0 : 0 ≤ u / r := div_nonneg hu.le hr.le
  rw [Real.rpow_neg hu.le, Real.rpow_natCast, Real.rpow_neg hur0, Real.rpow_natCast,
    div_pow]
  simp only [div_pow, inv_div, pow_add]
  field_simp [hn0, hr.ne', hu.ne']
  ring

private theorem planar_scale (r u : ℝ) (hr : 0 < r) (hu : 0 < u) :
    (u ^ 2 - 2 * r ^ 2 * Real.log u) - (r ^ 2 - 2 * r ^ 2 * Real.log r) =
      r ^ 2 * ((u / r) ^ 2 - 1 - 2 * Real.log (u / r)) := by
  rw [Real.log_div hu.ne' hr.ne']
  field_simp [hr.ne']
  ring

private theorem transient_radial_bounds (d : ℕ) (hd : 3 ≤ d) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ r u : ℝ, 0 < r → 0 < u →
      (u - r) ^ 2 ≤ (u ^ 2 + 2 / ((d : ℝ) - 2) * r ^ d * u ^ (2 - (d : ℝ))) -
        (r ^ 2 + 2 / ((d : ℝ) - 2) * r ^ 2) ∧
      (r / 2 ≤ u → u ≤ 2 * r →
        (u ^ 2 + 2 / ((d : ℝ) - 2) * r ^ d * u ^ (2 - (d : ℝ))) -
          (r ^ 2 + 2 / ((d : ℝ) - 2) * r ^ 2) ≤ Q * (u - r) ^ 2) := by
  let n := d - 2
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hdn : d = n + 2 := by dsimp [n]; omega
  have hcast : (d : ℝ) - 2 = n := by
    rw [hdn]
    push_cast
    ring
  have hexp : 2 - (d : ℝ) = -(n : ℝ) := by linarith
  let Q := 2 + 2 * ((n : ℝ) + 1) * ((1 : ℝ) / 2) ^ (-(n : ℝ) - 2)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  refine ⟨Q, hQ, fun r u hr hu => ?_⟩
  have ht : 0 < u / r := div_pos hu hr
  have hsquared : r ^ 2 * (u / r - 1) ^ 2 = (u - r) ^ 2 := by
    field_simp [hr.ne']
  have hscale := transient_scale n hn r u hr hu
  have hlow := transient_phi_lower n hn (u / r) ht
  have hrlow := mul_le_mul_of_nonneg_left hlow (sq_nonneg r)
  rw [hsquared, ← hscale] at hrlow
  rw [hcast, hexp, hdn]
  constructor
  · exact hrlow
  · intro hu1 hu2
    have ht1 : (1 : ℝ) / 2 ≤ u / r := (le_div_iff₀ hr).2 (by linarith)
    have ht2 : u / r ≤ 2 := (div_le_iff₀ hr).2 (by linarith)
    have hup := transient_phi_upper n hn (u / r) ht1 ht2
    have hrup := mul_le_mul_of_nonneg_left hup (sq_nonneg r)
    rw [← hscale] at hrup
    have heq : r ^ 2 * (Q * (u / r - 1) ^ 2) = Q * (u - r) ^ 2 := by
      rw [show r ^ 2 * (Q * (u / r - 1) ^ 2) = Q * (r ^ 2 * (u / r - 1) ^ 2) by ring, hsquared]
    change _ ≤ r ^ 2 * (Q * (u / r - 1) ^ 2) at hrup
    rwa [heq] at hrup


private theorem planar_radial_bounds (r u : ℝ) (hr : 0 < r) (hu : 0 < u) :
    (u-r) ^ 2 ≤ (u ^ 2 - 2 * r ^ 2 * Real.log u) -
        (r ^ 2 - 2 * r ^ 2 * Real.log r) ∧
      (r / 2 ≤ u → u ≤ 2 * r →
        (u ^ 2 - 2 * r ^ 2 * Real.log u) -
          (r ^ 2 - 2 * r ^ 2 * Real.log r) ≤ 5 * (u-r) ^ 2) := by
  have ht : 0 < u / r := div_pos hu hr
  have hsquared : r ^ 2 * (u / r - 1) ^ 2 = (u - r) ^ 2 := by field_simp [hr.ne']
  have hscale := planar_scale r u hr hu
  have hlog := Real.log_le_sub_one_of_pos ht
  have hlow : (u / r - 1) ^ 2 ≤ (u / r) ^ 2 - 1 - 2 * Real.log (u / r) := by nlinarith
  have hrlow := mul_le_mul_of_nonneg_left hlow (sq_nonneg r)
  rw [hsquared, ← hscale] at hrlow
  constructor
  · exact hrlow
  · intro hu1 _
    have ht1 : (1 : ℝ) / 2 ≤ u / r := (le_div_iff₀ hr).2 (by linarith)
    have hup := (planar_phi_bound (u / r) ht1).2
    have hrup := mul_le_mul_of_nonneg_left hup (sq_nonneg r)
    rw [← hscale] at hrup
    have heq : r ^ 2 * (5 * (u / r - 1) ^ 2) = 5 * (u - r) ^ 2 := by
      rw [show r ^ 2 * (5 * (u / r - 1) ^ 2) = 5 * (r ^ 2 * (u / r - 1) ^ 2) by ring, hsquared]
    rwa [heq] at hrup


private structure GreenData (d : ℕ) where
  g : Site d → ℝ
  phi : ℝ → ℝ → ℝ
  b : ℝ → ℝ
  C : ℝ
  R : ℝ
  Q : ℝ
  C_nonneg : 0 ≤ C
  R_ge : 1 ≤ R
  Q_nonneg : 0 ≤ Q
  equation : ∀ x, walkOp g x = g x - if x = 0 then 1 else 0
  linear_lower : ∃ C : ℝ, 0 ≤ C ∧ ∀ x, -C * (1 + euclidNorm x) ≤ g x
  asymptotic : ∀ r : ℝ, 0 ≤ r → ∀ x : Site d, R ≤ euclidNorm x →
    |(euclidNorm x ^ 2 + omegaD d * r ^ d * g x) - (phi r (euclidNorm x) + b r)| ≤
      C * r ^ d * euclidNorm x ^ (-(d : ℝ))
  radial : ∀ r u : ℝ, 0 < r → 0 < u → (u-r) ^ 2 ≤ phi r u - phi r r ∧
    (r / 2 ≤ u → u ≤ 2 * r → phi r u - phi r r ≤ Q * (u-r) ^ 2)

private noncomputable def greenData (d : ℕ) (hd : 2 ≤ d) : GreenData d := Classical.choice (show Nonempty (GreenData d) from by
  classical
  rcases eq_or_lt_of_le hd with h | h
  · subst d
    obtain ⟨κ, C, R, hC, hR, hasym⟩ := planar_scaled_asymptotic
    refine ⟨⟨fun x => -potentialKernel x, fun r u => u ^ 2 - 2 * r ^ 2 * Real.log u,
      fun r => -Real.pi * r ^ 2 * κ, C, R, 5, hC, hR, by norm_num, ?_,
      potentialKernel_linear_lower, ?_, planar_radial_bounds⟩⟩
    · intro x
      rw [walkOp_neg]
      have h := walkOp_potentialKernel_sub x
      linarith
    · intro r hr x hx
      have h := hasym r hr x hx
      convert h using 1
      ring
  · have hd3 : 3 ≤ d := by omega
    obtain ⟨C, R, hC, hR, hasym⟩ := transient_scaled_asymptotic d hd3
    obtain ⟨Q, hQ, hrad⟩ := transient_radial_bounds d hd3
    refine ⟨⟨srwGreenInf d, fun r u => u ^ 2 + 2 / ((d : ℝ) - 2) * r ^ d * u ^ (2 - (d : ℝ)),
      fun _ => 0, C, R, Q, hC, hR, hQ, walkOp_srwGreenInf hd3,
      ⟨0, le_rfl, ?_⟩, ?_, ?_⟩⟩
    · intro x
      simpa using srwGreenInf_nonneg x
    · intro r hr x hx
      simpa only [add_zero] using hasym r hr x hx
    · intro r u hr hu
      have h := hrad r u hr hu
      have hrpos : 0 < r := hr
      have hid : r ^ d * r ^ (2 - (d : ℝ)) = r ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hrpos]
        norm_num
      have hmodel : 2 / ((d : ℝ) - 2) * r ^ d * r ^ (2 - (d : ℝ)) =
          2 / ((d : ℝ) - 2) * r ^ 2 := by rw [mul_assoc, hid]
      simpa only [hmodel] using h)


private theorem green_outer_lower {d : ℕ} (G : GreenData d) (r : ℝ)
    (hrR : 3 * G.R ≤ r) (hr6 : 6 ≤ r) (p x : Site d)
    (hp : |euclidNorm p - r| ≤ 1) (hx : r / 3 ≤ euclidNorm x) :
    (euclidNorm x - r) ^ 2 - (G.C * (3 ^ d + 2 ^ d) + G.Q) ≤
      (euclidNorm x ^ 2 + omegaD d * r ^ d * G.g x) -
        (euclidNorm p ^ 2 + omegaD d * r ^ d * G.g p) := by
  have hr0 : 0 < r := by linarith
  have hxR : G.R ≤ euclidNorm x := by linarith
  have hx0 : 0 < euclidNorm x := by linarith [G.R_ge]
  have hp1 := abs_le.mp hp
  have hp0 : 0 < euclidNorm p := by linarith [hp1.1]
  have hpR : G.R ≤ euclidNorm p := by linarith [G.R_ge, hp1.1]
  have hpHalf : r / 2 ≤ euclidNorm p := by linarith [hp1.1]
  have hpDouble : euclidNorm p ≤ 2 * r := by linarith [hp1.2]
  have hpe := scaled_error_le d r (euclidNorm p) 2 hr0.le hp0 (by linarith)
  have hxe := scaled_error_le d r (euclidNorm x) 3 hr0.le hx0 (by linarith)
  have hpErr := G.asymptotic r hr0.le p hpR
  have hxErr := G.asymptotic r hr0.le x hxR
  have hpErr' : |(euclidNorm p ^ 2 + omegaD d * r ^ d * G.g p) -
      (G.phi r (euclidNorm p) + G.b r)| ≤ G.C * 2 ^ d := by
    have h := mul_le_mul_of_nonneg_left hpe G.C_nonneg
    nlinarith
  have hxErr' : |(euclidNorm x ^ 2 + omegaD d * r ^ d * G.g x) -
      (G.phi r (euclidNorm x) + G.b r)| ≤ G.C * 3 ^ d := by
    have h := mul_le_mul_of_nonneg_left hxe G.C_nonneg
    nlinarith
  have hpr := (G.radial r (euclidNorm p) hr0 hp0).2 hpHalf hpDouble
  have hxr := (G.radial r (euclidNorm x) hr0 hx0).1
  have hpsq : (euclidNorm p - r) ^ 2 ≤ 1 := by nlinarith [hp1.1, hp1.2]
  have hq := mul_le_mul_of_nonneg_left hpsq G.Q_nonneg
  have hpupper := (abs_le.mp hpErr').2
  have hxlower := (abs_le.mp hxErr').1
  nlinarith


private theorem green_shell_upper {d : ℕ} (G : GreenData d) (r K : ℝ)
    (hrR : 2 * G.R ≤ r) (hrK : 2 * max K 1 ≤ r) (p x : Site d)
    (hp : |euclidNorm p - r| ≤ 1) (hx : |euclidNorm x - r| ≤ K) :
    (euclidNorm x ^ 2 + omegaD d * r ^ d * G.g x) -
      (euclidNorm p ^ 2 + omegaD d * r ^ d * G.g p) ≤
        G.Q * K ^ 2 + 2 * G.C * 2 ^ d := by
  have hr0 : 0 < r := by linarith [G.R_ge]
  have hp1 := abs_le.mp hp
  have hx1 := abs_le.mp hx
  have hK : 0 ≤ K := (abs_nonneg _).trans hx
  have hmax := le_max_left K (1 : ℝ)
  have hmax1 := le_max_right K (1 : ℝ)
  have hp0 : 0 < euclidNorm p := by linarith [hp1.1]
  have hx0 : 0 < euclidNorm x := by linarith [hx1.1]
  have hpR : G.R ≤ euclidNorm p := by linarith [hp1.1]
  have hxR : G.R ≤ euclidNorm x := by linarith [hx1.1]
  have hpHalf : r / 2 ≤ euclidNorm p := by linarith [hp1.1]
  have hxHalf : r / 2 ≤ euclidNorm x := by linarith [hx1.1]
  have hxDouble : euclidNorm x ≤ 2 * r := by linarith [hx1.2]
  have hpe := scaled_error_le d r (euclidNorm p) 2 hr0.le hp0 (by linarith)
  have hxe := scaled_error_le d r (euclidNorm x) 2 hr0.le hx0 (by linarith)
  have hpErr := G.asymptotic r hr0.le p hpR
  have hxErr := G.asymptotic r hr0.le x hxR
  have hpErr' : |(euclidNorm p ^ 2 + omegaD d * r ^ d * G.g p) -
      (G.phi r (euclidNorm p) + G.b r)| ≤ G.C * 2 ^ d := by
    have h := mul_le_mul_of_nonneg_left hpe G.C_nonneg
    nlinarith
  have hxErr' : |(euclidNorm x ^ 2 + omegaD d * r ^ d * G.g x) -
      (G.phi r (euclidNorm x) + G.b r)| ≤ G.C * 2 ^ d := by
    have h := mul_le_mul_of_nonneg_left hxe G.C_nonneg
    nlinarith
  have hxr := (G.radial r (euclidNorm x) hr0 hx0).2 hxHalf hxDouble
  have hpr := (G.radial r (euclidNorm p) hr0 hp0).1
  have hxsq : (euclidNorm x - r) ^ 2 ≤ K ^ 2 := by nlinarith [hx1.1, hx1.2]
  have hq := mul_le_mul_of_nonneg_left hxsq G.Q_nonneg
  have hxx := (abs_le.mp hxErr').2
  have hpp := (abs_le.mp hpErr').1
  nlinarith [sq_nonneg (euclidNorm p - r)]


private lemma euclidNorm_neg {d : ℕ} (z : Site d) : euclidNorm (-z) = euclidNorm z := by
  unfold euclidNorm
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.neg_apply]
  push_cast
  ring

/-- Minkowski's triangle inequality for the Euclidean norm, via Cauchy-Schwarz. -/

private lemma euclidNorm_add_le {d : ℕ} (a b : Site d) :
    euclidNorm (a + b) ≤ euclidNorm a + euclidNorm b := by
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin d))
    (fun i => ((a i : ℤ) : ℝ)) (fun i => ((b i : ℤ) : ℝ))
  have hA : (0 : ℝ) ≤ euclidNorm a := euclidNorm_nonneg a
  have hB : (0 : ℝ) ≤ euclidNorm b := euclidNorm_nonneg b
  have hpt : ∀ i : Fin d, (((a + b) i : ℤ) : ℝ) ^ 2 =
      ((a i : ℤ) : ℝ) ^ 2 + 2 * (((a i : ℤ) : ℝ) * ((b i : ℤ) : ℝ))
        + ((b i : ℤ) : ℝ) ^ 2 := by
    intro i
    have hi : ((a + b) i : ℤ) = (a i : ℤ) + (b i : ℤ) := by simp [Pi.add_apply]
    rw [hi]
    push_cast
    ring
  have hexpand : (∑ i : Fin d, (((a + b) i : ℤ) : ℝ) ^ 2) =
      (∑ i : Fin d, ((a i : ℤ) : ℝ) ^ 2)
        + 2 * (∑ i : Fin d, ((a i : ℤ) : ℝ) * ((b i : ℤ) : ℝ))
        + (∑ i : Fin d, ((b i : ℤ) : ℝ) ^ 2) := by
    rw [Finset.sum_congr rfl (fun i _ => hpt i)]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hcross : (∑ i : Fin d, ((a i : ℤ) : ℝ) * ((b i : ℤ) : ℝ)) ≤
      euclidNorm a * euclidNorm b := hcs
  have haa : euclidNorm a ^ 2 = ∑ i : Fin d, ((a i : ℤ) : ℝ) ^ 2 := by
    unfold euclidNorm
    rw [Real.sq_sqrt (by positivity)]
  have hbb : euclidNorm b ^ 2 = ∑ i : Fin d, ((b i : ℤ) : ℝ) ^ 2 := by
    unfold euclidNorm
    rw [Real.sq_sqrt (by positivity)]
  have hsq : (∑ i : Fin d, (((a + b) i : ℤ) : ℝ) ^ 2) ≤
      (euclidNorm a + euclidNorm b) ^ 2 := by
    rw [hexpand]
    have hring : (euclidNorm a + euclidNorm b) ^ 2 =
        euclidNorm a ^ 2 + 2 * (euclidNorm a * euclidNorm b) + euclidNorm b ^ 2 := by ring
    rw [hring, haa, hbb]
    linarith [hcross]
  calc euclidNorm (a + b) = Real.sqrt (∑ i : Fin d, (((a + b) i : ℤ) : ℝ) ^ 2) := rfl
    _ ≤ Real.sqrt ((euclidNorm a + euclidNorm b) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = euclidNorm a + euclidNorm b := Real.sqrt_sq (by linarith [hA, hB])

private lemma euclidNorm_unit {d : ℕ} (i : Fin d) : euclidNorm (unit i) = 1 := by
  have hsum : (∑ j : Fin d, (((unit i) j : ℤ) : ℝ) ^ 2) = 1 := by
    classical
    rw [Finset.sum_eq_single i]
    · simp [unit]
    · intro j _ hji
      simp [unit, hji]
    · intro hi
      exact False.elim (hi (Finset.mem_univ i))
  unfold euclidNorm
  rw [hsum, Real.sqrt_one]



private theorem euclidNorm_le_of_adj {d : ℕ} {x y : Site d} (h : (lattice d).Adj x y) :
    euclidNorm y ≤ euclidNorm x + 1 := by
  obtain ⟨i, hi | hi⟩ := h
  · rw [hi]
    simpa only [euclidNorm_unit] using euclidNorm_add_le x (unit i)
  · have heq : y = x + (-unit i) := by rw [hi]; abel
    rw [heq]
    simpa only [euclidNorm_neg, euclidNorm_unit] using euclidNorm_add_le x (-unit i)


private theorem superharmonic_ball_lower {d : ℕ} (hd : 1 ≤ d) (g : Site d → ℝ)
    (hg : ∀ x, walkOp g x = g x - if x = 0 then 1 else 0) (R m : ℝ)
    (hboundary : ∀ z, R ≤ euclidNorm z → euclidNorm z ≤ R + 1 → m ≤ g z)
    (x : Site d) (hx : euclidNorm x < R) : m ≤ g x := by
  classical
  have : NeZero d := ⟨by omega⟩
  let A : Finset (Site d) := (ballFinset d R).filter (fun z => euclidNorm z < R)
  have hA : ∀ z : Site d, z ∈ A ↔ euclidNorm z < R := by
    intro z
    simp only [A, Finset.mem_filter, mem_ballFinset_iff]
    exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩
  obtain ⟨N, hN⟩ := exists_nat_gt R
  let z : Site d := fun _ => (N : ℤ)
  let i : Fin d := ⟨0, by omega⟩
  have hsup : N ≤ supNorm z := by
    have h := Finset.le_sup (f := fun j : Fin d => (z j).natAbs) (Finset.mem_univ i)
    simpa only [z, Int.natAbs_natCast, supNorm] using h
  have hzr : R < euclidNorm z := by
    have hcast : (N : ℝ) ≤ (supNorm z : ℝ) := by exact_mod_cast hsup
    linarith [supNorm_le_euclidNorm z]
  have haccess : Network.BoundaryAccessible (lattice d) A :=
    Network.boundaryAccessible_of_connected (Graph.Zd.latticeConnected d) A
      ⟨z, fun hz => (not_lt_of_ge hzr.le) ((hA z).mp hz)⟩
  let f : Site d → ℝ := fun z => if euclidNorm z ≤ R + 1 then g z else m
  have hfx : ∀ z, euclidNorm z ≤ R + 1 → f z = g z := by
    intro z hz
    exact ite_eq_left hz
  have hsupharm : ∀ v ∈ A, Network.netLaplacian (lattice d) (Network.unitCond (lattice d)) f v ≤ 0 := by
    intro v hv
    have hvR := (hA v).mp hv
    have hfv : f v = g v := hfx v (by linarith)
    have hlap : Network.netLaplacian (lattice d) (Network.unitCond (lattice d)) f v =
        Network.netLaplacian (lattice d) (Network.unitCond (lattice d)) g v := by
      unfold Network.netLaplacian
      apply Finset.sum_congr rfl
      intro y hy
      have hadj := (SimpleGraph.mem_neighborFinset _ _ _).mp hy
      have hny := euclidNorm_le_of_adj hadj
      rw [hfv, hfx y (by linarith)]
    rw [hlap, netLaplacian_lattice hd, hg v]
    split_ifs <;> nlinarith
  have hfb : ∀ v, v ∉ A → m ≤ f v := by
    intro v hv
    have hvR : R ≤ euclidNorm v := le_of_not_gt (fun h => hv ((hA v).mpr h))
    by_cases hv2 : euclidNorm v ≤ R + 1
    · rw [hfx v hv2]
      exact hboundary v hvR hv2
    · dsimp [f]
      rw [ite_eq_right hv2]
  have hmin := Network.superharmonic_minimum_principle
    (Network.isCond_unitCond (G := lattice d)) A haccess f m hsupharm hfb x
  rwa [hfx x (by linarith)] at hmin


private theorem green_large_lower {d : ℕ} (hd : 1 ≤ d) (G : GreenData d) (r : ℝ)
    (hrR : 3 * G.R ≤ r) (hr6 : 6 ≤ r) (p x : Site d)
    (hp : |euclidNorm p - r| ≤ 1) :
    -(G.C * (3 ^ d + 2 ^ d) + G.Q + 3) ≤
      (euclidNorm x ^ 2 + omegaD d * r ^ d * G.g x) -
        (euclidNorm p ^ 2 + omegaD d * r ^ d * G.g p) := by
  let E : ℝ := G.C * (3 ^ d + 2 ^ d) + G.Q
  by_cases hx : r / 3 ≤ euclidNorm x
  · have h := green_outer_lower G r hrR hr6 p x hp hx
    nlinarith [sq_nonneg (euclidNorm x - r)]
  · have hxinner : euclidNorm x < r / 3 := lt_of_not_ge hx
    have hr0 : 0 < r := by linarith
    let m : ℝ := omegaD d * r ^ d
    have hm : 0 < m := mul_pos (omegaD_pos d) (pow_pos hr0 _)
    let Fp : ℝ := euclidNorm p ^ 2 + m * G.g p
    let B : ℝ := (Fp + r ^ 2 / 3 - 2 * r - E) / m
    have hb : ∀ z : Site d, r / 3 ≤ euclidNorm z → euclidNorm z ≤ r / 3 + 1 → B ≤ G.g z := by
      intro z hz1 hz2
      apply (div_le_iff₀ hm).2
      have hout := green_outer_lower G r hrR hr6 p z hp hz1
      have hpbound : 0 ≤ r * (r / 3 + 1 - euclidNorm z) :=
        mul_nonneg hr0.le (by linarith)
      dsimp [B, Fp, E, m] at *
      nlinarith
    have hinner := superharmonic_ball_lower hd G.g G.equation (r / 3) B hb x hxinner
    have hmul := mul_le_mul_of_nonneg_left hinner hm.le
    have heq : m * B = Fp + r ^ 2 / 3 - 2 * r - E := by
      dsimp [B]
      field_simp
    rw [heq] at hmul
    have hs := sq_nonneg (r - 3)
    dsimp [Fp, m, E] at *
    nlinarith [sq_nonneg (euclidNorm x)]


end LatticeProb.Sandpile.FLP

namespace LatticeProb.Sandpile.FLP
open LatticeProb

/-- A Green function whose quadratic comparison is bounded below and near the ball boundary. -/
theorem exists_greenComparison (d : ℕ) (hd : 2 ≤ d) :
    ∃ g : Site d → ℝ, (∀ x, walkOp g x = g x - if x = 0 then 1 else 0) ∧
      ∃ a : ℝ, ∀ K : ℝ, ∃ C : ℝ, ∀ r : ℝ, 1 ≤ r → ∀ p x : Site d, |euclidNorm p - r| ≤ 1 →
        -a ≤ euclidNorm x ^ 2 + omegaD d * r ^ d * g x - (euclidNorm p ^ 2 + omegaD d * r ^ d * g p) ∧
        (|euclidNorm x - r| ≤ K →
          euclidNorm x ^ 2 + omegaD d * r ^ d * g x - (euclidNorm p ^ 2 + omegaD d * r ^ d * g p) ≤ C) := by
  let G := greenData d hd
  obtain ⟨C₀, hC₀, hg⟩ := G.linear_lower
  let R₀ := max (3 * G.R) 6
  have hR₀ : 1 ≤ R₀ := by have := le_max_right (3 * G.R) (6 : ℝ); linarith
  obtain ⟨a₀, hsmall⟩ := small_radius_comparison d G.g R₀ C₀ hR₀ hC₀ hg
  let a₁ := G.C * (3 ^ d + 2 ^ d) + G.Q + 3
  refine ⟨G.g, G.equation, max a₀ a₁, fun K => ?_⟩
  let R₁ := max R₀ (2 * max K 1)
  have hR₁ : 1 ≤ R₁ := hR₀.trans (le_max_left _ _)
  obtain ⟨_, hsmallK⟩ := small_radius_comparison d G.g R₁ C₀ hR₁ hC₀ hg
  obtain ⟨C₁, hC₁⟩ := hsmallK K
  refine ⟨max C₁ (G.Q * K ^ 2 + 2 * G.C * 2 ^ d), ?_⟩
  intro r hr p x hp
  constructor
  · by_cases hrsmall : r ≤ R₀
    · obtain ⟨_, hs⟩ := hsmall K
      have h := (hs r hr hrsmall p x hp).1
      have := le_max_left a₀ a₁
      linarith
    · have hrlarge : R₀ ≤ r := le_of_lt (lt_of_not_ge hrsmall)
      have h := green_large_lower (by omega) G r
        ((le_max_left (3 * G.R) 6).trans hrlarge)
        ((le_max_right (3 * G.R) 6).trans hrlarge) p x hp
      have := le_max_right a₀ a₁
      dsimp [a₁] at *
      linarith
  · intro hx
    by_cases hrsmall : r ≤ R₁
    · exact ((hC₁ r hr hrsmall p x hp).2 hx).trans (le_max_left _ _)
    · have hrlarge : R₁ ≤ r := le_of_lt (lt_of_not_ge hrsmall)
      have hrR : 2 * G.R ≤ r := by
        have := le_max_left (3 * G.R) (6 : ℝ)
        have := le_max_left R₀ (2 * max K 1)
        have := G.R_ge
        dsimp [R₀, R₁] at *
        linarith
      have hrK : 2 * max K 1 ≤ r := (le_max_right _ _).trans hrlarge
      exact (green_shell_upper G r K hrR hrK p x hp hx).trans (le_max_right _ _)

end LatticeProb.Sandpile.FLP
