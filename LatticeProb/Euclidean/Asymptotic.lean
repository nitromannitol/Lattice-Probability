import LatticeProb.Euclidean.Lattice
import LatticeProb.Euclidean.Cube
import LatticeProb.Euclidean.Shell
import LatticeProb.Euclidean.Summability
import LatticeProb.Euclidean.Integral

/-!
# Asymptotic of the critical Euclidean lattice sum

For `d ≥ 1`, the sum of `|z|^{-d}` over the nonzero integer points with `|z| ≤ R` differs from
`d · unitBallVolume d · log R` by at most one constant `K(d)`, uniformly for every real `R ≥ 2`.
The proof combines the disjoint cube comparison with the sandwich of the cube union between two
Euclidean annuli, and it bounds the points of radius below `3√d` by a box count.
-/

noncomputable section

open scoped BigOperators
open LatticeProb.Euclidean.Lattice LatticeProb.Euclidean.Cube LatticeProb.Euclidean.Shell
open LatticeProb.Euclidean.Summability LatticeProb.Euclidean.Integral MeasureTheory Set

namespace LatticeProb.Euclidean.Asymptotic

/-- For `R > 0`, `1/R · r ≤ 1` exactly when `r ≤ R`. -/
lemma one_div_mul_le_one_iff {R r : ℝ} (hR : 0 < R) : 1 / R * r ≤ 1 ↔ r ≤ R := by
  rw [one_div, inv_mul_le_iff₀ hR, mul_one]

/-- The points of `unitBallIndices d (1/R)` of physical radius at least `2√d` are exactly the points
of `latticeAnnulus d R`. -/
lemma unitBallIndices_filter_eq_latticeAnnulus {d : ℕ} (hd : 1 ≤ d) {R : ℝ} (hR : 0 < R) :
    (unitBallIndices d (1 / R)).filter (fun z => 2 * Real.sqrt d ≤ radius (physical 1 z)) =
      latticeAnnulus d R := by
  ext z
  rw [Finset.mem_filter, mem_unitBallIndices (one_div_pos.mpr hR),
    radius_physical_eq_mul (one_div_pos.mpr hR).le z, mem_latticeAnnulus]
  constructor
  · rintro ⟨⟨_, hle⟩, hz⟩
    exact ⟨hz, (one_div_mul_le_one_iff hR).mp hle⟩
  · rintro ⟨hz, hle⟩
    have hmem : z ∈ latticeAnnulus d R := (mem_latticeAnnulus d R z).mpr ⟨hz, hle⟩
    exact ⟨⟨latticeAnnulus_nonzero d hd R z hmem, (one_div_mul_le_one_iff hR).mpr hle⟩, hz⟩

/-- A finite set of nonzero integer points of radius below `M` has critical sum at most the number
of integer points of the box `[-⌈M⌉, ⌈M⌉]^d`, since every summand is at most one. -/
lemma sum_rpow_le_box_card {d : ℕ} {M : ℝ} (T : Finset (Site d))
    (hT : ∀ z ∈ T, z ≠ 0 ∧ radius (physical 1 z) < M) :
    ∑ z ∈ T, Real.rpow (radius (physical 1 z)) (-(d : ℝ)) ≤
      ((Fintype.piFinset (fun _ : Fin d => Finset.Icc (-⌈M⌉) ⌈M⌉)).card : ℝ) := by
  have h1 : ∀ z ∈ T, Real.rpow (radius (physical 1 z)) (-(d : ℝ)) ≤ 1 := fun z hz =>
    Real.rpow_le_one_of_one_le_of_nonpos (lattice_radius_ge_one (hT z hz).1)
      (neg_nonpos.mpr (Nat.cast_nonneg d))
  have h2 : T ⊆ Fintype.piFinset (fun _ : Fin d => Finset.Icc (-⌈M⌉) ⌈M⌉) := by
    intro z hz
    rw [Fintype.mem_piFinset]
    intro k
    rw [Finset.mem_Icc]
    have hk : |(z k : ℝ)| < M := by
      have h := abs_coord_le_radius (physical 1 z) k
      have e : physical 1 z k = (z k : ℝ) := by simp [physical]
      rw [e] at h
      exact h.trans_lt (hT z hz).2
    have hc : |(z k : ℝ)| ≤ (⌈M⌉ : ℝ) := hk.le.trans (Int.le_ceil M)
    rw [← Int.cast_abs] at hc
    have hc' : |z k| ≤ ⌈M⌉ := by exact_mod_cast hc
    exact abs_le.mp hc'
  calc ∑ z ∈ T, Real.rpow (radius (physical 1 z)) (-(d : ℝ))
      ≤ ∑ _z ∈ T, (1 : ℝ) := Finset.sum_le_sum h1
    _ = (T.card : ℝ) := by simp
    _ ≤ ((Fintype.piFinset (fun _ : Fin d => Finset.Icc (-⌈M⌉) ⌈M⌉)).card : ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card h2)

/-- The outer radius ratio is at most `R · 4/(3√d)` once `R ≥ 3√d`, so its log is `log R` plus a
constant. -/
lemma log_outer_le {d : ℕ} (hd : 1 ≤ d) {R : ℝ} (hR : 3 * Real.sqrt d ≤ R) :
    Real.log ((R + Real.sqrt d / 2) / (3 * Real.sqrt d / 2)) ≤
      Real.log R + Real.log (4 / (3 * Real.sqrt d)) := by
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
  have hRpos : 0 < R := by linarith
  have h3s : 0 < 3 * Real.sqrt d := by linarith
  have h32 : 0 < 3 * Real.sqrt d / 2 := by linarith
  have hc : 4 / (3 * Real.sqrt d) ≠ 0 := (div_pos (by norm_num) h3s).ne'
  have hle : (R + Real.sqrt d / 2) / (3 * Real.sqrt d / 2) ≤ R * (4 / (3 * Real.sqrt d)) := by
    rw [div_le_iff₀ h32]
    have hsne : Real.sqrt d ≠ 0 := hs.ne'
    have e : R * (4 / (3 * Real.sqrt d)) * (3 * Real.sqrt d / 2) = 2 * R := by
      field_simp
      ring
    rw [e]
    linarith
  have hpos : 0 < (R + Real.sqrt d / 2) / (3 * Real.sqrt d / 2) :=
    div_pos (by linarith) h32
  calc Real.log ((R + Real.sqrt d / 2) / (3 * Real.sqrt d / 2))
      ≤ Real.log (R * (4 / (3 * Real.sqrt d))) := Real.log_le_log hpos hle
    _ = Real.log R + Real.log (4 / (3 * Real.sqrt d)) := Real.log_mul hRpos.ne' hc

/-- For `0 ≤ s ≤ R`, `R · (5s/2) ≤ (R - s/2) · (5s)`, since the difference is
`(5/2) s (R - s) ≥ 0`. -/
private lemma cross_mul_le_inner {R s : ℝ} (hs : 0 ≤ s) (hsR : s ≤ R) :
    R * (5 * s / 2) ≤ (R - s / 2) * (5 * s) := by
  calc R * (5 * s / 2) = (R - s / 2) * (5 * s) - 5 / 2 * (s * (R - s)) := by ring
    _ ≤ (R - s / 2) * (5 * s) :=
      sub_le_self _ (mul_nonneg (by norm_num) (mul_nonneg hs (by linarith)))

/-- The inner radius ratio is at least `R/(5√d)` once `R ≥ 3√d`, so its log is `log R` minus a
constant. -/
lemma log_inner_ge {d : ℕ} (hd : 1 ≤ d) {R : ℝ} (hR : 3 * Real.sqrt d ≤ R) :
    Real.log R - Real.log (5 * Real.sqrt d) ≤
      Real.log ((R - Real.sqrt d / 2) / (5 * Real.sqrt d / 2)) := by
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
  have hRpos : 0 < R := by linarith
  have h5 : 0 < 5 * Real.sqrt d := by linarith
  have h52 : 0 < 5 * Real.sqrt d / 2 := by linarith
  have hle : R / (5 * Real.sqrt d) ≤ (R - Real.sqrt d / 2) / (5 * Real.sqrt d / 2) := by
    rw [div_le_div_iff₀ h5 h52]
    exact cross_mul_le_inner hs.le (by linarith)
  rw [← Real.log_div hRpos.ne' h5.ne']
  exact Real.log_le_log (div_pos hRpos h5) hle

/-- **Uniform critical asymptotic.** The discrete asymptotic
`∑_{z ∈ unitBallIndices d (1/R)} |z|^{-d} = d · unitBallVolume d · log R + O(1)`
holds uniformly for `R ≥ 2`: one constant `K(d)` bounds the error for every such `R`. -/
theorem shell_sum_asymp {d : ℕ} (hd : 1 ≤ d) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ R : ℝ, 2 ≤ R →
      |(∑ z ∈ unitBallIndices d (1 / R), Real.rpow (radius (physical 1 z)) (-(d : ℝ)))
        - (d : ℝ) * unitBallVolume d * Real.log R| ≤ K := by
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
  have hD : 0 ≤ (d : ℝ) * unitBallVolume d :=
    mul_nonneg (Nat.cast_nonneg d) (unitBallVolume_pos d).le
  have hC1 : 0 ≤ comparisonConstant d * radialErrorConstant d :=
    mul_nonneg (comparisonConstant_nonneg d) (radialErrorConstant_nonneg d)
  have hK3 : (0 : ℝ) ≤ ((Fintype.piFinset
      (fun _ : Fin d => Finset.Icc (-⌈3 * Real.sqrt d⌉) ⌈3 * Real.sqrt d⌉)).card : ℝ) :=
    Nat.cast_nonneg _
  have hA : 0 ≤ (d : ℝ) * unitBallVolume d * |Real.log (4 / (3 * Real.sqrt d))| :=
    mul_nonneg hD (abs_nonneg _)
  have hB : 0 ≤ (d : ℝ) * unitBallVolume d * |Real.log (5 * Real.sqrt d)| :=
    mul_nonneg hD (abs_nonneg _)
  have hC : 0 ≤ (d : ℝ) * unitBallVolume d * |Real.log (3 * Real.sqrt d)| :=
    mul_nonneg hD (abs_nonneg _)
  refine ⟨comparisonConstant d * radialErrorConstant d
      + (d : ℝ) * unitBallVolume d * |Real.log (4 / (3 * Real.sqrt d))|
      + (d : ℝ) * unitBallVolume d * |Real.log (5 * Real.sqrt d)|
      + ((Fintype.piFinset
          (fun _ : Fin d => Finset.Icc (-⌈3 * Real.sqrt d⌉) ⌈3 * Real.sqrt d⌉)).card : ℝ)
      + (d : ℝ) * unitBallVolume d * |Real.log (3 * Real.sqrt d)|, by linarith, ?_⟩
  intro R hR2
  have hRpos : 0 < R := by linarith
  have hlogR0 : 0 ≤ Real.log R := Real.log_nonneg (by linarith)
  have hDlog : 0 ≤ (d : ℝ) * unitBallVolume d * Real.log R := mul_nonneg hD hlogR0
  have hdisj := disjoint_cube_integral_inequality d hd R
  have hSI : |(∑ w ∈ latticeAnnulus d R, Real.rpow (radius (physical 1 w)) (-(d : ℝ)))
      - ∫ x in cubeUnion d R, Real.rpow (radius x) (-(d : ℝ))|
      ≤ comparisonConstant d * radialErrorConstant d :=
    le_trans hdisj.1 hdisj.2
  rcases lt_or_ge R (3 * Real.sqrt d) with hRlt | hR3
  · -- Case `2 ≤ R < 3√d`: every point of `unitBallIndices d (1/R)` has radius below `3√d`.
    have hT : ∀ z ∈ unitBallIndices d (1 / R),
        z ≠ 0 ∧ radius (physical 1 z) < 3 * Real.sqrt d := by
      intro z hz
      obtain ⟨hz0, hz1⟩ := (mem_unitBallIndices (one_div_pos.mpr hRpos) z).mp hz
      rw [radius_physical_eq_mul (one_div_pos.mpr hRpos).le z] at hz1
      exact ⟨hz0, lt_of_le_of_lt ((one_div_mul_le_one_iff hRpos).mp hz1) hRlt⟩
    have hsum := sum_rpow_le_box_card (d := d) (M := 3 * Real.sqrt d) _ hT
    have hsum0 : 0 ≤ ∑ z ∈ unitBallIndices d (1 / R),
        Real.rpow (radius (physical 1 z)) (-(d : ℝ)) :=
      Finset.sum_nonneg (fun z _ => Real.rpow_nonneg (radius_nonneg _) _)
    have hlogle : Real.log R ≤ Real.log (3 * Real.sqrt d) := Real.log_le_log hRpos hRlt.le
    have hlogle' : (d : ℝ) * unitBallVolume d * Real.log R
        ≤ (d : ℝ) * unitBallVolume d * |Real.log (3 * Real.sqrt d)| :=
      le_trans (mul_le_mul_of_nonneg_left hlogle hD)
        (mul_le_mul_of_nonneg_left (le_abs_self _) hD)
    rw [abs_le]
    constructor <;> linarith
  · -- Case `R ≥ 3√d`: split off the points of radius below `2√d`, which lie in a fixed box.
    have hsplit : (∑ z ∈ latticeAnnulus d R, Real.rpow (radius (physical 1 z)) (-(d : ℝ)))
        + (∑ z ∈ (unitBallIndices d (1 / R)).filter
            (fun z => ¬ (2 * Real.sqrt d ≤ radius (physical 1 z))),
          Real.rpow (radius (physical 1 z)) (-(d : ℝ)))
        = ∑ z ∈ unitBallIndices d (1 / R), Real.rpow (radius (physical 1 z)) (-(d : ℝ)) := by
      rw [← unitBallIndices_filter_eq_latticeAnnulus hd hRpos]
      exact Finset.sum_filter_add_sum_filter_not _ _ _
    have hrest0 : 0 ≤ ∑ z ∈ (unitBallIndices d (1 / R)).filter
        (fun z => ¬ (2 * Real.sqrt d ≤ radius (physical 1 z))),
          Real.rpow (radius (physical 1 z)) (-(d : ℝ)) :=
      Finset.sum_nonneg (fun z _ => Real.rpow_nonneg (radius_nonneg _) _)
    have hrest : ∑ z ∈ (unitBallIndices d (1 / R)).filter
        (fun z => ¬ (2 * Real.sqrt d ≤ radius (physical 1 z))),
          Real.rpow (radius (physical 1 z)) (-(d : ℝ))
        ≤ ((Fintype.piFinset
            (fun _ : Fin d => Finset.Icc (-⌈3 * Real.sqrt d⌉) ⌈3 * Real.sqrt d⌉)).card : ℝ) := by
      apply sum_rpow_le_box_card
      intro z hz
      obtain ⟨hz1, hz2⟩ := Finset.mem_filter.mp hz
      have hne : z ≠ 0 := ((mem_unitBallIndices (one_div_pos.mpr hRpos) z).mp hz1).1
      have hlt : radius (physical 1 z) < 3 * Real.sqrt d := by
        have h2 := not_le.mp hz2
        linarith
      exact ⟨hne, hlt⟩
    have hU := integral_cubeUnion_le hd (show Real.sqrt d ≤ R by linarith)
    have hL := integral_cubeUnion_ge hd hR3
    have hU' := mul_le_mul_of_nonneg_left (log_outer_le hd hR3) hD
    have hL' := mul_le_mul_of_nonneg_left (log_inner_ge hd hR3) hD
    have hAa : (d : ℝ) * unitBallVolume d * Real.log (4 / (3 * Real.sqrt d))
        ≤ (d : ℝ) * unitBallVolume d * |Real.log (4 / (3 * Real.sqrt d))| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hD
    have hBb : (d : ℝ) * unitBallVolume d * Real.log (5 * Real.sqrt d)
        ≤ (d : ℝ) * unitBallVolume d * |Real.log (5 * Real.sqrt d)| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hD
    have hSI' := abs_le.mp hSI
    rw [abs_le]
    constructor <;> linarith

end LatticeProb.Euclidean.Asymptotic
