/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.Lemma38Source.Numerics at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.Lemma38Source.Admissible

/-!
# Exponent choices and uniform numerical bounds for Lemma 3.8

The small inner-scale exponent is chosen once from `q` and G4's test-growth
and failure exponents. The choice is intentionally stricter than the corrected
`β ≤ α₁/4`; it also leaves room for G3's explicit error terms.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Set Metric Real Filter
open scoped ENNReal Topology

namespace MatedCRTHarmonic.Lemma38Source

/-- One explicit source-faithful choice of the Lemma 3.8 scale exponent and
the boundary-layer width exponent. -/
theorem chooseScaleExponents {q betaG4 alphaG4 : ℝ}
    (hq : 0 < q) (hq1 : q < 1)
    (hbeta : 0 < betaG4) (halpha : 0 < alphaG4) :
    ∃ β β' : ℝ,
      0 < β ∧ β ≤ 1 ∧ 0 < β' ∧
      6 * β ≤ betaG4 ∧
      40 * β ≤ q ∧ 20 * β ≤ β' ∧ 20 * β ≤ alphaG4 ∧
      β' ≤ q ∧ β' ≤ betaG4 ∧ β ≤ alphaG4 / 4 := by
  let m := min q betaG4
  let β : ℝ := min m alphaG4 / 100
  let β' : ℝ := m / 2
  have hm : 0 < m := lt_min hq hbeta
  have hβ : 0 < β := by dsimp [β]; exact div_pos (lt_min hm halpha) (by norm_num)
  have hβ' : 0 < β' := by dsimp [β']; linarith
  have hmQ : m ≤ q := min_le_left _ _
  have hmB : m ≤ betaG4 := min_le_right _ _
  have hβm : 100 * β ≤ m := by dsimp [β]; linarith [min_le_left m alphaG4]
  have hβα : 100 * β ≤ alphaG4 := by dsimp [β]; linarith [min_le_right m alphaG4]
  refine ⟨β, β', hβ, ?_, hβ', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · dsimp [β']; linarith
  · linarith
  · dsimp [β']; linarith
  · dsimp [β']; linarith
  · linarith

/-- Positive powers of the dyadic mesh become smaller than any fixed positive
geometric margin. -/
theorem eventually_meshPow_lt {a c : ℝ} (ha : 0 < a) (hc : 0 < c) :
    ∀ᶠ k : ℕ in atTop, CellFamily.mesh k ^ a < c := by
  have hp : Tendsto (fun k : ℕ => (2 : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hi : Tendsto (fun k : ℕ => ((2 : ℝ) ^ k)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hp
  have hm : Tendsto CellFamily.mesh atTop (𝓝 0) := by
    convert hi using 1
    ext k
    simp [CellFamily.mesh, zpow_neg]
  have hcont : ContinuousAt (fun x : ℝ => x ^ a) 0 :=
    Real.continuousAt_rpow_const 0 a (Or.inr ha.le)
  have hzero : Tendsto (fun k : ℕ => CellFamily.mesh k ^ a) atTop (𝓝 0) := by
    simpa [Function.comp_def, Real.zero_rpow ha.ne'] using hcont.tendsto.comp hm
  exact hzero.eventually (Iio_mem_nhds hc)

/-- A source-scale error with exponent at least `20β` is at most the tenth
power of the inner radius `ι = s*r`. This is uniform over all representatives
and all radii above the mesh cutoff. -/
theorem meshPow_le_innerPowTen {ε s r β a : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hs : ε ^ β ≤ s) (hr : ε ^ β ≤ r)
    (ha : 20 * β ≤ a) : ε ^ a ≤ (s * r) ^ 10 := by
  have hb : 0 ≤ ε ^ β := Real.rpow_nonneg hε.le β
  have hprod : ε ^ (2 * β) ≤ s * r := by
    rw [show 2 * β = β + β by ring, Real.rpow_add hε]
    exact mul_le_mul hs hr hb (hb.trans hs)
  have hpow : (ε ^ (2 * β)) ^ 10 ≤ (s * r) ^ 10 :=
    pow_le_pow_left₀ (Real.rpow_nonneg hε.le _) hprod _
  calc
    ε ^ a ≤ ε ^ (20 * β) :=
      Real.rpow_le_rpow_of_exponent_ge hε hε1 ha
    _ = (ε ^ (2 * β)) ^ 10 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]
      congr 1
      ring
    _ ≤ (s * r) ^ 10 := hpow

/-- The energy input in (3.19) has quadratic inner-radius growth. -/
theorem lemma38K_le_quadratic {ι w A η : ℝ}
    (hι : 0 < ι) (hι1 : ι ≤ 1)
    (hw : 0 ≤ w) (hwι : w ≤ ι ^ 10)
    (hA : 0 ≤ A) (hη : 0 ≤ η) (hηι : η ≤ ι ^ 10) :
    GMS3.lemma38K ι w (2 * A) η ≤ 2000 * (A + 1) * ι ^ 2 := by
  have hι0 : 0 ≤ ι := hι.le
  have hι2 : ι ^ 2 ≤ 1 := by nlinarith
  have hι10 : ι ^ 10 ≤ ι ^ 2 := by
    calc
      ι ^ 10 = ι ^ 2 * (ι ^ 2) ^ 4 := by ring
      _ ≤ ι ^ 2 * 1 := by
        apply mul_le_mul_of_nonneg_left
        exact pow_le_one₀ (by positivity) hι2
        positivity
      _ = ι ^ 2 := by ring
  have hw2 : w ≤ ι ^ 2 := hwι.trans hι10
  have hη2 : η ≤ ι ^ 2 := hηι.trans hι10
  have hwι' : w * ι ≤ ι ^ 2 := by
    calc
      w * ι ≤ ι * ι := mul_le_mul_of_nonneg_right (by nlinarith [hw2]) hι0
      _ = ι ^ 2 := by ring
  have hww : w * w ≤ ι ^ 2 := by
    calc
      w * w ≤ ι * ι := mul_self_le_mul_self (by nlinarith [hw2])
        (by nlinarith [hw2])
      _ = ι ^ 2 := by ring
  have hπ : 0 ≤ Real.pi := Real.pi_pos.le
  have hπ4 : Real.pi ≤ 4 := Real.pi_le_four
  have hpoly : w * (ι / 2 + 2 * w) + w * (9 * ι + 2 * w) ≤
      14 * ι ^ 2 := by nlinarith [hwι', hww]
  have hpoly0 : 0 ≤ w * (ι / 2 + 2 * w) + w * (9 * ι + 2 * w) := by
    positivity
  have hterm :
      Real.pi * (9 * ι) ^ 2 ≤ 324 * ι ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 4 - Real.pi by linarith) (sq_nonneg ι)]
  have hlayer :
      8 * Real.pi * w * (ι / 2 + 2 * w) +
      8 * Real.pi * w * (9 * ι + 2 * w) ≤ 448 * ι ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ 4 - Real.pi by linarith) hpoly0,
      mul_nonneg hπ (show 0 ≤ 14 * ι ^ 2 -
        (w * (ι / 2 + 2 * w) + w * (9 * ι + 2 * w)) by linarith)]
  unfold GMS3.lemma38K
  nlinarith [mul_nonneg hA (show 0 ≤ 324 * ι ^ 2 - Real.pi * (9 * ι) ^ 2 by linarith),
    mul_nonneg hA (show 0 ≤ 448 * ι ^ 2 -
      (8 * Real.pi * w * (ι / 2 + 2 * w) +
        8 * Real.pi * w * (9 * ι + 2 * w)) by linarith),
    mul_nonneg (show 0 ≤ A by exact hA) (sq_nonneg ι)]

/-- Elementary normalized error margins implied by a tenth-power bound. -/
theorem normalizedMargins {ι δ w η : ℝ}
    (hι : 0 < ι) (hι1 : ι ≤ 1)
    (hδ : 0 ≤ δ) (hδι : δ ≤ ι ^ 10)
    (hw : 0 ≤ w) (hwι : w ≤ ι ^ 10)
    (hη : 0 ≤ η) (hηι : η ≤ ι ^ 10) :
    δ / ι ^ 3 ≤ 1 ∧ δ / ι ^ 2 ≤ 1 ∧
    w / ι ≤ 1 ∧ w / ι ^ 2 ≤ 1 ∧
    η / ι ^ 2 ≤ 1 ∧ η / ι ≤ 1 := by
  have hι0 : 0 ≤ ι := hι.le
  have hp (n : ℕ) (hn : n ≤ 10) : ι ^ 10 ≤ ι ^ n :=
    pow_le_pow_of_le_one hι0 hι1 hn
  have hι2 : 0 < ι ^ 2 := pow_pos hι _
  have hι3 : 0 < ι ^ 3 := pow_pos hι _
  constructor
  · exact (div_le_one hι3).mpr (hδι.trans (hp 3 (by omega)))
  constructor
  · exact (div_le_one hι2).mpr (hδι.trans (hp 2 (by omega)))
  constructor
  · exact (div_le_one hι).mpr (by simpa only [pow_one] using hwι.trans (hp 1 (by omega)))
  constructor
  · exact (div_le_one hι2).mpr (hwι.trans (hp 2 (by omega)))
  constructor
  · exact (div_le_one hι2).mpr (hηι.trans (hp 2 (by omega)))
  · exact (div_le_one hι).mpr (by simpa only [pow_one] using hηι.trans (hp 1 (by omega)))

/-- The logarithm of the annulus aspect ratio lies between `1` and `1/ι`.
The upper bound controls the tolerance term in Lemma 3.4. -/
theorem annulusLogMargins {ι r : ℝ}
    (hι : 0 < ι) (h10 : 10 * ι ≤ r) (hr1 : r ≤ 1) :
    1 ≤ Real.log (r / ι) ∧ Real.log (r / ι) ≤ ι⁻¹ := by
  have hr : 0 < r := by linarith
  have hratio : 10 ≤ r / ι := (le_div_iff₀ hι).mpr (by linarith)
  have hlog10 : 1 ≤ Real.log 10 := by
    have he : Real.exp 1 < 10 := Real.exp_one_lt_three.trans (by norm_num)
    have h := Real.log_le_log (Real.exp_pos _) he.le
    simpa only [Real.log_exp] using h
  have hloglo : 1 ≤ Real.log (r / ι) :=
    hlog10.trans (Real.log_le_log (by norm_num) hratio)
  have hratioUp : r / ι ≤ ι⁻¹ := by
    rw [div_eq_mul_inv]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hr1 (inv_nonneg.mpr hι.le)
  have hlogUp : Real.log (r / ι) ≤ Real.log ι⁻¹ :=
    Real.log_le_log (by positivity) hratioUp
  have hlogInv : Real.log ι⁻¹ ≤ ι⁻¹ := by
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hι)
    linarith
  exact ⟨hloglo, hlogUp.trans hlogInv⟩

/-- The explicit Lemma 3.4 energy error is controlled by the inverse
annulus logarithm, uniformly in both radii. -/
theorem lemma34Bound_le_inverseLog {ι r δ w A η : ℝ}
    (hι : 0 < ι) (h10 : 10 * ι ≤ r) (hr1 : r ≤ 1)
    (hδ : 0 ≤ δ) (hδι : δ ≤ ι ^ 10)
    (hw : 0 ≤ w) (hwι : w ≤ ι ^ 10)
    (hA : 0 ≤ A) (hη : 0 ≤ η) (hηι : η ≤ ι ^ 10) :
    GMS3.lemma34Bound ι r δ w (2 * A) η ≤
      200000 * (A + 1) / Real.log (r / ι) := by
  let L := Real.log (r / ι)
  have hL1 : 1 ≤ L := (annulusLogMargins hι h10 hr1).1
  have hLup : L ≤ ι⁻¹ := (annulusLogMargins hι h10 hr1).2
  have hLpos : 0 < L := by linarith
  have hι1 : ι ≤ 1 := by linarith
  have hnorm := normalizedMargins hι hι1 hδ hδι hw hwι hη hηι
  have hδ3 : 0 ≤ δ / ι ^ 3 := div_nonneg hδ (pow_nonneg hι.le _)
  have hδ2 : 0 ≤ δ / ι ^ 2 := div_nonneg hδ (pow_nonneg hι.le _)
  have hw1 : 0 ≤ w / ι := div_nonneg hw hι.le
  have hw2 : 0 ≤ w / ι ^ 2 := div_nonneg hw (pow_nonneg hι.le _)
  have hη2 : 0 ≤ η / ι ^ 2 := div_nonneg hη (pow_nonneg hι.le _)
  have hLinv0 : 0 ≤ L⁻¹ := inv_nonneg.mpr hLpos.le
  have hLinv1 : L⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hL1
  have hLsq : (L⁻¹) ^ 2 ≤ L⁻¹ := by nlinarith [sq_nonneg L⁻¹]
  have hι10 : ι ^ 10 ≤ ι := by
    simpa only [pow_one] using
      (pow_le_pow_of_le_one hι.le hι1 (show (1 : ℕ) ≤ 10 by omega))
  have hLη : L * η ≤ 1 := by
    have h := mul_le_mul hLup (hηι.trans hι10) hη (inv_nonneg.mpr hι.le)
    nlinarith [inv_mul_cancel₀ hι.ne']
  have hηL : η ≤ L⁻¹ := by
    simpa only [one_div] using
      ((le_div_iff₀ hLpos).mpr (by simpa only [mul_comm] using hLη) : η ≤ 1 / L)
  have hr : 0 < r := by linarith
  have hr2 : r ^ 2 ≤ 1 := by nlinarith
  have hπ : 0 ≤ Real.pi := Real.pi_pos.le
  have hπ4 : Real.pi ≤ 4 := Real.pi_le_four
  have hπr : Real.pi * r ^ 2 ≤ 4 := by
    nlinarith [mul_nonneg (show 0 ≤ 4 - Real.pi by linarith) (sq_nonneg r),
      mul_nonneg hπ (show 0 ≤ 1 - r ^ 2 by linarith)]
  have hwle : w ≤ 1 := by
    exact hwι.trans (pow_le_one₀ hι.le hι1)
  have hιw : w * (ι + 2 * w) + w * (r + 2 * w) ≤ 6 := by
    have hww : w * w ≤ 1 := by
      nlinarith [pow_le_pow_left₀ hw hwle 2]
    nlinarith [mul_nonneg hw (show 0 ≤ 1 - ι by linarith),
      mul_nonneg hw (show 0 ≤ 1 - r by linarith),
      hww]
  have hιw0 : 0 ≤ w * (ι + 2 * w) + w * (r + 2 * w) := by positivity
  have hvol : 8 * Real.pi * w * (ι + 2 * w) +
      8 * Real.pi * w * (r + 2 * w) ≤ 192 := by
    nlinarith [mul_nonneg (show 0 ≤ 4 - Real.pi by linarith) hιw0,
      mul_nonneg hπ (show 0 ≤ 6 -
        (w * (ι + 2 * w) + w * (r + 2 * w)) by linarith)]
  have hvol0 : 0 ≤ 8 * Real.pi * w * (ι + 2 * w) +
      8 * Real.pi * w * (r + 2 * w) := by positivity
  have hU : w / ι + 4 * (w / ι) ^ 2 + r * (w / ι ^ 2) ≤ 6 := by
    have hUsq : (w / ι) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (w / ι)]
    have hUr : r * (w / ι ^ 2) ≤ 1 := by
      nlinarith [mul_nonneg (show 0 ≤ 1 - r by linarith) hw2,
        mul_nonneg hr.le (show 0 ≤ 1 - w / ι ^ 2 by linarith [hnorm.2.2.2.1])]
    linarith [hnorm.2.2.1]
  have hU0 : 0 ≤ w / ι + 4 * (w / ι) ^ 2 + r * (w / ι ^ 2) := by positivity
  have hbracket1 : 0 ≤ (2 * A) * (Real.pi * r ^ 2) + η := by positivity
  have hbracket1_le : (2 * A) * (Real.pi * r ^ 2) + η ≤ 8 * A + 1 := by
    have hη1 : η ≤ 1 := hηι.trans (pow_le_one₀ hι.le hι1)
    nlinarith [mul_nonneg hA (show 0 ≤ 4 - Real.pi * r ^ 2 by linarith)]
  have hbracket2 : 0 ≤ (2 * A) * (8 * Real.pi) *
      (w / ι + 4 * (w / ι) ^ 2 + r * (w / ι ^ 2)) + η / ι ^ 2 := by positivity
  have hbracket2_le : (2 * A) * (8 * Real.pi) *
      (w / ι + 4 * (w / ι) ^ 2 + r * (w / ι ^ 2)) + η / ι ^ 2 ≤
      384 * A + 1 := by
    nlinarith [mul_nonneg hA (show 0 ≤ 4 - Real.pi by linarith),
      mul_nonneg (mul_nonneg hA hπ) (show 0 ≤ 6 -
        (w / ι + 4 * (w / ι) ^ 2 + r * (w / ι ^ 2)) by linarith), hnorm.2.2.2.2.1]
  have hbracket3 : 0 ≤ (2 * A) * (Real.pi * r ^ 2) + η +
      ((2 * A) * (8 * Real.pi * w * (ι + 2 * w) +
        8 * Real.pi * w * (r + 2 * w)) + η) := by positivity
  have hbracket3_le : (2 * A) * (Real.pi * r ^ 2) + η +
      ((2 * A) * (8 * Real.pi * w * (ι + 2 * w) +
        8 * Real.pi * w * (r + 2 * w)) + η) ≤ 392 * A + 2 := by
    have hη1 : η ≤ 1 := hηι.trans (pow_le_one₀ hι.le hι1)
    nlinarith [mul_nonneg hA (show 0 ≤ 4 - Real.pi * r ^ 2 by linarith),
      mul_nonneg hA (show 0 ≤ 192 -
        (8 * Real.pi * w * (ι + 2 * w) +
          8 * Real.pi * w * (r + 2 * w)) by linarith)]
  have hδ2sq : (δ / ι ^ 2) ^ 2 ≤ 1 := by nlinarith [sq_nonneg (δ / ι ^ 2)]
  have hδ2sq0 : 0 ≤ (δ / ι ^ 2) ^ 2 := sq_nonneg _
  rw [GMS3.lemma34Bound_eq hι (by exact hLpos.ne'), show Real.log (r / ι) = L by rfl]
  have hT1 : 3 * (2 * A) * (2 * Real.pi) * L⁻¹ ≤ 48 * A * L⁻¹ := by
    have hcoef : 3 * (2 * A) * (2 * Real.pi) ≤ 48 * A := by
      nlinarith [mul_nonneg hA (show 0 ≤ 4 - Real.pi by linarith)]
    exact mul_le_mul_of_nonneg_right hcoef hLinv0
  have hT2 : 3 * η ≤ 3 * L⁻¹ := by linarith
  have hT3 : 6 * L⁻¹ ^ 2 * (δ / ι ^ 3) *
      ((2 * A) * (Real.pi * r ^ 2) + η) ≤
      6 * L⁻¹ * (8 * A + 1) := by
    have hprod : (δ / ι ^ 3) * ((2 * A) * (Real.pi * r ^ 2) + η) ≤
        8 * A + 1 := by
      simpa only [one_mul] using
        (mul_le_mul hnorm.1 hbracket1_le hbracket1 (by norm_num))
    calc
      _ = 6 * L⁻¹ ^ 2 *
          ((δ / ι ^ 3) * ((2 * A) * (Real.pi * r ^ 2) + η)) := by ring
      _ ≤ 6 * L⁻¹ ^ 2 * (8 * A + 1) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
      _ ≤ 6 * L⁻¹ * (8 * A + 1) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hLsq (by norm_num)) (by positivity)
  have hT4 : 12 * L⁻¹ ^ 2 *
      ((2 * A) * (8 * Real.pi) *
        (w / ι + 4 * (w / ι) ^ 2 + r * (w / ι ^ 2)) + η / ι ^ 2) ≤
      12 * L⁻¹ * (384 * A + 1) := by
    calc
      _ ≤ 12 * L⁻¹ ^ 2 * (384 * A + 1) :=
        mul_le_mul_of_nonneg_left hbracket2_le (by positivity)
      _ ≤ 12 * L⁻¹ * (384 * A + 1) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hLsq (by norm_num)) (by positivity)
  have hT5 : 384 * L⁻¹ ^ 2 * (δ / ι ^ 2) ^ 2 *
      (((2 * A) * (Real.pi * r ^ 2) + η) +
        ((2 * A) * (8 * Real.pi * w * (ι + 2 * w) +
          8 * Real.pi * w * (r + 2 * w)) + η)) ≤
      384 * L⁻¹ * (392 * A + 2) := by
    have hprod : (δ / ι ^ 2) ^ 2 *
        (((2 * A) * (Real.pi * r ^ 2) + η) +
          ((2 * A) * (8 * Real.pi * w * (ι + 2 * w) +
            8 * Real.pi * w * (r + 2 * w)) + η)) ≤ 392 * A + 2 := by
      simpa only [one_mul] using
        (mul_le_mul hδ2sq hbracket3_le hbracket3 (by norm_num))
    calc
      _ = 384 * L⁻¹ ^ 2 * ((δ / ι ^ 2) ^ 2 *
          (((2 * A) * (Real.pi * r ^ 2) + η) +
            ((2 * A) * (8 * Real.pi * w * (ι + 2 * w) +
              8 * Real.pi * w * (r + 2 * w)) + η))) := by ring
      _ ≤ 384 * L⁻¹ ^ 2 * (392 * A + 2) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
      _ ≤ 384 * L⁻¹ * (392 * A + 2) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hLsq (by norm_num)) (by positivity)
  apply le_trans (add_le_add (add_le_add (add_le_add (add_le_add hT1 hT2) hT3) hT4) hT5)
  rw [div_eq_mul_inv]
  nlinarith [mul_nonneg hA hLinv0]

/-- Square-root absorption for the two deterministic Lemma 3.8 bounds. -/
theorem sqrtProduct_le_inverseSqrt {K E ι L A : ℝ}
    (hK0 : 0 ≤ K) (hE0 : 0 ≤ E) (hι : 0 < ι)
    (hL : 0 < L) (hA : 0 ≤ A)
    (hK : K ≤ 2000 * (A + 1) * ι ^ 2)
    (hE : E ≤ 200000 * (A + 1) / L) :
    6 * Real.sqrt K * Real.sqrt E / ι ≤
      120000 * (A + 1) / Real.sqrt L := by
  have hEL : E * L ≤ 200000 * (A + 1) := (le_div_iff₀ hL).mp hE
  have hKEL : K * (E * L) ≤
      (2000 * (A + 1) * ι ^ 2) * (200000 * (A + 1)) := by
    exact mul_le_mul hK hEL (by positivity) (by positivity)
  have hS : 0 < Real.sqrt L := Real.sqrt_pos.2 hL
  let X := Real.sqrt K * Real.sqrt E * Real.sqrt L
  have hX0 : 0 ≤ X := by dsimp [X]; positivity
  have hXsq : X ^ 2 = K * (E * L) := by
    dsimp [X]
    rw [mul_pow, mul_pow, Real.sq_sqrt hK0, Real.sq_sqrt hE0,
      Real.sq_sqrt hL.le]
    ring
  have hB0 : 0 ≤ 20000 * (A + 1) * ι := by positivity
  have hX : X ≤ 20000 * (A + 1) * ι := by
    have hs : X ^ 2 ≤ (20000 * (A + 1) * ι) ^ 2 := by
      rw [hXsq]
      nlinarith [hKEL]
    nlinarith
  apply (div_le_div_iff₀ hι hS).mpr
  dsimp [X] at hX
  nlinarith [hX]

/-- The exact G3 error term, with `κ = 1/√log(r/ι)`, has the target
inverse-square-root logarithmic form. -/
theorem lemma38Error_le_inverseSqrt {ι r δ w A η : ℝ}
    (hι : 0 < ι) (h10 : 10 * ι ≤ r) (hr1 : r ≤ 1)
    (hδ : 0 ≤ δ) (hδι : δ ≤ ι ^ 10)
    (hw : 0 ≤ w) (hwι : w ≤ ι ^ 10)
    (hA : 0 ≤ A) (hη : 0 ≤ η) (hηι : η ≤ ι ^ 10) :
    6 * Real.sqrt (GMS3.lemma38K ι w (2 * A) η) *
        Real.sqrt (GMS3.lemma34Bound ι r δ w (2 * A) η) / ι +
      2 * (Real.sqrt (Real.log (r / ι)))⁻¹ ≤
      120002 * (A + 1) / Real.sqrt (Real.log (r / ι)) := by
  have hL := (annulusLogMargins hι h10 hr1).1
  have hLpos : 0 < Real.log (r / ι) := by linarith
  have hr : 0 < r := by linarith
  have hιr : ι < r := by linarith
  have hι1 : ι ≤ 1 := by linarith
  have hK0 : 0 ≤ GMS3.lemma38K ι w (2 * A) η := by
    unfold GMS3.lemma38K
    positivity
  have hE0 : 0 ≤ GMS3.lemma34Bound ι r δ w (2 * A) η :=
    GMS3.lemma34Bound_nonneg hι hιr hδ hw (by positivity) hη
  have hprod := sqrtProduct_le_inverseSqrt hK0 hE0 hι hLpos hA
    (lemma38K_le_quadratic hι hι1 hw hwι hA hη hηι)
    (lemma34Bound_le_inverseLog hι h10 hr1 hδ hδι hw hwι hA hη hηι)
  have hS : 0 < Real.sqrt (Real.log (r / ι)) := Real.sqrt_pos.2 hLpos
  calc
    _ ≤ 120000 * (A + 1) / Real.sqrt (Real.log (r / ι)) +
        2 / Real.sqrt (Real.log (r / ι)) := by
      simpa only [div_eq_mul_inv] using
        (add_le_add hprod (le_refl (2 * (Real.sqrt (Real.log (r / ι)))⁻¹)))
    _ = (120000 * (A + 1) + 2) / Real.sqrt (Real.log (r / ι)) := by ring
    _ ≤ 120002 * (A + 1) / Real.sqrt (Real.log (r / ι)) := by
      apply div_le_div_of_nonneg_right _ hS.le
      linarith

/-- Compare the representative's deterministic error with the requested
radius anywhere in its `5/4` block. -/
theorem lemma38Error_le_target {s s' r δ w A η : ℝ}
    (hs : 0 < s) (hss' : s ≤ s') (hs'10 : s' ≤ 1 / 10)
    (hr : 0 < r) (hr1 : r ≤ 1)
    (hδ : 0 ≤ δ) (hδι : δ ≤ (s * r) ^ 10)
    (hw : 0 ≤ w) (hwι : w ≤ (s * r) ^ 10)
    (hA : 0 ≤ A) (hη : 0 ≤ η) (hηι : η ≤ (s * r) ^ 10) :
    6 * Real.sqrt (GMS3.lemma38K (s * r) w (2 * A) η) *
        Real.sqrt (GMS3.lemma34Bound (s * r) r δ w (2 * A) η) / (s * r) +
      2 * (Real.sqrt (Real.log (r / (s * r))))⁻¹ ≤
      120002 * (A + 1) / Real.sqrt (Real.log s'⁻¹) := by
  have hs' : 0 < s' := hs.trans_le hss'
  have hs10 : s ≤ 1 / 10 := hss'.trans hs'10
  have hι : 0 < s * r := mul_pos hs hr
  have h10 : 10 * (s * r) ≤ r := by nlinarith
  have hratio : r / (s * r) = s⁻¹ := by field_simp
  have hLpos : 0 < Real.log (r / (s * r)) := by
    have h := (annulusLogMargins hι h10 hr1).1
    linarith
  have hL'pos : 0 < Real.log s'⁻¹ := by
    have hratio' : (10 : ℝ) ≤ s'⁻¹ := by
      simpa only [show (1 / 10 : ℝ)⁻¹ = 10 by norm_num] using
        (inv_anti₀ hs' hs'10)
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 10) hratio'
    have hlog10 : 0 < Real.log 10 := Real.log_pos (by norm_num)
    linarith
  have hL'le : Real.log s'⁻¹ ≤ Real.log (r / (s * r)) := by
    rw [hratio]
    exact Real.log_le_log (inv_pos.mpr hs') (inv_anti₀ hs hss')
  have hS' : 0 < Real.sqrt (Real.log s'⁻¹) := Real.sqrt_pos.2 hL'pos
  have hS : 0 < Real.sqrt (Real.log (r / (s * r))) := Real.sqrt_pos.2 hLpos
  have hinv : (Real.sqrt (Real.log (r / (s * r))))⁻¹ ≤
      (Real.sqrt (Real.log s'⁻¹))⁻¹ :=
    inv_anti₀ hS' (Real.sqrt_le_sqrt hL'le)
  calc
    _ ≤ 120002 * (A + 1) / Real.sqrt (Real.log (r / (s * r))) :=
      lemma38Error_le_inverseSqrt hι h10 hr1 hδ hδι hw hwι hA hη hηι
    _ ≤ 120002 * (A + 1) / Real.sqrt (Real.log s'⁻¹) := by
      simp only [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hinv (by positivity)

end MatedCRTHarmonic.Lemma38Source
