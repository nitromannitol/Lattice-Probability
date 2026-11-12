import Mathlib
import LatticeProb.LQG.LQGOnePieceScaling
import LatticeProb.LQG.LQGNegSmall

/-!
# Self-similar splitting of the mass of a square

Let `T = [-1/8, 1/8]² ⊆ B(0, 1/4)` and `R = 2^{-k}`. Two sub-squares `S_s = z_s + R T`
(`z_0 = -1/16`, `z_1 = 1/16`) are disjoint subsets of `T` with `‖z_s‖ + R ≤ 1` and `|z_0 - z_1| ≥ 2R`.

* `lqgApprox_preimage_dyadic`: for a measurable `A`, `μ_{Rε}(z + R A) = R^{2+γ²/2} e^{γ h_R(z)} μ'_ε(A)`,
  with `μ'` the approximation of the recentred and dilated circle averages.
* `lqgApproxMass_square_ge_sum`: for `n = k + m`,
  `μ_n(T) ≥ ∑_s R^{2+γ²/2} e^{γ h_R(z_s)} μ'^{(s)}_m(T)`.
-/

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal

namespace LatticeProb.LQG

open LatticeProb.Gauss LQGDyadicScaling LatticeProb

/-- **Scaling of the mass of a measurable set.** With `r = 2^{-j}` and `A` measurable,
`μ_{rε}(z + r A) = r^{2+γ²/2} e^{γ h_r(z)} μ'_ε(A)`. -/
theorem lqgApprox_preimage_dyadic {γ : ℝ} (hγ : γ ≠ 0) (h : ℝ → ℂ → ℝ) (j : ℕ) (z : ℂ) {ε : ℝ}
    (hε : 0 ≤ ε) {A : Set ℂ} (hA : MeasurableSet A) :
    lqgApprox γ h (dyadicScale j * ε) ((fun x : ℂ => (x - z) / (dyadicScale j : ℂ)) ⁻¹' A) =
      dyadicFactor γ j (h (dyadicScale j) z) *
        lqgApprox γ (fun s w => h (dyadicScale j * s) ((dyadicScale j : ℂ) * w + z) -
          h (dyadicScale j) z) ε A := by
  have hr := dyadicScale_pos' j
  have h1 := LQGCoordChangeFixed.lqgApprox_dilate_translate hγ h hr hε z
  have e : (fun (s : ℝ) (u : ℂ) => h (dyadicScale j * s) ((dyadicScale j : ℂ) * u + z) +
      lqgQ γ * Real.log (dyadicScale j)) = fun s w =>
        (h (dyadicScale j * s) ((dyadicScale j : ℂ) * w + z) - h (dyadicScale j) z) +
          (h (dyadicScale j) z + lqgQ γ * Real.log (dyadicScale j)) := by
    funext s u; ring
  rw [e, lqgApprox_add_const] at h1
  have h2 := congrArg (fun m : Measure ℂ => m A) h1
  simp only [Measure.smul_apply, smul_eq_mul] at h2
  rw [Measure.map_apply (by fun_prop) hA] at h2
  rw [← h2]
  congr 1
  unfold dyadicFactor
  rw [mul_add, Real.exp_add, LQGCoordChangeFixed.exp_mul_lqgQ_log hγ hr,
    rpow_two_add_half_sq hr, mul_comm (Real.exp _)]

/-- **Scaling of the mass of an indicator.** For `A` measurable and `n = j + m`,
`∫ 1_{z + 2^{-j} A} dμ_n = 2^{-j(2+γ²/2)} e^{γ h_{2^{-j}}(z)} ∫ 1_A dμ'_m`. -/
theorem lqgApproxMass_indicator_preimage_dyadic {γ : ℝ} (hγ : γ ≠ 0) (h : ℝ → ℂ → ℝ) (j m : ℕ)
    (z : ℂ) {A : Set ℂ} (hA : MeasurableSet A) :
    lqgApproxMass γ h (((fun x : ℂ => (x - z) / (dyadicScale j : ℂ)) ⁻¹' A).indicator 1) (j + m) =
      dyadicFactor γ j (h (dyadicScale j) z) *
        lqgApproxMass γ (fun s w => h (dyadicScale j * s) ((dyadicScale j : ℂ) * w + z) -
          h (dyadicScale j) z) (A.indicator 1) m := by
  have hpre : MeasurableSet ((fun x : ℂ => (x - z) / (dyadicScale j : ℂ)) ⁻¹' A) :=
    (by fun_prop : Measurable fun x : ℂ => (x - z) / (dyadicScale j : ℂ)) hA
  unfold lqgApproxMass
  rw [lintegral_indicator_one hpre, lintegral_indicator_one hA, ← dyadicScale_mul_dyadicScale]
  rw [mul_comm (dyadicScale m) (dyadicScale j)]
  exact lqgApprox_preimage_dyadic hγ h j z (dyadicScale_pos' m).le hA

/-- The closed square `[-1/8, 1/8]²`. -/
def lqgSquare : Set ℂ := {w | |w.re| ≤ 1 / 8 ∧ |w.im| ≤ 1 / 8}

theorem measurableSet_lqgSquare : MeasurableSet lqgSquare := by
  have hre : Measurable fun w : ℂ => |w.re| := (Complex.measurable_re).abs
  have him : Measurable fun w : ℂ => |w.im| := (Complex.measurable_im).abs
  exact (measurableSet_le hre measurable_const).inter (measurableSet_le him measurable_const)

theorem lqgSquare_subset_closedBall : lqgSquare ⊆ closedBall (0 : ℂ) (1 / 4) := by
  intro w ⟨h1, h2⟩
  rw [mem_closedBall_zero_iff]
  have := Complex.norm_le_abs_re_add_abs_im w
  linarith

theorem ball_subset_lqgSquare : ball (0 : ℂ) (1 / 8) ⊆ lqgSquare := by
  intro w hw
  rw [mem_ball_zero_iff] at hw
  exact ⟨(Complex.abs_re_le_norm w).trans hw.le, (Complex.abs_im_le_norm w).trans hw.le⟩

theorem volume_lqgSquare_pos : 0 < volume lqgSquare :=
  lt_of_lt_of_le (Metric.measure_ball_pos volume (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 8))
    (measure_mono ball_subset_lqgSquare)

/-- The centres `z_0 = -1/16`, `z_1 = 1/16` of the two sub-squares. -/
noncomputable def lqgSquareCentre (s : Fin 2) : ℂ := ((((s : ℕ) : ℝ) / 8 - 1 / 16 : ℝ) : ℂ)

/-- The sub-square `z_s + 2^{-k} [-1/8, 1/8]²`. -/
def lqgSubSquare (k : ℕ) (s : Fin 2) : Set ℂ :=
  (fun x : ℂ => (x - lqgSquareCentre s) / (dyadicScale k : ℂ)) ⁻¹' lqgSquare

theorem norm_lqgSquareCentre (s : Fin 2) : ‖lqgSquareCentre s‖ = 1 / 16 := by
  unfold lqgSquareCentre
  rw [Complex.norm_real]
  fin_cases s <;> norm_num

theorem dist_lqgSquareCentre : dist (lqgSquareCentre 0) (lqgSquareCentre 1) = 1 / 8 := by
  unfold lqgSquareCentre
  rw [Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real]
  norm_num

theorem dyadicScale_le_sixteenth {k : ℕ} (hk : 4 ≤ k) : dyadicScale k ≤ 1 / 16 := by
  have := dyadicScale_le_of_le hk
  have h4 : dyadicScale 4 = 1 / 16 := by unfold dyadicScale; norm_num
  linarith

theorem measurableSet_lqgSubSquare (k : ℕ) (s : Fin 2) : MeasurableSet (lqgSubSquare k s) :=
  (by fun_prop : Measurable fun x : ℂ => (x - lqgSquareCentre s) / (dyadicScale k : ℂ))
    measurableSet_lqgSquare

theorem mem_lqgSubSquare_iff (k : ℕ) (s : Fin 2) (x : ℂ) :
    x ∈ lqgSubSquare k s ↔ |x.re - (((s : ℕ) : ℝ) / 8 - 1 / 16)| ≤ dyadicScale k / 8 ∧
      |x.im| ≤ dyadicScale k / 8 := by
  have hR := dyadicScale_pos' k
  unfold lqgSubSquare lqgSquare lqgSquareCentre
  simp only [mem_preimage, Set.mem_ofPred_eq, Complex.div_ofReal_re, Complex.div_ofReal_im,
    Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero, abs_div,
    abs_of_pos hR]
  rw [div_le_iff₀ hR, div_le_iff₀ hR]
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨by linarith, by linarith⟩

theorem lqgSubSquare_subset {k : ℕ} (hk : 4 ≤ k) (s : Fin 2) : lqgSubSquare k s ⊆ lqgSquare := by
  intro x hx
  rw [mem_lqgSubSquare_iff] at hx
  have hR := dyadicScale_le_sixteenth hk
  obtain ⟨h1, h2⟩ := hx
  have hs : ((s : ℕ) : ℝ) ≤ 1 := by exact_mod_cast Nat.lt_succ_iff.1 s.2
  have hs0 : (0 : ℝ) ≤ ((s : ℕ) : ℝ) := Nat.cast_nonneg _
  rw [abs_le] at h1
  refine ⟨?_, by linarith⟩
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2]

theorem disjoint_lqgSubSquare {k : ℕ} (hk : 4 ≤ k) : Disjoint (lqgSubSquare k 0) (lqgSubSquare k 1) := by
  rw [Set.disjoint_left]
  intro x hx0 hx1
  rw [mem_lqgSubSquare_iff] at hx0 hx1
  have hR := dyadicScale_le_sixteenth hk
  have hR0 := dyadicScale_pos' k
  obtain ⟨h0, -⟩ := hx0
  obtain ⟨h1, -⟩ := hx1
  rw [abs_le] at h0 h1
  norm_num at h0 h1
  linarith [h0.1, h0.2, h1.1, h1.2]

/-- **Splitting the mass of the square.** For `n = k + m`, `k ≥ 4`,
`μ_n(T) ≥ ∑_s R^{2+γ²/2} e^{γ h_R(z_s)} μ'^{(s)}_m(T)`, `R = 2^{-k}`, `μ'^{(s)}` the approximation of
the field recentred at `z_s` and dilated by `R`. -/
theorem lqgApproxMass_square_ge_sum {γ : ℝ} (hγ : γ ≠ 0) (h : ℝ → ℂ → ℝ) {k : ℕ} (hk : 4 ≤ k)
    (m : ℕ) :
    ∑ s : Fin 2, dyadicFactor γ k (h (dyadicScale k) (lqgSquareCentre s)) *
        lqgApproxMass γ (fun t w => h (dyadicScale k * t)
          ((dyadicScale k : ℂ) * w + lqgSquareCentre s) - h (dyadicScale k) (lqgSquareCentre s))
          (lqgSquare.indicator 1) m ≤
      lqgApproxMass γ h (lqgSquare.indicator 1) (k + m) := by
  have hterm : ∀ s : Fin 2, dyadicFactor γ k (h (dyadicScale k) (lqgSquareCentre s)) *
        lqgApproxMass γ (fun t w => h (dyadicScale k * t)
          ((dyadicScale k : ℂ) * w + lqgSquareCentre s) - h (dyadicScale k) (lqgSquareCentre s))
          (lqgSquare.indicator 1) m =
      lqgApprox γ h (dyadicScale (k + m)) (lqgSubSquare k s) := fun s => by
    rw [← lqgApproxMass_indicator_preimage_dyadic hγ h k m (lqgSquareCentre s)
      measurableSet_lqgSquare]
    unfold lqgApproxMass
    exact lintegral_indicator_one (measurableSet_lqgSubSquare k s)
  rw [Finset.sum_congr rfl fun s _ => hterm s, Fin.sum_univ_two,
    ← measure_union (disjoint_lqgSubSquare hk) (measurableSet_lqgSubSquare k 1)]
  unfold lqgApproxMass
  rw [lintegral_indicator_one measurableSet_lqgSquare]
  exact measure_mono (Set.union_subset (lqgSubSquare_subset hk 0) (lqgSubSquare_subset hk 1))

/-- The splitting inequality for a family of circle averages `hcirc` and a sample point `ω`. -/
theorem lqgApproxMass_square_ge_sum_recentred {Ω : Type*} {γ : ℝ} (hγ : γ ≠ 0)
    (hcirc : Ω → ℝ → ℂ → ℝ) (ω : Ω) {k : ℕ} (hk : 4 ≤ k) (m : ℕ) :
    ∑ s : Fin 2, dyadicFactor γ k (hcirc ω (dyadicScale k) (lqgSquareCentre s)) *
        lqgApproxMass γ (recentredField hcirc k (lqgSquareCentre s) ω) (lqgSquare.indicator 1) m ≤
      lqgApproxMass γ (hcirc ω) (lqgSquare.indicator 1) (k + m) :=
  lqgApproxMass_square_ge_sum hγ (hcirc ω) hk m

/-- The discs `B(z_s, R)` lie in the unit disc. -/
theorem norm_lqgSquareCentre_add_dyadicScale_le_one {k : ℕ} (hk : 4 ≤ k) (s : Fin 2) :
    ‖lqgSquareCentre s‖ + dyadicScale k ≤ 1 := by
  have := dyadicScale_le_sixteenth hk
  rw [norm_lqgSquareCentre]
  linarith

/-- The centres are `2R` apart. -/
theorem two_mul_dyadicScale_le_dist_lqgSquareCentre {k : ℕ} (hk : 4 ≤ k) :
    2 * dyadicScale k ≤ dist (lqgSquareCentre 0) (lqgSquareCentre 1) := by
  have := dyadicScale_le_sixteenth hk
  rw [dist_lqgSquareCentre]
  linarith

end LatticeProb.LQG
