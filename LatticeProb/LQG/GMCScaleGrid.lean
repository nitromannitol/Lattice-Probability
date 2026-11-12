import LatticeProb.LQG.LQGCoordChangeIdent

/-!
# Circle-average Gaussian multiplicative chaos on a growing grid of radii

At level `k` the radii `s_{k,j} = 2^{-k} (1 - j / (2 N_k))`, `0 ≤ j ≤ N_k`, form a grid of `[2^{-k-1}, 2^{-k}]` with
mesh `2^{-k} / (2 N_k)`. If the `L¹` increments between radii in `[ε/2, ε]` are at most `K ε^c` (as for the
circle-average approximations of the whole-plane Gaussian free field, `ScaleIncrementL1Bound`), and the number of grid
points grows slowly enough that `∑_k (N_k + 1) K 2^{-ck} / 2^{-θk} < ∞`, then almost surely, for all large `k`, the
recentred approximations at every grid radius are within `2^{-θk}` of the approximation at `2^{-k}`.

This is the grid step of the almost sure vague convergence of the approximations along every ratio `r 2^{-k}`
simultaneously: between grid points, the radius is controlled by a modulus of continuity of the circle-average process
(`GMCScaleSandwich`).

## Main results

* `ae_eventually_forall_abs_lt`: Borel-Cantelli over finite families of growing size, from `L¹` bounds.
* `gridScale`, `gridScale_mem_Icc`: the grid of radii and its range.
* `gridCount`, `summable_gridCount`: the standard grid size `N_k = ⌊2^{ck/2}⌋` and the convergence of the series.
* `IsWholePlaneGFF.ae_eventually_grid`: the almost sure grid estimate for the recentred approximations.
-/

namespace LatticeProb.LQG.GMCScaleGrid

open MeasureTheory Filter Topology
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Borel-Cantelli over growing finite families.** If `E |X_{k,j}| ≤ b_k` for `j ≤ N_k` and
`∑_k (N_k + 1) b_k / δ_k < ∞`, then almost surely, for all large `k`, `|X_{k,j}| < δ_k` for every `j ≤ N_k`. -/
theorem ae_eventually_forall_abs_lt {X : ℕ → ℕ → Ω → ℝ} {N : ℕ → ℕ} {b δ : ℕ → ℝ}
    (hδ : ∀ k, 0 < δ k) (hX : ∀ k j, j ≤ N k → Integrable (X k j) P)
    (hb : ∀ k j, j ≤ N k → ∫ ω, |X k j ω| ∂P ≤ b k)
    (hsum : Summable fun k => ((N k : ℝ) + 1) * (b k / δ k)) :
    ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ∀ j ≤ N k, |X k j ω| < δ k := by
  set S : ℕ → Set Ω := fun k => ⋃ j ∈ Finset.range (N k + 1), {ω | δ k ≤ |X k j ω|} with hSdef
  have hb0 : ∀ k, 0 ≤ b k := fun k =>
    (integral_nonneg fun ω => abs_nonneg (X k 0 ω)).trans (hb k 0 (Nat.zero_le _))
  have hmeas : ∀ k j, j ≤ N k → P {ω | δ k ≤ |X k j ω|} ≤ ENNReal.ofReal (b k / δ k) := by
    intro k j hj
    have hfi : Integrable (fun ω => |X k j ω|) P := (hX k j hj).abs
    have hε0 : ENNReal.ofReal (δ k) ≠ 0 := by simpa using hδ k
    have h1 : P {ω | δ k ≤ |X k j ω|} ≤
        (∫⁻ ω, ENNReal.ofReal |X k j ω| ∂P) / ENNReal.ofReal (δ k) := by
      refine le_trans (measure_mono fun ω hω => ?_)
        (meas_ge_le_lintegral_div hfi.aemeasurable.ennreal_ofReal hε0 ENNReal.ofReal_ne_top)
      exact ENNReal.ofReal_le_ofReal hω
    rw [← ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all _ fun ω => abs_nonneg _)] at h1
    refine h1.trans ?_
    rw [← ENNReal.ofReal_div_of_pos (hδ k)]
    exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hb k j hj) (hδ k).le)
  have hS : ∀ k, P (S k) ≤ ENNReal.ofReal (((N k : ℝ) + 1) * (b k / δ k)) := by
    intro k
    refine (measure_biUnion_finset_le _ _).trans ?_
    calc ∑ j ∈ Finset.range (N k + 1), P {ω | δ k ≤ |X k j ω|}
        ≤ ∑ _j ∈ Finset.range (N k + 1), ENNReal.ofReal (b k / δ k) :=
          Finset.sum_le_sum fun j hj => hmeas k j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
      _ = ENNReal.ofReal (((N k : ℝ) + 1) * (b k / δ k)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [show ((N k : ℝ) + 1) = ((N k + 1 : ℕ) : ℝ) by push_cast; ring, ENNReal.ofReal_natCast]
  have hnn : ∀ k, 0 ≤ ((N k : ℝ) + 1) * (b k / δ k) := fun k =>
    mul_nonneg (by positivity) (div_nonneg (hb0 k) (hδ k).le)
  have hfin : (∑' k, P (S k)) ≠ ∞ := by
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑' k, ((N k : ℝ) + 1) * (b k / δ k))) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg hnn hsum]
    exact ENNReal.tsum_le_tsum hS
  filter_upwards [ae_eventually_notMem hfin] with ω hω
  filter_upwards [hω] with k hk j hj
  by_contra hcon
  exact hk (Set.mem_iUnion₂.2 ⟨j, Finset.mem_range.2 (Nat.lt_succ_of_le hj), not_lt.1 hcon⟩)

/-- The grid of radii at level `k`: `s_{k,j} = 2^{-k} (1 - j / (2 N_k))`. -/
noncomputable def gridScale (N : ℕ → ℕ) (k j : ℕ) : ℝ :=
  dyadicScale k * (1 - (j : ℝ) / (2 * N k))

theorem gridScale_mem_Icc (N : ℕ → ℕ) {k j : ℕ} (hj : j ≤ N k) :
    dyadicScale k / 2 ≤ gridScale N k j ∧ gridScale N k j ≤ dyadicScale k := by
  have hd : 0 < dyadicScale k := pow_pos (by norm_num) k
  have hq0 : 0 ≤ (j : ℝ) / (2 * N k) := by positivity
  have hq1 : (j : ℝ) / (2 * N k) ≤ 1 / 2 := by
    rcases Nat.eq_zero_or_pos (N k) with h0 | hpos
    · simp [h0]
    · rw [div_le_iff₀ (by positivity)]
      have : (j : ℝ) ≤ N k := by exact_mod_cast hj
      linarith
  unfold gridScale
  constructor <;> nlinarith

/-- The standard number of grid intervals at level `k`: `N_k = ⌊2^{ck/2}⌋`. -/
noncomputable def gridCount (c : ℝ) (k : ℕ) : ℕ :=
  ⌊dyadicScale k ^ (-(c / 2))⌋₊

/-- With `N_k = ⌊2^{ck/2}⌋` and `0 ≤ θ < c/2`, the Borel-Cantelli series `∑_k (N_k + 1) K 2^{-ck} / 2^{-θk}`
converges. -/
theorem summable_gridCount {c θ K : ℝ} (hθ0 : 0 ≤ θ) (hθ : θ < c / 2) :
    Summable fun k => ((gridCount c k : ℝ) + 1) * (K * dyadicScale k ^ c / dyadicScale k ^ θ) := by
  have hd : ∀ k, 0 < dyadicScale k := fun k => pow_pos (by norm_num) k
  have hd1 : ∀ k, dyadicScale k ≤ 1 := fun k => pow_le_one₀ (by norm_num) (by norm_num)
  have hpow : ∀ (x : ℝ) (k : ℕ), dyadicScale k ^ x = ((2 : ℝ)⁻¹ ^ x) ^ k := fun x k => by
    rw [dyadicScale, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
      Real.rpow_natCast]
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (2 : ℝ)⁻¹ ^ (c / 2 - θ) := ⟨_, rfl⟩
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  have hr1 : r < 1 := by rw [hr]; exact Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith)
  refine Summable.of_norm_bounded (g := fun k => 2 * |K| * r ^ k)
    ((summable_geometric_of_lt_one hr0 hr1).mul_left _) fun k => ?_
  have hc : dyadicScale k ^ c > 0 := Real.rpow_pos_of_pos (hd k) c
  have hθk : dyadicScale k ^ θ > 0 := Real.rpow_pos_of_pos (hd k) θ
  have hN : (gridCount c k : ℝ) + 1 ≤ 2 * dyadicScale k ^ (-(c / 2)) := by
    have h1 : (gridCount c k : ℝ) ≤ dyadicScale k ^ (-(c / 2)) :=
      Nat.floor_le (Real.rpow_pos_of_pos (hd k) _).le
    have h2 : 1 ≤ dyadicScale k ^ (-(c / 2)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos (hd k) (hd1 k) (by linarith)
    linarith
  have hcomb : dyadicScale k ^ (-(c / 2)) * dyadicScale k ^ c / dyadicScale k ^ θ = r ^ k := by
    rw [← Real.rpow_add (hd k), ← Real.rpow_sub (hd k), hpow, hr]
    congr 2
    ring
  have hX : 0 ≤ |K| * dyadicScale k ^ c / dyadicScale k ^ θ :=
    div_nonneg (mul_nonneg (abs_nonneg K) hc.le) hθk.le
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (gridCount c k : ℝ) + 1), abs_div,
    abs_mul, abs_of_pos hc, abs_of_pos hθk]
  calc ((gridCount c k : ℝ) + 1) * (|K| * dyadicScale k ^ c / dyadicScale k ^ θ)
      ≤ (2 * dyadicScale k ^ (-(c / 2))) * (|K| * dyadicScale k ^ c / dyadicScale k ^ θ) :=
        mul_le_mul_of_nonneg_right hN hX
    _ = 2 * |K| * (dyadicScale k ^ (-(c / 2)) * dyadicScale k ^ c / dyadicScale k ^ θ) := by ring
    _ = 2 * |K| * r ^ k := by rw [hcomb]

end LatticeProb.LQG.GMCScaleGrid

namespace LatticeProb.Gauss.IsWholePlaneGFF

open MeasureTheory Filter Topology Real LatticeProb.LQG LatticeProb.LQG.GMCScaleGrid

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **The grid estimate.** Let `g` be continuous with compact support, `‖z‖ + 1 ≤ R` on its support, and suppose the
`L¹` increments of the recentred approximations between radii `ε/2 ≤ s ≤ ε ≤ 1` are at most `K ε^c`. If
`∑_k (N_k + 1) K 2^{-ck} / 2^{-θk} < ∞`, then almost surely, for all large `k` and every `j ≤ N_k`, the recentred
approximations at the grid radius `s_{k,j}` and at `2^{-k}` differ by less than `2^{-θk}`. -/
theorem ae_eventually_grid (hh : IsWholePlaneGFF P hC hcirc) (γ : ℝ) {g : ℂ → ℝ} (hgc : Continuous g)
    (hgs : HasCompactSupport g) {R K c : ℝ} (hR : 0 < R) (hgR : ∀ z, g z ≠ 0 → ‖z‖ + 1 ≤ R)
    (hK : ∀ ε s : ℝ, 0 < ε → ε ≤ 1 → ε / 2 ≤ s → s ≤ ε →
      ∫ ω, |∫ z, g z * (s ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω s z - hcirc ω R 0)) -
        ε ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω ε z - hcirc ω R 0)))| ∂P ≤ K * ε ^ c)
    {N : ℕ → ℕ} {θ : ℝ}
    (hsum : Summable fun k => ((N k : ℝ) + 1) * (K * dyadicScale k ^ c / dyadicScale k ^ θ)) :
    ∀ᵐ ω ∂P, ∀ᶠ k in atTop, ∀ j ≤ N k,
      |∫ z, g z * (gridScale N k j ^ (γ ^ 2 / 2) *
          rexp (γ * (hcirc ω (gridScale N k j) z - hcirc ω R 0)) -
        dyadicScale k ^ (γ ^ 2 / 2) * rexp (γ * (hcirc ω (dyadicScale k) z - hcirc ω R 0)))| <
        dyadicScale k ^ θ := by
  have hd : ∀ k, 0 < dyadicScale k := fun k => pow_pos (by norm_num) k
  have hd1 : ∀ k, dyadicScale k ≤ 1 := fun k => pow_le_one₀ (by norm_num) (by norm_num)
  refine ae_eventually_forall_abs_lt (fun k => Real.rpow_pos_of_pos (hd k) θ) (fun k j hj => ?_)
    (fun k j hj => ?_) hsum
  · obtain ⟨h1, h2⟩ := gridScale_mem_Icc N hj
    exact hh.integrable_integral_increment_scales (by linarith [hd k]) (hd k) hR volume
      hgc.measurable (hgc.integrable_of_hasCompactSupport hgs)
      (fun z hz => by linarith [hgR z hz, hd1 k]) (fun z hz => by linarith [hgR z hz, hd1 k]) γ
  · obtain ⟨h1, h2⟩ := gridScale_mem_Icc N hj
    exact hK _ _ (hd k) (hd1 k) h1 h2

end LatticeProb.Gauss.IsWholePlaneGFF
