import LatticeProb.LQG.GMCScaleIncrementUniform
import LatticeProb.LQG.GMCScaleGrid
import LatticeProb.LQG.GMCDilationField

/-!
# Grid estimate for the dilated recentred fields

Let `h` be a whole-plane Gaussian free field with circle averages `h_r(z)` and let
`h^{(j)} = h(2^{-j} ·) - h_{2^{-j}}(0)` be its dilated recentred fields, again whole-plane Gaussian free fields.
At level `n` of the field `h^{(j)}` take the grid of radii `s_{n,i} = 2^{-n} (1 - i / (2 N_{n+j}))`, `0 ≤ i ≤ N_{n+j}`,
with `N_k = ⌊2^{a k / 2}⌋`: the grid is indexed by the absolute level `n + j`, so that in the coordinates of `h`
its mesh is `2^{-(n+j)} / (2 N_{n+j})`. We show that almost surely, for all large `j`, at every level `n` and every
grid radius, the recentred approximations of `h^{(j)}` at `s_{n,i}` and at `2^{-n}` differ by less than `e^{η j}`,
provided `a / 2 < c` (the exponent of the `L¹` increment bound) and `(a / 2) log 2 < η`.

The proof is a Borel-Cantelli argument over the pairs `(j, n)`, from the increment bound of
`exists_scaleIncrement_bound_uniform`, which is uniform over whole-plane Gaussian free fields and hence applies to
all the `h^{(j)}` with the same constants.

## Main results

* `GMCScaleGrid.ae_eventually_forall_forall_abs_lt`: Borel-Cantelli over pairs `(j, n)` with finite families of
  growing size, from `L¹` bounds.
* `IsWholePlaneGFF.ae_eventually_grid_dilateRecentre`: the grid estimate for the dilated recentred fields.
-/

open MeasureTheory ProbabilityTheory Real Function Filter Topology
open scoped ENNReal NNReal

namespace LatticeProb.LQG.GMCScaleGrid

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Borel-Cantelli over pairs with growing finite families.** If `E |X_{j,n,i}| ≤ b_{j,n}` for `i ≤ N_{j,n}` and
`∑_{(j,n)} (N_{j,n} + 1) b_{j,n} / δ_{j,n} < ∞`, then almost surely, for all large `j`, `|X_{j,n,i}| < δ_{j,n}` for
every `n` and every `i ≤ N_{j,n}`. -/
theorem ae_eventually_forall_forall_abs_lt {X : ℕ → ℕ → ℕ → Ω → ℝ} {N : ℕ → ℕ → ℕ} {b δ : ℕ → ℕ → ℝ}
    (hδ : ∀ j n, 0 < δ j n) (hX : ∀ j n i, i ≤ N j n → Integrable (X j n i) P)
    (hb : ∀ j n i, i ≤ N j n → ∫ ω, |X j n i ω| ∂P ≤ b j n)
    (hsum : Summable fun p : ℕ × ℕ => ((N p.1 p.2 : ℝ) + 1) * (b p.1 p.2 / δ p.1 p.2)) :
    ∀ᵐ ω ∂P, ∀ᶠ j in atTop, ∀ n, ∀ i ≤ N j n, |X j n i ω| < δ j n := by
  set S : ℕ → ℕ → Set Ω := fun j n => ⋃ i ∈ Finset.range (N j n + 1), {ω | δ j n ≤ |X j n i ω|} with hSdef
  have hb0 : ∀ j n, 0 ≤ b j n := fun j n =>
    (integral_nonneg fun ω => abs_nonneg (X j n 0 ω)).trans (hb j n 0 (Nat.zero_le _))
  have hmeas : ∀ j n i, i ≤ N j n → P {ω | δ j n ≤ |X j n i ω|} ≤ ENNReal.ofReal (b j n / δ j n) := by
    intro j n i hi
    have hfi : Integrable (fun ω => |X j n i ω|) P := (hX j n i hi).abs
    have hε0 : ENNReal.ofReal (δ j n) ≠ 0 := by simpa using hδ j n
    have h1 : P {ω | δ j n ≤ |X j n i ω|} ≤
        (∫⁻ ω, ENNReal.ofReal |X j n i ω| ∂P) / ENNReal.ofReal (δ j n) := by
      refine le_trans (measure_mono fun ω hω => ?_)
        (meas_ge_le_lintegral_div hfi.aemeasurable.ennreal_ofReal hε0 ENNReal.ofReal_ne_top)
      exact ENNReal.ofReal_le_ofReal hω
    rw [← ofReal_integral_eq_lintegral_ofReal hfi (ae_of_all _ fun ω => abs_nonneg _)] at h1
    refine h1.trans ?_
    rw [← ENNReal.ofReal_div_of_pos (hδ j n)]
    exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hb j n i hi) (hδ j n).le)
  have hS : ∀ j n, P (S j n) ≤ ENNReal.ofReal (((N j n : ℝ) + 1) * (b j n / δ j n)) := by
    intro j n
    refine (measure_biUnion_finset_le _ _).trans ?_
    calc ∑ i ∈ Finset.range (N j n + 1), P {ω | δ j n ≤ |X j n i ω|}
        ≤ ∑ _i ∈ Finset.range (N j n + 1), ENNReal.ofReal (b j n / δ j n) :=
          Finset.sum_le_sum fun i hi => hmeas j n i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
      _ = ENNReal.ofReal (((N j n : ℝ) + 1) * (b j n / δ j n)) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [show ((N j n : ℝ) + 1) = ((N j n + 1 : ℕ) : ℝ) by push_cast; ring, ENNReal.ofReal_natCast]
  have hnn : ∀ p : ℕ × ℕ, 0 ≤ ((N p.1 p.2 : ℝ) + 1) * (b p.1 p.2 / δ p.1 p.2) := fun p =>
    mul_nonneg (by positivity) (div_nonneg (hb0 p.1 p.2) (hδ p.1 p.2).le)
  set T : ℕ → Set Ω := fun j => ⋃ n, S j n with hT
  have hfin : (∑' j, P (T j)) ≠ ∞ := by
    refine ne_top_of_le_ne_top
      (ENNReal.ofReal_ne_top (r := ∑' p : ℕ × ℕ, ((N p.1 p.2 : ℝ) + 1) * (b p.1 p.2 / δ p.1 p.2))) ?_
    rw [ENNReal.ofReal_tsum_of_nonneg hnn hsum, ENNReal.tsum_prod']
    exact ENNReal.tsum_le_tsum fun j =>
      (measure_iUnion_le _).trans (ENNReal.tsum_le_tsum fun n => hS j n)
  filter_upwards [ae_eventually_notMem hfin] with ω hω
  filter_upwards [hω] with j hj n i hi
  by_contra hcon
  exact hj (Set.mem_iUnion.2 ⟨n, Set.mem_iUnion₂.2
    ⟨i, Finset.mem_range.2 (Nat.lt_succ_of_le hi), not_lt.1 hcon⟩⟩)

/-- **Summability for the dilated grids.** If `0 ≤ a`, `a / 2 < c` and `(a / 2) log 2 < η`, then
`∑_{(j,n)} (N_{n+j} + 1) K 2^{-c n} / e^{η j} < ∞` for `N_k = ⌊2^{a k / 2}⌋`. -/
theorem summable_gridCount_dilate {a c η K : ℝ} (ha : 0 ≤ a) (hac : a / 2 < c)
    (haη : a / 2 * Real.log 2 < η) :
    Summable fun p : ℕ × ℕ =>
      ((gridCount a (p.2 + p.1) : ℝ) + 1) * (K * dyadicScale p.2 ^ c / rexp (η * p.1)) := by
  have hd : ∀ k, 0 < dyadicScale k := fun k => pow_pos (by norm_num) k
  have hd1 : ∀ k, dyadicScale k ≤ 1 := fun k => pow_le_one₀ (by norm_num) (by norm_num)
  have hpow : ∀ (x : ℝ) (k : ℕ), dyadicScale k ^ x = ((2 : ℝ)⁻¹ ^ x) ^ k := fun x k => by
    rw [dyadicScale, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
      Real.rpow_natCast]
  set q : ℝ := (2 : ℝ)⁻¹ ^ (-(a / 2)) with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  set r1 : ℝ := q / rexp η with hr1
  set r2 : ℝ := q * (2 : ℝ)⁻¹ ^ c with hr2
  have hqexp : q = rexp (a / 2 * Real.log 2) := by
    rw [hq, Real.rpow_def_of_pos (by norm_num), Real.log_inv]
    congr 1
    ring
  have hr10 : 0 ≤ r1 := div_nonneg hq0.le (Real.exp_pos _).le
  have hr11 : r1 < 1 := by
    rw [hr1, div_lt_one (Real.exp_pos _), hqexp]
    exact Real.exp_lt_exp.2 haη
  have hr20 : 0 ≤ r2 := mul_nonneg hq0.le (Real.rpow_pos_of_pos (by norm_num) _).le
  have hr21 : r2 < 1 := by
    rw [hr2, hq, ← Real.rpow_add (by norm_num)]
    exact Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith)
  have hgeo : Summable fun p : ℕ × ℕ => 2 * |K| * (r1 ^ p.1 * r2 ^ p.2) :=
    ((summable_geometric_of_lt_one hr10 hr11).mul_of_nonneg (summable_geometric_of_lt_one hr20 hr21)
      (fun _ => pow_nonneg hr10 _) (fun _ => pow_nonneg hr20 _)).mul_left _
  refine Summable.of_norm_bounded (g := fun p : ℕ × ℕ => 2 * |K| * (r1 ^ p.1 * r2 ^ p.2)) hgeo fun p => ?_
  obtain ⟨j, n⟩ := p
  simp only
  have hx1 : 1 ≤ dyadicScale (n + j) ^ (-(a / 2)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos (hd _) (hd1 _) (by linarith)
  have hN : (gridCount a (n + j) : ℝ) + 1 ≤ 2 * dyadicScale (n + j) ^ (-(a / 2)) := by
    have : (gridCount a (n + j) : ℝ) ≤ dyadicScale (n + j) ^ (-(a / 2)) :=
      Nat.floor_le (Real.rpow_pos_of_pos (hd _) _).le
    linarith
  have hqn : dyadicScale (n + j) ^ (-(a / 2)) = q ^ n * q ^ j := by
    rw [hpow, pow_add]
  have hexp : rexp (η * j) = rexp η ^ j := by
    rw [mul_comm, Real.exp_nat_mul]
  have hc : dyadicScale n ^ c = ((2 : ℝ)⁻¹ ^ c) ^ n := hpow c n
  have hE : 0 < rexp η ^ j := pow_pos (Real.exp_pos _) j
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (gridCount a (n + j) : ℝ) + 1),
    abs_div, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (hd n) c), abs_of_pos (Real.exp_pos _)]
  calc ((gridCount a (n + j) : ℝ) + 1) * (|K| * dyadicScale n ^ c / rexp (η * j))
      ≤ (2 * (q ^ n * q ^ j)) * (|K| * ((2 : ℝ)⁻¹ ^ c) ^ n / rexp η ^ j) := by
        rw [← hqn, ← hc, ← hexp]
        exact mul_le_mul_of_nonneg_right hN
          (div_nonneg (mul_nonneg (abs_nonneg K) (Real.rpow_pos_of_pos (hd n) c).le) (Real.exp_pos _).le)
    _ = 2 * |K| * (r1 ^ j * r2 ^ n) := by
        rw [hr1, hr2, div_pow, mul_pow]
        field_simp

end LatticeProb.LQG.GMCScaleGrid

namespace LatticeProb.Gauss.IsWholePlaneGFF

open LatticeProb.LQG LatticeProb.LQG.GMCScaleGrid

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Grid estimate for the dilated recentred fields.** Let `g` be continuous with compact support and
`‖z‖ + 1 ≤ R` on its support, `0 < γ < 2`. There is `c > 0` such that for all `a ≥ 0` and `η` with `a / 2 < c` and
`(a / 2) log 2 < η`, almost surely, for all large `j`, every `n` and every `i ≤ N_{n+j} = ⌊2^{a (n+j) / 2}⌋`, the
recentred approximations of `h^{(j)} = h(2^{-j} ·) - h_{2^{-j}}(0)` at the grid radius
`s_{n,i} = 2^{-n} (1 - i / (2 N_{n+j}))` and at `2^{-n}` differ by less than `e^{η j}`. -/
theorem ae_eventually_grid_dilateRecentre (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ} (hγ0 : 0 < γ)
    (hγ2 : γ < 2) {g : ℂ → ℝ} (hgc : Continuous g) (hgs : HasCompactSupport g) {R : ℝ} (hR : 0 < R)
    (hgR : ∀ z, g z ≠ 0 → ‖z‖ + 1 ≤ R) :
    ∃ c : ℝ, 0 < c ∧ ∀ a η : ℝ, 0 ≤ a → a / 2 < c → a / 2 * Real.log 2 < η →
      ∀ᵐ ω ∂P, ∀ᶠ j in atTop, ∀ n, ∀ i ≤ gridCount a (n + j),
        |∫ z, g z * (gridScale (fun m => gridCount a (m + j)) n i ^ (γ ^ 2 / 2) *
            rexp (γ * (dilateRecentre (dyadicScale j) (hcirc ω)
              (gridScale (fun m => gridCount a (m + j)) n i) z - dilateRecentre (dyadicScale j) (hcirc ω) R 0)) -
          dyadicScale n ^ (γ ^ 2 / 2) * rexp (γ * (dilateRecentre (dyadicScale j) (hcirc ω) (dyadicScale n) z -
            dilateRecentre (dyadicScale j) (hcirc ω) R 0)))| < rexp (η * j) := by
  obtain ⟨K, c, -, hc, hKb⟩ := exists_scaleIncrement_bound_uniform hγ0 hγ2 hgc hgs hR hgR
  refine ⟨c, hc, fun a η ha hac haη => ?_⟩
  have hd : ∀ k, 0 < dyadicScale k := fun k => pow_pos (by norm_num) k
  have hd1 : ∀ k, dyadicScale k ≤ 1 := fun k => pow_le_one₀ (by norm_num) (by norm_num)
  choose hC' hG' using fun j : ℕ => isWholePlaneGFF_dilateRecentre hh (c := dyadicScale j) (hd j)
  refine ae_eventually_forall_forall_abs_lt (N := fun j n => gridCount a (n + j))
    (b := fun _ n => K * dyadicScale n ^ c) (δ := fun j _ => rexp (η * j))
    (X := fun j n i ω => ∫ z, g z * (gridScale (fun m => gridCount a (m + j)) n i ^ (γ ^ 2 / 2) *
            rexp (γ * (dilateRecentre (dyadicScale j) (hcirc ω)
              (gridScale (fun m => gridCount a (m + j)) n i) z - dilateRecentre (dyadicScale j) (hcirc ω) R 0)) -
          dyadicScale n ^ (γ ^ 2 / 2) * rexp (γ * (dilateRecentre (dyadicScale j) (hcirc ω) (dyadicScale n) z -
            dilateRecentre (dyadicScale j) (hcirc ω) R 0))))
    (fun j n => Real.exp_pos _) (fun j n i hi => ?_) (fun j n i hi => ?_)
    (summable_gridCount_dilate ha hac haη)
  · obtain ⟨h1, h2⟩ := gridScale_mem_Icc (fun m => gridCount a (m + j)) hi
    exact (hG' j).integrable_integral_increment_scales (by linarith [hd n]) (hd n) hR volume
      hgc.measurable (hgc.integrable_of_hasCompactSupport hgs)
      (fun z hz => by linarith [hgR z hz, hd1 n]) (fun z hz => by linarith [hgR z hz, hd1 n]) γ
  · obtain ⟨h1, h2⟩ := gridScale_mem_Icc (fun m => gridCount a (m + j)) hi
    exact hKb (hG' j) _ _ (hd n) (hd1 n) h1 h2

end LatticeProb.Gauss.IsWholePlaneGFF
