/-
The Kolmogorov-Chentsov theorem.

A process on `ℝ≥0` whose increments satisfy `∫⁻ ‖X t - X s‖ₑ ^ p ≤ M |t - s| ^ q`
with `q > 1` has a modification with continuous paths.  Mathlib 4.32 defines the
hypothesis, `ProbabilityTheory.IsKolmogorovProcess`, and records that the
conclusion is not available; this is the conclusion.

The proof is the classical one.  Chebyshev turns the moment bound into a bound on
the probability that some increment of `X` across the level-`n` dyadic grid,
over the initial segment of length `n · 2 ^ n`, exceeds `b ^ n`; the exponent `b`
is chosen so that the resulting series converges, which is where `q > 1` enters.
Borel-Cantelli then makes those increment bounds hold from some level on, almost
surely, and `LatticeProb.continuous_dlim` reads a continuous function off them.
That the continuous function is a modification is the only place where the
process itself is used again: the truncations `dtrunc n t` converge to `t`, so
`X (dtrunc n t)` converges to `X t` in measure by Chebyshev, while it converges
almost surely to the constructed value.
-/
import Mathlib
import LatticeProb.Prob.DyadicChain

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {p q : ℝ} {M : ℝ≥0}
  {X : ℝ≥0 → Ω → ℝ}

/-! ### The dyadic grid seen through `edist` -/

theorem coe_dyad (n k : ℕ) : ((dyad n k : ℝ≥0) : ℝ) = (k : ℝ) / 2 ^ n := by
  rw [dyad]
  push_cast
  ring

theorem edist_dyad_succ (n k : ℕ) :
    edist (dyad n (k + 1)) (dyad n k) = ENNReal.ofReal ((1 : ℝ) / 2 ^ n) := by
  rw [edist_dist, NNReal.dist_eq, coe_dyad, coe_dyad]
  congr 1
  rw [abs_of_nonneg (by push_cast; rw [sub_nonneg]; gcongr; norm_num)]
  push_cast
  ring

theorem edist_dtrunc_le (n : ℕ) (t : ℝ≥0) :
    edist (dtrunc n t) t ≤ ENNReal.ofReal ((1 : ℝ) / 2 ^ n) := by
  rw [edist_dist, NNReal.dist_eq]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 : dtrunc n t ≤ t := dtrunc_le n t
  have h2 : t < dyad n (⌊t * 2 ^ n⌋₊ + 1) := lt_dyad_floor_succ n t
  rw [abs_of_nonpos (by rw [sub_nonpos]; exact_mod_cast h1)]
  have h3 : (t : ℝ) < ((⌊t * 2 ^ n⌋₊ : ℝ) + 1) / 2 ^ n := by
    have := (NNReal.coe_lt_coe.mpr h2)
    rwa [coe_dyad, Nat.cast_add, Nat.cast_one] at this
  have h4 : ((dtrunc n t : ℝ≥0) : ℝ) = (⌊t * 2 ^ n⌋₊ : ℝ) / 2 ^ n := by
    rw [dtrunc, coe_dyad]
  rw [h4]
  have h5 : ((⌊t * 2 ^ n⌋₊ : ℝ) + 1) / 2 ^ n
      = (⌊t * 2 ^ n⌋₊ : ℝ) / 2 ^ n + 1 / 2 ^ n := by rw [add_div]
  rw [h5] at h3
  linarith

/-! ### Chebyshev -/

theorem measure_edist_ge_le (hX : IsKolmogorovProcess X P p q M) (u v : ℝ≥0)
    {ε : ℝ≥0∞} (hε : ε ≠ 0) (hε' : ε ≠ ∞) :
    P {ω | ε ≤ edist (X u ω) (X v ω)} ≤ M * edist u v ^ q / ε ^ p := by
  have hp := hX.p_pos
  have hεp0 : ε ^ p ≠ 0 := by
    simp [ENNReal.rpow_eq_zero_iff, hε, hε', hp, not_lt.2 hp.le]
  have hεptop : ε ^ p ≠ ∞ := by
    simp [ENNReal.rpow_eq_top_iff, hε, hε', not_lt.2 hp.le, hp]
  have hsub : {ω | ε ≤ edist (X u ω) (X v ω)}
      ⊆ {ω | ε ^ p ≤ edist (X u ω) (X v ω) ^ p} := fun ω hω =>
    ENNReal.rpow_le_rpow hω hp.le
  calc P {ω | ε ≤ edist (X u ω) (X v ω)}
      ≤ P {ω | ε ^ p ≤ edist (X u ω) (X v ω) ^ p} := measure_mono hsub
    _ ≤ (∫⁻ ω, edist (X u ω) (X v ω) ^ p ∂P) / ε ^ p :=
        meas_ge_le_lintegral_div (hX.measurable_edist.aemeasurable.pow_const _) hεp0 hεptop
    _ ≤ M * edist u v ^ q / ε ^ p := by gcongr; exact hX.kolmogorovCondition u v

/-! ### The bad events -/

/-- Some increment of `X` across the level-`n` dyadic grid, over the initial
segment of length `n · 2 ^ n`, is at least `r n`. -/
def badSet (X : ℝ≥0 → Ω → ℝ) (r : ℕ → ℝ) (n : ℕ) : Set Ω :=
  ⋃ k ∈ Finset.range (n * 2 ^ n),
    {ω | ENNReal.ofReal (r n) ≤ edist (X (dyad n (k + 1)) ω) (X (dyad n k) ω)}

theorem measurableSet_badSet (hX : IsKolmogorovProcess X P p q M) (r : ℕ → ℝ) (n : ℕ) :
    MeasurableSet (badSet X r n) := by
  refine Finset.measurableSet_biUnion _ fun k _ => ?_
  exact measurableSet_le measurable_const hX.measurable_edist

omit [MeasurableSpace Ω] in
theorem dyadicIncBound_of_notMem {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) {ω : Ω} {n₀ : ℕ}
    (h : ∀ n, n₀ ≤ n → ω ∉ badSet X r n) : DyadicIncBound (fun t => X t ω) r n₀ := by
  intro n hn k hk
  have hmem : k ∈ Finset.range (n * 2 ^ n) := Finset.mem_range.mpr (by omega)
  have := h n hn
  simp only [badSet, Set.mem_iUnion, Set.mem_setOf_eq, not_exists, exists_prop, not_and] at this
  have hlt : edist (X (dyad n (k + 1)) ω) (X (dyad n k) ω) < ENNReal.ofReal (r n) :=
    not_le.mp (this k hmem)
  rw [edist_dist, Real.dist_eq, ENNReal.ofReal_lt_ofReal_iff (hr n)] at hlt
  exact hlt.le

theorem measure_badSet_le (hX : IsKolmogorovProcess X P p q M) {r : ℕ → ℝ}
    (hr : ∀ n, 0 < r n) (n : ℕ) :
    P (badSet X r n) ≤ (n * 2 ^ n : ℕ) *
      (M * ENNReal.ofReal ((1 : ℝ) / 2 ^ n) ^ q / ENNReal.ofReal (r n) ^ p) := by
  refine le_trans (measure_biUnion_finset_le _ _) ?_
  have hbound : ∀ k ∈ Finset.range (n * 2 ^ n),
      P {ω | ENNReal.ofReal (r n) ≤ edist (X (dyad n (k + 1)) ω) (X (dyad n k) ω)}
        ≤ M * ENNReal.ofReal ((1 : ℝ) / 2 ^ n) ^ q / ENNReal.ofReal (r n) ^ p := by
    intro k _
    refine le_trans (measure_edist_ge_le hX _ _ (by simp [hr n]) ENNReal.ofReal_ne_top) ?_
    rw [edist_dyad_succ]
  refine le_trans (Finset.sum_le_sum hbound) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-! ### The choice of exponent -/

theorem rpow_pow_comm {x : ℝ} (hx : 0 ≤ x) (y : ℝ) (n : ℕ) : (x ^ n) ^ y = (x ^ y) ^ n := by
  rw [← Real.rpow_natCast x n, ← Real.rpow_natCast (x ^ y) n, ← Real.rpow_mul hx,
    ← Real.rpow_mul hx, mul_comm]

theorem two_mul_half_rpow (q : ℝ) : 2 * ((1 : ℝ) / 2) ^ q = (2 : ℝ) ^ (1 - q) := by
  have h1 : ((1 : ℝ) / 2) ^ q = ((2 : ℝ) ^ q)⁻¹ := by
    rw [one_div, Real.inv_rpow (by norm_num)]
  rw [h1, sub_eq_add_neg, Real.rpow_add (by norm_num), Real.rpow_one,
    Real.rpow_neg (by norm_num)]

/-- With `q > 1` there is an exponent `b < 1` for which the level-`n` bad
probabilities form a convergent series. -/
theorem exists_incr_exponent (hp : 0 < p) (hq : 1 < q) :
    ∃ b : ℝ, 0 < b ∧ b < 1 ∧ 2 * ((1 : ℝ) / 2) ^ q / b ^ p < 1 := by
  set β : ℝ := (2 : ℝ) ^ ((1 - q) / p) with hβdef
  have hβpos : 0 < β := Real.rpow_pos_of_pos (by norm_num) _
  have hβlt : β < 1 := by
    refine Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) ?_
    exact div_neg_of_neg_of_pos (by linarith) hp
  refine ⟨(β + 1) / 2, by positivity, by linarith, ?_⟩
  have hβb : β < (β + 1) / 2 := by linarith
  have hpow : β ^ p < ((β + 1) / 2) ^ p := Real.rpow_lt_rpow hβpos.le hβb hp
  have hβp : β ^ p = (2 : ℝ) ^ (1 - q) := by
    rw [hβdef, ← Real.rpow_mul (by norm_num), div_mul_cancel₀ _ hp.ne']
  rw [div_lt_one (by positivity), two_mul_half_rpow, ← hβp]
  exact hpow

/-! ### The summable bound on the bad probabilities -/

theorem measure_badSet_le_ofReal (hX : IsKolmogorovProcess X P p q M) {b : ℝ}
    (hb0 : 0 < b) (n : ℕ) :
    P (badSet X (fun n => b ^ n) n)
      ≤ ENNReal.ofReal ((M : ℝ) * n * (2 * ((1 : ℝ) / 2) ^ q / b ^ p) ^ n) := by
  have hp := hX.p_pos
  set c : ℝ := ((1 : ℝ) / 2) ^ q with hcdef
  set d : ℝ := b ^ p with hddef
  have hc0 : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
  have hd0 : 0 < d := Real.rpow_pos_of_pos hb0 _
  have hkern : ENNReal.ofReal ((1 : ℝ) / 2 ^ n) ^ q = ENNReal.ofReal (c ^ n) := by
    rw [ENNReal.ofReal_rpow_of_pos (by positivity)]
    congr 1
    rw [hcdef, ← rpow_pow_comm (by norm_num) q n, one_div, ← inv_pow, ← one_div]
  have hden : ENNReal.ofReal ((fun n => b ^ n) n) ^ p = ENNReal.ofReal (d ^ n) := by
    rw [ENNReal.ofReal_rpow_of_pos (by positivity)]
    congr 1
    exact rpow_pow_comm hb0.le p n
  refine le_trans (measure_badSet_le hX (fun n => pow_pos hb0 n) n) ?_
  rw [hkern, hden, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_div_of_pos (by positivity)]
  have hcast : ((n * 2 ^ n : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((n : ℝ) * 2 ^ n) := by
    rw [← ENNReal.ofReal_natCast]
    push_cast
    ring_nf
  rw [hcast, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  rw [div_pow, mul_pow]
  ring

theorem summable_badSet_bound {b : ℝ} (hb0 : 0 < b) (hθ : 2 * ((1 : ℝ) / 2) ^ q / b ^ p < 1)
    (M : ℝ≥0) :
    Summable fun n : ℕ => (M : ℝ) * n * (2 * ((1 : ℝ) / 2) ^ q / b ^ p) ^ n := by
  set θ : ℝ := 2 * ((1 : ℝ) / 2) ^ q / b ^ p with hθdef
  have hθ0 : 0 ≤ θ := by
    rw [hθdef]
    positivity
  have hnorm : ‖θ‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hθ0]
  have := (summable_pow_mul_geometric_of_norm_lt_one 1 hnorm).mul_left (M : ℝ)
  refine this.congr fun n => ?_
  simp [pow_one]
  ring

/-! ### The good set -/

/-- **Kolmogorov-Chentsov.**  A process on `ℝ≥0` whose increments satisfy the
Kolmogorov condition with exponent `q > 1` has a modification whose paths are
continuous. -/
theorem exists_continuous_modification (hX : IsKolmogorovProcess X P p q M) (hq : 1 < q) :
    ∃ Y : ℝ≥0 → Ω → ℝ, (∀ t, Measurable (Y t)) ∧ (∀ t, X t =ᵐ[P] Y t) ∧
      ∀ᵐ ω ∂P, Continuous fun t => Y t ω := by
  have hp := hX.p_pos
  obtain ⟨b, hb0, hb1, hθ⟩ := exists_incr_exponent (p := p) (q := q) hp hq
  set r : ℕ → ℝ := fun n => b ^ n with hrdef
  have hrpos : ∀ n, 0 < r n := fun n => pow_pos hb0 n
  have hrsum : Summable r := summable_geometric_of_lt_one hb0.le hb1
  -- Borel-Cantelli
  have hsum : ∑' n : ℕ, P (badSet X r n) ≠ ∞ := by
    have hle : ∀ n, P (badSet X r n)
        ≤ ENNReal.ofReal ((M : ℝ) * n * (2 * ((1 : ℝ) / 2) ^ q / b ^ p) ^ n) :=
      fun n => measure_badSet_le_ofReal hX hb0 n
    have hgs := summable_badSet_bound (q := q) (p := p) hb0 hθ M
    have hnn : ∀ n : ℕ, 0 ≤ (M : ℝ) * n * (2 * ((1 : ℝ) / 2) ^ q / b ^ p) ^ n := by
      intro n
      have : (0 : ℝ) ≤ 2 * ((1 : ℝ) / 2) ^ q / b ^ p := by positivity
      positivity
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hle)
    rw [← ENNReal.ofReal_tsum_of_nonneg hnn hgs]
    exact ENNReal.ofReal_ne_top
  have hBC : P (limsup (badSet X r) atTop) = 0 := measure_limsup_atTop_eq_zero hsum
  -- the good set
  have hgood : ∀ᵐ ω ∂P, ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ω ∉ badSet X r n := by
    rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_) hBC
    simp only [Set.mem_setOf_eq, not_exists, not_forall] at hω
    rw [mem_limsup_iff_frequently_mem, Filter.frequently_atTop]
    intro n₀
    obtain ⟨n, hn, hmem⟩ := hω n₀
    exact ⟨n, hn, by simpa using hmem⟩
  have hlim : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n => X (dtrunc n t) ω) atTop (𝓝 (dlim (fun u => X u ω) t)) := by
    filter_upwards [hgood] with ω hω
    obtain ⟨n₀, hn₀⟩ := hω
    exact fun t => tendsto_dtrunc (dyadicIncBound_of_notMem hrpos hn₀)
      (fun n => (hrpos n).le) hrsum t
  refine ⟨fun t ω => dlim (fun u => X u ω) t, fun t => ?_, fun t => ?_, ?_⟩
  · exact Measurable.limsup fun n => hX.measurable (dtrunc n t)
  · -- the modification property
    have hmeas : TendstoInMeasure P (fun n ω => X (dtrunc n t) ω) atTop (X t) := by
      refine tendstoInMeasure_of_ne_top fun ε hε hε' => ?_
      set c : ℝ := ((1 : ℝ) / 2) ^ q with hcdef
      have hc0 : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
      have hc1 : c < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith)
      have hkern : ∀ n : ℕ, ENNReal.ofReal ((1 : ℝ) / 2 ^ n) ^ q = ENNReal.ofReal (c ^ n) := by
        intro n
        rw [ENNReal.ofReal_rpow_of_pos (by positivity)]
        congr 1
        rw [hcdef, ← rpow_pow_comm (by norm_num) q n, one_div, ← inv_pow, ← one_div]
      have hεp0 : ε ^ p ≠ 0 := by
        simp [ENNReal.rpow_eq_zero_iff, hε.ne', hε', hp, not_lt.2 hp.le]
      have hbdd : ∀ n : ℕ, P {ω | ε ≤ edist (X (dtrunc n t) ω) (X t ω)}
          ≤ ((M : ℝ≥0∞) * (ε ^ p)⁻¹) * ENNReal.ofReal (c ^ n) := by
        intro n
        refine le_trans (measure_edist_ge_le hX _ _ hε.ne' hε') ?_
        have h2 : edist (dtrunc n t) t ^ q ≤ ENNReal.ofReal ((1 : ℝ) / 2 ^ n) ^ q :=
          ENNReal.rpow_le_rpow (edist_dtrunc_le n t) (by linarith)
        refine le_trans (ENNReal.div_le_div_right (mul_le_mul_right h2 _) _) ?_
        rw [hkern n, div_eq_mul_inv, mul_right_comm]
      have hK : (M : ℝ≥0∞) * (ε ^ p)⁻¹ ≠ ∞ :=
        ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.inv_ne_top.mpr hεp0)
      have h1 : Tendsto (fun n : ℕ => ENNReal.ofReal (c ^ n)) atTop (𝓝 0) := by
        have := (ENNReal.continuous_ofReal.tendsto 0).comp
          (tendsto_pow_atTop_nhds_zero_of_lt_one hc0.le hc1)
        simpa [Function.comp_def] using this
      have h3 : Tendsto (fun n : ℕ => ((M : ℝ≥0∞) * (ε ^ p)⁻¹) * ENNReal.ofReal (c ^ n))
          atTop (𝓝 0) := by
        have := ENNReal.Tendsto.const_mul h1 (Or.inr hK)
        simpa using this
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3
        (fun _ => zero_le) hbdd
    obtain ⟨ns, hns, hns'⟩ := hmeas.exists_seq_tendsto_ae
    filter_upwards [hlim, hns'] with ω h1 h2
    exact tendsto_nhds_unique h2 ((h1 t).comp hns.tendsto_atTop)
  · filter_upwards [hgood] with ω hω
    obtain ⟨n₀, hn₀⟩ := hω
    exact continuous_dlim (dyadicIncBound_of_notMem hrpos hn₀) (fun n => (hrpos n).le) hrsum

end LatticeProb

end
