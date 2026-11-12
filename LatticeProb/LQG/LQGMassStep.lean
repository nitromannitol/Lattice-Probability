import Mathlib
import LatticeProb.LQG.LQGMassCross

/-!
# One step of the induction for the positive moments of the mass

Let `h` be a whole-plane Gaussian free field, `μ_n = lqgApprox γ h 2^{-n}` the approximate Liouville
measure at the dyadic scale `2^{-n}`, `f` a cut-off function supported in the disc `closedBall 0 (1/2)`,
`M_n = ∫ f dμ_n`, `r = 2^{-k}/4`, and `X_i = ∫_{S_i} f dμ_n` the masses of the dyadic squares `S_i` of
side `r`. For `p ∈ (m, m+1]` the estimate

`E M_n^p ≤ 4^{p-1} (N_r R^{ζ(p)} C + 4 (N_r^{m+1} D)^{p/(m+1)})`

holds, where `R = 2^{-k}`, `ζ(p) = p(2 + γ²/2) - p²γ²/2`, `N_r` is the number of squares and
`D = ((2/r)^{γ²})^{(m+1)²} K^{m+1}`, assuming the moment bounds `K` for the integer exponents `1 ≤ a ≤ m`
and `C` for the exponent `p` of the recentred and dilated masses at level `n - k` at every square centre.

* `LatticeProb.sum_rpow_le_card_rpow_mul`: `(∑ z_i)^p ≤ (card s)^{p-1} ∑ z_i^p` in `[0, ∞]`.
* `LatticeProb.card_nonconstTuples_le`: the number of non-constant `N`-tuples in `s` is at most `|s|^N`.
* `LatticeProb.LQG.lqgApproxMass_eq_sum_squareClass`: `M_n` is the sum of the square masses, grouped by
  parity class.
* `LatticeProb.LQG.IsWholePlaneGFF.aemeasurable_squareMass`: the square masses are a.e. measurable.
* `LatticeProb.LQG.IsWholePlaneGFF.lintegral_rpow_lqgApproxMass_step`: the one-step estimate above.
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace LatticeProb

/-- Power mean inequality for finite sums in `[0, ∞]`: `(∑ z_i)^p ≤ |s|^{p-1} ∑ z_i^p` for `p ≥ 1`. -/
theorem sum_rpow_le_card_rpow_mul {ι : Type*} (s : Finset ι) (z : ι → ℝ≥0∞) {p : ℝ} (hp : 1 ≤ p)
    (hs : s.Nonempty) :
    (∑ i ∈ s, z i) ^ p ≤ (s.card : ℝ≥0∞) ^ (p - 1) * ∑ i ∈ s, z i ^ p := by
  have hc0 : (s.card : ℝ≥0∞) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
  have hct : (s.card : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  set c : ℝ≥0∞ := (s.card : ℝ≥0∞) with hc
  have hp0 : 0 ≤ p := by linarith
  have hw : ∑ _i ∈ s, c⁻¹ = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, ENNReal.mul_inv_cancel hc0 hct]
  have h := ENNReal.rpow_arith_mean_le_arith_mean_rpow s (fun _ => c⁻¹) z hw hp
  rw [← Finset.mul_sum, ← Finset.mul_sum, ENNReal.mul_rpow_of_nonneg _ _ hp0,
    ENNReal.inv_rpow] at h
  have hcp0 : c ^ p ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hc0) hct).ne'
  have hcpt : c ^ p ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hp0 hct
  calc (∑ i ∈ s, z i) ^ p = c ^ p * ((c ^ p)⁻¹ * (∑ i ∈ s, z i) ^ p) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel hcp0 hcpt, one_mul]
    _ ≤ c ^ p * (c⁻¹ * ∑ i ∈ s, z i ^ p) := mul_le_mul' le_rfl h
    _ = c ^ (p - 1) * ∑ i ∈ s, z i ^ p := by
        rw [← mul_assoc, ENNReal.rpow_sub _ _ hc0 hct, ENNReal.rpow_one, div_eq_mul_inv]

/-- The number of non-constant `N`-tuples with values in `s` is at most `|s|^N`. -/
theorem card_nonconstTuples_le {ι : Type*} (s : Finset ι) (N : ℕ) :
    (nonconstTuples s N).card ≤ s.card ^ N := by
  classical
  calc (nonconstTuples s N).card ≤ (Fintype.piFinset fun _ : Fin N => s).card :=
        Finset.card_le_card fun f hf => Fintype.mem_piFinset.2 (mem_nonconstTuples.1 hf).1
    _ = s.card ^ N := by simp [Fintype.card_piFinset]

end LatticeProb

namespace LatticeProb.LQG

open LatticeProb.Gauss LQGDyadicScaling LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- **Decomposition into squares.** The mass of a cut-off `f` supported in `closedBall 0 (1/2)` is the sum
of the masses of the squares, grouped by parity class. -/
theorem lqgApproxMass_eq_sum_squareClass {r : ℝ} (hr : 0 < r) (γ : ℝ) (h : ℝ → ℂ → ℝ)
    {f : ℂ → ℝ≥0∞} (hf0 : ∀ x ∉ closedBall (0 : ℂ) (1 / 2), f x = 0) (n : ℕ) :
    lqgApproxMass γ h f n = ∑ c : ZMod 2 × ZMod 2,
      ∑ i ∈ (squareIndex r).filter (fun i => squareClass i = c), squareMass γ h f r i n := by
  classical
  unfold lqgApproxMass
  rw [lintegral_eq_sum_dyadicSquare hr _ hf0, Finset.sum_fiberwise (squareIndex r) squareClass
    (fun i => squareMass γ h f r i n)]
  rfl

/-- The square masses are almost everywhere measurable. -/
theorem IsWholePlaneGFF.aemeasurable_squareMass (hh : IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    {f : ℂ → ℝ≥0∞} (hfm : Measurable f) (r : ℝ) (i : ℤ × ℤ) (n : ℕ) :
    AEMeasurable (fun ω => squareMass γ (hcirc ω) f r i n) P := by
  have hε : 0 < dyadicScale n := dyadicScale_pos' n
  obtain ⟨H, hHc, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  have hmul : Measurable fun p : ℂ × Ω => (dyadicSquare r i).indicator f p.1 *
      gmcDensityENN (fun z ω => H ω (dyadicScale n) z) γ (dyadicScale n) p.1 p.2 :=
    ((hfm.indicator (measurableSet_dyadicSquare r i)).comp measurable_fst).mul
      (measurable_uncurry_gmcDensityENN (hHm _ hε) γ _)
  have hm : Measurable fun ω => pieceMass (fun j => (dyadicSquare r j).indicator f)
      (gmcDensityENN (fun z ω => H ω (dyadicScale n) z) γ (dyadicScale n)) i ω :=
    hmul.lintegral_prod_left'
  refine hm.aemeasurable.congr ?_
  filter_upwards [hHae] with ω hω
  exact (squareMass_eq_pieceMass hfm r i (fun z ω => H ω (dyadicScale n) z) ω
    ((hHm _ hε).comp (measurable_id.prodMk measurable_const)) fun z => hω _ _).symm

/-- The centre of a square meeting the disc is at distance at most `1 - 2^{-k}` from the origin
(for `k ≥ 2`). -/
theorem norm_dyadicSquareCentre_add_le {k : ℕ} (hk : 2 ≤ k) {i : ℤ × ℤ}
    (hi : i ∈ squareIndex (dyadicScale k * (1 / 4))) :
    ‖dyadicSquareCentre (dyadicScale k * (1 / 4)) i‖ + dyadicScale k ≤ 1 := by
  have hR4 : dyadicScale k ≤ 1 / 4 := by
    have h2 : dyadicScale 2 = 1 / 4 := by norm_num [dyadicScale]
    exact h2 ▸ dyadicScale_le_of_le hk
  have hr : 0 < dyadicScale k * (1 / 4) := by have := dyadicScale_pos' k; positivity
  have := norm_dyadicSquareCentre_lt hr hi
  linarith

/-- **One step of the induction.** Let `r = 2^{-k}/4`, `2 ≤ k < n`, `1 ≤ m`, `m γ² ≤ 4`, `m < p ≤ m + 1`.
If the recentred and dilated masses at level `n - k` satisfy `E (∫ f dμ'_{n-k})^a ≤ K` for the integers
`1 ≤ a ≤ m` and `E (∫ f dμ'_{n-k})^p ≤ C` at every square centre, then
`E M_n^p ≤ 4^{p-1} (N_r R^{ζ(p)} C + 4 (N_r^{m+1} D)^{p/(m+1)})`. -/
theorem IsWholePlaneGFF.lintegral_rpow_lqgApproxMass_step [IsProbabilityMeasure P]
    (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ} (hγ : γ ≠ 0) {f : ℂ → ℝ≥0∞} (hfm : Measurable f)
    (hf1 : ∀ x, f x ≤ 1) (hf14 : ∀ x ∈ ball (0 : ℂ) (1 / 4), 1 ≤ f x)
    (hf0 : ∀ x ∉ closedBall (0 : ℂ) (1 / 2), f x = 0) {k n : ℕ} (hk : 2 ≤ k) (hkn : k < n)
    {m : ℕ} (hm1 : 1 ≤ m) (hm : (m : ℝ) * γ ^ 2 ≤ 4) {K : ℝ} (hK : 1 ≤ K)
    (hIH : ∀ a : ℕ, 1 ≤ a → a ≤ m → ∀ i ∈ squareIndex (dyadicScale k * (1 / 4)),
      ∫⁻ ω, (lqgApproxMass γ (recentredField hcirc k
        (dyadicSquareCentre (dyadicScale k * (1 / 4)) i) ω) f (n - k)) ^ (a : ℝ) ∂P ≤
        ENNReal.ofReal K)
    {p : ℝ} (hpm : (m : ℝ) < p) (hpm1 : p ≤ m + 1) {C : ℝ}
    (hIHn : ∀ i ∈ squareIndex (dyadicScale k * (1 / 4)),
      ∫⁻ ω, (lqgApproxMass γ (recentredField hcirc k
        (dyadicSquareCentre (dyadicScale k * (1 / 4)) i) ω) f (n - k)) ^ p ∂P ≤ ENNReal.ofReal C) :
    ∫⁻ ω, (lqgApproxMass γ (hcirc ω) f n) ^ p ∂P ≤
      (4 : ℝ≥0∞) ^ (p - 1) *
        (((squareIndex (dyadicScale k * (1 / 4))).card : ℝ≥0∞) *
            (ENNReal.ofReal (dyadicScale k ^ (p * (2 + γ ^ 2 / 2) - p ^ 2 * γ ^ 2 / 2)) *
              ENNReal.ofReal C) +
          4 * (((squareIndex (dyadicScale k * (1 / 4))).card : ℝ≥0∞) ^ (m + 1) *
            (ENNReal.ofReal ((2 / (dyadicScale k * (1 / 4))) ^ γ ^ 2) ^ ((m + 1) * (m + 1)) *
              ENNReal.ofReal K ^ (m + 1))) ^ (p / ((m + 1 : ℕ) : ℝ))) := by
  classical
  set r : ℝ := dyadicScale k * (1 / 4) with hrdef
  have hR : 0 < dyadicScale k := dyadicScale_pos' k
  have hr : 0 < r := by rw [hrdef]; positivity
  have hp1 : 1 ≤ p := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    linarith
  have hp0 : 0 < p := by linarith
  have hN : m + 1 ≠ 0 := Nat.succ_ne_zero m
  let s : ZMod 2 × ZMod 2 → Finset (ℤ × ℤ) := fun c => (squareIndex r).filter fun i => squareClass i = c
  let X : ℤ × ℤ → Ω → ℝ≥0∞ := fun i ω => squareMass γ (hcirc ω) f r i n
  have hX : ∀ i, AEMeasurable (X i) P := fun i =>
    LatticeProb.LQG.IsWholePlaneGFF.aemeasurable_squareMass hh γ hfm r i n
  have hfib : ∀ g : ℤ × ℤ → ℝ≥0∞, ∑ c, ∑ i ∈ s c, g i = ∑ i ∈ squareIndex r, g i := fun g =>
    Finset.sum_fiberwise (squareIndex r) squareClass g
  have hcard4 : ((Finset.univ : Finset (ZMod 2 × ZMod 2)).card : ℝ≥0∞) = 4 := by
    simp
  have hB : ∀ ω, (lqgApproxMass γ (hcirc ω) f n) ^ p ≤
      (4 : ℝ≥0∞) ^ (p - 1) * ∑ c, (∑ i ∈ s c, X i ω) ^ p := by
    intro ω
    rw [lqgApproxMass_eq_sum_squareClass hr γ (hcirc ω) hf0 n]
    have := sum_rpow_le_card_rpow_mul (Finset.univ : Finset (ZMod 2 × ZMod 2))
      (fun c => ∑ i ∈ s c, X i ω) hp1 Finset.univ_nonempty
    rwa [hcard4] at this
  have hmeasc : ∀ c, AEMeasurable (fun ω => (∑ i ∈ s c, X i ω) ^ p) P := fun c =>
    (show AEMeasurable (fun ω => ∑ i ∈ s c, X i ω) P from
      Finset.aemeasurable_fun_sum _ fun i _ => hX i).pow_const p
  have hC : ∫⁻ ω, (lqgApproxMass γ (hcirc ω) f n) ^ p ∂P ≤
      (4 : ℝ≥0∞) ^ (p - 1) * ∑ c, ∫⁻ ω, (∑ i ∈ s c, X i ω) ^ p ∂P := by
    calc _ ≤ ∫⁻ ω, (4 : ℝ≥0∞) ^ (p - 1) * ∑ c, (∑ i ∈ s c, X i ω) ^ p ∂P := lintegral_mono hB
      _ = _ := by
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) (by norm_num)),
          lintegral_finsetSum' _ fun c _ => hmeasc c]
  set D : ℝ≥0∞ := ENNReal.ofReal ((2 / r) ^ γ ^ 2) ^ ((m + 1) * (m + 1)) *
    ENNReal.ofReal K ^ (m + 1) with hD
  set Nr : ℕ := (squareIndex r).card with hNr
  have hcross : ∀ c, (∑ g ∈ nonconstTuples (s c) (m + 1), ∫⁻ ω, ∏ j, X (g j) ω ∂P) ≤
      (Nr : ℝ≥0∞) ^ (m + 1) * D := by
    intro c
    calc _ ≤ ∑ g ∈ nonconstTuples (s c) (m + 1), D := Finset.sum_le_sum fun g hg =>
            LatticeProb.LQG.IsWholePlaneGFF.lintegral_prod_squareMass_le hh hγ hfm hf1 hf14 hf0 hk
              hkn hm hK hIH (Finset.filter_subset _ _)
              (fun i hi j hj => by
                have h1 := (Finset.mem_filter.1 hi).2
                have h2 := (Finset.mem_filter.1 hj).2
                rw [h1, h2]) hg
      _ = (nonconstTuples (s c) (m + 1)).card • D := Finset.sum_const _
      _ ≤ _ := by
        rw [nsmul_eq_mul]
        refine mul_le_mul' ?_ le_rfl
        exact_mod_cast (card_nonconstTuples_le (s c) (m + 1)).trans
          (Nat.pow_le_pow_left (Finset.card_le_card (Finset.filter_subset _ _)) _)
  have hclass : ∀ c, ∫⁻ ω, (∑ i ∈ s c, X i ω) ^ p ∂P ≤ ∑ i ∈ s c, ∫⁻ ω, X i ω ^ p ∂P +
      ((Nr : ℝ≥0∞) ^ (m + 1) * D) ^ (p / ((m + 1 : ℕ) : ℝ)) := by
    intro c
    refine (lintegral_sum_rpow_le P (s c) X hX hN hp0 (by exact_mod_cast hpm1)).trans ?_
    exact add_le_add le_rfl (ENNReal.rpow_le_rpow (hcross c) (by positivity))
  have hdiag : ∑ c, ∑ i ∈ s c, ∫⁻ ω, X i ω ^ p ∂P ≤ (Nr : ℝ≥0∞) *
      (ENNReal.ofReal (dyadicScale k ^ (p * (2 + γ ^ 2 / 2) - p ^ 2 * γ ^ 2 / 2)) *
        ENNReal.ofReal C) := by
    rw [hfib (fun i => ∫⁻ ω, X i ω ^ p ∂P)]
    calc ∑ i ∈ squareIndex r, ∫⁻ ω, X i ω ^ p ∂P ≤ ∑ i ∈ squareIndex r,
          (ENNReal.ofReal (dyadicScale k ^ (p * (2 + γ ^ 2 / 2) - p ^ 2 * γ ^ 2 / 2)) *
            ENNReal.ofReal C) := Finset.sum_le_sum fun i hi => by
          calc ∫⁻ ω, X i ω ^ p ∂P ≤
              ENNReal.ofReal (dyadicScale k ^ (p * (2 + γ ^ 2 / 2) - p ^ 2 * γ ^ 2 / 2)) *
                ∫⁻ ω, (lqgApproxMass γ (recentredField hcirc k (dyadicSquareCentre r i) ω) f
                  (n - k)) ^ p ∂P :=
                LatticeProb.LQG.IsWholePlaneGFF.lintegral_rpow_setLIntegral_le hh hγ hp0.le hkn
                  (norm_dyadicSquareCentre_add_le hk hi) (dyadicSquare_subset_ball hr i) hf1 hf14
            _ ≤ _ := mul_le_mul' le_rfl (hIHn i hi)
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  calc ∫⁻ ω, (lqgApproxMass γ (hcirc ω) f n) ^ p ∂P
      ≤ (4 : ℝ≥0∞) ^ (p - 1) * ∑ c, ∫⁻ ω, (∑ i ∈ s c, X i ω) ^ p ∂P := hC
    _ ≤ (4 : ℝ≥0∞) ^ (p - 1) * ∑ c, (∑ i ∈ s c, ∫⁻ ω, X i ω ^ p ∂P +
          ((Nr : ℝ≥0∞) ^ (m + 1) * D) ^ (p / ((m + 1 : ℕ) : ℝ))) :=
        mul_le_mul' le_rfl (Finset.sum_le_sum fun c _ => hclass c)
    _ = (4 : ℝ≥0∞) ^ (p - 1) * (∑ c, ∑ i ∈ s c, ∫⁻ ω, X i ω ^ p ∂P +
          ∑ _c : ZMod 2 × ZMod 2, ((Nr : ℝ≥0∞) ^ (m + 1) * D) ^ (p / ((m + 1 : ℕ) : ℝ))) := by
        rw [Finset.sum_add_distrib]
    _ ≤ _ := by
        refine mul_le_mul' le_rfl (add_le_add hdiag ?_)
        rw [Finset.sum_const, nsmul_eq_mul, hcard4]

end LatticeProb.LQG
