import LatticeProb.Analysis.StretchedExponentialSummability

/-!
# Multiscale union bounds over dyadic grids

Let `S k` be finite sets of points whose cardinality grows at most like `4 ^ k` (for instance
the points of the grid `2⁻ᵏ ℤ²` in a fixed disc), and let `E k z` be events whose complements
have probability at most `g k`, where `g k` decays faster than every power of `2⁻ᵏ`. Then the
probability that some `E k z` fails at a scale `k ≥ m` decays faster than every power of
`2⁻ᵐ`, hence faster than every power of `ε` as soon as `2⁻ᵐ ≤ 2 ε`.

This is the union bound which turns a per-point stretched-exponential estimate
`P((E k z)ᶜ) ≤ a₀ exp(-a₁ 2^{θ k})`, uniform in the point `z`, into a superpolynomial
estimate for the event that all the `E k z` occur, over all scales `k ≥ m` and all grid points
of mesh `2⁻ᵏ` in the disc `B(0, 2R)`.

## Main results

* `exp_neg_mul_two_rpow_le`: `exp(-a 2^{θ k}) ≤ C (1/2)^{N k}` for every `N`;
* `gridPointsInBall`, `gridPointsInBall_finite`, `ncard_gridPointsInBall_le`: the grid `δ ℤ²`
  has at most `(2ρ/δ + 1)²` points in the open disc `B(0, ρ)`;
* `ncard_gridPointsInBall_dyadic_le`: at most `(4R + 1)² 4ᵏ` points of `2⁻ᵏ ℤ²` in `B(0, 2R)`;
* `measure_iUnion_ge_biUnion_compl_le`: the union bound with rate `(1/2)^{N m}`;
* `measure_iUnion_ge_biUnion_compl_le_pow`: the same with rate `ε ^ N` when `2⁻ᵐ ≤ 2 ε`;
* `measure_iUnion_ge_biUnion_compl_le_pow_of_exp`: the stretched-exponential case;
* `measure_iUnion_ge_gridPointsInBall_compl_le_pow`: the stretched-exponential case over the
  dyadic grids of `B(0, 2R)`.
-/

noncomputable section

open MeasureTheory Set

namespace LatticeProb

/-- A stretched exponential `exp(-a 2^{θ k})` decays faster than every power of `2⁻ᵏ`. -/
theorem exp_neg_mul_two_rpow_le {a θ : ℝ} (ha : 0 < a) (hθ : 0 < θ) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : ℕ,
      Real.exp (-(a * (2 : ℝ) ^ (θ * k))) ≤ C * (2⁻¹ : ℝ) ^ (N * k) := by
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (N : ℝ) ≤ θ * j := by
    obtain ⟨j, hj⟩ := exists_nat_ge ((N : ℝ) / θ)
    exact ⟨j, by rwa [div_le_iff₀ hθ, mul_comm] at hj⟩
  refine ⟨(Nat.factorial j : ℝ) / a ^ j, by positivity, fun k => ?_⟩
  have hx0 : (0 : ℝ) < (2 : ℝ) ^ (θ * k) := Real.rpow_pos_of_pos two_pos _
  have hkey := pow_mul_exp_neg_mul_le_factorial_div a ((2 : ℝ) ^ (θ * k)) ha hx0.le j
  have hxj : (2 : ℝ) ^ (N * k) ≤ ((2 : ℝ) ^ (θ * k)) ^ j := by
    rw [← Real.rpow_mul_natCast two_pos.le, ← Real.rpow_natCast]
    apply Real.rpow_le_rpow_of_exponent_le one_le_two
    push_cast
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  have h2pos : (0 : ℝ) < 2 ^ (N * k) := by positivity
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ h2pos]
  calc Real.exp (-(a * (2 : ℝ) ^ (θ * k))) * 2 ^ (N * k)
      ≤ Real.exp (-(a * (2 : ℝ) ^ (θ * k))) * ((2 : ℝ) ^ (θ * k)) ^ j :=
        mul_le_mul_of_nonneg_left hxj (Real.exp_pos _).le
    _ = ((2 : ℝ) ^ (θ * k)) ^ j * Real.exp (-(a * (2 : ℝ) ^ (θ * k))) := mul_comm _ _
    _ ≤ _ := hkey

/-- The points of the grid `δ ℤ²` lying in the open disc `B(0, ρ)`. -/
def gridPointsInBall (δ ρ : ℝ) : Set ℂ :=
  Metric.ball (0 : ℂ) ρ ∩
    range (fun p : ℤ × ℤ => (δ : ℂ) * ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I))

/-- The grid points of mesh `δ` in `B(0, ρ)` have both coordinates in `[-⌊ρ/δ⌋, ⌊ρ/δ⌋]`. -/
theorem gridPointsInBall_subset_image_box {δ ρ : ℝ} (hδ : 0 < δ) :
    gridPointsInBall δ ρ ⊆
      (fun p : ℤ × ℤ => (δ : ℂ) * ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) ''
        ((Finset.Icc (-⌊ρ / δ⌋) ⌊ρ / δ⌋ ×ˢ Finset.Icc (-⌊ρ / δ⌋) ⌊ρ / δ⌋ :
          Finset (ℤ × ℤ)) : Set (ℤ × ℤ)) := by
  rintro w ⟨hw, p, rfl⟩
  refine ⟨p, ?_, rfl⟩
  rw [Metric.mem_ball, dist_zero_right] at hw
  have hre : ((δ : ℂ) * ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)).re = δ * p.1 := by simp
  have him : ((δ : ℂ) * ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)).im = δ * p.2 := by simp
  have hcoord : ∀ x : ℤ, |δ * (x : ℝ)| < ρ → -⌊ρ / δ⌋ ≤ x ∧ x ≤ ⌊ρ / δ⌋ := by
    intro x hx
    rw [abs_mul, abs_of_pos hδ] at hx
    have hx' : |(x : ℝ)| ≤ ρ / δ := by
      rw [le_div_iff₀ hδ]
      linarith
    obtain ⟨hx1, hx2⟩ := abs_le.mp hx'
    refine ⟨neg_le.mpr (Int.le_floor.mpr ?_), Int.le_floor.mpr hx2⟩
    push_cast
    linarith
  have h1 := hcoord p.1 (by
    rw [← hre]
    exact (Complex.abs_re_le_norm _).trans_lt hw)
  have h2 := hcoord p.2 (by
    rw [← him]
    exact (Complex.abs_im_le_norm _).trans_lt hw)
  simp only [Finset.coe_product, Finset.coe_Icc, Set.mem_prod, Set.mem_Icc]
  exact ⟨h1, h2⟩

/-- There are finitely many grid points of mesh `δ > 0` in a disc. -/
theorem gridPointsInBall_finite {δ ρ : ℝ} (hδ : 0 < δ) : (gridPointsInBall δ ρ).Finite :=
  ((Finset.finite_toSet _).image _).subset (gridPointsInBall_subset_image_box hδ)

/-- The grid `δ ℤ²` has at most `(2ρ/δ + 1)²` points in the open disc `B(0, ρ)`. -/
theorem ncard_gridPointsInBall_le {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 ≤ ρ) :
    ((gridPointsInBall δ ρ).ncard : ℝ) ≤ (2 * ρ / δ + 1) ^ 2 := by
  have hn0 : 0 ≤ ⌊ρ / δ⌋ := Int.floor_nonneg.mpr (div_nonneg hρ hδ.le)
  have hle : (gridPointsInBall δ ρ).ncard ≤
      (Finset.Icc (-⌊ρ / δ⌋) ⌊ρ / δ⌋ ×ˢ Finset.Icc (-⌊ρ / δ⌋) ⌊ρ / δ⌋).card := by
    calc (gridPointsInBall δ ρ).ncard
        ≤ ((fun p : ℤ × ℤ => (δ : ℂ) * ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) ''
            ((Finset.Icc (-⌊ρ / δ⌋) ⌊ρ / δ⌋ ×ˢ Finset.Icc (-⌊ρ / δ⌋) ⌊ρ / δ⌋ :
              Finset (ℤ × ℤ)) : Set (ℤ × ℤ))).ncard :=
          Set.ncard_le_ncard (gridPointsInBall_subset_image_box hδ)
            ((Finset.finite_toSet _).image _)
      _ ≤ ((Finset.Icc (-⌊ρ / δ⌋) ⌊ρ / δ⌋ ×ˢ Finset.Icc (-⌊ρ / δ⌋) ⌊ρ / δ⌋ :
              Finset (ℤ × ℤ)) : Set (ℤ × ℤ)).ncard := Set.ncard_image_le (Finset.finite_toSet _)
      _ = _ := Set.ncard_coe_finset _
  have hIccZ : ((Finset.Icc (-⌊ρ / δ⌋) ⌊ρ / δ⌋).card : ℤ) = 2 * ⌊ρ / δ⌋ + 1 := by
    simp only [Int.card_Icc]
    omega
  have hIcc : ((Finset.Icc (-⌊ρ / δ⌋) ⌊ρ / δ⌋).card : ℝ) = 2 * (⌊ρ / δ⌋ : ℝ) + 1 := by
    rw [← Int.cast_natCast, hIccZ]
    push_cast
    ring
  have hfl : ((⌊ρ / δ⌋ : ℤ) : ℝ) ≤ ρ / δ := Int.floor_le _
  have hfl0 : (0 : ℝ) ≤ ((⌊ρ / δ⌋ : ℤ) : ℝ) := by exact_mod_cast hn0
  calc ((gridPointsInBall δ ρ).ncard : ℝ)
      ≤ ((Finset.Icc (-⌊ρ / δ⌋) ⌊ρ / δ⌋ ×ˢ Finset.Icc (-⌊ρ / δ⌋) ⌊ρ / δ⌋).card : ℝ) := by
        exact_mod_cast hle
    _ = ((Finset.Icc (-⌊ρ / δ⌋) ⌊ρ / δ⌋).card : ℝ) ^ 2 := by
        rw [Finset.card_product]
        push_cast
        ring
    _ = (2 * (⌊ρ / δ⌋ : ℝ) + 1) ^ 2 := by rw [hIcc]
    _ ≤ (2 * ρ / δ + 1) ^ 2 := by
        apply pow_le_pow_left₀ (by linarith)
        rw [mul_div_assoc]
        linarith

/-- The grid `2⁻ᵏ ℤ²` has at most `(4R + 1)² 4ᵏ` points in the open disc `B(0, 2R)`. -/
theorem ncard_gridPointsInBall_dyadic_le {R : ℝ} (hR : 0 ≤ R) (k : ℕ) :
    ((gridPointsInBall ((2⁻¹ : ℝ) ^ k) (2 * R)).ncard : ℝ) ≤ (4 * R + 1) ^ 2 * 4 ^ k := by
  refine (ncard_gridPointsInBall_le (by positivity) (by positivity)).trans ?_
  have h2k : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ one_le_two
  have hdiv : 2 * (2 * R) / (2⁻¹ : ℝ) ^ k = 4 * R * 2 ^ k := by
    rw [inv_pow, div_inv_eq_mul]
    ring
  have h4 : (4 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ 2 := by
    rw [← pow_mul, mul_comm, pow_mul]
    norm_num
  rw [hdiv, h4, ← mul_pow]
  apply pow_le_pow_left₀ (by positivity)
  nlinarith

/-- **Multiscale union bound.** Let `S k` have at most `C₀ 4ᵏ` points and let the events `E k z`,
`z ∈ S k`, fail with probability at most `g k` for `k ≥ k₀`, where `g` decays faster than every
power of `2⁻ᵏ`. Then for every `N` the probability that some `E k z` fails at a scale
`k ≥ m ≥ k₀` is at most `K (1/2)^{N m}`. -/
theorem measure_iUnion_ge_biUnion_compl_le {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S : ℕ → Finset ι) (E : ℕ → ι → Set Ω) {C₀ : ℝ}
    (hS : ∀ k, ((S k).card : ℝ) ≤ C₀ * 4 ^ k) (g : ℕ → ℝ) (k₀ : ℕ)
    (hE : ∀ k, k₀ ≤ k → ∀ z ∈ S k, P (E k z)ᶜ ≤ ENNReal.ofReal (g k))
    (hg : ∀ N : ℕ, ∃ C : ℝ, ∀ k : ℕ, g k ≤ C * (2⁻¹ : ℝ) ^ (N * k)) (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ, k₀ ≤ m →
      P (⋃ (k : ℕ) (_ : m ≤ k), ⋃ z ∈ S k, (E k z)ᶜ) ≤
        ENNReal.ofReal (K * (2⁻¹ : ℝ) ^ (N * m)) := by
  obtain ⟨C, hC⟩ := hg (N + 3)
  obtain ⟨C', hC'⟩ : ∃ C' : ℝ, C' = max C₀ 0 * max C 0 := ⟨_, rfl⟩
  have hC'0 : 0 ≤ C' := hC' ▸ mul_nonneg (le_max_right _ _) (le_max_right _ _)
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = (2⁻¹ : ℝ) ^ (N + 1) := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := hq ▸ by positivity
  have hqhalf : q ≤ 2⁻¹ := hq ▸ pow_le_of_le_one (by norm_num) (by norm_num) (Nat.succ_ne_zero N)
  have hq1 : q < 1 := hqhalf.trans_lt (by norm_num)
  have hid : ∀ k : ℕ, (4 : ℝ) ^ k * (2⁻¹ : ℝ) ^ ((N + 3) * k) = q ^ k := by
    intro k
    have h4 : (4 : ℝ) ^ k * ((2⁻¹ : ℝ) ^ 2) ^ k = 1 := by
      rw [← mul_pow]
      norm_num
    rw [hq, ← pow_mul, show (N + 3) * k = (N + 1) * k + 2 * k by ring, pow_add,
      pow_mul (2⁻¹ : ℝ) 2 k, mul_left_comm, h4, mul_one]
  have hscale : ∀ k, k₀ ≤ k → P (⋃ z ∈ S k, (E k z)ᶜ) ≤ ENNReal.ofReal (C' * q ^ k) := by
    intro k hk
    have hreal : ((S k).card : ℝ) * g k ≤ C' * q ^ k := by
      by_cases hgk : g k ≤ 0
      · exact (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) hgk).trans (by positivity)
      · have hgk' : 0 ≤ g k := (not_le.mp hgk).le
        have h1 : ((S k).card : ℝ) ≤ max C₀ 0 * 4 ^ k :=
          (hS k).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
        have h2 : g k ≤ max C 0 * (2⁻¹ : ℝ) ^ ((N + 3) * k) :=
          (hC k).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
        calc ((S k).card : ℝ) * g k
            ≤ (max C₀ 0 * 4 ^ k) * (max C 0 * (2⁻¹ : ℝ) ^ ((N + 3) * k)) :=
              mul_le_mul h1 h2 hgk' (mul_nonneg (le_max_right _ _) (by positivity))
          _ = C' * ((4 : ℝ) ^ k * (2⁻¹ : ℝ) ^ ((N + 3) * k)) := by rw [hC']; ring
          _ = C' * q ^ k := by rw [hid]
    calc P (⋃ z ∈ S k, (E k z)ᶜ) ≤ ∑ z ∈ S k, P (E k z)ᶜ := measure_biUnion_finset_le _ _
      _ ≤ ∑ _z ∈ S k, ENNReal.ofReal (g k) := Finset.sum_le_sum (fun z hz => hE k hk z hz)
      _ = ((S k).card : ENNReal) * ENNReal.ofReal (g k) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ENNReal.ofReal (((S k).card : ℝ) * g k) := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (C' * q ^ k) := ENNReal.ofReal_le_ofReal hreal
  refine ⟨C' * 2, by positivity, fun m hm => ?_⟩
  have hsub : (⋃ (k : ℕ) (_ : m ≤ k), ⋃ z ∈ S k, (E k z)ᶜ) ⊆
      ⋃ j : ℕ, ⋃ z ∈ S (j + m), (E (j + m) z)ᶜ := by
    intro ω hω
    simp only [mem_iUnion] at hω ⊢
    obtain ⟨k, hk, z, hz, hωz⟩ := hω
    refine ⟨k - m, ?_⟩
    rw [Nat.sub_add_cancel hk]
    exact ⟨z, hz, hωz⟩
  have hsumm : Summable (fun j : ℕ => C' * q ^ (j + m)) :=
    ((summable_geometric_of_lt_one hq0 hq1).mul_left (C' * q ^ m)).congr
      (fun j => by rw [pow_add]; ring)
  have htsum : ∑' j : ℕ, C' * q ^ (j + m) = C' * q ^ m * (1 - q)⁻¹ := by
    rw [← tsum_geometric_of_lt_one hq0 hq1, ← tsum_mul_left]
    congr 1
    funext j
    rw [pow_add]
    ring
  have hinv : (1 - q)⁻¹ ≤ 2 := by
    rw [inv_eq_one_div, div_le_iff₀ (by linarith)]
    linarith
  have hqm : q ^ m ≤ (2⁻¹ : ℝ) ^ (N * m) := by
    rw [hq, ← pow_mul]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by nlinarith)
  have hreal : C' * q ^ m * (1 - q)⁻¹ ≤ C' * 2 * (2⁻¹ : ℝ) ^ (N * m) := by
    have h1 : q ^ m * (1 - q)⁻¹ ≤ (2⁻¹ : ℝ) ^ (N * m) * 2 :=
      mul_le_mul hqm hinv (inv_nonneg.mpr (by linarith)) (by positivity)
    calc C' * q ^ m * (1 - q)⁻¹ = C' * (q ^ m * (1 - q)⁻¹) := by ring
      _ ≤ C' * ((2⁻¹ : ℝ) ^ (N * m) * 2) := mul_le_mul_of_nonneg_left h1 hC'0
      _ = C' * 2 * (2⁻¹ : ℝ) ^ (N * m) := by ring
  calc P (⋃ (k : ℕ) (_ : m ≤ k), ⋃ z ∈ S k, (E k z)ᶜ)
      ≤ P (⋃ j : ℕ, ⋃ z ∈ S (j + m), (E (j + m) z)ᶜ) := measure_mono hsub
    _ ≤ ∑' j : ℕ, P (⋃ z ∈ S (j + m), (E (j + m) z)ᶜ) := measure_iUnion_le _
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (C' * q ^ (j + m)) :=
        ENNReal.tsum_le_tsum (fun j => hscale (j + m) (by omega))
    _ = ENNReal.ofReal (∑' j : ℕ, C' * q ^ (j + m)) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity) hsumm).symm
    _ ≤ ENNReal.ofReal (C' * 2 * (2⁻¹ : ℝ) ^ (N * m)) := by
        rw [htsum]
        exact ENNReal.ofReal_le_ofReal hreal

/-- **Multiscale union bound, `ε` form.** Under the hypotheses of
`measure_iUnion_ge_biUnion_compl_le`, the failure probability over the scales `k ≥ m` is
`O(ε ^ N)` for every `N`, uniformly over the `m ≥ k₀` with `2⁻ᵐ ≤ 2 ε`. -/
theorem measure_iUnion_ge_biUnion_compl_le_pow {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (S : ℕ → Finset ι) (E : ℕ → ι → Set Ω) {C₀ : ℝ}
    (hS : ∀ k, ((S k).card : ℝ) ≤ C₀ * 4 ^ k) (g : ℕ → ℝ) (k₀ : ℕ)
    (hE : ∀ k, k₀ ≤ k → ∀ z ∈ S k, P (E k z)ᶜ ≤ ENNReal.ofReal (g k))
    (hg : ∀ N : ℕ, ∃ C : ℝ, ∀ k : ℕ, g k ≤ C * (2⁻¹ : ℝ) ^ (N * k)) (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ε : ℝ) (m : ℕ), k₀ ≤ m → (2⁻¹ : ℝ) ^ m ≤ 2 * ε →
      P (⋃ (k : ℕ) (_ : m ≤ k), ⋃ z ∈ S k, (E k z)ᶜ) ≤ ENNReal.ofReal (K * ε ^ N) := by
  obtain ⟨K, hK, hb⟩ := measure_iUnion_ge_biUnion_compl_le P S E hS g k₀ hE hg N
  refine ⟨K * 2 ^ N, by positivity, fun ε m hm hε => (hb m hm).trans
    (ENNReal.ofReal_le_ofReal ?_)⟩
  rw [pow_mul']
  calc K * ((2⁻¹ : ℝ) ^ m) ^ N ≤ K * (2 * ε) ^ N := by gcongr
    _ = K * 2 ^ N * ε ^ N := by rw [mul_pow]; ring

/-- **Multiscale union bound, stretched-exponential case.** If `S k` has at most `C₀ 4ᵏ` points
and every `E k z`, `z ∈ S k`, `k ≥ k₀`, fails with probability at most `a₀ exp(-a₁ 2^{θ k})`, then
for every `N` the failure probability over the scales `k ≥ m` is `O(ε ^ N)`, uniformly over the
`m ≥ k₀` with `2⁻ᵐ ≤ 2 ε`. -/
theorem measure_iUnion_ge_biUnion_compl_le_pow_of_exp {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (S : ℕ → Finset ι) (E : ℕ → ι → Set Ω) {C₀ a₀ a₁ θ : ℝ}
    (hS : ∀ k, ((S k).card : ℝ) ≤ C₀ * 4 ^ k) (ha₁ : 0 < a₁) (hθ : 0 < θ) (k₀ : ℕ)
    (hE : ∀ k, k₀ ≤ k → ∀ z ∈ S k,
      P (E k z)ᶜ ≤ ENNReal.ofReal (a₀ * Real.exp (-(a₁ * (2 : ℝ) ^ (θ * k))))) (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ε : ℝ) (m : ℕ), k₀ ≤ m → (2⁻¹ : ℝ) ^ m ≤ 2 * ε →
      P (⋃ (k : ℕ) (_ : m ≤ k), ⋃ z ∈ S k, (E k z)ᶜ) ≤ ENNReal.ofReal (K * ε ^ N) := by
  refine measure_iUnion_ge_biUnion_compl_le_pow P S E hS _ k₀ hE (fun M => ?_) N
  obtain ⟨C, hC0, hC⟩ := exp_neg_mul_two_rpow_le ha₁ hθ M
  refine ⟨|a₀| * C, fun k => ?_⟩
  calc a₀ * Real.exp (-(a₁ * (2 : ℝ) ^ (θ * k)))
      ≤ |a₀| * Real.exp (-(a₁ * (2 : ℝ) ^ (θ * k))) :=
        mul_le_mul_of_nonneg_right (le_abs_self a₀) (Real.exp_pos _).le
    _ ≤ |a₀| * (C * (2⁻¹ : ℝ) ^ (M * k)) := mul_le_mul_of_nonneg_left (hC k) (abs_nonneg a₀)
    _ = |a₀| * C * (2⁻¹ : ℝ) ^ (M * k) := by ring

/-- **Multiscale union bound over the dyadic grids of a disc.** Let `E k z` be events indexed by
the scales `k` and the points `z` of the grid `2⁻ᵏ ℤ²` in the open disc `B(0, 2R)`, each failing
with probability at most `a₀ exp(-a₁ 2^{θ k})` for `k ≥ k₀`. Then for every `N` the probability
that some `E k z` fails at a scale `k ≥ m` is `O(ε ^ N)`, uniformly over the `m ≥ k₀` with
`2⁻ᵐ ≤ 2 ε`. -/
theorem measure_iUnion_ge_gridPointsInBall_compl_le_pow {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (E : ℕ → ℂ → Set Ω) {R a₀ a₁ θ : ℝ} (hR : 0 ≤ R) (ha₁ : 0 < a₁)
    (hθ : 0 < θ) (k₀ : ℕ)
    (hE : ∀ k, k₀ ≤ k → ∀ z ∈ gridPointsInBall ((2⁻¹ : ℝ) ^ k) (2 * R),
      P (E k z)ᶜ ≤ ENNReal.ofReal (a₀ * Real.exp (-(a₁ * (2 : ℝ) ^ (θ * k))))) (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ε : ℝ) (m : ℕ), k₀ ≤ m → (2⁻¹ : ℝ) ^ m ≤ 2 * ε →
      P (⋃ (k : ℕ) (_ : m ≤ k), ⋃ z ∈ gridPointsInBall ((2⁻¹ : ℝ) ^ k) (2 * R), (E k z)ᶜ) ≤
        ENNReal.ofReal (K * ε ^ N) := by
  have hfin : ∀ k : ℕ, (gridPointsInBall ((2⁻¹ : ℝ) ^ k) (2 * R)).Finite :=
    fun k => gridPointsInBall_finite (by positivity)
  obtain ⟨K, hK, hb⟩ := measure_iUnion_ge_biUnion_compl_le_pow_of_exp P
    (fun k => (hfin k).toFinset) E (C₀ := (4 * R + 1) ^ 2)
    (fun k => by
      rw [← Set.ncard_eq_toFinset_card _ (hfin k)]
      exact ncard_gridPointsInBall_dyadic_le hR k)
    ha₁ hθ k₀ (fun k hk z hz => hE k hk z ((hfin k).mem_toFinset.mp hz)) N
  refine ⟨K, hK, fun ε m hm hε => ?_⟩
  have h := hb ε m hm hε
  simp only [Set.Finite.mem_toFinset] at h
  exact h

end LatticeProb
