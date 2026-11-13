import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsCorrelatedBM2
import LatticeProb.Bonanno.BouRabeeGwynne.Upstream.BrownianMotion.Continuity.KolmogorovChentsov

/-!
# Local Hölder continuity of the correlated Brownian pair

Let `μ` be the law of the two-sided correlated Brownian pair `(L, R)` of the mating-of-trees
encoding (`IsCorrelatedBM2 γ μ`, paths in `Path2 = C(ℝ, ℝ × ℝ)`). Each coordinate is a two-sided
standard Brownian motion: the increment `L_s - L_t` is a centred Gaussian of variance `|s - t|`,
so `E |L_s - L_t| ^ (2n) = c_n |s - t| ^ n`. The Kolmogorov-Chentsov criterion (Upstream
`ae_mem_holderSet`) gives Hölder bounds of every exponent `β < (n - 1) / (2n)` on the rational
times of each interval `[-r, r]`; since the sample paths are continuous, these extend to the whole
interval. Hence almost every path is locally `α`-Hölder for every `α < 1/2`.

* `IsCorrelatedBM2.ae_holderOnWith`: for a fixed `α < 1/2`, almost surely every coordinate path is
  `α`-Hölder on every interval `[-T, T]`.
* `IsCorrelatedBM2.ae_forall_holderOnWith`: the same almost surely for all `α < 1/2` at once.
-/

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb.CorrelatedBM

open MatedCRTHarmonic.MatedCRT

/-! ### Real intervals: covering numbers, density extension, exponent comparison -/

/-- Two points of `[-r, r]` are at distance at most `2r`. -/
lemma edist_le_of_mem_Icc {r : ℝ≥0} {x y : ℝ} (hx : x ∈ Set.Icc (-(r : ℝ)) r)
    (hy : y ∈ Set.Icc (-(r : ℝ)) r) : edist x y ≤ ((2 * r : ℝ≥0) : ℝ≥0∞) := by
  rw [edist_dist, Real.dist_eq, ← ENNReal.ofReal_coe_nnreal]
  refine ENNReal.ofReal_le_ofReal (abs_le.2 ⟨?_, ?_⟩)
  · push_cast
    linarith [hx.1, hx.2, hy.1, hy.2]
  · push_cast
    linarith [hx.1, hx.2, hy.1, hy.2]

/-- The interval `[-r, r]` has covering numbers at most `6 r / ε` at every scale `ε ≤ diam`. -/
lemma hasBoundedCoveringNumber_Icc (r : ℝ≥0) (hr : r ≠ 0) :
    HasBoundedCoveringNumber (Set.Icc (-(r : ℝ)) r) (6 * r) 1 := by
  have hsub : Set.Icc (-(r : ℝ)) r ⊆ Metric.closedEBall (0 : ℝ) r := by
    intro x hx
    rw [Metric.mem_closedEBall, edist_dist, Real.dist_eq, sub_zero, ← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal (abs_le.2 hx)
  have hdiam : Metric.ediam (Set.Icc (-(r : ℝ)) r) ≤ ((2 * r : ℝ≥0) : ℝ≥0∞) :=
    Metric.ediam_le fun x hx y hy => edist_le_of_mem_Icc hx hy
  refine ⟨hdiam.trans_lt ENNReal.coe_lt_top, fun ε hε => ?_⟩
  have hε2 : ε / 2 ≤ r := by
    have h : ε ≤ 2 * r := ENNReal.coe_le_coe.1 (hε.trans hdiam)
    rw [div_le_iff₀ two_pos, mul_comm]
    exact h
  calc (coveringNumber ε (Set.Icc (-(r : ℝ)) r) : ℝ≥0∞)
      ≤ coveringNumber (ε / 2) (Metric.closedEBall (0 : ℝ) r) :=
        mod_cast coveringNumber_subset_le hsub
    _ ≤ (3 * r / ((ε / 2 : ℝ≥0) : ℝ≥0∞)) ^ (Module.finrank ℝ ℝ) :=
        coveringNumber_closedBall_le_three_mul hr hε2
    _ = 6 * r * (ε : ℝ≥0∞)⁻¹ ^ (1 : ℝ) := by
        rw [Module.finrank_self, pow_one, ENNReal.rpow_one, ENNReal.coe_div two_ne_zero,
          div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (by simp) (by simp), inv_inv,
          ENNReal.coe_ofNat]
        ring

/-- A Hölder bound on the points of a dense set in `[a, b]` extends to `[a, b]` for a continuous
function. -/
lemma holderOnWith_of_dense {f : ℝ → ℝ} (hf : Continuous f) {D : Set ℝ} (hD : Dense D)
    {a b : ℝ} (hab : a < b) {K β : ℝ≥0}
    (h : ∀ x ∈ D ∩ Set.Icc a b, ∀ y ∈ D ∩ Set.Icc a b,
      edist (f x) (f y) ≤ K * edist x y ^ (β : ℝ)) :
    HolderOnWith K β f (Set.Icc a b) := by
  have hS : IsClosed {p : ℝ × ℝ | edist (f p.1) (f p.2) ≤ K * edist p.1 p.2 ^ (β : ℝ)} :=
    isClosed_le ((hf.comp continuous_fst).edist (hf.comp continuous_snd))
      ((ENNReal.continuous_const_mul ENNReal.coe_ne_top).comp
        (ENNReal.continuous_rpow_const.comp (continuous_fst.edist continuous_snd)))
  have hU : Set.Icc a b ⊆ closure (D ∩ Set.Icc a b) :=
    (closure_Ioo hab.ne).ge.trans (closure_minimal ((hD.open_subset_closure_inter isOpen_Ioo).trans
      (closure_mono fun x hx => ⟨hx.2, Set.Ioo_subset_Icc_self hx.1⟩)) isClosed_closure)
  intro x hx y hy
  have hxy : (x, y) ∈ closure ((D ∩ Set.Icc a b) ×ˢ (D ∩ Set.Icc a b)) := by
    rw [closure_prod_eq]
    exact ⟨hU hx, hU hy⟩
  exact closure_minimal (fun p hp => h p.1 hp.1 p.2 hp.2) hS hxy

/-- On a set of diameter at most `D`, a `β`-Hölder function is `α`-Hölder for `α ≤ β`. -/
lemma holderOnWith_exponent_le {f : ℝ → ℝ} {s : Set ℝ} {K α β D : ℝ≥0}
    (hf : HolderOnWith K β f s) (hαβ : α ≤ β) (hD : ∀ x ∈ s, ∀ y ∈ s, edist x y ≤ D) :
    HolderOnWith (K * D ^ ((β : ℝ) - α)) α f s := by
  have he : 0 ≤ (β : ℝ) - α := sub_nonneg.2 (NNReal.coe_le_coe.2 hαβ)
  intro x hx y hy
  have h2 : edist x y ^ ((β : ℝ) - α) ≤ (D : ℝ≥0∞) ^ ((β : ℝ) - α) :=
    ENNReal.rpow_le_rpow (hD x hx y hy) he
  have h1 : edist x y ^ (β : ℝ) ≤ (D : ℝ≥0∞) ^ ((β : ℝ) - α) * edist x y ^ (α : ℝ) := by
    calc edist x y ^ (β : ℝ) = edist x y ^ ((β : ℝ) - α) * edist x y ^ (α : ℝ) := by
          rw [← ENNReal.rpow_add_of_nonneg _ _ he α.coe_nonneg, sub_add_cancel]
      _ ≤ (D : ℝ≥0∞) ^ ((β : ℝ) - α) * edist x y ^ (α : ℝ) :=
          mul_le_mul_of_nonneg_right h2 zero_le
  calc edist (f x) (f y) ≤ K * edist x y ^ (β : ℝ) := hf x hx y hy
    _ ≤ K * ((D : ℝ≥0∞) ^ ((β : ℝ) - α) * edist x y ^ (α : ℝ)) := by gcongr
    _ = ((K * D ^ ((β : ℝ) - α) : ℝ≥0) : ℝ≥0∞) * edist x y ^ (α : ℝ) := by
        rw [ENNReal.coe_mul, ENNReal.coe_rpow_of_nonneg _ he, mul_assoc]

/-! ### Gaussian moments -/

/-- The `2n`-th absolute moment of `N(0, v)` is `v ^ n` times that of `N(0, 1)`. -/
lemma lintegral_enorm_rpow_gaussianReal_eq_mul (v : ℝ≥0) (n : ℕ) :
    ∫⁻ x : ℝ, ‖x‖ₑ ^ (2 * (n : ℝ)) ∂(gaussianReal 0 v)
      = (v : ℝ≥0∞) ^ (n : ℝ) * ∫⁻ x : ℝ, ‖x‖ₑ ^ (2 * (n : ℝ)) ∂(gaussianReal 0 1) := by
  have hmap : (gaussianReal 0 1).map (fun x : ℝ => Real.sqrt v * x) = gaussianReal 0 v := by
    have := gaussianReal_map_const_mul (μ := 0) (v := 1) (Real.sqrt v)
    rw [mul_zero, mul_one] at this
    rw [show (fun x : ℝ => Real.sqrt v * x) = (Real.sqrt v * ·) from rfl, this]
    congr 1
    rw [← NNReal.coe_inj]
    simp [Real.sq_sqrt v.coe_nonneg]
  rw [← hmap, lintegral_map (by fun_prop) (by fun_prop)]
  have hpt : ∀ x : ℝ, ‖Real.sqrt v * x‖ₑ ^ (2 * (n : ℝ))
      = ENNReal.ofReal (Real.sqrt v) ^ (2 * (n : ℝ)) * ‖x‖ₑ ^ (2 * (n : ℝ)) := by
    intro x
    rw [enorm_mul, ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
    congr 2
    rw [Real.enorm_eq_ofReal (Real.sqrt_nonneg _)]
  simp_rw [hpt]
  rw [lintegral_const_mul _ (by fun_prop)]
  congr 1
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by positivity),
    ← ENNReal.ofReal_coe_nnreal,
    ENNReal.ofReal_rpow_of_nonneg v.coe_nonneg (by positivity)]
  congr 1
  rw [show 2 * (n : ℝ) = ((2 * n : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast,
    Real.rpow_natCast, pow_mul, Real.sq_sqrt v.coe_nonneg]

/-- The `2n`-th absolute moment of `N(0, 1)` is finite. -/
lemma lintegral_enorm_rpow_gaussianReal_ne_top (n : ℕ) (hn : n ≠ 0) :
    ∫⁻ x : ℝ, ‖x‖ₑ ^ (2 * (n : ℝ)) ∂(gaussianReal 0 1) ≠ ∞ := by
  have h := memLp_id_gaussianReal (μ := 0) (v := 1) (2 * n : ℝ≥0)
  have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
    (p := ((2 * n : ℝ≥0) : ℝ≥0∞)) (f := (id : ℝ → ℝ)) (μ := gaussianReal 0 1)
    (by simp [hn]) ENNReal.coe_ne_top h
  simpa using this.ne

/-! ### Increments of the correlated Brownian pair -/

/-- `twoSidedMin s s - 2 twoSidedMin s t + twoSidedMin t t = |s - t|`: the variance of an increment
of a two-sided Brownian motion. -/
lemma twoSidedMin_sub_eq_abs (s t : ℝ) :
    twoSidedMin s s - 2 * twoSidedMin s t + twoSidedMin t t = |s - t| := by
  simp only [twoSidedMin, min_self]
  rw [abs_eq_max_neg]
  simp only [max_def, min_def]
  split_ifs <;> linarith

/-- A coordinate at a fixed time is a measurable function of the path. -/
lemma measurable_lrCoord_path (i : Fin 2) (t : ℝ) : Measurable (lrCoord i t) := by
  unfold lrCoord
  split_ifs
  · exact measurable_fst.comp (ContinuousMap.measurable_eval t)
  · exact measurable_snd.comp (ContinuousMap.measurable_eval t)

/-- Each coordinate path `t ↦ L_t`, `t ↦ R_t` is continuous. -/
lemma continuous_lrCoord_time (i : Fin 2) (b : Path2) : Continuous fun t => lrCoord i t b := by
  unfold lrCoord
  split_ifs
  · exact continuous_fst.comp b.continuous
  · exact continuous_snd.comp b.continuous

variable {γ : ℝ} {μ : Measure Path2}

/-- The increment `L_s - L_t` (or `R_s - R_t`) of the correlated Brownian pair has law
`N(0, |s - t|)`. -/
lemma hasLaw_lrCoord_sub (hμ : IsCorrelatedBM2 γ μ) (i : Fin 2) (s t : ℝ) :
    HasLaw (fun b => lrCoord i s b - lrCoord i t b) (gaussianReal 0 (nndist s t)) μ := by
  have := hμ.isProbabilityMeasure
  have hX := hμ.isGaussianProcess
  have hs : MemLp (lrCoord i s) 2 μ := (hX.hasGaussianLaw_eval (i, s)).memLp_two
  have ht : MemLp (lrCoord i t) 2 μ := (hX.hasGaussianLaw_eval (i, t)).memLp_two
  have hG : HasGaussianLaw (fun b => lrCoord i s b - lrCoord i t b) μ :=
    hX.hasGaussianLaw_fun_sub (s := (i, s)) (t := (i, t))
  have hmean : ∫ b, (lrCoord i s b - lrCoord i t b) ∂μ = 0 := by
    rw [integral_sub (hs.integrable one_le_two) (ht.integrable one_le_two), hμ.integral_eq_zero,
      hμ.integral_eq_zero, sub_zero]
  have hii : lrCov γ i i = 1 := by simp [lrCov]
  have hvar : Var[fun b => lrCoord i s b - lrCoord i t b; μ] = |s - t| := by
    rw [variance_fun_sub hs ht, ← covariance_self hs.aestronglyMeasurable.aemeasurable,
      ← covariance_self ht.aestronglyMeasurable.aemeasurable]
    simp only [hμ.covariance_eq, hii, one_mul]
    exact twoSidedMin_sub_eq_abs s t
  refine ⟨hG.aemeasurable, ?_⟩
  rw [hG.map_eq_gaussianReal, hmean, hvar, ← Real.dist_eq, ← coe_nndist, Real.toNNReal_coe]

/-- `E |L_s - L_t| ^ (2n) = c_n |s - t| ^ n` with `c_n` the `2n`-th absolute moment of `N(0, 1)`. -/
lemma lintegral_edist_lrCoord_rpow (hμ : IsCorrelatedBM2 γ μ) (i : Fin 2) (n : ℕ) (s t : ℝ) :
    ∫⁻ b, edist (lrCoord i s b) (lrCoord i t b) ^ (2 * (n : ℝ)) ∂μ
      = (∫⁻ x : ℝ, ‖x‖ₑ ^ (2 * (n : ℝ)) ∂(gaussianReal 0 1)) * edist s t ^ (n : ℝ) := by
  have hlaw := hasLaw_lrCoord_sub hμ i s t
  calc ∫⁻ b, edist (lrCoord i s b) (lrCoord i t b) ^ (2 * (n : ℝ)) ∂μ
      = ∫⁻ b, (fun x : ℝ => ‖x‖ₑ ^ (2 * (n : ℝ))) (lrCoord i s b - lrCoord i t b) ∂μ :=
        lintegral_congr fun b => by rw [edist_eq_enorm_sub]
    _ = ∫⁻ x : ℝ, ‖x‖ₑ ^ (2 * (n : ℝ)) ∂(gaussianReal 0 (nndist s t)) := by
        rw [← hlaw.map_eq]
        exact (lintegral_map' (f := fun x : ℝ => ‖x‖ₑ ^ (2 * (n : ℝ)))
          (g := fun b => lrCoord i s b - lrCoord i t b) (by fun_prop) hlaw.aemeasurable).symm
    _ = _ := by
        rw [lintegral_enorm_rpow_gaussianReal_eq_mul, edist_nndist, mul_comm]

/-- Each coordinate of the correlated Brownian pair satisfies the Kolmogorov condition with
exponents `p = 2n`, `q = n`. -/
lemma isKolmogorovProcess_lrCoord (hμ : IsCorrelatedBM2 γ μ) (i : Fin 2) (n : ℕ) (hn : 0 < n) :
    IsKolmogorovProcess (fun t b => lrCoord i t b) μ (2 * (n : ℝ)) n
      (∫⁻ x : ℝ, ‖x‖ₑ ^ (2 * (n : ℝ)) ∂(gaussianReal 0 1)).toNNReal := by
  refine IsKolmogorovProcess.mk_of_secondCountableTopology
    (fun t => measurable_lrCoord_path i t) (fun s t => ?_)
    (mul_pos two_pos (Nat.cast_pos.2 hn)) (Nat.cast_pos.2 hn)
  rw [lintegral_edist_lrCoord_rpow hμ i n s t,
    ENNReal.coe_toNNReal (lintegral_enorm_rpow_gaussianReal_ne_top n hn.ne')]

/-- On the event of the Kolmogorov-Chentsov criterion at the rational times of `[-r, r]`, the
coordinate path is `β`-Hölder on all of `[-r, r]`. -/
lemma holderOnWith_Icc_of_mem_holderSet {i : Fin 2} {n : ℕ} (hn : 0 < n) {β : ℝ≥0} (hβ : 0 < β)
    {r : ℝ≥0} (hr : r ≠ 0) {b : Path2}
    (hb : b ∈ holderSet (fun t b => lrCoord i t b) (Set.range ((↑) : ℚ → ℝ)) (2 * (n : ℝ)) β
      (Set.Icc (-(r : ℝ)) r)) :
    ∃ K : ℝ≥0, HolderOnWith K β (fun t => lrCoord i t b) (Set.Icc (-(r : ℝ)) r) := by
  obtain ⟨K, hK⟩ : ∃ K : ℝ≥0, HolderOnWith K β
      (fun t : Set.range ((↑) : ℚ → ℝ) => lrCoord i t b) {t' | (t' : ℝ) ∈ Set.Icc (-(r : ℝ)) r} :=
    ⟨_, holderOnWith_of_mem_holderSet (hasBoundedCoveringNumber_Icc r hr)
      (mul_pos two_pos (Nat.cast_pos.2 hn)) hβ hb⟩
  have hr0 : -(r : ℝ) < r := by
    have h := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hr)
    linarith
  exact ⟨K, holderOnWith_of_dense (continuous_lrCoord_time i b) Rat.denseRange_cast hr0
    fun x hx y hy => hK ⟨x, hx.1⟩ hx.2 ⟨y, hy.1⟩ hy.2⟩

end LatticeProb.CorrelatedBM

namespace MatedCRTHarmonic.MatedCRT

open LatticeProb.CorrelatedBM

/-- **Local Hölder continuity of the correlated Brownian pair.** For `α < 1/2`, almost surely each
coordinate path `t ↦ L_t`, `t ↦ R_t` is `α`-Hölder on every interval `[-T, T]`
(Kolmogorov-Chentsov criterion with the Gaussian moments `E |L_s - L_t| ^ (2n) = c_n |s - t| ^ n`). -/
theorem IsCorrelatedBM2.ae_holderOnWith {γ : ℝ} {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ)
    {α : ℝ≥0} (hα : (α : ℝ) < 1 / 2) (i : Fin 2) :
    ∀ᵐ b ∂μ, ∀ T : ℝ, ∃ C : ℝ≥0, HolderOnWith C α (fun t => lrCoord i t b) (Set.Icc (-T) T) := by
  have := hμ.isProbabilityMeasure
  obtain ⟨β, hβr⟩ : ∃ β : ℝ≥0, (β : ℝ) = (2 * α + 1) / 4 :=
    ⟨⟨(2 * α + 1) / 4, by positivity⟩, rfl⟩
  have hαβ : α ≤ β := by
    rw [← NNReal.coe_le_coe, hβr]
    linarith
  have hβ0 : 0 < β := by
    rw [← NNReal.coe_pos, hβr]
    positivity
  have hpos : 0 < 1 - 2 * (β : ℝ) := by
    rw [hβr]
    linarith
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / (1 - 2 * (β : ℝ)))
  have hn1 : 1 < n * (1 - 2 * (β : ℝ)) := by rwa [div_lt_iff₀ hpos] at hn
  have hq : (1 : ℝ) < n := by
    nlinarith [NNReal.coe_nonneg β, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hn0 : 0 < n := by exact_mod_cast zero_lt_one.trans hq
  have hβ_lt : (β : ℝ) < ((n : ℝ) - 1) / (2 * (n : ℝ)) := by
    rw [lt_div_iff₀ (by linarith)]
    nlinarith
  have hX := isKolmogorovProcess_lrCoord hμ i n hn0
  have hall : ∀ᵐ b ∂μ, ∀ m : ℕ, b ∈ holderSet (fun t b => lrCoord i t b)
      (Set.range ((↑) : ℚ → ℝ)) (2 * (n : ℝ)) β
      (Set.Icc (-(((m : ℝ≥0) + 1 : ℝ≥0) : ℝ)) (((m : ℝ≥0) + 1 : ℝ≥0) : ℝ)) := by
    rw [ae_all_iff]
    exact fun m => ae_mem_holderSet (hasBoundedCoveringNumber_Icc ((m : ℝ≥0) + 1) (by positivity))
      hX (by finiteness) one_pos hq hβ0 hβ_lt (Set.countable_range _)
  filter_upwards [hall] with b hb T
  obtain ⟨m, hm⟩ := exists_nat_ge T
  obtain ⟨K, hK⟩ := holderOnWith_Icc_of_mem_holderSet hn0 hβ0 (by positivity) (hb m)
  refine ⟨_, (holderOnWith_exponent_le hK hαβ fun x hx y hy => edist_le_of_mem_Icc hx hy).mono ?_⟩
  intro x hx
  simp only [Set.mem_Icc] at hx ⊢
  push_cast
  constructor <;> linarith [hx.1, hx.2]

/-- **Local Hölder continuity of the correlated Brownian pair, all exponents at once.** Almost
surely, for every `α < 1/2`, each coordinate path is `α`-Hölder on every interval `[-T, T]`. -/
theorem IsCorrelatedBM2.ae_forall_holderOnWith {γ : ℝ} {μ : Measure Path2}
    (hμ : IsCorrelatedBM2 γ μ) (i : Fin 2) :
    ∀ᵐ b ∂μ, ∀ α : ℝ≥0, (α : ℝ) < 1 / 2 → ∀ T : ℝ, ∃ C : ℝ≥0,
      HolderOnWith C α (fun t => lrCoord i t b) (Set.Icc (-T) T) := by
  have hk : ∀ k : ℕ, ((((k : ℝ≥0) + 1) / (2 * (k : ℝ≥0) + 4) : ℝ≥0) : ℝ) < 1 / 2 := by
    intro k
    push_cast
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have hall := ae_all_iff.2 fun k : ℕ => hμ.ae_holderOnWith (hk k) i
  filter_upwards [hall] with b hb α hα T
  have hpos : 0 < 1 - 2 * (α : ℝ) := by linarith
  obtain ⟨k, hk'⟩ := exists_nat_gt (1 / (1 - 2 * (α : ℝ)))
  have hk1 : 1 < k * (1 - 2 * (α : ℝ)) := by rwa [div_lt_iff₀ hpos] at hk'
  have hkα : α ≤ ((k : ℝ≥0) + 1) / (2 * (k : ℝ≥0) + 4) := by
    rw [← NNReal.coe_le_coe]
    push_cast
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  obtain ⟨m, hm⟩ := exists_nat_ge T
  obtain ⟨C, hC⟩ := hb k ((m : ℝ≥0) : ℝ)
  refine ⟨_, (holderOnWith_exponent_le hC hkα fun x hx y hy => edist_le_of_mem_Icc hx hy).mono ?_⟩
  intro x hx
  simp only [Set.mem_Icc] at hx ⊢
  push_cast
  constructor <;> linarith [hx.1, hx.2]

end MatedCRTHarmonic.MatedCRT
