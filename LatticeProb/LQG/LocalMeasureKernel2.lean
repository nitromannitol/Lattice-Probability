import LatticeProb.LQG.LocalMeasureKernel
import LatticeProb.Gauss.CircleAverageApprox2
import LatticeProb.LQG.LQGMeasureDerived
import LatticeProb.Gauss.GFF
import LatticeProb.Gauss.GFFAffineInvariance

/-!
# Local decoder: layers 1 to 3

The parameter domain `LocalParam` of the circles in a disc `ball c R`, its unit-mass bump `bumpRho`, the local tests
`localTest`, the observation `obsAt`, the circle coordinate `localCoord`, and the existence of a local decoder
`exists_localDecoder`. The circle coordinates of the observation converge almost surely to the centred circle averages
of a whole-plane GFF. The approximants, the discrete decoder and the kernel are in `LatticeProb.LQG.LocalMeasureKernel3`.
The general lemmas used here are proved in this file: `integrable_mul_wholePlaneCov`,
`wholePlaneGFFCov_pairing_linear_left/right`, `ae_pairing_linear_combination`, and `tendsto_unitCircleDensity_mul_log`.
No hypothesis is added.
-/

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal
open LatticeProb.Gauss LatticeProb.LQG

universe u

namespace LatticeProb.LocalMeasureKernel

/-- The local mean-zero observation of the field `h = h^ℂ - α₀ log|·|` on a set `D`: the pairings of `h` with the
mean-zero test functions supported in `D`. -/
noncomputable def localMeanZeroObs (α₀ : ℝ) (D : Set ℂ) (hC : (ℂ → ℝ) → ℝ) :
    {φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0} → ℝ :=
  fun φ => fieldPairing α₀ hC φ.1

/-- The covariance kernel is integrable against a compactly supported
continuous density at every fixed point. -/
theorem integrable_mul_wholePlaneCov {g : ℂ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (x : ℂ) :
    Integrable (fun y => g y * wholePlaneCov x y) := by
  have hgi : Integrable g := hg.integrable_of_hasCompactSupport hgc
  have hni : Integrable (fun y => g y * wholePlaneNormalization y) :=
    (hg.mul continuous_wholePlaneNormalization).integrable_of_hasCompactSupport hgc.mul_right
  have hli : Integrable (fun y => g y * Real.log ‖y - x‖) := by
    have h := (locallyIntegrable_comp_sub_of_integrableOn_ball integrableOn_ball_log_norm x
      ).integrable_smul_right_of_hasCompactSupport hg hgc
    simpa only [smul_eq_mul, mul_comm] using h
  have hi : Integrable (fun y => (g y * wholePlaneNormalization x +
      g y * wholePlaneNormalization y) - g y * Real.log ‖y - x‖) :=
    ((hgi.mul_const _).add hni).sub hli
  apply hi.congr
  filter_upwards [ae_ne_complex x] with y hy
  have hxy : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hy.symm)
  have hx : max ‖x‖ 1 ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  have hy' : max ‖y‖ 1 ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_right _ _))
  rw [wholePlaneCov, Real.log_div (mul_ne_zero hx hy') hxy, Real.log_mul hx hy',
    norm_sub_rev]
  simp only [wholePlaneNormalization]
  ring


section PairingLinear

open ProbabilityTheory

theorem wholePlaneGFFCov_pairing_linear_left {φ ψ χ : ℂ → ℝ}
    (hφ : IsTestFunction univ φ) (hψ : IsTestFunction univ ψ)
    (hχ : IsTestFunction univ χ) (a b : ℝ) :
    wholePlaneGFFCov (.pairing (fun x => a * φ x + b * ψ x)) (.pairing χ) =
      a * wholePlaneGFFCov (.pairing φ) (.pairing χ) +
        b * wholePlaneGFFCov (.pairing ψ) (.pairing χ) := by
  let p : ℂ → ℝ := fun x => ∫ y, χ y * wholePlaneCov x y
  have hp : Continuous p := AffineDerived.continuous_wholePlaneCov_potential_general hχ.1.continuous hχ.2.1
  have hφp : Integrable (fun x => φ x * p x) :=
    (hφ.1.continuous.mul hp).integrable_of_hasCompactSupport hφ.2.1.mul_right
  have hψp : Integrable (fun x => ψ x * p x) :=
    (hψ.1.continuous.mul hp).integrable_of_hasCompactSupport hψ.2.1.mul_right
  change (∫ x, (a * φ x + b * ψ x) * p x) =
    a * (∫ x, φ x * p x) + b * (∫ x, ψ x * p x)
  have heq : (fun x => (a * φ x + b * ψ x) * p x) =
      fun x => a * (φ x * p x) + b * (ψ x * p x) := by
    funext x
    ring
  rw [heq, integral_add (hφp.const_mul a) (hψp.const_mul b), integral_const_mul,
    integral_const_mul]

/-- Covariance is linear in its second test function. -/
theorem wholePlaneGFFCov_pairing_linear_right {φ ψ χ : ℂ → ℝ}
    (hφ : IsTestFunction univ φ) (hψ : IsTestFunction univ ψ)
    (hχ : IsTestFunction univ χ) (a b : ℝ) :
    wholePlaneGFFCov (.pairing χ) (.pairing (fun x => a * φ x + b * ψ x)) =
      a * wholePlaneGFFCov (.pairing χ) (.pairing φ) +
        b * wholePlaneGFFCov (.pairing χ) (.pairing ψ) := by
  let p : ℂ → ℝ := fun x => ∫ y, φ y * wholePlaneCov x y
  let q : ℂ → ℝ := fun x => ∫ y, ψ y * wholePlaneCov x y
  have hp : Continuous p := AffineDerived.continuous_wholePlaneCov_potential_general hφ.1.continuous hφ.2.1
  have hq : Continuous q := AffineDerived.continuous_wholePlaneCov_potential_general hψ.1.continuous hψ.2.1
  have hχp : Integrable (fun x => χ x * p x) :=
    (hχ.1.continuous.mul hp).integrable_of_hasCompactSupport hχ.2.1.mul_right
  have hχq : Integrable (fun x => χ x * q x) :=
    (hχ.1.continuous.mul hq).integrable_of_hasCompactSupport hχ.2.1.mul_right
  have hinner (x : ℂ) : (∫ y, (a * φ y + b * ψ y) * wholePlaneCov x y) =
      a * p x + b * q x := by
    have heq : (fun y => (a * φ y + b * ψ y) * wholePlaneCov x y) =
        fun y => a * (φ y * wholePlaneCov x y) + b * (ψ y * wholePlaneCov x y) := by
      funext y
      ring
    rw [heq, integral_add ((integrable_mul_wholePlaneCov hφ.1.continuous hφ.2.1 x).const_mul a)
      ((integrable_mul_wholePlaneCov hψ.1.continuous hψ.2.1 x).const_mul b),
      integral_const_mul, integral_const_mul]
  change (∫ x, χ x * (∫ y, (a * φ y + b * ψ y) * wholePlaneCov x y)) =
    a * (∫ x, χ x * p x) + b * (∫ x, χ x * q x)
  simp_rw [hinner]
  have heq : (fun x => χ x * (a * p x + b * q x)) =
      fun x => a * (χ x * p x) + b * (χ x * q x) := by
    funext x
    ring
  rw [heq, integral_add (hχp.const_mul a) (hχq.const_mul b), integral_const_mul,
    integral_const_mul]

/-- For each fixed pair of tests and fixed coefficients, GFF pairings obey
linearity almost surely. The exceptional null set may depend on the tests and
coefficients. -/
theorem ae_pairing_linear_combination
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (h : IsWholePlaneGFF P hC hcirc) {φ ψ : ℂ → ℝ}
    (hφ : IsTestFunction univ φ) (hψ : IsTestFunction univ ψ) (a b : ℝ) :
    ∀ᵐ ω ∂P, hC ω (fun x => a * φ x + b * ψ x) = a * hC ω φ + b * hC ω ψ := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  let θ : ℂ → ℝ := fun x => a * φ x + b * ψ x
  have hθ : IsTestFunction univ θ := hφ.const_mul_add_const_mul hψ a b
  let X : Ω → ℝ := fun ω => hC ω φ
  let Y : Ω → ℝ := fun ω => hC ω ψ
  let Z : Ω → ℝ := fun ω => hC ω θ
  have hX : MemLp X 2 P :=
    (h.isGaussianProcess.hasGaussianLaw_eval ⟨.pairing φ, hφ⟩).memLp (by simp)
  have hY : MemLp Y 2 P :=
    (h.isGaussianProcess.hasGaussianLaw_eval ⟨.pairing ψ, hψ⟩).memLp (by simp)
  have hZ : MemLp Z 2 P :=
    (h.isGaussianProcess.hasGaussianLaw_eval ⟨.pairing θ, hθ⟩).memLp (by simp)
  have hA : MemLp (a • X) 2 P := hX.const_smul a
  have hB : MemLp (b • Y) 2 P := hY.const_smul b
  have hErr : MemLp (Z - (a • X + b • Y)) 2 P := hZ.sub (hA.add hB)
  have hmeanX : ∫ ω, X ω ∂P = 0 := h.integral_eq_zero (.pairing φ) hφ
  have hmeanY : ∫ ω, Y ω ∂P = 0 := h.integral_eq_zero (.pairing ψ) hψ
  have hmeanZ : ∫ ω, Z ω ∂P = 0 := h.integral_eq_zero (.pairing θ) hθ
  have hmean : ∫ ω, (Z - (a • X + b • Y)) ω ∂P = 0 := by
    change (∫ ω, Z ω - (a * X ω + b * Y ω) ∂P) = 0
    have hiX := (hX.integrable (by simp)).const_mul a
    have hiY := (hY.integrable (by simp)).const_mul b
    have hs : Integrable (fun ω => a * X ω + b * Y ω) P := hiX.add hiY
    rw [integral_sub (hZ.integrable (by simp)) hs,
      integral_add hiX hiY, integral_const_mul, integral_const_mul,
      hmeanX, hmeanY, hmeanZ, mul_zero, mul_zero, add_zero, sub_zero]
  have hcov (f g : ℂ → ℝ) (hf : IsTestFunction univ f) (hg : IsTestFunction univ g) :
      cov[fun ω => hC ω f, fun ω => hC ω g; P] =
        wholePlaneGFFCov (.pairing f) (.pairing g) := by
    simpa only [GFFObservable.eval] using h.covariance_eq (.pairing f) (.pairing g) hf hg
  have hv : variance (Z - (a • X + b • Y)) P = 0 := by
    rw [variance_sub hZ (hA.add hB), variance_add hA hB,
      covariance_add_right hZ hA hB, variance_smul, variance_smul,
      covariance_smul_right, covariance_smul_right, covariance_smul_left,
      covariance_smul_right, ← covariance_self hZ.aemeasurable,
      ← covariance_self hX.aemeasurable, ← covariance_self hY.aemeasurable]
    rw [hcov θ θ hθ hθ]
    rw [hcov θ φ hθ hφ, hcov θ ψ hθ hψ, hcov φ φ hφ hφ,
      hcov φ ψ hφ hψ, hcov ψ ψ hψ hψ]
    dsimp [θ]
    rw [wholePlaneGFFCov_pairing_linear_left hφ hψ hθ a b,
      wholePlaneGFFCov_pairing_linear_right hφ hψ hφ a b,
      wholePlaneGFFCov_pairing_linear_right hφ hψ hψ a b,
      wholePlaneGFFCov_pairing_linear_left hφ hψ hφ a b,
      wholePlaneGFFCov_pairing_linear_left hφ hψ hψ a b]
    have hcomm : wholePlaneGFFCov (.pairing ψ) (.pairing φ) =
        wholePlaneGFFCov (.pairing φ) (.pairing ψ) := by
      rw [← hcov ψ φ hψ hφ, ← hcov φ ψ hφ hψ, covariance_comm]
    rw [hcomm]
    ring
  have he := ae_eq_integral_of_variance_eq_zero hErr hv
  filter_upwards [he] with ω he
  rw [hmean] at he
  change hC ω θ - (a * hC ω φ + b * hC ω ψ) = 0 at he
  exact sub_eq_zero.mp he


end PairingLinear

theorem tendsto_unitCircleDensity_mul_log {r : ℝ} (hr : 0 < r) {δ : ℕ → ℝ} (hδ : ∀ j, 0 < δ j)
    (hsmall : ∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ j, N ≤ j → δ j ≤ r * η) (z w : ℂ) :
    Tendsto (fun j => ∫ x, unitCircleDensity r (δ j) (hδ j) z x * Real.log ‖x - w‖) atTop
      (𝓝 (Real.log (max r ‖z - w‖))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set η : ℝ := min (r / 2) (ε * r / 8) with hηdef
  have hη : 0 < η := lt_min (by linarith) (by positivity)
  have hηr : η ≤ r / 2 := min_le_left _ _
  have hηε : η ≤ ε * r / 8 := min_le_right _ _
  obtain ⟨N, hN⟩ := hsmall η hη
  refine Filter.eventually_atTop.mpr ⟨N, fun j hj => ?_⟩
  have hb := abs_circleDensity_log_potential_sub_circle_le hr (hδ j)
    (lt_of_le_of_lt hηr (by linarith)) (hN j hj) z w
  have hl := log_add_sub_log_sub_le_four_mul hr hη hηr
  have h4 : 4 * η / r ≤ ε / 2 := by
    rw [div_le_iff₀ hr]
    nlinarith
  unfold unitCircleDensity
  rw [Real.dist_eq]
  exact lt_of_le_of_lt (hb.trans (hl.trans h4)) (by linarith)


theorem exists_dense_decode_polish (X : Type*) [TopologicalSpace X] [PolishSpace X] [LocallyCompactSpace X]
    [Nonempty X] :
    ∃ d : ℕ → X, DenseRange d ∧ ∃ decode : (ℕ → ℝ) → C(X, ℝ), Measurable decode ∧
      ∀ f : C(X, ℝ), decode (fun n => f (d n)) = f := by
  let d : ℕ → X := TopologicalSpace.denseSeq X
  have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq X
  let e : C(X, ℝ) → ℕ → ℝ := fun f n => f (d n)
  have he : Measurable e := measurable_pi_iff.mpr fun n => (continuous_eval_const (d n)).measurable
  have hinj : Function.Injective e := by
    intro f g h
    apply ContinuousMap.ext
    have hdense := hd.equalizer f.continuous g.continuous
    apply congrFun (hdense ?_)
    funext n
    exact congrFun h n
  have hemb : MeasurableEmbedding e := he.measurableEmbedding hinj
  obtain ⟨decode, hdecode, hdecode_eq⟩ :=
    hemb.exists_measurable_extend (g := id) measurable_id (fun _ => inferInstance)
  exact ⟨d, hd, decode, hdecode, fun f => congrFun hdecode_eq f⟩

namespace LocalDecoderCommon

/-! ### 1. The parameter domain of a disc -/

/-- The circles `closedBall x r ⊆ ball c R` (`r > 0`), as parameters `(r, x)`, written with the equivalent
condition `dist x c + r < R`: the domain of the local profile of the disc `ball c R`. -/
def LocalParam (c : ℂ) (R : ℝ) : Set (ℝ × ℂ) := {p | 0 < p.1 ∧ dist p.2 c + p.1 < R}

theorem mem_localParam_iff (c : ℂ) (R : ℝ) (p : ℝ × ℂ) :
    p ∈ LocalParam c R ↔ 0 < p.1 ∧ dist p.2 c + p.1 < R := Iff.rfl

theorem isOpen_localParam (c : ℂ) (R : ℝ) : IsOpen (LocalParam c R) := by
  have h : LocalParam c R = {p : ℝ × ℂ | 0 < p.1} ∩ {p : ℝ × ℂ | dist p.2 c + p.1 < R} := rfl
  rw [h]
  exact (isOpen_lt continuous_const continuous_fst).inter
    (isOpen_lt ((continuous_snd.dist continuous_const).add continuous_fst) continuous_const)

instance instPolishLocalParam (c : ℂ) (R : ℝ) : PolishSpace (LocalParam c R) :=
  (isOpen_localParam c R).polishSpace

instance instLocallyCompactLocalParam (c : ℂ) (R : ℝ) : LocallyCompactSpace (LocalParam c R) :=
  (isOpen_localParam c R).locallyCompactSpace

theorem localParam_nonempty (c : ℂ) {R : ℝ} (hR : 0 < R) : Nonempty (LocalParam c R) :=
  ⟨⟨(R / 2, c), (mem_localParam_iff c R _).2 ⟨half_pos hR, by show dist c c + R / 2 < R; rw [dist_self]; linarith⟩⟩⟩

/-- The radius of a parameter of the disc. -/
theorem localParam_radius_pos {c : ℂ} {R : ℝ} (p : LocalParam c R) : 0 < p.1.1 :=
  ((mem_localParam_iff c R p.1).1 p.2).1

/-- The distance condition of a parameter of the disc. -/
theorem localParam_dist_lt {c : ℂ} {R : ℝ} (p : LocalParam c R) : dist p.1.2 c + p.1.1 < R :=
  ((mem_localParam_iff c R p.1).1 p.2).2

/-! ### 2. Circle approximants inside the disc -/

/-- The fixed unit-mass bump `ρ` of the disc `ball c R`: the circle approximant of the circle of radius `R/2`
about `c` (its support lies in `ball c R`). -/
noncomputable def bumpRho (c : ℂ) {R : ℝ} (hR : 0 < R) : ℂ → ℝ :=
  circleApprox (half_pos hR) c 0

theorem eventually_approxEta_lt {r t : ℝ} (ht : 0 < t) :
    ∃ N : ℕ, ∀ j, N ≤ j → approxEta r j < t := by
  have h : Tendsto (fun j : ℕ => r / 4 * (1 / 2 : ℝ) ^ j) atTop (𝓝 (r / 4 * 0)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).const_mul (r / 4)
  rw [mul_zero] at h
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((tendsto_order.1 h).2 t ht)
  exact ⟨N, fun j hj => hN j hj⟩

/-- The support of the annular approximant of the circle `(r, x)` lies in the disc `ball c R` as soon as its
width `approxEta r j` is below the margin `R - (dist x c + r)`. -/
theorem tsupport_circleApprox_subset_ball {c x : ℂ} {R r : ℝ} (hr : 0 < r) {j : ℕ}
    (h : approxEta r j < R - (dist x c + r)) :
    tsupport (circleApprox hr x j) ⊆ ball c R := by
  intro y hy
  have hy' : y ∈ tsupport (unitCircleDensity r (r * approxEta r j) (mul_pos hr (approxEta_pos hr j)) x) := hy
  have hsub := tsupport_unitCircleDensity_subset hr (mul_pos hr (approxEta_pos hr j)) (le_refl _) x hy'
  have habs : |‖y - x‖ - r| ≤ approxEta r j := hsub
  have h1 : ‖y - x‖ ≤ r + approxEta r j := by linarith [le_abs_self (‖y - x‖ - r)]
  have htri : dist y c ≤ dist y x + dist x c := dist_triangle y x c
  have hyx : dist y x = ‖y - x‖ := dist_eq_norm y x
  rw [mem_ball]
  linarith

/-- For a circle of the disc, all large indices give approximants supported in the disc. -/
theorem exists_tsupport_circleApprox_subset {c x : ℂ} {R r : ℝ} (hr : 0 < r) (h : dist x c + r < R) :
    ∃ N : ℕ, ∀ j, N ≤ j → tsupport (circleApprox hr x j) ⊆ ball c R := by
  obtain ⟨N, hN⟩ := eventually_approxEta_lt (r := r) (sub_pos.2 h)
  exact ⟨N, fun j hj => tsupport_circleApprox_subset_ball hr (hN j hj)⟩

/-- The index shift `N_p` of the parameter `p`: the approximants of index `≥ N_p` are supported in the disc. -/
noncomputable def localShift (c : ℂ) {R : ℝ} (p : LocalParam c R) : ℕ :=
  Classical.choose (exists_tsupport_circleApprox_subset (localParam_radius_pos p) (localParam_dist_lt p))

theorem localShift_spec (c : ℂ) {R : ℝ} (p : LocalParam c R) (j : ℕ) (hj : localShift c p ≤ j) :
    tsupport (circleApprox (localParam_radius_pos p) p.1.2 j) ⊆ ball c R :=
  Classical.choose_spec (exists_tsupport_circleApprox_subset (localParam_radius_pos p) (localParam_dist_lt p)) j hj

theorem bumpRho_isTest (c : ℂ) {R : ℝ} (hR : 0 < R) :
    IsTestFunction (ball c R) (bumpRho c hR) := by
  have hsub : tsupport (bumpRho c hR) ⊆ ball c R := by
    apply tsupport_circleApprox_subset_ball (half_pos hR)
    unfold approxEta
    rw [dist_self, pow_zero]
    linarith
  exact ⟨(isTestFunction_circleApprox (half_pos hR) c 0).1,
    (isTestFunction_circleApprox (half_pos hR) c 0).2.1, hsub⟩

theorem integral_bumpRho (c : ℂ) {R : ℝ} (hR : 0 < R) : ∫ x, bumpRho c hR x = 1 :=
  integral_circleApprox (half_pos hR) c 0

/-- The mean-zero test `ψ_{j + N_p} - ρ` attached to the parameter `p`. -/
noncomputable def localTest (c : ℂ) {R : ℝ} (hR : 0 < R) (p : LocalParam c R) (j : ℕ) : ℂ → ℝ :=
  circleApprox (localParam_radius_pos p) p.1.2 (j + localShift c p) - bumpRho c hR

theorem localTest_isTest (c : ℂ) {R : ℝ} (hR : 0 < R) (p : LocalParam c R) (j : ℕ) :
    IsTestFunction (ball c R) (localTest c hR p j) ∧ ∫ x, localTest c hR p j x = 0 := by
  have hψ := isTestFunction_circleApprox (localParam_radius_pos p) p.1.2 (j + localShift c p)
  have hsub : tsupport (localTest c hR p j) ⊆ ball c R := by
    unfold localTest
    refine (tsupport_sub _ _).trans (Set.union_subset ?_ ?_)
    · exact localShift_spec c p (j + localShift c p) (Nat.le_add_left _ _)
    · exact (bumpRho_isTest c hR).2.2
  refine ⟨⟨hψ.1.sub (bumpRho_isTest c hR).1, hψ.2.1.sub (bumpRho_isTest c hR).2.1, hsub⟩, ?_⟩
  unfold localTest
  have hψi : Integrable (circleApprox (localParam_radius_pos p) p.1.2 (j + localShift c p)) :=
    hψ.1.continuous.integrable_of_hasCompactSupport hψ.2.1
  have hρi : Integrable (bumpRho c hR) :=
    (bumpRho_isTest c hR).1.continuous.integrable_of_hasCompactSupport (bumpRho_isTest c hR).2.1
  simp only [Pi.sub_apply]
  rw [integral_sub hψi hρi, integral_circleApprox, integral_bumpRho, sub_self]

open Classical in
/-- An observation `v` on the mean-zero tests of `D`, read on an arbitrary function `φ` (value `0` when `φ` is not
an admissible test). -/
noncomputable def obsAt {D : Set ℂ} (v : {φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0} → ℝ) (φ : ℂ → ℝ) : ℝ :=
  if h : IsTestFunction D φ ∧ ∫ x, φ x = 0 then v ⟨φ, h⟩ else 0

theorem measurable_obsAt {D : Set ℂ} (φ : ℂ → ℝ) :
    Measurable fun v : {φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0} → ℝ => obsAt v φ := by
  by_cases h : IsTestFunction D φ ∧ ∫ x, φ x = 0
  · have heq : (fun v : {φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0} → ℝ => obsAt v φ) =
        fun v => v ⟨φ, h⟩ := by
      funext v
      simp only [obsAt, h, and_self, ↓reduceDIte]
    rw [heq]
    exact measurable_pi_apply _
  · have heq : (fun v : {φ : ℂ → ℝ // IsTestFunction D φ ∧ ∫ x, φ x = 0} → ℝ => obsAt v φ) =
        fun _ => 0 := by
      funext v
      simp [obsAt, h]
    rw [heq]
    exact measurable_const

/-- The circle coordinate of the observation `v` at the parameter `p`: the limit of the mean-zero pairings
`v(ψ_j - ρ)` along the approximants. -/
noncomputable def localCoord (c : ℂ) {R : ℝ} (hR : 0 < R) (p : LocalParam c R)
    (v : {φ : ℂ → ℝ // IsTestFunction (ball c R) φ ∧ ∫ x, φ x = 0} → ℝ) : ℝ :=
  limUnder atTop (fun j => obsAt v (localTest c hR p j))

theorem measurable_localCoord (c : ℂ) {R : ℝ} (hR : 0 < R) (p : LocalParam c R) :
    Measurable fun v : {φ : ℂ → ℝ // IsTestFunction (ball c R) φ ∧ ∫ x, φ x = 0} → ℝ =>
      localCoord c hR p v := by
  have h : ∀ j, Measurable fun v : {φ : ℂ → ℝ // IsTestFunction (ball c R) φ ∧ ∫ x, φ x = 0} → ℝ =>
      obsAt v (localTest c hR p j) := fun j => measurable_obsAt _
  exact (StronglyMeasurable.limUnder fun j => (h j).stronglyMeasurable).measurable

/-! ### 3. Identification of the circle coordinates (almost surely) -/

/-- `φ · log‖·‖` is integrable for a test function `φ` whose support avoids the origin (the integrals in
`fieldPairing` are then genuine Lebesgue integrals). -/
theorem integrable_mul_log_norm {U : Set ℂ} {φ : ℂ → ℝ} (hφ : IsTestFunction U φ) (h0 : (0 : ℂ) ∉ U) :
    Integrable fun x => φ x * Real.log ‖x‖ := by
  have hsub : tsupport φ ⊆ U := hφ.2.2
  have h0' : (0 : ℂ) ∉ tsupport φ := fun h => h0 (hsub h)
  have hc : ContinuousOn (fun x => φ x * Real.log ‖x‖) (tsupport φ) := by
    refine (hφ.1.continuous.continuousOn).mul (ContinuousOn.log continuous_norm.continuousOn ?_)
    intro x hx
    exact norm_ne_zero_iff.2 (fun h => h0' (h ▸ hx))
  have hint : IntegrableOn (fun x => φ x * Real.log ‖x‖) (tsupport φ) :=
    hc.integrableOn_compact hφ.2.1
  have hsupp : Function.support (fun x => φ x * Real.log ‖x‖) ⊆ tsupport φ :=
    fun x hx => subset_tsupport φ (fun h => hx (by simp [h]))
  exact (integrableOn_iff_integrable_of_support_subset hsupp).1 hint

/-- The circle average of the logarithm of the modulus, in the form used by `fieldCircleAverage`. -/
theorem circleAverage_log_norm_eq_max {r : ℝ} (hr : 0 < r) (x : ℂ) :
    Real.circleAverage (fun y : ℂ => Real.log ‖y‖) x r = Real.log (max r ‖x‖) := by
  have h := circleAverage_log_norm_sub_eq x 0 hr
  simpa only [sub_zero] using h

/-- **Circle coordinates of the GFF, a.s.** For a whole-plane GFF `h^ℂ` with circle averages `hcirc`, the
coordinate of the observation `v = localMeanZeroObs α D (hC ω)` at a fixed parameter `p` equals the centred
circle average `h_r(x) - ⟨h, ρ⟩` almost surely (the centring constant is `fieldPairing α hC ρ`,
which the decoder cannot see). Linearity of the pairings on the countably many tests `ψ_j - ρ` is
`IsWholePlaneGFF.ae_pairing_linear_combination`; the limits are `ae_tendsto_circleApprox` (a.s.) and
`tendsto_unitCircleDensity_mul_log` (deterministic). -/
theorem ae_tendsto_localPairing {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (α : ℝ) (c : ℂ) {R : ℝ} (hR : 0 < R) (h0 : (0 : ℂ) ∉ ball c R) (p : LocalParam c R) :
    ∀ᵐ ω ∂P, Tendsto (fun j => obsAt (localMeanZeroObs α (ball c R) (hC ω)) (localTest c hR p j)) atTop
      (𝓝 (hcirc ω p.1.1 p.1.2 - α * Real.log (max p.1.1 ‖p.1.2‖) - fieldPairing α (hC ω) (bumpRho c hR))) := by
  have hr : 0 < p.1.1 := localParam_radius_pos p
  set N := localShift c p with hN_def
  set ψ : ℕ → ℂ → ℝ := fun j => circleApprox hr p.1.2 (j + N) with hψ_def
  have hρ : IsTestFunction univ (bumpRho c hR) :=
    ⟨(bumpRho_isTest c hR).1, (bumpRho_isTest c hR).2.1, subset_univ _⟩
  -- (a) the pairing of the test `ψ_j - ρ` is the difference of the pairings (a.s., all `j`)
  have hlin : ∀ᵐ ω ∂P, ∀ j, hC ω (localTest c hR p j) = hC ω (ψ j) - hC ω (bumpRho c hR) := by
    refine ae_all_iff.2 fun j => ?_
    have hψj : IsTestFunction univ (ψ j) :=
      isTestFunction_circleApprox hr p.1.2 (j + N)
    have h := ae_pairing_linear_combination hGFF hψj hρ 1 (-1)
    filter_upwards [h] with ω hω
    have hfun : (fun y => 1 * ψ j y + (-1) * bumpRho c hR y) = localTest c hR p j := by
      funext y
      simp only [localTest, hψ_def, one_mul, neg_mul, Pi.sub_apply]
      ring
    rw [hfun] at hω
    rw [hω]
    ring
  -- (b) the limit of the pairings of the approximants, a.s. and deterministically
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun j => hC ω (ψ j)) atTop (𝓝 (hcirc ω p.1.1 p.1.2)) := by
    have h := ae_tendsto_circleApprox hGFF hr p.1.2
    filter_upwards [h] with ω hω
    exact (tendsto_add_atTop_iff_nat N).2 hω
  have hlog : Tendsto (fun j => ∫ y, ψ j y * Real.log ‖y‖) atTop
      (𝓝 (Real.log (max p.1.1 ‖p.1.2‖))) := by
    have hδ : ∀ j : ℕ, 0 < p.1.1 * approxEta p.1.1 (j + N) := fun j => mul_pos hr (approxEta_pos hr _)
    have hsmall : ∀ η : ℝ, 0 < η → ∃ M : ℕ, ∀ j, M ≤ j →
        p.1.1 * approxEta p.1.1 (j + N) ≤ p.1.1 * η := by
      intro η hη
      obtain ⟨M, hM⟩ := eventually_approxEta_lt (r := p.1.1) hη
      exact ⟨M, fun j hj => mul_le_mul_of_nonneg_left (le_of_lt (hM (j + N) (by omega))) hr.le⟩
    have h := tendsto_unitCircleDensity_mul_log (r := p.1.1)
      (δ := fun j => p.1.1 * approxEta p.1.1 (j + N)) hr hδ hsmall p.1.2 0
    simp only [sub_zero] at h
    exact h
  -- (c) integrability of the logarithmic integrands (the approximants are tests in the disc)
  have hψD : ∀ j, IsTestFunction (ball c R) (ψ j) := fun j =>
    ⟨(isTestFunction_circleApprox hr p.1.2 (j + N)).1, (isTestFunction_circleApprox hr p.1.2 (j + N)).2.1,
      localShift_spec c p (j + N) (Nat.le_add_left _ _)⟩
  have hI : ∀ j, Integrable fun y => ψ j y * Real.log ‖y‖ := fun j =>
    integrable_mul_log_norm (hψD j) h0
  have hIρ : Integrable fun y => bumpRho c hR y * Real.log ‖y‖ :=
    integrable_mul_log_norm (bumpRho_isTest c hR) h0
  -- (d) the pairing splits as the difference, once the linearity holds at `j`
  have hsplit : ∀ ω, (∀ j, hC ω (localTest c hR p j) = hC ω (ψ j) - hC ω (bumpRho c hR)) →
      ∀ j, fieldPairing α (hC ω) (localTest c hR p j) =
        fieldPairing α (hC ω) (ψ j) - fieldPairing α (hC ω) (bumpRho c hR) := by
    intro ω hω j
    have hint : (∫ y, localTest c hR p j y * Real.log ‖y‖) =
        (∫ y, ψ j y * Real.log ‖y‖) - ∫ y, bumpRho c hR y * Real.log ‖y‖ := by
      rw [← integral_sub (hI j) hIρ]
      congr 1
      funext y
      simp only [localTest, Pi.sub_apply, hψ_def]
      ring
    unfold fieldPairing
    rw [hω j, hint]
    ring
  -- (e) the observation on the tests is the pairing, and the coordinate is the limit
  filter_upwards [hlin, hlim] with ω hωlin hωlim
  have hobs : ∀ j, obsAt (localMeanZeroObs α (ball c R) (hC ω)) (localTest c hR p j) =
      fieldPairing α (hC ω) (localTest c hR p j) := fun j => by
    have hadm := localTest_isTest c hR p j
    simp only [obsAt, hadm, and_self, ↓reduceDIte]
    rfl
  have h1 : Tendsto (fun j => fieldPairing α (hC ω) (ψ j)) atTop
      (𝓝 (hcirc ω p.1.1 p.1.2 - α * Real.log (max p.1.1 ‖p.1.2‖))) := by
    unfold fieldPairing
    exact hωlim.sub (hlog.const_mul α)
  have h2 : Tendsto (fun j => fieldPairing α (hC ω) (localTest c hR p j)) atTop
      (𝓝 (hcirc ω p.1.1 p.1.2 - α * Real.log (max p.1.1 ‖p.1.2‖) - fieldPairing α (hC ω) (bumpRho c hR))) := by
    have heq : (fun j => fieldPairing α (hC ω) (localTest c hR p j)) =
        fun j => fieldPairing α (hC ω) (ψ j) - fieldPairing α (hC ω) (bumpRho c hR) :=
      funext (hsplit ω hωlin)
    rw [heq]
    exact h1.sub_const _
  have heq' : (fun j => obsAt (localMeanZeroObs α (ball c R) (hC ω)) (localTest c hR p j)) =
      fun j => fieldPairing α (hC ω) (localTest c hR p j) := funext hobs
  rw [heq']
  exact h2

/-- **Circle coordinates of the GFF, a.s.** The coordinate of the mean-zero observation at `p` is the centred circle
average `h_r(x) - α log max(r,|x|) - (h, ρ)` almost surely (`ae_tendsto_localPairing` and `Tendsto.limUnder_eq`). -/
theorem ae_localCoord_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (α : ℝ) (c : ℂ) {R : ℝ} (hR : 0 < R) (h0 : (0 : ℂ) ∉ ball c R) (p : LocalParam c R) :
    ∀ᵐ ω ∂P, localCoord c hR p (localMeanZeroObs α (ball c R) (hC ω)) =
      hcirc ω p.1.1 p.1.2 - α * Real.log (max p.1.1 ‖p.1.2‖) - fieldPairing α (hC ω) (bumpRho c hR) := by
  filter_upwards [ae_tendsto_localPairing hGFF α c hR h0 p] with ω hω
  unfold localCoord
  exact hω.limUnder_eq

/-- For the local domain, a countable dense sequence `d` of `LocalParam c R` and a measurable
decoder `decode` with `decode (n ↦ f (d n)) = f` for every continuous `f` on `LocalParam c R`. -/
theorem exists_localDecoder (c : ℂ) {R : ℝ} (hR : 0 < R) :
    ∃ d : ℕ → LocalParam c R, ∃ decode : (ℕ → ℝ) → C(LocalParam c R, ℝ), Measurable decode ∧
      ∀ f : C(LocalParam c R, ℝ), decode (fun n => f (d n)) = f := by
  have := localParam_nonempty c hR
  obtain ⟨d, -, decode, hm, hdec⟩ := exists_dense_decode_polish (LocalParam c R)
  exact ⟨d, decode, hm, hdec⟩

/-- Almost surely the decoded local profile of the mean-zero observation is the continuous
function `p ↦ h^ℂ_{r}(x) - α log max(r,|x|) - (h, ρ)` on `LocalParam c R` (the centred circle profile). -/
theorem ae_decode_localCoord_eq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (α : ℝ) (c : ℂ) {R : ℝ} (hR : 0 < R) (h0 : (0 : ℂ) ∉ ball c R)
    (d : ℕ → LocalParam c R) (decode : (ℕ → ℝ) → C(LocalParam c R, ℝ))
    (hdec : ∀ f : C(LocalParam c R, ℝ), decode (fun n => f (d n)) = f) :
    ∀ᵐ ω ∂P, ∃ G : C(LocalParam c R, ℝ),
      (∀ p : LocalParam c R, G p = hcirc ω p.1.1 p.1.2 - α * Real.log (max p.1.1 ‖p.1.2‖) -
        fieldPairing α (hC ω) (bumpRho c hR)) ∧
      decode (fun n => localCoord c hR (d n) (localMeanZeroObs α (ball c R) (hC ω))) = G := by
  have hco : ∀ᵐ ω ∂P, ∀ n, localCoord c hR (d n) (localMeanZeroObs α (ball c R) (hC ω)) =
      hcirc ω (d n).1.1 (d n).1.2 - α * Real.log (max (d n).1.1 ‖(d n).1.2‖) -
        fieldPairing α (hC ω) (bumpRho c hR) :=
    ae_all_iff.2 fun n => ae_localCoord_eq hGFF α c hR h0 (d n)
  filter_upwards [hGFF.ae_continuousOn_circle, hco] with ω hω hωn
  have hpos : ∀ p : LocalParam c R, 0 < p.1.1 := fun p => localParam_radius_pos p
  have hmem : ∀ p : LocalParam c R, ((p.1.1, p.1.2) : ℝ × ℂ) ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℂ) :=
    fun p => ⟨hpos p, Set.mem_univ _⟩
  have hpair : Continuous fun p : LocalParam c R => ((p.1.1, p.1.2) : ℝ × ℂ) :=
    (continuous_fst.comp continuous_subtype_val).prodMk (continuous_snd.comp continuous_subtype_val)
  have hcirc_c : Continuous fun p : LocalParam c R => hcirc ω p.1.1 p.1.2 :=
    hω.comp_continuous hpair hmem
  have hlog : Continuous fun p : LocalParam c R => Real.log (max p.1.1 ‖p.1.2‖) :=
    Continuous.log ((continuous_fst.comp continuous_subtype_val).max
      (continuous_norm.comp (continuous_snd.comp continuous_subtype_val)))
      fun p => ne_of_gt (lt_of_lt_of_le (hpos p) (le_max_left _ _))
  have hgc : Continuous fun p : LocalParam c R => hcirc ω p.1.1 p.1.2 - α * Real.log (max p.1.1 ‖p.1.2‖) -
      fieldPairing α (hC ω) (bumpRho c hR) :=
    (hcirc_c.sub (continuous_const.mul hlog)).sub continuous_const
  refine ⟨⟨_, hgc⟩, fun p => rfl, ?_⟩
  have hfun : (fun n => localCoord c hR (d n) (localMeanZeroObs α (ball c R) (hC ω))) =
      fun n => (⟨_, hgc⟩ : C(LocalParam c R, ℝ)) (d n) :=
    funext fun n => hωn n
  rw [hfun, hdec]

end LocalDecoderCommon

end LatticeProb.LocalMeasureKernel
