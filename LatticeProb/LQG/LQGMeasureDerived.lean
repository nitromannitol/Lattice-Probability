import Mathlib
import LatticeProb.LQG.LQGMeasure
import LatticeProb.Gauss.GFF

/-!
# Measurability of the LQG measure as a function of its circle-average profile

Adapted from the Lean formalization accompanying [Harmonic balls in Liouville quantum gravity,
arXiv:2208.11795], Fact 2.1. The argument uses only the definitions of `LatticeProb.Gauss.GFF`
and `LatticeProb.LQG.LQGMeasure`. The statement `LQGMeasureOfProfileMeasurableLP` has the same
binders, quantifiers and conclusion as the profile-decoder measurability statement of the source.
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal CompactlySupported

universe u

namespace LatticeProb.LQG

open LatticeProb.Gauss

namespace ProfileDerived

/-- Measurability of the LQG measure of a whole-plane Gaussian free field as a function of its circle-average
profile: the measure is almost surely equal to `Dec` applied to the profile, for a measurable decoder `Dec`. -/
def LQGMeasureOfProfileMeasurableLP : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (γ α : ℝ)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (F : Ω → C(CircleParameter, ℝ)),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α hcirc μ → Measurable F →
    (∀ p : CircleParameter, (fun ω => F ω p) =ᵐ[P] fun ω => hcirc ω p.1 p.2) →
    ∃ Dec : C(CircleParameter, ℝ) → Measure ℂ, Measurable Dec ∧
      (∀ᵐ ω ∂P, μ ω = Dec (F ω)) ∧
      (∀ᵐ y ∂(P.map F), IsLQGLimit γ (fieldCircleAverage α (circleProfile y)) (Dec y))

/-! ### 1. A countable test family -/

/-- A countable family `D` of compactly supported continuous test functions. (i) Each ball `closedBall 0 n` is
covered by a mass-bounding member `D m`: `0 ≤ D m` and `1 ≤ D m` on the ball. (ii) Every `f` supported in
`closedBall 0 n` is approximated uniformly, to any `δ > 0`, by some `D m` supported in `closedBall 0 n`. -/
structure TestFamily where
  D : ℕ → C_c(ℂ, ℝ)
  mass : ∀ n : ℕ, ∃ m : ℕ, (∀ z : ℂ, 0 ≤ D m z) ∧ ∀ z ∈ closedBall (0 : ℂ) n, 1 ≤ D m z
  approx : ∀ (n : ℕ) (f : C_c(ℂ, ℝ)), tsupport ⇑f ⊆ closedBall (0 : ℂ) n → ∀ δ : ℝ, 0 < δ →
    ∃ m : ℕ, tsupport ⇑(D m) ⊆ closedBall (0 : ℂ) n ∧ ∀ z : ℂ, |f z - D m z| ≤ δ

/-- The explicit cutoff: `1` on `closedBall 0 n`, `0` outside `closedBall 0 (n + 1)`. -/
def cutoffFun (n : ℕ) (z : ℂ) : ℝ := max 0 (min 1 ((n : ℝ) + 1 - ‖z‖))

theorem continuous_cutoffFun (n : ℕ) : Continuous (cutoffFun n) := by
  unfold cutoffFun
  fun_prop

/-- The cutoff as a compactly supported continuous function. -/
def cutoffC (n : ℕ) : C_c(ℂ, ℝ) where
  toContinuousMap := ⟨cutoffFun n, continuous_cutoffFun n⟩
  hasCompactSupport' := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) ((n : ℝ) + 1)) fun z hz => ?_
    have hz' : (n : ℝ) + 1 < ‖z‖ := by simpa [mem_closedBall, dist_zero_right] using hz
    have h1 : (n : ℝ) + 1 - ‖z‖ ≤ 0 := by linarith
    show cutoffFun n z = 0
    unfold cutoffFun
    rw [min_eq_right (show (n : ℝ) + 1 - ‖z‖ ≤ 1 by linarith), max_eq_left h1]

theorem cutoffC_nonneg (n : ℕ) (z : ℂ) : 0 ≤ cutoffC n z := by
  show 0 ≤ cutoffFun n z
  unfold cutoffFun
  exact le_max_left _ _

theorem cutoffC_mass (n : ℕ) (z : ℂ) (hz : z ∈ closedBall (0 : ℂ) n) : 1 ≤ cutoffC n z := by
  have hz' : ‖z‖ ≤ (n : ℝ) := by simpa [mem_closedBall, dist_zero_right] using hz
  show 1 ≤ cutoffFun n z
  unfold cutoffFun
  rw [min_eq_left (show (1 : ℝ) ≤ (n : ℝ) + 1 - ‖z‖ by linarith)]
  exact le_max_of_le_right le_rfl

/-- Restriction of a compactly supported function to a closed ball, as a continuous function on the ball. -/
def restrictBall (n : ℕ) (g : C_c(ℂ, ℝ)) : C(closedBall (0 : ℂ) n, ℝ) :=
  ContinuousMap.restrict (closedBall (0 : ℂ) n) g.toContinuousMap

theorem exists_testFamily : Nonempty TestFamily := by
  classical
  let S : ℕ → Set C_c(ℂ, ℝ) := fun n => {g | tsupport ⇑g ⊆ closedBall (0 : ℂ) n}
  have hsep : ∀ n : ℕ, TopologicalSpace.IsSeparable (restrictBall n '' S n) := fun n =>
    TopologicalSpace.IsSeparable.of_separableSpace _
  have hex : ∀ n : ℕ, ∃ t ⊆ restrictBall n '' S n, t.Countable ∧ restrictBall n '' S n ⊆ closure t :=
    fun n => (hsep n).exists_countable_dense_subset
  choose t hts htc hdense using hex
  have hlift : ∀ n, ∀ τ ∈ t n, ∃ g ∈ S n, restrictBall n g = τ := fun n τ hτ => hts n hτ
  choose! lift hliftS hliftR using hlift
  let Dset : Set C_c(ℂ, ℝ) := Set.range cutoffC ∪ ⋃ n, lift n '' t n
  have hcount : Dset.Countable :=
    (countable_range _).union (countable_iUnion fun n => (htc n).image _)
  obtain ⟨D, hD⟩ := hcount.exists_eq_range ⟨cutoffC 0, Or.inl ⟨0, rfl⟩⟩
  have hmemD : ∀ g ∈ Dset, ∃ m, D m = g := fun g hg => by
    rw [hD] at hg
    exact hg
  refine ⟨⟨D, ?_, ?_⟩⟩
  · intro n
    obtain ⟨m, hm⟩ := hmemD (cutoffC n) (Or.inl ⟨n, rfl⟩)
    refine ⟨m, fun z => ?_, fun z hz => ?_⟩
    · rw [hm]
      exact cutoffC_nonneg n z
    · rw [hm]
      exact cutoffC_mass n z hz
  · intro n f hf δ hδ
    have hfS : f ∈ S n := hf
    obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.1 (hdense n ⟨f, hfS, rfl⟩) δ hδ
    have hdmem : lift n b ∈ Dset := Or.inr (mem_iUnion.2 ⟨n, mem_image_of_mem _ hb⟩)
    obtain ⟨m, hm⟩ := hmemD _ hdmem
    have hdS : tsupport ⇑(lift n b) ⊆ closedBall (0 : ℂ) n := hliftS n b hb
    refine ⟨m, ?_, fun z => ?_⟩
    · rw [hm]
      exact hdS
    · rw [hm]
      by_cases hz : z ∈ closedBall (0 : ℂ) n
      · have h3 : dist (f z) (lift n b z) ≤ dist (restrictBall n f) (restrictBall n (lift n b)) :=
          ContinuousMap.dist_apply_le_dist (f := restrictBall n f)
            (g := restrictBall n (lift n b)) (⟨z, hz⟩ : closedBall (0 : ℂ) n)
        rw [hliftR n b hb] at h3
        rw [Real.dist_eq] at h3
        exact h3.trans hdist.le
      · have hf0 : f z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hf h))
        have hd0 : lift n b z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hdS h))
        rw [hf0, hd0, sub_zero, abs_zero]
        exact hδ.le

/-! ### 2. Vague convergence is tested on the family -/

theorem integrable_of_cc (g : C_c(ℂ, ℝ)) (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] :
    Integrable g μ :=
  g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport

theorem tendsto_of_testFamily (T : TestFamily) {ν : ℕ → Measure ℂ}
    (hν : ∀ k, IsLocallyFiniteMeasure (ν k))
    (hconv : ∀ m : ℕ, ∃ L, Tendsto (fun k => ∫ z, T.D m z ∂(ν k)) atTop (𝓝 L))
    (f : C_c(ℂ, ℝ)) : ∃ L, Tendsto (fun k => ∫ z, f z ∂(ν k)) atTop (𝓝 L) := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1
    f.hasCompactSupport.isCompact.isBounded
  have hsupp : tsupport ⇑f ⊆ closedBall (0 : ℂ) ⌈r⌉₊ :=
    hr.trans (closedBall_subset_closedBall (Nat.le_ceil r))
  obtain ⟨m₀, hm₀nonneg, hm₀one⟩ := T.mass ⌈r⌉₊
  obtain ⟨L₀, hL₀⟩ := hconv m₀
  have hK₀ : 0 < |L₀| + 1 := by positivity
  have hev : ∀ᶠ k in atTop, ∫ z, T.D m₀ z ∂(ν k) < |L₀| + 1 :=
    hL₀.eventually (gt_mem_nhds (by linarith [le_abs_self L₀]))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
  have hcauchy : CauchySeq (fun k => ∫ z, f z ∂(ν k)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    set δ : ℝ := ε / (4 * (|L₀| + 1)) with hδdef
    have hδ : 0 < δ := div_pos hε (by positivity)
    obtain ⟨m₁, hm₁supp, hm₁close⟩ := T.approx ⌈r⌉₊ f hsupp δ hδ
    obtain ⟨L₁, hL₁⟩ := hconv m₁
    obtain ⟨N₁, hN₁⟩ := Metric.cauchySeq_iff.1 hL₁.cauchySeq (ε / 2) (by positivity)
    have key : ∀ k, N₀ ≤ k → |∫ z, f z ∂(ν k) - ∫ z, T.D m₁ z ∂(ν k)| ≤ ε / 4 := by
      intro k hk
      have := hν k
      have hpt : ∀ z, ‖f z - T.D m₁ z‖ ≤ δ * T.D m₀ z := by
        intro z
        by_cases hz : z ∈ closedBall (0 : ℂ) ⌈r⌉₊
        · have h1 : ‖f z - T.D m₁ z‖ ≤ δ := by
            rw [Real.norm_eq_abs]
            exact hm₁close z
          have h2 : 1 ≤ T.D m₀ z := hm₀one z hz
          calc ‖f z - T.D m₁ z‖ ≤ δ := h1
            _ = δ * 1 := (mul_one δ).symm
            _ ≤ δ * T.D m₀ z := mul_le_mul_of_nonneg_left h2 hδ.le
        · have hf0 : f z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hsupp h))
          have hd0 : T.D m₁ z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hm₁supp h))
          rw [hf0, hd0, sub_zero, norm_zero]
          exact mul_nonneg hδ.le (hm₀nonneg z)
      have hb : ‖∫ z, (f z - T.D m₁ z) ∂(ν k)‖ ≤ ∫ z, δ * T.D m₀ z ∂(ν k) :=
        norm_integral_le_of_norm_le ((integrable_of_cc (T.D m₀) (ν k)).const_mul δ)
          (Eventually.of_forall hpt)
      rw [integral_const_mul, integral_sub (integrable_of_cc f _) (integrable_of_cc (T.D m₁) _),
        Real.norm_eq_abs] at hb
      have hc : ∫ z, T.D m₀ z ∂(ν k) ≤ |L₀| + 1 := (hN₀ k hk).le
      calc |∫ z, f z ∂(ν k) - ∫ z, T.D m₁ z ∂(ν k)| ≤ δ * ∫ z, T.D m₀ z ∂(ν k) := hb
        _ ≤ δ * (|L₀| + 1) := mul_le_mul_of_nonneg_left hc hδ.le
        _ = ε / 4 := by rw [hδdef]; field_simp
    refine ⟨max N₀ N₁, fun p hp q hq => ?_⟩
    have hp' : N₀ ≤ p := (le_max_left _ _).trans hp
    have hq' : N₀ ≤ q := (le_max_left _ _).trans hq
    have hb : |(∫ z, T.D m₁ z ∂(ν p)) - ∫ z, T.D m₁ z ∂(ν q)| < ε / 2 := by
      have := hN₁ p ((le_max_right _ _).trans hp) q ((le_max_right _ _).trans hq)
      rwa [Real.dist_eq] at this
    have kp := key p hp'
    have kq := key q hq'
    have h2 : |(∫ z, T.D m₁ z ∂(ν q)) - ∫ z, f z ∂(ν q)| ≤ ε / 4 := by
      rw [abs_sub_comm]
      exact kq
    have h3 := abs_add_three ((∫ z, f z ∂(ν p)) - ∫ z, T.D m₁ z ∂(ν p))
      ((∫ z, T.D m₁ z ∂(ν p)) - ∫ z, T.D m₁ z ∂(ν q)) ((∫ z, T.D m₁ z ∂(ν q)) - ∫ z, f z ∂(ν q))
    have h4 : |(∫ z, f z ∂(ν p)) - ∫ z, f z ∂(ν q)| =
        |((∫ z, f z ∂(ν p)) - ∫ z, T.D m₁ z ∂(ν p)) + ((∫ z, T.D m₁ z ∂(ν p)) - ∫ z, T.D m₁ z ∂(ν q))
          + ((∫ z, T.D m₁ z ∂(ν q)) - ∫ z, f z ∂(ν q))| := by
      congr 1
      ring
    rw [Real.dist_eq]
    linarith [h3, h4, kp, hb, h2]
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  exact ⟨L, hL⟩

/-- The positive linear functional `g ↦ lim_k ∫ g dν_k` on `C_c(ℂ, ℝ)`. -/
theorem tendsto_limUnder_test (ν : ℕ → Measure ℂ) (hconv : ∀ g : C_c(ℂ, ℝ), ∃ L,
    Tendsto (fun k => ∫ z, g z ∂(ν k)) atTop (𝓝 L)) (g : C_c(ℂ, ℝ)) :
    Tendsto (fun k => ∫ z, g z ∂(ν k)) atTop
      (𝓝 (limUnder atTop (fun k => ∫ z, g z ∂(ν k)))) :=
  tendsto_nhds_limUnder (hconv g)

/-- The limit functional of a sequence of locally finite measures along which all test integrals converge. -/
def limFunctional (ν : ℕ → Measure ℂ) (hν : ∀ k, IsLocallyFiniteMeasure (ν k))
    (hconv : ∀ g : C_c(ℂ, ℝ), ∃ L, Tendsto (fun k => ∫ z, g z ∂(ν k)) atTop (𝓝 L)) :
    C_c(ℂ, ℝ) →ₚ[ℝ] ℝ where
  toFun g := limUnder atTop (fun k => ∫ z, g z ∂(ν k))
  map_add' f g := by
    show limUnder atTop (fun k => ∫ z, (f + g) z ∂(ν k)) =
      limUnder atTop (fun k => ∫ z, f z ∂(ν k)) + limUnder atTop (fun k => ∫ z, g z ∂(ν k))
    refine tendsto_nhds_unique (tendsto_limUnder_test ν hconv (f + g)) ?_
    refine Tendsto.congr (fun k => ?_)
      ((tendsto_limUnder_test ν hconv f).add (tendsto_limUnder_test ν hconv g))
    have := hν k
    simp only [CompactlySupportedContinuousMap.coe_add, Pi.add_apply]
    exact (integral_add (integrable_of_cc f _) (integrable_of_cc g _)).symm
  map_smul' c f := by
    show limUnder atTop (fun k => ∫ z, (c • f) z ∂(ν k)) =
      c • limUnder atTop (fun k => ∫ z, f z ∂(ν k))
    rw [smul_eq_mul]
    refine tendsto_nhds_unique (tendsto_limUnder_test ν hconv (c • f)) ?_
    refine Tendsto.congr (fun k => ?_) ((tendsto_limUnder_test ν hconv f).const_mul c)
    have := hν k
    simp only [CompactlySupportedContinuousMap.smul_apply, smul_eq_mul]
    exact (integral_const_mul c _).symm
  monotone' := by
    intro f g hfg
    show limUnder atTop (fun k => ∫ z, f z ∂(ν k)) ≤ limUnder atTop (fun k => ∫ z, g z ∂(ν k))
    refine le_of_tendsto_of_tendsto' (tendsto_limUnder_test ν hconv f)
      (tendsto_limUnder_test ν hconv g) (fun k => ?_)
    have := hν k
    exact integral_mono (integrable_of_cc f _) (integrable_of_cc g _) (fun z => hfg z)

instance : LocallyCompactSpace (Set.Ioi (0 : ℝ)) :=
  isOpen_Ioi.locallyCompactSpace

/-! ### Auxiliary lemmas -/

/-- The positive dyadic scale `2^{-k}`. -/
theorem dyadicScale_pos (k : ℕ) : 0 < dyadicScale k := pow_pos (by norm_num) k

theorem circleAverage_log_norm_eq {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    Real.circleAverage (fun x : ℂ => Real.log ‖x‖) z ε = Real.log ε + Real.posLog (ε⁻¹ * ‖z‖) := by
  simpa [sub_zero] using
    circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := 0) (c := z) (R := ε) hε.ne'

theorem continuous_circleAverage_log_norm {ε : ℝ} (hε : 0 < ε) :
    Continuous fun z : ℂ => Real.circleAverage (fun x : ℂ => Real.log ‖x‖) z ε := by
  have h : (fun z : ℂ => Real.circleAverage (fun x : ℂ => Real.log ‖x‖) z ε) =
      fun z => Real.log ε + Real.posLog (ε⁻¹ * ‖z‖) :=
    funext fun z => circleAverage_log_norm_eq hε z
  rw [h]
  exact continuous_const.add (Real.continuous_posLog.comp (continuous_const.mul continuous_norm))

theorem isLocallyFiniteMeasure_lqgApprox (γ : ℝ) {hε : ℝ → ℂ → ℝ} {ε : ℝ} (hc : Continuous (hε ε)) :
    IsLocallyFiniteMeasure (lqgApprox γ hε ε) := by
  unfold lqgApprox
  exact IsLocallyFiniteMeasure.withDensity_ofReal
    (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hc)))

/-- Uniqueness of the LQG limit. -/
theorem isLQGLimit_unique {γ : ℝ} {hε : ℝ → ℂ → ℝ} {m m' : Measure ℂ} (h : IsLQGLimit γ hε m)
    (h' : IsLQGLimit γ hε m') : m = m' := by
  have := h.isLocallyFiniteMeasure
  have := h'.isLocallyFiniteMeasure
  refine Measure.ext_of_integral_eq_on_compactlySupported fun f => ?_
  exact tendsto_nhds_unique (h.tendsto_integral f f.continuous f.hasCompactSupport)
    (h'.tendsto_integral f f.continuous f.hasCompactSupport)

/-! ### Auxiliary lemmas on open measures -/

theorem exists_open_mass_test_functions {U : Set ℂ} (hU : IsOpen U) :
    ∃ f : ℕ → ℂ → ℝ,
      (∀ n, Continuous (f n)) ∧ (∀ n, HasCompactSupport (f n)) ∧
      ∀ μ : Measure ℂ, IsLocallyFiniteMeasure μ →
        μ U = ⨆ n, ENNReal.ofReal (∫ z, f n z ∂μ) := by
  classical
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let K : CompactExhaustion U := CompactExhaustion.choice U
  let C : ℕ → Set ℂ := fun n => Subtype.val '' K n
  have hC (n : ℕ) : IsCompact (C n) := (K.isCompact n).image continuous_subtype_val
  have hCU (n : ℕ) : C n ⊆ U := by
    rintro z ⟨x, hx, rfl⟩
    exact x.property
  have hmono : Monotone C := fun i j hij => image_mono (K.subset hij)
  have hcover : (⋃ n, C n) = U := by
    rw [← image_iUnion, K.iUnion_eq, image_univ]
    exact Subtype.range_coe
  have hcut (n : ℕ) : ∃ g : C(ℂ, ℝ), EqOn g 1 (C n) ∧ EqOn g 0 Uᶜ ∧
      HasCompactSupport g ∧ ∀ z, g z ∈ Icc (0 : ℝ) 1 :=
    exists_continuous_one_zero_of_isCompact (hC n) hU.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr (hCU n))
  choose g hgOne hgZero hgComp hgRange using hcut
  refine ⟨fun n => g n, fun n => (g n).continuous, hgComp, ?_⟩
  intro μ hμ
  let _ := hμ
  apply le_antisymm
  · rw [← hcover, hmono.measure_iUnion]
    apply iSup_le
    intro n
    apply le_iSup_of_le n
    apply ((g n).continuous.integrable_of_hasCompactSupport (hgComp n)).measure_le_integral
    · exact Filter.Eventually.of_forall fun z => (hgRange n z).1
    · intro z hz
      simpa using le_of_eq (hgOne n hz).symm
  · apply iSup_le
    intro n
    apply integral_le_measure
    · intro z hz
      exact (hgRange n z).2
    · intro z hz
      exact le_of_eq (hgZero n hz)

theorem measurable_measure_of_isOpen {Ω : Type*} [MeasurableSpace Ω]
    {ν : Ω → Measure ℂ} (hloc : ∀ ω, IsLocallyFiniteMeasure (ν ω))
    (hopen : ∀ U : Set ℂ, IsOpen U → Measurable (fun ω => ν ω U)) : Measurable ν := by
  let B : ℕ → Set ℂ := fun n => Metric.ball 0 n
  have hB (n : ℕ) : IsOpen (B n) := Metric.isOpen_ball
  have hfinite (n : ℕ) (ω : Ω) : IsFiniteMeasure ((ν ω).restrict (B n)) := by
    let _ := hloc ω
    apply isFiniteMeasure_restrict.mpr
    apply ne_of_lt
    exact lt_of_le_of_lt (measure_mono Metric.ball_subset_closedBall)
      ((isCompact_closedBall 0 n).measure_lt_top)
  have hres (n : ℕ) : Measurable (fun ω => (ν ω).restrict (B n)) := by
    let _ : ∀ ω, IsFiniteMeasure ((ν ω).restrict (B n)) := hfinite n
    apply Measurable.measure_of_isPiSystem BorelSpace.measurable_eq isPiSystem_isOpen
    · intro U hU
      change IsOpen U at hU
      simpa only [Measure.restrict_apply hU.measurableSet] using hopen (U ∩ B n) (hU.inter (hB n))
    · simpa only [Measure.restrict_apply MeasurableSet.univ, univ_inter] using hopen (B n) (hB n)
  apply Measure.measurable_measure.mpr
  intro S hS
  have heq (ω : Ω) : ν ω S = ⨆ n, ((ν ω).restrict (B n)) S := by
    simp only [Measure.restrict_apply hS]
    rw [← Monotone.measure_iUnion]
    · change ν ω S = ν ω (⋃ n : ℕ, S ∩ Metric.ball 0 n)
      rw [← inter_iUnion, Metric.iUnion_ball_nat, inter_univ]
    · intro i j hij
      exact inter_subset_inter_right S (Metric.ball_subset_ball (by exact_mod_cast hij))
  simp_rw [heq]
  exact Measurable.iSup fun n => (Measure.measurable_coe hS).comp (hres n)

/-! ### Auxiliary lemmas on circle averages -/

theorem ae_circle_map_eq_raw
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hcirc : Ω → ℝ → ℂ → ℝ} {F : Ω → C(CircleParameter, ℝ)}
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun p : ℝ × ℂ => hcirc ω p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.univ))
    (hF : ∀ p : CircleParameter, (fun ω => F ω p) =ᵐ[P] fun ω => hcirc ω p.1 p.2) :
    ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω p.1 p.2 := by
  let : Nonempty CircleParameter := ⟨⟨⟨1, by simp⟩, 0⟩⟩
  let d : ℕ → CircleParameter := TopologicalSpace.denseSeq CircleParameter
  have hd : DenseRange d := TopologicalSpace.denseRange_denseSeq CircleParameter
  have he : ∀ᵐ ω ∂P, ∀ n, F ω (d n) = hcirc ω (d n).1 (d n).2 :=
    ae_all_iff.mpr fun n => hF (d n)
  filter_upwards [he, hcont] with ω hω hc
  have hraw : Continuous (fun p : CircleParameter => hcirc ω p.1 p.2) :=
    continuousOn_univ.mp (hc.comp
      (continuous_subtype_val.prodMap continuous_id).continuousOn
      (by intro p hp; exact ⟨p.1.2, Set.mem_univ _⟩))
  exact fun p => congrFun (hd.equalizer (F ω).continuous hraw (funext hω)) p

theorem ae_lqgApprox_circleProfile_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hcirc : Ω → ℝ → ℂ → ℝ} {F : Ω → C(CircleParameter, ℝ)}
    (h : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω p.1 p.2) :
    ∀ᵐ ω ∂P, ∀ γ α r, 0 < r →
      lqgApprox γ (fieldCircleAverage α (hcirc ω)) r =
        lqgApprox γ (fieldCircleAverage α (circleProfile (F ω))) r := by
  filter_upwards [h] with ω hω γ α r hr
  unfold lqgApprox
  congr 1
  funext z
  simp only [fieldCircleAverage, circleProfile, dite_eq_left hr, hω (⟨r, hr⟩, z)]

theorem isLQGMeasureOfField_circleProfile_iff
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hcirc : Ω → ℝ → ℂ → ℝ} {F : Ω → C(CircleParameter, ℝ)}
    (h : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω p.1 p.2)
    (γ α : ℝ) (μ : Ω → Measure ℂ) :
    IsLQGMeasureOfField P γ α hcirc μ ↔
      IsLQGMeasureOfField P γ α (fun ω => circleProfile (F ω)) μ := by
  have he := ae_lqgApprox_circleProfile_eq h
  constructor <;> intro hm
  all_goals
    filter_upwards [he, hm] with ω hω hlim
    refine ⟨hlim.isLocallyFiniteMeasure, ?_⟩
    intro f hf hfc
    have hs : (fun k : ℕ => lqgApprox γ (fieldCircleAverage α (hcirc ω)) (dyadicScale k)) =
        (fun k : ℕ => lqgApprox γ (fieldCircleAverage α (circleProfile (F ω))) (dyadicScale k)) :=
      funext fun k => hω γ α _ (dyadicScale_pos k)
    have hi := congrArg (fun g : ℕ → Measure ℂ => fun k => ∫ z, f z ∂(g k)) hs
    first | rw [← hi]; exact hlim.tendsto_integral f hf hfc
          | rw [hi]; exact hlim.tendsto_integral f hf hfc

/-! ### 3. The dyadic approximations depend measurably on the profile -/

theorem fca_circleProfile_eq (α : ℝ) (y : C(CircleParameter, ℝ)) {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    fieldCircleAverage α (circleProfile y) ε z =
      y (⟨ε, hε⟩, z) - α * Real.circleAverage (fun x : ℂ => Real.log ‖x‖) z ε := by
  simp only [fieldCircleAverage, circleProfile, hε, ↓reduceDIte]

theorem continuous_fca (α : ℝ) (y : C(CircleParameter, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    Continuous fun z : ℂ => fieldCircleAverage α (circleProfile y) ε z := by
  have h : (fun z : ℂ => fieldCircleAverage α (circleProfile y) ε z) =
      fun z => y (⟨ε, hε⟩, z) - α * Real.circleAverage (fun x : ℂ => Real.log ‖x‖) z ε :=
    funext fun z => fca_circleProfile_eq α y hε z
  rw [h]
  exact (y.continuous.comp (continuous_const.prodMk continuous_id)).sub
    ((continuous_circleAverage_log_norm hε).const_mul α)

/-- The dyadic approximation `ε^{γ²/2} e^{γ h_ε(z)} dz` of the profile `y`, at the scale `2^{-k}`. -/
def approxMeas (γ α : ℝ) (y : C(CircleParameter, ℝ)) (k : ℕ) : Measure ℂ :=
  lqgApprox γ (fieldCircleAverage α (circleProfile y)) (dyadicScale k)

theorem isLocallyFiniteMeasure_approxMeas (γ α : ℝ) (y : C(CircleParameter, ℝ)) (k : ℕ) :
    IsLocallyFiniteMeasure (approxMeas γ α y k) :=
  isLocallyFiniteMeasure_lqgApprox γ (continuous_fca α y (dyadicScale_pos k))

/-- The integrand `ε^{γ²/2} e^{γ h_ε(z)} f(z)` of the approximation at scale `ε`. -/
def approxIntegrand (γ α : ℝ) {ε : ℝ} (hε : 0 < ε) (f : ℂ → ℝ) (y : C(CircleParameter, ℝ)) (z : ℂ) : ℝ :=
  ε ^ (γ ^ 2 / 2) * Real.exp (γ * (y (⟨ε, hε⟩, z) - α * Real.circleAverage (fun x : ℂ => Real.log ‖x‖) z ε)) *
    f z

theorem continuous_approxIntegrand (γ α : ℝ) {ε : ℝ} (hε : 0 < ε) {f : ℂ → ℝ} (hf : Continuous f) :
    Continuous fun q : C(CircleParameter, ℝ) × ℂ => approxIntegrand γ α hε f q.1 q.2 := by
  have hE : Continuous fun q : C(CircleParameter, ℝ) × ℂ => q.1 (⟨ε, hε⟩, q.2) :=
    continuous_eval.comp (continuous_fst.prodMk (continuous_const.prodMk continuous_snd))
  have hA : Continuous fun q : C(CircleParameter, ℝ) × ℂ =>
      Real.circleAverage (fun x : ℂ => Real.log ‖x‖) q.2 ε :=
    (continuous_circleAverage_log_norm hε).comp continuous_snd
  have hρ : Continuous fun q : C(CircleParameter, ℝ) × ℂ =>
      ε ^ (γ ^ 2 / 2) * Real.exp (γ * (q.1 (⟨ε, hε⟩, q.2) -
        α * Real.circleAverage (fun x : ℂ => Real.log ‖x‖) q.2 ε)) :=
    continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul (hE.sub (continuous_const.mul hA))))
  exact hρ.mul (hf.comp continuous_snd)

theorem measurable_integral_approxMeas (γ α : ℝ) {f : ℂ → ℝ} (hf : Continuous f) (k : ℕ) :
    Measurable fun y : C(CircleParameter, ℝ) => ∫ z, f z ∂(approxMeas γ α y k) := by
  have hε : 0 < dyadicScale k := dyadicScale_pos k
  have key : ∀ y : C(CircleParameter, ℝ), ∫ z, f z ∂(approxMeas γ α y k) =
      ∫ z, approxIntegrand γ α hε f y z := by
    intro y
    have hρ : Continuous fun z : ℂ => dyadicScale k ^ (γ ^ 2 / 2) *
        Real.exp (γ * fieldCircleAverage α (circleProfile y) (dyadicScale k) z) :=
      continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul (continuous_fca α y hε)))
    unfold approxMeas lqgApprox
    rw [integral_withDensity_eq_integral_toReal_smul (f := fun z : ℂ => ENNReal.ofReal
      (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * fieldCircleAverage α (circleProfile y) (dyadicScale k) z)))
      hρ.measurable.ennreal_ofReal (Eventually.of_forall fun z => ENNReal.ofReal_lt_top)]
    congr 1
    funext z
    have hnn : 0 ≤ dyadicScale k ^ (γ ^ 2 / 2) *
        Real.exp (γ * fieldCircleAverage α (circleProfile y) (dyadicScale k) z) :=
      mul_nonneg (Real.rpow_nonneg hε.le _) (Real.exp_pos _).le
    rw [smul_eq_mul, ENNReal.toReal_ofReal hnn, approxIntegrand, fca_circleProfile_eq α y hε z]
  have hSM : StronglyMeasurable fun q : C(CircleParameter, ℝ) × ℂ => approxIntegrand γ α hε f q.1 q.2 :=
    (continuous_approxIntegrand γ α hε hf).stronglyMeasurable
  have hmeas : Measurable fun y : C(CircleParameter, ℝ) => ∫ z, approxIntegrand γ α hε f y z :=
    (hSM.integral_prod_right (ν := volume)).measurable
  simp only [key]
  exact hmeas

/-! ### 4. The convergence locus and the decoder -/

/-- The convergence locus: profiles whose dyadic approximations integrate every test function of the family to a
convergent sequence. -/
def convSet (T : TestFamily) (γ α : ℝ) : Set (C(CircleParameter, ℝ)) :=
  {y | ∀ m : ℕ, ∃ L, Tendsto (fun k => ∫ z, T.D m z ∂(approxMeas γ α y k)) atTop (𝓝 L)}

theorem measurableSet_convSet (T : TestFamily) (γ α : ℝ) : MeasurableSet (convSet T γ α) := by
  have h : convSet T γ α = ⋂ m : ℕ,
      {y | ∃ L, Tendsto (fun k => ∫ z, T.D m z ∂(approxMeas γ α y k)) atTop (𝓝 L)} := by
    ext y
    simp [convSet]
  rw [h]
  exact MeasurableSet.iInter fun m => measurableSet_exists_tendsto fun k =>
    measurable_integral_approxMeas γ α (T.D m).continuous k

theorem conv_of_mem (T : TestFamily) (γ α : ℝ) {y : C(CircleParameter, ℝ)} (hy : y ∈ convSet T γ α)
    (g : C_c(ℂ, ℝ)) : ∃ L, Tendsto (fun k => ∫ z, g z ∂(approxMeas γ α y k)) atTop (𝓝 L) :=
  tendsto_of_testFamily T (fun k => isLocallyFiniteMeasure_approxMeas γ α y k) hy g

open Classical in
/-- The limit functional of the profile `y`: the vague limit of the dyadic approximations on the convergence locus,
and `0` off it. -/
def decoderFunctional (T : TestFamily) (γ α : ℝ) (y : C(CircleParameter, ℝ)) : C_c(ℂ, ℝ) →ₚ[ℝ] ℝ :=
  if hy : y ∈ convSet T γ α then
    limFunctional (fun k => approxMeas γ α y k) (fun k => isLocallyFiniteMeasure_approxMeas γ α y k)
      (fun g => conv_of_mem T γ α hy g)
  else 0

theorem decoderFunctional_of_mem {T : TestFamily} {γ α : ℝ} {y : C(CircleParameter, ℝ)}
    (hy : y ∈ convSet T γ α) (g : C_c(ℂ, ℝ)) :
    decoderFunctional T γ α y g = limUnder atTop (fun k => ∫ z, g z ∂(approxMeas γ α y k)) := by
  simp only [decoderFunctional, hy, ↓reduceDIte]
  rfl

theorem decoderFunctional_of_not_mem {T : TestFamily} {γ α : ℝ} {y : C(CircleParameter, ℝ)}
    (hy : y ∉ convSet T γ α) (g : C_c(ℂ, ℝ)) : decoderFunctional T γ α y g = 0 := by
  simp only [decoderFunctional, hy, ↓reduceDIte]
  rfl

/-- The decoder: the Riesz measure of the limit functional. -/
def decoder (T : TestFamily) (γ α : ℝ) (y : C(CircleParameter, ℝ)) : Measure ℂ :=
  RealRMK.rieszMeasure (decoderFunctional T γ α y)

instance isLocallyFiniteMeasure_decoder (T : TestFamily) (γ α : ℝ) (y : C(CircleParameter, ℝ)) :
    IsLocallyFiniteMeasure (decoder T γ α y) := by
  unfold decoder
  infer_instance

theorem integral_decoder (T : TestFamily) (γ α : ℝ) (y : C(CircleParameter, ℝ)) (g : C_c(ℂ, ℝ)) :
    ∫ z, g z ∂(decoder T γ α y) = decoderFunctional T γ α y g :=
  RealRMK.integral_rieszMeasure _ g

theorem measurable_decoderFunctional_apply (T : TestFamily) (γ α : ℝ) (g : C_c(ℂ, ℝ)) :
    Measurable fun y => decoderFunctional T γ α y g := by
  have hind : ∀ k, Measurable fun y : C(CircleParameter, ℝ) =>
      (convSet T γ α).indicator (fun y => ∫ z, g z ∂(approxMeas γ α y k)) y := fun k =>
    (measurable_integral_approxMeas γ α g.continuous k).indicator (measurableSet_convSet T γ α)
  refine measurable_of_tendsto_metrizable hind ?_
  refine tendsto_pi_nhds.2 fun y => ?_
  by_cases hy : y ∈ convSet T γ α
  · simp only [Set.indicator_of_mem hy]
    rw [decoderFunctional_of_mem hy g]
    obtain ⟨L, hL⟩ := conv_of_mem T γ α hy g
    exact tendsto_nhds_limUnder ⟨L, hL⟩
  · simp only [Set.indicator_of_notMem hy]
    rw [decoderFunctional_of_not_mem hy g]
    exact tendsto_const_nhds

theorem measurable_decoder (T : TestFamily) (γ α : ℝ) : Measurable (decoder T γ α) := by
  refine measurable_measure_of_isOpen (fun y => inferInstance) (fun U hU => ?_)
  obtain ⟨f, hfc, hfcc, hmass⟩ := exists_open_mass_test_functions hU
  have heq : (fun y => decoder T γ α y U) =
      fun y => ⨆ n, ENNReal.ofReal (decoderFunctional T γ α y ⟨⟨f n, hfc n⟩, hfcc n⟩) := by
    funext y
    rw [hmass (decoder T γ α y) inferInstance]
    congr 1
    funext n
    congr 1
    exact integral_decoder T γ α y ⟨⟨f n, hfc n⟩, hfcc n⟩
  rw [heq]
  exact Measurable.iSup fun n =>
    ENNReal.measurable_ofReal.comp (measurable_decoderFunctional_apply T γ α _)

theorem isLQGLimit_decoder (T : TestFamily) (γ α : ℝ) {y : C(CircleParameter, ℝ)}
    (hy : y ∈ convSet T γ α) :
    IsLQGLimit γ (fieldCircleAverage α (circleProfile y)) (decoder T γ α y) := by
  refine ⟨inferInstance, fun f hf hfc => ?_⟩
  have h := integral_decoder T γ α y ⟨⟨f, hf⟩, hfc⟩
  rw [show (∫ z, f z ∂(decoder T γ α y)) = decoderFunctional T γ α y ⟨⟨f, hf⟩, hfc⟩ from h,
    decoderFunctional_of_mem hy]
  exact tendsto_nhds_limUnder (conv_of_mem T γ α hy ⟨⟨f, hf⟩, hfc⟩)

/-- Proof of `LQGMeasureOfProfileMeasurableLP`. -/
theorem lqgMeasureOfProfileMeasurable_lp : LQGMeasureOfProfileMeasurableLP.{u} := by
  intro Ω _ P _ γ α hC hcirc μ F hh hμ hFm hF
  obtain ⟨T⟩ := exists_testFamily
  have hagree : ∀ᵐ ω ∂P, ∀ p : CircleParameter, F ω p = hcirc ω p.1 p.2 :=
    ae_circle_map_eq_raw hh.ae_continuousOn_circle hF
  have h2 : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α (circleProfile (F ω))) (μ ω) :=
    (isLQGMeasureOfField_circleProfile_iff hagree γ α μ).1 hμ
  have hmem : ∀ᵐ ω ∂P, F ω ∈ convSet T γ α := by
    filter_upwards [h2] with ω hω
    intro m
    exact ⟨_, hω.tendsto_integral (T.D m) (T.D m).continuous (T.D m).hasCompactSupport⟩
  refine ⟨decoder T γ α, measurable_decoder T γ α, ?_, ?_⟩
  · filter_upwards [h2, hmem] with ω hω hωm
    exact isLQGLimit_unique hω (isLQGLimit_decoder T γ α hωm)
  · have hae : ∀ᵐ y ∂(P.map F), y ∈ convSet T γ α :=
      (ae_map_iff hFm.aemeasurable (measurableSet_convSet T γ α)).2 hmem
    filter_upwards [hae] with y hy
    exact isLQGLimit_decoder T γ α hy

end ProfileDerived

end LatticeProb.LQG

end
