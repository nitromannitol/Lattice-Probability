import Mathlib

/-!
# Local decoder: measure-theory core on a locally compact metric space

For a locally compact, second countable metric space `X` and a compact exhaustion `K`, this file gives the countable
test family `TestFamilyX K` (Urysohn cut-offs, uniform approximation of compactly supported continuous functions), the
limit functional `limFunctionalX`, the decoder `decoderX` (values on the test family), and their measurability lemmas.
The declarations carry the suffix `X`; no hypothesis is added. The module imports only Mathlib.
-/

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace LatticeProb.LocalMeasureKernel

section Vague

open scoped CompactlySupported

variable {X : Type*} [MetricSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]

/-- A countable family of compactly supported test functions adapted to a compact exhaustion `K` of `X`:
(i) each `K n` is covered by a member `D m` with `0 ≤ D m` and `1 ≤ D m` on `K n` (mass bound);
(ii) every `f` supported in `K n` is approximated uniformly, to any `δ > 0`, by some `D m` supported in `K n`. -/
structure TestFamilyX (K : ℕ → Set X) where
  D : ℕ → C_c(X, ℝ)
  mass : ∀ n : ℕ, ∃ m : ℕ, (∀ x : X, 0 ≤ D m x) ∧ ∀ x ∈ K n, 1 ≤ D m x
  approx : ∀ (n : ℕ) (f : C_c(X, ℝ)), tsupport ⇑f ⊆ K n → ∀ δ : ℝ, 0 < δ →
    ∃ m : ℕ, tsupport ⇑(D m) ⊆ K n ∧ ∀ x : X, |f x - D m x| ≤ δ

omit [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X] in
/-- Urysohn cut-off in a locally compact Hausdorff space: a nonnegative compactly supported continuous function
equal to `1` on a compact set `K`. -/
theorem exists_cc_one_on {K : Set X} (hK : IsCompact K) :
    ∃ g : C_c(X, ℝ), (∀ x, 0 ≤ g x) ∧ ∀ x ∈ K, 1 ≤ g x := by
  obtain ⟨K', hK'c, hKK', -⟩ := exists_compact_between hK isOpen_univ (subset_univ K)
  obtain ⟨f, hf0, hf1, hfI⟩ := exists_continuous_zero_one_of_isCompact' hK
    (isOpen_interior.isClosed_compl) (Set.disjoint_compl_right_iff_subset.2 hKK')
  have hsupp : HasCompactSupport f := by
    refine HasCompactSupport.intro hK'c fun x hx => hf0 ?_
    exact fun h => hx (interior_subset h)
  exact ⟨{ toContinuousMap := f, hasCompactSupport' := hsupp }, fun x => (hfI x).1,
    fun x hx => le_of_eq (hf1 hx).symm⟩

/-- Restriction of a compactly supported continuous function to a compact piece `K n` of the exhaustion. -/
def restrictK (K : ℕ → Set X) (n : ℕ) (g : C_c(X, ℝ)) : C(K n, ℝ) :=
  ⟨fun x => g x.1, g.continuous.comp continuous_subtype_val⟩

omit [MeasurableSpace X] [BorelSpace X] in
/-- The countable family exists: the countable dense subsets of the restrictions to the compact pieces, lifted
back to test functions supported in `K n`, together with a cut-off for each `n`. -/
theorem exists_testFamilyX (K : ℕ → Set X) (hKc : ∀ n, IsCompact (K n)) : Nonempty (TestFamilyX K) := by
  have hcpt : ∀ n, CompactSpace (K n) := fun n => isCompact_iff_compactSpace.mp (hKc n)
  classical
  let S : ℕ → Set C_c(X, ℝ) := fun n => {g | tsupport ⇑g ⊆ K n}
  have hsep : ∀ n : ℕ, TopologicalSpace.IsSeparable (restrictK K n '' S n) := by
    intro n
    exact TopologicalSpace.IsSeparable.of_separableSpace _
  have hex : ∀ n : ℕ, ∃ t ⊆ restrictK K n '' S n, t.Countable ∧ restrictK K n '' S n ⊆ closure t :=
    fun n => (hsep n).exists_countable_dense_subset
  choose t hts htc hdense using hex
  have hlift : ∀ n, ∀ τ ∈ t n, ∃ g ∈ S n, restrictK K n g = τ := fun n τ hτ => hts n hτ
  choose! lift hliftS hliftR using hlift
  choose cut hcut0 hcut1 using fun n => exists_cc_one_on (hKc n)
  let Dset : Set C_c(X, ℝ) := Set.range cut ∪ ⋃ n, lift n '' t n
  have hcount : Dset.Countable :=
    (countable_range _).union (countable_iUnion fun n => (htc n).image _)
  obtain ⟨D, hD⟩ := hcount.exists_eq_range ⟨cut 0, Or.inl ⟨0, rfl⟩⟩
  have hmemD : ∀ g ∈ Dset, ∃ m, D m = g := fun g hg => by
    rw [hD] at hg
    exact hg
  refine ⟨⟨D, ?_, ?_⟩⟩
  · intro n
    obtain ⟨m, hm⟩ := hmemD (cut n) (Or.inl ⟨n, rfl⟩)
    exact ⟨m, fun x => by rw [hm]; exact hcut0 n x, fun x hx => by rw [hm]; exact hcut1 n x hx⟩
  · intro n f hf δ hδ
    have hfS : f ∈ S n := hf
    obtain ⟨b, hb, hdist⟩ := Metric.mem_closure_iff.1 (hdense n ⟨f, hfS, rfl⟩) δ hδ
    have hdmem : lift n b ∈ Dset := Or.inr (mem_iUnion.2 ⟨n, mem_image_of_mem _ hb⟩)
    obtain ⟨m, hm⟩ := hmemD _ hdmem
    have hdS : tsupport ⇑(lift n b) ⊆ K n := hliftS n b hb
    refine ⟨m, ?_, fun x => ?_⟩
    · rw [hm]
      exact hdS
    · rw [hm]
      by_cases hx : x ∈ K n
      · have h3 : dist (f x) (lift n b x) ≤ dist (restrictK K n f) (restrictK K n (lift n b)) :=
          ContinuousMap.dist_apply_le_dist (f := restrictK K n f)
            (g := restrictK K n (lift n b)) (⟨x, hx⟩ : K n)
        rw [hliftR n b hb] at h3
        rw [Real.dist_eq] at h3
        exact h3.trans hdist.le
      · have hf0 : f x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hf h))
        have hd0 : lift n b x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hdS h))
        rw [hf0, hd0, sub_zero, abs_zero]
        exact hδ.le

theorem integrable_of_ccX (g : C_c(X, ℝ)) (μ : Measure X) [IsLocallyFiniteMeasure μ] :
    Integrable g μ :=
  g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport

/-- Vague convergence is tested on the countable family: if all the integrals of the members `D m` converge, so
do the integrals of every `f ∈ C_c(X, ℝ)` (ε-argument of `ProfileDecoderDerived.tendsto_of_testFamily`). -/
theorem tendsto_of_testFamilyX {K : ℕ → Set X} (hKs : ∀ s : Set X, IsCompact s → ∃ n, s ⊆ K n)
    (T : TestFamilyX K) {ν : ℕ → Measure X} (hν : ∀ k, IsLocallyFiniteMeasure (ν k))
    (hconv : ∀ m : ℕ, ∃ L, Tendsto (fun k => ∫ x, T.D m x ∂(ν k)) atTop (𝓝 L))
    (f : C_c(X, ℝ)) : ∃ L, Tendsto (fun k => ∫ x, f x ∂(ν k)) atTop (𝓝 L) := by
  obtain ⟨n, hsupp⟩ := hKs (tsupport ⇑f) f.hasCompactSupport.isCompact
  obtain ⟨m₀, hm₀nonneg, hm₀one⟩ := T.mass n
  obtain ⟨L₀, hL₀⟩ := hconv m₀
  have hK₀ : 0 < |L₀| + 1 := by positivity
  have hev : ∀ᶠ k in atTop, ∫ x, T.D m₀ x ∂(ν k) < |L₀| + 1 :=
    hL₀.eventually (gt_mem_nhds (by linarith [le_abs_self L₀]))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hev
  have hcauchy : CauchySeq (fun k => ∫ x, f x ∂(ν k)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    set δ : ℝ := ε / (4 * (|L₀| + 1)) with hδdef
    have hδ : 0 < δ := div_pos hε (by positivity)
    obtain ⟨m₁, hm₁supp, hm₁close⟩ := T.approx n f hsupp δ hδ
    obtain ⟨L₁, hL₁⟩ := hconv m₁
    obtain ⟨N₁, hN₁⟩ := Metric.cauchySeq_iff.1 hL₁.cauchySeq (ε / 2) (by positivity)
    have key : ∀ k, N₀ ≤ k → |∫ x, f x ∂(ν k) - ∫ x, T.D m₁ x ∂(ν k)| ≤ ε / 4 := by
      intro k hk
      have := hν k
      have hpt : ∀ x, ‖f x - T.D m₁ x‖ ≤ δ * T.D m₀ x := by
        intro x
        by_cases hx : x ∈ K n
        · have h1 : ‖f x - T.D m₁ x‖ ≤ δ := by
            rw [Real.norm_eq_abs]
            exact hm₁close x
          have h2 : 1 ≤ T.D m₀ x := hm₀one x hx
          calc ‖f x - T.D m₁ x‖ ≤ δ := h1
            _ = δ * 1 := (mul_one δ).symm
            _ ≤ δ * T.D m₀ x := mul_le_mul_of_nonneg_left h2 hδ.le
        · have hf0 : f x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp h))
          have hd0 : T.D m₁ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hm₁supp h))
          rw [hf0, hd0, sub_zero, norm_zero]
          exact mul_nonneg hδ.le (hm₀nonneg x)
      have hb : ‖∫ x, (f x - T.D m₁ x) ∂(ν k)‖ ≤ ∫ x, δ * T.D m₀ x ∂(ν k) :=
        norm_integral_le_of_norm_le ((integrable_of_ccX (T.D m₀) (ν k)).const_mul δ)
          (Eventually.of_forall hpt)
      rw [integral_const_mul, integral_sub (integrable_of_ccX f _) (integrable_of_ccX (T.D m₁) _),
        Real.norm_eq_abs] at hb
      have hc : ∫ x, T.D m₀ x ∂(ν k) ≤ |L₀| + 1 := (hN₀ k hk).le
      calc |∫ x, f x ∂(ν k) - ∫ x, T.D m₁ x ∂(ν k)| ≤ δ * ∫ x, T.D m₀ x ∂(ν k) := hb
        _ ≤ δ * (|L₀| + 1) := mul_le_mul_of_nonneg_left hc hδ.le
        _ = ε / 4 := by rw [hδdef]; field_simp
    refine ⟨max N₀ N₁, fun p hp q hq => ?_⟩
    have hp' : N₀ ≤ p := (le_max_left _ _).trans hp
    have hq' : N₀ ≤ q := (le_max_left _ _).trans hq
    have hb : |(∫ x, T.D m₁ x ∂(ν p)) - ∫ x, T.D m₁ x ∂(ν q)| < ε / 2 := by
      have := hN₁ p ((le_max_right _ _).trans hp) q ((le_max_right _ _).trans hq)
      rwa [Real.dist_eq] at this
    have kp := key p hp'
    have kq := key q hq'
    have h2 : |(∫ x, T.D m₁ x ∂(ν q)) - ∫ x, f x ∂(ν q)| ≤ ε / 4 := by
      rw [abs_sub_comm]
      exact kq
    have h3 := abs_add_three ((∫ x, f x ∂(ν p)) - ∫ x, T.D m₁ x ∂(ν p))
      ((∫ x, T.D m₁ x ∂(ν p)) - ∫ x, T.D m₁ x ∂(ν q)) ((∫ x, T.D m₁ x ∂(ν q)) - ∫ x, f x ∂(ν q))
    have h4 : |(∫ x, f x ∂(ν p)) - ∫ x, f x ∂(ν q)| =
        |((∫ x, f x ∂(ν p)) - ∫ x, T.D m₁ x ∂(ν p)) + ((∫ x, T.D m₁ x ∂(ν p)) - ∫ x, T.D m₁ x ∂(ν q))
          + ((∫ x, T.D m₁ x ∂(ν q)) - ∫ x, f x ∂(ν q))| := by
      congr 1
      ring
    rw [Real.dist_eq]
    linarith [h3, h4, kp, hb, h2]
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  exact ⟨L, hL⟩

/-- The limit of the integrals along a sequence of locally finite measures on which the integrals of all
`C_c(X, ℝ)` functions converge: a positive linear functional on `C_c(X, ℝ)` (the vague limit functional). -/
noncomputable def limFunctionalX {ν : ℕ → Measure X} (hν : ∀ k, IsLocallyFiniteMeasure (ν k))
    (hconv : ∀ g : C_c(X, ℝ), ∃ L, Tendsto (fun k => ∫ x, g x ∂(ν k)) atTop (𝓝 L)) :
    C_c(X, ℝ) →ₚ[ℝ] ℝ where
  toFun g := limUnder atTop (fun k => ∫ x, g x ∂(ν k))
  map_add' f g := by
    show limUnder atTop (fun k => ∫ x, (f + g) x ∂(ν k)) =
      limUnder atTop (fun k => ∫ x, f x ∂(ν k)) + limUnder atTop (fun k => ∫ x, g x ∂(ν k))
    refine tendsto_nhds_unique (tendsto_nhds_limUnder (hconv (f + g))) ?_
    refine Tendsto.congr (fun k => ?_)
      ((tendsto_nhds_limUnder (hconv f)).add (tendsto_nhds_limUnder (hconv g)))
    have := hν k
    simp only [CompactlySupportedContinuousMap.coe_add, Pi.add_apply]
    exact (integral_add (integrable_of_ccX f _) (integrable_of_ccX g _)).symm
  map_smul' c f := by
    show limUnder atTop (fun k => ∫ x, (c • f) x ∂(ν k)) =
      c • limUnder atTop (fun k => ∫ x, f x ∂(ν k))
    rw [smul_eq_mul]
    refine tendsto_nhds_unique (tendsto_nhds_limUnder (hconv (c • f))) ?_
    refine Tendsto.congr (fun k => ?_) ((tendsto_nhds_limUnder (hconv f)).const_mul c)
    have := hν k
    simp only [CompactlySupportedContinuousMap.smul_apply, smul_eq_mul]
    exact (integral_const_mul c _).symm
  monotone' := by
    intro f g hfg
    show limUnder atTop (fun k => ∫ x, f x ∂(ν k)) ≤ limUnder atTop (fun k => ∫ x, g x ∂(ν k))
    refine le_of_tendsto_of_tendsto' (tendsto_nhds_limUnder (hconv f))
      (tendsto_nhds_limUnder (hconv g)) (fun k => ?_)
    have := hν k
    exact integral_mono (integrable_of_ccX f _) (integrable_of_ccX g _) (fun x => hfg x)

/-- Open-set test functions on `X`: for an open `U`, continuous compactly supported `f n` with
`μ U = ⨆ n, ∫ f n dμ` for every locally finite `μ`. -/
theorem exists_open_mass_test_functionsX {U : Set X} (hU : IsOpen U) :
    ∃ f : ℕ → X → ℝ, (∀ n, Continuous (f n)) ∧ (∀ n, HasCompactSupport (f n)) ∧
      ∀ μ : Measure X, IsLocallyFiniteMeasure μ → μ U = ⨆ n, ENNReal.ofReal (∫ x, f n x ∂μ) := by
  classical
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let K : CompactExhaustion U := CompactExhaustion.choice U
  let C : ℕ → Set X := fun n => Subtype.val '' K n
  have hC (n : ℕ) : IsCompact (C n) := (K.isCompact n).image continuous_subtype_val
  have hCU (n : ℕ) : C n ⊆ U := by
    rintro x ⟨y, -, rfl⟩
    exact y.property
  have hmono : Monotone C := fun i j hij => image_mono (K.subset hij)
  have hcover : (⋃ n, C n) = U := by
    rw [← image_iUnion, K.iUnion_eq, image_univ]
    exact Subtype.range_coe
  have hcut (n : ℕ) : ∃ g : C(X, ℝ), EqOn g 1 (C n) ∧ EqOn g 0 Uᶜ ∧
      HasCompactSupport g ∧ ∀ x, g x ∈ Icc (0 : ℝ) 1 :=
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
    · exact Filter.Eventually.of_forall fun x => (hgRange n x).1
    · intro x hx
      simpa using le_of_eq (hgOne n hx).symm
  · apply iSup_le
    intro n
    apply integral_le_measure
    · intro x hx
      exact (hgRange n x).2
    · intro x hx
      exact le_of_eq (hgZero n hx)

/-- A family of locally finite measures on `X` is measurable once its values on open sets are measurable
(with the balls replaced by the interiors of a compact exhaustion of `X`). -/
theorem measurable_measure_of_isOpenX {Ω : Type*} [MeasurableSpace Ω] {ν : Ω → Measure X}
    (hloc : ∀ ω, IsLocallyFiniteMeasure (ν ω))
    (hopen : ∀ U : Set X, IsOpen U → Measurable (fun ω => ν ω U)) : Measurable ν := by
  let K : CompactExhaustion X := CompactExhaustion.choice X
  let B : ℕ → Set X := fun n => interior (K n)
  have hB (n : ℕ) : IsOpen (B n) := isOpen_interior
  have hmono : Monotone B := fun i j hij => interior_mono (K.subset hij)
  have hBU : (⋃ n, B n) = univ := by
    refine eq_univ_of_forall fun x => ?_
    have hx : x ∈ ⋃ n, K n := by rw [K.iUnion_eq]; exact mem_univ x
    obtain ⟨m, hm⟩ := mem_iUnion.1 hx
    exact mem_iUnion.2 ⟨m + 1, K.subset_interior_succ m hm⟩
  have hfinite (n : ℕ) (ω : Ω) : IsFiniteMeasure ((ν ω).restrict (B n)) := by
    let _ := hloc ω
    apply isFiniteMeasure_restrict.mpr
    apply ne_of_lt
    exact lt_of_le_of_lt (measure_mono interior_subset) (K.isCompact n).measure_lt_top
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
    · congr 1
      rw [← inter_iUnion, hBU, inter_univ]
    · intro i j hij
      exact inter_subset_inter_right S (hmono hij)
  simp_rw [heq]
  exact Measurable.iSup fun n => (Measure.measurable_coe hS).comp (hres n)

section Decoder

variable {Y : Type*} [MeasurableSpace Y]

/-- The parameters at which all test integrals `∫ T.D m dν_k(y)` converge. -/
def convSetX {K : ℕ → Set X} (T : TestFamilyX K) (ν : Y → ℕ → Measure X) : Set Y :=
  {y | ∀ m : ℕ, ∃ L, Tendsto (fun k => ∫ x, T.D m x ∂(ν y k)) atTop (𝓝 L)}

omit [LocallyCompactSpace X] [SecondCountableTopology X] [BorelSpace X] in
theorem measurableSet_convSetX {K : ℕ → Set X} (T : TestFamilyX K) {ν : Y → ℕ → Measure X}
    (hmeas : ∀ (g : C_c(X, ℝ)) (k : ℕ), Measurable fun y => ∫ x, g x ∂(ν y k)) :
    MeasurableSet (convSetX T ν) := by
  have h : convSetX T ν = ⋂ m : ℕ, {y | ∃ L, Tendsto (fun k => ∫ x, T.D m x ∂(ν y k)) atTop (𝓝 L)} := by
    ext y
    simp [convSetX]
  rw [h]
  exact MeasurableSet.iInter fun m => measurableSet_exists_tendsto fun k => hmeas (T.D m) k

open Classical in
/-- The decoded functional: the vague limit of the approximations on `convSetX`, `0` elsewhere. -/
noncomputable def decoderFunctionalX {K : ℕ → Set X} (hKs : ∀ s : Set X, IsCompact s → ∃ n, s ⊆ K n)
    (T : TestFamilyX K) (ν : Y → ℕ → Measure X) (hloc : ∀ y k, IsLocallyFiniteMeasure (ν y k)) (y : Y) :
    C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  if hy : y ∈ convSetX T ν then
    limFunctionalX (fun k => hloc y k)
      (fun g => tendsto_of_testFamilyX hKs T (fun k => hloc y k) hy g)
  else 0

/-- The decoded measure: the Riesz measure of the decoded functional (`RealRMK.rieszMeasure`). -/
noncomputable def decoderX {K : ℕ → Set X} (hKs : ∀ s : Set X, IsCompact s → ∃ n, s ⊆ K n)
    (T : TestFamilyX K) (ν : Y → ℕ → Measure X) (hloc : ∀ y k, IsLocallyFiniteMeasure (ν y k)) (y : Y) :
    Measure X :=
  RealRMK.rieszMeasure (decoderFunctionalX hKs T ν hloc y)

omit [MeasurableSpace Y] in
theorem integral_decoderX {K : ℕ → Set X} (hKs : ∀ s : Set X, IsCompact s → ∃ n, s ⊆ K n)
    (T : TestFamilyX K) (ν : Y → ℕ → Measure X) (hloc : ∀ y k, IsLocallyFiniteMeasure (ν y k))
    (y : Y) (g : C_c(X, ℝ)) :
    ∫ x, g x ∂(decoderX hKs T ν hloc y) = decoderFunctionalX hKs T ν hloc y g :=
  RealRMK.integral_rieszMeasure _ g

omit [MeasurableSpace Y] in
theorem decoderFunctionalX_of_mem {K : ℕ → Set X} (hKs : ∀ s : Set X, IsCompact s → ∃ n, s ⊆ K n)
    (T : TestFamilyX K) (ν : Y → ℕ → Measure X) (hloc : ∀ y k, IsLocallyFiniteMeasure (ν y k))
    {y : Y} (hy : y ∈ convSetX T ν) (g : C_c(X, ℝ)) :
    decoderFunctionalX hKs T ν hloc y g = limUnder atTop (fun k => ∫ x, g x ∂(ν y k)) := by
  unfold decoderFunctionalX
  split_ifs
  rfl

omit [MeasurableSpace Y] in
theorem decoderFunctionalX_of_not_mem {K : ℕ → Set X} (hKs : ∀ s : Set X, IsCompact s → ∃ n, s ⊆ K n)
    (T : TestFamilyX K) (ν : Y → ℕ → Measure X) (hloc : ∀ y k, IsLocallyFiniteMeasure (ν y k))
    {y : Y} (hy : y ∉ convSetX T ν) (g : C_c(X, ℝ)) :
    decoderFunctionalX hKs T ν hloc y g = 0 := by
  unfold decoderFunctionalX
  split_ifs
  simp

/-- Measurability of the decoded functional in the observation. -/
theorem measurable_decoderFunctionalX_apply {K : ℕ → Set X}
    (hKs : ∀ s : Set X, IsCompact s → ∃ n, s ⊆ K n)
    (T : TestFamilyX K) (ν : Y → ℕ → Measure X) (hloc : ∀ y k, IsLocallyFiniteMeasure (ν y k))
    (hmeas : ∀ (g : C_c(X, ℝ)) (k : ℕ), Measurable fun y => ∫ x, g x ∂(ν y k)) (g : C_c(X, ℝ)) :
    Measurable fun y => decoderFunctionalX hKs T ν hloc y g := by
  have hind : ∀ k, Measurable fun y => (convSetX T ν).indicator (fun y => ∫ x, g x ∂(ν y k)) y :=
    fun k => (hmeas g k).indicator (measurableSet_convSetX T hmeas)
  refine measurable_of_tendsto_metrizable hind ?_
  refine tendsto_pi_nhds.2 fun y => ?_
  by_cases hy : y ∈ convSetX T ν
  · simp only [Set.indicator_of_mem hy]
    rw [decoderFunctionalX_of_mem hKs T ν hloc hy g]
    obtain ⟨L, hL⟩ := tendsto_of_testFamilyX hKs T (fun k => hloc y k) hy g
    exact tendsto_nhds_limUnder ⟨L, hL⟩
  · simp only [Set.indicator_of_notMem hy]
    rw [decoderFunctionalX_of_not_mem hKs T ν hloc hy g]
    exact tendsto_const_nhds

/-- The decoder is measurable as a map into measures on `X`. -/
theorem measurable_decoderX {K : ℕ → Set X} (hKs : ∀ s : Set X, IsCompact s → ∃ n, s ⊆ K n)
    (T : TestFamilyX K) (ν : Y → ℕ → Measure X) (hloc : ∀ y k, IsLocallyFiniteMeasure (ν y k))
    (hmeas : ∀ (g : C_c(X, ℝ)) (k : ℕ), Measurable fun y => ∫ x, g x ∂(ν y k)) :
    Measurable (decoderX hKs T ν hloc) := by
  have hl : ∀ y, IsLocallyFiniteMeasure (decoderX hKs T ν hloc y) := fun y => by
    unfold decoderX
    infer_instance
  refine measurable_measure_of_isOpenX hl (fun U hU => ?_)
  obtain ⟨f, hfc, hfcc, hmass⟩ := exists_open_mass_test_functionsX hU
  have heq : (fun y => decoderX hKs T ν hloc y U) =
      fun y => ⨆ n, ENNReal.ofReal (decoderFunctionalX hKs T ν hloc y ⟨⟨f n, hfc n⟩, hfcc n⟩) := by
    funext y
    rw [hmass (decoderX hKs T ν hloc y) (hl y)]
    congr 1
    funext n
    congr 1
    exact integral_decoderX hKs T ν hloc y ⟨⟨f n, hfc n⟩, hfcc n⟩
  rw [heq]
  exact Measurable.iSup fun n => ENNReal.measurable_ofReal.comp
    (measurable_decoderFunctionalX_apply hKs T ν hloc hmeas _)

end Decoder

end Vague

end LatticeProb.LocalMeasureKernel
