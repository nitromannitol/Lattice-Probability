/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.VagueOpenExist at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaExistenceVague
import LatticeProb.Bonanno.QuantumZipper.LQG.Local
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.VagueUniqueOn

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Vague limits on an arbitrary open set from convergence of the test integrals (COORD-CHANGE, D98)

`VagueOpen.exists_isVagueLimitOn_of_tendsto_open`: the Riesz–Markov–Kakutani argument of
`VagueH.exists_isVagueLimitOn_of_tendsto` (mathlib `RealRMK.rieszMeasure` on the subtype `↥U`)
for an arbitrary open `U ⊆ ℂ` in place of `ℍ`. First step of the node `Prop16LitRepMeasStmt`: the
existence of a local vague limit is implied by countably many convergence statements.
Own bookkeeping (verbatim generalization).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped CompactlySupported ENNReal

namespace QuantumZipper
namespace VagueOpen

/-- A continuous compactly supported function is integrable when its support has finite mass. -/
theorem integrable_of_testFun {μ : Measure ℂ} {f : ℂ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hμ : μ (tsupport f) < ∞) : Integrable f μ := by
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hfc
  have hs : MeasurableSet (tsupport f) := (isClosed_tsupport f).measurableSet
  have hi : Integrable ((tsupport f).indicator (fun _ => C)) μ :=
    (integrable_indicator_iff hs).2 (integrableOn_const hμ.ne)
  refine hi.mono' hf.aestronglyMeasurable (ae_of_all _ fun z => ?_)
  by_cases hz : z ∈ tsupport f
  · rw [indicator_of_mem hz]; exact hC z
  · rw [indicator_of_notMem hz, image_eq_zero_of_notMem_tsupport hz, norm_zero]

/-- **Existence of the vague limit** from convergence against every test function. -/
theorem exists_isVagueLimitOn_of_tendsto_open {U : Set ℂ} (hUo : IsOpen U) {μs : ℕ → Measure ℂ}
    (hfin : ∀ K, IsCompact K → K ⊆ U → ∀ᶠ k in atTop, μs k K < ∞)
    (hconv : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U → ∃ l, Tendsto (fun k => ∫ z, f z ∂(μs k)) atTop (𝓝 l)) :
    ∃ μ, IsVagueLimitOn U μs μ := by
  classical
  have : LocallyCompactSpace U := hUo.locallyCompactSpace
  let E : C_c(U, ℝ) → ℂ → ℝ := fun g => Subtype.val.extend g 0
  have hE : ∀ g, Continuous (E g) ∧ HasCompactSupport (E g) ∧ tsupport (E g) ⊆ U := fun g =>
    ⟨HasCompactSupport.continuous_extend_zero hUo (map_continuous g) g.hasCompactSupport,
      g.hasCompactSupport.extend_zero continuous_subtype_val,
      (g.hasCompactSupport.tsupport_extend_zero_subset continuous_subtype_val).trans
        (Subtype.coe_image_subset _ _)⟩
  have hEval : ∀ g (z : U), E g z = g z := fun g z =>
    Subtype.val_injective.extend_apply _ _ _
  have hEout : ∀ g (z : ℂ), z ∉ U → E g z = 0 := fun g z hz => by
    simp only [E]
    rw [Function.extend_apply' _ _ _ (by rintro ⟨w, rfl⟩; exact hz w.2)]
    rfl
  have hEadd : ∀ g h, E (g + h) = fun z => E g z + E h z := by
    intro g h; funext z
    by_cases hz : z ∈ U
    · rw [hEval (g + h) ⟨z, hz⟩, hEval g ⟨z, hz⟩, hEval h ⟨z, hz⟩]; rfl
    · rw [hEout _ _ hz, hEout _ _ hz, hEout _ _ hz, add_zero]
  have hEsmul : ∀ (c : ℝ) g, E (c • g) = fun z => c * E g z := by
    intro c g; funext z
    by_cases hz : z ∈ U
    · rw [hEval (c • g) ⟨z, hz⟩, hEval g ⟨z, hz⟩]; rfl
    · rw [hEout _ _ hz, hEout _ _ hz, mul_zero]
  let Λ₀ : C_c(U, ℝ) → ℝ := fun g => limUnder atTop (fun k => ∫ z, E g z ∂(μs k))
  have hΛ : ∀ g, Tendsto (fun k => ∫ z, E g z ∂(μs k)) atTop (𝓝 (Λ₀ g)) := fun g =>
    tendsto_nhds_limUnder (hconv _ (hE g).1 (hE g).2.1 (hE g).2.2)
  have hint : ∀ f : ℂ → ℝ, Continuous f ∧ HasCompactSupport f ∧ tsupport f ⊆ U →
      ∀ᶠ k in atTop, Integrable f (μs k) := fun f hf =>
    (hfin _ hf.2.1 hf.2.2).mono fun k hk => integrable_of_testFun hf.1 hf.2.1 hk
  have hadd : ∀ g h, Λ₀ (g + h) = Λ₀ g + Λ₀ h := by
    intro g h
    refine tendsto_nhds_unique (hΛ (g + h)) ?_
    refine ((hΛ g).add (hΛ h)).congr' ?_
    filter_upwards [hint _ (hE g), hint _ (hE h)] with k h1 h2
    rw [hEadd, integral_add h1 h2]
  have hsmul : ∀ (c : ℝ) g, Λ₀ (c • g) = c • Λ₀ g := by
    intro c g
    refine tendsto_nhds_unique (hΛ (c • g)) ?_
    refine ((hΛ g).const_mul c).congr' (Eventually.of_forall fun k => ?_)
    rw [hEsmul]
    exact (integral_const_mul c _).symm
  have hpos : ∀ g, 0 ≤ g → 0 ≤ Λ₀ g := by
    intro g hg
    refine ge_of_tendsto' (hΛ g) fun k => integral_nonneg fun z => ?_
    by_cases hz : z ∈ U
    · rw [hEval g ⟨z, hz⟩]; exact hg ⟨z, hz⟩
    · rw [hEout g z hz]; exact le_rfl
  let Λ : C_c(U, ℝ) →ₚ[ℝ] ℝ :=
    PositiveLinearMap.mk₀ { toFun := Λ₀, map_add' := hadd, map_smul' := hsmul } hpos
  refine ⟨(RealRMK.rieszMeasure Λ).map Subtype.val, ?_, ?_, ?_⟩
  · rw [Measure.map_apply measurable_subtype_coe hUo.measurableSet.compl]
    have : (Subtype.val ⁻¹' Uᶜ : Set U) = ∅ := by
      ext z; simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_not]
      exact z.2
    rw [this, measure_empty]
  · intro K hK hKU
    rw [Measure.map_apply measurable_subtype_coe hK.measurableSet]
    have hK' : IsCompact (Subtype.val ⁻¹' K : Set U) := by
      rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.2 hKU]
      exact hK
    exact hK'.measure_lt_top
  · intro f hf hfc hfU
    have hg : HasCompactSupport (fun z : U => f z) := by
      refine HasCompactSupport.intro (K := (Subtype.val ⁻¹' tsupport f : Set U)) ?_ ?_
      · rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.2 hfU]
        exact hfc
      · intro z hz
        exact image_eq_zero_of_notMem_tsupport hz
    let g : C_c(U, ℝ) := ⟨⟨fun z => f z, hf.comp continuous_subtype_val⟩, hg⟩
    have hEg : E g = f := by
      funext z
      by_cases hz : z ∈ U
      · exact hEval g ⟨z, hz⟩
      · rw [hEout g z hz, image_eq_zero_of_notMem_tsupport (fun h => hz (hfU h))]
    have h1 : ∫ z, f z ∂((RealRMK.rieszMeasure Λ).map Subtype.val) = Λ g := by
      rw [integral_map measurable_subtype_coe.aemeasurable hf.aestronglyMeasurable]
      exact RealRMK.integral_rieszMeasure Λ g
    rw [h1]
    have := hΛ g
    rw [hEg] at this
    exact this

/-- **Convergence of a test integral from convergent approximants** (the Cauchy argument of
`VagueH.tendsto_of_denseTestFamily`, with the approximating family given abstractly). -/
theorem tendsto_of_approx {μs : ℕ → Measure ℂ} {K : Set ℂ} (hK : IsCompact K)
    (hfinK : ∀ᶠ k in atTop, μs k K < ∞) {f : ℂ → ℝ} (hf : Continuous f)
    (hfs : HasCompactSupport f) (hfK : tsupport f ⊆ K) {φ : ℂ → ℝ} (hφc : Continuous φ)
    (hφs : HasCompactSupport φ) (hφfin : ∀ᶠ k in atTop, μs k (tsupport φ) < ∞)
    (hφ0 : ∀ z, 0 ≤ φ z) (hφ1 : ∀ z ∈ K, 1 ≤ φ z)
    (hφconv : ∃ l, Tendsto (fun k => ∫ z, φ z ∂(μs k)) atTop (𝓝 l))
    (happrox : ∀ η > 0, ∃ g : ℂ → ℝ, Continuous g ∧ HasCompactSupport g ∧ tsupport g ⊆ K ∧
      (∀ z, |f z - g z| ≤ η) ∧ ∃ l, Tendsto (fun k => ∫ z, g z ∂(μs k)) atTop (𝓝 l)) :
    ∃ l, Tendsto (fun k => ∫ z, f z ∂(μs k)) atTop (𝓝 l) := by
  obtain ⟨lφ, hlφ⟩ := hφconv
  refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff.2 fun ε hε => ?_)
  set B := |lφ| + 1 with hB
  have hB0 : 0 < B := by positivity
  set η := ε / (4 * B) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨g, hgc, hgs, hgK, hfg, lg, hlg⟩ := happrox η hη0
  obtain ⟨N1, hN1⟩ := Metric.cauchySeq_iff.1 hlg.cauchySeq (ε / 2) (by positivity)
  have hev : ∀ᶠ k in atTop, |∫ z, f z ∂(μs k) - ∫ z, g z ∂(μs k)| ≤ ε / 4 := by
    have hbφ : ∀ᶠ k in atTop, ∫ z, φ z ∂(μs k) < B :=
      hlφ.eventually (gt_mem_nhds (by rw [hB]; linarith [le_abs_self lφ]))
    filter_upwards [hfinK, hφfin, hbφ] with k hkK hkφ hkb
    have hif : Integrable f (μs k) := integrable_of_testFun hf hfs ((measure_mono hfK).trans_lt hkK)
    have hig : Integrable g (μs k) := integrable_of_testFun hgc hgs ((measure_mono hgK).trans_lt hkK)
    have hiφ : Integrable φ (μs k) := integrable_of_testFun hφc hφs hkφ
    have hpt : ∀ z, |f z - g z| ≤ η * φ z := by
      intro z
      by_cases hz : z ∈ K
      · calc |f z - g z| ≤ η := hfg z
          _ = η * 1 := (mul_one η).symm
          _ ≤ η * φ z := mul_le_mul_of_nonneg_left (hφ1 z hz) hη0.le
      · rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hfK h)),
          image_eq_zero_of_notMem_tsupport (fun h => hz (hgK h)), sub_zero, abs_zero]
        exact mul_nonneg hη0.le (hφ0 z)
    calc |∫ z, f z ∂(μs k) - ∫ z, g z ∂(μs k)| = |∫ z, (f z - g z) ∂(μs k)| := by
          rw [integral_sub hif hig]
      _ ≤ ∫ z, |f z - g z| ∂(μs k) := abs_integral_le_integral_abs
      _ ≤ ∫ z, η * φ z ∂(μs k) :=
          integral_mono (hif.sub hig).abs (hiφ.const_mul η) hpt
      _ = η * ∫ z, φ z ∂(μs k) := integral_const_mul _ _
      _ ≤ η * B := mul_le_mul_of_nonneg_left hkb.le hη0.le
      _ = ε / 4 := by rw [hη]; field_simp
  obtain ⟨N2, hN2⟩ := eventually_atTop.1 hev
  refine ⟨max N1 N2, fun m hm n hn => ?_⟩
  have h1 := hN2 m (le_of_max_le_right hm)
  have h2 := hN2 n (le_of_max_le_right hn)
  have h3 := hN1 m (le_of_max_le_left hm) n (le_of_max_le_left hn)
  rw [Real.dist_eq] at h3 ⊢
  calc |∫ z, f z ∂(μs m) - ∫ z, f z ∂(μs n)|
      ≤ |∫ z, f z ∂(μs m) - ∫ z, g z ∂(μs m)| + |∫ z, g z ∂(μs m) - ∫ z, g z ∂(μs n)| +
        |∫ z, g z ∂(μs n) - ∫ z, f z ∂(μs n)| := by
        have := abs_sub_le (∫ z, f z ∂(μs m)) (∫ z, g z ∂(μs m)) (∫ z, f z ∂(μs n))
        have := abs_sub_le (∫ z, g z ∂(μs m)) (∫ z, g z ∂(μs n)) (∫ z, f z ∂(μs n))
        linarith
    _ < ε / 4 + ε / 2 + ε / 4 := by
        rw [abs_sub_comm (∫ z, g z ∂(μs n))]
        linarith
    _ = ε := by ring

/-- **Existence of a local vague limit from countably many convergent test integrals.** The
countable family is `χ n · g`, `g` in a dense test family on `ℍ` (`VagueH.IsDenseTestFamily`) and
`χ n` cutoffs of `U` (continuous, values in `[0,1]`, closed support in `U`, eventually `1` on each
compact subset of `U`). -/
theorem exists_isVagueLimitOn_of_cutoff {U : Set ℂ} (hUo : IsOpen U) (hUH : U ⊆ H)
    {χ : ℕ → ℂ → ℝ} (hχc : ∀ n, Continuous (χ n)) (hχ0 : ∀ n z, 0 ≤ χ n z)
    (hχ1' : ∀ n z, χ n z ≤ 1) (hχU : ∀ n, tsupport (χ n) ⊆ U)
    (hχ1 : ∀ K, IsCompact K → K ⊆ U → ∃ n, ∀ z ∈ K, χ n z = 1)
    {F : Set (ℂ → ℝ)} (hF : VagueH.IsDenseTestFamily F) {μs : ℕ → Measure ℂ}
    (hfin : ∀ K, IsCompact K → K ⊆ U → ∀ᶠ k in atTop, μs k K < ∞)
    (hconv : ∀ n, ∀ g ∈ F, ∃ l, Tendsto (fun k => ∫ z, χ n z * g z ∂(μs k)) atTop (𝓝 l)) :
    ∃ μ, IsVagueLimitOn U μs μ := by
  -- products with a cutoff are test functions in `U`
  have hprod : ∀ n, ∀ g ∈ F, Continuous (fun z => χ n z * g z) ∧
      HasCompactSupport (fun z => χ n z * g z) ∧
      tsupport (fun z => χ n z * g z) ⊆ tsupport g ∩ tsupport (χ n) := by
    intro n g hg
    obtain ⟨hgc, hgs, -⟩ := hF.1 g hg
    refine ⟨(hχc n).mul hgc, hgs.mul_left, ?_⟩
    exact subset_inter (tsupport_mul_subset_right) (tsupport_mul_subset_left)
  refine exists_isVagueLimitOn_of_tendsto_open hUo hfin fun f hf hfs hfU => ?_
  obtain ⟨K, hK, hKH, hfK, ⟨φ, hφF, hφ0, hφ1⟩, happ⟩ := hF.2 f ⟨hf, hfs, hfU.trans hUH⟩
  obtain ⟨n, hn⟩ := hχ1 (tsupport f) hfs hfU
  set K' := K ∩ tsupport (χ n) with hK'def
  have hK' : IsCompact K' := hK.inter_right (isClosed_tsupport _)
  have hK'U : K' ⊆ U := inter_subset_right.trans (hχU n)
  obtain ⟨n', hn'⟩ := hχ1 K' hK' hK'U
  have hφ := hF.1 φ hφF
  obtain ⟨hpφc, hpφs, hpφt⟩ := hprod n' φ hφF
  have hχf : ∀ z, χ n z * f z = f z := fun z => by
    by_cases hz : z ∈ tsupport f
    · rw [hn z hz, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]
  refine tendsto_of_approx hK' (hfin K' hK' hK'U) hf hfs ?_ hpφc hpφs ?_ ?_ ?_ (hconv n' φ hφF) ?_
  · exact subset_inter hfK (fun z hz => by
      have : χ n z = 1 := hn z hz
      exact subset_tsupport _ (by rw [Function.mem_support, this]; norm_num))
  · exact hfin _ hpφs (hpφt.trans (inter_subset_right.trans (hχU n')))
  · exact fun z => mul_nonneg (hχ0 n' z) (hφ0 z)
  · intro z hz
    rw [hn' z hz, one_mul]
    exact hφ1 z hz.1
  · intro η hη
    obtain ⟨g, hgF, hgK, hfg⟩ := happ η hη
    obtain ⟨hpc, hps, hpt⟩ := hprod n g hgF
    refine ⟨_, hpc, hps, hpt.trans (inter_subset_inter hgK subset_rfl), fun z => ?_,
      hconv n g hgF⟩
    rw [← hχf z, ← mul_sub, abs_mul, abs_of_nonneg (hχ0 n z)]
    calc χ n z * |f z - g z| ≤ 1 * |f z - g z| :=
          mul_le_mul_of_nonneg_right (hχ1' n z) (abs_nonneg _)
      _ ≤ η := by rw [one_mul]; exact hfg z

/-- **Measures on `U` are determined by the countable cutoff family.** Two measures carried by
`U` and finite on its compact subsets that agree on every `χ n · g` (`g ∈ F`) are equal. -/
theorem eq_of_integral_cutoff_eq {U : Set ℂ} (hUo : IsOpen U) (hUH : U ⊆ H)
    {χ : ℕ → ℂ → ℝ} (hχc : ∀ n, Continuous (χ n)) (hχ0 : ∀ n z, 0 ≤ χ n z)
    (hχ1' : ∀ n z, χ n z ≤ 1) (hχU : ∀ n, tsupport (χ n) ⊆ U)
    (hχ1 : ∀ K, IsCompact K → K ⊆ U → ∃ n, ∀ z ∈ K, χ n z = 1)
    {F : Set (ℂ → ℝ)} (hF : VagueH.IsDenseTestFamily F) {μ₁ μ₂ : Measure ℂ}
    (h₁ : μ₁ Uᶜ = 0) (h₂ : μ₂ Uᶜ = 0)
    (hK₁ : ∀ K, IsCompact K → K ⊆ U → μ₁ K < ∞) (hK₂ : ∀ K, IsCompact K → K ⊆ U → μ₂ K < ∞)
    (heq : ∀ n, ∀ g ∈ F, ∫ z, χ n z * g z ∂μ₁ = ∫ z, χ n z * g z ∂μ₂) : μ₁ = μ₂ := by
  set μs : ℕ → Measure ℂ := fun k => if Even k then μ₁ else μ₂ with hμs
  have hfin : ∀ K, IsCompact K → K ⊆ U → ∀ᶠ k in atTop, μs k K < ∞ := fun K hK hKU =>
    Eventually.of_forall fun k => by
      simp only [hμs]; split_ifs
      · exact hK₁ K hK hKU
      · exact hK₂ K hK hKU
  have hconst : ∀ n, ∀ g ∈ F, ∀ k, ∫ z, χ n z * g z ∂(μs k) = ∫ z, χ n z * g z ∂μ₁ := by
    intro n g hg k
    simp only [hμs]; split_ifs
    · rfl
    · exact (heq n g hg).symm
  obtain ⟨μ, hμ⟩ := exists_isVagueLimitOn_of_cutoff hUo hUH hχc hχ0 hχ1' hχU hχ1 hF hfin
    fun n g hg => ⟨_, tendsto_const_nhds.congr fun k => (hconst n g hg k).symm⟩
  have hall : ∀ f : ℂ → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ U →
      ∫ z, f z ∂μ₁ = ∫ z, f z ∂μ₂ := by
    intro f hf hfs hfU
    have ht := hμ.2.2 f hf hfs hfU
    have he : Tendsto (fun k : ℕ => ∫ z, f z ∂(μs (2 * k))) atTop (𝓝 (∫ z, f z ∂μ)) :=
      ht.comp (tendsto_id.const_mul_atTop' (by norm_num : 0 < 2))
    have ho : Tendsto (fun k : ℕ => ∫ z, f z ∂(μs (2 * k + 1))) atTop (𝓝 (∫ z, f z ∂μ)) :=
      ht.comp (tendsto_atTop_mono (f := fun k : ℕ => k) (fun k => by show k ≤ 2 * k + 1; omega)
        tendsto_id)
    have e1 : ∀ k : ℕ, μs (2 * k) = μ₁ := fun k => by simp [hμs]
    have e2 : ∀ k : ℕ, μs (2 * k + 1) = μ₂ := fun k => by simp [hμs]
    simp only [e1, e2] at he ho
    exact (tendsto_nhds_unique tendsto_const_nhds he).trans (tendsto_nhds_unique ho tendsto_const_nhds)
  have hv₁ : IsVagueLimitOn U (fun _ => μ₁) μ₁ := ⟨h₁, hK₁, fun f _ _ _ => tendsto_const_nhds⟩
  have hv₂ : IsVagueLimitOn U (fun _ => μ₁) μ₂ := ⟨h₂, hK₂, fun f hf hfs hfU =>
    tendsto_const_nhds.congr fun _ => hall f hf hfs hfU |>.symm⟩
  exact isVagueLimitOn_unique hUo hv₁ hv₂

end VagueOpen
end QuantumZipper
