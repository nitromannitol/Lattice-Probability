/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.AreaExistenceVague at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.LQG.Measures
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Metrizable.Basic

/-!
# M4-A1, part 2 (deterministic): vague limits on `ℍ` from a countable family

Blueprint node M4-R5(b), area version, used by M4-A1.

* `exists_isVagueLimitOn_of_tendsto`: if `μs k` is (eventually) finite on each compact subset
  of `ℍ` and `∫ f dμs k` converges for **every** test function `f` (continuous, compact support
  inside `ℍ`), then a vague limit exists (Riesz–Markov–Kakutani on the subtype `↥H`).
* `exists_denseTestFamily`: there is a countable family of test functions which is dense in the
  required sense (`IsDenseTestFamily`: uniform approximation with supports in a fixed compact
  `K ⊆ ℍ`, plus a bump `≥ 1` on `K`).
* `tendsto_of_denseTestFamily`: convergence on such a family implies convergence for all test
  functions.
* `exists_isVagueLimitOn_of_family`: the combination.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped CompactlySupported ENNReal

namespace QuantumZipper
namespace VagueH

/-- Test functions for vague convergence on `ℍ`. -/
def IsTestH (f : ℂ → ℝ) : Prop := Continuous f ∧ HasCompactSupport f ∧ tsupport f ⊆ H

theorem IsTestH.integrable {μ : Measure ℂ} {f : ℂ → ℝ} (hf : IsTestH f)
    (hμ : μ (tsupport f) < ∞) : Integrable f μ := by
  obtain ⟨C, hC⟩ := hf.1.bounded_above_of_compact_support hf.2.1
  have hs : MeasurableSet (tsupport f) := (isClosed_tsupport f).measurableSet
  have hi : Integrable ((tsupport f).indicator (fun _ => C)) μ :=
    (integrable_indicator_iff hs).2 (integrableOn_const hμ.ne)
  refine hi.mono' hf.1.aestronglyMeasurable (ae_of_all _ fun z => ?_)
  by_cases hz : z ∈ tsupport f
  · rw [indicator_of_mem hz]; exact hC z
  · rw [indicator_of_notMem hz, image_eq_zero_of_notMem_tsupport hz, norm_zero]

/-! ### Riesz–Markov–Kakutani on `↥H` -/

/-- **Existence of the vague limit** from convergence against every test function. -/
theorem exists_isVagueLimitOn_of_tendsto {μs : ℕ → Measure ℂ}
    (hfin : ∀ K, IsCompact K → K ⊆ H → ∀ᶠ k in atTop, μs k K < ∞)
    (hconv : ∀ f, IsTestH f → ∃ l, Tendsto (fun k => ∫ z, f z ∂(μs k)) atTop (𝓝 l)) :
    ∃ μ, IsVagueLimitOn H μs μ := by
  classical
  have : LocallyCompactSpace H := isOpen_H.locallyCompactSpace
  let E : C_c(H, ℝ) → ℂ → ℝ := fun g => Subtype.val.extend g 0
  have hE : ∀ g, IsTestH (E g) := fun g =>
    ⟨HasCompactSupport.continuous_extend_zero isOpen_H (map_continuous g) g.hasCompactSupport,
      g.hasCompactSupport.extend_zero continuous_subtype_val,
      (g.hasCompactSupport.tsupport_extend_zero_subset continuous_subtype_val).trans
        (Subtype.coe_image_subset _ _)⟩
  have hEval : ∀ g (z : H), E g z = g z := fun g z =>
    Subtype.val_injective.extend_apply _ _ _
  have hEout : ∀ g (z : ℂ), z ∉ H → E g z = 0 := fun g z hz => by
    simp only [E]
    rw [Function.extend_apply' _ _ _ (by rintro ⟨w, rfl⟩; exact hz w.2)]
    rfl
  have hEadd : ∀ g h, E (g + h) = fun z => E g z + E h z := by
    intro g h; funext z
    by_cases hz : z ∈ H
    · rw [hEval (g + h) ⟨z, hz⟩, hEval g ⟨z, hz⟩, hEval h ⟨z, hz⟩]; rfl
    · rw [hEout _ _ hz, hEout _ _ hz, hEout _ _ hz, add_zero]
  have hEsmul : ∀ (c : ℝ) g, E (c • g) = fun z => c * E g z := by
    intro c g; funext z
    by_cases hz : z ∈ H
    · rw [hEval (c • g) ⟨z, hz⟩, hEval g ⟨z, hz⟩]; rfl
    · rw [hEout _ _ hz, hEout _ _ hz, mul_zero]
  let Λ₀ : C_c(H, ℝ) → ℝ := fun g => limUnder atTop (fun k => ∫ z, E g z ∂(μs k))
  have hΛ : ∀ g, Tendsto (fun k => ∫ z, E g z ∂(μs k)) atTop (𝓝 (Λ₀ g)) := fun g =>
    tendsto_nhds_limUnder (hconv _ (hE g))
  have hint : ∀ f, IsTestH f → ∀ᶠ k in atTop, Integrable f (μs k) := fun f hf =>
    (hfin _ hf.2.1 hf.2.2).mono fun k hk => hf.integrable hk
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
    by_cases hz : z ∈ H
    · rw [hEval g ⟨z, hz⟩]; exact hg ⟨z, hz⟩
    · rw [hEout g z hz]; exact le_rfl
  let Λ : C_c(H, ℝ) →ₚ[ℝ] ℝ :=
    PositiveLinearMap.mk₀ { toFun := Λ₀, map_add' := hadd, map_smul' := hsmul } hpos
  refine ⟨(RealRMK.rieszMeasure Λ).map Subtype.val, ?_, ?_, ?_⟩
  · rw [Measure.map_apply measurable_subtype_coe isOpen_H.measurableSet.compl]
    have : (Subtype.val ⁻¹' Hᶜ : Set H) = ∅ := by
      ext z; simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_not]
      exact z.2
    rw [this, measure_empty]
  · intro K hK hKH
    rw [Measure.map_apply measurable_subtype_coe hK.measurableSet]
    have hK' : IsCompact (Subtype.val ⁻¹' K : Set H) := by
      rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.2 hKH]
      exact hK
    exact hK'.measure_lt_top
  · intro f hf hfc hfH
    have hg : HasCompactSupport (fun z : H => f z) := by
      refine HasCompactSupport.intro (K := (Subtype.val ⁻¹' tsupport f : Set H)) ?_ ?_
      · rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.2 hfH]
        exact hfc
      · intro z hz
        exact image_eq_zero_of_notMem_tsupport hz
    let g : C_c(H, ℝ) := ⟨⟨fun z => f z, hf.comp continuous_subtype_val⟩, hg⟩
    have hEg : E g = f := by
      funext z
      by_cases hz : z ∈ H
      · exact hEval g ⟨z, hz⟩
      · rw [hEout g z hz, image_eq_zero_of_notMem_tsupport (fun h => hz (hfH h))]
    have h1 : ∫ z, f z ∂((RealRMK.rieszMeasure Λ).map Subtype.val) = Λ g := by
      rw [integral_map measurable_subtype_coe.aemeasurable hf.aestronglyMeasurable]
      exact RealRMK.integral_rieszMeasure Λ g
    rw [h1]
    have := hΛ g
    rw [hEg] at this
    exact this

/-! ### Convergence from a dense countable family -/

/-- A family of test functions which is dense in the sense needed for vague convergence. -/
def IsDenseTestFamily (F : Set (ℂ → ℝ)) : Prop :=
  (∀ f ∈ F, IsTestH f) ∧ ∀ f, IsTestH f → ∃ K, IsCompact K ∧ K ⊆ H ∧ tsupport f ⊆ K ∧
    (∃ φ ∈ F, (∀ z, 0 ≤ φ z) ∧ ∀ z ∈ K, 1 ≤ φ z) ∧
    ∀ η > 0, ∃ g ∈ F, tsupport g ⊆ K ∧ ∀ z, |f z - g z| ≤ η

theorem tendsto_of_denseTestFamily {μs : ℕ → Measure ℂ}
    (hfin : ∀ K, IsCompact K → K ⊆ H → ∀ᶠ k in atTop, μs k K < ∞) {F : Set (ℂ → ℝ)}
    (hF : IsDenseTestFamily F)
    (hconv : ∀ f ∈ F, ∃ l, Tendsto (fun k => ∫ z, f z ∂(μs k)) atTop (𝓝 l))
    (f : ℂ → ℝ) (hf : IsTestH f) :
    ∃ l, Tendsto (fun k => ∫ z, f z ∂(μs k)) atTop (𝓝 l) := by
  obtain ⟨K, hK, hKH, hfK, ⟨φ, hφF, hφ0, hφ1⟩, happrox⟩ := hF.2 f hf
  have hφ := hF.1 φ hφF
  obtain ⟨lφ, hlφ⟩ := hconv φ hφF
  refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff.2 fun ε hε => ?_)
  set B := |lφ| + 1 with hB
  have hB0 : 0 < B := by positivity
  set η := ε / (4 * B) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨g, hgF, hgK, hfg⟩ := happrox η hη0
  have hg := hF.1 g hgF
  obtain ⟨lg, hlg⟩ := hconv g hgF
  obtain ⟨N1, hN1⟩ := Metric.cauchySeq_iff.1 hlg.cauchySeq (ε / 2) (by positivity)
  have hev : ∀ᶠ k in atTop, |∫ z, f z ∂(μs k) - ∫ z, g z ∂(μs k)| ≤ ε / 4 := by
    have hbφ : ∀ᶠ k in atTop, ∫ z, φ z ∂(μs k) < B :=
      hlφ.eventually (gt_mem_nhds (by rw [hB]; linarith [le_abs_self lφ]))
    filter_upwards [hfin K hK hKH, hfin _ hφ.2.1 hφ.2.2, hbφ] with k hkK hkφ hkb
    have hif : Integrable f (μs k) := hf.integrable ((measure_mono hfK).trans_lt hkK)
    have hig : Integrable g (μs k) := hg.integrable ((measure_mono hgK).trans_lt hkK)
    have hiφ : Integrable φ (μs k) := hφ.integrable hkφ
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

/-! ### Construction of a countable dense family -/

/-- The exhausting compacts `K_n = {‖z‖ ≤ n, Im z ≥ 1/(n+1)}` of `ℍ`. -/
def Kset (n : ℕ) : Set ℂ := {z | ‖z‖ ≤ n ∧ 1 / ((n : ℝ) + 1) ≤ z.im}

theorem isCompact_Kset (n : ℕ) : IsCompact (Kset n) := by
  refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
  · exact (isClosed_le continuous_norm continuous_const).inter
      (isClosed_le continuous_const Complex.continuous_im)
  · exact (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := n)).subset fun z hz => by
      simpa using hz.1

theorem Kset_subset_H (n : ℕ) : Kset n ⊆ H := fun z hz =>
  show 0 < z.im from lt_of_lt_of_le (by positivity) hz.2

theorem exists_Kset {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) : ∃ n, K ⊆ Kset n := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).1 hK.isBounded
  obtain ⟨d, hd, hdK⟩ : ∃ d : ℝ, 0 < d ∧ ∀ z ∈ K, d ≤ z.im := by
    rcases K.eq_empty_or_nonempty with hK0 | hne
    · exact ⟨1, one_pos, by simp [hK0]⟩
    · obtain ⟨z₀, hz₀, hmin⟩ := hK.exists_isMinOn hne Complex.continuous_im.continuousOn
      exact ⟨z₀.im, hKH hz₀, fun z hz => isMinOn_iff.mp hmin z hz⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (max r (1 / d))
  refine ⟨n, fun z hz => ⟨?_, ?_⟩⟩
  · have := hr hz
    rw [Metric.mem_closedBall, dist_zero_right] at this
    linarith [le_max_left r (1 / d)]
  · have h1 : 1 / d < (n : ℝ) + 1 := by linarith [le_max_right r (1 / d)]
    have : 1 / ((n : ℝ) + 1) < d := by
      rw [div_lt_iff₀ (by positivity)]
      rw [div_lt_iff₀ hd] at h1
      linarith
    linarith [hdK z hz]

/-- A bump `φ_n` with `0 ≤ φ_n ≤ 1`, `φ_n = 1` on `K_n`, compactly supported in `ℍ`. -/
theorem exists_bump_Kset (n : ℕ) :
    ∃ φ : ℂ → ℝ, IsTestH φ ∧ (∀ z, 0 ≤ φ z) ∧ ∀ z ∈ Kset n, 1 ≤ φ z := by
  set c : ℝ := 1 / (2 * ((n : ℝ) + 1)) with hc
  have hc0 : 0 < c := by positivity
  have hcK : c < 1 / ((n : ℝ) + 1) := by
    rw [hc]; apply one_div_lt_one_div_of_lt (by positivity); linarith [(n.cast_nonneg : (0:ℝ) ≤ n)]
  obtain ⟨φ, hφ1, hφ0, hφc, hφr⟩ := exists_continuous_one_zero_of_isCompact (X := ℂ)
    (isCompact_Kset n) (isClosed_le Complex.continuous_im continuous_const)
    (t := {z : ℂ | z.im ≤ c})
    (by
      rw [Set.disjoint_left]
      intro z hz hzt
      have := hz.2
      simp only [Set.mem_ofPred_eq] at hzt
      linarith)
  refine ⟨φ, ⟨φ.continuous, hφc, ?_⟩, fun z => (hφr z).1, fun z hz => by rw [hφ1 hz]; rfl⟩
  have hsub : Function.support φ ⊆ {z : ℂ | c ≤ z.im} := by
    intro z hz
    by_contra h
    simp only [Set.mem_ofPred_eq, not_le] at h
    exact hz (hφ0 (show z.im ≤ c from h.le))
  refine (closure_minimal hsub (isClosed_le continuous_const Complex.continuous_im)).trans ?_
  intro z hz
  show 0 < z.im
  exact lt_of_lt_of_le hc0 hz

/-- For each `n`, a countable family of test functions supported in `K_n`, uniformly dense
among the test functions supported in `K_n`. -/
theorem exists_dense_Kset (n : ℕ) :
    ∃ D : Set (ℂ → ℝ), D.Countable ∧ (∀ g ∈ D, IsTestH g ∧ tsupport g ⊆ Kset n) ∧
      ∀ f, IsTestH f → tsupport f ⊆ Kset n → ∀ η > 0, ∃ g ∈ D, ∀ z, |f z - g z| ≤ η := by
  classical
  have : CompactSpace (Kset n) := isCompact_iff_compactSpace.mp (isCompact_Kset n)
  let T : Set C(Kset n, ℝ) :=
    {F | ∃ f : ℂ → ℝ, (IsTestH f ∧ tsupport f ⊆ Kset n) ∧ ∀ x : Kset n, F x = f x}
  obtain ⟨c, hcT, hcc, hTc⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace T).exists_countable_dense_subset
  let w : C(Kset n, ℝ) → (ℂ → ℝ) := fun F => if h : F ∈ T then h.choose else 0
  have hw : ∀ F ∈ T, (IsTestH (w F) ∧ tsupport (w F) ⊆ Kset n) ∧ ∀ x : Kset n, F x = w F x := by
    intro F hF
    simp only [w, hF, ↓reduceDIte]
    exact hF.choose_spec
  refine ⟨w '' c, hcc.image w, ?_, ?_⟩
  · rintro g ⟨F, hF, rfl⟩
    exact (hw F (hcT hF)).1
  · intro f hf hfK η hη
    let F : C(Kset n, ℝ) := ⟨fun x => f x, hf.1.comp continuous_subtype_val⟩
    have hFT : F ∈ T := ⟨f, ⟨hf, hfK⟩, fun x => rfl⟩
    obtain ⟨G, hGc, hFG⟩ := Metric.mem_closure_iff.1 (hTc hFT) η hη
    obtain ⟨⟨hgt, hgK⟩, hGw⟩ := hw G (hcT hGc)
    refine ⟨w G, ⟨G, hGc, rfl⟩, fun z => ?_⟩
    by_cases hz : z ∈ Kset n
    · have h1 := ContinuousMap.dist_apply_le_dist (f := F) (g := G) ⟨z, hz⟩
      rw [Real.dist_eq] at h1
      have e1 : F ⟨z, hz⟩ = f z := rfl
      rw [e1, hGw ⟨z, hz⟩] at h1
      exact h1.trans hFG.le
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hfK h)),
        image_eq_zero_of_notMem_tsupport (fun h => hz (hgK h)), sub_zero, abs_zero]
      exact hη.le

/-- **A countable dense test family exists.** -/
theorem exists_denseTestFamily : ∃ F : Set (ℂ → ℝ), F.Countable ∧ IsDenseTestFamily F := by
  choose D hDc hDt hDa using exists_dense_Kset
  choose φ hφt hφ0 hφ1 using exists_bump_Kset
  refine ⟨⋃ n, (D n ∪ {φ n}), countable_iUnion fun n => (hDc n).union (countable_singleton _),
    ?_, ?_⟩
  · intro f hf
    obtain ⟨n, hn⟩ := mem_iUnion.1 hf
    rcases hn with hn | hn
    · exact (hDt n f hn).1
    · rw [mem_singleton_iff.1 hn]; exact hφt n
  · intro f hf
    obtain ⟨n, hn⟩ := exists_Kset hf.2.1 hf.2.2
    refine ⟨Kset n, isCompact_Kset n, Kset_subset_H n, hn,
      ⟨φ n, mem_iUnion.2 ⟨n, Or.inr rfl⟩, hφ0 n, hφ1 n⟩, fun η hη => ?_⟩
    obtain ⟨g, hgD, hg⟩ := hDa n f hf hn η hη
    exact ⟨g, mem_iUnion.2 ⟨n, Or.inl hgD⟩, (hDt n g hgD).2, hg⟩

/-- **Vague limit from a dense countable family.** -/
theorem exists_isVagueLimitOn_of_family {μs : ℕ → Measure ℂ}
    (hfin : ∀ K, IsCompact K → K ⊆ H → ∀ᶠ k in atTop, μs k K < ∞) {F : Set (ℂ → ℝ)}
    (hF : IsDenseTestFamily F)
    (hconv : ∀ f ∈ F, ∃ l, Tendsto (fun k => ∫ z, f z ∂(μs k)) atTop (𝓝 l)) :
    ∃ μ, IsVagueLimitOn H μs μ :=
  exists_isVagueLimitOn_of_tendsto hfin (tendsto_of_denseTestFamily hfin hF hconv)

end VagueH
end QuantumZipper
