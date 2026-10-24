import LatticeProb.Analysis.Elliptic.Holder
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
# Smooth compactly supported approximation on open sets

Smooth compactly supported functions have finite Euclidean Hölder norms. On a bounded open
coordinate domain, a countable family of such functions is dense in the restricted `L²` space.
The smooth index is `∞`; the index `⊤` means analytic and forces compactly supported functions
to vanish in positive dimension.
-/

namespace LatticeProb

open MeasureTheory Set Metric
open Euclidean.Lattice Elliptic
open scoped ENNReal ContDiff Topology

noncomputable section

variable {d : ℕ}

/-- At the analytic regularity index `⊤`, compact support forces a function to vanish. -/
theorem analytic_compact_eq_zero {f : (Fin 1 → ℝ) → ℝ}
    (hf : ContDiff ℝ ⊤ f) (hs : HasCompactSupport f) : f = 0 := by
  obtain ⟨x, hx⟩ := (ne_univ_iff_exists_notMem (tsupport f)).mp hs.ne_univ
  have heq := hf.analyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
    isPreconnected_univ (mem_univ x) (notMem_tsupport_iff_eventuallyEq.mp hx)
  exact funext fun y => heq (mem_univ y)

/-- Continuous functions supported compactly inside an open bounded set are dense in `L²`. -/
theorem exists_continuous_supported_eLpNorm_sub_le {U : Set (Fin d → ℝ)}
    (hU : IsOpen U) (hbound : Bornology.IsBounded U)
    {f : (Fin d → ℝ) → ℝ} (hf : MemLp f 2 (volume.restrict U))
    {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g, eLpNorm (f - g) 2 (volume.restrict U) ≤ ε ∧
      Continuous g ∧ HasCompactSupport g ∧ tsupport g ⊆ U := by
  let μ := volume.restrict U
  apply hf.induction_dense (by norm_num)
    (fun g => Continuous g ∧ HasCompactSupport g ∧ tsupport g ⊆ U) _ _ _ hε
  · intro c t ht htμ ε hε
    obtain ⟨δ, hδ, hhalf⟩ := exists_Lp_half ℝ μ 2 hε
    obtain ⟨η, hη, hηbound⟩ := exists_eLpNorm_indicator_le (p := (2 : ℝ≥0∞))
      (μ := μ) (by norm_num) c hδ.ne'
    have hηpos : (η : ℝ≥0∞) ≠ 0 := (ENNReal.coe_pos.mpr hη).ne'
    have htU : volume (t ∩ U) ≠ ⊤ := by
      have hfinite : volume (t ∩ U) < ⊤ := by
        simpa only [μ, Measure.restrict_apply ht] using htμ
      exact hfinite.ne
    obtain ⟨s, hst, hs, herr⟩ := (ht.inter hU.measurableSet).exists_isCompact_sdiff_lt
      htU hηpos
    obtain ⟨V, hV, hsV, hVU⟩ := hs.exists_isOpen_closure_subset
      (hU.mem_nhdsSet.mpr (hst.trans inter_subset_right))
    have hts : s ⊆ t := hst.trans inter_subset_left
    have hsμ : μ s ≠ ⊤ := ne_top_of_le_ne_top htμ.ne (measure_mono hts)
    have herror : μ (t \ s) ≤ η := by
      rw [Measure.restrict_apply (ht.diff hs.measurableSet)]
      have hsubset : (t \ s) ∩ U ⊆ (t ∩ U) \ s := by
        intro x hx
        exact ⟨⟨hx.1.1, hx.2⟩, hx.1.2⟩
      exact (measure_mono hsubset).trans herr.le
    obtain ⟨g, hgc, hge, _, hgs, hgm⟩ :=
      exists_continuous_eLpNorm_sub_le_of_closed (μ := μ) (p := 2) (by norm_num)
        hs.isClosed hV hsV hsμ c hδ.ne'
    have hsupport : tsupport g ⊆ U :=
      (closure_mono hgs).trans hVU
    have hcompact : HasCompactSupport g :=
      hbound.isCompact_closure.of_isClosed_subset (isClosed_tsupport _)
        (hsupport.trans subset_closure)
    have hi : eLpNorm (s.indicator (fun _ => c) - t.indicator (fun _ => c)) 2 μ ≤ δ := by
      rw [← eLpNorm_neg, neg_sub, ← indicator_sdiff hts]
      exact hηbound _ herror
    refine ⟨g, ?_, hgc, hcompact, hsupport⟩
    convert! (hhalf _ _
      (hgm.aestronglyMeasurable.sub
        (aestronglyMeasurable_const.indicator hs.measurableSet))
      ((aestronglyMeasurable_const.indicator hs.measurableSet).sub
        (aestronglyMeasurable_const.indicator ht)) hge hi).le using 2
    simp only [sub_add_sub_cancel]
  · rintro f g ⟨hfc, hfs, hfU⟩ ⟨hgc, hgs, hgU⟩
    exact ⟨hfc.add hgc, hfs.add hgs, (tsupport_add f g).trans (union_subset hfU hgU)⟩
  · rintro g ⟨hgc, _, _⟩
    exact hgc.aestronglyMeasurable

/-- Smooth approximation can preserve the topological support of a continuous function. -/
theorem exists_smooth_eLpNorm_sub_le_tsupport {μ : Measure (Fin d → ℝ)}
    [IsFiniteMeasureOnCompacts μ] {f : (Fin d → ℝ) → ℝ}
    (hs : HasCompactSupport f) (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ g, HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧ tsupport g ⊆ tsupport f ∧
      eLpNorm (f - g) 2 μ ≤ ENNReal.ofReal ε := by
  by_cases hz : f =ᵐ[μ] 0
  · refine ⟨0, HasCompactSupport.zero, contDiff_const, ?_, ?_⟩
    · simp only [tsupport_zero, empty_subset]
    · simp only [sub_zero, eLpNorm_congr_ae hz, eLpNorm_zero, zero_le]
  have hfinite : μ (tsupport f) ≠ ⊤ := hs.measure_lt_top.ne
  have hpos : 0 < (μ (tsupport f)).toReal := by
    rw [← Measure.measure_support_eq_zero_iff _] at hz
    exact ENNReal.toReal_pos
      (pos_mono (subset_tsupport f) (pos_of_ne_zero hz)).ne' hfinite
  let δ := ε * (μ (tsupport f)).toReal ^ (-(1 / (2 : ℝ≥0∞).toReal))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hscale : ENNReal.ofReal δ * μ (tsupport f) ^ (1 / (2 : ℝ≥0∞).toReal) ≤
      ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_toReal hfinite, ENNReal.ofReal_rpow_of_pos hpos,
      ← ENNReal.ofReal_mul hδ.le, ENNReal.ofReal_le_ofReal_iff hε.le]
    dsimp [δ]
    rw [mul_assoc, ← Real.rpow_add hpos, neg_add_cancel, Real.rpow_zero, mul_one]
  obtain ⟨g, hgc, hge, hgs⟩ := hf.exists_contDiff_approx ⊤
    (ε := fun _ => δ) continuous_const (fun _ => hδ)
  refine ⟨g, hs.mono hgs, hgc, closure_mono hgs, ?_⟩
  exact (eLpNorm_sub_le_of_dist_bdd μ (by norm_num) hs.measurableSet hδ.le
    (fun x => by simpa only [dist_comm] using (hge x).le)
    (subset_tsupport f) (hgs.trans (subset_tsupport f))).trans hscale

/-- Every restricted `L²` function admits smooth approximation with support inside the domain. -/
theorem exists_smooth_supported_eLpNorm_sub_le {U : Set (Fin d → ℝ)}
    (hU : IsOpen U) (hbound : Bornology.IsBounded U)
    {f : (Fin d → ℝ) → ℝ} (hf : MemLp f 2 (volume.restrict U))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g, HasCompactSupport g ∧ ContDiff ℝ ∞ g ∧ tsupport g ⊆ U ∧
      eLpNorm (f - g) 2 (volume.restrict U) ≤ ENNReal.ofReal ε := by
  obtain ⟨g, hge, hgc, hgs, hgU⟩ := exists_continuous_supported_eLpNorm_sub_le
    hU hbound hf (ENNReal.ofReal_pos.mpr (half_pos hε)).ne'
  obtain ⟨g', hg's, hg'c, hg'U, hg'e⟩ :=
    exists_smooth_eLpNorm_sub_le_tsupport (μ := volume.restrict U) hgs hgc (half_pos hε)
  have hgm : MemLp g 2 (volume.restrict U) := hgc.memLp_of_hasCompactSupport hgs
  have hg'm : MemLp g' 2 (volume.restrict U) := hg'c.continuous.memLp_of_hasCompactSupport hg's
  refine ⟨g', hg's, hg'c, hg'U.trans hgU, ?_⟩
  calc
    eLpNorm (f - g') 2 (volume.restrict U) =
        eLpNorm ((f - g) + (g - g')) 2 (volume.restrict U) := by
      congr 1
      funext x
      simp only [Pi.add_apply, Pi.sub_apply, sub_add_sub_cancel]
    _ ≤ eLpNorm (f - g) 2 (volume.restrict U) +
        eLpNorm (g - g') 2 (volume.restrict U) :=
      eLpNorm_add_le (hf.sub hgm).aestronglyMeasurable
        (hgm.sub hg'm).aestronglyMeasurable (by norm_num)
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := add_le_add hge hg'e
    _ = ENNReal.ofReal ε := by rw [← ENNReal.ofReal_add (half_pos hε).le
        (half_pos hε).le, add_halves]

/-- Restricted `L²` classes with a smooth representative supported inside the domain are dense. -/
theorem dense_smooth_supported {U : Set (Fin d → ℝ)}
    (hU : IsOpen U) (hbound : Bornology.IsBounded U) :
    Dense {u : Lp ℝ 2 (volume.restrict U) | ∃ g : (Fin d → ℝ) → ℝ,
      u =ᵐ[volume.restrict U] g ∧ ContDiff ℝ ∞ g ∧
        HasCompactSupport g ∧ tsupport g ⊆ U} := by
  intro u
  refine (mem_closure_iff_nhds_basis Metric.nhds_basis_closedBall).2 fun ε hε => ?_
  obtain ⟨g, hgs, hgc, hgU, hge⟩ := exists_smooth_supported_eLpNorm_sub_le
    hU hbound (Lp.memLp u) hε
  have hgm : MemLp g 2 (volume.restrict U) := hgc.continuous.memLp_of_hasCompactSupport hgs
  refine ⟨hgm.toLp g, ⟨g, hgm.coeFn_toLp, hgc, hgs, hgU⟩, ?_⟩
  rw [Metric.mem_closedBall, dist_comm, Lp.dist_def,
    ← ENNReal.le_ofReal_iff_toReal_le
      ((Lp.memLp u).sub (Lp.memLp (hgm.toLp g))).eLpNorm_ne_top hε.le]
  convert hge using 1
  apply eLpNorm_congr_ae
  filter_upwards [hgm.coeFn_toLp] with x hx
  simp only [Pi.sub_apply, hx]

/-- A bounded open coordinate domain admits a countable dense family of smooth test functions. -/
theorem exists_dense_smooth_family_infty {U : Set (Fin d → ℝ)}
    (hU : IsOpen U) (hbound : Bornology.IsBounded U) :
    ∃ (f : ℕ → (Fin d → ℝ) → ℝ)
      (hf : ∀ k, MemLp (f k) 2 (volume.restrict U)),
      (∀ k, ContDiff ℝ ∞ (f k) ∧ HasCompactSupport (f k) ∧ tsupport (f k) ⊆ U) ∧
      DenseRange (fun k => (hf k).toLp (f k)) := by
  let S := {u : Lp ℝ 2 (volume.restrict U) | ∃ g : (Fin d → ℝ) → ℝ,
    u =ᵐ[volume.restrict U] g ∧ ContDiff ℝ ∞ g ∧
      HasCompactSupport g ∧ tsupport g ⊆ U}
  have hS : Dense S := dense_smooth_supported hU hbound
  letI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  letI : Nonempty S := hS.nonempty.to_subtype
  obtain ⟨v, hv⟩ := TopologicalSpace.exists_dense_seq S
  have hreps (k : ℕ) : ∃ g : (Fin d → ℝ) → ℝ,
      (v k).val =ᵐ[volume.restrict U] g ∧ ContDiff ℝ ∞ g ∧
        HasCompactSupport g ∧ tsupport g ⊆ U := (v k).property
  choose f heq hfc hfs hfU using hreps
  let hf k : MemLp (f k) 2 (volume.restrict U) :=
    (hfc k).continuous.memLp_of_hasCompactSupport (hfs k)
  refine ⟨f, hf, fun k => ⟨hfc k, hfs k, hfU k⟩, ?_⟩
  have heqLp (k : ℕ) : (hf k).toLp (f k) = (v k).val := by
    apply Lp.ext
    exact (hf k).coeFn_toLp.trans (heq k).symm
  have hdense := hS.denseRange_val.comp hv continuous_subtype_val
  simpa only [Function.comp_def, heqLp] using hdense

/-- The coordinate supremum norm is bounded by the Euclidean radius. -/
theorem norm_le_euclidean_radius (x : Fin d → ℝ) : ‖x‖ ≤ radius x := by
  exact (pi_norm_le_iff_of_nonneg (radius_nonneg x)).2 fun i => by
    simpa only [Real.norm_eq_abs] using abs_coord_le_radius x i

/-- Smooth compactly supported functions have a global Euclidean Hölder bound. -/
theorem smooth_compact_holder_bound {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) {σ : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) :
    ∃ C : ℝ, ∀ x y, |f x - f y| ≤ C * radius (x - y) ^ σ := by
  obtain ⟨M, hM⟩ := hs.exists_bound_of_continuous hf.continuous
  obtain ⟨L, hL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hf (by simp)
  have hM0 : 0 ≤ M := (norm_nonneg (f 0)).trans (hM 0)
  refine ⟨L + 2 * M, fun x y => ?_⟩
  have hr := Real.rpow_nonneg (radius_nonneg (x - y)) σ
  by_cases hsmall : radius (x - y) ≤ 1
  · calc
      |f x - f y| ≤ L * ‖x - y‖ := by
        simpa only [Real.norm_eq_abs, dist_eq_norm] using hL.dist_le_mul x y
      _ ≤ L * radius (x - y) :=
        mul_le_mul_of_nonneg_left (norm_le_euclidean_radius _) L.coe_nonneg
      _ ≤ L * radius (x - y) ^ σ := mul_le_mul_of_nonneg_left
        (Real.self_le_rpow_of_le_one (radius_nonneg _) hsmall hσ1) L.coe_nonneg
      _ ≤ (L + 2 * M) * radius (x - y) ^ σ :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity)) hr
  · have hlarge := Real.one_le_rpow (le_of_not_ge hsmall) hσ
    have hb : |f x - f y| ≤ 2 * M := by
      calc
        |f x - f y| ≤ |f x| + |f y| := abs_sub _ _
        _ ≤ M + M := add_le_add (by simpa only [Real.norm_eq_abs] using hM x)
          (by simpa only [Real.norm_eq_abs] using hM y)
        _ = 2 * M := (two_mul M).symm
    calc
      |f x - f y| ≤ 2 * M := hb
      _ ≤ (2 * M) * radius (x - y) ^ σ :=
        le_mul_of_one_le_right (by positivity) hlarge
      _ ≤ (L + 2 * M) * radius (x - y) ^ σ :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left L.coe_nonneg) hr

/-- A smooth compactly supported function has finite Euclidean `C^{0,σ}` norm on any set. -/
theorem c0HolderNorm_lt_top_of_smooth_compact {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) {σ : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (S : Set (Fin d → ℝ)) :
    c0HolderNorm σ S f < ⊤ := by
  obtain ⟨M, hM⟩ := hs.exists_bound_of_continuous hf.continuous
  obtain ⟨C, hC⟩ := smooth_compact_holder_bound hf hs hσ hσ1
  apply ENNReal.add_lt_top.mpr
  constructor
  · exact supNorm_lt_top_of_bound M fun x _ => by
      simpa only [Real.norm_eq_abs] using hM x
  · apply holderSeminorm_lt_top_of_bound C
    intro x _ y _ hxy
    exact (div_le_iff₀ (Real.rpow_pos_of_pos
      (radius_pos (sub_ne_zero.mpr hxy)) σ)).mpr (hC x y)

/-- Coordinate derivatives preserve smoothness and compact support. -/
theorem smooth_compact_partialDeriv {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (i : Fin d) :
    ContDiff ℝ ∞ (partialDeriv i f) ∧ HasCompactSupport (partialDeriv i f) := by
  constructor
  · exact (hf.fderiv_right (by simp)).clm_apply contDiff_const
  · exact hs.fderiv_apply ℝ (Pi.single i 1)

/-- Second coordinate derivatives preserve smoothness and compact support. -/
theorem smooth_compact_secondPartial {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) (i j : Fin d) :
    ContDiff ℝ ∞ (secondPartial i j f) ∧ HasCompactSupport (secondPartial i j f) := by
  let e := ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => Fin d → ℝ) ℝ
    ![Pi.single i 1, Pi.single j 1]
  constructor
  · have hindex : ((⊤ : ℕ∞) : ℕ∞ω) + 2 ≤ ((⊤ : ℕ∞) : ℕ∞ω) := by
      calc
        ((⊤ : ℕ∞) : ℕ∞ω) + 2 = (((⊤ : ℕ∞) : ℕ∞ω) + 1) + 1 := by
          rw [add_assoc, one_add_one_eq_two]
        _ = ((⊤ : ℕ∞) : ℕ∞ω) := by rw [ENat.coe_top_add_one, ENat.coe_top_add_one]
        _ ≤ ((⊤ : ℕ∞) : ℕ∞ω) := le_rfl
    exact e.contDiff.comp (hf.iteratedFDeriv_right hindex)
  · exact (hs.iteratedFDeriv 2).comp_left (g := e) (map_zero e)

/-- Smooth compactly supported functions have finite Euclidean `C^{2,σ}` norm on any set. -/
theorem c2HolderNorm_lt_top_of_smooth_compact {f : (Fin d → ℝ) → ℝ}
    (hf : ContDiff ℝ ∞ f) (hs : HasCompactSupport f) {σ : ℝ}
    (hσ : 0 ≤ σ) (hσ1 : σ ≤ 1) (S : Set (Fin d → ℝ)) :
    c2HolderNorm σ S f < ⊤ := by
  have finite_sup (g : (Fin d → ℝ) → ℝ) (hg : ContDiff ℝ ∞ g)
      (hgs : HasCompactSupport g) : supNorm S g < ⊤ := by
    obtain ⟨M, hM⟩ := hgs.exists_bound_of_continuous hg.continuous
    exact supNorm_lt_top_of_bound M fun x _ => by
      simpa only [Real.norm_eq_abs] using hM x
  have first i := smooth_compact_partialDeriv hf hs i
  have second i j := smooth_compact_secondPartial hf hs i j
  simp only [c2HolderNorm, ENNReal.add_lt_top, ENNReal.sum_lt_top]
  refine ⟨⟨⟨finite_sup f hf hs, fun i _ =>
    finite_sup _ (first i).1 (first i).2⟩, fun i _ j _ =>
    finite_sup _ (second i j).1 (second i j).2⟩, fun i _ j _ => ?_⟩
  exact lt_of_le_of_lt le_add_self
    (c0HolderNorm_lt_top_of_smooth_compact (second i j).1 (second i j).2 hσ hσ1 S)

/-- A countable dense test family also satisfies all the finite Hölder-norm requirements. -/
theorem exists_dense_smooth_family_infty_holder {U : Set (Fin d → ℝ)}
    (hU : IsOpen U) (hbound : Bornology.IsBounded U) :
    ∃ (f : ℕ → (Fin d → ℝ) → ℝ)
      (hf : ∀ k, MemLp (f k) 2 (volume.restrict U)),
      DenseRange (fun k => (hf k).toLp (f k)) ∧
      ∀ k, ContDiff ℝ ∞ (f k) ∧ HasCompactSupport (f k) ∧ tsupport (f k) ⊆ U ∧
        ∀ σ : ℝ, 0 < σ → σ < 1 →
          c0HolderNorm σ (closure U) (f k) < ⊤ ∧
          c2HolderNorm σ (closure U) (f k) < ⊤ ∧
          ∃ M : ℝ, 0 ≤ M ∧ c0HolderNorm σ (closure U) (f k) ≤ ENNReal.ofReal M := by
  obtain ⟨f, hf, hregular, hdense⟩ := exists_dense_smooth_family_infty hU hbound
  refine ⟨f, hf, hdense, fun k => ⟨(hregular k).1, (hregular k).2.1,
    (hregular k).2.2, fun σ hσ hσ1 => ?_⟩⟩
  have hzero := c0HolderNorm_lt_top_of_smooth_compact
    (hregular k).1 (hregular k).2.1 hσ.le hσ1.le (closure U)
  have htwo := c2HolderNorm_lt_top_of_smooth_compact
    (hregular k).1 (hregular k).2.1 hσ.le hσ1.le (closure U)
  refine ⟨hzero, htwo, (c0HolderNorm σ (closure U) (f k)).toReal,
    ENNReal.toReal_nonneg, ?_⟩
  exact (ENNReal.ofReal_toReal hzero.ne).ge

end

end LatticeProb
