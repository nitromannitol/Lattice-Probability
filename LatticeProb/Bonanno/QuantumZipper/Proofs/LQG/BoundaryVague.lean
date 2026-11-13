/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.LQG.BoundaryVague at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.LQG.Measures
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# M4-R5(b): vague limits on `ℝ` from a countable family of test functions

A deterministic tool for M4-B3. We fix an explicit countable family of continuous compactly
supported test functions on `ℝ`: the bumps `bump N` (`= 1` on `[-N,N]`, `0` off
`(-(N+1), N+1)`) and `testFam N m = bump N · (g_{N,m} ∘ projIcc)`, where `g_{N,·}` is a dense
sequence of `C([-(N+1), N+1], ℝ)`. Every `f ∈ C_c(ℝ)` is approximated by the family in the strong
sense `|f − testFam N m| ≤ ε · bump N` (`exists_testFam_approx`).

`exists_isVagueLimitR_of_testFam`: if the measures `νs k` are finite on compacts and
`∫ g dνs k` converges for every `g` of the family, then `νs` has a vague limit (constructed by the
Riesz–Markov–Kakutani theorem).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped CompactlySupported ENNReal

namespace QuantumZipper
namespace BdryVague

/-- The bump `max 0 (min 1 (N + 1 − |x|))`. -/
def bump (N : ℕ) (x : ℝ) : ℝ := max 0 (min 1 ((N : ℝ) + 1 - |x|))

theorem continuous_bump (N : ℕ) : Continuous (bump N) :=
  continuous_const.max (continuous_const.min (continuous_const.sub continuous_abs))

theorem bump_nonneg (N : ℕ) (x : ℝ) : 0 ≤ bump N x := le_max_left _ _

theorem bump_eq_one {N : ℕ} {x : ℝ} (hx : |x| ≤ N) : bump N x = 1 := by
  unfold bump
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

theorem bump_eq_zero {N : ℕ} {x : ℝ} (hx : (N : ℝ) + 1 ≤ |x|) : bump N x = 0 := by
  unfold bump
  rw [max_eq_left]
  exact min_le_of_right_le (by linarith)

theorem hasCompactSupport_bump (N : ℕ) : HasCompactSupport (bump N) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := -((N : ℝ) + 1)) (b := (N : ℝ) + 1))
    fun x hx => bump_eq_zero ?_
  simp only [mem_Icc, not_and_or, not_le] at hx
  rcases hx with h | h
  · rw [abs_of_neg (by linarith)]; linarith
  · rw [abs_of_pos (by linarith)]; linarith

theorem Icc_le (N : ℕ) : -((N : ℝ) + 1) ≤ (N : ℝ) + 1 := by linarith [(N.cast_nonneg : (0 : ℝ) ≤ N)]

/-- A dense sequence of `C([-(N+1), N+1], ℝ)`. -/
def dseq (N : ℕ) : ℕ → C(Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1), ℝ) :=
  TopologicalSpace.denseSeq _

/-- The countable test family. -/
def testFam (N m : ℕ) (x : ℝ) : ℝ :=
  bump N x * dseq N m (projIcc (-((N : ℝ) + 1)) ((N : ℝ) + 1) (Icc_le N) x)

theorem continuous_testFam (N m : ℕ) : Continuous (testFam N m) :=
  (continuous_bump N).mul ((dseq N m).continuous.comp continuous_projIcc)

theorem hasCompactSupport_testFam (N m : ℕ) : HasCompactSupport (testFam N m) :=
  (hasCompactSupport_bump N).mul_right

/-- Every `f ∈ C_c(ℝ)` is approximated by the family: `|f − testFam N m| ≤ ε · bump N`. -/
theorem exists_testFam_approx {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f) :
    ∃ N : ℕ, ∀ ε > 0, ∃ m, ∀ x, |f x - testFam N m x| ≤ ε * bump N x := by
  obtain ⟨r, hr⟩ := hcs.isCompact.isBounded.subset_closedBall (0 : ℝ)
  refine ⟨⌈r⌉₊, fun ε hε => ?_⟩
  set N := ⌈r⌉₊
  have hsupp : ∀ x, f x ≠ 0 → |x| ≤ N := by
    intro x hx
    have := hr (subset_tsupport f hx)
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    exact this.trans (Nat.le_ceil r)
  have hfb : ∀ x, f x = bump N x * f x := by
    intro x
    by_cases h : f x = 0
    · simp [h]
    · rw [bump_eq_one (hsupp x h), one_mul]
  let fr : C(Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1), ℝ) := ⟨fun y => f y, hf.comp continuous_subtype_val⟩
  obtain ⟨m, hm⟩ := Metric.denseRange_iff.1 (TopologicalSpace.denseRange_denseSeq
    (C(Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1), ℝ))) fr ε hε
  refine ⟨m, fun x => ?_⟩
  by_cases hx : x ∈ Icc (-((N : ℝ) + 1)) ((N : ℝ) + 1)
  · have h1 : |f x - dseq N m ⟨x, hx⟩| ≤ ε := by
      have := (ContinuousMap.dist_apply_le_dist (f := fr) (g := dseq N m) ⟨x, hx⟩).trans hm.le
      rwa [Real.dist_eq] at this
    unfold testFam
    rw [projIcc_of_mem _ hx, hfb x, ← mul_sub, abs_mul, abs_of_nonneg (bump_nonneg N x),
      mul_comm ε]
    exact mul_le_mul_of_nonneg_left h1 (bump_nonneg N x)
  · have hb : bump N x = 0 := by
      apply bump_eq_zero
      simp only [mem_Icc, not_and_or, not_le] at hx
      rcases hx with h | h
      · rw [abs_of_neg (by linarith [(N.cast_nonneg : (0 : ℝ) ≤ N)])]; linarith
      · rw [abs_of_pos (by linarith [(N.cast_nonneg : (0 : ℝ) ≤ N)])]; linarith
    have hf0 : f x = 0 := by rw [hfb x, hb, zero_mul]
    simp [testFam, hb, hf0]

/-- Convergence on the family implies convergence for every `f ∈ C_c(ℝ)`. -/
theorem exists_tendsto_of_testFam {νs : ℕ → Measure ℝ}
    (hfin : ∀ k, IsFiniteMeasureOnCompacts (νs k))
    (hconv : ∀ N m, ∃ l, Tendsto (fun k => ∫ x, testFam N m x ∂νs k) atTop (𝓝 l))
    (hbump : ∀ N, ∃ l, Tendsto (fun k => ∫ x, bump N x ∂νs k) atTop (𝓝 l))
    {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f) :
    ∃ l, Tendsto (fun k => ∫ x, f x ∂νs k) atTop (𝓝 l) := by
  obtain ⟨N, hN⟩ := exists_testFam_approx hf hcs
  obtain ⟨lb, hlb⟩ := hbump N
  obtain ⟨B, hB⟩ := hlb.bddAbove_range
  have hB' : ∀ k, ∫ x, bump N x ∂νs k ≤ B := fun k => hB ⟨k, rfl⟩
  have hB0 : 0 ≤ B := (integral_nonneg (bump_nonneg N)).trans (hB' 0)
  apply cauchySeq_tendsto_of_complete
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨m, hm⟩ := hN (ε / (3 * (B + 1))) (by positivity)
  obtain ⟨l, hl⟩ := hconv N m
  obtain ⟨K, hK⟩ := Metric.cauchySeq_iff.1 hl.cauchySeq (ε / 3) (by positivity)
  have happ : ∀ k, |∫ x, f x ∂νs k - ∫ x, testFam N m x ∂νs k| ≤ ε / 3 := by
    intro k
    have := hfin k
    have hi1 : Integrable f (νs k) := hf.integrable_of_hasCompactSupport hcs
    have hi2 : Integrable (testFam N m) (νs k) :=
      (continuous_testFam N m).integrable_of_hasCompactSupport (hasCompactSupport_testFam N m)
    have hi3 : Integrable (bump N) (νs k) :=
      (continuous_bump N).integrable_of_hasCompactSupport (hasCompactSupport_bump N)
    rw [← integral_sub hi1 hi2]
    have := norm_integral_le_of_norm_le (hi3.const_mul (ε / (3 * (B + 1))))
      (ae_of_all _ fun x => by rw [Real.norm_eq_abs]; exact hm x)
    rw [Real.norm_eq_abs, integral_const_mul] at this
    refine this.trans ?_
    calc ε / (3 * (B + 1)) * ∫ x, bump N x ∂νs k ≤ ε / (3 * (B + 1)) * B :=
          mul_le_mul_of_nonneg_left (hB' k) (by positivity)
      _ ≤ ε / 3 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith
  refine ⟨K, fun a ha b hb => ?_⟩
  have h2 := hK a ha b hb
  rw [Real.dist_eq] at h2 ⊢
  have h1 := happ a
  have h3 := happ b
  have t1 := abs_sub_le (∫ x, f x ∂νs a) (∫ x, testFam N m x ∂νs a) (∫ x, f x ∂νs b)
  have t2 := abs_sub_le (∫ x, testFam N m x ∂νs a) (∫ x, testFam N m x ∂νs b) (∫ x, f x ∂νs b)
  rw [abs_sub_comm (∫ x, testFam N m x ∂νs b)] at t2
  linarith

/-- **Vague limit from the countable family** (Riesz–Markov–Kakutani). -/
theorem exists_isVagueLimitR_of_testFam {νs : ℕ → Measure ℝ}
    (hfin : ∀ k, IsFiniteMeasureOnCompacts (νs k))
    (hconv : ∀ N m, ∃ l, Tendsto (fun k => ∫ x, testFam N m x ∂νs k) atTop (𝓝 l))
    (hbump : ∀ N, ∃ l, Tendsto (fun k => ∫ x, bump N x ∂νs k) atTop (𝓝 l)) :
    ∃ ν, IsVagueLimitR νs ν := by
  have htend : ∀ f : C_c(ℝ, ℝ), Tendsto (fun k => ∫ x, f x ∂νs k) atTop
      (𝓝 (limUnder atTop fun k => ∫ x, f x ∂νs k)) := fun f =>
    tendsto_nhds_limUnder (exists_tendsto_of_testFam hfin hconv hbump f.continuous
      f.hasCompactSupport)
  have hint : ∀ (f : C_c(ℝ, ℝ)) k, Integrable f (νs k) := fun f k => by
    have := hfin k; exact f.continuous.integrable_of_hasCompactSupport f.hasCompactSupport
  let Λ₀ : C_c(ℝ, ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun f => limUnder atTop fun k => ∫ x, f x ∂νs k
      map_add' := fun f g => by
        refine tendsto_nhds_unique (htend (f + g)) ?_
        have e : (fun k => ∫ x, (f + g) x ∂νs k) =
            fun k => ∫ x, f x ∂νs k + ∫ x, g x ∂νs k := by
          funext k
          simp only [CompactlySupportedContinuousMap.coe_add, Pi.add_apply]
          exact integral_add (hint f k) (hint g k)
        rw [e]; exact (htend f).add (htend g)
      map_smul' := fun c f => by
        refine tendsto_nhds_unique (htend (c • f)) ?_
        have e : (fun k => ∫ x, (c • f) x ∂νs k) = fun k => c • ∫ x, f x ∂νs k := by
          funext k
          simp only [CompactlySupportedContinuousMap.coe_smul, Pi.smul_apply]
          exact integral_smul c _
        rw [e]; exact (htend f).const_smul c }
  let Λ : C_c(ℝ, ℝ) →ₚ[ℝ] ℝ := PositiveLinearMap.mk₀ Λ₀ fun f hf =>
    ge_of_tendsto' (htend f) fun k =>
      integral_nonneg fun x => (CompactlySupportedContinuousMap.le_def.1 hf) x
  refine ⟨RealRMK.rieszMeasure Λ, inferInstance, fun f hf hcs => ?_⟩
  let fc : C_c(ℝ, ℝ) := ⟨⟨f, hf⟩, hcs⟩
  have h := RealRMK.integral_rieszMeasure Λ fc
  change ∫ x, f x ∂(RealRMK.rieszMeasure Λ) = limUnder atTop (fun k => ∫ x, f x ∂νs k) at h
  rw [h]
  exact htend fc

/-- Finiteness on all `[-N, N]` gives finiteness on compacts. -/
theorem isFiniteMeasureOnCompacts_of_Icc {μ : Measure ℝ}
    (h : ∀ N : ℕ, μ (Icc (-(N : ℝ)) N) < ∞) : IsFiniteMeasureOnCompacts μ := by
  refine ⟨fun K hK => ?_⟩
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0 : ℝ)
  rw [Real.closedBall_eq_Icc, zero_sub, zero_add] at hr
  refine (measure_mono (hr.trans (Icc_subset_Icc ?_ ?_))).trans_lt (h ⌈r⌉₊)
  · exact neg_le_neg (Nat.le_ceil r)
  · exact Nat.le_ceil r

/-- Vague limits are stable under multiplication by a finite constant. -/
theorem IsVagueLimitR.const_smul {νs : ℕ → Measure ℝ} {ν : Measure ℝ} (h : IsVagueLimitR νs ν)
    {c : ℝ≥0∞} (hc : c ≠ ∞) : IsVagueLimitR (fun k => c • νs k) (c • ν) := by
  obtain ⟨hloc, htend⟩ := h
  refine ⟨⟨fun x => ?_⟩, fun f hf hcs => ?_⟩
  · obtain ⟨U, hU, hfin⟩ := hloc.finiteAtNhds x
    exact ⟨U, hU, by
      rw [Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_lt_top hc.lt_top hfin⟩
  · simp only [integral_smul_measure]
    exact (htend f hf hcs).const_smul _

end BdryVague
end QuantumZipper
