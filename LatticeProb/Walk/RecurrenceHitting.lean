import LatticeProb.Walk.ExteriorDirichlet
import LatticeProb.Walk.SRWGreenLower
import LatticeProb.Walk.PotentialKernel

/-!
# Hitting every site in two dimensions

The finite first-passage decomposition bounds a truncated Green function by
the eventual hitting probability times the return Green function. In two
dimensions the return Green function diverges, whereas its difference from
the Green function at a fixed site converges to the potential kernel. Hence
the eventual hitting probability is one.
-/

namespace LatticeProb

open Finset Filter MeasureTheory Topology

variable {d : ℕ}

/-- A uniform direction has the actual increment law after applying its
coordinate vector. -/
theorem stepLaw_map_dirVec (d : ℕ) [NeZero d] :
    (stepLaw d).map dirVec = incLaw d := by
  classical
  have huniform : stepLaw d = (((2 * d : ℕ) : ENNReal)⁻¹) •
      ∑ a : Dir d, Measure.dirac a := by
    calc
      stepLaw d = ∑ a : Dir d, stepLaw d {a} • Measure.dirac a := by
        rw [← Measure.sum_fintype, Measure.sum_smul_dirac]
      _ = _ := by simp only [stepLaw_singleton, Finset.smul_sum]
  have hmeas : Measurable (dirVec : Dir d → Site d) := measurable_of_countable _
  rw [huniform, Measure.map_smul, Measure.map_finset_sum' hmeas.aemeasurable]
  simp only [Measure.map_dirac' hmeas, Fintype.sum_prod_type, Fintype.sum_bool,
    dirVec_eq_unit, dirVec_eq_neg_unit]
  rw [incLaw, instructionLaw]
  simp only [zero_add, zero_sub, Nat.cast_mul, Nat.cast_ofNat]

/-- Independent uniform directions give independent increments with the
specified increment law. -/
theorem pathLaw_map_dirVec (d : ℕ) [NeZero d] :
    (pathLaw d).map (fun ξ n => dirVec (ξ n)) = incPathLaw d := by
  unfold pathLaw incPathLaw
  rw [Measure.infinitePi_map_pi (μ := fun _ : ℕ => stepLaw d)
    (fun _ => measurable_of_countable dirVec)]
  simp only [stepLaw_map_dirVec]

/-- Accumulating the uniform directions gives the actual position-path law. -/
theorem pathLaw_map_sitePath (d : ℕ) [NeZero d] (x : Site d) :
    (pathLaw d).map (fun ξ n => x + ∑ j ∈ Finset.range n, dirVec (ξ j)) =
      siteWalkLaw d x := by
  have hmeas : Measurable (fun ξ : ℕ → Dir d => fun n => dirVec (ξ n)) :=
    measurable_pi_lambda _ fun n => (measurable_of_countable dirVec).comp
      (measurable_pi_apply n)
  change (pathLaw d).map (sitePath x ∘ (fun ξ n => dirVec (ξ n))) = _
  rw [← Measure.map_map (measurable_sitePath x) hmeas, pathLaw_map_dirVec]
  rfl

/-- The first-passage decomposition summed over a finite time horizon. -/
theorem srwGreen_eq_sum_srwFirstHit (n : ℕ) (x : Site d) :
    srwGreen d n x =
      ∑ j ∈ Finset.range n, srwFirstHit d j x * srwGreen d (n - j) 0 := by
  induction n with
  | zero => simp only [srwGreen_zero, Finset.range_zero, Finset.sum_empty]
  | succ n ih =>
      rw [srwGreen_succ, ih, srwHeat_eq_sum_srwFirstHit]
      have hpad : (∑ j ∈ Finset.range n, srwFirstHit d j x * srwGreen d (n - j) 0) =
          ∑ j ∈ Finset.range (n + 1), srwFirstHit d j x * srwGreen d (n - j) 0 := by
        rw [Finset.sum_range_succ, Nat.sub_self, srwGreen_zero, mul_zero, add_zero]
      rw [hpad, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← mul_add, ← srwGreen_succ]
      congr 2
      have hjn := Finset.mem_range.mp hj
      omega

/-- Truncated Green functions increase with the time horizon. -/
theorem srwGreen_mono {m n : ℕ} (hmn : m ≤ n) (x : Site d) :
    srwGreen d m x ≤ srwGreen d n x := by
  unfold srwGreen
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hmn)
    (fun j _ _ => srwHeat_nonneg j x)

/-- A finite Green function is bounded by eventual first passage times the
return Green function, without assuming transience. -/
theorem srwGreen_le_srwHitProb_mul (hd : 0 < d) (n : ℕ) (x : Site d) :
    srwGreen d n x ≤ srwHitProb d x * srwGreen d n 0 := by
  rw [srwGreen_eq_sum_srwFirstHit]
  calc
    (∑ j ∈ Finset.range n, srwFirstHit d j x * srwGreen d (n - j) 0) ≤
        ∑ j ∈ Finset.range n, srwFirstHit d j x * srwGreen d n 0 :=
      Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (srwGreen_mono (Nat.sub_le n j) 0)
          (srwFirstHit_nonneg j x)
    _ = (∑ j ∈ Finset.range n, srwFirstHit d j x) * srwGreen d n 0 :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ srwHitProb d x * srwGreen d n 0 :=
      mul_le_mul_of_nonneg_right
        ((summable_srwFirstHit hd x).sum_le_tsum (Finset.range n)
          (fun j _ => srwFirstHit_nonneg j x)) (srwGreen_nonneg n 0)

/-- The two-dimensional return Green function tends to infinity. -/
theorem tendsto_srwGreen_two_dim_origin :
    Tendsto (fun n : ℕ => srwGreen 2 n 0) atTop atTop := by
  obtain ⟨c, hc, hbound⟩ := exists_le_srwGreen_two_dim
  have hlog : Tendsto (fun n : ℕ => c * Real.log (n : ℝ)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hc
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  exact tendsto_atTop_mono' atTop
    (eventually_atTop.mpr ⟨2, fun n hn => hbound n hn⟩) hlog

/-- Simple random walk in two dimensions hits the origin with probability one
from every starting site. -/
theorem srwHitProb_two_dim_eq_one (x : Site 2) : srwHitProb 2 x = 1 := by
  apply le_antisymm (srwHitProb_le_one (by norm_num) x)
  by_contra h
  have hpos : 0 < 1 - srwHitProb 2 x := sub_pos.mpr (lt_of_not_ge h)
  have hdiv : Tendsto (fun n : ℕ => (1 - srwHitProb 2 x) * srwGreen 2 n 0)
      atTop atTop :=
    Filter.Tendsto.const_mul_atTop hpos tendsto_srwGreen_two_dim_origin
  have hbound (n : ℕ) :
      (1 - srwHitProb 2 x) * srwGreen 2 n 0 ≤ srwGreen 2 n 0 - srwGreen 2 n x := by
    have hgreen := srwGreen_le_srwHitProb_mul (by norm_num : 0 < 2) n x
    rw [sub_mul, one_mul]
    exact sub_le_sub_left hgreen _
  exact not_tendsto_atTop_of_tendsto_nhds (tendsto_potentialKernel x)
    (tendsto_atTop_mono hbound hdiv)

/-- The law on position paths hits the origin almost surely in dimension two. -/
theorem siteWalkLaw_two_dim_hitOrigin (x : Site 2) :
    siteWalkLaw 2 x (hitOrigin 2) = 1 := by
  rw [siteWalkLaw_hitOrigin (by norm_num), srwHitProb_two_dim_eq_one,
    ENNReal.ofReal_one]

/-- Hitting any fixed site is a measurable path event. Time zero is included. -/
theorem measurableSet_hit_site (a : Site d) :
    MeasurableSet {X : ℕ → Site d | ∃ n : ℕ, X n = a} := by
  simp only [Set.setOf_exists]
  exact MeasurableSet.iUnion fun n => measurableSet_eq_fun (measurable_pi_apply n)
    measurable_const

/-- Translate a target site to the origin in the actual position-path law. -/
theorem siteWalkLaw_hit_site [NeZero d] (hd : 1 ≤ d) (x a : Site d) :
    siteWalkLaw d x {X | ∃ n : ℕ, X n = a} =
      ENNReal.ofReal (srwHitProb d (x - a)) := by
  have hpre : sitePath x ⁻¹' {X | ∃ n : ℕ, X n = a} =
      sitePath (x - a) ⁻¹' hitOrigin d := by
    ext ξ
    have hshift (n : ℕ) : sitePath (x - a) ξ n = sitePath x ξ n - a := by
      unfold sitePath
      abel
    change (∃ n : ℕ, sitePath x ξ n = a) ↔
      ∃ n : ℕ, sitePath (x - a) ξ n = 0
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, by rw [hshift, hn, sub_self]⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, sub_eq_zero.mp ((hshift n).symm.trans hn)⟩
  rw [siteWalkLaw, Measure.map_apply (measurable_sitePath x) (measurableSet_hit_site a),
    hpre, ← Measure.map_apply (measurable_sitePath (x - a)) measurableSet_hitOrigin]
  exact siteWalkLaw_hitOrigin hd (x - a)

/-- Two-dimensional simple random walk hits every fixed site almost surely,
from every starting site, including a hit at time zero. -/
theorem siteWalkLaw_two_dim_hit_site (x a : Site 2) :
    siteWalkLaw 2 x {X | ∃ n : ℕ, X n = a} = 1 := by
  rw [siteWalkLaw_hit_site (by norm_num), srwHitProb_two_dim_eq_one,
    ENNReal.ofReal_one]

/-- The iid direction drivers hit every fixed site almost surely in two
dimensions. The sum is empty at time zero. -/
theorem pathLaw_two_dim_hit_site (x a : Site 2) :
    pathLaw 2 {ξ | ∃ n : ℕ, x + ∑ j ∈ Finset.range n, dirVec (ξ j) = a} = 1 := by
  have hmeas : Measurable (fun ξ : ℕ → Dir 2 => fun n =>
      x + ∑ j ∈ Finset.range n, dirVec (ξ j)) :=
    (measurable_sitePath x).comp (measurable_pi_lambda _ fun n =>
      (measurable_of_countable dirVec).comp (measurable_pi_apply n))
  have h := siteWalkLaw_two_dim_hit_site x a
  rw [← pathLaw_map_sitePath 2 x,
    Measure.map_apply hmeas (measurableSet_hit_site a)] at h
  exact h

end LatticeProb
