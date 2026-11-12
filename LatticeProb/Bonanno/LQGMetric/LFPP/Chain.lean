/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.LFPP.Chain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.LFPP.DistOn

/-!
# Reduction of the LFPP infimum to polygonal chains with vertices in a countable dense set

Task P2-LFPP, item 2 (measurability). For continuous `φ` and convex `S`, every piecewise C¹ path
`P : z → w` in `S` is approximated in LFPP cost by a polygonal chain `z = v₀, v₁, …, v_N,
v_{N+1} = w` with inner vertices in a dense subset `C ⊆ S`: on a fine partition `t_i = i/(N+1)`
the segment `[v_i, v_{i+1}]` costs at most `(e^{ξφ(P(t_i))} + ω/2)(|P(t_{i+1}) - P(t_i)| + 2ρ)`
(uniform continuity of `e^{ξφ}` and of `P`), and chord ≤ arclength bounds this by
`∫_{t_i}^{t_{i+1}} (e^{ξφ(P)} + ω)|P'| + O(ρ)`. Own elementary argument (Riemann-sum
approximation of a path integral); DFGPS/GM use the measurability without comment.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace LFPP

variable {ξ : ℝ} {φ : ℂ → ℝ} {S : Set ℂ}

theorem sum_setLIntegral_Ioc (g : ℝ → ℝ≥0∞) (u : ℕ → ℝ) (hu : Monotone u) (n : ℕ) :
    ∑ i ∈ Finset.range n, ∫⁻ τ in Ioc (u i) (u (i + 1)), g τ = ∫⁻ τ in Ioc (u 0) (u n), g τ := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih, ← lintegral_union measurableSet_Ioc
      (Ioc_disjoint_Ioc_of_le le_rfl), Ioc_union_Ioc_eq_Ioc (hu (Nat.zero_le m))
      (hu (Nat.le_succ m))]

/-- **Approximation of a path by a chain** (see the module docstring). -/
theorem exists_chain_le (hφ : Continuous φ) {C : Set ℂ}
    (hC : ∀ x ∈ S, ∀ ρ > 0, ∃ q ∈ C, ‖q - x‖ < ρ) {P : ℝ → ℂ} {z w : ℂ}
    (hP : IsPiecewiseC1Path P z w) (hPS : ∀ t ∈ Icc (0 : ℝ) 1, P t ∈ S) {δ : ℝ} (hδ : 0 < δ) :
    ∃ (N : ℕ) (v : ℕ → ℂ), v 0 = z ∧ v (N + 1) = w ∧ (∀ i, 1 ≤ i → i ≤ N → v i ∈ C) ∧
      ∑ i ∈ Finset.range (N + 1), segCost ξ φ (v i) (v (i + 1)) ≤
        lfppLen ξ φ P + ENNReal.ofReal δ := by
  classical
  set E : ℂ → ℝ := fun x => Real.exp (ξ * φ x) with hEdef
  have hE : Continuous E := Real.continuous_exp.comp (continuous_const.mul hφ)
  set K := P '' Icc 0 1
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn hP.continuousOn
  set K' := Metric.cthickening 1 K
  have hK' : IsCompact K' := hK.cthickening
  have hKK' : K ⊆ K' := Metric.self_subset_cthickening K
  have hPK : ∀ t ∈ Icc (0 : ℝ) 1, P t ∈ K' := fun t ht => hKK' (mem_image_of_mem P ht)
  obtain ⟨M, hM⟩ := hK'.exists_bound_of_continuousOn hE.continuousOn
  have hEM : ∀ x ∈ K', E x ≤ M := fun x hx => (le_abs_self _).trans (hM x hx)
  have hM0 : 0 ≤ M := (Real.exp_pos _).le.trans (hEM _ (hPK 0 ⟨le_rfl, zero_le_one⟩))
  set A := ∫⁻ t in Icc (0 : ℝ) 1, ENNReal.ofReal ‖deriv P t‖
  have hA : A ≠ ∞ := hP.lintegral_norm_deriv_lt_top.ne
  set Ar := A.toReal
  have hAr : 0 ≤ Ar := ENNReal.toReal_nonneg
  set ω := δ / (2 * (Ar + 1))
  have hω : 0 < ω := by positivity
  have hωA : ω * Ar ≤ δ / 2 := by
    have : ω * (Ar + 1) = δ / 2 := by simp only [ω]; field_simp
    nlinarith
  obtain ⟨η, hη, hηE⟩ := Metric.uniformContinuousOn_iff.1
    (hK'.uniformContinuousOn_of_continuous hE.continuousOn) (ω / 2) (by positivity)
  set η' := min η 1
  have hη' : 0 < η' := lt_min hη one_pos
  obtain ⟨τ, hτ, hτP⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hP.continuousOn) (η' / 4) (by positivity)
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hτ
  set t : ℕ → ℝ := fun i => i / ((N : ℝ) + 1)
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have ht_mono : Monotone t := fun i j hij => by
    simp only [t]; gcongr
  have ht_mem : ∀ i, i ≤ N + 1 → t i ∈ Icc (0 : ℝ) 1 := fun i hi => by
    refine ⟨by positivity, ?_⟩
    rw [div_le_one hN1]; exact_mod_cast hi
  have ht0 : t 0 = 0 := by simp [t]
  have ht1 : t (N + 1) = 1 := by simp only [t]; push_cast; exact div_self hN1.ne'
  have ht_step : ∀ i, t (i + 1) - t i = 1 / ((N : ℝ) + 1) := fun i => by
    simp only [t]; push_cast; ring
  set ρ := min (η' / 4) (δ / (4 * ((N : ℝ) + 1) * (M + ω)))
  have hρ : 0 < ρ := lt_min (by positivity) (by positivity)
  have hv : ∀ i : ℕ, ∃ q : ℂ, (i = 0 → q = z) ∧ (i = N + 1 → q = w) ∧
      (1 ≤ i → i ≤ N → q ∈ C) ∧ (i ≤ N + 1 → ‖q - P (t i)‖ < ρ) := by
    intro i
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · exact ⟨z, fun _ => rfl, fun h => absurd h (by omega), fun h => absurd h (by omega),
        fun _ => by simp [ht0, hP.source, hρ]⟩
    by_cases hiN : i ≤ N
    · obtain ⟨q, hq, hq'⟩ := hC _ (hPS _ (ht_mem i (by omega))) ρ hρ
      exact ⟨q, fun h => absurd h (by omega), fun h => absurd h (by omega), fun _ _ => hq,
        fun _ => hq'⟩
    · by_cases hiN1 : i = N + 1
      · subst hiN1
        exact ⟨w, fun h => absurd h (by omega), fun _ => rfl, fun _ h => absurd h hiN,
          fun _ => by simp [ht1, hP.target, hρ]⟩
      · exact ⟨0, fun h => absurd h (by omega), fun h => absurd h hiN1, fun _ h => absurd h hiN,
          fun h => absurd h (by omega)⟩
  choose v hv0 hvN hvC hvP using hv
  refine ⟨N, v, hv0 0 rfl, hvN _ rfl, hvC, ?_⟩
  -- the bound on one segment
  set g : ℝ → ℝ≥0∞ := fun s => lenDens ξ φ P s + ENNReal.ofReal ω * ENNReal.ofReal ‖deriv P s‖
  have hPstep : ∀ i, i ≤ N → ∀ s ∈ Icc (t i) (t (i + 1)), dist (P s) (P (t i)) < η' / 4 := by
    intro i hi s hs
    have hsI : s ∈ Icc (0 : ℝ) 1 :=
      ⟨(ht_mem i (by omega)).1.trans hs.1, hs.2.trans (ht_mem (i + 1) (by omega)).2⟩
    refine hτP s hsI _ (ht_mem i (by omega)) ?_
    rw [Real.dist_eq, abs_of_nonneg (by linarith [hs.1])]
    linarith [hs.2, ht_step i]
  have hseg : ∀ i, i ≤ N → segCost ξ φ (v i) (v (i + 1)) ≤
      (∫⁻ s in Ioc (t i) (t (i + 1)), g s) + ENNReal.ofReal (2 * ρ * (M + ω)) := by
    intro i hi
    have hti := ht_mem i (by omega)
    have hti1 := ht_mem (i + 1) (by omega)
    set B := E (P (t i)) + ω / 2
    have hB0 : 0 ≤ B := by positivity
    have hBM : B ≤ M + ω := by
      show E (P (t i)) + ω / 2 ≤ M + ω; linarith [hEM _ (hPK _ hti)]
    have hΔP : ‖P (t (i + 1)) - P (t i)‖ < η' / 4 := by
      rw [← dist_eq_norm]; exact hPstep i hi _ ⟨ht_mono (Nat.le_succ i), le_rfl⟩
    have h1 := hvP i (by omega)
    have h2 := hvP (i + 1) (by omega)
    have hΔv : ‖v (i + 1) - v i‖ ≤ ‖P (t (i + 1)) - P (t i)‖ + 2 * ρ := by
      have := norm_sub_le_norm_sub_add_norm_sub (v (i + 1)) (P (t (i + 1))) (v i)
      have h3 := norm_sub_le_norm_sub_add_norm_sub (P (t (i + 1))) (P (t i)) (v i)
      rw [norm_sub_rev (P (t i)) (v i)] at h3
      linarith
    have hρη : ρ ≤ η' / 4 := min_le_left _ _
    have hball : ∀ x ∈ Metric.closedBall (v i) ‖v (i + 1) - v i‖, E x ≤ B := by
      intro x hx
      have hxd : dist x (P (t i)) < η' := by
        have := dist_triangle x (v i) (P (t i))
        rw [Metric.mem_closedBall] at hx
        rw [dist_eq_norm (v i)] at this
        linarith
      have hxK : x ∈ K' := Metric.mem_cthickening_of_dist_le x (P (t i)) 1 K
        (mem_image_of_mem P hti) (hxd.le.trans (min_le_right _ _))
      have := hηE x hxK _ (hPK _ hti) (hxd.trans_le (min_le_left _ _))
      rw [Real.dist_eq, abs_lt] at this
      simp only [B]; linarith
    calc segCost ξ φ (v i) (v (i + 1)) ≤ ENNReal.ofReal (B * ‖v (i + 1) - v i‖) :=
          segCost_le hball
      _ ≤ ENNReal.ofReal (B * ‖P (t (i + 1)) - P (t i)‖) +
          ENNReal.ofReal (2 * ρ * (M + ω)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          nlinarith
      _ ≤ (∫⁻ s in Ioc (t i) (t (i + 1)), g s) + ENNReal.ofReal (2 * ρ * (M + ω)) := by
          refine add_le_add_left ?_ _
          rw [setLIntegral_congr Ioc_ae_eq_Icc, ENNReal.ofReal_mul hB0]
          calc ENNReal.ofReal B * ENNReal.ofReal ‖P (t (i + 1)) - P (t i)‖
              ≤ ENNReal.ofReal B * ∫⁻ s in Icc (t i) (t (i + 1)), ENNReal.ofReal ‖deriv P s‖ :=
                mul_le_mul_right (hP.ofReal_norm_sub_le hti.1 (ht_mono (Nat.le_succ i))
                  hti1.2) _
            _ = ∫⁻ s in Icc (t i) (t (i + 1)), ENNReal.ofReal B * ENNReal.ofReal ‖deriv P s‖ :=
                (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
            _ ≤ ∫⁻ s in Icc (t i) (t (i + 1)), g s := by
                refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
                have hsI : s ∈ Icc (0 : ℝ) 1 := ⟨hti.1.trans hs.1, hs.2.trans hti1.2⟩
                have hd := hηE _ (hPK _ hti) _ (hPK _ hsI)
                  ((by rw [dist_comm]; exact hPstep i hi s hs :
                    dist (P (t i)) (P s) < η' / 4).trans_le
                    ((by linarith : η' / 4 ≤ η').trans (min_le_left _ _)))
                rw [Real.dist_eq, abs_lt] at hd
                simp only [g, lenDens, ← ENNReal.ofReal_mul hB0,
                  ← ENNReal.ofReal_mul hω.le]
                rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
                refine ENNReal.ofReal_le_ofReal ?_
                have : B ≤ E (P s) + ω := by simp only [B]; linarith
                have hn := norm_nonneg (deriv P s)
                simp only [E] at this
                nlinarith
  -- summing up
  have hsum := Finset.sum_le_sum fun i (hi : i ∈ Finset.range (N + 1)) =>
    hseg i (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
  refine hsum.trans ?_
  rw [Finset.sum_add_distrib, sum_setLIntegral_Ioc g t ht_mono, ht0, ht1, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul]
  have hg : ∫⁻ s in Ioc (0 : ℝ) 1, g s ≤ lfppLen ξ φ P + ENNReal.ofReal (δ / 2) := by
    refine (lintegral_mono_set Ioc_subset_Icc_self).trans ?_
    simp only [g]
    rw [lintegral_add_right _ ((measurable_deriv P).norm.ennreal_ofReal.const_mul _),
      lintegral_const_mul _ (measurable_deriv P).norm.ennreal_ofReal, ← lfppLen_eq]
    refine add_le_add_right ?_ _
    rw [show (∫⁻ a in Icc (0 : ℝ) 1, ENNReal.ofReal ‖deriv P a‖) = ENNReal.ofReal Ar from
      (ENNReal.ofReal_toReal hA).symm, ← ENNReal.ofReal_mul hω.le]
    exact ENNReal.ofReal_le_ofReal hωA
  have hρ' : ((N + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (2 * ρ * (M + ω)) ≤
      ENNReal.ofReal (δ / 2) := by
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hρδ : ρ ≤ δ / (4 * ((N : ℝ) + 1) * (M + ω)) := min_le_right _ _
    rw [le_div_iff₀ (by positivity)] at hρδ
    push_cast
    nlinarith
  calc (∫⁻ s in Ioc (0 : ℝ) 1, g s) + ((N + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (2 * ρ * (M + ω))
      ≤ lfppLen ξ φ P + ENNReal.ofReal (δ / 2) + ENNReal.ofReal (δ / 2) := add_le_add hg hρ'
    _ = lfppLen ξ φ P + ENNReal.ofReal δ := by
      rw [add_assoc, ← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]

end LFPP
end LQGMetric
