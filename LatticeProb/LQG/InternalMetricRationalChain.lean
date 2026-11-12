import Mathlib
import LatticeProb.LQG.LQGMetricMeasurable

/-!
# Rational chains along paths of a Euclidean length metric

Let `D` be a Euclidean length metric on `ℂ`, `U` an open set and `P` a path from `x` to `y` with range in `U`.
For every `ε > 0` there are a rational radius `ρ > 0` and a chain `x = z₀, z₁, …, z_m = y` whose interior points
`z₁, …, z_{m-1}` have rational real and imaginary parts, such that for every step

* the Euclidean ball `B(z_i, ρ)` lies in `U`,
* the step length `D(z_i, z_{i+1})` is strictly smaller than the minimum of `D(z_i, ·)` on the circle `∂B(z_i, ρ)`,

and the `D`-length `∑ D(z_i, z_{i+1})` of the chain is at most `len(P; D) + ε`
(`IsEuclideanLengthMetric.exists_ratChain_le_pathLength`).

This is the completeness half of a countable chain formula for the internal metric `D(x, y; U)`: such chains
involve only countably many values of `D`, and conversely (by the length property and the intermediate value
theorem) each chain of this kind can be followed by paths in `U` of total `D`-length close to the chain length.

The proof: the range of `P` is compact in `U`, so a rational `ρ` with `B(P(t), 2ρ) ⊆ U` exists; by compactness,
`D(z, ·)` is bounded below on `∂B(z, ρ)` by some `c > 0` uniformly for `z` within distance `ρ` of the range of `P`;
a uniform partition of `[0, 1]` makes the steps `D(P(t_i), P(t_{i+1}))` smaller than `c / 4`; and the interior
partition points are moved to nearby rational points.
-/

namespace LatticeProb.LQG

open Set Metric
open scoped ENNReal

/-- The points of `ℂ` with rational real and imaginary parts are dense. -/
theorem denseRange_ratComplex : DenseRange (fun q : ℚ × ℚ => (⟨q.1, q.2⟩ : ℂ)) := by
  have h1 : DenseRange (fun q : ℚ × ℚ => ((q.1 : ℝ), (q.2 : ℝ))) :=
    Rat.denseRange_cast.prodMap Rat.denseRange_cast
  have h2 : DenseRange (Complex.equivRealProdCLM.symm : ℝ × ℝ → ℂ) :=
    Complex.equivRealProdCLM.symm.surjective.denseRange
  exact h2.comp h1 Complex.equivRealProdCLM.symm.continuous

/-- A Euclidean length metric is nonnegative. -/
theorem IsEuclideanLengthMetric.apply_nonneg {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (z w : ℂ) : 0 ≤ D z w := by
  have h := hD.triangle z w z
  rw [hD.self_eq_zero, hD.symm w z] at h
  linarith

/-- A Euclidean length metric is jointly Euclidean-continuous. -/
theorem IsEuclideanLengthMetric.continuous_uncurry {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) : Continuous fun p : ℂ × ℂ => D p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨x, y⟩
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ₁, hδ₁, H₁⟩ :=
    Metric.continuousAt_iff.1 (hD.continuous_left x).continuousAt (ε / 2) (half_pos hε)
  obtain ⟨δ₂, hδ₂, H₂⟩ :=
    Metric.continuousAt_iff.1 (hD.continuous_left y).continuousAt (ε / 2) (half_pos hε)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun {p} hp => ?_⟩
  rw [Prod.dist_eq, max_lt_iff] at hp
  have h1 := H₁ (hp.1.trans_le (min_le_left _ _))
  have h2 := H₂ (hp.2.trans_le (min_le_right _ _))
  simp only at h1 h2
  rw [hD.self_eq_zero, Real.dist_eq, sub_zero] at h1 h2
  have a1 := hD.triangle p.1 x p.2
  have a2 := hD.triangle x y p.2
  have a3 := hD.triangle x p.1 y
  have a4 := hD.triangle p.1 p.2 y
  have s1 := hD.symm x p.1
  have s2 := hD.symm y p.2
  have n1 := hD.apply_nonneg p.1 x
  have n2 := hD.apply_nonneg p.2 y
  rw [Real.dist_eq, abs_lt]
  rw [abs_lt] at h1 h2
  constructor <;> linarith [h1.2, h2.2]

/-- **Rational chains along a path** (completeness half of the chain formula for the internal metric). For a
Euclidean length metric `D`, an open set `U`, a path `P` from `x` to `y` with range in `U` and `ε > 0`, there are
`m > 0`, a rational radius `ρ > 0` and a chain `z 0 = x, …, z m = y` with rational interior points such that for
every step `i < m` the ball `B(z i, ρ)` lies in `U` and `D(z i, z (i + 1))` is strictly smaller than
`inf_θ D(z i, z i + ρ e^{iθ})`, and `∑_{i < m} D(z i, z (i + 1)) ≤ len(P; D) + ε`. -/
theorem IsEuclideanLengthMetric.exists_ratChain_le_pathLength {D : ℂ → ℂ → ℝ}
    (hD : IsEuclideanLengthMetric D) {U : Set ℂ} (hU : IsOpen U) {x y : ℂ} (P : Path x y)
    (hPU : ∀ t, P t ∈ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : ℕ) (z : ℕ → ℂ) (ρ : ℝ), 0 < m ∧ z 0 = x ∧ z m = y ∧
      (∀ i, 0 < i → i < m → ∃ q : ℚ × ℚ, z i = ⟨q.1, q.2⟩) ∧
      (∃ q : ℚ, (q : ℝ) = ρ) ∧ 0 < ρ ∧
      (∀ i < m, ball (z i) ρ ⊆ U ∧
        ENNReal.ofReal (D (z i) (z (i + 1))) <
          ⨅ θ : ℝ, ENNReal.ofReal (D (z i) (z i + (ρ : ℂ) * Complex.exp (θ * Complex.I)))) ∧
      ∑ i ∈ Finset.range m, ENNReal.ofReal (D (z i) (z (i + 1))) ≤
        pathLength D P + ENNReal.ofReal ε := by
  classical
  have hDc := hD.continuous_uncurry
  set p : ℝ → ℂ := ⇑P.extend with hp_def
  have hpc : Continuous p := P.extend.continuous
  set K : Set ℂ := range P with hK_def
  have hK : IsCompact K := isCompact_range P.continuous
  have hKU : K ⊆ U := by rintro _ ⟨t, rfl⟩; exact hPU t
  have hpK : ∀ t, p t ∈ K := fun t => by rw [hK_def, ← P.extend_range]; exact mem_range_self t
  -- a rational radius `ρ` with `B(P(t), 2ρ) ⊆ U`
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_thickening_subset_open hU hKU
  obtain ⟨ρq, hρ0, hρδ⟩ := exists_rat_btwn (half_pos hδ)
  set ρ : ℝ := (ρq : ℝ) with hρ_def
  -- a uniform lower bound `c` of `D(z, ·)` on `∂B(z, ρ)`, for `z` within `ρ` of the range of `P`
  set K' : Set ℂ := cthickening ρ K with hK'_def
  have hK' : IsCompact K' := hK.cthickening
  set A : Set (ℂ × ℂ) := K' ×ˢ sphere (0 : ℂ) ρ with hA_def
  have hA : IsCompact A := hK'.prod (isCompact_sphere 0 ρ)
  have hxK' : x ∈ K' := self_subset_cthickening K ⟨0, P.source⟩
  have hAne : A.Nonempty := ⟨(x, (ρ : ℂ)), hxK', by
    rw [mem_sphere_zero_iff_norm, Complex.norm_real, Real.norm_of_nonneg hρ0.le]⟩
  have hg : ContinuousOn (fun q : ℂ × ℂ => D q.1 (q.1 + q.2)) A :=
    (hDc.comp (continuous_fst.prodMk (continuous_fst.add continuous_snd))).continuousOn
  obtain ⟨q0, hq0A, hq0min⟩ := hA.exists_isMinOn hAne hg
  set c : ℝ := D q0.1 (q0.1 + q0.2) with hc_def
  have hc : 0 < c := by
    rcases (hD.apply_nonneg q0.1 (q0.1 + q0.2)).lt_or_eq with h | h
    · exact h
    · exfalso
      have h0 := hD.eq_of_eq_zero _ _ h.symm
      have h2 : q0.2 = 0 := by linear_combination -h0
      have hn := hq0A.2
      rw [mem_sphere_zero_iff_norm, h2, norm_zero] at hn
      exact hρ0.ne' hn.symm
  have hcircle : ∀ z ∈ K', ∀ θ : ℝ, c ≤ D z (z + (ρ : ℂ) * Complex.exp (θ * Complex.I)) := by
    intro z hz θ
    refine isMinOn_iff.1 hq0min (z, (ρ : ℂ) * Complex.exp (θ * Complex.I)) ⟨hz, ?_⟩
    rw [mem_sphere_zero_iff_norm, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hρ0.le]
  -- uniform continuity of `(s, t) ↦ D(P(s), P(t))` on `[0, 1]²`
  have hf : Continuous (fun s : ℝ × ℝ => D (p s.1) (p s.2)) :=
    hDc.comp ((hpc.comp continuous_fst).prodMk (hpc.comp continuous_snd))
  have hcpt : IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have huc := hcpt.uniformContinuousOn_of_continuous hf.continuousOn
  obtain ⟨η, hη, Hη⟩ := Metric.uniformContinuousOn_iff.1 huc (c / 4) (by positivity)
  have hstep : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1, |s - t| < η → D (p s) (p t) < c / 4 := by
    intro s hs t ht hst
    have h := Hη (s, t) ⟨hs, ht⟩ (s, s) ⟨hs, hs⟩ (by
      rw [Prod.dist_eq, dist_self, max_lt_iff, Real.dist_eq, abs_sub_comm]; exact ⟨hη, hst⟩)
    simp only at h
    rw [hD.self_eq_zero, Real.dist_eq, sub_zero] at h
    exact (le_abs_self _).trans_lt h
  -- the uniform partition `t_i = i / N`
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hη
  set N : ℕ := n + 1 with hN_def
  have hNpos : (0 : ℝ) < N := by positivity
  have hNR : (N : ℝ) = n + 1 := by rw [hN_def]; push_cast; ring
  set u : ℕ → ℝ := fun i => min ((i : ℝ) / N) 1 with hu_def
  have hu : ∀ i, i ≤ N → u i = i / N := fun i hi =>
    min_eq_left ((div_le_one hNpos).2 (by exact_mod_cast hi))
  have humono : Monotone u := fun a b hab =>
    min_le_min_right _ (div_le_div_of_nonneg_right (by exact_mod_cast hab) hNpos.le)
  have humem : ∀ i, u i ∈ Icc (0 : ℝ) 1 := fun i =>
    ⟨le_min (by positivity) zero_le_one, min_le_right _ _⟩
  have hstepu : ∀ i < N, D (p (u i)) (p (u (i + 1))) < c / 4 := by
    intro i hi
    refine hstep _ (humem i) _ (humem (i + 1)) ?_
    rw [hu i hi.le, hu (i + 1) hi]
    push_cast
    rw [show (i : ℝ) / N - ((i : ℝ) + 1) / N = -(1 / N) by ring, abs_neg,
      abs_of_pos (by positivity), hNR]
    exact hn
  -- moving the interior partition points to nearby rational points
  set e : ℝ := min (c / 4) (ε / (2 * N)) with he_def
  have he : 0 < e := lt_min (by positivity) (by positivity)
  have hw : ∀ i : ℕ, ∃ w : ℂ, dist w (p (u i)) < ρ ∧ D (p (u i)) w < e ∧
      (0 < i → i < N → ∃ q : ℚ × ℚ, w = ⟨q.1, q.2⟩) ∧ (¬ (0 < i ∧ i < N) → w = p (u i)) := by
    intro i
    by_cases hi : 0 < i ∧ i < N
    · have hO : IsOpen (ball (p (u i)) ρ ∩ {v | D (p (u i)) v < e}) :=
        isOpen_ball.inter (isOpen_lt (hDc.comp (continuous_const.prodMk continuous_id))
          continuous_const)
      obtain ⟨q, hq⟩ := denseRange_ratComplex.exists_mem_open hO
        ⟨p (u i), mem_ball_self hρ0, by simp only [mem_ofPred_eq, hD.self_eq_zero]; exact he⟩
      exact ⟨_, hq.1, hq.2, fun _ _ => ⟨q, rfl⟩, fun h => absurd hi h⟩
    · refine ⟨p (u i), by rw [dist_self]; exact hρ0, by rw [hD.self_eq_zero]; exact he,
        fun h1 h2 => absurd ⟨h1, h2⟩ hi, fun _ => rfl⟩
  choose w hwρ hwe hwq hwp using hw
  have hw0 : w 0 = x := by
    rw [hwp 0 (fun h => lt_irrefl 0 h.1)]
    simp only [hu_def, CharP.cast_eq_zero, zero_div, zero_le_one, min_eq_left, hp_def,
      Path.extend_zero]
  have hwN : w N = y := by
    rw [hwp N (fun h => lt_irrefl N h.2), hu N le_rfl, div_self hNpos.ne', hp_def, Path.extend_one]
  have hwK' : ∀ i, w i ∈ K' := fun i =>
    mem_cthickening_of_dist_le (w i) (p (u i)) ρ K (hpK _) (hwρ i).le
  refine ⟨N, w, ρ, Nat.succ_pos n, hw0, hwN, hwq, ⟨ρq, rfl⟩, hρ0, fun i hi => ⟨?_, ?_⟩, ?_⟩
  · -- `B(w i, ρ) ⊆ U`
    intro v hv
    apply hδU
    rw [mem_thickening_iff]
    refine ⟨p (u i), hpK _, ?_⟩
    have := dist_triangle v (w i) (p (u i))
    have := hwρ i
    rw [mem_ball] at hv
    linarith
  · -- the step is shorter than the circle minimum
    have hlt : D (w i) (w (i + 1)) < c := by
      have t1 := hD.triangle (w i) (p (u i)) (w (i + 1))
      have t2 := hD.triangle (p (u i)) (p (u (i + 1))) (w (i + 1))
      have s1 := hD.symm (w i) (p (u i))
      have s2 := hD.symm (p (u (i + 1))) (w (i + 1))
      have e1 := hwe i
      have e2 := hwe (i + 1)
      have e3 : e ≤ c / 4 := min_le_left _ _
      have := hstepu i hi
      linarith
    refine ((ENNReal.ofReal_lt_ofReal_iff hc).2 hlt).trans_le (le_iInf fun θ => ?_)
    exact ENNReal.ofReal_le_ofReal (hcircle _ (hwK' i) θ)
  · -- the chain length
    have hterm : ∀ i ∈ Finset.range N, ENNReal.ofReal (D (w i) (w (i + 1))) ≤
        ENNReal.ofReal (D (p (u (i + 1))) (p (u i))) +
          ENNReal.ofReal (D (p (u i)) (w i) + D (p (u (i + 1))) (w (i + 1))) := by
      intro i _
      rw [← ENNReal.ofReal_add (hD.apply_nonneg _ _)
        (add_nonneg (hD.apply_nonneg _ _) (hD.apply_nonneg _ _))]
      apply ENNReal.ofReal_le_ofReal
      have t1 := hD.triangle (w i) (p (u i)) (w (i + 1))
      have t2 := hD.triangle (p (u i)) (p (u (i + 1))) (w (i + 1))
      have s1 := hD.symm (w i) (p (u i))
      have s2 := hD.symm (p (u (i + 1))) (p (u i))
      linarith
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_add_distrib]
    refine add_le_add ?_ ?_
    · show _ ≤ curveLength D P.extend 0 1
      exact le_iSup_of_le
        (⟨N, ⟨u, humono, humem⟩⟩ : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc (0 : ℝ) 1}) le_rfl
    · rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ =>
        add_nonneg (hD.apply_nonneg _ _) (hD.apply_nonneg _ _))]
      apply ENNReal.ofReal_le_ofReal
      calc ∑ i ∈ Finset.range N, (D (p (u i)) (w i) + D (p (u (i + 1))) (w (i + 1)))
          ≤ ∑ _i ∈ Finset.range N, 2 * e :=
            Finset.sum_le_sum fun i _ => by linarith [hwe i, hwe (i + 1)]
        _ = N * (2 * e) := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        _ ≤ N * (2 * (ε / (2 * N))) := by
            gcongr
            exact min_le_right _ _
        _ = ε := by field_simp

end LatticeProb.LQG
