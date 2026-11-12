import Mathlib
import LatticeProb.LQG.WeylChainLower

/-!
# Weighted chain sums of local internal metrics below the length of a path

Let `D` be a Euclidean length metric on `ℂ`, `f` a continuous function with `ξ f ≤ K`, and `E = e^{ξ f} · D` its
Weyl scaling (Gwynne-Miller, arXiv:1905.00383, (1.7)-(1.8)), assumed to be a Euclidean length metric with `E ≥ 0`. Let
`U` be open, `Q` dense, `δ > 0`, and `η` a modulus of continuity of `ξ f` at scale `δ`.

* `chain_step_le`: one link of a chain. If `p'` and `z` are within `δ / 4` of `p`, then for every `z'` the
  weighted local distance `e^{ξ f(z)} D(z, z'; B(z, δ) ∩ U)` is at most `e^{2η} E(p, p'; B(p, δ/4) ∩ U)` plus
  `e^K` times the two connector distances `D(p, z; B(p, δ/4) ∩ U)` and `D(p', z'; B(p', δ/4) ∩ U)`.
* `exists_chain_sum_le_pathLength`: for every path `P` in `U` from `x` to `y` and every `ε > 0` there is a chain
  `x = z₀, z₁, …, z_m = y` with `z₁, …, z_{m-1} ∈ Q` and
  `∑_{i < m} e^{ξ f(z_i)} D(z_i, z_{i+1}; B(z_i, δ) ∩ U) ≤ e^{2η} len(P; E) + ε`.

This is the lower half of the approximation of the internal metric of `E` on `U` by weighted chain sums of local
internal metrics of `D` (the upper half is `internalMetric_weylScaling_le_chain_sum`).
-/

namespace LatticeProb.LQG

open Set Filter Topology
open scoped ENNReal

/-- One link of a weighted chain: if `dist p' p` and `dist z p` are less than `δ / 4` and `η` bounds the oscillation
of `ξ f` at distance less than `δ`, then for every `z'`
`e^{ξ f(z)} D(z, z'; B(z, δ) ∩ U) ≤ e^{2η} E(p, p'; B(p, δ/4) ∩ U)`
`  + e^K (D(p, z; B(p, δ/4) ∩ U) + D(p', z'; B(p', δ/4) ∩ U))`. -/
theorem chain_step_le {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) (hE0 : ∀ x y, 0 ≤ E x y) {ξ K : ℝ} {f : ℂ → ℝ} (hf : Continuous f)
    (hK : ∀ z, ξ * f z ≤ K) (hscale : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y)
    {U : Set ℂ} {δ η : ℝ} (hη : ∀ a b, dist a b < δ → |ξ * f a - ξ * f b| ≤ η)
    {p p' z z' : ℂ} (hp' : dist p' p < δ / 4) (hz : dist z p < δ / 4) :
    ENNReal.ofReal (Real.exp (ξ * f z)) * internalMetric D (Metric.ball z δ ∩ U) z z' ≤
      ENNReal.ofReal (Real.exp (2 * η)) * internalMetric E (Metric.ball p (δ / 4) ∩ U) p p' +
        ENNReal.ofReal (Real.exp K) * (internalMetric D (Metric.ball p (δ / 4) ∩ U) p z +
          internalMetric D (Metric.ball p' (δ / 4) ∩ U) p' z') := by
  have hd0 : 0 ≤ dist z p := dist_nonneg
  have hWpV : Metric.ball p (δ / 4) ∩ U ⊆ Metric.ball z δ ∩ U := by
    rintro w ⟨hw, hwU⟩
    refine ⟨?_, hwU⟩
    rw [Metric.mem_ball] at hw ⊢
    calc dist w z ≤ dist w p + dist p z := dist_triangle w p z
      _ < δ := by rw [dist_comm p z]; linarith
  have hWp'V : Metric.ball p' (δ / 4) ∩ U ⊆ Metric.ball z δ ∩ U := by
    rintro w ⟨hw, hwU⟩
    refine ⟨?_, hwU⟩
    rw [Metric.mem_ball] at hw ⊢
    calc dist w z ≤ dist w p' + dist p' p + dist p z := dist_triangle4 w p' p z
      _ < δ := by rw [dist_comm p z]; linarith
  have htri : internalMetric D (Metric.ball z δ ∩ U) z z' ≤
      internalMetric D (Metric.ball p (δ / 4) ∩ U) p z + internalMetric D (Metric.ball p (δ / 4) ∩ U) p p' +
        internalMetric D (Metric.ball p' (δ / 4) ∩ U) p' z' := by
    calc internalMetric D (Metric.ball z δ ∩ U) z z'
        ≤ internalMetric D (Metric.ball z δ ∩ U) z p' + internalMetric D (Metric.ball z δ ∩ U) p' z' :=
          hD.internalMetric_triangle _ z p' z'
      _ ≤ (internalMetric D (Metric.ball z δ ∩ U) z p + internalMetric D (Metric.ball z δ ∩ U) p p') +
            internalMetric D (Metric.ball z δ ∩ U) p' z' :=
          add_le_add (hD.internalMetric_triangle _ z p p') le_rfl
      _ = (internalMetric D (Metric.ball z δ ∩ U) p z + internalMetric D (Metric.ball z δ ∩ U) p p') +
            internalMetric D (Metric.ball z δ ∩ U) p' z' := by
          rw [hD.internalMetric_symm _ z p]
      _ ≤ _ := add_le_add (add_le_add (internalMetric_anti D hWpV _ _) (internalMetric_anti D hWpV _ _))
          (internalMetric_anti D hWp'V _ _)
  have hB : internalMetric D (Metric.ball p (δ / 4) ∩ U) p p' ≤
      ENNReal.ofReal (Real.exp (-(ξ * f p - η))) * internalMetric E (Metric.ball p (δ / 4) ∩ U) p p' :=
    internalMetric_le_exp_neg_mul_of_weylScaling hD hE hE0 hf hK hscale (fun w hw => by
      have h := hη w p (lt_of_lt_of_le (Metric.mem_ball.mp hw.1) (by linarith))
      linarith [neg_abs_le (ξ * f w - ξ * f p)]) p p'
  have hzp : ξ * f z ≤ ξ * f p + η := by
    have h := hη z p (by linarith)
    linarith [le_abs_self (ξ * f z - ξ * f p)]
  have hexp1 : ENNReal.ofReal (Real.exp (ξ * f z)) * ENNReal.ofReal (Real.exp (-(ξ * f p - η))) ≤
      ENNReal.ofReal (Real.exp (2 * η)) := by
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by linarith))
  have hexpK : ENNReal.ofReal (Real.exp (ξ * f z)) ≤ ENNReal.ofReal (Real.exp K) :=
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (hK z))
  calc ENNReal.ofReal (Real.exp (ξ * f z)) * internalMetric D (Metric.ball z δ ∩ U) z z'
      ≤ ENNReal.ofReal (Real.exp (ξ * f z)) * (internalMetric D (Metric.ball p (δ / 4) ∩ U) p z +
          internalMetric D (Metric.ball p (δ / 4) ∩ U) p p' + internalMetric D (Metric.ball p' (δ / 4) ∩ U) p' z') :=
        mul_le_mul' le_rfl htri
    _ = ENNReal.ofReal (Real.exp (ξ * f z)) * internalMetric D (Metric.ball p (δ / 4) ∩ U) p p' +
          ENNReal.ofReal (Real.exp (ξ * f z)) * (internalMetric D (Metric.ball p (δ / 4) ∩ U) p z +
            internalMetric D (Metric.ball p' (δ / 4) ∩ U) p' z') := by ring
    _ ≤ _ := by
      refine add_le_add ?_ (mul_le_mul' hexpK le_rfl)
      calc _ ≤ ENNReal.ofReal (Real.exp (ξ * f z)) * (ENNReal.ofReal (Real.exp (-(ξ * f p - η))) *
              internalMetric E (Metric.ball p (δ / 4) ∩ U) p p') := mul_le_mul' le_rfl hB
        _ = (ENNReal.ofReal (Real.exp (ξ * f z)) * ENNReal.ofReal (Real.exp (-(ξ * f p - η)))) *
              internalMetric E (Metric.ball p (δ / 4) ∩ U) p p' := (mul_assoc _ _ _).symm
        _ ≤ _ := mul_le_mul' hexp1 le_rfl

/-- Lower half of the chain approximation: for a path `P` in an open set `U` from `x` to `y`, a dense set `Q`,
`δ > 0` with `|ξ f(a) - ξ f(b)| ≤ η` whenever `dist a b < δ`, and `ε > 0`, there is a chain
`x = z₀, z₁, …, z_m = y` with `z₁, …, z_{m-1} ∈ Q` and
`∑_{i < m} e^{ξ f(z_i)} D(z_i, z_{i+1}; B(z_i, δ) ∩ U) ≤ e^{2η} len(P; E) + ε`. -/
theorem exists_chain_sum_le_pathLength {D E : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    (hE : IsEuclideanLengthMetric E) (hE0 : ∀ x y, 0 ≤ E x y) {ξ K : ℝ} {f : ℂ → ℝ} (hf : Continuous f)
    (hK : ∀ z, ξ * f z ≤ K) (hscale : ∀ x y, ENNReal.ofReal (E x y) = weylScaling D ξ f x y)
    {U : Set ℂ} (hU : IsOpen U) {Q : Set ℂ} (hQ : Dense Q) {δ η : ℝ} (hδ : 0 < δ)
    (hη : ∀ a b, dist a b < δ → |ξ * f a - ξ * f b| ≤ η)
    {x y : ℂ} (P : Path x y) (hPU : ∀ t, P t ∈ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : ℕ) (z : ℕ → ℂ), z 0 = x ∧ z m = y ∧ (∀ i, 0 < i → i < m → z i ∈ Q) ∧
      ∑ i ∈ Finset.range m, ENNReal.ofReal (Real.exp (ξ * f (z i))) *
          internalMetric D (Metric.ball (z i) δ ∩ U) (z i) (z (i + 1)) ≤
        ENNReal.ofReal (Real.exp (2 * η)) * pathLength E P + ENNReal.ofReal ε := by
  have hD0 : ∀ a b, 0 ≤ D a b := euclid_D_nonneg hD
  have hδ4 : 0 < δ / 4 := by linarith
  have hext : ∀ t, P.extend t ∈ U := fun t => by
    simp only [Path.extend]; exact hPU _
  obtain ⟨m, hm, hpart⟩ := exists_partition_ball_of_path P hδ4
  have hm' : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  set p : ℕ → ℂ := fun j => P.extend ((j : ℝ) / m) with hp
  set τ : ℝ := ε / (2 * m * Real.exp K) with hτdef
  have hτ : 0 < τ := by positivity
  have hchoose : ∀ j : ℕ, ∃ w : ℂ, (j = 0 → w = x) ∧ (m ≤ j → w = y) ∧ (0 < j → j < m → w ∈ Q) ∧
      dist w (p j) < δ / 4 ∧ internalMetric D (Metric.ball (p j) (δ / 4) ∩ U) (p j) w < ENNReal.ofReal τ := by
    intro j
    have hWo : IsOpen (Metric.ball (p j) (δ / 4) ∩ U) := Metric.isOpen_ball.inter hU
    have hpW : p j ∈ Metric.ball (p j) (δ / 4) ∩ U := ⟨Metric.mem_ball_self hδ4, hext _⟩
    have hlt : internalMetric D (Metric.ball (p j) (δ / 4) ∩ U) (p j) (p j) < ENNReal.ofReal τ := by
      rw [hD.internalMetric_self_of_mem_open hD0 hWo hpW]; exact ENNReal.ofReal_pos.mpr hτ
    have hδp : dist (p j) (p j) < δ / 4 := by rw [dist_self]; exact hδ4
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · have hpx : p j = x := by subst hj0; simp [hp]
      exact ⟨p j, fun _ => hpx, fun _ => by omega, fun h _ => by omega, hδp, hlt⟩
    · by_cases hmj : m ≤ j
      · have hpy : p j = y := Path.extend_of_one_le P (by rw [one_le_div hm']; exact_mod_cast hmj)
        exact ⟨p j, fun _ => by omega, fun _ => hpy, fun _ _ => by omega, hδp, hlt⟩
      · have hn := (hD.continuousAt_internalMetric_self hD0 hWo hpW).preimage_mem_nhds (Iio_mem_nhds hlt)
        obtain ⟨w, hwQ, hwS, hwB⟩ :=
          hQ.inter_nhds_nonempty (Filter.inter_mem hn (Metric.ball_mem_nhds (p j) hδ4))
        exact ⟨w, fun _ => by omega, fun h => absurd h hmj, fun _ _ => hwQ, Metric.mem_ball.mp hwB, hwS⟩
  choose z hz0 hzm hzQ hzd hzc using hchoose
  refine ⟨m, z, hz0 0 rfl, hzm m le_rfl, fun i h0 h1 => hzQ i h0 h1, ?_⟩
  have hpi1 : ∀ i : ℕ, p (i + 1) = P.extend (((i : ℝ) + 1) / m) := fun i => by
    simp only [hp]; push_cast; rfl
  have hstep : ∀ i ∈ Finset.range m, ENNReal.ofReal (Real.exp (ξ * f (z i))) *
      internalMetric D (Metric.ball (z i) δ ∩ U) (z i) (z (i + 1)) ≤
        ENNReal.ofReal (Real.exp (2 * η)) * internalMetric E (Metric.ball (p i) (δ / 4) ∩ U)
          (P.extend ((i : ℝ) / m)) (P.extend (((i : ℝ) + 1) / m)) +
        ENNReal.ofReal (Real.exp K) * (ENNReal.ofReal τ + ENNReal.ofReal τ) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hp' : dist (p (i + 1)) (p i) < δ / 4 := by
      rw [hpi1]
      exact Metric.mem_ball.mp (hpart i hi' _ ⟨div_le_div_of_nonneg_right (by linarith) hm'.le, le_rfl⟩)
    refine (chain_step_le hD hE hE0 hf hK hscale (U := U) hη hp' (hzd i)).trans ?_
    refine add_le_add (le_of_eq ?_) (mul_le_mul' le_rfl (add_le_add (hzc i).le (hzc (i + 1)).le))
    rw [hpi1]
  have hW' : ∀ i < m, P.extend '' Icc ((i : ℝ) / m) (((i : ℝ) + 1) / m) ⊆ Metric.ball (p i) (δ / 4) ∩ U := by
    rintro i hi _ ⟨t, ht, rfl⟩
    exact ⟨hpart i hi t ht, hext t⟩
  have hconst : (m : ℝ≥0∞) * (ENNReal.ofReal (Real.exp K) * (ENNReal.ofReal τ + ENNReal.ofReal τ)) =
      ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_add hτ.le hτ.le, ← ENNReal.ofReal_mul (Real.exp_nonneg K), ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg m)]
    congr 1
    rw [hτdef]
    field_simp
    norm_num
  calc ∑ i ∈ Finset.range m, ENNReal.ofReal (Real.exp (ξ * f (z i))) *
          internalMetric D (Metric.ball (z i) δ ∩ U) (z i) (z (i + 1))
      ≤ ∑ i ∈ Finset.range m, (ENNReal.ofReal (Real.exp (2 * η)) * internalMetric E (Metric.ball (p i) (δ / 4) ∩ U)
          (P.extend ((i : ℝ) / m)) (P.extend (((i : ℝ) + 1) / m)) +
          ENNReal.ofReal (Real.exp K) * (ENNReal.ofReal τ + ENNReal.ofReal τ)) := Finset.sum_le_sum hstep
    _ = ENNReal.ofReal (Real.exp (2 * η)) * ∑ i ∈ Finset.range m, internalMetric E (Metric.ball (p i) (δ / 4) ∩ U)
          (P.extend ((i : ℝ) / m)) (P.extend (((i : ℝ) + 1) / m)) +
          (m : ℝ≥0∞) * (ENNReal.ofReal (Real.exp K) * (ENNReal.ofReal τ + ENNReal.ofReal τ)) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ ≤ ENNReal.ofReal (Real.exp (2 * η)) * pathLength E P + ENNReal.ofReal ε := by
        rw [hconst]
        exact add_le_add (mul_le_mul' le_rfl (sum_internalMetric_le_pathLength hE P hm _ hW')) le_rfl

end LatticeProb.LQG
