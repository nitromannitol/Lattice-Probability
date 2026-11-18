import LatticeProb.LQG.SingularApproximantOffOrigin
import LatticeProb.LQG.SingularApproximantOriginPower

/-!
# Ball power bounds for singular approximants on compact sets

Let `h = h₀ - α log |·|` with `0 ≤ α < Q`, and let `v_k`, `m_k` be the approximants of the
LQG measures of `h` and `h₀` at the dyadic scale `2^{-k}`. Suppose that the regular
approximants satisfy, on every compact set of centers, a ball bound `m_k(B(z, r)) ≤ C r^κ`
uniformly in `k` and in `0 < r ≤ 1`.

* Away from the singularity, `v_k` is at most `d^{-γα}` times `m_k` on every set whose points
  have modulus at least `d`.
* A finite covering by unit balls bounds `m_k(B(0, L))` uniformly in `k`; together with a
  power bound `A s^a` for `v_k(B(0, s))`, `s ≤ s₀`, this bounds `v_k(B(0, L))` uniformly in `k`
  and extends the origin bound to every `s ≤ L`.
* `lqgApprox_fieldCircleAverage_ball_le_rpow` then gives a power bound `K r^β` for
  `v_k(B(z, r))`, uniformly in `k`, for all centers in a compact set and all `0 < r ≤ 1`.

On a common event the origin bound holds by
`ae_exists_singular_approximant_origin_rpow_bound`, so the regular ball bound transfers to
the singular approximants almost surely.
-/

open MeasureTheory Filter Set Topology Metric
open scoped ENNReal

namespace LatticeProb.LQG

open LatticeProb.Gauss

/-- Away from the singularity the singular approximant is dominated by the regular one: on a
measurable set all of whose points have modulus at least `d > 0`, the singular approximant is
at most `d^{-γα}` times the regular approximant, when `γ α ≥ 0`. -/
theorem lqgApprox_fieldCircleAverage_le_of_norm_ge (γ α : ℝ) (hcirc : ℝ → ℂ → ℝ) {ε : ℝ}
    (hε : 0 < ε) (hγα : 0 ≤ γ * α) {d : ℝ} (hd : 0 < d) {S : Set ℂ} (hS : MeasurableSet S)
    (hSd : ∀ x ∈ S, d ≤ ‖x‖) :
    lqgApprox γ (fieldCircleAverage α hcirc) ε S ≤
      ENNReal.ofReal (d ^ (-(γ * α))) * lqgApprox γ hcirc ε S := by
  unfold lqgApprox
  rw [withDensity_apply _ hS, withDensity_apply _ hS,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact setLIntegral_mono_ae' hS (ae_of_all _ fun x hx =>
    approxDensity_fieldCircleAverage_le γ α hcirc hε hγα hd (hSd x hx))

/-- The singular approximant of `ball 0 L` is at most its mass on `ball 0 d` plus `d^{-γα}`
times the regular approximant of `ball 0 L`. -/
theorem lqgApprox_fieldCircleAverage_ball_zero_le (γ α : ℝ) (hcirc : ℝ → ℂ → ℝ) {ε : ℝ}
    (hε : 0 < ε) (hγα : 0 ≤ γ * α) {d L : ℝ} (hd : 0 < d) :
    lqgApprox γ (fieldCircleAverage α hcirc) ε (ball 0 L) ≤
      lqgApprox γ (fieldCircleAverage α hcirc) ε (ball 0 d) +
        ENNReal.ofReal (d ^ (-(γ * α))) * lqgApprox γ hcirc ε (ball 0 L) := by
  have hsub : ball (0 : ℂ) L ⊆ ball 0 d ∪ (ball 0 L \ ball 0 d) := by
    intro x hx
    by_cases h : x ∈ ball (0 : ℂ) d
    · exact Or.inl h
    · exact Or.inr ⟨hx, h⟩
  have hdiff : lqgApprox γ (fieldCircleAverage α hcirc) ε (ball 0 L \ ball 0 d) ≤
      ENNReal.ofReal (d ^ (-(γ * α))) * lqgApprox γ hcirc ε (ball 0 L) := by
    refine (lqgApprox_fieldCircleAverage_le_of_norm_ge γ α hcirc hε hγα hd
      (measurableSet_ball.diff measurableSet_ball) fun x hx => ?_).trans
      (mul_le_mul' le_rfl (measure_mono sdiff_subset))
    have h := hx.2
    rw [mem_ball_zero_iff, not_lt] at h
    exact h
  calc lqgApprox γ (fieldCircleAverage α hcirc) ε (ball 0 L)
      ≤ lqgApprox γ (fieldCircleAverage α hcirc) ε (ball 0 d ∪ (ball 0 L \ ball 0 d)) :=
        measure_mono hsub
    _ ≤ lqgApprox γ (fieldCircleAverage α hcirc) ε (ball 0 d) +
          lqgApprox γ (fieldCircleAverage α hcirc) ε (ball 0 L \ ball 0 d) :=
        measure_union_le _ _
    _ ≤ _ := add_le_add le_rfl hdiff

/-- A ball centered at the origin is covered by finitely many unit balls whose centers lie in
its closure. -/
theorem exists_finset_unit_ball_cover (L : ℝ) :
    ∃ t : Finset ℂ, (∀ x ∈ t, ‖x‖ ≤ L) ∧ ball (0 : ℂ) L ⊆ ⋃ x ∈ t, ball x 1 := by
  obtain ⟨t, ht, hcov⟩ := (isCompact_closedBall (0 : ℂ) L).elim_nhds_subcover
    (fun x => ball x 1) (fun x _ => ball_mem_nhds x one_pos)
  exact ⟨t, fun x hx => mem_closedBall_zero_iff.1 (ht x hx), ball_subset_closedBall.trans hcov⟩

/-- A bound `C` on the mass of unit balls with centers in `closedBall 0 L` bounds the mass of
`ball 0 L` by `card t · C` for a fixed finite cover `t`. -/
theorem measure_ball_zero_le_of_unit_ball_bound {μ : Measure ℂ} {L C : ℝ} {t : Finset ℂ}
    (ht : ∀ x ∈ t, ‖x‖ ≤ L) (hcov : ball (0 : ℂ) L ⊆ ⋃ x ∈ t, ball x 1)
    (hμ : ∀ z : ℂ, ‖z‖ ≤ L → μ (ball z 1) ≤ ENNReal.ofReal C) :
    μ (ball 0 L) ≤ ENNReal.ofReal (t.card * C) :=
  calc μ (ball 0 L) ≤ μ (⋃ x ∈ t, ball x 1) := measure_mono hcov
    _ ≤ ∑ x ∈ t, μ (ball x 1) := measure_biUnion_finset_le t _
    _ ≤ ∑ _x ∈ t, ENNReal.ofReal C := Finset.sum_le_sum fun x hx => hμ x (ht x hx)
    _ = ENNReal.ofReal (t.card * C) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
          ENNReal.ofReal_natCast]

/-- **Singular approximants from regular ball bounds (deterministic form).** Let `γ α ≥ 0`
and let `ε k > 0` be approximation scales. Suppose that the singular approximants satisfy
`A s^a` on `ball 0 s` for `0 < s ≤ s₀`, uniformly in `k`, and that for every `R` the regular
approximants satisfy `C r^κ` on all balls `ball z r` with `‖z‖ ≤ R`, `0 < r ≤ 1`, uniformly
in `k`. Then for every `R` the singular approximants satisfy a power bound `K r^β`, `β > 0`,
on the same balls, uniformly in `k`. -/
theorem lqgApprox_fieldCircleAverage_ball_le_rpow_of_origin_of_regular
    (γ α : ℝ) (hcirc : ℝ → ℂ → ℝ) {ε : ℕ → ℝ} (hε : ∀ k, 0 < ε k) (hγα : 0 ≤ γ * α)
    {a A s₀ : ℝ} (ha : 0 < a) (hA : 0 ≤ A) (hs₀ : 0 < s₀)
    (horig : ∀ k, ∀ s : ℝ, 0 < s → s ≤ s₀ →
      lqgApprox γ (fieldCircleAverage α hcirc) (ε k) (ball 0 s) ≤ ENNReal.ofReal (A * s ^ a))
    (hreg : ∀ R : ℝ, ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧ ∀ k, ∀ z : ℂ, ‖z‖ ≤ R →
      ∀ r : ℝ, 0 < r → r ≤ 1 →
        lqgApprox γ hcirc (ε k) (ball z r) ≤ ENNReal.ofReal (C * r ^ κ)) :
    ∀ R : ℝ, ∃ K β : ℝ, 0 < β ∧ ∀ k, ∀ z : ℂ, ‖z‖ ≤ R → ∀ r : ℝ, 0 < r → r ≤ 1 →
      lqgApprox γ (fieldCircleAverage α hcirc) (ε k) (ball z r) ≤
        ENNReal.ofReal (K * r ^ β) := by
  intro R
  have hRL : R ≤ max 3 (3 / 2 * R) := by
    rcases le_total 0 R with h | h
    · exact le_max_of_le_right (by linarith)
    · exact le_max_of_le_left (by linarith)
  obtain ⟨C, κ, hC, hκ, hm⟩ := hreg (max 3 (3 / 2 * R))
  obtain ⟨t, ht, hcov⟩ := exists_finset_unit_ball_cover (max 3 (3 / 2 * R))
  have hAs : 0 ≤ A * s₀ ^ a := mul_nonneg hA (Real.rpow_nonneg hs₀.le _)
  have htC : 0 ≤ s₀ ^ (-(γ * α)) * (t.card * C) :=
    mul_nonneg (Real.rpow_nonneg hs₀.le _) (mul_nonneg (Nat.cast_nonneg _) hC)
  have hmass : ∀ k, lqgApprox γ (fieldCircleAverage α hcirc) (ε k)
      (ball 0 (max 3 (3 / 2 * R))) ≤
        ENNReal.ofReal (A * s₀ ^ a + s₀ ^ (-(γ * α)) * (t.card * C)) := by
    intro k
    have hunit : ∀ z : ℂ, ‖z‖ ≤ max 3 (3 / 2 * R) →
        lqgApprox γ hcirc (ε k) (ball z 1) ≤ ENNReal.ofReal C := by
      intro z hz
      simpa using hm k z hz 1 one_pos le_rfl
    calc _ ≤ _ := lqgApprox_fieldCircleAverage_ball_zero_le γ α hcirc (hε k) hγα
          (L := max 3 (3 / 2 * R)) hs₀
      _ ≤ ENNReal.ofReal (A * s₀ ^ a) +
            ENNReal.ofReal (s₀ ^ (-(γ * α))) * ENNReal.ofReal (t.card * C) :=
          add_le_add (horig k s₀ hs₀ le_rfl)
            (mul_le_mul' le_rfl (measure_ball_zero_le_of_unit_ball_bound ht hcov hunit))
      _ = _ := by
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hs₀.le _), ← ENNReal.ofReal_add hAs htC]
  have hext := rpow_bound_extend_of_ball_mass_le
    (fun k => lqgApprox γ (fieldCircleAverage α hcirc) (ε k)) (0 : ℂ) ha.le
    (add_nonneg hAs htC) hs₀ horig hmass
  set B := max A ((A * s₀ ^ a + s₀ ^ (-(γ * α)) * (t.card * C)) / s₀ ^ a) with hB
  have hA' : 0 ≤ B := le_max_of_le_left hA
  refine ⟨max (B * 3 ^ a) ((B * (3 / 2) ^ a) ^ (1 - a / (a + γ * α)) *
      (2 ^ (γ * α) * C) ^ (a / (a + γ * α))), min a (κ * (a / (a + γ * α))),
    lt_min ha (mul_pos hκ (div_pos ha (by linarith))), ?_⟩
  intro k z hz r hr hr1
  exact lqgApprox_fieldCircleAverage_ball_le_rpow γ α hcirc (hε k) hγα (R := R) hA' hC ha
    (fun s hs hsL => hext k s hs hsL)
    (fun z hz r hr hr1 => hm k z (hz.trans hRL) r hr hr1) z hz r hr hr1

/-- **Singular approximants from regular ball bounds, almost surely.** Under the hypotheses of
`ae_exists_singular_approximant_origin_rpow_bound` with `0 ≤ α`, suppose that almost surely,
for every `R`, the regular dyadic approximants of the selected circle averages `c ω` satisfy a
ball bound `C s^κ` with `κ > 0` on all balls `ball z s` with `‖z‖ ≤ R`, `0 < s ≤ 1`, uniformly
in the level. Then almost surely, for every `R`, the approximants of the field with
logarithmic singularity `-α log |·|` satisfy a power bound `K s^β`, `β > 0`, on the same balls,
uniformly in the level. -/
theorem ae_singular_approximant_ball_rpow_bound_of_regular
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → LQGMetric.DistC} (hX : LQGMetric.IsNormalizedWPGFF X P)
    {hC : Ω → (ℂ → ℝ) → ℝ} {c : Ω → ℝ → ℂ → ℝ}
    (hG : IsWholePlaneGFF P hC c)
    (hc : ∀ ω, ContinuousOn (fun p : ℝ × ℂ => c ω p.1 p.2) (Ioi 0 ×ˢ univ))
    (heq : ∀ r, 0 < r → ∀ z, ∀ᵐ ω ∂P, c ω r z = LQGMetric.circleAvg (X ω) r z)
    {γ α δ r ρ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : 0 ≤ α) (hαQ : α < lqgQ γ)
    (hδ : 0 < δ) (hρ : ρ ∈ Ioo (0 : ℝ) 1) (hr : 0 < r) (hrρ : r < ρ)
    (hreg : ∀ᵐ ω ∂P, ∀ R : ℝ, ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧ ∀ k : ℕ, ∀ z : ℂ, ‖z‖ ≤ R →
      ∀ s : ℝ, 0 < s → s ≤ 1 →
        lqgApprox γ (c ω) (dyadicScale k) (ball z s) ≤ ENNReal.ofReal (C * s ^ κ)) :
    ∀ᵐ ω ∂P, ∀ R : ℝ, ∃ K β : ℝ, 0 < β ∧ ∀ k : ℕ, ∀ z : ℂ, ‖z‖ ≤ R →
      ∀ s : ℝ, 0 < s → s ≤ 1 →
        lqgApprox γ (fieldCircleAverage α (c ω)) (dyadicScale k) (ball z s) ≤
          ENNReal.ofReal (K * s ^ β) := by
  filter_upwards [ae_exists_singular_approximant_origin_rpow_bound hX hG hc heq hγ hγ2 hαQ
    hδ hρ hr hrρ, hreg] with ω hω hregω
  obtain ⟨a, A, s₀, ha, -, hA, hs₀, horig⟩ := hω
  exact lqgApprox_fieldCircleAverage_ball_le_rpow_of_origin_of_regular γ α (c ω)
    (fun k => by unfold dyadicScale; positivity) (mul_nonneg hγ.le hα) ha hA hs₀ horig hregω

end LatticeProb.LQG
