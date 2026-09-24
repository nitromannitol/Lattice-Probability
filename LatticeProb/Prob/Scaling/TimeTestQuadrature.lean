/- Uniform temporal quadrature bounds for compactly supported smooth tests.

Moved from Parking-Sharpness.
-/
import LatticeProb.Prob.Scaling.TimeTest
import LatticeProb.Prob.Scaling.TimeRiemannEstimate

open MeasureTheory
noncomputable section
namespace LatticeProb.Scaling.TimeTest
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Compact support gives one Lipschitz constant for every time slice. -/
theorem exists_uniform_time_lipschitz {ψ : ℝ × E → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) :
    ∃ L : NNReal, ∀ x : E, LipschitzWith L (fun s : ℝ => ψ (s, x)) := by
  have hdc := (contDiff_timeDeriv hψ).continuous
  have hds := hasCompactSupport_timeDeriv (hψ.differentiable (by simp)) hc
  obtain ⟨M, hM⟩ := hdc.norm.bddAbove_range_of_hasCompactSupport hds.norm
  refine ⟨⟨max M 0, le_max_right _ _⟩, fun x => ?_⟩
  apply lipschitzWith_of_nnnorm_deriv_le
    ((hψ.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp))
  intro s
  change |timeDeriv ψ (s, x)| ≤ max M 0
  exact (hM ⟨(s, x), rfl⟩).trans (le_max_left _ _)

/-- The right-endpoint quadrature error is uniform in the spatial variable. -/
theorem exists_time_quadrature_bound {ψ : ℝ × E → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (h : ℝ), 0 ≤ h → ∀ (N : ℕ) (x : E),
      |h * ∑ k ∈ Finset.range N, ψ ((((k + 1 : ℕ) : ℝ) * h), x) -
        ∫ s in (0 : ℝ)..(N : ℝ) * h, ψ (s, x)| ≤ (N : ℝ) * h * (L * h) := by
  obtain ⟨L, hL⟩ := exists_uniform_time_lipschitz hψ hc
  exact ⟨L, L.coe_nonneg, fun _ hh _ x =>
    TimeRiemannEstimate.abs_sum_sub_integral_le (hL x) hh _⟩

/-- Positive-time compact tests admit a uniform whole-line quadrature bound, with
both endpoint values zero. The terminal mesh point is chosen beyond the support. -/
theorem exists_positive_time_quadrature_bound_with_support {ψ : ℝ × E → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hpos : ∀ p ∈ tsupport ψ, 0 < p.1) :
    ∃ T C : ℝ, 0 < T ∧ 0 ≤ C ∧ (∀ p ∈ tsupport ψ, p.1 < T) ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      (∀ x, ψ (0, x) = 0) ∧ (∀ x, ψ ((⌈T / h⌉₊ : ℝ) * h, x) = 0) ∧
      ∀ x, |h * ∑ k ∈ Finset.range ⌈T / h⌉₊, ψ ((((k + 1 : ℕ) : ℝ) * h), x) -
        ∫ s : ℝ, ψ (s, x)| ≤ C * h := by
  obtain ⟨B, hB⟩ := hc.isCompact.exists_bound_of_continuousOn
    (f := fun p : ℝ × E => p.1) continuous_fst.continuousOn
  obtain ⟨L, hL, herr⟩ := exists_time_quadrature_bound hψ hc
  let T : ℝ := max B 0 + 1
  have hT : 0 < T := by dsimp [T]; linarith [le_max_right B 0]
  have hBT : B < T := by dsimp [T]; linarith [le_max_left B 0]
  refine ⟨T, (T + 1) * L, hT, mul_nonneg (by linarith) hL,
    (fun p hp => (le_abs_self p.1).trans_lt ((hB p hp).trans_lt hBT)), fun h hh hh1 => ?_⟩
  have hlow : T ≤ (⌈T / h⌉₊ : ℝ) * h :=
    (div_le_iff₀ hh).mp (Nat.le_ceil (T / h))
  have hupp : (⌈T / h⌉₊ : ℝ) * h ≤ T + h := by
    have he := Nat.ceil_lt_add_one (div_nonneg hT.le hh.le)
    have hm := (mul_lt_mul_of_pos_right he hh).le
    simpa only [add_mul, div_mul_cancel₀ _ hh.ne', one_mul] using hm
  have hzero : ∀ x, ψ (0, x) = 0 := by
    intro x
    by_contra hn
    have hp := hpos (0, x) (subset_tsupport ψ hn)
    exact (lt_irrefl 0) hp
  have hfinal : ∀ x, ψ ((⌈T / h⌉₊ : ℝ) * h, x) = 0 := by
    intro x
    by_contra hn
    have hb := hB _ (subset_tsupport ψ hn)
    have hv := le_abs_self ((⌈T / h⌉₊ : ℝ) * h)
    change |(⌈T / h⌉₊ : ℝ) * h| ≤ B at hb
    linarith
  refine ⟨hzero, hfinal, fun x => ?_⟩
  have heq : (∫ s in (0 : ℝ)..(⌈T / h⌉₊ : ℝ) * h, ψ (s, x)) =
      ∫ s : ℝ, ψ (s, x) := by
    rw [intervalIntegral.integral_of_le (hT.le.trans hlow)]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro s hs
    by_contra hn
    have hp := subset_tsupport ψ hn
    have ht := hpos (s, x) hp
    have hb := hB (s, x) hp
    change |s| ≤ B at hb
    apply hs
    exact ⟨ht, (le_abs_self s).trans (hb.trans (hBT.le.trans hlow))⟩
  have he := herr h hh.le ⌈T / h⌉₊ x
  rw [heq] at he
  refine he.trans ?_
  have hlen : (⌈T / h⌉₊ : ℝ) * h ≤ T + 1 := by linarith
  calc
    (⌈T / h⌉₊ : ℝ) * h * (L * h) ≤ (T + 1) * (L * h) :=
      mul_le_mul_of_nonneg_right hlen (mul_nonneg hL hh.le)
    _ = ((T + 1) * L) * h := by ring

/-- Whole-line temporal quadrature with zero boundary values. -/
theorem exists_positive_time_quadrature_bound {ψ : ℝ × E → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hpos : ∀ p ∈ tsupport ψ, 0 < p.1) :
    ∃ T C : ℝ, 0 < T ∧ 0 ≤ C ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      (∀ x, ψ (0, x) = 0) ∧ (∀ x, ψ ((⌈T / h⌉₊ : ℝ) * h, x) = 0) ∧
      ∀ x, |h * ∑ k ∈ Finset.range ⌈T / h⌉₊, ψ ((((k + 1 : ℕ) : ℝ) * h), x) -
        ∫ s : ℝ, ψ (s, x)| ≤ C * h := by
  obtain ⟨T, C, hT, hC, _, h⟩ := exists_positive_time_quadrature_bound_with_support hψ hc hpos
  exact ⟨T, C, hT, hC, h⟩

end LatticeProb.Scaling.TimeTest
