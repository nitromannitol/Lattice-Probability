/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Limit.UniformGridOscillation at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Limit.GridModulusProbability
import LatticeProb.Bonanno.ReflectedGMS.Limit.GridStoppingIncrement

/-!
# Uniform small-time oscillations on a deterministic grid

The quantitative finite-grid modulus estimate is made uniform over every
integer lag whose physical duration is below one fixed positive window.
-/

-- Merged from `ReflectedGMS/Limit/GridModulusBracket.lean` (Packet C, 2026-09-18); names unchanged.
section Merged_GridModulusBracket

/- The actual bracket estimate supplies every short-gap term in the finite-grid
modulus bound. The large-single-jump term is retained explicitly. -/
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators

namespace ReflectedGMS.MartingaleLimit

variable {Ω : Type*} {m : MeasurableSpace Ω}

theorem grid_modulus_probability_le_of_linear_bracket_error
    {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Filtration ℝ≥0 m} {M B : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M F P)
    (hC : Martingale (fun t ω => M t ω * M t ω - B t ω) F P)
    (d : ℝ≥0) {ε b : ℝ} (hε : 0 < ε) (hb : 0 ≤ b)
    (N L K : ℕ) (hK : 0 < K)
    (hrM : ∀ᵐ ω ∂P, IsRightContinuous (fun t => M t ω))
    (hrC : ∀ᵐ ω ∂P,
      IsRightContinuous (fun t => M t ω * M t ω - B t ω))
    (h2T : MemLp (M ((N : ℝ≥0) * d)) 2 P)
    {v : ℝ} (hv : 0 ≤ v) {R : Ω → ℝ} (hR : Integrable R P)
    (herror : ∀ᵐ ω ∂P, ∀ t ≤ (N : ℝ≥0) * d,
      |B t ω - v * (t : ℝ)| ≤ R ω) :
    P {ω | ∃ i j : ℕ, i ≤ j ∧ j ≤ N ∧ j - i ≤ L ∧
        4 * (ε + b) < |M ((j : ℝ≥0) * d) ω - M ((i : ℝ≥0) * d) ω|} ≤
      P {ω | ∃ n < N,
        b < |M (((n + 1 : ℕ) : ℝ≥0) * d) ω - M ((n : ℝ≥0) * d) ω|} +
      ENNReal.ofReal
        ((∫ ω, (M ((N : ℝ≥0) * d) ω) ^ 2 ∂P) / (ε ^ 2 * (K : ℝ))) +
      (K : ℝ≥0∞) * ENNReal.ofReal
        ((v * ((L : ℝ≥0) * d : ℝ≥0) + 2 * ∫ ω, R ω ∂P) / ε ^ 2) := by
  let grid : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * d
  have hgrid : Monotone grid := fun i j hij =>
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hij) (show 0 ≤ d from zero_le)
  let G : Filtration ℕ m :=
    { seq := fun i => F (grid i)
      mono' := fun _ _ hij => F.mono (hgrid hij)
      le' := fun i => F.le (grid i) }
  let X : ℕ → Ω → ℝ := fun i => M (grid i)
  let σ : ℕ → Ω → ℕ := greedyOscillationStop X ε N
  have hX : StronglyAdapted G X := fun i => hM.stronglyAdapted (grid i)
  have hσ : ∀ k, IsStoppingTime G (fun ω => (σ k ω : WithTop ℕ)) := fun k =>
    greedyOscillationStop_isStoppingTime hX N k
  let gapBound := ENNReal.ofReal
    ((v * ((L : ℝ≥0) * d : ℝ≥0) + 2 * ∫ ω, R ω ∂P) / ε ^ 2)
  have hgap (k : ℕ) :
      P {ω | σ (k + 1) ω < N ∧ σ (k + 1) ω ≤ σ k ω + L} ≤ gapBound := by
    have hstop := grid_stopping_short_gap_probability_le
      hM hC d (fun i => (le_rfl : G i ≤ F ((i : ℝ≥0) * d)))
      (hσ k) (hσ (k + 1)) N L
      (fun ω => greedyOscillationStop_mono_step X hε N k ω)
      (fun ω => greedyOscillationStop_le X ε N (k + 1) ω)
      hrM hrC h2T hv hR herror hε
    refine (measure_mono ?_).trans hstop
    intro ω hω
    refine ⟨hω.2, ?_⟩
    exact le_abs_sub_at_greedyOscillationStop_succ X hε N k ω hω.1
  have hsum :
      (∑ k ∈ Finset.range K,
        P {ω | σ (k + 1) ω < N ∧ σ (k + 1) ω ≤ σ k ω + L}) ≤
        (K : ℝ≥0∞) * gapBound := by
    calc
      _ ≤ ∑ _k ∈ Finset.range K, gapBound :=
        Finset.sum_le_sum fun k _ => hgap k
      _ = _ := by simp
  exact (grid_modulus_probability_le hM hC d hε hb N L K hK hrM hrC h2T).trans
    (add_le_add_right hsum _)

end ReflectedGMS.MartingaleLimit

end Merged_GridModulusBracket

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace ReflectedGMS.MartingaleLimit

variable {Ω : Type*} {m : MeasurableSpace Ω}

/-- Uniform terminal second moments, vanishing bracket-envelope means, and
vanishing maximal grid jumps imply a uniform small-time grid modulus bound.
The probability space is common to the whole martingale array. -/
theorem uniform_grid_oscillation_probability_le
    {P : Measure Ω} [IsProbabilityMeasure P]
    {F : ℕ → Filtration ℝ≥0 m} {M B : ℕ → ℝ≥0 → Ω → ℝ}
    (d : ℕ → ℝ≥0) (N : ℕ → ℕ)
    (hM : ∀ n, Martingale (M n) (F n) P)
    (hC : ∀ n,
      Martingale (fun t ω => M n t ω * M n t ω - B n t ω) (F n) P)
    (hrM : ∀ n, ∀ᵐ ω ∂P, IsRightContinuous (fun t => M n t ω))
    (hrC : ∀ n, ∀ᵐ ω ∂P,
      IsRightContinuous (fun t => M n t ω * M n t ω - B n t ω))
    (h2T : ∀ n, MemLp (M n ((N n : ℝ≥0) * d n)) 2 P)
    {C : ℝ}
    (hterminal : ∀ n, ∫ ω, (M n ((N n : ℝ≥0) * d n) ω) ^ 2 ∂P ≤ C)
    {v : ℝ} (hv : 0 ≤ v) {R : ℕ → Ω → ℝ}
    (hR : ∀ n, Integrable (R n) P)
    (herror : ∀ n, ∀ᵐ ω ∂P, ∀ t ≤ (N n : ℝ≥0) * d n,
      |B n t ω - v * (t : ℝ)| ≤ R n ω)
    (hRlim : Tendsto (fun n => ∫ ω, R n ω ∂P) atTop (𝓝 0))
    (hjump : ∀ b : ℝ, 0 < b → Tendsto (fun n =>
      P {ω | ∃ k < N n,
        b < |M n (((k + 1 : ℕ) : ℝ≥0) * d n) ω -
          M n ((k : ℝ≥0) * d n) ω|}) atTop (𝓝 0)) :
    ∀ η : ℝ, 0 < η → ∀ ρ : ℝ, 0 < ρ →
      ∃ δ : ℝ≥0, 0 < δ ∧ ∀ᶠ n in atTop, ∀ L : ℕ,
        (L : ℝ≥0) * d n ≤ δ →
        P {ω | ∃ i j : ℕ, i ≤ j ∧ j ≤ N n ∧ j - i ≤ L ∧
          η < |M n ((j : ℝ≥0) * d n) ω - M n ((i : ℝ≥0) * d n) ω|} ≤
          ENNReal.ofReal ρ := by
  intro η hη ρ hρ
  let ε : ℝ := η / 8
  have hε : 0 < ε := div_pos hη (by norm_num)
  have hC0 : 0 ≤ C := by
    exact (integral_nonneg fun ω => sq_nonneg (M 0 ((N 0 : ℝ≥0) * d 0) ω)).trans
      (hterminal 0)
  obtain ⟨K, hKlarge⟩ := exists_nat_gt (4 * C / (ε ^ 2 * ρ))
  have hquot_nonneg : 0 ≤ 4 * C / (ε ^ 2 * ρ) := by positivity
  have hK : 0 < K := by
    exact_mod_cast lt_of_le_of_lt hquot_nonneg hKlarge
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
  have hterminalBudget : C / (ε ^ 2 * (K : ℝ)) < ρ / 4 := by
    have hden : 0 < ε ^ 2 * ρ := mul_pos (sq_pos_of_pos hε) hρ
    have hlarge : 4 * C < (K : ℝ) * (ε ^ 2 * ρ) :=
      (div_lt_iff₀ hden).mp hKlarge
    rw [div_lt_iff₀ (mul_pos (sq_pos_of_pos hε) hKreal)]
    nlinarith
  let q : ℝ := ρ * ε ^ 2 / (16 * (K : ℝ))
  have hq : 0 < q := by
    dsimp [q]
    positivity
  let δr : ℝ := q / (v + 1)
  have hv1 : 0 < v + 1 := by linarith
  have hδr : 0 < δr := div_pos hq hv1
  let δ : ℝ≥0 := ⟨δr, hδr.le⟩
  refine ⟨δ, by exact_mod_cast hδr, ?_⟩
  have hslopeδ : v * δr ≤ q := by
    have hvdiv : v / (v + 1) ≤ 1 := (div_le_one hv1).2 (by linarith)
    calc
      v * δr = q * (v / (v + 1)) := by
        dsimp [δr]
        field_simp
        <;> ring
      _ ≤ q * 1 := mul_le_mul_of_nonneg_left hvdiv hq.le
      _ = q := mul_one q
  have hRsmall : ∀ᶠ n in atTop, (∫ ω, R n ω ∂P) < q :=
    (tendsto_order.1 hRlim).2 q hq
  have hjumpsmall : ∀ᶠ n in atTop,
      P {ω | ∃ k < N n,
        ε < |M n (((k + 1 : ℕ) : ℝ≥0) * d n) ω -
          M n ((k : ℝ≥0) * d n) ω|} < ENNReal.ofReal (ρ / 4) :=
    (tendsto_order.1 (hjump ε hε)).2 _ (ENNReal.ofReal_pos.2 (by positivity))
  filter_upwards [hRsmall, hjumpsmall] with n hnR hnjump
  intro L hLd
  have hRnonnegAE : ∀ᵐ ω ∂P, 0 ≤ R n ω := by
    filter_upwards [herror n] with ω hω
    exact (abs_nonneg (B n 0 ω - v * (0 : ℝ))).trans (hω 0 (by simp))
  have hRnonneg : 0 ≤ ∫ ω, R n ω ∂P := integral_nonneg_of_ae hRnonnegAE
  have hLdreal : ((((L : ℝ≥0) * d n : ℝ≥0) : ℝ)) ≤ δr := by
    exact_mod_cast hLd
  have hslope : v * (((L : ℝ≥0) * d n : ℝ≥0) : ℝ) ≤ q :=
    (mul_le_mul_of_nonneg_left hLdreal hv).trans hslopeδ
  have hgapReal : (K : ℝ) *
      ((v * (((L : ℝ≥0) * d n : ℝ≥0) : ℝ) +
        2 * ∫ ω, R n ω ∂P) / ε ^ 2) ≤ ρ / 2 := by
    have hnum : v * (((L : ℝ≥0) * d n : ℝ≥0) : ℝ) +
        2 * ∫ ω, R n ω ∂P < 3 * q := by nlinarith
    have hcalc : (K : ℝ) * (3 * q / ε ^ 2) = 3 * ρ / 16 := by
      dsimp [q]
      field_simp
      <;> ring
    calc
      (K : ℝ) * ((v * (((L : ℝ≥0) * d n : ℝ≥0) : ℝ) +
          2 * ∫ ω, R n ω ∂P) / ε ^ 2) ≤
          (K : ℝ) * (3 * q / ε ^ 2) := by
            gcongr
      _ = 3 * ρ / 16 := hcalc
      _ ≤ ρ / 2 := by linarith
  have hterm : ENNReal.ofReal
      ((∫ ω, (M n ((N n : ℝ≥0) * d n) ω) ^ 2 ∂P) /
        (ε ^ 2 * (K : ℝ))) ≤ ENNReal.ofReal (ρ / 4) := by
    apply ENNReal.ofReal_le_ofReal
    exact (div_le_div_of_nonneg_right (hterminal n)
      (mul_nonneg (sq_nonneg ε) (Nat.cast_nonneg K))).trans hterminalBudget.le
  have hgapNonneg : 0 ≤
      (v * (((L : ℝ≥0) * d n : ℝ≥0) : ℝ) +
        2 * ∫ ω, R n ω ∂P) / ε ^ 2 := by positivity
  have hgap : (K : ℝ≥0∞) * ENNReal.ofReal
      ((v * (((L : ℝ≥0) * d n : ℝ≥0) : ℝ) +
        2 * ∫ ω, R n ω ∂P) / ε ^ 2) ≤ ENNReal.ofReal (ρ / 2) := by
    rw [show (K : ℝ≥0∞) = ENNReal.ofReal (K : ℝ) by simp,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg K)]
    exact ENNReal.ofReal_le_ofReal hgapReal
  have hbound := grid_modulus_probability_le_of_linear_bracket_error
    (hM n) (hC n) (d n) hε hε.le (N n) L K hK
    (hrM n) (hrC n) (h2T n) hv (hR n) (herror n)
  have heta : 4 * (ε + ε) = η := by
    dsimp [ε]
    ring
  calc
    P {ω | ∃ i j : ℕ, i ≤ j ∧ j ≤ N n ∧ j - i ≤ L ∧
        η < |M n ((j : ℝ≥0) * d n) ω - M n ((i : ℝ≥0) * d n) ω|} ≤
        P {ω | ∃ k < N n,
          ε < |M n (((k + 1 : ℕ) : ℝ≥0) * d n) ω -
            M n ((k : ℝ≥0) * d n) ω|} +
        ENNReal.ofReal
          ((∫ ω, (M n ((N n : ℝ≥0) * d n) ω) ^ 2 ∂P) /
            (ε ^ 2 * (K : ℝ))) +
        (K : ℝ≥0∞) * ENNReal.ofReal
          ((v * (((L : ℝ≥0) * d n : ℝ≥0) : ℝ) +
            2 * ∫ ω, R n ω ∂P) / ε ^ 2) := by
              simpa only [heta] using hbound
    _ ≤ ENNReal.ofReal (ρ / 4) + ENNReal.ofReal (ρ / 4) +
        ENNReal.ofReal (ρ / 2) := add_le_add (add_le_add hnjump.le hterm) hgap
    _ = ENNReal.ofReal ρ := by
      rw [← ENNReal.ofReal_add (by positivity : 0 ≤ ρ / 4)
          (by positivity : 0 ≤ ρ / 4),
        ← ENNReal.ofReal_add (by positivity : 0 ≤ ρ / 4 + ρ / 4)
          (by positivity : 0 ≤ ρ / 2)]
      congr 1
      ring

end ReflectedGMS.MartingaleLimit
