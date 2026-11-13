/-
The time Brownian motion on `ℝ ^ d` spends in a ball has an exponential tail.

For Brownian motion on `ℝ ^ d` with generator `Δ / (2 d)` started at `u` (presented as in
`LatticeProb.IsBrownianSpace`), the probability that it stays in the open ball of radius `r`
about `u` up to time `A r ^ 2` is at most `c₀ exp (- c₁ A)`, with `c₀` and `c₁` depending only on
the dimension.

The argument needs only the Markov property at deterministic times, in the form of the
independence of the increments of one coordinate.  Cut `[0, A r ^ 2]` into the `n = ⌊A⌋` windows
`[i r ^ 2, (i + 1) r ^ 2]`.  While the motion stays in the ball, the rescaled first coordinate
`√d (B · 0 - u 0)` moves by less than `2 √d r` over each window.  These `n` increments are
independent centred Gaussians of variance `r ^ 2`, so the chance that all of them are this small
is `q ^ n`, where `q` is the mass the standard Gaussian gives to `(-2 √d, 2 √d)` (Brownian
scaling).  Since `q < 1` and `n > A - 1`, `q ^ n ≤ q⁻¹ q ^ A`, which is the exponential tail.
-/
import Mathlib
import LatticeProb.Prob.BrownianExit

open MeasureTheory ProbabilityTheory Filter Set

open scoped ENNReal NNReal Topology

noncomputable section

namespace LatticeProb

/-- The standard Gaussian gives mass less than one to any interval `(-a, a)`: the half-line
`(a, ∞)` has positive Lebesgue measure, hence positive Gaussian mass. -/
theorem gaussianReal_Ioo_neg_lt_one (a : ℝ) : gaussianReal 0 1 (Ioo (-a) a) < 1 := by
  have hpos : gaussianReal 0 1 (Ioi a) ≠ 0 := by
    intro h
    have h' := gaussianReal_absolutelyContinuous' 0 one_ne_zero h
    simp at h'
  have hdisj : Disjoint (Ioo (-a) a) (Ioi a) :=
    Set.disjoint_left.2 fun x hx hx' => lt_asymm hx.2 hx'
  have hsum : gaussianReal 0 1 (Ioo (-a) a) + gaussianReal 0 1 (Ioi a) ≤ 1 := by
    rw [← measure_union hdisj measurableSet_Ioi]
    exact prob_le_one
  calc gaussianReal 0 1 (Ioo (-a) a)
      < gaussianReal 0 1 (Ioo (-a) a) + gaussianReal 0 1 (Ioi a) :=
        ENNReal.lt_add_right (measure_ne_top _ _) hpos
    _ ≤ 1 := hsum

/-- **Brownian scaling of an interval.**  A centred Gaussian of variance `r ^ 2` gives to the
interval `(-b r, b r)` the mass the standard Gaussian gives to `(-b, b)`. -/
theorem gaussianReal_Ioo_mul_eq (τ : ℝ≥0) {r : ℝ} (hr : 0 < r) (hτ : (τ : ℝ) = r ^ 2)
    (b : ℝ) : gaussianReal 0 τ (Ioo (-(b * r)) (b * r)) = gaussianReal 0 1 (Ioo (-b) b) := by
  have hmap : (gaussianReal 0 1).map (fun x : ℝ => r * x) = gaussianReal 0 τ := by
    rw [gaussianReal_map_const_mul, mul_zero, mul_one]
    congr 1
    exact NNReal.eq (by simp [hτ])
  rw [← hmap, Measure.map_apply (by fun_prop) measurableSet_Ioo]
  congr 1
  ext x
  simp only [mem_preimage, mem_Ioo]
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> nlinarith
  · rintro ⟨h1, h2⟩
    constructor <;> nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Small increments over consecutive windows.**  For a real Brownian motion `W`, the
probability that each of its first `n` increments over the windows `[i τ, (i + 1) τ]` is less
than `a` in absolute value is the `n`-th power of the mass the centred Gaussian of variance `τ`
gives to `(-a, a)`: the increments are independent with that law. -/
theorem measure_forall_abs_increment_lt (W : ℝ≥0 → Ω → ℝ) (hW : IsBrownianReal W P)
    (τ : ℝ≥0) (a : ℝ) (n : ℕ) :
    P {ω | ∀ i < n, |W (((i + 1 : ℕ) : ℝ≥0) * τ) ω - W ((i : ℝ≥0) * τ) ω| < a}
      = gaussianReal 0 τ (Ioo (-a) a) ^ n := by
  let X : ℕ → Ω → ℝ := fun i ω => W (((i + 1 : ℕ) : ℝ≥0) * τ) ω - W ((i : ℝ≥0) * τ) ω
  have hind : iIndepFun X P :=
    hW.hasIndepIncrements.nat (t := fun i : ℕ => (i : ℝ≥0) * τ)
      (fun a b hab => mul_le_mul_of_nonneg_right (Nat.mono_cast hab) (by positivity))
  have hlaw : ∀ i, HasLaw (X i) (gaussianReal 0 τ) P := by
    intro i
    have h := hW.hasLaw_sub (((i + 1 : ℕ) : ℝ≥0) * τ) ((i : ℝ≥0) * τ)
    have hd : nndist (((i + 1 : ℕ) : ℝ≥0) * τ).1 ((i : ℝ≥0) * τ).1 = τ := by
      rw [← NNReal.coe_inj, coe_nndist, Real.dist_eq]
      change |((((i + 1 : ℕ) : ℝ≥0) * τ : ℝ≥0) : ℝ) - (((i : ℝ≥0) * τ : ℝ≥0) : ℝ)| = τ
      push_cast
      rw [show ((i : ℝ) + 1) * τ - i * τ = τ by ring, abs_of_nonneg (NNReal.coe_nonneg τ)]
    rw [hd] at h
    exact h
  have hset : {ω | ∀ i < n, |X i ω| < a} = ⋂ i ∈ Finset.range n, X i ⁻¹' Ioo (-a) a := by
    ext ω
    simp only [mem_ofPred_eq, mem_iInter, Finset.mem_range, mem_preimage, mem_Ioo, abs_lt]
  have hprod : ∀ i ∈ Finset.range n, P (X i ⁻¹' Ioo (-a) a) = gaussianReal 0 τ (Ioo (-a) a) :=
    fun i _ => (hlaw i).measure_eq measurableSet_Ioo
  change P {ω | ∀ i < n, |X i ω| < a} = _
  rw [hset, hind.measure_inter_preimage_eq_mul _ (fun i _ => measurableSet_Ioo),
    Finset.prod_congr rfl hprod]
  simp

/-- **The exponential tail of the time spent in a ball.**  For Brownian motion on `ℝ ^ d` with
generator `Δ / (2 d)` started at `u`, the probability that it stays in the open ball of radius
`r` about `u` up to time `A r ^ 2` is at most `c₀ exp (- c₁ A)`, with `c₀` and `c₁` depending
only on the dimension.  Equivalently, the exit time of the ball, divided by `r ^ 2`, has an
exponential tail. -/
theorem exists_brownian_stay_tail (d : ℕ) (hd : 0 < d) :
    ∃ c₀ c₁ : ℝ, 0 < c₀ ∧ 0 < c₁ ∧
      ∀ (u : EuclideanSpace ℝ (Fin d)) (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω),
        IsProbabilityMeasure P → ∀ B : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin d),
          IsBrownianSpace d u B P → ∀ r : ℝ, 0 < r → ∀ A : ℝ, 1 ≤ A →
            P {ω | ∀ s : ℝ≥0, (s : ℝ) ≤ A * r ^ 2 → ‖B s ω - u‖ < r}
              ≤ ENNReal.ofReal (c₀ * Real.exp (-(c₁ * A))) := by
  obtain ⟨q, hq⟩ : ∃ q : ℝ≥0∞,
      gaussianReal 0 1 (Ioo (-(2 * Real.sqrt d)) (2 * Real.sqrt d)) = q := ⟨_, rfl⟩
  have hq1 : q < 1 := by
    rw [← hq]
    exact gaussianReal_Ioo_neg_lt_one _
  have hqt : q.toReal < 1 := by
    have h := (ENNReal.toReal_lt_toReal (ne_top_of_lt hq1) ENNReal.one_ne_top).2 hq1
    simpa using h
  obtain ⟨ρ, hρpos, hρ1, hqρ⟩ : ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ q.toReal ≤ ρ :=
    ⟨max q.toReal (1 / 2), lt_max_of_lt_right (by norm_num), max_lt hqt (by norm_num),
      le_max_left _ _⟩
  have hlog : Real.log ρ < 0 := Real.log_neg hρpos hρ1
  refine ⟨Real.exp (-Real.log ρ), -Real.log ρ, Real.exp_pos _, by linarith, ?_⟩
  intro u Ω _ P _hP B hB r hr A hA
  obtain ⟨n, hn_def⟩ : ∃ n : ℕ, n = ⌊A⌋₊ := ⟨_, rfl⟩
  have hn : (n : ℝ) ≤ A := by
    rw [hn_def]
    exact Nat.floor_le (by linarith)
  have hA1 : A < n + 1 := by
    rw [hn_def]
    exact Nat.lt_floor_add_one A
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ≥0, (τ : ℝ) = r ^ 2 := ⟨⟨r ^ 2, sq_nonneg r⟩, rfl⟩
  let i0 : Fin d := ⟨0, hd⟩
  have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  have hcoord : ∀ v : EuclideanSpace ℝ (Fin d), |v i0| ≤ ‖v‖ := fun v => by
    rw [← Real.norm_eq_abs]
    exact PiLp.norm_apply_le v i0
  have hcoe : ∀ k : ℕ, (((k : ℝ≥0) * τ : ℝ≥0) : ℝ) = k * r ^ 2 := fun k => by
    rw [NNReal.coe_mul, NNReal.coe_natCast, hτ]
  have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
  have hsub : {ω | ∀ s : ℝ≥0, (s : ℝ) ≤ A * r ^ 2 → ‖B s ω - u‖ < r} ⊆
      {ω | ∀ i < n, |Real.sqrt d * (B (((i + 1 : ℕ) : ℝ≥0) * τ) ω i0 - u i0)
          - Real.sqrt d * (B ((i : ℝ≥0) * τ) ω i0 - u i0)| < 2 * Real.sqrt d * r} := by
    intro ω hω
    rw [mem_ofPred_eq] at hω ⊢
    intro i hi
    have hi' : (i : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt hi
    have h1 := hω (((i + 1 : ℕ) : ℝ≥0) * τ) (by
      rw [hcoe]
      push_cast
      exact mul_le_mul_of_nonneg_right (by linarith) hr2)
    have h0 := hω ((i : ℝ≥0) * τ) (by
      rw [hcoe]
      exact mul_le_mul_of_nonneg_right (by linarith) hr2)
    have e1 := abs_le.1 (hcoord (B (((i + 1 : ℕ) : ℝ≥0) * τ) ω - u))
    have e0 := abs_le.1 (hcoord (B ((i : ℝ≥0) * τ) ω - u))
    simp only [PiLp.sub_apply] at e1 e0
    have hx : |B (((i + 1 : ℕ) : ℝ≥0) * τ) ω i0 - B ((i : ℝ≥0) * τ) ω i0| < 2 * r :=
      abs_lt.2 ⟨by linarith [e1.1, e0.2], by linarith [e1.2, e0.1]⟩
    have e : Real.sqrt d * (B (((i + 1 : ℕ) : ℝ≥0) * τ) ω i0 - u i0)
        - Real.sqrt d * (B ((i : ℝ≥0) * τ) ω i0 - u i0)
        = Real.sqrt d * (B (((i + 1 : ℕ) : ℝ≥0) * τ) ω i0 - B ((i : ℝ≥0) * τ) ω i0) := by
      ring
    rw [e, abs_mul, abs_of_pos hsqrt]
    have := mul_lt_mul_of_pos_left hx hsqrt
    linarith
  have hscale : gaussianReal 0 τ (Ioo (-(2 * Real.sqrt d * r)) (2 * Real.sqrt d * r)) = q := by
    rw [← hq]
    exact gaussianReal_Ioo_mul_eq τ hr hτ _
  have hlaw : P {ω | ∀ i < n, |Real.sqrt d * (B (((i + 1 : ℕ) : ℝ≥0) * τ) ω i0 - u i0)
          - Real.sqrt d * (B ((i : ℝ≥0) * τ) ω i0 - u i0)| < 2 * Real.sqrt d * r} = q ^ n := by
    rw [← hscale]
    exact measure_forall_abs_increment_lt (fun t ω => Real.sqrt d * (B t ω i0 - u i0))
      (hB.coord i0) τ _ n
  have hreal : q.toReal ^ n ≤ Real.exp (-Real.log ρ) * Real.exp (-(-Real.log ρ * A)) := by
    calc q.toReal ^ n ≤ ρ ^ n := pow_le_pow_left₀ ENNReal.toReal_nonneg hqρ n
      _ = Real.exp (n * Real.log ρ) := by rw [Real.exp_nat_mul, Real.exp_log hρpos]
      _ ≤ Real.exp (-Real.log ρ) * Real.exp (-(-Real.log ρ * A)) := by
        rw [← Real.exp_add]
        apply Real.exp_le_exp.2
        have := mul_le_mul_of_nonpos_left hA1.le hlog.le
        linarith
  calc P {ω | ∀ s : ℝ≥0, (s : ℝ) ≤ A * r ^ 2 → ‖B s ω - u‖ < r}
      ≤ P {ω | ∀ i < n, |Real.sqrt d * (B (((i + 1 : ℕ) : ℝ≥0) * τ) ω i0 - u i0)
          - Real.sqrt d * (B ((i : ℝ≥0) * τ) ω i0 - u i0)| < 2 * Real.sqrt d * r} :=
        measure_mono hsub
    _ = q ^ n := hlaw
    _ = ENNReal.ofReal (q.toReal ^ n) := by
        rw [ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal (ne_top_of_lt hq1)]
    _ ≤ ENNReal.ofReal (Real.exp (-Real.log ρ) * Real.exp (-(-Real.log ρ * A))) :=
        ENNReal.ofReal_le_ofReal hreal

end LatticeProb
