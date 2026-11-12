/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.LowerAssembly at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.LowerAssemblyAux2

/-!
# Node `LA`: the conditional assembly of the lower bound (1.8)

We prove `Blueprint.Draft.LowerAssembly`:
`AOneFinite → ASubadditiveE → SegCombLaw → Oscillation37 → DiscreteBlockConstruction →
CouplingAtPoints → PolygonRiemannBound → ExponentFromProb → Prop12Lower`.

Fix `n`, `θ = η log M / 3` (`M = 16^n`), and `ξ` small; put `δ = ξ^{2/3}`, `ρ = δ n^{3/4}`,
`ε_j = ρ M^{-j}`, `b = 4^{ξ²/2}(1 - δ²(a_n - C n^{7/8}) + θ δ²)` and `Λ = -log b / log M`.
For `θ' > 0` we show `P(log D_{ε_j} / log ε_j < Λ - θ') → 0` (`key_tendsto`), so that
`ExponentFromProb` gives `Λ ≤ λ`.  For each depth `j`:

1. `DiscreteBlockConstruction` gives polygons `poly i`, a point set `S ⊇ riemannPts`, band Gram
   vectors `u` and a selection `sel` with `E[cost(poly (sel x), ⟪u, x⟫)] ≤ b^j`.
2. `CouplingAtPoints` glues `u` to a Gram realisation `V` of the circle-average covariance at
   `ε_j` on `S`, with `‖V s - ι (u s)‖² ≤ C_ρ`.
3. Deterministically (`PolygonRiemannBound`, edges `≤ Nr ε_j ≤ Nr · 8ε_j`), on the event where
   `osc(h_{ε_j}, 8ε_j) ≤ κ log(1/ε_j)` and some polygon has cost `≤ t_j = e^{j(log b + s)}`,
   `log D ≤ ξκ log(1/ε_j) + j (log b + s)`; since `D > 0` and `log ε_j < 0` for large `j`,
   this gives `log D / log ε_j ≥ Λ - θ'` for large `j` (with `ξκ = θ'/4`, `s = θ' log M / 4`).
4. The probability that every polygon costs more than `t_j` is bounded in Gram space
   (`prob_all_cost_gt_le`, using `SegCombLaw` for the law of `(h_{ε_j}(s))_{s ∈ S}`) by
   `2|S| e^{-l T + C_ρ l²/2} + e^{ξ T} b^j / t_j` with `T = τ j`, `τ = s/(2ξ)` and
   `l τ = |A_gr| + 1`; both terms decay exponentially in `j` since `|S| ≤ e^{A_gr j}`.
5. `Oscillation37` handles the oscillation event.

Finally `-log b ≥ δ²(a_n - C n^{7/8} - θ) - (ξ²/2) log 4` (from `log x ≤ x - 1`), and
`ξ² / δ² = ξ^{2/3} → 0`, which gives (1.8) with the constant `C` of
`DiscreteBlockConstruction`.

The hypotheses `AOneFinite` and `ASubadditiveE` are not needed: `DiscreteBlockConstruction` and
`Prop12Lower` are both phrased with `a n = (aE n).toReal`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace Classical

namespace LQGDimension.LowerAsm

open Blueprint.Draft

/-- The body of `DiscreteBlockConstruction` at depth `j`, for `ε_j = ρ M^{-j}` and block factor
`b` (with `ρ = ξ^{2/3} n^{3/4}` and `M = 16^n` it is literally the node's statement). -/
def BlockData (ξ ρ M b Agr : ℝ) (j : ℕ) : Prop :=
  ∃ (m : ℕ) (poly : Fin m → List ℂ) (S : Finset ℂ) (Nr d : ℕ)
      (u : ℂ → EuclideanSpace ℝ (Fin d)) (sel : EuclideanSpace ℝ (Fin d) → Fin m),
      (∀ i, (poly i).head? = some 0 ∧ (poly i).getLast? = some 1 ∧ (∀ p ∈ poly i, p ∈ U) ∧
        (∀ e ∈ edges (poly i), ‖e.2 - e.1‖ ≤ Nr * (ρ * M⁻¹ ^ j)) ∧
        riemannPts Nr (poly i) ⊆ ↑S) ∧
      1 ≤ Nr ∧ (∀ s ∈ S, ‖s‖ ≤ 3) ∧ (S.card : ℝ) ≤ Real.exp (Agr * j) ∧
      (∀ s ∈ S, ∀ s' ∈ S, ⟪u s, u s'⟫ = bandCov (ρ * M⁻¹ ^ j) ρ s s') ∧
      Measurable sel ∧
      Integrable (fun x => riemannCost ξ Nr (poly (sel x)) (fun z => ⟪u z, x⟫))
        (stdGaussian (EuclideanSpace ℝ (Fin d))) ∧
      ∫ x, riemannCost ξ Nr (poly (sel x)) (fun z => ⟪u z, x⟫)
          ∂stdGaussian (EuclideanSpace ℝ (Fin d)) ≤ b ^ j

theorem tendsto_geom_nhdsWithin {ρ M : ℝ} (hρ : 0 < ρ) (hM : 1 < M) :
    Tendsto (fun j : ℕ => ρ * M⁻¹ ^ j) atTop (𝓝[>] 0) := by
  have hMinv0 : 0 < M⁻¹ := inv_pos.2 (by linarith)
  have hMinv1 : M⁻¹ < 1 := inv_lt_one_of_one_lt₀ hM
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun j => ?_⟩
  · have := (tendsto_pow_atTop_nhds_zero_of_lt_one hMinv0.le hMinv1).const_mul ρ
    rwa [mul_zero] at this
  · exact mul_pos hρ (pow_pos hMinv0 j)

/-- **Main probabilistic estimate.**  Along `ε_j = ρ M^{-j}`, for every `θ' > 0`,
`P(log D_{ε_j} / log ε_j < -log b / log M - θ') → 0`. -/
theorem key_tendsto (hP1 : SegCombLaw) (hL37 : Oscillation37) (hC36 : CouplingAtPoints)
    (hPR : PolygonRiemannBound) {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : ℝ → ℂ → Ω → ℝ} (hG : IsGFFCircleAverage h P) {ξ ρ M b Agr : ℝ} (hξ : 0 < ξ)
    (hρ : 0 < ρ) (hM : 1 < M) (hb : 0 < b) (hB : ∀ j : ℕ, 1 ≤ j → BlockData ξ ρ M b Agr j)
    {θ' : ℝ} (hθ' : 0 < θ') :
    Tendsto (fun j : ℕ => P {ω | Real.log (lfppDistance ξ (fun z => h (ρ * M⁻¹ ^ j) z ω)) /
        Real.log (ρ * M⁻¹ ^ j) < -Real.log b / Real.log M - θ'}) atTop (𝓝 0) := by
  have hL : 0 < Real.log M := Real.log_pos hM
  have hMinv0 : 0 < M⁻¹ := inv_pos.2 (by linarith)
  have hMinv1 : M⁻¹ < 1 := inv_lt_one_of_one_lt₀ hM
  have hεpos : ∀ j : ℕ, 0 < ρ * M⁻¹ ^ j := fun j => mul_pos hρ (pow_pos hMinv0 j)
  have hεlt : ∀ j : ℕ, 1 ≤ j → ρ * M⁻¹ ^ j < ρ := by
    intro j hj
    have : M⁻¹ ^ j < 1 := pow_lt_one₀ hMinv0.le hMinv1 (by omega)
    nlinarith
  have hlogε : ∀ j : ℕ, Real.log (ρ * M⁻¹ ^ j) = Real.log ρ - j * Real.log M := by
    intro j
    rw [Real.log_mul hρ.ne' (pow_pos hMinv0 j).ne', Real.log_pow, Real.log_inv]
    ring
  -- parameters
  set L : ℝ := Real.log M with hLdef
  have hLne : L ≠ 0 := hL.ne'
  have hξne : ξ ≠ 0 := hξ.ne'
  set κ : ℝ := θ' / (4 * ξ) with hκ
  have hκ0 : 0 < κ := by positivity
  have hξκ : ξ * κ = θ' / 4 := by
    rw [hκ]
    field_simp
  set s : ℝ := θ' * L / 4 with hs
  have hs0 : 0 < s := by positivity
  set τ : ℝ := s / (2 * ξ) with hτ
  have hτ0 : 0 < τ := by positivity
  have hτne : τ ≠ 0 := hτ0.ne'
  have hξτ : ξ * τ = s / 2 := by
    rw [hτ]
    field_simp
  set l : ℝ := (|Agr| + 1) / τ with hl
  have hl0 : 0 ≤ l := by positivity
  have hlτ : l * τ = |Agr| + 1 := by
    rw [hl]
    field_simp
  obtain ⟨Cρ, hCρ⟩ := hC36 ρ hρ
  set Λ : ℝ := -Real.log b / L with hΛ
  set c : ℝ := Λ - 3 * θ' / 4 with hc
  obtain ⟨J, hJ⟩ := exists_nat_ge (max (Real.log ρ / L + 1) (-2 * c * Real.log ρ / (θ' * L)))
  -- the oscillation events
  have h1 : Tendsto (fun j : ℕ => P {ω | κ * Real.log (1 / (ρ * M⁻¹ ^ j)) <
      osc (fun z => h (ρ * M⁻¹ ^ j) z ω) (8 * (ρ * M⁻¹ ^ j))}) atTop (𝓝 0) :=
    ((hL37 Ω P h hG).1 κ hκ0).comp (tendsto_geom_nhdsWithin hρ hM)
  -- the dominating sequence
  have e1 : Tendsto (fun j : ℕ => ENNReal.ofReal (2 * Real.exp (Cρ * l ^ 2 / 2) *
      Real.exp (-(j : ℝ)))) atTop (𝓝 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.comp tendsto_natCast_atTop_atTop).const_mul
      (2 * Real.exp (Cρ * l ^ 2 / 2))
    rw [mul_zero] at this
    have := ENNReal.tendsto_ofReal this
    rwa [ENNReal.ofReal_zero] at this
  have e2 : Tendsto (fun j : ℕ => ENNReal.ofReal (Real.exp (-(s / 2) * j))) atTop (𝓝 0) := by
    have h0 : Tendsto (fun j : ℕ => (s / 2) * (j : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp h0
    have := ENNReal.tendsto_ofReal this
    rw [ENNReal.ofReal_zero] at this
    refine this.congr fun j => ?_
    simp only [Function.comp_apply]
    congr 2
    ring
  have hf := (h1.add e1).add e2
  rw [add_zero, add_zero] at hf
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hf
    (Eventually.of_forall fun _ => zero_le) (eventually_atTop.2 ⟨max J 1, fun j hj => ?_⟩)
  -- the estimate at depth `j`
  have hj1 : 1 ≤ j := le_of_max_le_right hj
  have hjJ : (J : ℝ) ≤ j := by exact_mod_cast le_of_max_le_left hj
  obtain ⟨m, poly, S, Nr, d, u, sel, hpoly, hNr, hS3, hScard, hu, -, hint, hbound⟩ := hB j hj1
  obtain ⟨d', ι, V, hV, hVw⟩ := hCρ (ρ * M⁻¹ ^ j) ⟨hεpos j, hεlt j hj1⟩ S hS3 d u hu
  set t : ℝ := Real.exp (j * (Real.log b + s)) with ht
  set T : ℝ := τ * j with hT
  have hbad2 := prob_all_cost_gt_le hP1 hG (hεpos j) hξ.le poly S
    (fun i => (hpoly i).2.2.2.2) u sel hint ι V hV hVw (t := t) (T := T) (l := l)
    (Real.exp_pos _) hl0
  -- `log ε_j < 0` and the linear inequality for large `j`
  set ℓ : ℝ := Real.log (ρ * M⁻¹ ^ j) with hℓdef
  have hℓ : ℓ = Real.log ρ - j * L := hlogε j
  have hℓneg : ℓ < 0 := by
    have h2 : Real.log ρ / L + 1 ≤ j := (le_max_left _ _).trans hJ |>.trans hjJ
    have h3 : Real.log ρ + L ≤ j * L := by
      have := mul_le_mul_of_nonneg_right h2 hL.le
      rwa [add_mul, div_mul_cancel₀ _ hL.ne', one_mul] at this
    rw [hℓ]
    linarith
  have hlin : -c * Real.log ρ ≤ j * θ' * L / 2 := by
    have h2 : -2 * c * Real.log ρ / (θ' * L) ≤ j := (le_max_right _ _).trans hJ |>.trans hjJ
    rw [div_le_iff₀ (by positivity)] at h2
    linarith
  have hsub : {ω | Real.log (lfppDistance ξ (fun z => h (ρ * M⁻¹ ^ j) z ω)) / ℓ < Λ - θ'} ⊆
      {ω | κ * Real.log (1 / (ρ * M⁻¹ ^ j)) <
        osc (fun z => h (ρ * M⁻¹ ^ j) z ω) (8 * (ρ * M⁻¹ ^ j))} ∪
      {ω | ∀ i, t < riemannCost ξ Nr (poly i) (fun z => h (ρ * M⁻¹ ^ j) z ω)} := by
    intro ω hω
    by_contra hcon
    rw [mem_union, not_or] at hcon
    obtain ⟨hn1, hn2⟩ := hcon
    simp only [mem_ofPred_eq, not_lt, not_forall] at hn1 hn2
    obtain ⟨i, hi⟩ := hn2
    have hφ : Continuous fun z => h (ρ * M⁻¹ ^ j) z ω := hG.continuous _ (hεpos j) ω
    have hedge : ∀ e ∈ edges (poly i), ‖e.2 - e.1‖ ≤ Nr * (8 * (ρ * M⁻¹ ^ j)) := by
      intro e he
      have h2 := (hpoly i).2.2.2.1 e he
      have h3 : (0 : ℝ) ≤ Nr := Nat.cast_nonneg _
      have h4 := hεpos j
      nlinarith
    have hD := hPR ξ hξ (poly i) Nr (8 * (ρ * M⁻¹ ^ j)) hNr (hpoly i).1 (hpoly i).2.1
      (hpoly i).2.2.1 hedge _ hφ
    have hDpos := lfppDistance_pos ξ hφ
    have hDle : lfppDistance ξ (fun z => h (ρ * M⁻¹ ^ j) z ω) ≤
        Real.exp (ξ * (κ * Real.log (1 / (ρ * M⁻¹ ^ j)))) * t :=
      hD.trans (mul_le_mul (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hn1 hξ.le)) hi
        (riemannCost_nonneg _ _ _ _) (Real.exp_pos _).le)
    have hlogD := Real.log_le_log hDpos hDle
    rw [Real.log_mul (Real.exp_pos _).ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp,
      one_div, Real.log_inv, ← hℓdef] at hlogD
    have hA' : Real.log (lfppDistance ξ (fun z => h (ρ * M⁻¹ ^ j) z ω)) ≤
        -(θ' / 4) * ℓ + j * (Real.log b + s) := by
      have : ξ * (κ * -ℓ) = -(ξ * κ) * ℓ := by ring
      rw [this, hξκ] at hlogD
      exact hlogD
    have hkey : (Λ - θ') * ℓ - (-(θ' / 4) * ℓ + j * (Real.log b + s)) =
        c * Real.log ρ + j * θ' * L / 2 := by
      rw [hc, hΛ, hs, hℓ]
      field_simp
      ring
    have hfin : Λ - θ' ≤ Real.log (lfppDistance ξ (fun z => h (ρ * M⁻¹ ^ j) z ω)) / ℓ := by
      rw [le_div_iff_of_neg hℓneg]
      linarith
    exact absurd hω (not_lt.2 hfin)
  -- the two finite-dimensional bounds
  have hA1 : 2 * (S.card : ℝ) * Real.exp (-l * T + Cρ * l ^ 2 / 2) ≤
      2 * Real.exp (Cρ * l ^ 2 / 2) * Real.exp (-(j : ℝ)) := by
    have hlT : l * T = (|Agr| + 1) * j := by rw [hT, ← mul_assoc, hlτ]
    have hAj : Agr * j ≤ |Agr| * j :=
      mul_le_mul_of_nonneg_right (le_abs_self Agr) (Nat.cast_nonneg j)
    have hexp1 : Real.exp (Agr * j) * Real.exp (-l * T + Cρ * l ^ 2 / 2) ≤
        Real.exp (Cρ * l ^ 2 / 2) * Real.exp (-(j : ℝ)) := by
      rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
      have : -l * T = -(l * T) := by ring
      rw [this, hlT]
      linarith
    have := mul_le_mul_of_nonneg_right hScard (Real.exp_pos (-l * T + Cρ * l ^ 2 / 2)).le
    linarith
  have hA2 : Real.exp (ξ * T) * (∫ x, riemannCost ξ Nr (poly (sel x)) (fun z => ⟪u z, x⟫)
      ∂stdGaussian (EuclideanSpace ℝ (Fin d))) / t ≤ Real.exp (-(s / 2) * j) := by
    have hbj : b ^ j = Real.exp (j * Real.log b) := by
      rw [Real.exp_nat_mul, Real.exp_log hb]
    calc Real.exp (ξ * T) * (∫ x, riemannCost ξ Nr (poly (sel x)) (fun z => ⟪u z, x⟫)
          ∂stdGaussian (EuclideanSpace ℝ (Fin d))) / t
        ≤ Real.exp (ξ * T) * b ^ j / t := by
          gcongr
      _ = Real.exp (-(s / 2) * j) := by
          rw [hbj, ht, ← Real.exp_add, ← Real.exp_sub]
          congr 1
          rw [hT]
          linear_combination (j : ℝ) * hξτ
  calc P {ω | Real.log (lfppDistance ξ (fun z => h (ρ * M⁻¹ ^ j) z ω)) / ℓ < Λ - θ'}
      ≤ P ({ω | κ * Real.log (1 / (ρ * M⁻¹ ^ j)) <
          osc (fun z => h (ρ * M⁻¹ ^ j) z ω) (8 * (ρ * M⁻¹ ^ j))} ∪
          {ω | ∀ i, t < riemannCost ξ Nr (poly i) (fun z => h (ρ * M⁻¹ ^ j) z ω)}) :=
        measure_mono hsub
    _ ≤ P {ω | κ * Real.log (1 / (ρ * M⁻¹ ^ j)) <
          osc (fun z => h (ρ * M⁻¹ ^ j) z ω) (8 * (ρ * M⁻¹ ^ j))} +
        P {ω | ∀ i, t < riemannCost ξ Nr (poly i) (fun z => h (ρ * M⁻¹ ^ j) z ω)} :=
        measure_union_le _ _
    _ ≤ _ := by
        rw [add_assoc]
        refine add_le_add le_rfl (hbad2.trans (add_le_add ?_ ?_))
        · exact ENNReal.ofReal_le_ofReal hA1
        · exact ENNReal.ofReal_le_ofReal hA2

end LQGDimension.LowerAsm

namespace LQGDimension

open Blueprint.Draft LowerAsm

/-- **Node `LA`** (`Blueprint.Draft.LowerAssembly`): the conditional assembly of (1.8). -/
theorem lowerAssembly : Blueprint.Draft.LowerAssembly := by
  intro _hA1 _hAS hP1 hL37 hB57 hC36 hPR hEX Ω _ P h hG
  obtain ⟨C, N₀, hB⟩ := hB57
  refine ⟨C, max N₀ 1, fun n hn η hη => ?_⟩
  have hn1 : 1 ≤ n := le_of_max_le_right hn
  have hM : (1 : ℝ) < (16 : ℝ) ^ n := one_lt_pow₀ (by norm_num) (by omega)
  set L : ℝ := Real.log ((16 : ℝ) ^ n) with hLdef
  have hL : 0 < L := Real.log_pos hM
  have hLne : L ≠ 0 := hL.ne'
  set θ : ℝ := η * L / 3 with hθ
  have hθ0 : 0 < θ := by positivity
  set A : ℝ := a n - C * (n : ℝ) ^ (7 / 8 : ℝ) with hA
  have hp0 : Tendsto (fun ξ : ℝ => ξ ^ (2 / 3 : ℝ)) (𝓝[>] 0) (𝓝 0) := by
    have := Real.continuousAt_rpow_const 0 (2 / 3 : ℝ) (Or.inr (by norm_num))
    rw [ContinuousAt, Real.zero_rpow (by norm_num)] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  have ev1 : ∀ᶠ ξ in 𝓝[>] (0 : ℝ),
      0 < 1 - (ξ ^ (2 / 3 : ℝ)) ^ 2 * A + θ * (ξ ^ (2 / 3 : ℝ)) ^ 2 := by
    have h2 := (tendsto_const_nhds (x := (1 : ℝ))).sub ((hp0.pow 2).mul_const A) |>.add
      ((hp0.pow 2).const_mul θ)
    rw [show (1 : ℝ) - (0 : ℝ) ^ 2 * A + θ * (0 : ℝ) ^ 2 = 1 by ring] at h2
    exact h2.eventually_const_lt one_pos
  have ev2 : ∀ᶠ ξ in 𝓝[>] (0 : ℝ), ξ ^ (2 / 3 : ℝ) * Real.log 4 < 2 * L * η / 3 := by
    have h2 := hp0.mul_const (Real.log 4)
    rw [zero_mul] at h2
    exact h2.eventually_lt_const (by positivity)
  filter_upwards [hB n (le_of_max_le_left hn) θ hθ0, self_mem_nhdsWithin, ev1, ev2]
    with ξ hBξ hξ hb1 hsmall
  intro lam hlam
  have hξ0 : 0 < ξ := hξ
  obtain ⟨Agr, hAgr⟩ := hBξ
  set p : ℝ := ξ ^ (2 / 3 : ℝ) with hp
  have hpp : 0 < p := Real.rpow_pos_of_pos hξ0 _
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  set ρ : ℝ := p * (n : ℝ) ^ (3 / 4 : ℝ) with hρ
  have hρ0 : 0 < ρ := mul_pos hpp (Real.rpow_pos_of_pos hn0 _)
  set b : ℝ := (4 : ℝ) ^ (ξ ^ 2 / 2) * (1 - p ^ 2 * A + θ * p ^ 2) with hb
  have h4 : (0 : ℝ) < (4 : ℝ) ^ (ξ ^ 2 / 2) := Real.rpow_pos_of_pos (by norm_num) _
  have hb0 : 0 < b := mul_pos h4 hb1
  have hΛ : -Real.log b / L ≤ lam := by
    refine (hEX Ω P h ξ lam (-Real.log b / L) hG.isProbabilityMeasure hlam).2 fun θ' hθ' => ?_
    exact ⟨fun j => ρ * ((16 : ℝ) ^ n)⁻¹ ^ j, tendsto_geom_nhdsWithin hρ0 hM,
      key_tendsto hP1 hL37 hC36 hPR hG hξ0 hρ0 hM hb0 hAgr hθ'⟩
  -- algebra
  have hp2 : ξ ^ (4 / 3 : ℝ) = p ^ 2 := by
    rw [hp, ← Real.rpow_natCast, ← Real.rpow_mul hξ0.le]
    norm_num
  have hp3 : ξ ^ 2 = p ^ 3 := by
    rw [hp, ← Real.rpow_natCast (ξ ^ (2 / 3 : ℝ)) 3, ← Real.rpow_mul hξ0.le]
    norm_num
  have hlogb : Real.log b ≤ p ^ 3 / 2 * Real.log 4 - p ^ 2 * A + θ * p ^ 2 := by
    rw [hb, Real.log_mul h4.ne' hb1.ne', Real.log_rpow (by norm_num), hp3]
    have := Real.log_le_sub_one_of_pos hb1
    linarith
  have h1 : -Real.log b ≤ lam * L := (div_le_iff₀ hL).1 hΛ
  have h3 : p ^ 3 / 2 * Real.log 4 ≤ p ^ 2 * (L * η / 3) := by
    have e : p ^ 3 / 2 * Real.log 4 = p ^ 2 / 2 * (p * Real.log 4) := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left hsmall.le (by positivity : (0 : ℝ) ≤ p ^ 2 / 2)
    linarith
  have h5 : 0 ≤ η * L * p ^ 2 := by positivity
  have key : (A - η * L) * p ^ 2 ≤ lam * L := by
    rw [hθ] at hlogb
    nlinarith
  rw [hp2, le_div_iff₀ (by positivity)]
  calc (A / L - η) * p ^ 2 = (A - η * L) * p ^ 2 / L := by field_simp
    _ ≤ lam * L / L := by gcongr
    _ = lam := by field_simp

end LQGDimension
