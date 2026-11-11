import Mathlib
import LatticeProb.LQG.LQGMeasureNonatomicMassTail
import LatticeProb.LQG.LQGMeasureNonatomicMassPoly

/-!
# The multiscale ball-mass bound for `h^ℂ` around the origin

Adapted from the Lean formalization accompanying [Harmonic balls in Liouville quantum gravity, arXiv:2208.11795],
Lemma 2.4: the union bound over the dyadic scales of Berestycki and Gwynne, Random walks on mated-CRT planar maps and
Liouville Brownian motion, arXiv:2003.10320, Lemma A.1, p. 66 of v2 (and of Ding and Gwynne 2020,
Lemma 3.8, for the rescaled fields). The steps of arXiv:2208.11795, Lemma 2.4, `WholePlaneScaledBallMassStep`, `RescaledBallMassUniformStep`
and the event `rescaledBallMassEvent`, are stated as definitions with the names of this library. Nothing is assumed: the
reduction `wholePlaneScaledBallMassStep_of_uniform_lp` takes the steps as hypotheses, and the reduction itself is proved here.
-/

universe u

namespace LatticeProb.LQG.LQGMeasureNonatomicMass

open MeasureTheory ProbabilityTheory Metric Filter Set Topology LatticeProb.Gauss LatticeProb.LQG
open scoped ENNReal
open LatticeProb.LQG.ProfileDerived (dyadicScale_pos)

/-- The rescaled ball-mass event `rescaledBallMassEvent`: for `τ = 2^{-k}`,
`τ^{γQ} e^{γ h^ℂ_τ(0)} r^{β⁻} ≤ μ₀(B_{τr}(τw)) ≤ τ^{γQ} e^{γ h^ℂ_τ(0)} r^{β⁺}` for all `w ∈ closedBall 0 R`. -/
def rescaledBallMassEvent {Ω : Type*} (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ₀ : Ω → Measure ℂ)
    (R βplus βminus : ℝ) (k : ℕ) (r : ℝ) : Set Ω :=
  {ω | ∀ w ∈ closedBall (0 : ℂ) R,
    ENNReal.ofReal (dyadicScale k ^ (γ * lqgQ γ) * Real.exp (γ * hcirc ω (dyadicScale k) 0) * r ^ βminus) ≤
        μ₀ ω (ball ((dyadicScale k : ℂ) * w) (dyadicScale k * r)) ∧
      μ₀ ω (ball ((dyadicScale k : ℂ) * w) (dyadicScale k * r)) ≤
        ENNReal.ofReal (dyadicScale k ^ (γ * lqgQ γ) * Real.exp (γ * hcirc ω (dyadicScale k) 0) * r ^ βplus)}

/-- The uniform rescaled ball-mass step, Ding-Gwynne Lemma 3.8 for the rescaled fields uniformly in the scale. A
definition; proved in the module `LatticeProb.LQG.LQGMeasureNonatomicMassRescaled`. -/
def RescaledBallMassUniformStepLP : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ₀ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ₀ →
  ∀ R : ℝ, 0 < R → ∀ βplus βminus : ℝ, 0 < βplus → βplus < (2 - γ) ^ 2 / 2 → (2 + γ) ^ 2 / 2 < βminus →
    ∃ p : ℝ, 0 < p ∧ ∃ C : ℝ, ∃ r₀ > 0, ∀ k : ℕ, ∀ r : ℝ, 0 < r → r < r₀ →
      P (rescaledBallMassEvent γ hcirc μ₀ R βplus βminus k r)ᶜ ≤ ENNReal.ofReal (C * ((k : ℝ) + 1) ^ 2 * r ^ p)

/-- The multiscale ball-mass step of arXiv:2208.11795, Lemma 2.4: the multiscale ball bound for `h^ℂ` around the origin, with
polynomially high probability. A definition; proved in the module `LatticeProb.LQG.LQGMeasureNonatomicMassRescaled`. -/
def WholePlaneScaledBallMassStepLP : Prop :=
  ∀ γ : ℝ, 0 < γ → γ < 2 →
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ₀ : Ω → Measure ℂ), IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ₀ →
  ∀ R : ℝ, 0 < R → ∀ βplus βminus ζ : ℝ, 0 < βplus → βplus < (2 - γ) ^ 2 / 2 → (2 + γ) ^ 2 / 2 < βminus →
    0 < ζ → ζ < 1 →
    PolyHighProb P fun δ => {ω | ∀ t : ℝ, δ ^ (1 - ζ) ≤ t → t ≤ 1 → ∀ z ∈ closedBall (0 : ℂ) (R * t),
      ENNReal.ofReal (t ^ (γ * lqgQ γ) * (δ / t) ^ βminus * δ ^ ζ) ≤ μ₀ ω (ball z δ) ∧
        μ₀ ω (ball z δ) ≤ ENNReal.ofReal (t ^ (γ * lqgQ γ) * (δ / t) ^ βplus * δ ^ (-ζ))}

/-- Polynomially high probability from an eventual bound `P[(E r)ᶜ] ≤ r^p`. -/
theorem polyHighProb_of_eventually {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E : ℝ → Set Ω} {p : ℝ}
    (hp : 0 < p) (h : ∀ᶠ r in 𝓝[>] (0 : ℝ), P (E r)ᶜ ≤ ENNReal.ofReal (r ^ p)) : PolyHighProb P E := by
  obtain ⟨r₁, hr₁, h'⟩ := exists_pos_of_eventually_nhdsGT h
  exact ⟨p, hp, 1, r₁, hr₁, fun r hr hrr => by rw [one_mul]; exact h' r hr hrr⟩

/-- `δ / δ^{1-ζ} = δ^ζ`. -/
theorem div_rpow_one_sub {δ : ℝ} (hδ : 0 < δ) (ζ : ℝ) : δ / δ ^ (1 - ζ) = δ ^ ζ := by
  rw [div_eq_iff (Real.rpow_pos_of_pos hδ _).ne', ← Real.rpow_add hδ]
  have : ζ + (1 - ζ) = 1 := by ring
  rw [this, Real.rpow_one]

/-- The good event at scale `δ`: at every dyadic scale `2^{-k} ≥ δ^{1-ζ}`, the event of Ding-Gwynne Lemma 3.8 for the rescaled
field at radius `δ 2^k`, and `δ^{ζ/2} ≤ e^{γ h^ℂ_{2^{-k}}(0)} ≤ δ^{-ζ/2}`. -/
def scaledGoodEvent {Ω : Type*} (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ₀ : Ω → Measure ℂ)
    (R βplus βminus ζ δ : ℝ) : Set Ω :=
  {ω | ∀ k : ℕ, δ ^ (1 - ζ) ≤ dyadicScale k →
    ω ∈ rescaledBallMassEvent γ hcirc μ₀ R βplus βminus k (δ / dyadicScale k) ∧
      (δ ^ (ζ / 2) ≤ Real.exp (γ * hcirc ω (dyadicScale k) 0) ∧
        Real.exp (γ * hcirc ω (dyadicScale k) 0) ≤ δ ^ (-(ζ / 2)))}

/-- Deterministic part: on the good event, the multiscale ball bound of `WholePlaneScaledBallMassStep`. -/
theorem scaledBallBound_of_good {Ω : Type*} {γ R βp βm ζ δ : ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ₀ : Ω → Measure ℂ} {ω : Ω} (hβp : 0 < βp) (hβm : 0 ≤ βm) (hδ : 0 < δ) (hG : 0 ≤ γ * lqgQ γ)
    (h2G : 2 ^ (γ * lqgQ γ) * δ ^ (ζ / 2) ≤ 1) (h2βm : 2 ^ βm * δ ^ (ζ / 2) ≤ 1)
    (hω : ω ∈ scaledGoodEvent γ hcirc μ₀ R βp βm ζ δ)
    {t : ℝ} (ht : δ ^ (1 - ζ) ≤ t) (ht1 : t ≤ 1) {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) (R * t)) :
    ENNReal.ofReal (t ^ (γ * lqgQ γ) * (δ / t) ^ βm * δ ^ ζ) ≤ μ₀ ω (ball z δ) ∧
      μ₀ ω (ball z δ) ≤ ENNReal.ofReal (t ^ (γ * lqgQ γ) * (δ / t) ^ βp * δ ^ (-ζ)) := by
  set G := γ * lqgQ γ with hG_def
  have ht0 : 0 < t := (Real.rpow_pos_of_pos hδ _).trans_le ht
  obtain ⟨k, hk1, hk2⟩ :=
    exists_nat_pow_near_of_lt_one ht0 ht1 (by norm_num : (0 : ℝ) < 2⁻¹) (by norm_num)
  have hτdef : dyadicScale k = (2 : ℝ)⁻¹ ^ k := rfl
  have hτ0 : 0 < dyadicScale k := dyadicScale_pos k
  have htτ : t ≤ dyadicScale k := by rw [hτdef]; exact hk2
  have hτ2 : dyadicScale k ≤ 2 * t := by
    rw [hτdef]; rw [pow_succ] at hk1; linarith
  obtain ⟨hDG, hX1, hX2⟩ := hω k (ht.trans htτ)
  set τ := dyadicScale k with hτ
  set X := Real.exp (γ * hcirc ω τ 0) with hX
  have hX0 : 0 < X := Real.exp_pos _
  have hτc : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ0.ne'
  have hzw : (τ : ℂ) * (z / (τ : ℂ)) = z := mul_div_cancel₀ z hτc
  have hr : τ * (δ / τ) = δ := mul_div_cancel₀ δ hτ0.ne'
  have hw : z / (τ : ℂ) ∈ closedBall (0 : ℂ) R := by
    rw [mem_closedBall_zero_iff] at hz ⊢
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hτ0, div_le_iff₀ hτ0]
    have hR : 0 ≤ R := by
      by_contra hR; nlinarith [norm_nonneg z, not_le.1 hR]
    nlinarith
  obtain ⟨hlow, hup⟩ := hDG _ hw
  rw [hzw, hr] at hlow hup
  constructor
  · refine le_trans (ENNReal.ofReal_le_ofReal ?_) hlow
    have h2pos : 0 < (2 : ℝ) ^ βm := by positivity
    have hδζ : δ ^ ζ ≤ X / 2 ^ βm := by
      have e1 : δ ^ ζ = δ ^ (ζ / 2) * δ ^ (ζ / 2) := by
        rw [← Real.rpow_add hδ]; congr 1; ring
      rw [e1, le_div_iff₀ h2pos]
      calc δ ^ (ζ / 2) * δ ^ (ζ / 2) * 2 ^ βm = (2 ^ βm * δ ^ (ζ / 2)) * δ ^ (ζ / 2) := by ring
        _ ≤ 1 * X := mul_le_mul h2βm hX1 (by positivity) zero_le_one
        _ = X := one_mul X
    have h3 : (δ / t) ^ βm / 2 ^ βm ≤ (δ / τ) ^ βm := by
      rw [← Real.div_rpow (by positivity) (by norm_num)]
      refine Real.rpow_le_rpow (by positivity) ?_ hβm
      rw [div_div, div_le_div_iff_of_pos_left hδ (by positivity) hτ0]; linarith
    calc t ^ G * (δ / t) ^ βm * δ ^ ζ ≤ τ ^ G * (δ / t) ^ βm * (X / 2 ^ βm) := by
          gcongr
      _ = τ ^ G * X * ((δ / t) ^ βm / 2 ^ βm) := by ring
      _ ≤ τ ^ G * X * (δ / τ) ^ βm := by gcongr
  · refine hup.trans (ENNReal.ofReal_le_ofReal ?_)
    have h1 : τ ^ G ≤ 2 ^ G * t ^ G := by
      rw [← Real.mul_rpow (by norm_num) ht0.le]; exact Real.rpow_le_rpow hτ0.le hτ2 hG
    have h2 : (δ / τ) ^ βp ≤ (δ / t) ^ βp :=
      Real.rpow_le_rpow (by positivity) (div_le_div_of_nonneg_left hδ.le ht0 htτ) hβp.le
    have h3 : 2 ^ G * X ≤ δ ^ (-ζ) := by
      have e1 : δ ^ (-ζ) = δ ^ (-(ζ / 2)) * δ ^ (-(ζ / 2)) := by
        rw [← Real.rpow_add hδ]; congr 1; ring
      have h2G' : 2 ^ G ≤ δ ^ (-(ζ / 2)) := by
        calc (2 : ℝ) ^ G = 2 ^ G * δ ^ (ζ / 2) * δ ^ (-(ζ / 2)) := by
              rw [mul_assoc, ← Real.rpow_add hδ]; simp
          _ ≤ 1 * δ ^ (-(ζ / 2)) := by gcongr
          _ = δ ^ (-(ζ / 2)) := one_mul _
      rw [e1]; exact mul_le_mul h2G' hX2 hX0.le (by positivity)
    calc τ ^ G * X * (δ / τ) ^ βp ≤ (2 ^ G * t ^ G) * X * (δ / t) ^ βp := by gcongr
      _ = t ^ G * (δ / t) ^ βp * (2 ^ G * X) := by ring
      _ ≤ t ^ G * (δ / t) ^ βp * δ ^ (-ζ) := by gcongr

/-- Probability of the good event: the union bound over the dyadic scales `2^{-k} ≥ δ^{1-ζ}`. -/
theorem scaledGoodEvent_polyHighProb {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {γ R βp βm ζ : ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ₀ : Ω → Measure ℂ} (hγ : 0 < γ) (hζ0 : 0 < ζ)
    {p C r₀ : ℝ} (hp : 0 < p) (hr₀ : 0 < r₀)
    (hU : ∀ k : ℕ, ∀ r : ℝ, 0 < r → r < r₀ →
      P (rescaledBallMassEvent γ hcirc μ₀ R βp βm k r)ᶜ ≤ ENNReal.ofReal (C * ((k : ℝ) + 1) ^ 2 * r ^ p))
    (hT : ∀ k : ℕ, ∀ L : ℝ, 0 ≤ L → P {ω | L ≤ |hcirc ω (dyadicScale k) 0|} ≤
        ENNReal.ofReal (2 * Real.exp (-(L ^ 2) / (2 * (((k : ℝ) + 1) * Real.log 2))))) :
    PolyHighProb P (scaledGoodEvent γ hcirc μ₀ R βp βm ζ) := by
  classical
  set c : ℝ := ζ ^ 2 / (16 * γ ^ 2) with hc
  have hc0 : 0 < c := by positivity
  set q : ℝ := min (ζ * p) c with hq
  have hq0 : 0 < q := lt_min (mul_pos hζ0 hp) hc0
  have hqp : q ≤ ζ * p := min_le_left _ _
  have hqc : q ≤ c := min_le_right _ _
  set ε' : ℝ := q / 8 with hε'
  have hε'0 : 0 < ε' := by positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K : ℝ := 1 / (ε' * Real.log 2) + 1 with hK
  set C' : ℝ := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  obtain ⟨r₁, hr₁, hsmall⟩ := exists_pos_forall_rpow_le hζ0 (half_pos hr₀)
  refine polyHighProb_of_eventually (half_pos hq0) ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min (by norm_num : (0 : ℝ) < 1 / 2) hr₁),
    eventually_mul_rpow_le ((C' + 2) * K ^ 3) (a := q - 3 * ε') (b := q / 2) (by linarith)] with δ hδ hfin
  obtain ⟨hδ0, hδm⟩ := hδ
  have hδ2 : δ < 1 / 2 := hδm.trans_le (min_le_left _ _)
  have hδr₁ : δ < r₁ := hδm.trans_le (min_le_right _ _)
  have hδ1 : δ < 1 := by linarith
  have hδζ : δ ^ ζ < r₀ := (hsmall δ hδ0 hδr₁).trans_lt (half_lt_self hr₀)
  set ℓ := Real.log δ⁻¹ with hℓ
  have hℓ2 : Real.log 2 ≤ ℓ := Real.log_le_log (by norm_num)
    (by rw [le_inv_comm₀ (by norm_num) hδ0, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]; exact hδ2.le)
  have hℓ0 : 0 < ℓ := hlog2.trans_le hℓ2
  have hlogδ : Real.log δ = -ℓ := by rw [hℓ, Real.log_inv, neg_neg]
  set M : ℕ := ⌊ℓ / Real.log 2⌋₊ + 1 with hM
  have hMR : (M : ℝ) ≤ ℓ / Real.log 2 + 1 := by
    rw [hM, Nat.cast_add, Nat.cast_one]; gcongr; exact Nat.floor_le (by positivity)
  have hM1 : (1 : ℝ) ≤ M := by
    rw [hM, Nat.cast_add, Nat.cast_one]; linarith [Nat.cast_nonneg (α := ℝ) ⌊ℓ / Real.log 2⌋₊]
  have hkM : ∀ k : ℕ, δ ^ (1 - ζ) ≤ dyadicScale k → k < M := by
    intro k hk
    have hδk : δ ≤ (2 : ℝ)⁻¹ ^ k := by
      calc δ = δ ^ (1 : ℝ) := (Real.rpow_one δ).symm
        _ ≤ δ ^ (1 - ζ) := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le (by linarith)
        _ ≤ _ := hk
    have hlog : (k : ℝ) * Real.log 2 ≤ ℓ := by
      have := Real.log_le_log hδ0 hδk
      rw [Real.log_pow, Real.log_inv] at this
      linarith
    have : k ≤ ⌊ℓ / Real.log 2⌋₊ := Nat.le_floor (by rw [le_div_iff₀ hlog2]; exact hlog)
    omega
  set A : ℕ → Set Ω := fun k => (rescaledBallMassEvent γ hcirc μ₀ R βp βm k (δ / dyadicScale k))ᶜ ∪
      {ω | ζ / (2 * γ) * ℓ ≤ |hcirc ω (dyadicScale k) 0|} with hA
  set S := (Finset.range M).filter (fun k => δ ^ (1 - ζ) ≤ dyadicScale k) with hS
  have hγL : γ * (ζ / (2 * γ) * ℓ) = ζ / 2 * ℓ := by field_simp
  have hsub : (scaledGoodEvent γ hcirc μ₀ R βp βm ζ δ)ᶜ ⊆ ⋃ k ∈ S, A k := by
    intro ω hω
    simp only [scaledGoodEvent, mem_compl_iff, Set.mem_ofPred_eq, not_forall] at hω
    obtain ⟨k, hk, hk'⟩ := hω
    refine mem_iUnion₂.2 ⟨k, Finset.mem_filter.2 ⟨Finset.mem_range.2 (hkM k hk), hk⟩, ?_⟩
    by_contra hcon
    simp only [hA, mem_union, mem_compl_iff, not_or, not_not, Set.mem_ofPred_eq, not_le] at hcon
    obtain ⟨hDG, hX⟩ := hcon
    apply hk'
    refine ⟨hDG, ?_, ?_⟩
    · rw [Real.rpow_def_of_pos hδ0, hlogδ]
      apply Real.exp_le_exp.2
      have := mul_lt_mul_of_pos_left (abs_lt.1 hX).1 hγ
      linarith
    · rw [Real.rpow_def_of_pos hδ0, hlogδ]
      apply Real.exp_le_exp.2
      have := mul_lt_mul_of_pos_left (abs_lt.1 hX).2 hγ
      linarith
  have hAk : ∀ k ∈ S, P (A k) ≤ ENNReal.ofReal (C' * (M : ℝ) ^ 2 * δ ^ q + 2 * δ ^ q) := by
    intro k hk
    obtain ⟨hkM', hk⟩ := Finset.mem_filter.1 hk
    have hkM'' : (k : ℝ) + 1 ≤ M := by
      have := Finset.mem_range.1 hkM'; exact_mod_cast this
    have hτ0 := dyadicScale_pos k
    have hr0 : 0 < δ / dyadicScale k := div_pos hδ0 hτ0
    have hrζ : δ / dyadicScale k ≤ δ ^ ζ := by
      rw [← div_rpow_one_sub hδ0 ζ]
      exact div_le_div_of_nonneg_left hδ0.le (Real.rpow_pos_of_pos hδ0 _) hk
    have hrq : (δ / dyadicScale k) ^ p ≤ δ ^ q := by
      calc (δ / dyadicScale k) ^ p ≤ (δ ^ ζ) ^ p := Real.rpow_le_rpow hr0.le hrζ hp.le
        _ = δ ^ (ζ * p) := (Real.rpow_mul hδ0.le _ _).symm
        _ ≤ δ ^ q := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le hqp
    have hL0 : 0 ≤ ζ / (2 * γ) * ℓ := by positivity
    have hD : 2 * (((k : ℝ) + 1) * Real.log 2) ≤ 4 * ℓ := by
      have h1 : ((k : ℝ) + 1) * Real.log 2 ≤ (ℓ / Real.log 2 + 1) * Real.log 2 :=
        mul_le_mul_of_nonneg_right (hkM''.trans hMR) hlog2.le
      have h2 : (ℓ / Real.log 2 + 1) * Real.log 2 = ℓ + Real.log 2 := by field_simp
      rw [h2] at h1
      linarith
    have hL2 : (ζ / (2 * γ) * ℓ) ^ 2 = 4 * c * ℓ ^ 2 := by rw [hc]; field_simp; ring
    have hexp : -((ζ / (2 * γ) * ℓ) ^ 2) / (2 * (((k : ℝ) + 1) * Real.log 2)) ≤ Real.log δ * c := by
      rw [hlogδ, hL2, neg_div, neg_mul, neg_le_neg_iff, le_div_iff₀ (by positivity)]
      nlinarith [mul_nonneg (mul_nonneg hℓ0.le hc0.le) (sub_nonneg.2 hD)]
    calc P (A k) ≤ P (rescaledBallMassEvent γ hcirc μ₀ R βp βm k (δ / dyadicScale k))ᶜ +
          P {ω | ζ / (2 * γ) * ℓ ≤ |hcirc ω (dyadicScale k) 0|} := measure_union_le _ _
      _ ≤ ENNReal.ofReal (C * ((k : ℝ) + 1) ^ 2 * (δ / dyadicScale k) ^ p) +
          ENNReal.ofReal (2 * Real.exp (-((ζ / (2 * γ) * ℓ) ^ 2) /
            (2 * (((k : ℝ) + 1) * Real.log 2)))) :=
          add_le_add (hU k _ hr0 (hrζ.trans_lt hδζ)) (hT k _ hL0)
      _ ≤ ENNReal.ofReal (C' * (M : ℝ) ^ 2 * δ ^ q) + ENNReal.ofReal (2 * δ ^ q) := by
          refine add_le_add (ENNReal.ofReal_le_ofReal ?_) (ENNReal.ofReal_le_ofReal ?_)
          · calc C * ((k : ℝ) + 1) ^ 2 * (δ / dyadicScale k) ^ p
                ≤ C' * ((k : ℝ) + 1) ^ 2 * (δ / dyadicScale k) ^ p := by gcongr; exact le_max_left _ _
              _ ≤ C' * (M : ℝ) ^ 2 * δ ^ q := by gcongr
          · calc 2 * Real.exp (-((ζ / (2 * γ) * ℓ) ^ 2) / (2 * (((k : ℝ) + 1) * Real.log 2)))
                ≤ 2 * Real.exp (Real.log δ * c) := by gcongr
              _ = 2 * δ ^ c := by rw [Real.rpow_def_of_pos hδ0]
              _ ≤ 2 * δ ^ q :=
                  mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le hqc) (by norm_num)
      _ = _ := (ENNReal.ofReal_add (by positivity) (by positivity)).symm
  have hMK : (M : ℝ) ≤ K * δ ^ (-ε') := by
    have hlogle : ℓ ≤ δ ^ (-ε') / ε' := by
      have := Real.log_le_rpow_div (inv_nonneg.2 hδ0.le) hε'0
      rwa [Real.inv_rpow hδ0.le, ← Real.rpow_neg hδ0.le] at this
    have h1 : 1 ≤ δ ^ (-ε') := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ0 hδ1.le (by linarith)
    calc (M : ℝ) ≤ ℓ / Real.log 2 + 1 := hMR
      _ ≤ δ ^ (-ε') / ε' / Real.log 2 + δ ^ (-ε') := by gcongr
      _ = K * δ ^ (-ε') := by rw [hK]; field_simp
  have hM3 : (M : ℝ) ^ 3 ≤ K ^ 3 * δ ^ (-(3 * ε')) := by
    calc (M : ℝ) ^ 3 ≤ (K * δ ^ (-ε')) ^ 3 := pow_le_pow_left₀ (by positivity) hMK 3
      _ = K ^ 3 * δ ^ (-(3 * ε')) := by
          rw [mul_pow, ← Real.rpow_natCast (δ ^ (-ε')) 3, ← Real.rpow_mul hδ0.le]
          congr 2; push_cast; ring
  have hMM : (M : ℝ) ≤ (M : ℝ) ^ 3 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hM1) (by positivity : (0 : ℝ) ≤ (M : ℝ) * (M + 1))]
  have hreal : (M : ℝ) * (C' * (M : ℝ) ^ 2 * δ ^ q + 2 * δ ^ q) ≤ δ ^ (q / 2) := by
    have hδq : 0 ≤ δ ^ q := (Real.rpow_pos_of_pos hδ0 _).le
    calc (M : ℝ) * (C' * (M : ℝ) ^ 2 * δ ^ q + 2 * δ ^ q) = (C' * (M : ℝ) ^ 3 + 2 * M) * δ ^ q := by ring
      _ ≤ (C' * (M : ℝ) ^ 3 + 2 * (M : ℝ) ^ 3) * δ ^ q := by gcongr
      _ = (C' + 2) * (M : ℝ) ^ 3 * δ ^ q := by ring
      _ ≤ (C' + 2) * (K ^ 3 * δ ^ (-(3 * ε'))) * δ ^ q := by gcongr
      _ = (C' + 2) * K ^ 3 * δ ^ (q - 3 * ε') := by
          rw [sub_eq_add_neg, Real.rpow_add hδ0]; ring
      _ ≤ δ ^ (q / 2) := hfin
  calc P (scaledGoodEvent γ hcirc μ₀ R βp βm ζ δ)ᶜ ≤ P (⋃ k ∈ S, A k) := measure_mono hsub
    _ ≤ ∑ k ∈ S, P (A k) := measure_biUnion_finset_le S A
    _ ≤ ∑ _k ∈ S, ENNReal.ofReal (C' * (M : ℝ) ^ 2 * δ ^ q + 2 * δ ^ q) := Finset.sum_le_sum hAk
    _ = S.card • ENNReal.ofReal (C' * (M : ℝ) ^ 2 * δ ^ q + 2 * δ ^ q) := Finset.sum_const _
    _ ≤ M • ENNReal.ofReal (C' * (M : ℝ) ^ 2 * δ ^ q + 2 * δ ^ q) := by
        refine nsmul_le_nsmul_left (by positivity) ?_
        exact (Finset.card_filter_le _ _).trans (Finset.card_range M).le
    _ = ENNReal.ofReal ((M : ℝ) * (C' * (M : ℝ) ^ 2 * δ ^ q + 2 * δ ^ q)) := by
        rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    _ ≤ ENNReal.ofReal (δ ^ (q / 2)) := ENNReal.ofReal_le_ofReal hreal

/-- **Reduction**: the multiscale ball bound for `h^ℂ`
around the origin from the uniform rescaled bound (`RescaledBallMassUniformStepLP`) and the Gaussian tail of
`h^ℂ_{2^{-k}}(0)` (`CircleAverageDyadicTailStepLP`). -/
theorem wholePlaneScaledBallMassStep_of_uniform_lp (h1 : RescaledBallMassUniformStepLP.{u})
    (h2 : CircleAverageDyadicTailStepLP.{u}) : WholePlaneScaledBallMassStepLP.{u} := by
  intro γ hγ hγ2 Ω _ P hC hcirc μ₀ hGFF hμ₀ R hR βp βm ζ hβp hβpA hβm hζ0 hζ1
  obtain ⟨p, hp, C, r₀, hr₀, hU⟩ := h1 γ hγ hγ2 Ω P hC hcirc μ₀ hGFF hμ₀ R hR βp βm hβp hβpA hβm
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  have hG : 0 ≤ γ * lqgQ γ := by positivity
  have hβm0 : 0 ≤ βm := le_trans (by positivity) hβm.le
  have hgood := scaledGoodEvent_polyHighProb (P := P) (R := R) (βp := βp) (βm := βm) (μ₀ := μ₀)
    hγ hζ0 hp hr₀ hU (h2 Ω P hC hcirc hGFF)
  refine polyHighProb_mono_of_eventually hgood ?_
  filter_upwards [Ioo_mem_nhdsGT one_pos,
    eventually_mul_rpow_le (2 ^ (γ * lqgQ γ)) (a := ζ / 2) (b := 0) (by linarith),
    eventually_mul_rpow_le (2 ^ βm) (a := ζ / 2) (b := 0) (by linarith)] with δ hδ h2G h2βm
  rw [Real.rpow_zero] at h2G h2βm
  intro ω hω
  rw [Set.mem_ofPred_eq]
  intro t ht ht1 z hz
  exact scaledBallBound_of_good hβp hβm0 hδ.1 hG h2G h2βm hω ht ht1 hz

end LatticeProb.LQG.LQGMeasureNonatomicMass
