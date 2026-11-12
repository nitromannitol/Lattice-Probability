import Mathlib
import LatticeProb.LQG.LQGMassSquares
import LatticeProb.LQG.LQGMassAlgebra
import LatticeProb.LQG.LQGMassMoment

/-!
# Cross terms of the mass of a cut-off function against the approximate Liouville measure

Let `h` be a whole-plane Gaussian free field, `μ_n = lqgApprox γ h 2^{-n}` the approximate Liouville measure
at the dyadic scale `2^{-n}`, and `S_i` the half-open squares of side `r = 2^{-k}/4` meeting the disc
`closedBall 0 (1/2)`. The square masses `X_i = ∫_{S_i} f dμ_n` of a cut-off function `f` supported in the disc
satisfy the cross-term bound used for the positive moments of the mass: for a non-constant tuple
`g : Fin (m+1) → s` of indices of one parity class (so that the squares are `r`-separated),

`E ∏_j X_{g j} ≤ ((2/r)^{γ²})^{(m+1)²} · K^{m+1}`,

provided the moments `E (∫ f dμ'_{n-k})^a ≤ K` for the integer exponents `1 ≤ a ≤ m` hold for the
recentred and dilated fields `h'` at the centres of the squares, and `m γ² ≤ 4`.

* `LatticeProb.LQG.squareMass`: the mass `∫_{S_i} f dμ_n`.
* `LatticeProb.LQG.squareMass_eq_pieceMass`: it is the piece mass of the density `ε^{γ²/2} exp (γ H z ω)`
  when `H` is a version of the circle averages.
* `LatticeProb.LQG.IsWholePlaneGFF.lintegral_prod_squareMass_le`: the cross-term bound above, from the
  decoupling of the piece masses and the one-piece scaling estimate.
-/

open MeasureTheory Metric Set
open scoped ENNReal

namespace LatticeProb.LQG

open LatticeProb.Gauss LQGDyadicScaling LatticeProb

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The mass `∫_{S_i} f dμ_n` of the dyadic square `i` of side `r` against the approximate Liouville
measure at the dyadic scale `2^{-n}`. -/
noncomputable def squareMass (γ : ℝ) (h : ℝ → ℂ → ℝ) (f : ℂ → ℝ≥0∞) (r : ℝ) (i : ℤ × ℤ) (n : ℕ) :
    ℝ≥0∞ :=
  ∫⁻ x in dyadicSquare r i, f x ∂(lqgApprox γ h (dyadicScale n))

omit [MeasurableSpace Ω] in
/-- The square mass is the piece mass of the density `ε^{γ²/2} exp (γ H z ω)` for the weight
`1_{S_i} f`, when `H · ω` is a measurable version of the circle averages at the scale `ε = 2^{-n}`. -/
theorem squareMass_eq_pieceMass {γ : ℝ} {h : ℝ → ℂ → ℝ} {n : ℕ} {f : ℂ → ℝ≥0∞} (hfm : Measurable f)
    (r : ℝ) (i : ℤ × ℤ) (H : ℂ → Ω → ℝ) (ω : Ω) (hHx : Measurable fun z => H z ω)
    (hHh : ∀ z, H z ω = h (dyadicScale n) z) :
    squareMass γ h f r i n =
      pieceMass (fun j => (dyadicSquare r j).indicator f) (gmcDensityENN H γ (dyadicScale n)) i ω := by
  have hd : Measurable fun x => gmcDensityENN H γ (dyadicScale n) x ω := by
    unfold gmcDensityENN
    exact (by fun_prop : Measurable fun z => dyadicScale n ^ (γ ^ 2 / 2) * Real.exp (γ * H z ω)).ennreal_ofReal
  have e : (fun z => ENNReal.ofReal (dyadicScale n ^ (γ ^ 2 / 2) * Real.exp (γ * h (dyadicScale n) z))) =
      fun z => gmcDensityENN H γ (dyadicScale n) z ω := by
    funext z
    simp only [gmcDensityENN, hHh]
  unfold squareMass pieceMass lqgApprox
  rw [← lintegral_indicator (measurableSet_dyadicSquare r i), e,
    lintegral_withDensity_eq_lintegral_mul _ hd (hfm.indicator (measurableSet_dyadicSquare r i))]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply]
  exact mul_comm _ _

/-- **Cross terms.** Let `r = 2^{-k}/4`, `2 ≤ k < n`, `f` a measurable cut-off (`f ≤ 1`, `f ≥ 1` on `B(0, 1/4)`,
`f = 0` off `closedBall 0 (1/2)`), `m γ² ≤ 4`, and suppose that the recentred fields satisfy the moment bounds
`E (∫ f dμ'_{n-k})^a ≤ K` for all `1 ≤ a ≤ m` at all centres of the squares. Then for a non-constant tuple
`g` of squares of one parity class, `E ∏_{j ≤ m} X_{g j} ≤ ((2/r)^{γ²})^{(m+1)²} K^{m+1}`. -/
theorem IsWholePlaneGFF.lintegral_prod_squareMass_le [IsProbabilityMeasure P]
    (hh : IsWholePlaneGFF P hC hcirc) {γ : ℝ} (hγ : γ ≠ 0) {f : ℂ → ℝ≥0∞} (hfm : Measurable f)
    (hf1 : ∀ x, f x ≤ 1) (hf14 : ∀ x ∈ ball (0 : ℂ) (1 / 4), 1 ≤ f x)
    (hf0 : ∀ x ∉ closedBall (0 : ℂ) (1 / 2), f x = 0) {k n : ℕ} (hk : 2 ≤ k) (hkn : k < n)
    {m : ℕ} (hm : (m : ℝ) * γ ^ 2 ≤ 4) {K : ℝ} (hK : 1 ≤ K)
    (hIH : ∀ a : ℕ, 1 ≤ a → a ≤ m → ∀ i ∈ squareIndex (dyadicScale k * (1 / 4)),
      ∫⁻ ω, (lqgApproxMass γ (recentredField hcirc k
        (dyadicSquareCentre (dyadicScale k * (1 / 4)) i) ω) f (n - k)) ^ (a : ℝ) ∂P ≤
        ENNReal.ofReal K)
    {s : Finset (ℤ × ℤ)} (hs : s ⊆ squareIndex (dyadicScale k * (1 / 4)))
    (hcls : ∀ i ∈ s, ∀ j ∈ s, squareClass i = squareClass j) {g : Fin (m + 1) → ℤ × ℤ}
    (hg : g ∈ nonconstTuples s (m + 1)) :
    ∫⁻ ω, ∏ j, squareMass γ (hcirc ω) f (dyadicScale k * (1 / 4)) (g j) n ∂P ≤
      ENNReal.ofReal ((2 / (dyadicScale k * (1 / 4))) ^ γ ^ 2) ^ ((m + 1) * (m + 1)) *
        ENNReal.ofReal K ^ (m + 1) := by
  classical
  set r : ℝ := dyadicScale k * (1 / 4) with hrdef
  set ε : ℝ := dyadicScale n with hεdef
  have hR : 0 < dyadicScale k := dyadicScale_pos' k
  have hR4 : dyadicScale k ≤ 1 / 4 := by
    have h2 : dyadicScale 2 = 1 / 4 := by norm_num [dyadicScale]
    exact h2 ▸ dyadicScale_le_of_le hk
  have hr : 0 < r := by rw [hrdef]; positivity
  have hr2 : r ≤ 2 := by rw [hrdef]; linarith
  have hε : 0 < ε := dyadicScale_pos' n
  have hε2 : ε ≤ 1 / 2 := by
    obtain ⟨l, hl⟩ : ∃ l, n = l + 1 := ⟨n - 1, by omega⟩
    rw [hεdef, hl, dyadicScale_succ_eq_half]
    have := dyadicScale_le_one' l
    linarith
  have hgs : ∀ j, g j ∈ s := (mem_nonconstTuples.1 hg).1
  obtain ⟨H, hHc, hHm, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  let w : s → ℂ → ℝ≥0∞ := fun i => (dyadicSquare r i.1).indicator f
  let S : s → Set ℂ := fun i => dyadicSquare r i.1 ∩ closedBall 0 (1 / 2)
  have hw : ∀ i, Measurable (w i) := fun i => hfm.indicator (measurableSet_dyadicSquare r i.1)
  have hwS : ∀ i a, w i a ≠ 0 → a ∈ S i := by
    intro i a ha
    by_contra hcon
    apply ha
    simp only [w, Set.indicator]
    split_ifs with h1
    · exact hf0 a fun h2 => hcon ⟨h1, h2⟩
    · rfl
  have hin : ∀ i, ∀ a ∈ S i, ‖a‖ + ε ≤ 1 := fun i a ha => by
    have : ‖a‖ ≤ 1 / 2 := by simpa using ha.2
    linarith
  have hsep : ∀ i i', i ≠ i' → ∀ a ∈ S i, ∀ b ∈ S i', r ≤ ‖a - b‖ := fun i i' hne a ha b hb =>
    le_norm_sub_of_squareClass_eq hr (fun h => hne (Subtype.ext h)) (hcls _ i.2 _ i'.2) ha.1 hb.1
  let lab : Fin (m + 1) → s := fun j => ⟨g j, hgs j⟩
  let T : Finset s := Finset.univ.image lab
  have hdec := hh.lintegral_prod_pieceMass_gmc_le (H := fun z ω => H ω ε z) (hHm ε hε) hε hr hr2 γ
    (fun z => by filter_upwards [hHae] with ω hω; exact hω ε z) hw S hwS hin hsep T (Fin (m + 1)) lab
    (fun j => Finset.mem_image_of_mem _ (Finset.mem_univ j))
  have hlink : ∀ᵐ ω ∂P, ∀ i : s, squareMass γ (hcirc ω) f r i.1 n =
      pieceMass w (gmcDensityENN (fun z ω => H ω ε z) γ ε) i ω := by
    filter_upwards [hHae] with ω hω i
    exact squareMass_eq_pieceMass hfm r i.1 (fun z ω => H ω ε z) ω
      ((hHm ε hε).comp (measurable_id.prodMk measurable_const)) fun z => hω ε z
  have hfac : ∀ i ∈ T, ∫⁻ ω, pieceMass w (gmcDensityENN (fun z ω => H ω ε z) γ ε) i ω ^
      Nat.card {j // lab j = i} ∂P ≤ ENNReal.ofReal K := by
    intro i hiT
    obtain ⟨j0, -, rfl⟩ := Finset.mem_image.1 hiT
    have heq : Nat.card {j // lab j = lab j0} = Nat.card {j // g j = g j0} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun j => by simp [lab, Subtype.ext_iff])
    have hlt : Nat.card {j // lab j = lab j0} < m + 1 := heq ▸ nat_card_fibre_lt hg (g j0)
    have h1 : 1 ≤ Nat.card {j // lab j = lab j0} :=
      Nat.card_pos_iff.2 ⟨⟨⟨j0, rfl⟩⟩, inferInstance⟩
    set a := Nat.card {j // lab j = lab j0} with ha
    have hgi : g j0 ∈ squareIndex r := hs (hgs j0)
    have hz : ‖dyadicSquareCentre r (g j0)‖ + dyadicScale k ≤ 1 := by
      have := norm_dyadicSquareCentre_lt hr hgi
      rw [hrdef] at this
      linarith
    have hζ : 0 ≤ (a : ℝ) * (2 + γ ^ 2 / 2) - (a : ℝ) ^ 2 * γ ^ 2 / 2 := by
      have ham : (a : ℝ) ≤ m := by exact_mod_cast (by omega : a ≤ m)
      have h0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
      have hag : (a : ℝ) * γ ^ 2 ≤ 4 :=
        (mul_le_mul_of_nonneg_right ham (sq_nonneg γ)).trans hm
      have : (a : ℝ) * (2 + γ ^ 2 / 2) - (a : ℝ) ^ 2 * γ ^ 2 / 2 =
          a * (2 - a * γ ^ 2 / 2 + γ ^ 2 / 2) := by ring
      rw [this]
      exact mul_nonneg h0 (by nlinarith [sq_nonneg γ])
    calc ∫⁻ ω, pieceMass w (gmcDensityENN (fun z ω => H ω ε z) γ ε) (lab j0) ω ^ a ∂P
        = ∫⁻ ω, (∫⁻ x in dyadicSquare r (g j0), f x ∂(lqgApprox γ (hcirc ω) (dyadicScale n))) ^
            (a : ℝ) ∂P := by
          refine lintegral_congr_ae ?_
          filter_upwards [hlink] with ω hω
          rw [← hω (lab j0), ENNReal.rpow_natCast]
          rfl
      _ ≤ ENNReal.ofReal (dyadicScale k ^ ((a : ℝ) * (2 + γ ^ 2 / 2) - (a : ℝ) ^ 2 * γ ^ 2 / 2)) *
            ∫⁻ ω, (lqgApproxMass γ (recentredField hcirc k (dyadicSquareCentre r (g j0)) ω) f
              (n - k)) ^ (a : ℝ) ∂P :=
          LatticeProb.LQG.IsWholePlaneGFF.lintegral_rpow_setLIntegral_le hh hγ (Nat.cast_nonneg a)
            hkn hz (dyadicSquare_subset_ball hr (g j0)) hf1 hf14
      _ ≤ 1 * ENNReal.ofReal K := by
          refine mul_le_mul' ?_ (hIH a h1 (by omega) (g j0) hgi)
          exact ENNReal.ofReal_le_one.2
            (Real.rpow_le_one hR.le (dyadicScale_le_one' k) hζ)
      _ = ENNReal.ofReal K := one_mul _
  calc ∫⁻ ω, ∏ j, squareMass γ (hcirc ω) f r (g j) n ∂P
      = ∫⁻ ω, ∏ j, pieceMass w (gmcDensityENN (fun z ω => H ω ε z) γ ε) (lab j) ω ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hlink] with ω hω
        exact Finset.prod_congr rfl fun j _ => hω (lab j)
    _ ≤ _ := hdec
    _ ≤ ENNReal.ofReal ((2 / r) ^ γ ^ 2) ^ ((m + 1) * (m + 1)) * ENNReal.ofReal K ^ (m + 1) := by
        have hc : Nat.card (Fin (m + 1)) = m + 1 := by simp
        rw [hc]
        refine mul_le_mul' le_rfl ?_
        calc ∏ i ∈ T, ∫⁻ ω, pieceMass w (gmcDensityENN (fun z ω => H ω ε z) γ ε) i ω ^
              Nat.card {j // lab j = i} ∂P ≤ ∏ i ∈ T, ENNReal.ofReal K :=
            Finset.prod_le_prod hfac
          _ = ENNReal.ofReal K ^ T.card := Finset.prod_const _
          _ ≤ ENNReal.ofReal K ^ (m + 1) := by
            refine pow_le_pow_right₀ (ENNReal.one_le_ofReal.2 hK) ?_
            exact (Finset.card_image_le).trans (by simp)

end LatticeProb.LQG
