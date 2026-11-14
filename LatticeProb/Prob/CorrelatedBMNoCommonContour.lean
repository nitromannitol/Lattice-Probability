import LatticeProb.Prob.CorrelatedBMCommonContourStraddle
import LatticeProb.Prob.CorrelatedBMWhitening

/-!
# No common weak contour pair of a correlated Brownian pair, from the polarity of points for the Cauchy process

Let `μ` be the law of the two-sided correlated Brownian pair `(L, R)` (`IsCorrelatedBM2 γ μ`), and write
`U = L + R` and `V = L - R`.

* **Literature input** (`CauchyPointPolarInput`). For two independent two-sided standard Brownian motions `(L, R)`
  (the case `γ = √2`), almost surely, for every level `l < 0`, the values of `R` at the two ends of the straddling pair
  `(lastBelow L 0 l, firstBelow L 0 l)` of `L` at time `0` differ. Writing `T_a = firstBelow L 0 (-a)` and
  `-T'_a = lastBelow L 0 (-a)`, this says that `R (T_a) - R (-T'_a)` never vanishes for `a > 0`; the process
  `a ↦ R (T_a) - R (-T'_a)` is a symmetric Cauchy process (taken left continuous), and points are polar for it
  (Aïdékon–Da Silva, arXiv:2005.06372, proof of Prop. 2.7, p. 7; Bertoin, *Lévy processes*, 1996, Ch. II §5).
* **Transport of straddling pairs** (deterministic). Straddling pairs commute with time shifts and with increasing
  affine maps of the values: for `c > 0`, the straddling pair of `u ↦ (f (q + u) - f q) / c` at time `0` at the level
  `(l - f q) / c` is the straddling pair of `f` at time `q` at the level `l`, shifted by `-q`.
* **No common weak contour pair.** For `0 < γ < 2`, a common weak contour pair of `L` and `R` produces a rational
  time `q` and a level `l < U q` such that `V` takes the same value at both ends of the straddling pair of `U` at `q`
  (`exists_rat_straddle_of_not_noCommonWeakContourPair`). The whitening at `q` (`whitenAt γ q`) maps the law of
  `(L, R)` to the law of two independent two-sided standard Brownian motions, with first coordinate the rescaled
  increment of `U` after `q` and second coordinate that of `V`. Its first coordinate is almost surely unbounded below on
  both sides of `0`, so by the transport of straddling pairs the literature input applies at each rational time `q`;
  the union over `q ∈ ℚ` is null.

## Main results
* `CauchyPointPolarInput`: the literature input above.
* `lastBelow_increment_div`, `firstBelow_increment_div`: the transport of straddling pairs, given points at or below
  the level on the relevant side of `q`.
* `apply_lastBelow_ne_of_increment_div`: if the rescaled increments `F`, `G` of `f`, `g` after time `q` satisfy the
  conclusion of the literature input, and `F` is unbounded below on both sides of `0`, then `g` takes distinct values
  at the two ends of every straddling pair of `f` at time `q`.
* `one_add_lrCov_pos`: for `0 < γ < 2`, the correlation `lrCov γ 0 1 = -cos(πγ²/4)` exceeds `-1`.
* `ae_noCommonWeakContourPair_of_cauchyPointPolar`: given the literature input, for `0 < γ < 2` the two coordinates of
  the correlated Brownian pair almost surely have no common weak contour pair.
* `hNC_of_cauchyPointPolar`: the same, for all `γ ∈ (0, 2)` and all laws `μ` at once.
-/

set_option autoImplicit false

open Set MeasureTheory ProbabilityTheory

namespace LatticeProb.CorrelatedBM

open MatedCRTHarmonic.MatedCRT

/-- **Polarity of points for the Cauchy process of a Brownian pair at the passage times** (literature input).
For the law `μ` of two independent two-sided standard Brownian motions `(L, R)` (`IsCorrelatedBM2 (√2) μ`), almost
surely, for every level `l < 0`, the second coordinate `R` takes distinct values at the two ends of the straddling pair
`(lastBelow L 0 l, firstBelow L 0 l)` of the first coordinate `L` at time `0`.

Source: E. Aïdékon and W. Da Silva, *Growth-fragmentation process embedded in a planar Brownian excursion*,
arXiv:2005.06372, proof of Prop. 2.7, p. 7: with `T_a` and `T'_a` the hitting times of `a` by two independent
Brownian motions and `X`, `X'` two further independent Brownian motions, `X_{T_a}` and `X'_{T'_a}` are independent
symmetric Cauchy processes, so `X_{T_a} - X'_{T'_a}` is a Cauchy process, and points are polar for the symmetric
Cauchy process (J. Bertoin, *Lévy processes*, 1996, Ch. II §5); hence `P(∃ 0 < a ≤ α, X_{T_a} = X'_{T'_a}) = 0`.
Here `X`, `X'` are the forward and backward halves of `R` from `0`, `T_a = firstBelow L 0 (-a)` and
`-T'_a = lastBelow L 0 (-a)`, and the union is over `α ∈ ℕ`. -/
def CauchyPointPolarInput : Prop :=
  ∀ μ : Measure Path2, IsCorrelatedBM2 (Real.sqrt 2) μ → ∀ᵐ ω ∂μ, ∀ l : ℝ, l < 0 →
    lrCoord 1 (LatticeProb.lastBelow (fun u => lrCoord 0 u ω) 0 l) ω ≠
      lrCoord 1 (LatticeProb.firstBelow (fun u => lrCoord 0 u ω) 0 l) ω

/-- Comparison of rescaled increments: for `c > 0`, `(f (q + u) - f q) / c ≤ (l - f q) / c` if and only if
`f (q + u) ≤ l`. -/
theorem increment_div_le_iff {f : ℝ → ℝ} {q u l c : ℝ} (hc : 0 < c) :
    (f (q + u) - f q) / c ≤ (l - f q) / c ↔ f (q + u) ≤ l := by
  rw [div_le_div_iff_of_pos_right hc, sub_le_sub_iff_right]

/-- **Transport of the left end of a straddling pair.** For `c > 0`, if `f ≤ l` somewhere at or before `q`, then the
last time at or before `0` at which `u ↦ (f (q + u) - f q) / c` is at most `(l - f q) / c` is
`lastBelow f q l - q`. -/
theorem lastBelow_increment_div {f : ℝ → ℝ} {q l c : ℝ} (hc : 0 < c) (ha : ∃ a ≤ q, f a ≤ l) :
    lastBelow (fun u => (f (q + u) - f q) / c) 0 ((l - f q) / c) = lastBelow f q l - q := by
  obtain ⟨a, haq, hfa⟩ := ha
  have e : ∀ x, q + (x - q) = x := fun x => by ring
  refine le_antisymm (csSup_le ⟨a - q, by linarith, ?_⟩ fun u hu => ?_) ?_
  · show (f (q + (a - q)) - f q) / c ≤ (l - f q) / c
    rwa [increment_div_le_iff hc, e]
  · have := le_lastBelow (f := f) (by linarith [hu.1] : q + u ≤ q)
      ((increment_div_le_iff (f := f) (q := q) (u := u) (l := l) hc).1 hu.2)
    linarith
  · refine sub_le_iff_le_add.2 (csSup_le ⟨a, haq, hfa⟩ fun w hw => ?_)
    have := le_lastBelow (f := fun u => (f (q + u) - f q) / c) (l := (l - f q) / c)
      (by linarith [hw.1] : w - q ≤ 0)
      (by show (f (q + (w - q)) - f q) / c ≤ (l - f q) / c; rw [increment_div_le_iff hc, e]; exact hw.2)
    linarith

/-- **Transport of the right end of a straddling pair.** For `c > 0`, if `f ≤ l` somewhere at or after `q`, then the
first time at or after `0` at which `u ↦ (f (q + u) - f q) / c` is at most `(l - f q) / c` is
`firstBelow f q l - q`. -/
theorem firstBelow_increment_div {f : ℝ → ℝ} {q l c : ℝ} (hc : 0 < c) (hb : ∃ b, q ≤ b ∧ f b ≤ l) :
    firstBelow (fun u => (f (q + u) - f q) / c) 0 ((l - f q) / c) = firstBelow f q l - q := by
  obtain ⟨b, hqb, hfb⟩ := hb
  have e : ∀ x, q + (x - q) = x := fun x => by ring
  refine le_antisymm ?_ (le_csInf ⟨b - q, by linarith, ?_⟩ fun u hu => ?_)
  · refine le_sub_iff_add_le.2 (le_csInf ⟨b, hqb, hfb⟩ fun w hw => ?_)
    have := firstBelow_le (f := fun u => (f (q + u) - f q) / c) (l := (l - f q) / c)
      (by linarith [hw.1] : 0 ≤ w - q)
      (by show (f (q + (w - q)) - f q) / c ≤ (l - f q) / c; rw [increment_div_le_iff hc, e]; exact hw.2)
    linarith
  · show (f (q + (b - q)) - f q) / c ≤ (l - f q) / c
    rwa [increment_div_le_iff hc, e]
  · have := firstBelow_le (f := f) (by linarith [hu.1] : q ≤ q + u)
      ((increment_div_le_iff (f := f) (q := q) (u := u) (l := l) hc).1 hu.2)
    linarith

/-- **Distinct values at the ends of the straddling pairs, from the rescaled increments** (deterministic). Let
`F u = (f (q + u) - f q) / c` with `c > 0` and `G u = (g (q + u) - g q) / d`. If `F` is unbounded below on both sides
of `0`, and `G` takes distinct values at the two ends of every straddling pair of `F` at `0` at a level `l' < 0`, then
`g` takes distinct values at the two ends of every straddling pair of `f` at `q` at a level `l < f q`. -/
theorem apply_lastBelow_ne_of_increment_div {f g F G : ℝ → ℝ} {q c d : ℝ} (hc : 0 < c)
    (hF : ∀ u, F u = (f (q + u) - f q) / c) (hG : ∀ u, G u = (g (q + u) - g q) / d)
    (hlow : ∀ l' : ℝ, (∃ a ≤ 0, F a ≤ l') ∧ ∃ b, 0 ≤ b ∧ F b ≤ l')
    (hCP : ∀ l' : ℝ, l' < 0 → G (lastBelow F 0 l') ≠ G (firstBelow F 0 l')) {l : ℝ} (hl : l < f q) :
    g (lastBelow f q l) ≠ g (firstBelow f q l) := by
  obtain rfl : F = fun u => (f (q + u) - f q) / c := funext hF
  intro heq
  obtain ⟨⟨a, ha0, hFa⟩, b, hb0, hFb⟩ := hlow ((l - f q) / c)
  have ha : ∃ a ≤ q, f a ≤ l :=
    ⟨q + a, by linarith, (increment_div_le_iff (f := f) (q := q) (u := a) (l := l) hc).1 hFa⟩
  have hb : ∃ b, q ≤ b ∧ f b ≤ l :=
    ⟨q + b, by linarith, (increment_div_le_iff (f := f) (q := q) (u := b) (l := l) hc).1 hFb⟩
  have e : ∀ x, q + (x - q) = x := fun x => by ring
  refine hCP _ (div_neg_of_neg_of_pos (sub_neg.2 hl) hc) ?_
  rw [lastBelow_increment_div hc ha, firstBelow_increment_div hc hb, hG, hG, e, e, heq]

/-- **The correlation exceeds `-1`.** For `0 < γ < 2`, `πγ²/4 ∈ (0, π)`, so `cos(πγ²/4) < 1` and the correlation
`lrCov γ 0 1 = -cos(πγ²/4)` of the coordinates satisfies `1 + lrCov γ 0 1 > 0`: the sum coordinate `U = L + R` has
positive variance. -/
theorem one_add_lrCov_pos {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2) : 0 < 1 + lrCov γ 0 1 := by
  have hθ0 : 0 < Real.pi * γ ^ 2 / 4 := by
    have := mul_pos Real.pi_pos (pow_pos hγ0 2)
    linarith
  have hγ4 : γ ^ 2 < 4 := by nlinarith [mul_pos hγ0 (sub_pos.2 hγ2)]
  have hθπ : Real.pi * γ ^ 2 / 4 < Real.pi := by nlinarith [mul_pos Real.pi_pos (sub_pos.2 hγ4)]
  have h := Real.cos_lt_cos_of_nonneg_of_le_pi le_rfl hθπ.le hθ0
  rw [Real.cos_zero] at h
  have hρ : lrCov γ 0 1 = -Real.cos (Real.pi * γ ^ 2 / 4) := rfl
  rw [hρ]
  linarith

/-- **No common weak contour pair, from the polarity of points for the Cauchy process.** Given the literature input
`CauchyPointPolarInput`, for `0 < γ < 2` the two coordinates `L`, `R` of the correlated Brownian pair almost surely have
no common weak contour pair.

Almost surely no coordinate has a flat rational increment (`ae_lrCoord_ne_of_rat_lt`), and for each rational `q` the
whitened path `whitenAt γ q ω`, whose law is that of two independent two-sided standard Brownian motions
(`isCorrelatedBM2_map_whitenAt`), satisfies the literature input and has first coordinate unbounded below on both
sides of `0` (`ae_coordinate_low`). A common weak contour pair gives a rational `q` and a level `l < U q` at which `V`
takes the same value at both ends of the straddling pair of `U` at `q`
(`exists_rat_straddle_of_not_noCommonWeakContourPair`), which the transport of straddling pairs
(`apply_lastBelow_ne_of_increment_div`) excludes. -/
theorem ae_noCommonWeakContourPair_of_cauchyPointPolar (hCP : CauchyPointPolarInput) {γ : ℝ} (hγ0 : 0 < γ)
    (hγ2 : γ < 2) {μ : Measure Path2} (hμ : IsCorrelatedBM2 γ μ) : ∀ᵐ ω ∂μ, NoCommonWeakContourPair ω := by
  have hq : ∀ q : ℚ, ∀ᵐ ω ∂μ,
      (∀ l : ℝ, l < 0 →
        lrCoord 1 (lastBelow (fun u => lrCoord 0 u (whitenAt γ q ω)) 0 l) (whitenAt γ q ω) ≠
          lrCoord 1 (firstBelow (fun u => lrCoord 0 u (whitenAt γ q ω)) 0 l) (whitenAt γ q ω)) ∧
      ∀ w l : ℝ, (∃ a ≤ w, lrCoord 0 a (whitenAt γ q ω) ≤ l) ∧
        ∃ b, w ≤ b ∧ lrCoord 0 b (whitenAt γ q ω) ≤ l := by
    intro q
    have hν := isCorrelatedBM2_map_whitenAt hγ0 hγ2 (q : ℝ) hμ
    have h := ae_of_ae_map (continuous_whitenAt γ q).measurable.aemeasurable
      ((hCP _ hν).and (ae_coordinate_low hν 0))
    exact h
  have hc : 0 < Real.sqrt (2 * (1 + lrCov γ 0 1)) :=
    Real.sqrt_pos.2 (by linarith [one_add_lrCov_pos hγ0 hγ2])
  filter_upwards [ae_lrCoord_ne_of_rat_lt hμ, ae_all_iff.2 hq] with ω h0 hω
  by_contra h
  obtain ⟨q, l, hl, heq⟩ := exists_rat_straddle_of_not_noCommonWeakContourPair ω h0 h
  exact apply_lastBelow_ne_of_increment_div (f := fun u => lrCoord 0 u ω + lrCoord 1 u ω)
    (g := fun u => lrCoord 0 u ω - lrCoord 1 u ω) (F := fun u => lrCoord 0 u (whitenAt γ q ω))
    (G := fun u => lrCoord 1 u (whitenAt γ q ω)) hc (fun u => lrCoord_zero_whitenAt γ q u ω)
    (fun u => lrCoord_one_whitenAt γ q u ω) (fun l' => (hω q).2 0 l') (hω q).1 hl heq

/-- **No common weak contour pair, for all correlation parameters at once.** Given the literature input
`CauchyPointPolarInput`, for every `γ ∈ (0, 2)` and every law `μ` of the correlated Brownian pair with parameter `γ`,
the two coordinates almost surely have no common weak contour pair. -/
theorem hNC_of_cauchyPointPolar (hCP : CauchyPointPolarInput) : ∀ γ : ℝ, 0 < γ → γ < 2 →
    ∀ μ : Measure Path2, IsCorrelatedBM2 γ μ → ∀ᵐ ω ∂μ, NoCommonWeakContourPair ω :=
  fun _ hγ0 hγ2 _ hμ => ae_noCommonWeakContourPair_of_cauchyPointPolar hCP hγ0 hγ2 hμ

end LatticeProb.CorrelatedBM
