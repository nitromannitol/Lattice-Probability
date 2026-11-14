import LatticeProb.Prob.CorrelatedBMRegularPaths

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

## Main results
* `CauchyPointPolarInput`: the literature input above.
* `lastBelow_increment_div`, `firstBelow_increment_div`: the transport of straddling pairs, given points at or below
  the level on the relevant side of `q`.
* `apply_lastBelow_ne_of_increment_div`: if the rescaled increments `F`, `G` of `f`, `g` after time `q` satisfy the
  conclusion of the literature input, and `F` is unbounded below on both sides of `0`, then `g` takes distinct values
  at the two ends of every straddling pair of `f` at time `q`.
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

end LatticeProb.CorrelatedBM
