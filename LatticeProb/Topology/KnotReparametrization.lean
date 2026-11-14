import Mathlib

/-!
# Reparametrizing one path along the knots of another

Let `τ` and `σ` be strictly increasing knot sequences in `[0, ∞)` starting at `0` and tending to
infinity. The piecewise-linear map `knotMap τ σ` sending `τ n ↦ σ n` and `[τ n, τ (n+1))` affinely onto
`[σ n, σ (n+1))` is an order isomorphism of `ℝ≥0` (`knotOrderIso`).

Consequently, if a path `f` stays within `a` of an anchor point `p n` on each knot interval
`[τ n, τ (n+1))`, a path `g` stays within `a` of `q n` on `[σ n, σ (n+1))`, and the anchors satisfy
`dist (p n) (q n) ≤ δ`, then `g ∘ φ` is uniformly within `a + δ + a` of `f` for an increasing
homeomorphism `φ` of `[0, ∞)` (`exists_orderIso_dist_le_of_knots`). This is the deterministic step
behind the comparison of paths modulo time parametrization from the comparison of their positions at
a chain of exit times, when both paths have small oscillation between consecutive exit times
(Gwynne–Miller–Sheffield, *An invariance principle for ergodic scale-free random environments*,
arXiv:1807.07515, end of the proof of Theorem 3.10).

`exists_orderIso_dist_le_of_finite_knots` is the version for finitely many knots `τ 0, …, τ N`
(strictly increasing), with tail conditions on `[τ N, ∞)` and `[σ N, ∞)`, as for stopped paths.
-/

namespace LatticeProb.KnotReparam

open Set Function
open scoped NNReal

open Classical in
/-- The index `k` of the knot interval `[τ k, τ (k+1))` containing `t` (the least `k` with
`t < τ (k+1)`); junk value `0` if there is none. -/
noncomputable def knotIndex (τ : ℕ → ℝ≥0) (t : ℝ≥0) : ℕ :=
  if h : ∃ n, t < τ (n + 1) then Nat.find h else 0

theorem knotIndex_eq {τ : ℕ → ℝ≥0} (hτ : StrictMono τ) {t : ℝ≥0} {n : ℕ} (h1 : τ n ≤ t)
    (h2 : t < τ (n + 1)) : knotIndex τ t = n := by
  have h : ∃ m, t < τ (m + 1) := ⟨n, h2⟩
  unfold knotIndex
  split_ifs
  rw [Nat.find_eq_iff]
  exact ⟨h2, fun m hm => not_lt.2 (le_trans (hτ.monotone (Nat.succ_le_of_lt hm)) h1)⟩

/-- Every `t ≥ 0` lies in a knot interval. -/
theorem exists_knot_bracket {τ : ℕ → ℝ≥0} (hτ0 : τ 0 = 0) (hτu : ∀ b, ∃ n, b < τ n) (t : ℝ≥0) :
    ∃ n, τ n ≤ t ∧ t < τ (n + 1) := by
  classical
  have h : ∃ m, t < τ m := hτu t
  have hm0 : Nat.find h ≠ 0 := by
    intro h0
    have := Nat.find_spec h
    rw [h0, hτ0] at this
    exact absurd this (by simp)
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  refine ⟨j, not_lt.1 (Nat.find_min h (by omega)), ?_⟩
  have := Nat.find_spec h
  rwa [hj] at this

theorem knotIndex_bracket {τ : ℕ → ℝ≥0} (hτ : StrictMono τ) (hτ0 : τ 0 = 0)
    (hτu : ∀ b, ∃ n, b < τ n) (t : ℝ≥0) :
    τ (knotIndex τ t) ≤ t ∧ t < τ (knotIndex τ t + 1) := by
  obtain ⟨n, h1, h2⟩ := exists_knot_bracket hτ0 hτu t
  rw [knotIndex_eq hτ h1 h2]
  exact ⟨h1, h2⟩

/-- The affine map of `[a, b)` onto `[c, d)` maps into `[c, d)`. -/
theorem affine_mem_Ico {x a b c d : ℝ} (hab : a < b) (hcd : c < d) (hx : a ≤ x) (hx' : x < b) :
    c ≤ c + (x - a) / (b - a) * (d - c) ∧ c + (x - a) / (b - a) * (d - c) < d := by
  have hl0 : 0 ≤ (x - a) / (b - a) := div_nonneg (by linarith) (by linarith)
  have hl1 : (x - a) / (b - a) < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have hdc : 0 < d - c := by linarith
  refine ⟨by nlinarith, ?_⟩
  have := mul_lt_of_lt_one_left hdc hl1
  linarith

/-- The real formula of the piecewise-linear map on the knot interval of `t`. -/
noncomputable def knotMapReal (τ σ : ℕ → ℝ≥0) (t : ℝ≥0) : ℝ :=
  (σ (knotIndex τ t) : ℝ) + ((t : ℝ) - τ (knotIndex τ t)) /
    ((τ (knotIndex τ t + 1) : ℝ) - τ (knotIndex τ t)) *
    ((σ (knotIndex τ t + 1) : ℝ) - σ (knotIndex τ t))

/-- The piecewise-linear map sending `τ n ↦ σ n`, affine on each knot interval `[τ n, τ (n+1))`. -/
noncomputable def knotMap (τ σ : ℕ → ℝ≥0) (t : ℝ≥0) : ℝ≥0 :=
  (knotMapReal τ σ t).toNNReal

theorem coe_knotMap_of_mem {τ σ : ℕ → ℝ≥0} (hτ : StrictMono τ) (hσ : StrictMono σ) {t : ℝ≥0}
    {n : ℕ} (h1 : τ n ≤ t) (h2 : t < τ (n + 1)) :
    (knotMap τ σ t : ℝ) = (σ n : ℝ) + ((t : ℝ) - τ n) / ((τ (n + 1) : ℝ) - τ n) *
      ((σ (n + 1) : ℝ) - σ n) ∧
    σ n ≤ knotMap τ σ t ∧ knotMap τ σ t < σ (n + 1) := by
  have hk := knotIndex_eq hτ h1 h2
  have hab : (τ n : ℝ) < τ (n + 1) := NNReal.coe_lt_coe.2 (hτ (Nat.lt_succ_self n))
  have hcd : (σ n : ℝ) < σ (n + 1) := NNReal.coe_lt_coe.2 (hσ (Nat.lt_succ_self n))
  obtain ⟨hA, hB⟩ := affine_mem_Ico hab hcd (NNReal.coe_le_coe.2 h1) (NNReal.coe_lt_coe.2 h2)
  have hval : (knotMap τ σ t : ℝ) = (σ n : ℝ) + ((t : ℝ) - τ n) / ((τ (n + 1) : ℝ) - τ n) *
      ((σ (n + 1) : ℝ) - σ n) := by
    rw [knotMap, knotMapReal, hk, Real.coe_toNNReal _ ((NNReal.coe_nonneg _).trans hA)]
  refine ⟨hval, ?_, ?_⟩
  · rw [← NNReal.coe_le_coe, hval]
    exact hA
  · rw [← NNReal.coe_lt_coe, hval]
    exact hB

theorem knotMap_knot {τ σ : ℕ → ℝ≥0} (hτ : StrictMono τ) (hσ : StrictMono σ) (n : ℕ) :
    knotMap τ σ (τ n) = σ n := by
  obtain ⟨hv, -, -⟩ := coe_knotMap_of_mem hτ hσ (le_refl (τ n)) (hτ (Nat.lt_succ_self n))
  apply NNReal.coe_injective
  rw [hv]
  simp

theorem strictMono_knotMap {τ σ : ℕ → ℝ≥0} (hτ : StrictMono τ) (hσ : StrictMono σ)
    (hτ0 : τ 0 = 0) (hτu : ∀ b, ∃ n, b < τ n) : StrictMono (knotMap τ σ) := by
  intro t t' htt'
  obtain ⟨h1, h2⟩ := knotIndex_bracket hτ hτ0 hτu t
  obtain ⟨h1', h2'⟩ := knotIndex_bracket hτ hτ0 hτu t'
  set k := knotIndex τ t
  set k' := knotIndex τ t'
  have hkk : k ≤ k' := by
    by_contra hlt
    have : τ (k' + 1) ≤ τ k := hτ.monotone (by omega)
    exact absurd (lt_of_lt_of_le (htt'.trans h2') this) (not_lt.2 h1)
  obtain ⟨hv, -, hlt⟩ := coe_knotMap_of_mem hτ hσ h1 h2
  obtain ⟨hv', hge', -⟩ := coe_knotMap_of_mem hτ hσ h1' h2'
  rcases hkk.lt_or_eq with hlt' | heq
  · calc knotMap τ σ t < σ (k + 1) := hlt
      _ ≤ σ k' := hσ.monotone (by omega)
      _ ≤ knotMap τ σ t' := hge'
  · rw [← NNReal.coe_lt_coe, hv, hv', ← heq]
    have hab : (0 : ℝ) < (τ (k + 1) : ℝ) - τ k := by
      have := NNReal.coe_lt_coe.2 (hτ (Nat.lt_succ_self k)); linarith
    have hcd : (0 : ℝ) < (σ (k + 1) : ℝ) - σ k := by
      have := NNReal.coe_lt_coe.2 (hσ (Nat.lt_succ_self k)); linarith
    have htt : (t : ℝ) < t' := NNReal.coe_lt_coe.2 htt'
    have : ((t : ℝ) - τ k) / ((τ (k + 1) : ℝ) - τ k) < ((t' : ℝ) - τ k) / ((τ (k + 1) : ℝ) - τ k) :=
      (div_lt_div_iff_of_pos_right hab).2 (by linarith)
    have := mul_lt_mul_of_pos_right this hcd
    linarith

theorem surjective_knotMap {τ σ : ℕ → ℝ≥0} (hτ : StrictMono τ) (hσ : StrictMono σ)
    (hσ0 : σ 0 = 0) (hσu : ∀ b, ∃ n, b < σ n) : Surjective (knotMap τ σ) := by
  intro u
  obtain ⟨m, hm1, hm2⟩ := exists_knot_bracket hσ0 hσu u
  have hab : (σ m : ℝ) < σ (m + 1) := NNReal.coe_lt_coe.2 (hσ (Nat.lt_succ_self m))
  have hcd : (τ m : ℝ) < τ (m + 1) := NNReal.coe_lt_coe.2 (hτ (Nat.lt_succ_self m))
  obtain ⟨hA, hB⟩ := affine_mem_Ico hab hcd (NNReal.coe_le_coe.2 hm1) (NNReal.coe_lt_coe.2 hm2)
  set s : ℝ := (τ m : ℝ) + ((u : ℝ) - σ m) / ((σ (m + 1) : ℝ) - σ m) * ((τ (m + 1) : ℝ) - τ m)
    with hs
  have hs0 : 0 ≤ s := (NNReal.coe_nonneg _).trans hA
  refine ⟨s.toNNReal, ?_⟩
  have hcs : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal _ hs0
  have h1 : τ m ≤ s.toNNReal := by rw [← NNReal.coe_le_coe, hcs]; exact hA
  have h2 : s.toNNReal < τ (m + 1) := by rw [← NNReal.coe_lt_coe, hcs]; exact hB
  obtain ⟨hv, -, -⟩ := coe_knotMap_of_mem hτ hσ h1 h2
  apply NNReal.coe_injective
  rw [hv, hcs, hs]
  have hne : (τ (m + 1) : ℝ) - τ m ≠ 0 := by linarith
  have hne' : (σ (m + 1) : ℝ) - σ m ≠ 0 := by linarith
  field_simp
  ring

/-- The piecewise-linear knot reparametrization as an order isomorphism of `ℝ≥0`. -/
noncomputable def knotOrderIso {τ σ : ℕ → ℝ≥0} (hτ : StrictMono τ) (hσ : StrictMono σ)
    (hτ0 : τ 0 = 0) (hσ0 : σ 0 = 0) (hτu : ∀ b, ∃ n, b < τ n) (hσu : ∀ b, ∃ n, b < σ n) :
    ℝ≥0 ≃o ℝ≥0 :=
  StrictMono.orderIsoOfSurjective (knotMap τ σ) (strictMono_knotMap hτ hσ hτ0 hτu)
    (surjective_knotMap hτ hσ hσ0 hσu)

theorem knotOrderIso_apply {τ σ : ℕ → ℝ≥0} (hτ : StrictMono τ) (hσ : StrictMono σ)
    (hτ0 : τ 0 = 0) (hσ0 : σ 0 = 0) (hτu : ∀ b, ∃ n, b < τ n) (hσu : ∀ b, ∃ n, b < σ n)
    (t : ℝ≥0) : knotOrderIso hτ hσ hτ0 hσ0 hτu hσu t = knotMap τ σ t := rfl

/-- **Knot reparametrization.** If `f` stays within `a` of `p n` on `[τ n, τ (n+1))`, `g` stays within
`a` of `q n` on `[σ n, σ (n+1))` and `dist (p n) (q n) ≤ δ` for all `n`, then some increasing
homeomorphism `φ` of `[0, ∞)` with `φ (τ n) = σ n` has `dist (f t) (g (φ t)) ≤ a + δ + a` for all `t`. -/
theorem exists_orderIso_dist_le_of_knots {E : Type*} [PseudoMetricSpace E] {f g : ℝ≥0 → E}
    {τ σ : ℕ → ℝ≥0} (hτ : StrictMono τ) (hσ : StrictMono σ) (hτ0 : τ 0 = 0) (hσ0 : σ 0 = 0)
    (hτu : ∀ b, ∃ n, b < τ n) (hσu : ∀ b, ∃ n, b < σ n) {p q : ℕ → E} {a δ : ℝ}
    (hpq : ∀ n, dist (p n) (q n) ≤ δ)
    (hf : ∀ n, ∀ t ∈ Ico (τ n) (τ (n + 1)), dist (f t) (p n) ≤ a)
    (hg : ∀ n, ∀ s ∈ Ico (σ n) (σ (n + 1)), dist (g s) (q n) ≤ a) :
    ∃ φ : ℝ≥0 ≃o ℝ≥0, (∀ n, φ (τ n) = σ n) ∧ ∀ t, dist (f t) (g (φ t)) ≤ a + δ + a := by
  refine ⟨knotOrderIso hτ hσ hτ0 hσ0 hτu hσu, fun n => knotMap_knot hτ hσ n, fun t => ?_⟩
  rw [knotOrderIso_apply]
  obtain ⟨h1, h2⟩ := knotIndex_bracket hτ hτ0 hτu t
  obtain ⟨-, hge, hlt⟩ := coe_knotMap_of_mem hτ hσ h1 h2
  set k := knotIndex τ t
  calc dist (f t) (g (knotMap τ σ t))
      ≤ dist (f t) (p k) + dist (p k) (q k) + dist (q k) (g (knotMap τ σ t)) := dist_triangle4 _ _ _ _
    _ ≤ a + δ + a := by
      rw [dist_comm (q k)]
      gcongr
      · exact hf k t ⟨h1, h2⟩
      · exact hpq k
      · exact hg k _ ⟨hge, hlt⟩

/-- Extension of the finite knot sequence `τ 0, …, τ N` by unit steps after `N`. -/
noncomputable def extendKnots (τ : ℕ → ℝ≥0) (N n : ℕ) : ℝ≥0 :=
  if n ≤ N then τ n else τ N + ((n - N : ℕ) : ℝ≥0)

theorem extendKnots_of_le {τ : ℕ → ℝ≥0} {N n : ℕ} (h : n ≤ N) : extendKnots τ N n = τ n := by
  simp [extendKnots, h]

theorem extendKnots_of_ge {τ : ℕ → ℝ≥0} {N n : ℕ} (h : N ≤ n) :
    extendKnots τ N n = τ N + ((n - N : ℕ) : ℝ≥0) := by
  rcases h.lt_or_eq with hlt | heq
  · simp [extendKnots, show ¬ n ≤ N by omega]
  · subst heq
    simp [extendKnots]

theorem strictMono_extendKnots {τ : ℕ → ℝ≥0} {N : ℕ} (hτ : ∀ n < N, τ n < τ (n + 1)) :
    StrictMono (extendKnots τ N) := by
  refine strictMono_nat_of_lt_succ fun n => ?_
  rcases lt_or_ge n N with hn | hn
  · rw [extendKnots_of_le hn.le, extendKnots_of_le hn]
    exact hτ n hn
  · rw [extendKnots_of_ge hn, extendKnots_of_ge (by omega : N ≤ n + 1),
      show n + 1 - N = (n - N) + 1 by omega]
    rw [Nat.cast_add, Nat.cast_one]
    exact (add_lt_add_iff_left (τ N)).2 (lt_add_one _)

theorem le_extendKnots {τ : ℕ → ℝ≥0} {N n : ℕ} (h : N ≤ n) : τ N ≤ extendKnots τ N n := by
  rw [extendKnots_of_ge h]
  exact le_self_add

theorem exists_lt_extendKnots (τ : ℕ → ℝ≥0) (N : ℕ) (b : ℝ≥0) : ∃ n, b < extendKnots τ N n := by
  refine ⟨N + (⌈b⌉₊ + 1), ?_⟩
  rw [extendKnots_of_ge (by omega), show N + (⌈b⌉₊ + 1) - N = ⌈b⌉₊ + 1 by omega]
  calc b ≤ (⌈b⌉₊ : ℝ≥0) := Nat.le_ceil b
    _ < ((⌈b⌉₊ + 1 : ℕ) : ℝ≥0) := by push_cast; exact lt_add_one _
    _ ≤ τ N + ((⌈b⌉₊ + 1 : ℕ) : ℝ≥0) := le_add_self

/-- **Knot reparametrization, finitely many knots.** Let `τ 0 = 0 < τ 1 < ⋯ < τ N` and
`σ 0 = 0 < σ 1 < ⋯ < σ N`. If `f` stays within `a` of `p n` on `[τ n, τ (n+1))` for `n < N` and within `a`
of `p N` on `[τ N, ∞)`, `g` likewise with `q` and `σ`, and `dist (p n) (q n) ≤ δ` for `n ≤ N`, then some
increasing homeomorphism `φ` of `[0, ∞)` with `φ (τ n) = σ n` for `n ≤ N` has
`dist (f t) (g (φ t)) ≤ a + δ + a` for all `t`. -/
theorem exists_orderIso_dist_le_of_finite_knots {E : Type*} [PseudoMetricSpace E]
    {f g : ℝ≥0 → E} {τ σ : ℕ → ℝ≥0} {N : ℕ} (hτ : ∀ n < N, τ n < τ (n + 1))
    (hσ : ∀ n < N, σ n < σ (n + 1)) (hτ0 : τ 0 = 0) (hσ0 : σ 0 = 0) {p q : ℕ → E} {a δ : ℝ}
    (hpq : ∀ n ≤ N, dist (p n) (q n) ≤ δ)
    (hf : ∀ n < N, ∀ t ∈ Ico (τ n) (τ (n + 1)), dist (f t) (p n) ≤ a)
    (hg : ∀ n < N, ∀ s ∈ Ico (σ n) (σ (n + 1)), dist (g s) (q n) ≤ a)
    (hfN : ∀ t, τ N ≤ t → dist (f t) (p N) ≤ a) (hgN : ∀ s, σ N ≤ s → dist (g s) (q N) ≤ a) :
    ∃ φ : ℝ≥0 ≃o ℝ≥0, (∀ n ≤ N, φ (τ n) = σ n) ∧ ∀ t, dist (f t) (g (φ t)) ≤ a + δ + a := by
  have hτ0' : extendKnots τ N 0 = 0 := by rw [extendKnots_of_le (Nat.zero_le N), hτ0]
  have hσ0' : extendKnots σ N 0 = 0 := by rw [extendKnots_of_le (Nat.zero_le N), hσ0]
  have hf' : ∀ n, ∀ t ∈ Ico (extendKnots τ N n) (extendKnots τ N (n + 1)),
      dist (f t) (p (min n N)) ≤ a := by
    intro n t ht
    rcases lt_or_ge n N with hn | hn
    · rw [extendKnots_of_le hn.le, extendKnots_of_le hn] at ht
      rw [min_eq_left hn.le]
      exact hf n hn t ht
    · rw [min_eq_right hn]
      exact hfN t ((le_extendKnots hn).trans ht.1)
  have hg' : ∀ n, ∀ s ∈ Ico (extendKnots σ N n) (extendKnots σ N (n + 1)),
      dist (g s) (q (min n N)) ≤ a := by
    intro n s hs
    rcases lt_or_ge n N with hn | hn
    · rw [extendKnots_of_le hn.le, extendKnots_of_le hn] at hs
      rw [min_eq_left hn.le]
      exact hg n hn s hs
    · rw [min_eq_right hn]
      exact hgN s ((le_extendKnots hn).trans hs.1)
  obtain ⟨φ, hφ, hdist⟩ := exists_orderIso_dist_le_of_knots (strictMono_extendKnots hτ)
    (strictMono_extendKnots hσ) hτ0' hσ0' (exists_lt_extendKnots τ N) (exists_lt_extendKnots σ N)
    (p := fun n => p (min n N)) (q := fun n => q (min n N))
    (fun n => hpq _ (min_le_right n N)) hf' hg'
  refine ⟨φ, fun n hn => ?_, hdist⟩
  have := hφ n
  rwa [extendKnots_of_le hn, extendKnots_of_le hn] at this

end LatticeProb.KnotReparam
