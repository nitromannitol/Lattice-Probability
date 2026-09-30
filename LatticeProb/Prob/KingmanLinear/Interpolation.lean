import Mathlib

/-!
# 3. Deterministic interpolation (pure real analysis)

Self-contained real analysis, independent of the measure-theoretic setting of the other stages.
`R : ℕ → ℕ` is a strictly increasing "bracketing" sequence with `R 0 = 0`. If a sequence `a` has
subsequence ratios `a (R j) / R j → lam`, the relative gaps `(R (j + 1) - R j) / R j → 0`, and `a`
is Lipschitz on doubling windows `[n, 2n]`, then every value `a n` at an index `n` bracketed by
`R j ≤ n < R (j + 1)` is within `O(ε)` of `lam * n`, which gives `a n / n → lam`
(`tendsto_div_of_tendsto_div_subseq`).
-/

open Filter Topology

namespace LatticeProb

/-- A strictly monotone `R : ℕ → ℕ` with `R 0 = 0` dominates the identity: `j ≤ R j`. -/
theorem le_apply_of_strictMono_of_zero_eq_zero {R : ℕ → ℕ} (hR0 : R 0 = 0)
    (hR : StrictMono R) (j : ℕ) : j ≤ R j := by
  induction j with
  | zero => simp [hR0]
  | succ j ih =>
    have h : R j < R (j + 1) := hR (Nat.lt_succ_self j)
    omega


/-- Every `n` is bracketed by consecutive values of a strictly monotone `R` with `R 0 = 0`:
`R j ≤ n < R (j + 1)` for some `j`. -/
private theorem exists_le_lt_apply_succ_of_strictMono_zero_eq_zero {R : ℕ → ℕ} (hR0 : R 0 = 0)
    (hR : StrictMono R) (n : ℕ) :
    ∃ j, R j ≤ n ∧ n < R (j + 1) := by
  have hex : ∃ j : ℕ, n < R (j + 1) :=
    ⟨n, lt_of_le_of_lt
      (Nat.rec (motive := fun k => k ≤ R k) (by simp [hR0])
        (fun k ih => le_trans (Nat.succ_le_succ ih) (Nat.succ_le_of_lt (hR (Nat.lt_succ_self k))))
        n)
      (hR (Nat.lt_succ_self n))⟩
  refine ⟨Nat.find hex,
    (Nat.eq_zero_or_pos (Nat.find hex)).elim
      (fun h => by rw [h, hR0]; exact Nat.zero_le n)
      (fun h => by
        obtain ⟨i, hi⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp h)
        rw [hi]
        exact le_of_not_gt (Nat.find_min hex (m := i) (by rw [hi]; exact Nat.lt_succ_self i))),
    Nat.find_spec hex⟩


/-- Eventually in `n`, every bracketing index `j` with `n < R (j + 1)` is at least a prescribed `J`.
-/
private theorem eventually_le_index_of_lt_apply_succ {R : ℕ → ℕ} (hR : StrictMono R) (J : ℕ) :
    ∀ᶠ n in atTop, ∀ j, n < R (j + 1) → J ≤ j := by
  refine eventually_atTop.mpr ⟨R J, fun n hn j hj => ?_⟩
  by_contra h
  have hlt : j < J := Nat.lt_of_not_le h
  have hle : R (j + 1) ≤ R J := hR.monotone (Nat.succ_le_of_lt hlt)
  omega


/-- If `R j / j → ρ`, the increments `(R (j + 1) - R j) / j` tend to `0`. -/
private theorem tendsto_sub_div_atTop_zero_of_tendsto_div {R : ℕ → ℕ} {ρ : ℝ}
    (hρ : Tendsto (fun j : ℕ => (R j : ℝ) / (j : ℝ)) atTop (𝓝 ρ)) :
    Tendsto (fun j : ℕ => ((R (j + 1) : ℝ) - R j) / (j : ℝ)) atTop (𝓝 0) := by
  have hbase0 : Tendsto (fun j : ℕ => (1 : ℝ) / (j : ℝ)) atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat
  have hbase : Tendsto (fun j : ℕ => (1 : ℝ) + 1 / (j : ℝ)) atTop (𝓝 1) := (by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).add hbase0)
  have hratio : Tendsto (fun j : ℕ => ((j + 1 : ℕ) : ℝ) / (j : ℝ)) atTop (𝓝 1) := (by
    have heq : (fun j : ℕ => (1 : ℝ) + 1 / (j : ℝ))
        =ᶠ[atTop] (fun j : ℕ => ((j + 1 : ℕ) : ℝ) / (j : ℝ)) := (by
      filter_upwards [eventually_ge_atTop 1] with j hj
      have hj' : (j : ℝ) ≠ 0 := (by
        have h0 : j ≠ 0 := (by omega)
        exact_mod_cast h0)
      rw [show ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 by push_cast; ring]
      field_simp)
    exact (Filter.tendsto_congr' heq).mp hbase)
  have h1 : Tendsto (fun j : ℕ => (R (j + 1) : ℝ) / ((j + 1 : ℕ) : ℝ)) atTop (𝓝 ρ) :=
    hρ.comp (tendsto_add_atTop_nat 1)
  have hmain : Tendsto (fun j : ℕ => (R (j + 1) : ℝ) / ((j + 1 : ℕ) : ℝ)
      * (((j + 1 : ℕ) : ℝ) / (j : ℝ)) - (R j : ℝ) / (j : ℝ)) atTop (𝓝 0) := (by
    have h := (h1.mul hratio).sub hρ
    simpa using h)
  have heq2 : (fun j : ℕ => (R (j + 1) : ℝ) / ((j + 1 : ℕ) : ℝ)
      * (((j + 1 : ℕ) : ℝ) / (j : ℝ)) - (R j : ℝ) / (j : ℝ))
      =ᶠ[atTop] (fun j : ℕ => ((R (j + 1) : ℝ) - R j) / (j : ℝ)) := (by
    filter_upwards [eventually_ge_atTop 1] with j hj
    have hj' : (j : ℝ) ≠ 0 := (by
      have h0 : j ≠ 0 := (by omega)
      exact_mod_cast h0)
    rw [show ((j + 1 : ℕ) : ℝ) = (j : ℝ) + 1 by push_cast; ring]
    field_simp)
  exact (Filter.tendsto_congr' heq2).mp hmain


/-- If `R j / j → ρ` for strictly monotone `R` with `R 0 = 0`, the relative increments `(R (j + 1) -
R j) / R j` tend to `0`. -/
theorem tendsto_sub_div_apply_atTop_zero_of_tendsto_div {R : ℕ → ℕ} (hR0 : R 0 = 0)
    (hR : StrictMono R) {ρ : ℝ}
    (hρ : Tendsto (fun j : ℕ => (R j : ℝ) / (j : ℝ)) atTop (𝓝 ρ)) :
    Tendsto (fun j : ℕ => ((R (j + 1) : ℝ) - R j) / (R j : ℝ)) atTop (𝓝 0) := by
  have hnum : ∀ j : ℕ, (0 : ℝ) ≤ (R (j + 1) : ℝ) - R j
  · intro j
    exact sub_nonneg.mpr (by exact_mod_cast hR.monotone (Nat.le_succ j))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_sub_div_atTop_zero_of_tendsto_div hρ) ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with j hj
    have hjle : j ≤ R j := le_apply_of_strictMono_of_zero_eq_zero hR0 hR j
    have hR1 : (1 : ℕ) ≤ R j := le_trans hj hjle
    have hRpos : (0 : ℝ) < (R j : ℝ) := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hR1)
    exact div_nonneg (hnum j) (le_of_lt hRpos)
  · filter_upwards [eventually_ge_atTop 1] with j hj
    have hjle : j ≤ R j := le_apply_of_strictMono_of_zero_eq_zero hR0 hR j
    have hjpos : (0 : ℝ) < (j : ℝ) := Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hj)
    have hcast : (j : ℝ) ≤ (R j : ℝ) := Nat.cast_le.mpr hjle
    exact div_le_div_of_nonneg_left (hnum j) hjpos hcast


/-- Pure real-analysis inequality: bounds `|g n - lam * n|` by `(C + 2 + |lam|) * ε * n`, from a
Lipschitz bound between `n` and a bracketing reference point `R`, a subsequence bound at `R`, and a
small relative gap between `R` and the next bracketing value `R'`. -/
private theorem abs_sub_linear_le_of_gap_and_lipschitz {gn gR lam C ε n R R' : ℝ} (hC : 0 ≤ C)
    (hε : 0 ≤ ε) (_hR : 0 < R) (hRn : R ≤ n) (hnR' : n ≤ R') (hgap : R' - R ≤ ε * R)
    (hlip : |gn - gR| ≤ C * (n - R) + ε * R) (hsubs : |gR - lam * R| ≤ ε * R) :
    |gn - lam * n| ≤ (C + 2 + |lam|) * ε * n := by
  have hnR : n - R ≤ ε * R := by linarith
  have hεR : ε * R ≤ ε * n := mul_le_mul_of_nonneg_left hRn hε
  have h3 : |lam * R - lam * n| = |lam| * (n - R) := by
    rw [show lam * R - lam * n = -(lam * (n - R)) by ring, abs_neg, abs_mul,
      abs_of_nonneg (by linarith : (0:ℝ) ≤ n - R)]
  have hdec1 : |gn - lam * n| ≤ |gn - gR| + |gR - lam * n| := abs_sub_le _ _ _
  have hdec2 : |gR - lam * n| ≤ |gR - lam * R| + |lam| * (n - R) := by
    have h := abs_sub_le gR (lam * R) (lam * n)
    rwa [h3] at h
  have hdec : |gn - lam * n| ≤ |gn - gR| + |gR - lam * R| + |lam| * (n - R) := by
    linarith [hdec1, hdec2]
  have hA : C * (n - R) ≤ C * (ε * R) := mul_le_mul_of_nonneg_left hnR hC
  have hB : C * (ε * R) ≤ C * (ε * n) := mul_le_mul_of_nonneg_left hεR hC
  have hAB : C * (n - R) ≤ C * (ε * n) := le_trans hA hB
  have h1 : |gn - gR| ≤ C * (ε * n) + ε * n := by linarith [hlip, hAB, hεR]
  have h2 : |gR - lam * R| ≤ ε * n := le_trans hsubs hεR
  have hk : |lam| * (n - R) ≤ |lam| * (ε * R) := mul_le_mul_of_nonneg_left hnR (abs_nonneg lam)
  have hk2 : |lam| * (ε * R) ≤ |lam| * (ε * n) := mul_le_mul_of_nonneg_left hεR (abs_nonneg lam)
  have h3b : |lam| * (n - R) ≤ |lam| * (ε * n) := le_trans hk hk2
  have hrw : C * (ε * n) + ε * n + ε * n + |lam| * (ε * n) = (C + 2 + |lam|) * ε * n := by
    ring
  have hsum : |gn - gR| + |gR - lam * R| + |lam| * (n - R) ≤ (C + 2 + |lam|) * ε * n := by
    linarith [h1, h2, h3b, hrw.le, hrw.ge]
  exact le_trans hdec hsum

/-- Restates `abs_sub_linear_le_of_gap_and_lipschitz`. -/
private theorem abs_sub_linear_le_of_gap_and_lipschitz' {gn gR lam C ε n R R' : ℝ} (hC : 0 ≤ C)
    (hε : 0 ≤ ε) (hR : 0 < R) (hRn : R ≤ n) (hnR' : n ≤ R') (hgap : R' - R ≤ ε * R)
    (hlip : |gn - gR| ≤ C * (n - R) + ε * R) (hsubs : |gR - lam * R| ≤ ε * R) :
    |gn - lam * n| ≤ (C + 2 + |lam|) * ε * n := by
  exact abs_sub_linear_le_of_gap_and_lipschitz hC hε hR hRn hnR' hgap hlip hsubs


/-- `min 1 (ε / (K + 1))` is positive for `K ≥ 0` and `ε > 0`. -/
private theorem pos_min_one_div_add_one (K : ℝ) (hK : 0 ≤ K) (ε : ℝ) (hε : 0 < ε) :
    (0 : ℝ) < min 1 (ε / (K + 1)) :=
  lt_min one_pos (div_pos hε (lt_of_le_of_lt hK (lt_add_one K)))

/-- `K * min 1 (ε / (K + 1)) < ε` for `K ≥ 0` and `ε > 0`. -/
private theorem mul_min_one_div_add_one_lt (K ε : ℝ) (hK : 0 ≤ K) (hε : 0 < ε) :
    K * min 1 (ε / (K + 1)) < ε := by
  have hpos : (0 : ℝ) < K + 1 := lt_of_le_of_lt hK (lt_add_one K)
  have hle : min 1 (ε / (K + 1)) ≤ ε / (K + 1) := min_le_right _ _
  have h1 : K * min 1 (ε / (K + 1)) ≤ K * (ε / (K + 1)) :=
    mul_le_mul_of_nonneg_left hle hK
  have h2 : K * (ε / (K + 1)) < ε := by
    rw [← mul_div_assoc, div_lt_iff₀ hpos]
    nlinarith [hε]
  exact lt_of_le_of_lt h1 h2

/-- A sequence with `|a n - l| ≤ K * ε` eventually, for every `0 < ε ≤ 1`, tends to `l`. -/
private theorem tendsto_of_forall_eventually_abs_sub_le_mul {a : ℕ → ℝ} {l K : ℝ} (hK : 0 ≤ K)
    (h : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ᶠ n in atTop, |a n - l| ≤ K * ε) :
    Tendsto a atTop (𝓝 l) := by
  rw [Metric.tendsto_nhds]
  intro ε' hε'
  filter_upwards [h (min 1 (ε' / (K + 1))) (pos_min_one_div_add_one K hK ε' hε') (min_le_left _ _)]
    with n hn
  rw [Real.dist_eq]
  exact lt_of_le_of_lt hn (mul_min_one_div_add_one_lt K ε' hK hε')


/-- Restates `le_apply_of_strictMono_of_zero_eq_zero` in the packaging used by the bracketing
argument below. -/
theorem le_apply_of_strictMono_of_zero_eq_zero' {R : ℕ → ℕ} (hR0 : R 0 = 0)
    (hR : StrictMono R) :
    ∀ j : ℕ, j ≤ R j := by
  intro j
  induction j with
  | zero => simp [hR0]
  | succ i ih =>
      have hlt : R i < R (i + 1) := hR (Nat.lt_succ_self i)
      omega

/-- The real cast of a natural number `n ≥ 1` is positive. -/
private theorem natCast_pos_of_one_le {n : ℕ} (h : (1 : ℕ) ≤ n) : (0 : ℝ) < (n : ℝ) := by
  exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one h : 0 < n)

/-- `dist x 0 < e` gives `x < e`. -/
private theorem lt_of_dist_zero_lt {x e : ℝ} (h : dist x 0 < e) : x < e := by
  have h' : |x| < e := by simpa [Real.dist_eq] using h
  exact (abs_lt.1 h').2

/-- `dist x y < e` gives `|x - y| < e`. -/
private theorem abs_sub_lt_of_dist_lt {x y e : ℝ} (h : dist x y < e) : |x - y| < e := by
  simpa [Real.dist_eq] using h

/-- `g / R < e` gives `g ≤ e * R`, for `R > 0`. -/
private theorem le_mul_of_div_lt {g e R : ℝ} (hp : 0 < R) (h : g / R < e) : g ≤ e * R := by
  have hb := (div_lt_iff₀ hp).1 h
  linarith

/-- `|x / R - l| < e` gives `|x - l * R| ≤ e * R`, for `R > 0`. -/
private theorem abs_sub_mul_le_of_abs_div_sub_lt {x l e R : ℝ} (hp : 0 < R) (h : |x / R - l| < e) :
    |x - l * R| ≤ e * R := by
  have hkey : x - l * R = (x / R - l) * R := by
    rw [sub_mul, div_mul_cancel₀ x (ne_of_gt hp)]
  rw [hkey, abs_mul, abs_of_pos hp]
  exact mul_le_mul_of_nonneg_right (le_of_lt h) (le_of_lt hp)

/-- Packages the subsequence limit, the relative-gap limit, and the Lipschitz hypothesis into a
single index `J` beyond which the gap, subsequence, and Lipschitz bounds all hold at scale `ε`. -/
private theorem exists_index_forall_bounds_of_tendsto_and_gap_and_lipschitz {a : ℕ → ℝ}
    {R : ℕ → ℕ} (hR0 : R 0 = 0) (hR : StrictMono R) {lam C : ℝ}
    (hsubs : Tendsto (fun j : ℕ => a (R j) / (R j : ℝ)) atTop (𝓝 lam))
    (hgap : Tendsto (fun j : ℕ => ((R (j + 1) : ℝ) - R j) / (R j : ℝ)) atTop (𝓝 0))
    (hlip : ∀ ε > 0, ∀ᶠ n in atTop, ∀ m, n ≤ m → m ≤ 2*n →
      |a m - a n| ≤ C*((m:ℝ)-n) + ε*n) {ε : ℝ} (hε : 0 < ε) :
    ∃ J : ℕ, ∀ j, J ≤ j → 0 < (R j : ℝ) ∧ ((R (j + 1) : ℝ) - R j ≤ ε * R j) ∧
      |a (R j) - lam * R j| ≤ ε * R j ∧
      (∀ m, R j ≤ m → m ≤ 2 * R j → |a m - a (R j)| ≤ C*((m:ℝ) - R j) + ε * R j) := by
  have jle : ∀ j : ℕ, j ≤ R j := le_apply_of_strictMono_of_zero_eq_zero' hR0 hR
  have h3 : ∀ᶠ j in atTop, 0 < (R j : ℝ) :=
    (eventually_ge_atTop (1 : ℕ)).mono (fun j hj =>
      natCast_pos_of_one_le (le_trans hj (jle j)))
  have h1 : ∀ᶠ j in atTop, ((R (j + 1) : ℝ) - R j) / (R j : ℝ) < ε :=
    ((Metric.tendsto_nhds.1 hgap) ε hε).mono (fun j hj => lt_of_dist_zero_lt hj)
  have h2 : ∀ᶠ j in atTop, |a (R j) / (R j : ℝ) - lam| < ε :=
    ((Metric.tendsto_nhds.1 hsubs) ε hε).mono (fun j hj => abs_sub_lt_of_dist_lt hj)
  have h4 : ∀ᶠ j in atTop, ((R (j + 1) : ℝ) - R j) ≤ ε * R j :=
    (h3.and h1).mono (fun j hj => le_mul_of_div_lt hj.1 hj.2)
  have h5 : ∀ᶠ j in atTop, |a (R j) - lam * R j| ≤ ε * R j :=
    (h3.and h2).mono (fun j hj => abs_sub_mul_le_of_abs_div_sub_lt hj.1 hj.2)
  have h6 : ∀ᶠ j in atTop, ∀ m, R j ≤ m → m ≤ 2 * R j →
      |a m - a (R j)| ≤ C * ((m : ℝ) - R j) + ε * R j :=
    (StrictMono.tendsto_atTop hR).eventually (hlip ε hε)
  have hall : ∀ᶠ j in atTop, 0 < (R j : ℝ) ∧ ((R (j + 1) : ℝ) - R j ≤ ε * R j) ∧
      |a (R j) - lam * R j| ≤ ε * R j ∧
      (∀ m, R j ≤ m → m ≤ 2 * R j →
        |a m - a (R j)| ≤ C * ((m : ℝ) - R j) + ε * R j) :=
    h3.and (h4.and (h5.and h6))
  rw [Filter.eventually_atTop] at hall
  exact hall


/-- Pointwise step: for `n` bracketed between `R j` and `R (j + 1)`, the bounds at `R j` transfer to
`|a n / n - lam| ≤ (C + 2 + |lam|) * ε`. -/
private theorem abs_div_sub_le_of_bounds {a : ℕ → ℝ} {R : ℕ → ℕ} {lam C ε : ℝ} (hC : 0 ≤ C)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) {j n : ℕ} (hRpos : 0 < (R j : ℝ))
    (hgap : (R (j + 1) : ℝ) - R j ≤ ε * R j)
    (hsubs : |a (R j) - lam * R j| ≤ ε * R j)
    (hlip : ∀ m, R j ≤ m → m ≤ 2 * R j → |a m - a (R j)| ≤ C*((m:ℝ) - R j) + ε * R j)
    (hjn : R j ≤ n) (hnj : n < R (j + 1)) :
    |a n / n - lam| ≤ (C + 2 + |lam|) * ε := by
  have hnR : (R j : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hjn
  have hnpos : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le hRpos hnR
  have hn_ne : (n : ℝ) ≠ 0 := ne_of_gt hnpos
  have hnR' : (n : ℝ) ≤ (R (j + 1) : ℝ) := Nat.cast_le.mpr (le_of_lt hnj)
  have hεR : ε * (R j : ℝ) ≤ (R j : ℝ) := mul_le_of_le_one_left (le_of_lt hRpos) hε1
  have h2R : (R (j + 1) : ℝ) ≤ ((2 * R j : ℕ) : ℝ) := (by push_cast; linarith)
  have h2 : R (j + 1) ≤ 2 * R j := Nat.cast_le.mp h2R
  have hnj2 : n ≤ 2 * R j := le_of_lt (lt_of_lt_of_le hnj h2)
  have hlip' : |a n - a (R j)| ≤ C * ((n : ℝ) - (R j : ℝ)) + ε * (R j : ℝ) := hlip n hjn hnj2
  have h16 : |a n - lam * (n : ℝ)| ≤ (C + 2 + |lam|) * ε * (n : ℝ) :=
    abs_sub_linear_le_of_gap_and_lipschitz' (gn := a n) (gR := a (R j)) (lam := lam) (C := C)
      (ε := ε) (n := (n : ℝ)) (R := (R j : ℝ)) (R' := (R (j + 1) : ℝ))
      hC hε0 hRpos hnR hnR' hgap hlip' hsubs
  have hub : |a n / (n : ℝ) - lam| = |a n - lam * (n : ℝ)| / (n : ℝ) :=
    (by rw [div_sub' hn_ne, mul_comm ((n : ℝ)) lam, abs_div, abs_of_pos hnpos])
  rw [hub, div_le_iff₀ hnpos]
  exact h16


/-- **Deterministic interpolation.** If the subsequence ratios `a (R j) / R j` tend to `lam` along a
strictly monotone `R` with `R 0 = 0` and vanishing relative gaps, and `a` is Lipschitz on doubling
windows, then `a n / n → lam`. -/
theorem tendsto_div_of_tendsto_div_subseq {a : ℕ → ℝ} {R : ℕ → ℕ} (hR0 : R 0 = 0)
    (hR : StrictMono R) {lam C : ℝ} (hC : 0 ≤ C)
    (hsubs : Tendsto (fun j : ℕ => a (R j) / (R j : ℝ)) atTop (𝓝 lam))
    (hgap : Tendsto (fun j : ℕ => ((R (j + 1) : ℝ) - R j) / (R j : ℝ)) atTop (𝓝 0))
    (hlip : ∀ ε > 0, ∀ᶠ n in atTop, ∀ m, n ≤ m → m ≤ 2*n →
      |a m - a n| ≤ C*((m:ℝ)-n) + ε*n) :
    Tendsto (fun n : ℕ => a n / (n : ℝ)) atTop (𝓝 lam) := by
  refine tendsto_of_forall_eventually_abs_sub_le_mul (K := max (C + 2 + |lam|) 0)
    (le_max_right _ _) ?_
  intro ε hε0 hε1
  obtain ⟨J, hJ⟩ :=
    exists_index_forall_bounds_of_tendsto_and_gap_and_lipschitz hR0 hR hsubs hgap hlip hε0
  filter_upwards [eventually_le_index_of_lt_apply_succ hR J] with n hn
  obtain ⟨j, hjn, hnj⟩ := exists_le_lt_apply_succ_of_strictMono_zero_eq_zero hR0 hR n
  obtain ⟨hRpos, hgapj, hsubsj, hlipj⟩ := hJ j (hn j hnj)
  have h := abs_div_sub_le_of_bounds hC hε0.le hε1 hRpos hgapj hsubsj hlipj hjn hnj
  exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hε0.le)

end LatticeProb
