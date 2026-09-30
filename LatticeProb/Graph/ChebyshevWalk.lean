import Mathlib

/-!
# Chebyshev polynomials and the simple random walk on `ℤ`

The algebra behind the Carne–Varopoulos bound. The law `p_n(k)` of the simple random walk on `ℤ`
(`lineWalk`) expands the powers of `X` in Chebyshev polynomials, `Xⁿ = ∑_k p_n(k) T_k(X)`
(`X_pow_eq_sum_lineWalk_T`), and has the Hoeffding tail `∑_{|k| ≥ r} p_n(k) ≤ 2 e^{-r²/(2n)}`
(`sum_lineWalk_tail_le`). For a real symmetric matrix `A` with eigenvalues in `[-1, 1]` every
entry of `T_k(A)` is at most `1` in absolute value (`abs_aeval_T_apply_le_one`, by the spectral
theorem), and a symmetric matrix conjugate by a positive diagonal to a substochastic one has its
eigenvalues there (`abs_eigenvalues_le_one`).
-/

open Polynomial

noncomputable section

namespace LatticeProb.Graph

/-! ### The simple random walk on `ℤ` and the Chebyshev expansion -/

/-- The law `p_n(k) = P(S_n = k)` of the simple random walk on `ℤ` started at `0`. -/
def lineWalk : ℕ → ℤ → ℝ
  | 0 => fun k => if k = 0 then 1 else 0
  | n + 1 => fun k => (lineWalk n (k - 1) + lineWalk n (k + 1)) / 2

/-- The law of the walk on `ℤ` is nonnegative. -/
theorem lineWalk_nonneg (n : ℕ) (k : ℤ) : 0 ≤ lineWalk n k := by
  induction n generalizing k with
  | zero => by_cases h : k = 0 <;> simp [lineWalk, h]
  | succ n ih =>
      unfold lineWalk
      exact div_nonneg (add_nonneg (ih (k - 1)) (ih (k + 1))) (by norm_num)

/-- At time `n` the walk on `ℤ` is in `[-n, n]`: `p_n(k) = 0` for `|k| > n`. -/
theorem lineWalk_eq_zero (n : ℕ) {k : ℤ} (hk : (n : ℤ) < |k|) : lineWalk n k = 0 := by
  induction n generalizing k with
  | zero =>
      rw [lineWalk]
      have hk0 : k ≠ 0 := abs_pos.mp (by exact_mod_cast hk)
      simp [hk0]
  | succ n ih =>
      have hk' : (n : ℤ) + 1 < |k| := by exact_mod_cast hk
      have h1 : (n : ℤ) < |k - 1| := by
        rcases lt_or_ge k 0 with hk0 | hk0
        · have hkabs : |k| = -k := abs_of_neg hk0
          rw [hkabs] at hk'
          have hk1 : k - 1 < 0 := by omega
          rw [abs_of_neg hk1]; omega
        · have hkabs : |k| = k := abs_of_nonneg hk0
          rw [hkabs] at hk'
          have hk1 : (0 : ℤ) ≤ k - 1 := by omega
          rw [abs_of_nonneg hk1]; omega
      have h2 : (n : ℤ) < |k + 1| := by
        rcases lt_or_ge k 0 with hk0 | hk0
        · have hkabs : |k| = -k := abs_of_neg hk0
          rw [hkabs] at hk'
          have hk1 : k + 1 ≤ 0 := by omega
          rw [abs_of_nonpos hk1]; omega
        · have hkabs : |k| = k := abs_of_nonneg hk0
          rw [hkabs] at hk'
          have hk1 : (0 : ℤ) ≤ k + 1 := by omega
          rw [abs_of_nonneg hk1]; omega
      unfold lineWalk
      rw [ih h1, ih h2]
      ring

/-- Doubling the Chebyshev recurrence: `2 * X * T k = T (k+1) + T (k-1)`. -/
private lemma two_mul_X_T (k : ℤ) :
    (2 : ℝ[X]) * X * Chebyshev.T ℝ k
      = Chebyshev.T ℝ (k + 1) + Chebyshev.T ℝ (k - 1) := by
  have h := Chebyshev.T_add_two ℝ (k - 1)
  rw [show k - 1 + 2 = k + 1 by ring, show k - 1 + 1 = k by ring] at h
  rw [h]
  ring

/-- `X * T k = (T (k+1) + T (k-1)) / 2`, with the `1/2` written as the scalar
polynomial `C (1/2)`. -/
private lemma X_mul_T (k : ℤ) :
    X * Chebyshev.T ℝ k
      = (Chebyshev.T ℝ (k + 1) + Chebyshev.T ℝ (k - 1)) * C (1/2 : ℝ) := by
  have h := two_mul_X_T k
  rw [← h]
  have hc : (2 : ℝ[X]) * C (1/2 : ℝ) = 1 := by
    rw [show (2 : ℝ[X]) = C (2 : ℝ) from (map_ofNat C 2).symm, ← map_mul]
    norm_num
  rw [show (2 * X * Chebyshev.T ℝ k) * C (1/2 : ℝ)
        = X * Chebyshev.T ℝ k * ((2 : ℝ[X]) * C (1/2 : ℝ)) by ring, hc, mul_one]

/-- The expansion `X ^ n = ∑_{k=-N}^{N} p_n(k) T_k` for every `N ≥ n`; the extra terms
vanish by `lineWalk_eq_zero`. -/
private lemma pow_eq_sum_lineWalk_T_Icc (n : ℕ) (N : ℕ) (hN : n ≤ N) :
    (X : ℝ[X]) ^ n
      = ∑ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), C (lineWalk n k) * Chebyshev.T ℝ k := by
  induction n generalizing N with
  | zero =>
      rw [pow_zero, Finset.sum_eq_single (0 : ℤ)]
      · simp [lineWalk, Chebyshev.T_zero]
      · intro b _ hb
        simp [lineWalk, hb]
      · intro h0
        exact absurd (Finset.mem_Icc.mpr ⟨by omega, by omega⟩) h0
  | succ n ih =>
      have hih := ih (N+1) (by omega)
      rw [pow_succ', hih]
      have hup : (∑ k ∈ Finset.Icc (-((N+1:ℕ):ℤ)) ((N+1:ℕ):ℤ),
            C (lineWalk n k) * Chebyshev.T ℝ (k+1))
          = ∑ j ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), C (lineWalk n (j-1)) * Chebyshev.T ℝ j := by
        have hshift : (∑ k ∈ Finset.Icc (-((N+1:ℕ):ℤ)) ((N+1:ℕ):ℤ),
              C (lineWalk n k) * Chebyshev.T ℝ (k+1))
            = ∑ j ∈ Finset.Icc (-(N:ℤ)) ((N:ℤ)+2),
                C (lineWalk n (j-1)) * Chebyshev.T ℝ j := by
          refine Finset.sum_nbij' (fun k : ℤ => k + 1) (fun j : ℤ => j - 1)
            ?_ ?_ ?_ ?_ ?_
          · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
          · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
          · intro a _; ring
          · intro a _; ring
          · intro a _; rw [show a + 1 - 1 = a by ring]
        rw [hshift]
        refine (Finset.sum_subset ?_ ?_).symm
        · intro x hx; simp only [Finset.mem_Icc] at hx ⊢; omega
        · intro x hx hxn
          simp only [Finset.mem_Icc] at hx hxn
          have hxN : (N:ℤ) < x := by
            by_contra hle
            exact hxn ⟨hx.1, not_lt.mp hle⟩
          have hzero : lineWalk n (x - 1) = 0 := by
            apply lineWalk_eq_zero
            have hxpos : (0:ℤ) < x - 1 := by omega
            rw [abs_of_pos hxpos]; omega
          rw [hzero, map_zero, zero_mul]
      have hdn : (∑ k ∈ Finset.Icc (-((N+1:ℕ):ℤ)) ((N+1:ℕ):ℤ),
            C (lineWalk n k) * Chebyshev.T ℝ (k-1))
          = ∑ j ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), C (lineWalk n (j+1)) * Chebyshev.T ℝ j := by
        have hshift : (∑ k ∈ Finset.Icc (-((N+1:ℕ):ℤ)) ((N+1:ℕ):ℤ),
              C (lineWalk n k) * Chebyshev.T ℝ (k-1))
            = ∑ j ∈ Finset.Icc (-((N:ℤ)+2)) (N:ℤ),
                C (lineWalk n (j+1)) * Chebyshev.T ℝ j := by
          refine Finset.sum_nbij' (fun k : ℤ => k - 1) (fun j : ℤ => j + 1)
            ?_ ?_ ?_ ?_ ?_
          · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
          · intro a ha; simp only [Finset.mem_Icc] at ha ⊢; omega
          · intro a _; ring
          · intro a _; ring
          · intro a _; rw [show a - 1 + 1 = a by ring]
        rw [hshift]
        refine (Finset.sum_subset ?_ ?_).symm
        · intro x hx; simp only [Finset.mem_Icc] at hx ⊢; omega
        · intro x hx hxn
          simp only [Finset.mem_Icc] at hx hxn
          have hxN : x < -(N:ℤ) := by
            by_contra hle
            exact hxn ⟨not_lt.mp hle, hx.2⟩
          have hzero : lineWalk n (x + 1) = 0 := by
            apply lineWalk_eq_zero
            have hxneg : x + 1 < 0 := by omega
            rw [abs_of_neg hxneg]; omega
          rw [hzero, map_zero, zero_mul]
      calc X * (∑ k ∈ Finset.Icc (-((N+1:ℕ):ℤ)) ((N+1:ℕ):ℤ),
              C (lineWalk n k) * Chebyshev.T ℝ k)
          = ∑ k ∈ Finset.Icc (-((N+1:ℕ):ℤ)) ((N+1:ℕ):ℤ),
              X * (C (lineWalk n k) * Chebyshev.T ℝ k) := by rw [Finset.mul_sum]
        _ = ∑ k ∈ Finset.Icc (-((N+1:ℕ):ℤ)) ((N+1:ℕ):ℤ),
              (C (lineWalk n k) * Chebyshev.T ℝ (k+1)
                + C (lineWalk n k) * Chebyshev.T ℝ (k-1)) * C (1/2 : ℝ) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [show X * (C (lineWalk n k) * Chebyshev.T ℝ k)
                  = C (lineWalk n k) * (X * Chebyshev.T ℝ k) by ring, X_mul_T]
            ring
        _ = (∑ k ∈ Finset.Icc (-((N+1:ℕ):ℤ)) ((N+1:ℕ):ℤ),
              (C (lineWalk n k) * Chebyshev.T ℝ (k+1)
                + C (lineWalk n k) * Chebyshev.T ℝ (k-1))) * C (1/2 : ℝ) := by
            rw [Finset.sum_mul]
        _ = ((∑ k ∈ Finset.Icc (-((N+1:ℕ):ℤ)) ((N+1:ℕ):ℤ),
                C (lineWalk n k) * Chebyshev.T ℝ (k+1))
              + (∑ k ∈ Finset.Icc (-((N+1:ℕ):ℤ)) ((N+1:ℕ):ℤ),
                C (lineWalk n k) * Chebyshev.T ℝ (k-1))) * C (1/2 : ℝ) := by
            rw [Finset.sum_add_distrib]
        _ = ((∑ j ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), C (lineWalk n (j-1)) * Chebyshev.T ℝ j)
              + (∑ j ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), C (lineWalk n (j+1)) * Chebyshev.T ℝ j))
              * C (1/2 : ℝ) := by
            rw [hup, hdn]
        _ = ∑ j ∈ Finset.Icc (-(N:ℤ)) (N:ℤ), C (lineWalk (n+1) j) * Chebyshev.T ℝ j := by
            rw [← Finset.sum_add_distrib, Finset.sum_mul]
            refine Finset.sum_congr rfl fun j _ => ?_
            have hC : C (lineWalk (n+1) j)
                = (C (lineWalk n (j-1)) + C (lineWalk n (j+1))) * C (1/2 : ℝ) := by
              change C ((lineWalk n (j-1) + lineWalk n (j+1)) / 2) = _
              rw [show (lineWalk n (j-1) + lineWalk n (j+1)) / 2
                    = (lineWalk n (j-1) + lineWalk n (j+1)) * (1/2 : ℝ) by ring]
              rw [map_mul, map_add]
            rw [hC]; ring

/-- The Chebyshev expansion of a power, `Xⁿ = ∑_{|k| ≤ n} p_n(k) T_k(X)`: the polynomial
form of `cosⁿ θ = E[cos(S_n θ)]`. -/
theorem X_pow_eq_sum_lineWalk_T (n : ℕ) :
    (X : ℝ[X]) ^ n
      = ∑ k ∈ Finset.Icc (-(n : ℤ)) n, C (lineWalk n k) * Chebyshev.T ℝ k :=
  pow_eq_sum_lineWalk_T_Icc n n le_rfl

/-- The weighted sums of `lineWalk n` over any integer interval containing `[-n, n]` agree. -/
private lemma sum_Icc_lineWalk_eq (n : ℕ) (g : ℤ → ℝ) {a b : ℤ} (ha : a ≤ -(n : ℤ))
    (hb : (n : ℤ) ≤ b) :
    ∑ k ∈ Finset.Icc a b, lineWalk n k * g k
      = ∑ k ∈ Finset.Icc (-(n : ℤ)) n, lineWalk n k * g k := by
  symm
  refine Finset.sum_subset (fun k hk => ?_) (fun k hk hk' => ?_)
  · rw [Finset.mem_Icc] at hk ⊢; omega
  · rw [Finset.mem_Icc] at hk hk'
    have hlt : (n : ℤ) < |k| := by
      rw [lt_abs]; omega
    rw [lineWalk_eq_zero n hlt, zero_mul]

/-- Shifting the summation variable of a sum over an integer interval by `c`. -/
private lemma sum_Icc_shift (f : ℤ → ℝ) (a b c : ℤ) :
    ∑ k ∈ Finset.Icc a b, f (k + c) = ∑ j ∈ Finset.Icc (a + c) (b + c), f j := by
  refine Finset.sum_nbij' (fun k => k + c) (fun j => j - c) ?_ ?_ ?_ ?_ ?_
  · intro k hk; simp only [Finset.mem_Icc] at hk ⊢; omega
  · intro j hj; simp only [Finset.mem_Icc] at hj ⊢; omega
  · intro k _; exact add_sub_cancel_right k c
  · intro j _; exact sub_add_cancel j c
  · intro k _; rfl

/-- Shifting `lineWalk n` by `c` with `|c| ≤ 1` inside the exponential sum at time `n + 1`
multiplies the sum at time `n` by `e^{-tc}`. -/
private lemma sum_lineWalk_shift_mul_exp (n : ℕ) (t : ℝ) (c : ℤ) (hc : |c| ≤ 1) :
    ∑ k ∈ Finset.Icc (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ),
        lineWalk n (k + c) * Real.exp (t * k)
      = Real.exp (-(t * c))
          * ∑ k ∈ Finset.Icc (-(n : ℤ)) n, lineWalk n k * Real.exp (t * k) := by
  obtain ⟨hc1, hc2⟩ := abs_le.mp hc
  have hF : ∀ k ∈ Finset.Icc (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ),
      lineWalk n (k + c) * Real.exp (t * k)
        = lineWalk n (k + c) * Real.exp (t * (((k + c : ℤ) : ℝ) - c)) := by
    intro k _
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl hF,
    sum_Icc_shift (fun j : ℤ => lineWalk n j * Real.exp (t * ((j : ℝ) - c))),
    sum_Icc_lineWalk_eq n (fun j : ℤ => Real.exp (t * ((j : ℝ) - c)))
      (by push_cast; omega) (by push_cast; omega),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show t * ((k : ℝ) - c) = t * k + -(t * c) by ring, Real.exp_add]
  ring

/-- The Laplace transform of the walk on `ℤ`: `∑_k p_n(k) e^{tk} = cosh(t)ⁿ`. -/
theorem sum_lineWalk_mul_exp (n : ℕ) (t : ℝ) :
    ∑ k ∈ Finset.Icc (-(n : ℤ)) n, lineWalk n k * Real.exp (t * k) = Real.cosh t ^ n := by
  induction n with
  | zero => simp [lineWalk]
  | succ n ih =>
      have hsplit : ∀ k ∈ Finset.Icc (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ),
          lineWalk (n + 1) k * Real.exp (t * k)
            = (lineWalk n (k + -1) * Real.exp (t * k)
                + lineWalk n (k + 1) * Real.exp (t * k)) / 2 := by
        intro k _
        show (lineWalk n (k - 1) + lineWalk n (k + 1)) / 2 * Real.exp (t * k) = _
        rw [sub_eq_add_neg]
        ring
      rw [Finset.sum_congr rfl hsplit, ← Finset.sum_div, Finset.sum_add_distrib,
        sum_lineWalk_shift_mul_exp n t (-1) (by norm_num),
        sum_lineWalk_shift_mul_exp n t 1 (by norm_num), ih, Real.cosh_eq, pow_succ]
      rw [show -(t * (((-1 : ℤ)) : ℝ)) = t by push_cast; ring,
        show -(t * (((1 : ℤ)) : ℝ)) = -t by push_cast; ring]
      ring

/-- The Hoeffding bound for the walk on `ℤ`: `∑_{|k| ≥ r} p_n(k) ≤ 2 e^{-r²/(2n)}`. -/
theorem sum_lineWalk_tail_le (n : ℕ) (hn : 1 ≤ n) (r : ℝ) (hr : 0 ≤ r) :
    ∑ k ∈ (Finset.Icc (-(n : ℤ)) n).filter (fun k : ℤ => r ≤ |(k : ℝ)|), lineWalk n k
      ≤ 2 * Real.exp (-r ^ 2 / (2 * n)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set t := r / n with htdef
  have ht : 0 ≤ t := div_nonneg hr hnpos.le
  have hpt : ∀ k : ℤ, r ≤ |(k : ℝ)| →
      1 ≤ Real.exp (-(t * r)) * (Real.exp (t * k) + Real.exp (-t * k)) := by
    intro k hk
    have h1 : Real.exp (t * r) ≤ Real.exp (t * |(k : ℝ)|) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hk ht)
    have h2 : Real.exp (t * |(k : ℝ)|) ≤ Real.exp (t * k) + Real.exp (-t * k) := by
      rcases abs_choice (k : ℝ) with h | h <;> rw [h]
      · linarith [Real.exp_pos (-t * k)]
      · rw [show t * -(k : ℝ) = -t * k by ring]; linarith [Real.exp_pos (t * k)]
    rw [Real.exp_neg, ← div_eq_inv_mul, le_div_iff₀ (Real.exp_pos _), one_mul]
    linarith
  have hw : ∀ k, 0 ≤ lineWalk n k := lineWalk_nonneg n
  calc ∑ k ∈ (Finset.Icc (-(n : ℤ)) n).filter (fun k : ℤ => r ≤ |(k : ℝ)|), lineWalk n k
      ≤ ∑ k ∈ (Finset.Icc (-(n : ℤ)) n).filter (fun k : ℤ => r ≤ |(k : ℝ)|),
          lineWalk n k * (Real.exp (-(t * r)) * (Real.exp (t * k) + Real.exp (-t * k))) := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [Finset.mem_filter] at hk
        exact le_mul_of_one_le_right (hw k) (hpt k hk.2)
    _ ≤ ∑ k ∈ Finset.Icc (-(n : ℤ)) n,
          lineWalk n k * (Real.exp (-(t * r)) * (Real.exp (t * k) + Real.exp (-t * k))) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun k _ _ => mul_nonneg (hw k) (by positivity))
    _ = Real.exp (-(t * r)) * (Real.cosh t ^ n + Real.cosh (-t) ^ n) := by
        rw [← sum_lineWalk_mul_exp n t, ← sum_lineWalk_mul_exp n (-t),
          ← Finset.sum_add_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
    _ = 2 * (Real.exp (-(t * r)) * Real.cosh t ^ n) := by rw [Real.cosh_neg]; ring
    _ ≤ 2 * (Real.exp (-(t * r)) * Real.exp (t ^ 2 / 2) ^ n) := by
        gcongr
        exact Real.cosh_le_exp_half_sq t
    _ = 2 * Real.exp (-r ^ 2 / (2 * n)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, htdef]
        congr 2
        field_simp
        ring

/-! ### Chebyshev polynomials of a symmetric matrix -/

section Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- If the eigenvalues of a real symmetric matrix `A` lie in `[-1, 1]`, every entry of
`T_k(A)` is at most `1` in absolute value. -/
theorem abs_aeval_T_apply_le_one {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (hev : ∀ i, |hA.eigenvalues i| ≤ 1) (k : ℤ) (i j : ι) :
    |(aeval A (Chebyshev.T ℝ k)) i j| ≤ 1 := by
  have haeval : aeval A (Chebyshev.T ℝ k) = hA.cfc ((Chebyshev.T ℝ k).eval) := by
    rw [← cfc_polynomial (Chebyshev.T ℝ k) A hA.isSelfAdjoint, hA.cfc_eq]
  rw [haeval, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  have hcast : (Algebra.cast ∘ (fun x => Polynomial.eval x (Chebyshev.T ℝ k))
      ∘ hA.eigenvalues) = fun l => (Chebyshev.T ℝ k).eval (hA.eigenvalues l) := by
    funext l; rfl
  rw [hcast]
  set U : Matrix ι ι ℝ := (hA.eigenvectorUnitary : Matrix ι ι ℝ) with hU
  have hentry : (U * Matrix.diagonal (fun l => (Chebyshev.T ℝ k).eval (hA.eigenvalues l))
      * star U) i j = ∑ l, U i l * (Chebyshev.T ℝ k).eval (hA.eigenvalues l) * U j l := by
    rw [Matrix.mul_apply]
    simp only [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply, star_trivial]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.sum_eq_single l]
    · simp only [if_true]
    · intro b _ hb; simp [hb]
    · intro hl; exact absurd (Finset.mem_univ l) hl
  rw [hentry]
  have hrow : ∀ a : ι, ∑ l, U a l ^ 2 = 1 := by
    intro a
    have hUU : U * star U = 1 := by
      rw [hU]; exact Unitary.coe_mul_star_self hA.eigenvectorUnitary
    have h := congr_fun (congr_fun hUU a) a
    rw [Matrix.mul_apply] at h
    simp only [Matrix.star_apply, star_trivial, Matrix.one_apply_eq] at h
    rw [← h]
    apply Finset.sum_congr rfl; intro l _
    ring
  calc |∑ l, U i l * (Chebyshev.T ℝ k).eval (hA.eigenvalues l) * U j l|
      ≤ ∑ l, |U i l * (Chebyshev.T ℝ k).eval (hA.eigenvalues l) * U j l| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l, |U i l| * |U j l| := by
        apply Finset.sum_le_sum
        intro l _
        have hf : |(Chebyshev.T ℝ k).eval (hA.eigenvalues l)| ≤ 1 :=
          Chebyshev.abs_eval_T_real_le_one k (hev l)
        calc |U i l * (Chebyshev.T ℝ k).eval (hA.eigenvalues l) * U j l|
            = |U i l| * |(Chebyshev.T ℝ k).eval (hA.eigenvalues l)| * |U j l| := by
              rw [abs_mul, abs_mul]
          _ ≤ |U i l| * 1 * |U j l| := by gcongr
          _ = |U i l| * |U j l| := by ring
    _ ≤ ∑ l, (U i l ^ 2 + U j l ^ 2) / 2 := by
        apply Finset.sum_le_sum
        intro l _
        have h := two_mul_le_add_sq |U i l| |U j l|
        rw [sq_abs, sq_abs] at h
        linarith
    _ = 1 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, hrow i, hrow j]
        norm_num

/-- A real symmetric matrix `A = D Q D⁻¹`, with `D` a positive diagonal and `Q` nonnegative
with row sums at most one, has its eigenvalues in `[-1, 1]`. -/
theorem abs_eigenvalues_le_one {A Q : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (hQ : ∀ i j, 0 ≤ Q i j) (hrow : ∀ i, ∑ j, Q i j ≤ 1) (s : ι → ℝ)
    (hs : ∀ i, 0 < s i) (hAQ : ∀ i j, A i j = s i * Q i j / s j) (i : ι) :
    |hA.eigenvalues i| ≤ 1 := by
  set v : ι → ℝ := ⇑(hA.eigenvectorBasis i) with hv
  have hv_ne : v ≠ 0 := by
    rw [hv]
    simpa only [ne_eq, WithLp.ofLp_eq_zero] using hA.eigenvectorBasis.orthonormal.ne_zero i
  set lam : ℝ := hA.eigenvalues i with hlam
  have heig : A.mulVec v = lam • v := by
    rw [hv, hlam]
    exact hA.mulVec_eigenvectorBasis i
  set w : ι → ℝ := fun j => v j / s j with hw
  have hw_eq : ∀ j, ∑ l, Q j l * w l = lam * w j := by
    intro j
    have h1 : (A.mulVec v) j = lam * v j := by rw [heig]; rfl
    have h2 : (A.mulVec v) j = ∑ l, A j l * v l := rfl
    rw [h2] at h1
    have hlhs : ∑ l, A j l * v l = s j * ∑ l, Q j l * w l := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro l _
      rw [hAQ j l, hw]
      field_simp [hs l |>.ne']
    have hrhs : lam * v j = s j * (lam * w j) := by
      rw [hw]
      field_simp [hs j |>.ne']
    rw [hlhs, hrhs] at h1
    exact mul_left_cancel₀ (hs j).ne' h1
  obtain ⟨j, _, hjmax⟩ :=
    Finset.exists_max_image Finset.univ (fun j => |w j|) ⟨i, Finset.mem_univ i⟩
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hv_ne
  have hwk : w k ≠ 0 := by
    rw [hw]
    exact div_ne_zero hk (hs k).ne'
  have hwj_pos : 0 < |w j| :=
    lt_of_lt_of_le (abs_pos.mpr hwk) (hjmax k (Finset.mem_univ k))
  have hmain : |lam| * |w j| ≤ 1 * |w j| := by
    calc |lam| * |w j| = |∑ l, Q j l * w l| := by rw [← abs_mul, ← hw_eq j]
      _ ≤ ∑ l, |Q j l * w l| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ l, Q j l * |w l| := by
          apply Finset.sum_congr rfl; intro l _
          rw [abs_mul, abs_of_nonneg (hQ j l)]
      _ ≤ ∑ l, Q j l * |w j| := by
          apply Finset.sum_le_sum; intro l _
          exact mul_le_mul_of_nonneg_left (hjmax l (Finset.mem_univ l)) (hQ j l)
      _ = (∑ l, Q j l) * |w j| := by rw [Finset.sum_mul]
      _ ≤ 1 * |w j| := by gcongr; exact hrow j
  have hfin : |lam| ≤ 1 := le_of_mul_le_mul_right hmain hwj_pos
  simpa [hlam] using hfin

end Matrix

end LatticeProb.Graph
