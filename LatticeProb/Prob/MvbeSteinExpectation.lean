import Mathlib

/-!
# Packet P4 of the Raic Theorem 1.3 formalisation: polarisation and the Stein expectation

This file contains two independent pieces; the second does not use the first.

## Part 1 (report L10): polarisation of symmetric trilinear forms

If `T` is a continuous symmetric trilinear form on a real normed space `E` and
`|T(u,u,u)| ≤ M` for `‖u‖ ≤ 1`, then `|T(a,b,c)| ≤ (9/2) M` for `a, b, c` in the unit ball
(`mvbe_polarization`, `mvbe_polarization_norm`).  The proof is the identity
`48 T(a,b,c) = ∑_{ε ∈ {±1}³} ε₁ε₂ε₃ T̂(ε₁a+ε₂b+ε₃c)` with `T̂(u) = T(u,u,u)`
(`mvbe_polarization_identity`), `‖ε₁a+ε₂b+ε₃c‖ ≤ 3`, `T̂(3v) = 27 T̂(v)`, and
`8 · 27 / 48 = 9/2`.  Symmetry is stated through the two transpositions `(0 1)` and `(1 2)`
(`mvbe_swaps_of_perm` derives them from invariance under all permutations).  For
`D³g(x) = iteratedFDeriv ℝ 3 g x` of a `C³` function the symmetry is proved
(`mvbe_iteratedFDeriv_three_swap12`, `..._swap23`, from `ContDiffAt.isSymmSndFDerivAt`, which
Mathlib has only for order two), so `mvbe_polarization_iteratedFDeriv` and
`mvbe_norm_iteratedFDeriv_three_le` need no symmetry hypothesis.

## Part 2 (report L11): Raic's Lemma 2.4 (Stein expectation, due to Götze)

Paper (arXiv:1802.06475, Section 2): for independent `X_i` with sum `W`, `E W = 0`,
`Var W = Id`, and bounded `C³` functions `g` with bounded derivatives,
`E S g(W) = ∑_i E ⟨∇³g(W_i + θ X_i), X_i ⊗ X̃_i^{⊗2} - (1-θ) X_i^{⊗3}⟩`,
`S g(w) = Δ g(w) - ⟨∇ g(w), w⟩`, `W_i = W - X_i`, `X̃_i` an independent copy of `X_i`,
`θ ∼ U[0,1]` independent of everything.  The proof in the paper: write
`Δ g(W) = ⟨∇²g(W), Var W⟩ = ∑_i ⟨∇²g(W), E X_i^{⊗2}⟩` and `W = ∑_i X_i`, expand
`∇²g(W_i + X_i)` and `∇g(W_i + X_i)` around `W_i` with integral remainders (first- and
second-order Taylor formulas, `mvbe_taylor_stein`), then use independence of `W_i` and `X_i`
(the two zeroth-order terms involving `∇²g(W_i)` cancel, the term `⟨∇g(W_i), X_i⟩` has mean
zero because `E X_i = 0`; `mvbe_freeze_zero`).

The Lean statement (`mvbe_stein_expectation`, general inner product space version
`mvbe_stein_expectation_general`) is the paper's formula verbatim, with no change of form:

* the space is `E = EuclideanSpace ℝ (Fin d)`; `ν : Fin n → Measure E` are probability measures
  with `∫ ‖x‖³ d(ν i) < ∞` and `∫ x d(ν i) = 0` (each summand centred; the paper only needs
  `E W = 0` but its proof uses `E X_i = 0` in the same way);
* `∑ i, Cov (ν i) = Id` is `hcov : ∑ i, ∫ ⟪x,u⟫ ⟪x,v⟫ d(ν i) = ⟪u,v⟫`;
* `P = Measure.pi ν`, `W ω = ∑ i, ω i` (the coordinates `ω i` are independent with laws `ν i`
  by `iIndepFun_pi`; the independence is used through `IndepFun.map_prod_eq_prod_map_map`);
* `g : E → ℝ` is `C³` with `‖fderiv ℝ g‖ ≤ C₁`, `‖iteratedFDeriv ℝ 2 g‖ ≤ C₂`,
  `‖iteratedFDeriv ℝ 3 g‖ ≤ C₃` (boundedness of `g` itself is never used);
* `S g(w) = Δ g(w) - fderiv ℝ g w w` with the Laplacian the sum of
  `iteratedFDeriv ℝ 2 g w ![e_k, e_k]` over the orthonormal basis (`mvbeStein`,
  `mvbeLaplacian`; `mvbeLaplacian_eq_laplacian` identifies it with Mathlib's
  `Laplacian.laplacian`);
* the right-hand side integrates, for each `i`, over the product space
  `P ⊗ (ν i ⊗ U[0,1])` whose points `(ω, x̃, θ)` stand for `(X, X̃_i, θ)`, with
  `U[0,1] = volume.restrict (Set.Icc 0 1)`, the integrand being
  `D³g(W_i + θ X_i)[X_i, X̃_i, X̃_i] - (1-θ) D³g(W_i + θ X_i)[X_i, X_i, X_i]`
  (`mvbeSteinRem`), which is `⟨∇³g(W_i + θ X_i), X_i ⊗ X̃_i^{⊗2} - (1-θ) X_i^{⊗3}⟩`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory

namespace LatticeProb

section Polarisation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mvbe_T3_add_left (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ) (x y u v : E) :
    T ![x + y, u, v] = T ![x, u, v] + T ![y, u, v] := by
  have h := T.map_update_add ![x, u, v] 0 x y
  have e : ∀ w : E, Function.update ![x, u, v] 0 w = ![w, u, v] := fun w => by
    ext i; fin_cases i <;> simp
  simpa [e] using h

theorem mvbe_T3_add_mid (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ) (x y u v : E) :
    T ![u, x + y, v] = T ![u, x, v] + T ![u, y, v] := by
  have h := T.map_update_add ![u, x, v] 1 x y
  have e : ∀ w : E, Function.update ![u, x, v] 1 w = ![u, w, v] := fun w => by
    ext i; fin_cases i <;> simp
  simpa [e] using h

theorem mvbe_T3_add_right (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ) (x y u v : E) :
    T ![u, v, x + y] = T ![u, v, x] + T ![u, v, y] := by
  have h := T.map_update_add ![u, v, x] 2 x y
  have e : ∀ w : E, Function.update ![u, v, x] 2 w = ![u, v, w] := fun w => by
    ext i; fin_cases i <;> simp
  simpa [e] using h

theorem mvbe_T3_smul_left (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ) (r : ℝ)
    (x u v : E) : T ![r • x, u, v] = r * T ![x, u, v] := by
  have h := T.map_update_smul ![x, u, v] 0 r x
  have e : ∀ w : E, Function.update ![x, u, v] 0 w = ![w, u, v] := fun w => by
    ext i; fin_cases i <;> simp
  simpa [e] using h

theorem mvbe_T3_smul_mid (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ) (r : ℝ)
    (x u v : E) : T ![u, r • x, v] = r * T ![u, x, v] := by
  have h := T.map_update_smul ![u, x, v] 1 r x
  have e : ∀ w : E, Function.update ![u, x, v] 1 w = ![u, w, v] := fun w => by
    ext i; fin_cases i <;> simp
  simpa [e] using h

theorem mvbe_T3_smul_right (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ) (r : ℝ)
    (x u v : E) : T ![u, v, r • x] = r * T ![u, v, x] := by
  have h := T.map_update_smul ![u, v, x] 2 r x
  have e : ∀ w : E, Function.update ![u, v, x] 2 w = ![u, v, w] := fun w => by
    ext i; fin_cases i <;> simp
  simpa [e] using h


section Expand

variable (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
  (s12 : ∀ p q r : E, T ![p, q, r] = T ![q, p, r])
  (s23 : ∀ p q r : E, T ![p, q, r] = T ![p, r, q])

include s12 s23 in
theorem mvbe_T3_expand (x y z : E) :
    T ![x + y + z, x + y + z, x + y + z] =
      T ![x, x, x] + T ![y, y, y] + T ![z, z, z]
      + 3 * T ![x, x, y] + 3 * T ![x, y, y] + 3 * T ![x, x, z] + 3 * T ![x, z, z]
      + 3 * T ![y, y, z] + 3 * T ![y, z, z] + 6 * T ![x, y, z] := by
  have e1 : T ![x, y, x] = T ![x, x, y] := s23 _ _ _
  have e2 : T ![y, x, x] = T ![x, x, y] := (s12 y x x).trans (s23 x y x)
  have e3 : T ![y, x, y] = T ![x, y, y] := s12 _ _ _
  have e4 : T ![y, y, x] = T ![x, y, y] := (s23 y y x).trans (s12 y x y)
  have e5 : T ![x, z, x] = T ![x, x, z] := s23 _ _ _
  have e6 : T ![z, x, x] = T ![x, x, z] := (s12 z x x).trans (s23 x z x)
  have e7 : T ![z, x, z] = T ![x, z, z] := s12 _ _ _
  have e8 : T ![z, z, x] = T ![x, z, z] := (s23 z z x).trans (s12 z x z)
  have e9 : T ![y, z, y] = T ![y, y, z] := s23 _ _ _
  have e10 : T ![z, y, y] = T ![y, y, z] := (s12 z y y).trans (s23 y z y)
  have e11 : T ![z, y, z] = T ![y, z, z] := s12 _ _ _
  have e12 : T ![z, z, y] = T ![y, z, z] := (s23 z z y).trans (s12 z y z)
  have e13 : T ![x, z, y] = T ![x, y, z] := s23 x z y
  have e14 : T ![y, x, z] = T ![x, y, z] := s12 y x z
  have e15 : T ![y, z, x] = T ![x, y, z] := (s23 y z x).trans (s12 y x z)
  have e16 : T ![z, x, y] = T ![x, y, z] := (s12 z x y).trans (s23 x z y)
  have e17 : T ![z, y, x] = T ![x, y, z] := (s23 z y x).trans e16
  simp only [mvbe_T3_add_left, mvbe_T3_add_mid, mvbe_T3_add_right, e1, e2, e3, e4, e5, e6, e7,
    e8, e9, e10, e11, e12, e13, e14, e15, e16, e17]
  ring

include s12 s23 in
theorem mvbe_T3_cubic (a b c : E) (s₁ s₂ s₃ : ℝ) :
    T ![s₁ • a + s₂ • b + s₃ • c, s₁ • a + s₂ • b + s₃ • c, s₁ • a + s₂ • b + s₃ • c] =
      s₁ ^ 3 * T ![a, a, a] + s₂ ^ 3 * T ![b, b, b] + s₃ ^ 3 * T ![c, c, c]
      + 3 * s₁ ^ 2 * s₂ * T ![a, a, b] + 3 * s₁ * s₂ ^ 2 * T ![a, b, b]
      + 3 * s₁ ^ 2 * s₃ * T ![a, a, c] + 3 * s₁ * s₃ ^ 2 * T ![a, c, c]
      + 3 * s₂ ^ 2 * s₃ * T ![b, b, c] + 3 * s₂ * s₃ ^ 2 * T ![b, c, c]
      + 6 * s₁ * s₂ * s₃ * T ![a, b, c] := by
  rw [mvbe_T3_expand T s12 s23]
  simp only [mvbe_T3_smul_left, mvbe_T3_smul_mid, mvbe_T3_smul_right]
  ring


include s12 s23 in
/-- The polarisation identity `48 T(a,b,c) = ∑_{ε ∈ {±1}³} ε₁ε₂ε₃ T̂(ε₁a+ε₂b+ε₃c)`. -/
theorem mvbe_polarization_identity (a b c : E) :
    48 * T ![a, b, c] = ∑ e₁ ∈ ({1, -1} : Finset ℝ), ∑ e₂ ∈ ({1, -1} : Finset ℝ),
      ∑ e₃ ∈ ({1, -1} : Finset ℝ), e₁ * e₂ * e₃ *
        T ![e₁ • a + e₂ • b + e₃ • c, e₁ • a + e₂ • b + e₃ • c, e₁ • a + e₂ • b + e₃ • c] := by
  have h : (1 : ℝ) ≠ -1 := by norm_num
  simp only [Finset.sum_pair h, mvbe_T3_cubic T s12 s23]
  ring

end Expand

theorem mvbe_T3_cube_scale (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ) (r : ℝ)
    (v : E) : T ![r • v, r • v, r • v] = r ^ 3 * T ![v, v, v] := by
  rw [mvbe_T3_smul_left, mvbe_T3_smul_mid, mvbe_T3_smul_right]
  ring

/-- Growth of the cubic form on the ball of radius 3, from the unit ball bound. -/
theorem mvbe_cube_bound_three (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ) {M : ℝ}
    (hM : ∀ u : E, ‖u‖ ≤ 1 → |T ![u, u, u]| ≤ M) {u : E} (hu : ‖u‖ ≤ 3) :
    |T ![u, u, u]| ≤ 27 * M := by
  have hv : ‖(3 : ℝ)⁻¹ • u‖ ≤ 1 := by
    rw [norm_smul, norm_inv, Real.norm_ofNat]
    linarith
  have h3 : T ![u, u, u] = 27 * T ![(3 : ℝ)⁻¹ • u, (3 : ℝ)⁻¹ • u, (3 : ℝ)⁻¹ • u] := by
    have := mvbe_T3_cube_scale T 3 ((3 : ℝ)⁻¹ • u)
    rw [smul_smul, mul_inv_cancel₀ (by norm_num : (3 : ℝ) ≠ 0), one_smul] at this
    rw [this]
    norm_num
  rw [h3, abs_mul]
  have := hM _ hv
  norm_num
  linarith

/-- **Polarisation for symmetric trilinear forms** (constant `n^n/n! = 27/6 = 9/2`):
if a symmetric trilinear form satisfies `|T(u,u,u)| ≤ M` on the unit ball then
`|T(a,b,c)| ≤ (9/2) M` for `a, b, c` in the unit ball. Symmetry is given by the two
transpositions `(0 1)` and `(1 2)`. -/
theorem mvbe_polarization (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (s12 : ∀ p q r : E, T ![p, q, r] = T ![q, p, r])
    (s23 : ∀ p q r : E, T ![p, q, r] = T ![p, r, q]) {M : ℝ}
    (hM : ∀ u : E, ‖u‖ ≤ 1 → |T ![u, u, u]| ≤ M) {a b c : E}
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
    |T ![a, b, c]| ≤ 9 / 2 * M := by
  have hS : ∀ e ∈ ({1, -1} : Finset ℝ), |e| = 1 := by
    intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl <;> simp
  have hterm : ∀ e₁ ∈ ({1, -1} : Finset ℝ), ∀ e₂ ∈ ({1, -1} : Finset ℝ),
      ∀ e₃ ∈ ({1, -1} : Finset ℝ),
      |e₁ * e₂ * e₃ * T ![e₁ • a + e₂ • b + e₃ • c, e₁ • a + e₂ • b + e₃ • c,
        e₁ • a + e₂ • b + e₃ • c]| ≤ 27 * M := by
    intro e₁ h₁ e₂ h₂ e₃ h₃
    have hn : ‖e₁ • a + e₂ • b + e₃ • c‖ ≤ 3 := by
      calc ‖e₁ • a + e₂ • b + e₃ • c‖ ≤ ‖e₁ • a + e₂ • b‖ + ‖e₃ • c‖ := norm_add_le _ _
        _ ≤ ‖e₁ • a‖ + ‖e₂ • b‖ + ‖e₃ • c‖ := by gcongr; exact norm_add_le _ _
        _ ≤ 3 := by
          rw [norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
            Real.norm_eq_abs, hS e₁ h₁, hS e₂ h₂, hS e₃ h₃]
          linarith
    rw [abs_mul, abs_mul, abs_mul, hS e₁ h₁, hS e₂ h₂, hS e₃ h₃]
    simpa using mvbe_cube_bound_three T hM hn
  have hid := mvbe_polarization_identity T s12 s23 a b c
  have h48 : 48 * |T ![a, b, c]| ≤ 8 * (27 * M) := by
    calc 48 * |T ![a, b, c]| = |48 * T ![a, b, c]| := by
          rw [abs_mul]; norm_num
      _ = |∑ e₁ ∈ ({1, -1} : Finset ℝ), ∑ e₂ ∈ ({1, -1} : Finset ℝ),
          ∑ e₃ ∈ ({1, -1} : Finset ℝ), e₁ * e₂ * e₃ *
          T ![e₁ • a + e₂ • b + e₃ • c, e₁ • a + e₂ • b + e₃ • c,
            e₁ • a + e₂ • b + e₃ • c]| := by rw [hid]
      _ ≤ ∑ e₁ ∈ ({1, -1} : Finset ℝ), ∑ e₂ ∈ ({1, -1} : Finset ℝ),
          ∑ e₃ ∈ ({1, -1} : Finset ℝ), 27 * M := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e₁ h₁ => ?_)
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun e₂ h₂ => ?_)
        exact (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun e₃ h₃ => hterm e₁ h₁ e₂ h₂ e₃ h₃)
      _ = 8 * (27 * M) := by
        have h : (1 : ℝ) ≠ -1 := by norm_num
        simp only [Finset.sum_pair h]
        ring
  linarith


/-- Invariance under all permutations of the three arguments gives the two transposition
hypotheses used in `mvbe_polarization`. -/
theorem mvbe_swaps_of_perm (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (h : ∀ (σ : Equiv.Perm (Fin 3)) (m : Fin 3 → E), T (fun i => m (σ i)) = T m) :
    (∀ p q r : E, T ![p, q, r] = T ![q, p, r]) ∧ (∀ p q r : E, T ![p, q, r] = T ![p, r, q]) := by
  constructor
  · intro p q r
    have := h (Equiv.swap 0 1) ![p, q, r]
    have e : (fun i => (![p, q, r] : Fin 3 → E) ((Equiv.swap (0 : Fin 3) 1) i)) = ![q, p, r] := by
      ext i; fin_cases i <;> simp [Equiv.swap_apply_def]
    rw [e] at this
    exact this.symm
  · intro p q r
    have := h (Equiv.swap 1 2) ![p, q, r]
    have e : (fun i => (![p, q, r] : Fin 3 → E) ((Equiv.swap (1 : Fin 3) 2) i)) = ![p, r, q] := by
      ext i; fin_cases i <;> simp [Equiv.swap_apply_def]
    rw [e] at this
    exact this.symm

/-- The operator-norm form of polarisation: `‖T‖ ≤ (9/2) M`. -/
theorem mvbe_polarization_norm (T : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (s12 : ∀ p q r : E, T ![p, q, r] = T ![q, p, r])
    (s23 : ∀ p q r : E, T ![p, q, r] = T ![p, r, q]) {M : ℝ}
    (hM : ∀ u : E, ‖u‖ ≤ 1 → |T ![u, u, u]| ≤ M) : ‖T‖ ≤ 9 / 2 * M := by
  have hM0 : 0 ≤ M := by
    have := hM 0 (by simp)
    exact (abs_nonneg _).trans this
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun m => ?_
  have hm : m = ![m 0, m 1, m 2] := by
    ext i; fin_cases i <;> simp
  rw [Fin.prod_univ_three]
  by_cases h0 : m 0 = 0
  · have : T m = 0 := T.map_coord_zero 0 h0
    rw [this]; simp [h0]
  by_cases h1 : m 1 = 0
  · have : T m = 0 := T.map_coord_zero 1 h1
    rw [this]; simp [h1]
  by_cases h2 : m 2 = 0
  · have : T m = 0 := T.map_coord_zero 2 h2
    rw [this]; simp [h2]
  have n0 : 0 < ‖m 0‖ := norm_pos_iff.2 h0
  have n1 : 0 < ‖m 1‖ := norm_pos_iff.2 h1
  have n2 : 0 < ‖m 2‖ := norm_pos_iff.2 h2
  have key := mvbe_polarization T s12 s23 hM
    (a := ‖m 0‖⁻¹ • m 0) (b := ‖m 1‖⁻¹ • m 1) (c := ‖m 2‖⁻¹ • m 2)
    (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ n0.ne'])
    (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ n1.ne'])
    (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ n2.ne'])
  have e : T m = ‖m 0‖ * ‖m 1‖ * ‖m 2‖ * T ![‖m 0‖⁻¹ • m 0, ‖m 1‖⁻¹ • m 1, ‖m 2‖⁻¹ • m 2] := by
    rw [mvbe_T3_smul_left, mvbe_T3_smul_mid, mvbe_T3_smul_right, ← hm]
    field_simp
  have hP : 0 ≤ ‖m 0‖ * ‖m 1‖ * ‖m 2‖ := by positivity
  rw [e, Real.norm_eq_abs, abs_mul, abs_of_nonneg hP]
  calc ‖m 0‖ * ‖m 1‖ * ‖m 2‖ * |T ![‖m 0‖⁻¹ • m 0, ‖m 1‖⁻¹ • m 1, ‖m 2‖⁻¹ • m 2]|
      ≤ ‖m 0‖ * ‖m 1‖ * ‖m 2‖ * (9 / 2 * M) := by gcongr
    _ = 9 / 2 * M * (‖m 0‖ * ‖m 1‖ * ‖m 2‖) := by ring


section IteratedFDeriv

variable {g : E → ℝ}

/-- Symmetry of the second Fréchet derivative of a `C²` function. -/
theorem mvbe_iteratedFDeriv_two_symm {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → F} (hg : ContDiff ℝ 2 g) (x a b : E) :
    iteratedFDeriv ℝ 2 g x ![a, b] = iteratedFDeriv ℝ 2 g x ![b, a] := by
  have h : IsSymmSndFDerivAt ℝ g x := hg.contDiffAt.isSymmSndFDerivAt (by simp)
  simp only [iteratedFDeriv_two_apply]
  exact h a b

/-- The third Fréchet derivative of a `C³` function is symmetric in its last two arguments. -/
theorem mvbe_iteratedFDeriv_three_swap23 (hg : ContDiff ℝ 3 g) (x a b c : E) :
    iteratedFDeriv ℝ 3 g x ![a, b, c] = iteratedFDeriv ℝ 3 g x ![a, c, b] := by
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ 2 g) x :=
    hg.differentiable_iteratedFDeriv (by norm_num) x
  have hg2 : ContDiff ℝ 2 g := hg.of_le (by norm_num)
  rw [hd.iteratedFDeriv_succ_apply_left', hd.iteratedFDeriv_succ_apply_left']
  have : (fun y => iteratedFDeriv ℝ 2 g y (Fin.tail ![a, b, c])) =
      fun y => iteratedFDeriv ℝ 2 g y (Fin.tail ![a, c, b]) := by
    funext y
    simpa using mvbe_iteratedFDeriv_two_symm hg2 y b c
  rw [this]
  rfl

/-- The third Fréchet derivative of a `C³` function is symmetric in its first two arguments. -/
theorem mvbe_iteratedFDeriv_three_swap12 (hg : ContDiff ℝ 3 g) (x a b c : E) :
    iteratedFDeriv ℝ 3 g x ![a, b, c] = iteratedFDeriv ℝ 3 g x ![b, a, c] := by
  have hh : ContDiff ℝ 2 (fderiv ℝ g) := hg.fderiv_right (by norm_num)
  rw [iteratedFDeriv_succ_apply_right (m := ![a, b, c]),
    iteratedFDeriv_succ_apply_right (m := ![b, a, c])]
  have e1 : Fin.init (![a, b, c] : Fin 3 → E) = ![a, b] := by
    ext i; fin_cases i <;> simp [Fin.init]
  have e2 : Fin.init (![b, a, c] : Fin 3 → E) = ![b, a] := by
    ext i; fin_cases i <;> simp [Fin.init]
  rw [e1, e2]
  have := mvbe_iteratedFDeriv_two_symm hh x a b
  simp only [Fin.last] at *
  simp [this]

/-- **Polarisation for the third derivative of a `C³` function.** If
`|D³g(x)(u,u,u)| ≤ M` for `‖u‖ ≤ 1` then `|D³g(x)(a,b,c)| ≤ (9/2) M` for `a,b,c` in the unit
ball.  Symmetry of `D³g(x)` is proved here (`mvbe_iteratedFDeriv_three_swap12`,
`mvbe_iteratedFDeriv_three_swap23`) from Mathlib's `ContDiffAt.isSymmSndFDerivAt`. -/
theorem mvbe_polarization_iteratedFDeriv (hg : ContDiff ℝ 3 g) (x : E) {M : ℝ}
    (hM : ∀ u : E, ‖u‖ ≤ 1 → |iteratedFDeriv ℝ 3 g x ![u, u, u]| ≤ M) {a b c : E}
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) :
    |iteratedFDeriv ℝ 3 g x ![a, b, c]| ≤ 9 / 2 * M :=
  mvbe_polarization (iteratedFDeriv ℝ 3 g x)
    (fun p q r => mvbe_iteratedFDeriv_three_swap12 hg x p q r)
    (fun p q r => mvbe_iteratedFDeriv_three_swap23 hg x p q r) hM ha hb hc

/-- Operator-norm form: `‖D³g(x)‖ ≤ (9/2) sup_{‖u‖≤1} |D³g(x)(u,u,u)|`. -/
theorem mvbe_norm_iteratedFDeriv_three_le (hg : ContDiff ℝ 3 g) (x : E) {M : ℝ}
    (hM : ∀ u : E, ‖u‖ ≤ 1 → |iteratedFDeriv ℝ 3 g x ![u, u, u]| ≤ M) :
    ‖iteratedFDeriv ℝ 3 g x‖ ≤ 9 / 2 * M :=
  mvbe_polarization_norm (iteratedFDeriv ℝ 3 g x)
    (fun p q r => mvbe_iteratedFDeriv_three_swap12 hg x p q r)
    (fun p q r => mvbe_iteratedFDeriv_three_swap23 hg x p q r) hM

end IteratedFDeriv

end Polarisation


section Taylor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : E → ℝ}

/-- Derivative of `s ↦ D^n g (a + s b) m` along a line. -/
theorem mvbe_hasDerivAt_line {n : ℕ} (hg : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) g)
    (a b : E) (m : Fin n → E) (s : ℝ) :
    HasDerivAt (fun s : ℝ => iteratedFDeriv ℝ n g (a + s • b) m)
      (iteratedFDeriv ℝ (n + 1) g (a + s • b) (Fin.cons b m)) s := by
  have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n g) (a + s • b) :=
    hg.differentiable_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_self n) _
  have h1 := hd.iteratedFDeriv_succ_apply_left' (m := Fin.cons b m)
  simp only [Fin.tail_cons, Fin.cons_zero] at h1
  rw [h1]
  have h2 : HasFDerivAt (fun y => iteratedFDeriv ℝ n g y m)
      (fderiv ℝ (fun y => iteratedFDeriv ℝ n g y m) (a + s • b)) (a + s • b) :=
    (hd.continuousMultilinear_apply_const m).hasFDerivAt
  have h3 : HasDerivAt (fun s : ℝ => a + s • b) b s := by
    simpa using ((hasDerivAt_id s).smul_const b).const_add a
  exact h2.comp_hasDerivAt s h3


/-- Continuity of `y ↦ D^k g y m` for a `C^k` function. -/
theorem mvbe_continuous_iter {k : ℕ} (hg : ContDiff ℝ (k : WithTop ℕ∞) g) (m : Fin k → E) :
    Continuous fun y => iteratedFDeriv ℝ k g y m := by
  have := hg.continuous_iteratedFDeriv (m := k) le_rfl
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => E) ℝ m).continuous.comp this

theorem mvbe_continuous_line {k : ℕ} (hg : ContDiff ℝ (k : WithTop ℕ∞) g) (a b : E)
    (m : Fin k → E) :
    Continuous fun θ : ℝ => iteratedFDeriv ℝ k g (a + θ • b) m :=
  (mvbe_continuous_iter hg m).comp (by fun_prop)

theorem mvbe_taylor_second (hg : ContDiff ℝ 3 g) (a b u : E) :
    iteratedFDeriv ℝ 2 g (a + b) ![u, u] - iteratedFDeriv ℝ 2 g a ![u, u] =
      ∫ θ in (0 : ℝ)..1, iteratedFDeriv ℝ 3 g (a + θ • b) ![b, u, u] := by
  have hg' : ContDiff ℝ ((2 + 1 : ℕ) : WithTop ℕ∞) g := by exact_mod_cast hg
  have hg3 : ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞) g := by exact_mod_cast hg
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun θ : ℝ => iteratedFDeriv ℝ 2 g (a + θ • b) ![u, u])]
  · simp
  · intro θ _
    exact mvbe_hasDerivAt_line hg' a b ![u, u] θ
  · exact (mvbe_continuous_line hg3 a b ![b, u, u]).intervalIntegrable _ _


theorem mvbe_taylor_first (hg : ContDiff ℝ 3 g) (a b : E) :
    fderiv ℝ g (a + b) b - fderiv ℝ g a b - iteratedFDeriv ℝ 2 g a ![b, b] =
      ∫ θ in (0 : ℝ)..1, (1 - θ) * iteratedFDeriv ℝ 3 g (a + θ • b) ![b, b, b] := by
  have hg1 : ContDiff ℝ ((1 + 1 : ℕ) : WithTop ℕ∞) g := by exact_mod_cast hg.of_le (by norm_num)
  have hg2 : ContDiff ℝ ((2 + 1 : ℕ) : WithTop ℕ∞) g := by exact_mod_cast hg
  have hg3 : ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞) g := by exact_mod_cast hg
  have key : ∀ θ ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun θ : ℝ => (1 - θ) * iteratedFDeriv ℝ 2 g (a + θ • b) ![b, b] +
        iteratedFDeriv ℝ 1 g (a + θ • b) ![b])
        ((1 - θ) * iteratedFDeriv ℝ 3 g (a + θ • b) ![b, b, b]) θ := by
    intro θ _
    have h1 : HasDerivAt (fun s : ℝ => iteratedFDeriv ℝ 1 g (a + s • b) ![b])
        (iteratedFDeriv ℝ 2 g (a + θ • b) ![b, b]) θ :=
      mvbe_hasDerivAt_line hg1 a b ![b] θ
    have h2 : HasDerivAt (fun s : ℝ => iteratedFDeriv ℝ 2 g (a + s • b) ![b, b])
        (iteratedFDeriv ℝ 3 g (a + θ • b) ![b, b, b]) θ :=
      mvbe_hasDerivAt_line hg2 a b ![b, b] θ
    have h0 : HasDerivAt (fun θ : ℝ => 1 - θ) (-1) θ := by
      simpa using (hasDerivAt_id θ).const_sub 1
    have h3 := (h0.mul h2).add h1
    refine h3.congr_deriv ?_
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt key]
  · simp
    ring
  · exact (continuous_const.sub continuous_id).mul (mvbe_continuous_line hg3 a b ![b, b, b])
      |>.intervalIntegrable _ _


/-- The integrand of the third-order term of Raic's Lemma 2.4 along the segment `[a, a+b]`:
`D³g(a + θ b)[b, u, u] − (1 − θ) D³g(a + θ b)[b, b, b]`. -/
noncomputable def mvbeSteinRem (g : E → ℝ) (a b u : E) (θ : ℝ) : ℝ :=
  iteratedFDeriv ℝ 3 g (a + θ • b) ![b, u, u] -
    (1 - θ) * iteratedFDeriv ℝ 3 g (a + θ • b) ![b, b, b]

theorem mvbe_continuous_steinRem (hg : ContDiff ℝ 3 g) (a b u : E) :
    Continuous (mvbeSteinRem g a b u) := by
  have hg3 : ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞) g := by exact_mod_cast hg
  unfold mvbeSteinRem
  exact (mvbe_continuous_line hg3 a b ![b, u, u]).sub
    ((continuous_const.sub continuous_id).mul (mvbe_continuous_line hg3 a b ![b, b, b]))

/-- The deterministic Taylor step of Raic's Lemma 2.4. -/
theorem mvbe_taylor_stein (hg : ContDiff ℝ 3 g) (a b u : E) :
    iteratedFDeriv ℝ 2 g (a + b) ![u, u] - fderiv ℝ g (a + b) b =
      (iteratedFDeriv ℝ 2 g a ![u, u] - fderiv ℝ g a b - iteratedFDeriv ℝ 2 g a ![b, b]) +
        ∫ θ, mvbeSteinRem g a b u θ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) := by
  have hg3 : ContDiff ℝ ((3 : ℕ) : WithTop ℕ∞) g := by exact_mod_cast hg
  have hI : ∫ θ, mvbeSteinRem g a b u θ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) =
      ∫ θ in (0 : ℝ)..1, mvbeSteinRem g a b u θ := by
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc]
  have i1 : IntervalIntegrable (fun θ : ℝ => iteratedFDeriv ℝ 3 g (a + θ • b) ![b, u, u])
      volume 0 1 := (mvbe_continuous_line hg3 a b ![b, u, u]).intervalIntegrable _ _
  have i2 : IntervalIntegrable
      (fun θ : ℝ => (1 - θ) * iteratedFDeriv ℝ 3 g (a + θ • b) ![b, b, b]) volume 0 1 :=
    ((continuous_const.sub continuous_id).mul
      (mvbe_continuous_line hg3 a b ![b, b, b])).intervalIntegrable _ _
  rw [hI]
  unfold mvbeSteinRem
  rw [intervalIntegral.integral_sub i1 i2, ← mvbe_taylor_second hg a b u,
    ← mvbe_taylor_first hg a b]
  ring

end Taylor


section Freeze

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] {n : ℕ} (ν : Fin n → Measure E) [∀ i, IsProbabilityMeasure (ν i)]

/-- `W_i = ∑_{j ≠ i} ω j`. -/
def mvbeWithout (i : Fin n) (ω : Fin n → E) : E := ∑ j ∈ Finset.univ.erase i, ω j

theorem mvbe_measurable_without (i : Fin n) : Measurable (mvbeWithout (E := E) i) := by
  unfold mvbeWithout
  exact Finset.measurable_sum _ fun j _ => measurable_pi_apply j

theorem mvbe_without_add (i : Fin n) (ω : Fin n → E) :
    mvbeWithout i ω + ω i = ∑ j, ω j := by
  unfold mvbeWithout
  exact Finset.sum_erase_add _ _ (Finset.mem_univ i)

theorem mvbe_indep_without (i : Fin n) :
    IndepFun (mvbeWithout i) (fun ω : Fin n → E => ω i) (Measure.pi ν) := by
  have h := iIndepFun_pi (μ := ν) (X := fun _ => (id : E → E)) (fun _ => aemeasurable_id)
  have h2 := h.indepFun_finsetSum_of_notMem (fun j => measurable_pi_apply j)
    (s := Finset.univ.erase i) (i := i) (Finset.notMem_erase i _)
  have e : (∑ j ∈ Finset.univ.erase i, fun ω : Fin n → E => id (ω j)) = mvbeWithout i := by
    funext ω
    simp [mvbeWithout, Finset.sum_apply]
  rw [e] at h2
  exact h2


/-- **Freezing lemma.**  Because `W_i` and `X_i = ω i` are independent under `Measure.pi ν`,
integrating a function `F (W_i, X_i)` is the same as integrating `x ↦ F (W_i, x)` against the
law `ν i` of an independent copy.  The integrand is continuous with polynomial growth. -/
theorem mvbe_integral_freeze (i : Fin n) (F : E → E → ℝ)
    (hF : Continuous fun q : E × E => F q.1 q.2) (C : ℝ)
    (hC : ∀ w x, |F w x| ≤ C * (1 + ‖x‖ ^ 3)) (hmom : Integrable (fun x => ‖x‖ ^ 3) (ν i)) :
    ∫ ω, F (mvbeWithout i ω) (ω i) ∂Measure.pi ν =
      ∫ ω, ∫ x, F (mvbeWithout i ω) x ∂ν i ∂Measure.pi ν := by
  set P := Measure.pi ν with hP
  have hmW : Measurable (mvbeWithout (E := E) i) := mvbe_measurable_without i
  have hmX : Measurable (fun ω : Fin n → E => ω i) := measurable_pi_apply i
  have hmap := (mvbe_indep_without ν i).map_prod_eq_prod_map_map hmW.aemeasurable
    hmX.aemeasurable
  have hX : P.map (fun ω : Fin n → E => ω i) = ν i := (measurePreserving_eval ν i).map_eq
  rw [hX] at hmap
  have hFm : AEStronglyMeasurable (fun q : E × E => F q.1 q.2)
      (P.map fun ω => (mvbeWithout i ω, ω i)) := hF.aestronglyMeasurable
  have hint : Integrable (fun q : E × E => F q.1 q.2) ((P.map (mvbeWithout i)).prod (ν i)) := by
    have h1 : Integrable (fun q : E × E => (1 : ℝ) * (C * (1 + ‖q.2‖ ^ 3)))
        ((P.map (mvbeWithout i)).prod (ν i)) :=
      (integrable_const (1 : ℝ)).mul_prod (((integrable_const (1 : ℝ)).add hmom).const_mul C)
    refine h1.mono' hF.aestronglyMeasurable (Filter.Eventually.of_forall fun q => ?_)
    simpa using hC q.1 q.2
  calc ∫ ω, F (mvbeWithout i ω) (ω i) ∂P
      = ∫ q, F q.1 q.2 ∂(P.map fun ω => (mvbeWithout i ω, ω i)) := by
        rw [integral_map (hmW.prodMk hmX).aemeasurable hFm]
    _ = ∫ q, F q.1 q.2 ∂((P.map (mvbeWithout i)).prod (ν i)) := by rw [hmap]
    _ = ∫ w, ∫ x, F w x ∂ν i ∂(P.map (mvbeWithout i)) := integral_prod _ hint
    _ = ∫ ω, ∫ x, F (mvbeWithout i ω) x ∂ν i ∂P := by
        rw [integral_map hmW.aemeasurable]
        exact (hF.stronglyMeasurable.integral_prod_right').aestronglyMeasurable

end Freeze


theorem mvbe_sq_le (t : ℝ) (ht : 0 ≤ t) : t ^ 2 ≤ 1 + t ^ 3 := by
  rcases le_total t 1 with h | h
  · nlinarith [sq_nonneg t, pow_nonneg ht 3]
  · nlinarith [sq_nonneg t, mul_nonneg ht (sq_nonneg t)]

theorem mvbe_self_le (t : ℝ) (ht : 0 ≤ t) : t ≤ 1 + t ^ 3 := by
  rcases le_total t 1 with h | h
  · nlinarith [pow_nonneg ht 3]
  · nlinarith [sq_nonneg t, mul_nonneg ht (sq_nonneg t)]

section Trace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem mvbe_integrable_of_bound {μ : Measure E} [IsFiniteMeasure μ]
    (hmom : Integrable (fun x => ‖x‖ ^ 3) μ) {f : E → ℝ} (hf : Continuous f) (C : ℝ)
    (hC : ∀ x, |f x| ≤ C * (1 + ‖x‖ ^ 3)) : Integrable f μ := by
  refine (((integrable_const (1 : ℝ)).add hmom).const_mul C).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  simpa using hC x

theorem mvbe_bilin_diag (b : OrthonormalBasis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ) (x : E) :
    B x x = ∑ k, ∑ l, inner ℝ x (b k) * inner ℝ x (b l) * B (b k) (b l) := by
  have hx : x = ∑ k, inner ℝ (b k) x • b k := (b.sum_repr' x).symm
  conv_lhs => rw [hx]
  simp only [map_sum, sum_apply, map_smul, smul_apply,
    smul_eq_mul, Finset.mul_sum, real_inner_comm x]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring


theorem mvbe_integrable_inner_mul {μ : Measure E} [IsFiniteMeasure μ]
    (hmom : Integrable (fun x => ‖x‖ ^ 3) μ) (u v : E) :
    Integrable (fun x => inner ℝ x u * inner ℝ x v) μ := by
  refine mvbe_integrable_of_bound hmom (by fun_prop) (‖u‖ * ‖v‖) fun x => ?_
  rw [abs_mul]
  have h1 : |inner ℝ x u| ≤ ‖x‖ * ‖u‖ := by
    simpa [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) x u
  have h2 : |inner ℝ x v| ≤ ‖x‖ * ‖v‖ := by
    simpa [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) x v
  calc |inner ℝ x u| * |inner ℝ x v| ≤ (‖x‖ * ‖u‖) * (‖x‖ * ‖v‖) := by gcongr
    _ = ‖u‖ * ‖v‖ * ‖x‖ ^ 2 := by ring
    _ ≤ ‖u‖ * ‖v‖ * (1 + ‖x‖ ^ 3) := by
        gcongr
        exact mvbe_sq_le _ (norm_nonneg x)

/-- Trace of a bilinear form against the covariance: if `∑ᵢ Cov(νᵢ) = Id` then
`∑ᵢ ∫ B(x,x) dνᵢ = ∑ₖ B(eₖ,eₖ)`. -/
theorem mvbe_trace_cov {n : ℕ} (ν : Fin n → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (hmom : ∀ i, Integrable (fun x => ‖x‖ ^ 3) (ν i))
    (hcov : ∀ u v : E, ∑ i, ∫ x, inner ℝ x u * inner ℝ x v ∂ν i = inner ℝ u v)
    (b : OrthonormalBasis ι ℝ E) (B : E →L[ℝ] E →L[ℝ] ℝ) :
    ∑ i, ∫ x, B x x ∂ν i = ∑ k, B (b k) (b k) := by
  have step : ∀ i, ∫ x, B x x ∂ν i =
      ∑ k, ∑ l, B (b k) (b l) * ∫ x, inner ℝ x (b k) * inner ℝ x (b l) ∂ν i := by
    intro i
    simp_rw [mvbe_bilin_diag b B]
    rw [integral_finsetSum _ fun k _ => ?_]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_finsetSum _ fun l _ => ?_]
      · refine Finset.sum_congr rfl fun l _ => ?_
        rw [integral_mul_const, mul_comm]
      · exact (mvbe_integrable_inner_mul (hmom i) (b k) (b l)).mul_const _
    · exact integrable_finsetSum _ fun l _ =>
        (mvbe_integrable_inner_mul (hmom i) (b k) (b l)).mul_const _
  simp_rw [step]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hcov]
  have horth := orthonormal_iff_ite.mp b.orthonormal
  simp [horth]

end Trace


section SteinHelpers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Laplacian of `g` at `w`, computed in the orthonormal basis `b`:
`Δ g (w) = ∑ₖ D²g(w)[bₖ, bₖ]`.  (Basis independent; `mvbeLaplacian_eq_laplacian` identifies it
with Mathlib's `Laplacian.laplacian`.) -/
noncomputable def mvbeLaplacian (b : OrthonormalBasis ι ℝ E) (g : E → ℝ) (w : E) : ℝ :=
  ∑ k, iteratedFDeriv ℝ 2 g w ![b k, b k]

/-- The Stein operator of Raic (2.4): `S g (w) = Δ g (w) - ⟨∇ g (w), w⟩`. -/
noncomputable def mvbeStein (b : OrthonormalBasis ι ℝ E) (g : E → ℝ) (w : E) : ℝ :=
  mvbeLaplacian b g w - fderiv ℝ g w w

theorem mvbeLaplacian_eq_laplacian [FiniteDimensional ℝ E] (b : OrthonormalBasis ι ℝ E)
    (g : E → ℝ) (w : E) : mvbeLaplacian b g w = Laplacian.laplacian g w := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis g b]
  rfl

theorem mvbe_abs_apply_two_le (c : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) ℝ) (u v : E) :
    |c ![u, v]| ≤ ‖c‖ * (‖u‖ * ‖v‖) := by
  have := c.le_opNorm ![u, v]
  simpa [Fin.prod_univ_two, Real.norm_eq_abs] using this

theorem mvbe_abs_apply_three_le (c : ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) ℝ)
    (u v w : E) : |c ![u, v, w]| ≤ ‖c‖ * (‖u‖ * ‖v‖ * ‖w‖) := by
  have := c.le_opNorm ![u, v, w]
  simpa [Fin.prod_univ_three, Real.norm_eq_abs, mul_assoc] using this

theorem mvbe_integrable_id {μ : Measure E} [IsFiniteMeasure μ]
    (hmom : Integrable (fun x => ‖x‖ ^ 3) μ) : Integrable (fun x : E => x) μ := by
  refine (((integrable_const (1 : ℝ)).add hmom)).mono' aestronglyMeasurable_id
    (Filter.Eventually.of_forall fun x => ?_)
  simpa using mvbe_self_le ‖x‖ (norm_nonneg x)

theorem mvbe_integrable_sq {μ : Measure E} [IsFiniteMeasure μ]
    (hmom : Integrable (fun x => ‖x‖ ^ 3) μ) : Integrable (fun x : E => ‖x‖ ^ 2) μ := by
  refine mvbe_integrable_of_bound hmom (by fun_prop) 1 fun x => ?_
  rw [abs_of_nonneg (by positivity), one_mul]
  exact mvbe_sq_le _ (norm_nonneg x)

theorem mvbe_integrable_norm {μ : Measure E} [IsFiniteMeasure μ]
    (hmom : Integrable (fun x => ‖x‖ ^ 3) μ) : Integrable (fun x : E => ‖x‖) μ := by
  refine mvbe_integrable_of_bound hmom (by fun_prop) 1 fun x => ?_
  rw [abs_of_nonneg (by positivity), one_mul]
  exact mvbe_self_le _ (norm_nonneg x)

theorem mvbe_integrable_eval {n : ℕ} (ν : Fin n → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (i : Fin n) {f : E → ℝ} (hf : Integrable f (ν i)) :
    Integrable (fun ω : Fin n → E => f (ω i)) (Measure.pi ν) :=
  ((measurePreserving_eval ν i).integrable_comp hf.aestronglyMeasurable).2 hf

end SteinHelpers

section SteinCont

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] {g : E → ℝ}

theorem mvbe_continuous_D2diag (hg : ContDiff ℝ 3 g) :
    Continuous fun q : E × E => iteratedFDeriv ℝ 2 g q.1 ![q.2, q.2] := by
  have hc : Continuous (iteratedFDeriv ℝ 2 g) := hg.continuous_iteratedFDeriv (by norm_num)
  have hm : Continuous fun q : E × E => (![q.2, q.2] : Fin 2 → E) := by
    refine continuous_pi fun i => ?_
    fin_cases i <;> simp <;> fun_prop
  exact (hc.comp continuous_fst).eval hm

theorem mvbe_continuous_D1 (hg : ContDiff ℝ 3 g) :
    Continuous fun q : E × E => fderiv ℝ g q.1 q.2 := by
  have hc : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
  exact (hc.comp continuous_fst).clm_apply continuous_snd

/-- The second moment functional `w ↦ ∫ D²g(w)[x,x] dμ(x)` is continuous. -/
theorem mvbe_continuous_secondMoment {μ : Measure E} [IsFiniteMeasure μ]
    (hmom : Integrable (fun x => ‖x‖ ^ 3) μ) (hg : ContDiff ℝ 3 g) (C₂ : ℝ)
    (hb2 : ∀ x, ‖iteratedFDeriv ℝ 2 g x‖ ≤ C₂) :
    Continuous fun w => ∫ x, iteratedFDeriv ℝ 2 g w ![x, x] ∂μ := by
  have hD := mvbe_continuous_D2diag hg
  refine continuous_of_dominated (bound := fun x => C₂ * ‖x‖ ^ 2) (fun w => ?_) (fun w => ?_)
    ((mvbe_integrable_sq hmom).const_mul C₂) (Filter.Eventually.of_forall fun x => ?_)
  · exact (hD.comp (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs]
    calc |iteratedFDeriv ℝ 2 g w ![x, x]| ≤ ‖iteratedFDeriv ℝ 2 g w‖ * (‖x‖ * ‖x‖) :=
          mvbe_abs_apply_two_le _ _ _
      _ ≤ C₂ * ‖x‖ ^ 2 := by
          rw [← sq]
          exact mul_le_mul_of_nonneg_right (hb2 w) (by positivity)
  · exact hD.comp (Continuous.prodMk continuous_id continuous_const)

end SteinCont

section SteinPi

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E] {g : E → ℝ} {n : ℕ}

theorem mvbe_continuous_without (i : Fin n) : Continuous (mvbeWithout (E := E) i) := by
  unfold mvbeWithout
  exact continuous_finsetSum _ fun j _ => continuous_apply j

theorem mvbe_integrable_pi_of_bound (ν : Fin n → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (i : Fin n) (hmom : Integrable (fun x => ‖x‖ ^ 3) (ν i)) {h : (Fin n → E) → ℝ}
    (hh : Continuous h) (C : ℝ) (hC : ∀ ω, |h ω| ≤ C * (1 + ‖ω i‖ ^ 3)) :
    Integrable h (Measure.pi ν) := by
  refine (((integrable_const (1 : ℝ)).add (mvbe_integrable_eval ν i hmom)).const_mul C).mono'
    hh.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  simpa using hC ω

theorem mvbe_abs_D1_le {C₁ : ℝ} (hb1 : ∀ x, ‖fderiv ℝ g x‖ ≤ C₁) (w x : E) :
    |fderiv ℝ g w x| ≤ C₁ * ‖x‖ := by
  rw [← Real.norm_eq_abs]
  exact ((fderiv ℝ g w).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hb1 w) (norm_nonneg _))

theorem mvbe_abs_D2_le {C₂ : ℝ} (hb2 : ∀ x, ‖iteratedFDeriv ℝ 2 g x‖ ≤ C₂) (w u v : E) :
    |iteratedFDeriv ℝ 2 g w ![u, v]| ≤ C₂ * (‖u‖ * ‖v‖) :=
  (mvbe_abs_apply_two_le _ u v).trans
    (mul_le_mul_of_nonneg_right (hb2 w) (mul_nonneg (norm_nonneg _) (norm_nonneg _)))

theorem mvbe_abs_D3_le {C₃ : ℝ} (hb3 : ∀ x, ‖iteratedFDeriv ℝ 3 g x‖ ≤ C₃) (w u v z : E) :
    |iteratedFDeriv ℝ 3 g w ![u, v, z]| ≤ C₃ * (‖u‖ * ‖v‖ * ‖z‖) :=
  (mvbe_abs_apply_three_le _ u v z).trans
    (mul_le_mul_of_nonneg_right (hb3 w)
      (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)))

theorem mvbe_abs_secondMoment_le {μ : Measure E} [IsFiniteMeasure μ]
    (hmom : Integrable (fun x => ‖x‖ ^ 3) μ) {C₂ : ℝ}
    (hb2 : ∀ x, ‖iteratedFDeriv ℝ 2 g x‖ ≤ C₂) (w : E) :
    |∫ x, iteratedFDeriv ℝ 2 g w ![x, x] ∂μ| ≤ C₂ * ∫ x, ‖x‖ ^ 2 ∂μ := by
  rw [← Real.norm_eq_abs, ← integral_const_mul]
  refine norm_integral_le_of_norm_le ((mvbe_integrable_sq hmom).const_mul C₂)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  calc |iteratedFDeriv ℝ 2 g w ![x, x]| ≤ C₂ * (‖x‖ * ‖x‖) := mvbe_abs_D2_le hb2 w x x
    _ = C₂ * ‖x‖ ^ 2 := by ring

theorem mvbe_integrable_M_comp (ν : Fin n → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (i : Fin n) (hmom : Integrable (fun x => ‖x‖ ^ 3) (ν i)) (hg : ContDiff ℝ 3 g) {C₂ : ℝ}
    (hb2 : ∀ x, ‖iteratedFDeriv ℝ 2 g x‖ ≤ C₂) {A : (Fin n → E) → E} (hA : Continuous A) :
    Integrable (fun ω => ∫ x, iteratedFDeriv ℝ 2 g (A ω) ![x, x] ∂ν i) (Measure.pi ν) := by
  have hC₂ : 0 ≤ C₂ := (norm_nonneg _).trans (hb2 0)
  refine mvbe_integrable_pi_of_bound ν i hmom
    ((mvbe_continuous_secondMoment hmom hg C₂ hb2).comp hA) (C₂ * ∫ x, ‖x‖ ^ 2 ∂ν i)
    fun ω => ?_
  refine (mvbe_abs_secondMoment_le hmom hb2 _).trans ?_
  have : 0 ≤ C₂ * ∫ x, ‖x‖ ^ 2 ∂ν i :=
    mul_nonneg hC₂ (integral_nonneg fun x => by positivity)
  nlinarith [pow_nonneg (norm_nonneg (ω i)) 3]

theorem mvbe_integrable_D1_comp (ν : Fin n → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (i : Fin n) (hmom : Integrable (fun x => ‖x‖ ^ 3) (ν i)) (hg : ContDiff ℝ 3 g) {C₁ : ℝ}
    (hb1 : ∀ x, ‖fderiv ℝ g x‖ ≤ C₁) {A : (Fin n → E) → E} (hA : Continuous A) :
    Integrable (fun ω => fderiv ℝ g (A ω) (ω i)) (Measure.pi ν) := by
  have hC₁ : 0 ≤ C₁ := (norm_nonneg _).trans (hb1 0)
  refine mvbe_integrable_pi_of_bound ν i hmom ((mvbe_continuous_D1 hg).comp
    (hA.prodMk (continuous_apply i))) C₁ fun ω => ?_
  exact (mvbe_abs_D1_le hb1 _ _).trans
    (mul_le_mul_of_nonneg_left (mvbe_self_le _ (norm_nonneg _)) hC₁)

theorem mvbe_integrable_D2_comp (ν : Fin n → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (i : Fin n) (hmom : Integrable (fun x => ‖x‖ ^ 3) (ν i)) (hg : ContDiff ℝ 3 g) {C₂ : ℝ}
    (hb2 : ∀ x, ‖iteratedFDeriv ℝ 2 g x‖ ≤ C₂) {A : (Fin n → E) → E} (hA : Continuous A) :
    Integrable (fun ω => iteratedFDeriv ℝ 2 g (A ω) ![ω i, ω i]) (Measure.pi ν) := by
  have hC₂ : 0 ≤ C₂ := (norm_nonneg _).trans (hb2 0)
  refine mvbe_integrable_pi_of_bound ν i hmom ((mvbe_continuous_D2diag hg).comp
    (hA.prodMk (continuous_apply i))) C₂ fun ω => ?_
  refine (mvbe_abs_D2_le hb2 _ _ _).trans ?_
  rw [← sq]
  exact mul_le_mul_of_nonneg_left (mvbe_sq_le _ (norm_nonneg _)) hC₂

/-- The mean-zero and independence cancellation in Raic's proof of Lemma 2.4: the terms of
`E[⟨∇²g(W_i), X̃_i^{⊗2}⟩ − ⟨∇g(W_i), X_i⟩ − ⟨∇²g(W_i), X_i^{⊗2}⟩]` cancel. -/
theorem mvbe_freeze_zero (ν : Fin n → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (hmom : ∀ i, Integrable (fun x => ‖x‖ ^ 3) (ν i)) (hmean : ∀ i, ∫ x, x ∂ν i = 0)
    (hg : ContDiff ℝ 3 g) {C₁ C₂ : ℝ} (hb1 : ∀ x, ‖fderiv ℝ g x‖ ≤ C₁)
    (hb2 : ∀ x, ‖iteratedFDeriv ℝ 2 g x‖ ≤ C₂) (i : Fin n) :
    ∫ ω, (-(∫ x, iteratedFDeriv ℝ 2 g (mvbeWithout i ω) ![x, x] ∂ν i) +
      fderiv ℝ g (mvbeWithout i ω) (ω i) +
      iteratedFDeriv ℝ 2 g (mvbeWithout i ω) ![ω i, ω i]) ∂Measure.pi ν = 0 := by
  have hC₁ : 0 ≤ C₁ := (norm_nonneg _).trans (hb1 0)
  have hC₂ : 0 ≤ C₂ := (norm_nonneg _).trans (hb2 0)
  have hD2 := mvbe_continuous_D2diag hg
  have hD1 := mvbe_continuous_D1 hg
  have hW := mvbe_continuous_without (E := E) (n := n) i
  have I1 := mvbe_integrable_M_comp ν i (hmom i) hg hb2 hW
  have I2 := mvbe_integrable_D1_comp ν i (hmom i) hg hb1 hW
  have I3 := mvbe_integrable_D2_comp ν i (hmom i) hg hb2 hW
  -- the two freezing identities
  have F2 : ∫ ω, iteratedFDeriv ℝ 2 g (mvbeWithout i ω) ![ω i, ω i] ∂Measure.pi ν =
      ∫ ω, ∫ x, iteratedFDeriv ℝ 2 g (mvbeWithout i ω) ![x, x] ∂ν i ∂Measure.pi ν := by
    refine mvbe_integral_freeze ν i (fun w x => iteratedFDeriv ℝ 2 g w ![x, x]) hD2 C₂
      (fun w x => ?_) (hmom i)
    refine (mvbe_abs_D2_le hb2 _ _ _).trans ?_
    rw [← sq]
    exact mul_le_mul_of_nonneg_left (mvbe_sq_le _ (norm_nonneg _)) hC₂
  have F1 : ∫ ω, fderiv ℝ g (mvbeWithout i ω) (ω i) ∂Measure.pi ν = 0 := by
    rw [mvbe_integral_freeze ν i (fun w x => fderiv ℝ g w x) hD1 C₁ (fun w x => ?_) (hmom i)]
    · have : ∀ w : E, ∫ x, fderiv ℝ g w x ∂ν i = 0 := fun w => by
        rw [ContinuousLinearMap.integral_comp_comm (fderiv ℝ g w) (mvbe_integrable_id (hmom i)),
          hmean i, map_zero]
      simp [this]
    · exact (mvbe_abs_D1_le hb1 _ _).trans
        (mul_le_mul_of_nonneg_left (mvbe_self_le _ (norm_nonneg _)) hC₁)
  have h1 := integral_add (I1.neg.add I2) I3
  have h2 := integral_add I1.neg I2
  simp only [Pi.add_apply, Pi.neg_apply] at h1 h2
  rw [h1, h2, integral_neg, F1, F2]
  ring

end SteinPi

section SteinFubini

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E] {g : E → ℝ} {n : ℕ}

theorem mvbe_continuous_steinRem_pi (hg : ContDiff ℝ 3 g) (i : Fin n) :
    Continuous fun p : (Fin n → E) × (E × ℝ) =>
      mvbeSteinRem g (mvbeWithout i p.1) (p.1 i) p.2.1 p.2.2 := by
  have hc3 : Continuous (iteratedFDeriv ℝ 3 g) := hg.continuous_iteratedFDeriv (by norm_num)
  have hpt : Continuous fun p : (Fin n → E) × (E × ℝ) =>
      mvbeWithout i p.1 + p.2.2 • p.1 i :=
    ((mvbe_continuous_without i).comp continuous_fst).add
      ((continuous_snd.comp continuous_snd).smul ((continuous_apply i).comp continuous_fst))
  have hb : Continuous fun p : (Fin n → E) × (E × ℝ) => p.1 i :=
    (continuous_apply i).comp continuous_fst
  have hu : Continuous fun p : (Fin n → E) × (E × ℝ) => p.2.1 := continuous_fst.comp continuous_snd
  have hm1 : Continuous fun p : (Fin n → E) × (E × ℝ) => (![p.1 i, p.2.1, p.2.1] : Fin 3 → E) := by
    refine continuous_pi fun j => ?_
    fin_cases j <;> simp <;> assumption
  have hm2 : Continuous fun p : (Fin n → E) × (E × ℝ) => (![p.1 i, p.1 i, p.1 i] : Fin 3 → E) := by
    refine continuous_pi fun j => ?_
    fin_cases j <;> simp <;> assumption
  unfold mvbeSteinRem
  exact ((hc3.comp hpt).eval hm1).sub
    ((continuous_const.sub (continuous_snd.comp continuous_snd)).mul ((hc3.comp hpt).eval hm2))

theorem mvbe_integrable_steinRem (ν : Fin n → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (hmom : ∀ i, Integrable (fun x => ‖x‖ ^ 3) (ν i)) (hg : ContDiff ℝ 3 g) {C₃ : ℝ}
    (hb3 : ∀ x, ‖iteratedFDeriv ℝ 3 g x‖ ≤ C₃) (i : Fin n) :
    Integrable (fun p : (Fin n → E) × (E × ℝ) =>
      mvbeSteinRem g (mvbeWithout i p.1) (p.1 i) p.2.1 p.2.2)
      ((Measure.pi ν).prod ((ν i).prod (volume.restrict (Set.Icc (0 : ℝ) 1)))) := by
  have hC₃ : 0 ≤ C₃ := (norm_nonneg _).trans (hb3 0)
  have hU : Integrable (fun θ : ℝ => 1 + |θ|) (volume.restrict (Set.Icc (0 : ℝ) 1)) :=
    (by fun_prop : Continuous fun θ : ℝ => 1 + |θ|).integrableOn_Icc
  have hq1 : Integrable (fun q : E × ℝ => ‖q.1‖ ^ 2 * (1 : ℝ))
      ((ν i).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
    (mvbe_integrable_sq (hmom i)).mul_prod (integrable_const (1 : ℝ))
  have hq2 : Integrable (fun q : E × ℝ => (1 : ℝ) * (1 + |q.2|))
      ((ν i).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) :=
    (integrable_const (1 : ℝ)).mul_prod hU
  have hp1 : Integrable (fun p : (Fin n → E) × (E × ℝ) => ‖p.1 i‖ * (‖p.2.1‖ ^ 2 * (1 : ℝ)))
      ((Measure.pi ν).prod ((ν i).prod (volume.restrict (Set.Icc (0 : ℝ) 1)))) :=
    (mvbe_integrable_eval ν i (mvbe_integrable_norm (hmom i))).mul_prod hq1
  have hp2 : Integrable (fun p : (Fin n → E) × (E × ℝ) =>
      ‖p.1 i‖ ^ 3 * ((1 : ℝ) * (1 + |p.2.2|)))
      ((Measure.pi ν).prod ((ν i).prod (volume.restrict (Set.Icc (0 : ℝ) 1)))) :=
    (mvbe_integrable_eval ν i (hmom i)).mul_prod hq2
  refine ((hp1.const_mul C₃).add (hp2.const_mul C₃)).mono'
    (mvbe_continuous_steinRem_pi hg i).aestronglyMeasurable
    (Filter.Eventually.of_forall fun p => ?_)
  simp only [mvbeSteinRem, Real.norm_eq_abs]
  have e1 := mvbe_abs_D3_le hb3 (mvbeWithout i p.1 + p.2.2 • p.1 i) (p.1 i) p.2.1 p.2.1
  have e2 := mvbe_abs_D3_le hb3 (mvbeWithout i p.1 + p.2.2 • p.1 i) (p.1 i) (p.1 i) (p.1 i)
  have h1θ : |1 - p.2.2| ≤ 1 + |p.2.2| := by
    calc |1 - p.2.2| ≤ |1| + |p.2.2| := abs_sub _ _
      _ = 1 + |p.2.2| := by simp
  refine (abs_sub _ _).trans ?_
  rw [abs_mul]
  have e3 : |1 - p.2.2| * |iteratedFDeriv ℝ 3 g (mvbeWithout i p.1 + p.2.2 • p.1 i)
      ![p.1 i, p.1 i, p.1 i]| ≤ (1 + |p.2.2|) * (C₃ * (‖p.1 i‖ * ‖p.1 i‖ * ‖p.1 i‖)) :=
    mul_le_mul h1θ e2 (abs_nonneg _) (by positivity)
  simp only [Pi.add_apply]
  nlinarith [e1, e3, norm_nonneg (p.1 i), norm_nonneg p.2.1, abs_nonneg p.2.2]

end SteinFubini

section SteinSingle

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E] {g : E → ℝ} {n : ℕ}

theorem mvbe_integrable_D2x {μ : Measure E} [IsFiniteMeasure μ]
    (hmom : Integrable (fun x => ‖x‖ ^ 3) μ) (hg : ContDiff ℝ 3 g) {C₂ : ℝ}
    (hb2 : ∀ x, ‖iteratedFDeriv ℝ 2 g x‖ ≤ C₂) (w : E) :
    Integrable (fun x => iteratedFDeriv ℝ 2 g w ![x, x]) μ := by
  have hC₂ : 0 ≤ C₂ := (norm_nonneg _).trans (hb2 0)
  refine mvbe_integrable_of_bound hmom
    ((mvbe_continuous_D2diag hg).comp (Continuous.prodMk continuous_const continuous_id)) C₂
    fun x => ?_
  refine (mvbe_abs_D2_le hb2 _ _ _).trans ?_
  rw [← sq]
  exact mul_le_mul_of_nonneg_left (mvbe_sq_le _ (norm_nonneg _)) hC₂

theorem mvbe_integral_x_step (μ : Measure E) [IsProbabilityMeasure μ]
    (hmom : Integrable (fun x => ‖x‖ ^ 3) μ) (hg : ContDiff ℝ 3 g) {C₂ : ℝ}
    (hb2 : ∀ x, ‖iteratedFDeriv ℝ 2 g x‖ ≤ C₂) (w a : E) (c₁ c₂ c₃ : ℝ) :
    ∫ x, ((iteratedFDeriv ℝ 2 g w ![x, x] - c₁) -
        (iteratedFDeriv ℝ 2 g a ![x, x] - c₂ - c₃)) ∂μ =
      (∫ x, iteratedFDeriv ℝ 2 g w ![x, x] ∂μ - c₁) -
        (∫ x, iteratedFDeriv ℝ 2 g a ![x, x] ∂μ - c₂ - c₃) := by
  have h1 := mvbe_integrable_D2x hmom hg hb2 w
  have h2 := mvbe_integrable_D2x hmom hg hb2 a
  have e1 : Integrable (fun x => iteratedFDeriv ℝ 2 g w ![x, x] - c₁) μ :=
    h1.sub (integrable_const c₁)
  have e2 : Integrable (fun x => iteratedFDeriv ℝ 2 g a ![x, x] - c₂) μ :=
    h2.sub (integrable_const c₂)
  have e3 : Integrable (fun x => iteratedFDeriv ℝ 2 g a ![x, x] - c₂ - c₃) μ :=
    e2.sub (integrable_const c₃)
  rw [integral_sub e1 e3, integral_sub h1 (integrable_const c₁),
    integral_sub e2 (integrable_const c₃), integral_sub h2 (integrable_const c₂)]
  simp

/-- The pointwise (in `ω`) value of the inner `x̃, θ` integrals in Raic's Lemma 2.4. -/
theorem mvbe_inner_integrals (ν : Fin n → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (hmom : ∀ i, Integrable (fun x => ‖x‖ ^ 3) (ν i)) (hg : ContDiff ℝ 3 g) {C₂ : ℝ}
    (hb2 : ∀ x, ‖iteratedFDeriv ℝ 2 g x‖ ≤ C₂) (i : Fin n) (ω : Fin n → E) :
    ∫ x, ∫ θ, mvbeSteinRem g (mvbeWithout i ω) (ω i) x θ ∂(volume.restrict (Set.Icc (0 : ℝ) 1))
        ∂ν i =
      (∫ x, iteratedFDeriv ℝ 2 g (∑ j, ω j) ![x, x] ∂ν i - fderiv ℝ g (∑ j, ω j) (ω i)) +
      (-(∫ x, iteratedFDeriv ℝ 2 g (mvbeWithout i ω) ![x, x] ∂ν i) +
        fderiv ℝ g (mvbeWithout i ω) (ω i) +
        iteratedFDeriv ℝ 2 g (mvbeWithout i ω) ![ω i, ω i]) := by
  have step : ∀ x, ∫ θ, mvbeSteinRem g (mvbeWithout i ω) (ω i) x θ
      ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) =
      (iteratedFDeriv ℝ 2 g (∑ j, ω j) ![x, x] - fderiv ℝ g (∑ j, ω j) (ω i)) -
        (iteratedFDeriv ℝ 2 g (mvbeWithout i ω) ![x, x] - fderiv ℝ g (mvbeWithout i ω) (ω i) -
          iteratedFDeriv ℝ 2 g (mvbeWithout i ω) ![ω i, ω i]) := by
    intro x
    have := mvbe_taylor_stein hg (mvbeWithout i ω) (ω i) x
    rw [mvbe_without_add] at this
    linarith
  simp_rw [step]
  rw [mvbe_integral_x_step (ν i) (hmom i) hg hb2]
  ring

/-- **Raic's Lemma 2.4 for a single summand.**  Under `P = Measure.pi ν`, with `X̃_i ∼ ν i`
and `θ ∼ U[0,1]` independent of everything, the third-order term of the summand `i` equals
`E[ ∫ D²g(W)[x,x] dν_i(x) − ⟨∇g(W), X_i⟩ ]`. -/
theorem mvbe_single_summand (ν : Fin n → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (hmom : ∀ i, Integrable (fun x => ‖x‖ ^ 3) (ν i)) (hmean : ∀ i, ∫ x, x ∂ν i = 0)
    (hg : ContDiff ℝ 3 g) {C₁ C₂ C₃ : ℝ} (hb1 : ∀ x, ‖fderiv ℝ g x‖ ≤ C₁)
    (hb2 : ∀ x, ‖iteratedFDeriv ℝ 2 g x‖ ≤ C₂) (hb3 : ∀ x, ‖iteratedFDeriv ℝ 3 g x‖ ≤ C₃)
    (i : Fin n) :
    ∫ p : (Fin n → E) × (E × ℝ), mvbeSteinRem g (mvbeWithout i p.1) (p.1 i) p.2.1 p.2.2
        ∂((Measure.pi ν).prod ((ν i).prod (volume.restrict (Set.Icc (0 : ℝ) 1)))) =
      ∫ ω, (∫ x, iteratedFDeriv ℝ 2 g (∑ j, ω j) ![x, x] ∂ν i -
        fderiv ℝ g (∑ j, ω j) (ω i)) ∂Measure.pi ν := by
  have hint := mvbe_integrable_steinRem ν hmom hg hb3 i
  have hW := mvbe_continuous_without (E := E) (n := n) i
  have hS : Continuous fun ω : Fin n → E => ∑ j, ω j := continuous_finsetSum _ fun j _ =>
    continuous_apply j
  have J1 := mvbe_integrable_M_comp ν i (hmom i) hg hb2 hS
  have J2 := mvbe_integrable_D1_comp ν i (hmom i) hg hb1 hS
  rw [integral_prod _ hint]
  have step : ∀ᵐ ω ∂Measure.pi ν,
      ∫ q, mvbeSteinRem g (mvbeWithout i ω) (ω i) q.1 q.2
        ∂((ν i).prod (volume.restrict (Set.Icc (0 : ℝ) 1))) =
      (∫ x, iteratedFDeriv ℝ 2 g (∑ j, ω j) ![x, x] ∂ν i - fderiv ℝ g (∑ j, ω j) (ω i)) +
      (-(∫ x, iteratedFDeriv ℝ 2 g (mvbeWithout i ω) ![x, x] ∂ν i) +
        fderiv ℝ g (mvbeWithout i ω) (ω i) +
        iteratedFDeriv ℝ 2 g (mvbeWithout i ω) ![ω i, ω i]) := by
    filter_upwards [hint.prod_right_ae] with ω hω
    rw [integral_prod _ hω]
    exact mvbe_inner_integrals ν hmom hg hb2 i ω
  rw [integral_congr_ae step]
  have K1 := mvbe_integrable_M_comp ν i (hmom i) hg hb2 hW
  have K2 := mvbe_integrable_D1_comp ν i (hmom i) hg hb1 hW
  have K3 := mvbe_integrable_D2_comp ν i (hmom i) hg hb2 hW
  have h1 := integral_add (J1.sub J2) ((K1.neg.add K2).add K3)
  simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply] at h1
  rw [h1, mvbe_freeze_zero ν hmom hmean hg hb1 hb2 i, add_zero]

end SteinSingle

section SteinMain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [SecondCountableTopology E] [CompleteSpace E] {g : E → ℝ} {n : ℕ}
  {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Summing the second-moment functionals over the summands gives the Laplacian, because the
covariances add up to the identity. -/
theorem mvbe_sum_secondMoment (ν : Fin n → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (hmom : ∀ i, Integrable (fun x => ‖x‖ ^ 3) (ν i))
    (hcov : ∀ u v : E, ∑ i, ∫ x, inner ℝ x u * inner ℝ x v ∂ν i = inner ℝ u v)
    (b : OrthonormalBasis ι ℝ E) (w : E) :
    ∑ i, ∫ x, iteratedFDeriv ℝ 2 g w ![x, x] ∂ν i = mvbeLaplacian b g w := by
  have := mvbe_trace_cov ν hmom hcov b (fderiv ℝ (fderiv ℝ g) w)
  simpa [iteratedFDeriv_two_apply, mvbeLaplacian] using this

/-- **Raic's Lemma 2.4 (Stein expectation, due to Götze), general form.**
`ν i` are probability measures on `E` with finite third absolute moment and mean zero whose
covariances add up to the identity; `P = Measure.pi ν`, `W ω = ∑ i, ω i`; `g` is `C³` with
bounded derivatives of orders `1, 2, 3`.  Then, with `W_i = W - X_i`, `X̃_i ∼ ν i` and
`θ ∼ U[0,1]` (the factor `(ν i).prod (volume.restrict (Set.Icc 0 1))`) independent of `P`,
`E[S g(W)] = ∑ i, E[D³g(W_i + θ X_i)[X_i, X̃_i, X̃_i] - (1-θ) D³g(W_i + θ X_i)[X_i, X_i, X_i]]`. -/
theorem mvbe_stein_expectation_general (b : OrthonormalBasis ι ℝ E)
    (ν : Fin n → Measure E) [∀ i, IsProbabilityMeasure (ν i)]
    (hmom : ∀ i, Integrable (fun x => ‖x‖ ^ 3) (ν i)) (hmean : ∀ i, ∫ x, x ∂ν i = 0)
    (hcov : ∀ u v : E, ∑ i, ∫ x, inner ℝ x u * inner ℝ x v ∂ν i = inner ℝ u v)
    (hg : ContDiff ℝ 3 g) {C₁ C₂ C₃ : ℝ} (hb1 : ∀ x, ‖fderiv ℝ g x‖ ≤ C₁)
    (hb2 : ∀ x, ‖iteratedFDeriv ℝ 2 g x‖ ≤ C₂) (hb3 : ∀ x, ‖iteratedFDeriv ℝ 3 g x‖ ≤ C₃) :
    ∫ ω, mvbeStein b g (∑ i, ω i) ∂Measure.pi ν =
      ∑ i, ∫ p : (Fin n → E) × (E × ℝ),
        mvbeSteinRem g (mvbeWithout i p.1) (p.1 i) p.2.1 p.2.2
          ∂((Measure.pi ν).prod ((ν i).prod (volume.restrict (Set.Icc (0 : ℝ) 1)))) := by
  have hS : Continuous fun ω : Fin n → E => ∑ j, ω j :=
    continuous_finsetSum _ fun j _ => continuous_apply j
  simp_rw [mvbe_single_summand ν hmom hmean hg hb1 hb2 hb3]
  have J : ∀ i, Integrable (fun ω : Fin n → E => ∫ x, iteratedFDeriv ℝ 2 g (∑ j, ω j) ![x, x]
      ∂ν i - fderiv ℝ g (∑ j, ω j) (ω i)) (Measure.pi ν) := fun i =>
    (mvbe_integrable_M_comp ν i (hmom i) hg hb2 hS).sub
      (mvbe_integrable_D1_comp ν i (hmom i) hg hb1 hS)
  rw [← integral_finsetSum _ fun i _ => J i]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only [mvbeStein]
  rw [Finset.sum_sub_distrib, mvbe_sum_secondMoment ν hmom hcov b, ← map_sum]

end SteinMain

section SteinEuclidean

variable {d n : ℕ}

theorem mvbeStein_basisFun_apply (g : EuclideanSpace ℝ (Fin d) → ℝ)
    (w : EuclideanSpace ℝ (Fin d)) :
    mvbeStein (EuclideanSpace.basisFun (Fin d) ℝ) g w =
      ∑ k, iteratedFDeriv ℝ 2 g w ![EuclideanSpace.single k 1, EuclideanSpace.single k 1] -
        fderiv ℝ g w w := by
  simp [mvbeStein, mvbeLaplacian]

theorem mvbeStein_eq_laplacian (b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)))
    (g : EuclideanSpace ℝ (Fin d) → ℝ) (w : EuclideanSpace ℝ (Fin d)) :
    mvbeStein b g w = Laplacian.laplacian g w - fderiv ℝ g w w := by
  rw [mvbeStein, mvbeLaplacian_eq_laplacian]

/-- **Raic's Lemma 2.4 on `EuclideanSpace ℝ (Fin d)`** (Götze's Stein expectation formula),
exactly in the form of the paper:
`E[S g(W)] = ∑ i, E[ ⟨∇³g(W_i + θ X_i), X_i ⊗ X̃_i^{⊗2} - (1-θ) X_i^{⊗3}⟩ ]`.

* `ν i` are the laws of the independent summands `X_i` (probability measures, finite third
  absolute moment, mean zero, `∑ i, Cov (ν i) = Id` with the covariance read through
  `∫ ⟪x,u⟫ ⟪x,v⟫ d(ν i)`);
* `P = Measure.pi ν`, `W ω = ∑ i, ω i`, `W_i = mvbeWithout i`, `X_i ω = ω i`;
* the expectation on the right is over `P ⊗ ν i ⊗ U[0,1]`: the point `(ω, x̃, θ)` stands for
  `(X, X̃_i, θ)`, an independent copy `X̃_i ∼ ν i` and an independent uniform `θ`;
* `S g(w) = Δ g(w) - ⟨∇g(w), w⟩` is `mvbeStein`, the Laplacian being the sum of
  `D²g(w)[e_k, e_k]` over the standard basis (`mvbeStein_basisFun_apply`);
* the tensor pairing `⟨∇³g(y), X_i ⊗ X̃_i^{⊗2}⟩` is `D³g(y)[X_i, X̃_i, X̃_i]`
  (`iteratedFDeriv ℝ 3 g y ![X_i, X̃_i, X̃_i]`, `mvbeSteinRem`).

Bounded derivatives of order 1, 2, 3 are the hypotheses `hb1 hb2 hb3`. -/
theorem mvbe_stein_expectation (ν : Fin n → Measure (EuclideanSpace ℝ (Fin d)))
    [∀ i, IsProbabilityMeasure (ν i)]
    (hmom : ∀ i, Integrable (fun x => ‖x‖ ^ 3) (ν i)) (hmean : ∀ i, ∫ x, x ∂ν i = 0)
    (hcov : ∀ u v : EuclideanSpace ℝ (Fin d),
      ∑ i, ∫ x, inner ℝ x u * inner ℝ x v ∂ν i = inner ℝ u v)
    {g : EuclideanSpace ℝ (Fin d) → ℝ} (hg : ContDiff ℝ 3 g) {C₁ C₂ C₃ : ℝ}
    (hb1 : ∀ x, ‖fderiv ℝ g x‖ ≤ C₁) (hb2 : ∀ x, ‖iteratedFDeriv ℝ 2 g x‖ ≤ C₂)
    (hb3 : ∀ x, ‖iteratedFDeriv ℝ 3 g x‖ ≤ C₃) :
    ∫ ω, mvbeStein (EuclideanSpace.basisFun (Fin d) ℝ) g (∑ i, ω i) ∂Measure.pi ν =
      ∑ i, ∫ p : (Fin n → EuclideanSpace ℝ (Fin d)) × (EuclideanSpace ℝ (Fin d) × ℝ),
        (iteratedFDeriv ℝ 3 g (mvbeWithout i p.1 + p.2.2 • p.1 i) ![p.1 i, p.2.1, p.2.1] -
          (1 - p.2.2) *
            iteratedFDeriv ℝ 3 g (mvbeWithout i p.1 + p.2.2 • p.1 i) ![p.1 i, p.1 i, p.1 i])
          ∂((Measure.pi ν).prod ((ν i).prod (volume.restrict (Set.Icc (0 : ℝ) 1)))) :=
  mvbe_stein_expectation_general (EuclideanSpace.basisFun (Fin d) ℝ) ν hmom hmean hcov hg
    hb1 hb2 hb3

end SteinEuclidean

end LatticeProb
