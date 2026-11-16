import LatticeProb.Analysis.Schauder.DirDerivComm

/-!
# Higher derivatives as nested directional derivatives

The `(n+1)`-th Fréchet derivative of a `C^{n+1}` function evaluated on `(m₀, …, mₙ)` is the `n`-th
Fréchet derivative of the directional derivative along `mₙ`, evaluated on `(m₀, …, mₙ₋₁)`. Iterating
this identity expresses the third and fourth derivatives of a `C³`, respectively `C⁴`, function on
a tuple of directions as a nested directional derivative. The operator-norm bound of a continuous
multilinear map then bounds each nested directional derivative by the norm of the corresponding
iterated derivative times the product of the norms of the directions.
-/

namespace LatticeProb.Analysis.Schauder

noncomputable section

variable {d : ℕ}

/-- The `(n+1)`-th derivative of a `C^{n+1}` function on a tuple of directions is the `n`-th
derivative of the directional derivative along the last direction, on the remaining directions. -/
theorem iteratedFDeriv_succ_apply_eq_dirDeriv {f : Euc d → ℝ} {n : ℕ}
    (hf : ContDiff ℝ (n + 1) f) (z : Euc d) (m : Fin (n + 1) → Euc d) :
    iteratedFDeriv ℝ (n + 1) f z m =
      iteratedFDeriv ℝ n (dirDeriv (m (Fin.last n)) f) z (Fin.init m) := by
  have hg : ContDiff ℝ n (fderiv ℝ f) := hf.fderiv_right (by exact_mod_cast le_rfl)
  have hfun : dirDeriv (m (Fin.last n)) f =
      (ContinuousLinearMap.apply ℝ ℝ (m (Fin.last n))) ∘ (fderiv ℝ f) := by
    funext y
    simp [dirDeriv]
  rw [iteratedFDeriv_succ_apply_right, hfun,
    (ContinuousLinearMap.apply ℝ ℝ (m (Fin.last n))).iteratedFDeriv_comp_left
      hg.contDiffAt le_rfl]
  rfl

/-- The third derivative of a `C³` function on three directions is the nested directional
derivative. -/
theorem iteratedFDeriv_three_apply_eq_dirDeriv {f : Euc d → ℝ} (hf : ContDiff ℝ 3 f)
    (z a b c : Euc d) :
    iteratedFDeriv ℝ 3 f z ![a, b, c] = dirDeriv a (dirDeriv b (dirDeriv c f)) z := by
  have hf' : ContDiff ℝ ((2 : ℕ) + 1) f := by exact_mod_cast hf
  have hc : ContDiff ℝ 2 (dirDeriv c f) := by
    exact_mod_cast contDiff_dirDeriv_of_contDiff hf' c
  have h := iteratedFDeriv_succ_apply_eq_dirDeriv hf' z ![a, b, c]
  have hlast : (![a, b, c] : Fin 3 → Euc d) (Fin.last 2) = c := rfl
  have hinit : Fin.init (![a, b, c] : Fin 3 → Euc d) = ![a, b] := by
    funext i
    fin_cases i <;> rfl
  rw [hlast, hinit] at h
  exact h.trans (iteratedFDeriv_two_apply_eq_dirDeriv hc z a b)

/-- The fourth derivative of a `C⁴` function on four directions is the nested directional
derivative. -/
theorem iteratedFDeriv_four_apply_eq_dirDeriv {f : Euc d → ℝ} (hf : ContDiff ℝ 4 f)
    (z a b c e : Euc d) :
    iteratedFDeriv ℝ 4 f z ![a, b, c, e] =
      dirDeriv a (dirDeriv b (dirDeriv c (dirDeriv e f))) z := by
  have hf' : ContDiff ℝ ((3 : ℕ) + 1) f := by exact_mod_cast hf
  have he : ContDiff ℝ 3 (dirDeriv e f) := by
    exact_mod_cast contDiff_dirDeriv_of_contDiff hf' e
  have h := iteratedFDeriv_succ_apply_eq_dirDeriv hf' z ![a, b, c, e]
  have hlast : (![a, b, c, e] : Fin 4 → Euc d) (Fin.last 3) = e := rfl
  have hinit : Fin.init (![a, b, c, e] : Fin 4 → Euc d) = ![a, b, c] := by
    funext i
    fin_cases i <;> rfl
  rw [hlast, hinit] at h
  exact h.trans (iteratedFDeriv_three_apply_eq_dirDeriv he z a b c)

/-- A nested second directional derivative of a `C²` function is bounded by the norm of the second
derivative times the norms of the two directions. -/
theorem abs_dirDeriv_two_le {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (z a b : Euc d) :
    |dirDeriv a (dirDeriv b f) z| ≤ ‖iteratedFDeriv ℝ 2 f z‖ * (‖a‖ * ‖b‖) := by
  rw [← iteratedFDeriv_two_apply_eq_dirDeriv hf z a b, ← Real.norm_eq_abs]
  have h := (iteratedFDeriv ℝ 2 f z).le_opNorm ![a, b]
  simpa [Fin.prod_univ_two] using h

/-- A nested third directional derivative of a `C³` function is bounded by the norm of the third
derivative times the norms of the three directions. -/
theorem abs_dirDeriv_three_le {f : Euc d → ℝ} (hf : ContDiff ℝ 3 f) (z a b c : Euc d) :
    |dirDeriv a (dirDeriv b (dirDeriv c f)) z| ≤
      ‖iteratedFDeriv ℝ 3 f z‖ * (‖a‖ * ‖b‖ * ‖c‖) := by
  rw [← iteratedFDeriv_three_apply_eq_dirDeriv hf z a b c, ← Real.norm_eq_abs]
  have h := (iteratedFDeriv ℝ 3 f z).le_opNorm ![a, b, c]
  simpa [Fin.prod_univ_three, mul_assoc] using h

/-- A nested fourth directional derivative of a `C⁴` function is bounded by the norm of the fourth
derivative times the norms of the four directions. -/
theorem abs_dirDeriv_four_le {f : Euc d → ℝ} (hf : ContDiff ℝ 4 f) (z a b c e : Euc d) :
    |dirDeriv a (dirDeriv b (dirDeriv c (dirDeriv e f))) z| ≤
      ‖iteratedFDeriv ℝ 4 f z‖ * (‖a‖ * ‖b‖ * ‖c‖ * ‖e‖) := by
  rw [← iteratedFDeriv_four_apply_eq_dirDeriv hf z a b c e, ← Real.norm_eq_abs]
  have h := (iteratedFDeriv ℝ 4 f z).le_opNorm ![a, b, c, e]
  simpa [Fin.prod_univ_four, mul_assoc] using h

end

end LatticeProb.Analysis.Schauder
