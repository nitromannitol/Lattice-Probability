/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MeshOnly.MeshOnlyNashKernelBound at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MeshOnly.MeshOnlyNashTwoRegimes
import LatticeProb.Bonanno.MeshOnly.MeshOnlyNashRate

/-!
# Initial-value independent on-diagonal decay from defective Nash

The constant is chosen before the mesh, the flow, and time. The heat module
instantiates this scalar theorem with the actual positive Dirac heat density.
-/

namespace BouRabeeGwynne

/-- The scalar analytic conclusion of Proposition 3.1, in its exact two-term
normalization. The initial value of X does not enter the constant. -/
theorem on_diagonal_decay_of_defective_nash {d : ℕ} (hd : 1 ≤ d)
    {C : ℝ} (hC : 0 ≤ C) :
    ∃ K : ℝ, 0 < K ∧ ∀ (ε : ℝ), 0 < ε → ∀ X Q : ℝ → ℝ,
      (∀ s, 0 ≤ s → 0 < X s) →
      (∀ s, 0 ≤ s → 0 ≤ Q s) →
      (∀ s, 0 ≤ s → HasDerivAt X (-2 * Q s) s) →
      (∀ s, 0 ≤ s → X s ^ (2 + 2 / (d : ℝ)) ≤
        C * Q s * (X s + ε ^ 2 * Q s)) →
      ∀ t : ℝ, 0 < t →
        X t ≤ K * (t ^ (-(d : ℝ) / 2) + ε ^ d * t ^ (-(d : ℝ))) := by
  have hdpos : (0 : ℝ) < d := Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one hd)
  have hd0 : (d : ℝ) ≠ 0 := hdpos.ne'
  let c : ℝ := 1 / (2 * C + 1)
  have hden : 0 < 2 * C + 1 := by positivity
  have hc : 0 < c := one_div_pos.mpr hden
  let A : ℝ := (c / (d : ℝ)) ^ (-(d : ℝ) / 2)
  let B : ℝ := (c / (2 * (d : ℝ))) ^ (-(d : ℝ))
  have hA : 0 < A := Real.rpow_pos_of_pos (div_pos hc hdpos) _
  have hB : 0 < B := Real.rpow_pos_of_pos (div_pos hc (mul_pos zero_lt_two hdpos)) _
  refine ⟨A + B, add_pos hA hB, ?_⟩
  intro ε hε X Q hX hQ hderiv hnash t ht
  have hp : (0 : ℝ) < 1 / (d : ℝ) := one_div_pos.mpr hdpos
  have hdecay : ∀ s, 0 ≤ s →
      c * min (X s ^ (1 + 2 * (1 / (d : ℝ))))
        (X s ^ (1 + 1 / (d : ℝ)) / ε) ≤ -(-2 * Q s) := by
    intro s hs
    have he : (2 : ℝ) + 2 * (1 / (d : ℝ)) = 2 + 2 / (d : ℝ) := by ring
    have hn := defective_nash_min_rate (p := 1 / (d : ℝ)) (hX s hs)
      (hQ s hs) hC hε (by simpa only [he] using hnash s hs)
    have hrate := mul_le_mul_of_nonneg_left hn hc.le
    have hcancel : c * ((2 * C + 1) * Q s) = Q s := by
      dsimp [c]
      field_simp
    rw [hcancel] at hrate
    linarith [hQ s hs]
  have hbound := nash_two_regime_decay X (fun s => -2 * Q s) hc hε hp
    (fun s hs => (hX s hs).le) hderiv hdecay ht
  have he₁ : -1 / (2 * (1 / (d : ℝ))) = -(d : ℝ) / 2 := by field_simp <;> ring
  have he₂ : -1 / (1 / (d : ℝ)) = -(d : ℝ) := by field_simp
  rw [he₁, he₂] at hbound
  have htermA : (c * (1 / (d : ℝ)) * t) ^ (-(d : ℝ) / 2) =
      A * t ^ (-(d : ℝ) / 2) := by
    rw [mul_one_div, Real.mul_rpow (div_pos hc hdpos).le ht.le]
  have htermB : (c * (1 / (d : ℝ)) * t / (2 * ε)) ^ (-(d : ℝ)) =
      B * (ε ^ d * t ^ (-(d : ℝ))) := by
    have he : c * (1 / (d : ℝ)) * t / (2 * ε) =
        (c / (2 * (d : ℝ))) * t * ε⁻¹ := by ring
    rw [he, Real.mul_rpow (by positivity) (inv_pos.mpr hε).le,
      Real.mul_rpow (by positivity) ht.le,
      ← Real.rpow_neg_eq_inv_rpow, neg_neg, Real.rpow_natCast]
    dsimp [B]
    ring
  rw [htermA, htermB] at hbound
  calc
    X t ≤ A * t ^ (-(d : ℝ) / 2) + B * (ε ^ d * t ^ (-(d : ℝ))) := hbound
    _ ≤ (A + B) * t ^ (-(d : ℝ) / 2) +
        (A + B) * (ε ^ d * t ^ (-(d : ℝ))) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hB.le)
          (Real.rpow_nonneg ht.le _)
      · exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hA.le) (by positivity)
    _ = _ := by ring

end BouRabeeGwynne
