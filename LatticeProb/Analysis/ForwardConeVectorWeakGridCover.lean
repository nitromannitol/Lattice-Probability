import LatticeProb.Analysis.ForwardConeVectorEndpoint
import LatticeProb.Analysis.ConeVectorWeakGridCover

/-!
# Grid barriers for reflected forward cone vectors

Reflection sends a forward cone vector to a pair with weak grid barriers.
-/

set_option autoImplicit false

open Set

namespace LatticeProb

/-- A reflected forward cone vector has approximate grid barriers in one of
    the two coordinate orientations. -/
theorem forwardConeVector_reflected_exists_grid_barriers
    {X Y : ℝ → ℝ} {N : ℕ} (hN : 0 < N) {a s b d H e : ℝ}
    (hX : Continuous X) (hY : Continuous Y)
    (hdrop : ∃ t > s, X t < X s ∨ Y t < Y s)
    (hvec : (a, s) ∈ forwardConeVectors X Y)
    (ha : 0 < -a) (hab : -a < b) (hbs : b < -s) (hs : -s < 1)
    (hd : 0 ≤ d) (hH : 0 ≤ H)
    (hmesh : 1 / (N : ℝ) < -a)
    (hsep : d + 1 / (N : ℝ) < -s - -a)
    (hforward : -a + H ≤ -s) (hbackward : b + H + 1 / (N : ℝ) < -s)
    (hmodX : ∀ x ∈ Icc (-a - 1 / (N : ℝ) - (-s - b)) (-s + 1 / (N : ℝ)),
      ∀ y ∈ Icc (-a - 1 / (N : ℝ) - (-s - b)) (-s + 1 / (N : ℝ)),
        |x - y| ≤ 1 / (N : ℝ) → |X (-x) - X (-y)| ≤ e)
    (hmodY : ∀ x ∈ Icc (-a - 1 / (N : ℝ) - (-s - b)) (-s + 1 / (N : ℝ)),
      ∀ y ∈ Icc (-a - 1 / (N : ℝ) - (-s - b)) (-s + 1 / (N : ℝ)),
        |x - y| ≤ 1 / (N : ℝ) → |Y (-x) - Y (-y)| ≤ e) :
    ∃ i j : Fin N,
      let t₀ : ℝ := (i.val : ℝ) / N
      let t₁ : ℝ := (j.val : ℝ) / N
      0 < t₀ ∧ t₁ < 1 ∧ d < t₁ - t₀ ∧
      |t₀ - -a| ≤ 1 / (N : ℝ) ∧ |t₁ - -s| ≤ 1 / (N : ℝ) ∧
      (((∀ u ∈ Icc 0 H, X (-t₀) - 2 * e ≤ X (-(t₀ + u))) ∧
        (∀ u ∈ Icc 0 H, X (-t₁) - 2 * e ≤ X (-(t₁ - u)) ∧
          Y (-t₁) - 2 * e ≤ Y (-(t₁ - u))) ∧
        |X (-t₁) - X (-t₀)| ≤ 2 * e ∧
        ∀ x ∈ Icc t₀ t₁, X (-t₁) - 2 * e ≤ X (-x)) ∨
      ((∀ u ∈ Icc 0 H, Y (-t₀) - 2 * e ≤ Y (-(t₀ + u))) ∧
        (∀ u ∈ Icc 0 H, Y (-t₁) - 2 * e ≤ Y (-(t₁ - u)) ∧
          X (-t₁) - 2 * e ≤ X (-(t₁ - u))) ∧
        |Y (-t₁) - Y (-t₀)| ≤ 2 * e ∧
        ∀ x ∈ Icc t₀ t₁, Y (-t₁) - 2 * e ≤ Y (-x))) := by
  have hbar : ∀ x ∈ Icc (-a) (-s), X s ≤ X (-x) ∧ Y s ≤ Y (-x) := by
    intro x hx
    have h := hvec.2.2.2 (-x) (by rw [← hvec.1]; constructor <;> linarith [hx.1, hx.2])
    exact h
  have hlocal : ∀ x ∈ Icc b (-s), X s ≤ X (-x) ∧ Y s ≤ Y (-x) := by
    intro x hx
    exact hbar x ⟨le_trans hab.le hx.1, hx.2⟩
  rcases forwardConeVector_closed_barrier hX hY hdrop hvec with ⟨heq, _⟩ | ⟨heq, _⟩
  · have hclosed : ∀ x ∈ Icc (-a) (-s), X (-(-s)) ≤ X (-x) := by
      intro x hx
      simpa using (hbar x hx).1
    have hlocal' : ∀ x ∈ Icc b (-s), X (-(-s)) ≤ X (-x) ∧ Y (-(-s)) ≤ Y (-x) := by
      simpa using hlocal
    have heq' : X (-(-a)) = X (-(-s)) := by simpa using heq
    obtain ⟨i, j, hi, hj, hdist, h₀, h₁, hrest⟩ :=
      closedBarriers_exists_grid_barriers (X := fun t => X (-t)) (Y := fun t => Y (-t))
        hN ha hab hbs hs heq' hclosed hlocal' hd hH hmesh hsep hforward hbackward hmodX hmodY
    exact ⟨i, j, hi, hj, hdist, h₀, h₁, Or.inl hrest⟩
  · have hclosed : ∀ x ∈ Icc (-a) (-s), Y (-(-s)) ≤ Y (-x) := by
      intro x hx
      simpa using (hbar x hx).2
    have hlocal' : ∀ x ∈ Icc b (-s), Y (-(-s)) ≤ Y (-x) ∧ X (-(-s)) ≤ X (-x) := by
      intro x hx
      simpa using ⟨(hlocal x hx).2, (hlocal x hx).1⟩
    have heq' : Y (-(-a)) = Y (-(-s)) := by simpa using heq
    obtain ⟨i, j, hi, hj, hdist, h₀, h₁, hrest⟩ :=
      closedBarriers_exists_grid_barriers (X := fun t => Y (-t)) (Y := fun t => X (-t))
        hN ha hab hbs hs heq' hclosed hlocal' hd hH hmesh hsep hforward hbackward hmodY hmodX
    exact ⟨i, j, hi, hj, hdist, h₀, h₁, Or.inr hrest⟩

end LatticeProb
