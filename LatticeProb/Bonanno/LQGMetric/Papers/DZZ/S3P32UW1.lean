/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32UW1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L5W6
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32YCross

/-!
# Walled (Eq.boundDprime), UW1: the deterministic crossing at a dyadic wall by similarity
(P2-DZZUPW, packet P-317K-UP, decision D123)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`) Prop 3.2, upper half (Eq.boundDprime), l. 1088–1103,
for the walled LGD `D^{B̄w}` (Remark 5.2, l. 2281–2284) and the walled approximate distance
`D'_S`, `S = cellsInside Bw`. Reuse (near miss, route (a) of AGENT_GUIDE): the deterministic
crossing claim at `𝕍` is the proved `l32BallCrossingW_holds` (S3P32YCross, D102). The wall box
`B̄w` is the image of `𝕍` under the similarity `wHom Bw` (S3L5W1, P2-DZZL35W), which maps the dyadic
grid of `𝕍` onto the dyadic sub-boxes of `B̄w` (`wEmb Bw`). Hence:

* `lgdDZZ_wPull`, `lgdMinSet_wPull`: `D^ν_δ` is invariant under the similarity, for the pulled-back
  measure `wPullMeas Bw ν = ν ∘ wHom Bw` (from `lgdDZZ_map_similarity`, Dimension/LGDScale);
* `approxDistSetOn_wHom` (S3L5W2): `D'_S` is the `D'` of the pulled-back mass;
* **`l32BallCrossingOn`**: the walled crossing claim, i.e. `l32BallCrossingW_holds` applied to the
  pulled-back mass `m ∘ wEmb Bw` and measure `wPullMeas Bw ν`.

The enclosures and the start conditions are those of the pulled-back cells and sets (relative to
the wall, as `encEventPsiW` of S3L5W3).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open DyBox

/-- The measure `ν` seen from `𝕍` through the similarity `wHom Bw : 𝕍 → B̄w`. -/
def wPullMeas (Bw : DyBox) (ν : Measure ℂ) : Measure ℂ := ν.map (wHom Bw).symm

lemma wHom_eq_simMap (Bw : DyBox) : ⇑(wHom Bw) = simMap ((Bw.side : ℝ) : ℂ) (wOff Bw) := by
  funext z; rw [wHom_apply]; rfl

lemma map_wPullMeas (Bw : DyBox) (ν : Measure ℂ) : (wPullMeas Bw ν).map (wHom Bw) = ν := by
  rw [wPullMeas, Measure.map_map (wHom Bw).continuous.measurable
    (wHom Bw).symm.continuous.measurable]
  have : ⇑(wHom Bw) ∘ ⇑(wHom Bw).symm = id := by
    funext z; simp
  rw [this, Measure.map_id]

/-- Similarity invariance of `D_δ` at a dyadic wall. -/
lemma lgdDZZ_wPull (Bw : DyBox) (ν : Measure ℂ) (δ : ℝ) (x y : ℂ) :
    lgdDZZ (wPullMeas Bw ν) δ x y = lgdDZZ ν δ (wHom Bw x) (wHom Bw y) := by
  have ha : ((Bw.side : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (wside_pos Bw).ne'
  have h := lgdDZZ_map_similarity ha (wOff Bw) (wPullMeas Bw ν) δ x y
  rw [← wHom_eq_simMap, map_wPullMeas] at h
  exact h.symm

/-- `min_{A × B} D_δ` is invariant under the similarity. -/
lemma lgdMinSet_wPull (Bw : DyBox) (ν : Measure ℂ) (δ : ℝ) (A B : Set ℂ) :
    lgdMinSet ν δ A B = lgdMinSet (wPullMeas Bw ν) δ (wHom Bw ⁻¹' A) (wHom Bw ⁻¹' B) := by
  unfold lgdMinSet
  apply le_antisymm
  · refine le_iInf₂ fun x' hx' => le_iInf₂ fun y' hy' => ?_
    rw [lgdDZZ_wPull]
    exact (iInf₂_le (wHom Bw x') hx').trans (iInf₂_le (wHom Bw y') hy')
  · refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
    have hx' : (wHom Bw).symm x ∈ wHom Bw ⁻¹' A := by simpa using hx
    have hy' : (wHom Bw).symm y ∈ wHom Bw ⁻¹' B := by simpa using hy
    refine (iInf₂_le _ hx').trans ((iInf₂_le _ hy').trans ?_)
    rw [lgdDZZ_wPull]; simp

/-- **The walled crossing claim** (DZZ l. 1088–1101 with Remark 5.2): `l32BallCrossingW_holds`
for the pulled-back mass and measure. `r` is the clipping depth in the coordinates of `𝕍`
(i.e. `s_{Bw} r` in the wall), `N₀` bounds the levels of the pulled-back cells. -/
theorem l32BallCrossingOn {m : DyBox → ℝ} {ν : Measure ℂ} {δ lam R r : ℝ} {k N₀ : ℕ}
    {Bw : DyBox} {A B : Set ℂ} (hδ : 0 < δ) (hlam : 1 ≤ lam) (hR : 0 ≤ R) (hr : 0 < r)
    (hr2 : 2 * r < (2⁻¹ : ℝ) ^ (N₀ + k))
    (hpart : ∀ v ∈ dzzV, ∃ b, IsCell m δ b ∧ b.Mem v)
    (hN₀ : ∀ b, IsCell m δ b → b.n ≤ Bw.n + N₀) (hs : WSplit m δ Bw)
    (henc : ∀ b, IsCell m δ (wEmb Bw b) →
      HasEnclosure b k fun c => PhiLeW (wPullMeas Bw ν) δ r c lam)
    (hAi : A ⊆ interior Bw.closedBox) (hBi : B ⊆ interior Bw.closedBox)
    (hA : wHom Bw ⁻¹' A ⊆ dzzVIn r) (hB : wHom Bw ⁻¹' B ⊆ dzzVIn r)
    (hAn : A.Nonempty) (hBn : B.Nonempty)
    (hSA : BallStartCondC (wPullMeas Bw ν) (fun c => m (wEmb Bw c)) δ r R (wHom Bw ⁻¹' A))
    (hSB : BallStartCondC (wPullMeas Bw ν) (fun c => m (wEmb Bw c)) δ r R (wHom Bw ⁻¹' B)) :
    ((lgdMinSet ν δ A B : ℕ∞) : ℝ≥0∞) ≤
      ((approxDistSetOn (cellsInside Bw) m δ A B : ℕ∞) : ℝ≥0∞) *
          ENNReal.ofReal (4 ^ (k + 2) * (lam + 1)) + ENNReal.ofReal (2 * R + 8) := by
  have hne : ∀ X : Set ℂ, X.Nonempty → (wHom Bw ⁻¹' X).Nonempty := fun X ⟨x, hx⟩ =>
    ⟨(wHom Bw).symm x, by simpa using hx⟩
  rw [lgdMinSet_wPull Bw, approxDistSetOn_wHom hs hAi hBi]
  exact l32BallCrossingW_holds (fun c => m (wEmb Bw c)) (wPullMeas Bw ν) δ lam R r k N₀ _ _ hδ
    hlam hR hr hr2 (hpart_wEmb hs hpart hN₀)
    (fun b hb => by
      have := hN₀ _ ((isCell_wEmb_iff hs).2 hb); simp only [wEmb] at this; omega)
    (not_isCell_root_of_split hs) (fun b hb => henc b ((isCell_wEmb_iff hs).2 hb)) hA hB
    (hne A hAn) (hne B hBn) hSA hSB

end DZZ
end LQGMetric
