/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L7PercIndep at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L7Perc

/-!
# DZZ Lemma 3.7: independence of far bad boxes (P2-DZZ3E)

Ding–Zeitouni–Zhang (arXiv:1807.00422, `LBM_LGDarXiv.tex`) (eq-B'-i-open), l. 992–996: the events
`𝓔_{B'_i,open}ᶜ` of same-level boxes at pairwise index distance `> r` are mutually independent
(the `hind` input of `perc_annulus_peierls`), once `2R + 2 · 2^{-(n+k'')} ≤ r 2^{-n}` and
`r(u) ≤ R` on the band.

* `boxOpen_compl_eq`: `𝓔_{B',open}ᶜ` as an event of the band field at `bdryCenters B' k''`.
* `measure_biInter_boxOpen_compl`: the product formula.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- The open set of band values: `γ x − γ²/2 Var < a`. -/
def bandGood (γ : ℝ) (s e a : ℝ) (w : ℂ) : Set ℝ :=
  {x | γ * x - γ ^ 2 / 2 * etaBandVar s e w < a}

lemma measurableSet_bandGood (γ s e a : ℝ) (w : ℂ) : MeasurableSet (bandGood γ s e a w) :=
  measurableSet_lt (by fun_prop) measurable_const

lemma boxOpen_compl_eq (γ : ℝ) (W : WNSpace → Ω → ℝ) (B : DyBox) (k'' N : ℕ) (a : ℝ) :
    (boxOpen γ W B k'' N a)ᶜ = {ω | ∃ w ∈ bdryCenters B k'',
      etaField W (Ioo (((2 : ℝ)⁻¹ ^ (B.n + k'')) ^ 2) (((2 : ℝ)⁻¹ ^ N) ^ 2)) w ω ∉
        bandGood γ ((2 : ℝ)⁻¹ ^ (B.n + k'')) ((2 : ℝ)⁻¹ ^ N) a w} := by
  ext ω
  simp only [boxOpen, mem_compl_iff, mem_ofPred_eq, not_forall, not_lt, mem_bdryCenters]
  constructor
  · rintro ⟨bt, hbt, h⟩
    refine ⟨bt.center, ⟨bt, hbt, rfl⟩, ?_⟩
    simp only [bandGood, mem_ofPred_eq, not_lt]
    rw [← side_bdry hbt]; exact h
  · rintro ⟨w, ⟨bt, hbt, rfl⟩, h⟩
    refine ⟨bt, hbt, ?_⟩
    simp only [bandGood, mem_ofPred_eq, not_lt] at h
    rw [← side_bdry hbt] at h; exact h

/-- **Independence of far bad boxes** (DZZ (eq-B'-i-open)). -/
theorem measure_biInter_boxOpen_compl (hW : IsWhiteNoise P W) (γ : ℝ) (F : Finset DyBox)
    {n₁ k'' N r : ℕ} {a R : ℝ} (hF : ∀ B ∈ F, B.n = n₁)
    (hR : ∀ u ∈ Ioo (((2 : ℝ)⁻¹ ^ (n₁ + k'')) ^ 2) (((2 : ℝ)⁻¹ ^ N) ^ 2), etaRad u ≤ R)
    (hRs : 2 * R + 2 * (2 : ℝ)⁻¹ ^ (n₁ + k'') ≤ r * (2 : ℝ)⁻¹ ^ n₁)
    (hfar : ∀ B₁ ∈ F, ∀ B₂ ∈ F, B₁ ≠ B₂ → (B₁.j + r + 1 ≤ B₂.j ∨ B₂.j + r + 1 ≤ B₁.j ∨
      B₁.k + r + 1 ≤ B₂.k ∨ B₂.k + r + 1 ≤ B₁.k)) :
    P (⋂ B ∈ F, (boxOpen γ W B k'' N a)ᶜ) = ∏ B ∈ F, P (boxOpen γ W B k'' N a)ᶜ := by
  set I := Ioo (((2 : ℝ)⁻¹ ^ (n₁ + k'')) ^ 2) (((2 : ℝ)⁻¹ ^ N) ^ 2)
  set G := bandGood γ ((2 : ℝ)⁻¹ ^ (n₁ + k'')) ((2 : ℝ)⁻¹ ^ N) a
  have hc : ∀ B ∈ F, (boxOpen γ W B k'' N a)ᶜ =
      {ω | ∃ w ∈ bdryCenters B k'', etaField W I w ω ∉ G w} := by
    intro B hB; rw [boxOpen_compl_eq, hF B hB]
  set S : F → Finset ℂ := fun B => bdryCenters B.1 k''
  have hdisj : Pairwise fun i j : F => Disjoint (bandSupp (((2 : ℝ)⁻¹ ^ (n₁ + k'')) ^ 2)
      (((2 : ℝ)⁻¹ ^ N) ^ 2) R (S i)) (bandSupp (((2 : ℝ)⁻¹ ^ (n₁ + k'')) ^ 2)
      (((2 : ℝ)⁻¹ ^ N) ^ 2) R (S j)) := by
    intro i j hij
    have hn : i.1.n = j.1.n := (hF _ i.2).trans (hF _ j.2).symm
    refine disjoint_bandSupp_of_far hn (hfar _ i.2 _ j.2 fun h => hij (Subtype.ext h)) ?_
    rw [hF _ i.2]; unfold DyBox.side; rw [hF _ i.2]; exact hRs
  have key := measure_biInter_band_bad_eq_prod hW (Finset.univ : Finset F) S (by positivity) hR
    hdisj G (measurableSet_bandGood _ _ _ _)
  have e1 : (⋂ B ∈ F, (boxOpen γ W B k'' N a)ᶜ) =
      ⋂ i ∈ (Finset.univ : Finset F), {ω | ∃ w ∈ S i, etaField W I w ω ∉ G w} := by
    ext ω
    simp only [mem_iInter, Finset.mem_univ, true_implies, Subtype.forall]
    exact forall₂_congr fun B hB => by rw [hc B hB]
  rw [e1, key, ← Finset.prod_coe_sort F]
  exact Finset.prod_congr rfl fun i _ => by rw [hc i.1 i.2]

end DZZ
end LQGMetric
