/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3ConcF at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3ConcE
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3D124
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12S5
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L7CountPsi
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L4
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L1Var
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3VarBdry

/-!
# The coarse field `𝒳_δ` and the good set `𝒜` (P2-DZZCONC, re-based on D124 by P2-DZZI0)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex`) l. 1555–1571: `𝐗_δ` is spanned by the field at scales
`ε ≥ δ^{C_mc}`; `𝒳_δ = (η_ε(v), h̃_ε(v))`; `𝒜_δ = {each cell of 𝒱_δ has side ≥ δ^{C_mc}}`, on
which `D'_{γ,δ} = D'_{γ,δ,𝒳_δ}` is a function of `𝒳_δ` (l. 1567–1569).

* `CoarseIdx κ δ`, `coarseField W κ δ`: DZZ's `𝒳_δ`, from `S3D124` (decision D124: `η` at the
  dyadic boxes of side `≥ δ^κ`, `h̃` at the rational coarse points).
* `coarseMass` (the box masses `M_{γ,s_B}(B)` read off a path `x` at `Sum.inl b`, `0` below
  `δ^κ`), `coarseLogD` (`log D'` from `x`), `CoarseGood` (DZZ's `𝒜_δ`, as a set of paths).
* `isCell_iff_of_agree`, **`logApproxLGD_eq_coarseLogD`**: `log D'_{γ,δ}(A,B) = F(𝒳_δ)` on `𝒜_δ`.
* **`coarseGood_of_cellSizeEvent`**, **`measureReal_not_coarseGood_le`**: `𝒳_δ ∈ 𝒜_δ` on the event
  of DZZ Lemma 3.1, hence `P(𝒳_δ ∉ 𝒜_δ) ≤ δ^c`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter Metric

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

variable {Ω : Type*} [MeasurableSpace Ω]

open Classical in
/-- The box masses `M_{γ,s_B}(B)` read off a coarse path `x` (`0` for `s_B < δ^κ`). -/
def coarseMass (γ κ δ : ℝ) (x : CoarseIdx κ δ → ℝ) (b : DyBox) : ℝ :=
  if h : δ ^ κ ≤ b.side then
    b.side ^ 2 * Real.exp (γ * x (Sum.inl ⟨b, h⟩) - γ ^ 2 / 2 * etaVar b.side b.center)
  else 0

/-- `log D'_{γ,δ,x}(A, B)`. -/
def coarseLogD (γ κ δ : ℝ) (A B : Set ℂ) (x : CoarseIdx κ δ → ℝ) : ℝ :=
  Real.log ((approxDistSet (coarseMass γ κ δ x) δ A B).toNat : ℝ)

/-- DZZ's `𝒜_δ`: every cell has side `≥ δ^κ`. -/
def CoarseGood (γ κ δ : ℝ) : Set (CoarseIdx κ δ → ℝ) :=
  {x | ∀ b, IsCell (coarseMass γ κ δ x) δ b → δ ^ κ ≤ b.side}

lemma side_le_side_anc (b : DyBox) (i : ℕ) : b.side ≤ (b.anc i).side := by
  rcases le_total b.n i with h | h
  · rw [anc_self h]
  · rw [side_anc h]
    have : (1 : ℝ) ≤ ((2 ^ (b.n - i) : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_two_pow
    have hs : 0 ≤ b.side := by unfold DyBox.side; positivity
    nlinarith

/-- Two mass functions agreeing above `s₀`, the second vanishing below `s₀` with all its cells
above `s₀`, have the same cells. -/
lemma isCell_iff_of_agree {m m' : DyBox → ℝ} {δ s₀ : ℝ} (hδ : δ ≠ 0)
    (hag : ∀ b : DyBox, s₀ ≤ b.side → m b = m' b) (hz : ∀ b : DyBox, b.side < s₀ → m' b = 0)
    (hbig : ∀ b, IsCell m' δ b → s₀ ≤ b.side) (b : DyBox) : IsCell m δ b ↔ IsCell m' δ b := by
  have hd : 0 < δ ^ 2 := by positivity
  have transfer : ∀ (m₁ m₂ : DyBox → ℝ), (∀ c : DyBox, s₀ ≤ c.side → m₁ c = m₂ c) →
      s₀ ≤ b.side → IsCell m₁ δ b → IsCell m₂ δ b := by
    intro m₁ m₂ h12 hs ⟨h1, h2⟩
    refine ⟨by rw [← h12 b hs]; exact h1, fun i hi => ?_⟩
    rw [← h12 _ (hs.trans (side_le_side_anc b i))]
    exact h2 i hi
  constructor
  · intro hc
    by_cases hs : s₀ ≤ b.side
    · exact transfer m m' hag hs hc
    · exfalso
      push Not at hs
      have hex : ∃ k, (b.anc k).side < s₀ := ⟨b.n, by rw [anc_self le_rfl]; exact hs⟩
      set k := Nat.find hex
      have hk : (b.anc k).side < s₀ := Nat.find_spec hex
      have hkn : k ≤ b.n := Nat.find_min' hex (by rw [anc_self le_rfl]; exact hs)
      have hcell : IsCell m' δ (b.anc k) := by
        refine ⟨by rw [hz _ hk]; exact hd, fun i hi => ?_⟩
        have hik : i < k := by
          have : (b.anc k).n = k := min_eq_left hkn
          omega
        rw [anc_anc b hik.le]
        have hsi : s₀ ≤ (b.anc i).side := by
          by_contra h'
          exact Nat.find_min hex hik (lt_of_not_ge h')
        rw [← hag _ hsi]
        exact hc.2 i (lt_of_lt_of_le hik hkn)
      exact absurd (hbig _ hcell) (not_le.2 hk)
  · intro hc
    exact transfer m' m (fun c hc' => (hag c hc').symm) (hbig b hc) hc

/-- **`D'_{γ,δ} = D'_{γ,δ,𝒳_δ}` on `𝒜_δ`** (DZZ l. 1567–1569). -/
theorem logApproxLGD_eq_coarseLogD {γ κ δ : ℝ} (hδ : δ ≠ 0) (W : WNSpace → Ω → ℝ)
    (A B : Set ℂ) (ω : Ω) (hω : (fun s => coarseField W κ δ s ω) ∈ CoarseGood γ κ δ) :
    logApproxLGD γ W δ A B ω = coarseLogD γ κ δ A B (fun s => coarseField W κ δ s ω) := by
  have hiff := isCell_iff_of_agree (m := approxLQG γ W ω)
    (m' := coarseMass γ κ δ (fun s => coarseField W κ δ s ω)) (s₀ := δ ^ κ) hδ
    (fun b hb => by simp [coarseMass, hb, approxLQG, coarseField_inl])
    (fun b hb => by simp [coarseMass, not_le.2 hb]) hω
  have hfun : IsCell (approxLQG γ W ω) δ =
      IsCell (coarseMass γ κ δ (fun s => coarseField W κ δ s ω)) δ := funext fun b => propext (hiff b)
  have hg : cellGraph (approxLQG γ W ω) δ =
      cellGraph (coarseMass γ κ δ (fun s => coarseField W κ δ s ω)) δ := by
    ext b b'
    simp only [cellGraph, hiff]
  unfold logApproxLGD coarseLogD approxLGDSet approxDistSet approxDist
  rw [hg]
  simp only [hiff]

/-- On the event of DZZ Lemma 3.1 the coarse field lies in `𝒜_δ` (DZZ l. 1567–1569: on
`𝒜_δ`, `D'` is read off `𝒳_δ`; Lemma 3.1 gives `P(𝒜_δ) ≥ 1 − δ^c`). -/
theorem coarseGood_of_cellSizeEvent {γ δ : ℝ} (hδ : δ ≠ 0) (W : WNSpace → Ω → ℝ) {ω : Ω}
    (hω : ω ∈ cellSizeEvent γ W δ) :
    (fun s => coarseField W (dzzCmc γ) δ s ω) ∈ CoarseGood γ (dzzCmc γ) δ := by
  intro b hb
  by_contra hlt
  push Not at hlt
  have hd : 0 < δ ^ 2 := by positivity
  obtain ⟨c, hc, hcm⟩ := hω.1 b.center (mem_center_self b).1
  have hcs := (hω.2 c hc).1
  have hcn : c.n < b.n := by
    by_contra hn
    push Not at hn
    have : c.side ≤ b.side := by
      unfold DyBox.side
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    linarith
  have hanc : b.anc c.n = c := by
    rw [← (mem_center_self b).2, anc_boxAt hcn.le, hcm.2]
  have h1 := hb.2 c.n hcn
  rw [hanc] at h1
  have h2 : coarseMass γ (dzzCmc γ) δ (fun s => coarseField W (dzzCmc γ) δ s ω) c =
      approxLQG γ W ω c := by
    simp [coarseMass, hcs, approxLQG, coarseField_inl]
  rw [h2] at h1
  exact absurd hc.1 (not_lt.2 h1)

/-- **`P(𝒳_δ ∉ 𝒜_δ) ≤ δ^c`** (DZZ Lemma 3.1, `dzz_lemma31`). -/
theorem measureReal_not_coarseGood_le {P : Measure Ω} {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) : ∃ c : ℝ, 0 < c ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      P.real {ω | (fun s => coarseField W (dzzCmc γ) δ s ω) ∉ CoarseGood γ (dzzCmc γ) δ} ≤
        δ ^ c := by
  have := hW.isProbabilityMeasure
  obtain ⟨c, hc, δ₀, hδ₀, h⟩ := dzz_lemma31 hW hγ hγ2
  refine ⟨c, hc, δ₀, hδ₀, fun δ hδ => ?_⟩
  have hsub : {ω | (fun s => coarseField W (dzzCmc γ) δ s ω) ∉ CoarseGood γ (dzzCmc γ) δ} ⊆
      (cellSizeEvent γ W δ)ᶜ := fun ω hω hω' =>
    hω (coarseGood_of_cellSizeEvent hδ.1.ne' W hω')
  refine (measureReal_mono hsub).trans ?_
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal (by have := hδ.1; positivity) (h δ hδ)

end DZZ
end LQGMetric
