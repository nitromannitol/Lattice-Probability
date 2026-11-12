/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S6L61C at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S6L61B

/-!
# DZZ Lemma 6.1, lower half: tools for the segment bound (P2-DZZ61L)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 6.1, l. 2593–2608.

* `conc_tendsto_of_eventually`: DZZ Proposition 3.17 for a pair of families that is
  `ξ`-admissible only for small `δ` (the families are completed by two fixed points).
* `frontier_openBox_eq`, `lgdMinSet_box_le_of_exit`: a path from `v ∈ ∂𝕍̄_{u,α}` to
  `∂𝕍̄_u` crosses `∂𝕍_{v,κ}`, `κ = (1−α)/20` (the first-exit step behind DZZ's use of
  (eq-point-to-boundary-kappa), l. 2593–2596; via `lgdMinSet_dzzWall_le_of_exit`, `K = ℂ`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric
namespace DZZ

variable {Ω : Type*} [MeasurableSpace Ω]

/-- DZZ Proposition 3.17 for families that are `ξ`-admissible for small `δ`. -/
theorem conc_tendsto_of_eventually {P : Measure Ω} {μ : Ω → Measure ℂ} {ξ : ℝ}
    (h317 : DZZProp317 P μ ξ) {a₀ b₀ : ℂ} (ha₀ : a₀ ∈ dzzVXi ξ) (hb₀ : b₀ ∈ dzzVXi ξ)
    (hab : ξ ≤ dist a₀ b₀) {A B : ℝ → Set ℂ}
    (hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), A δ ⊆ dzzVXi ξ ∧ B δ ⊆ dzzVXi ξ ∧
      IsXiAdmissibleSet ξ δ (A δ) ∧ IsXiAdmissibleSet ξ δ (B δ) ∧
      ∀ a ∈ A δ, ∀ b ∈ B δ, ξ ≤ dist a b)
    {ι : ℝ} (hι : ι ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun δ => P (conc1Event μ P δ ι (A δ) (B δ))ᶜ) (𝓝[>] 0) (𝓝 0) := by
  classical
  obtain ⟨c, hc, hconc⟩ := h317
  obtain ⟨δ₁, hδ₁, hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).mp hev
  let A' : ℝ → Set ℂ := fun δ => if δ ∈ Ioo (0 : ℝ) δ₁ then A δ else {a₀}
  let B' : ℝ → Set ℂ := fun δ => if δ ∈ Ioo (0 : ℝ) δ₁ then B δ else {b₀}
  have hAB : IsXiAdmissible ξ A' B' :=
    { subset_left := fun δ _ => by
        simp only [A']; split_ifs with h
        · exact (hsub h).1
        · exact singleton_subset_iff.mpr ha₀
      subset_right := fun δ _ => by
        simp only [B']; split_ifs with h
        · exact (hsub h).2.1
        · exact singleton_subset_iff.mpr hb₀
      adm_left := fun δ _ => by
        simp only [A']; split_ifs with h
        · exact (hsub h).2.2.1
        · exact Or.inl ⟨a₀, rfl⟩
      adm_right := fun δ _ => by
        simp only [B']; split_ifs with h
        · exact (hsub h).2.2.2.1
        · exact Or.inl ⟨b₀, rfl⟩
      dist_ge := fun δ _ a ha b hb => by
        simp only [A', B'] at ha hb; split_ifs at ha hb with h
        · exact (hsub h).2.2.2.2 a ha b hb
        · rw [mem_singleton_iff.mp ha, mem_singleton_iff.mp hb]; exact hab }
  obtain ⟨δ₀, hδ₀, hP⟩ := (hconc A' B' hAB).1 ι hι
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_ofReal_rpow_zero (a := c * ι ^ 2) (by have := hι.1; positivity))
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min hδ₀ hδ₁)] with δ hδ
  have h1 : δ ∈ Ioo (0 : ℝ) δ₁ := ⟨hδ.1, hδ.2.trans_le (min_le_right _ _)⟩
  have := hP δ ⟨hδ.1, hδ.2.trans_le (min_le_left _ _)⟩
  simp only [A', B', if_pos h1] at this
  exact this

lemma frontier_openBox_eq (c : ℂ) {l : ℝ} (hl : 0 < l) :
    frontier (Ioo (c.re - l / 2) (c.re + l / 2) ×ℂ Ioo (c.im - l / 2) (c.im + l / 2)) =
      frontier (sqBox c l) := by
  rw [sqBox_eq_reProdIm, Complex.frontier_reProdIm, Complex.frontier_reProdIm, closure_Ioo
    (by linarith), closure_Ioo (by linarith), frontier_Ioo (by linarith),
    frontier_Ioo (by linarith), closure_Icc, closure_Icc, frontier_Icc (by linarith),
    frontier_Icc (by linarith)]

lemma dzzWall_univ (μ : Measure ℂ) : dzzWall univ μ = μ := by
  simp [dzzWall]

/-- **First exit from `𝕍_{v,κ}`**: for `v ∈ ∂𝕍̄_{u,α}` and `κ = (1−α)/20`,
`min_{y ∈ ∂𝕍_{v,κ}} D_δ(v,y) ≤ min_{y ∈ ∂𝕍̄_u} D_δ(v,y)`. -/
theorem lgdMinSet_box_le_of_exit (μ : Measure ℂ) (δ : ℝ) {u v : ℂ} {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) (hv : v ∈ sqBox u (α / 20)) :
    lgdMinSet μ δ {v} (frontier (sqBox v ((1 - α) / 20))) ≤
      lgdMinSet μ δ {v} (frontier (sqBox u (1 / 20))) := by
  set κ := (1 - α) / 20
  have hκ : 0 < κ := by simp only [κ]; linarith
  set U := Ioo (v.re - κ / 2) (v.re + κ / 2) ×ℂ Ioo (v.im - κ / 2) (v.im + κ / 2)
  have hU : IsOpen U := isOpen_Ioo.reProdIm isOpen_Ioo
  have hvU : v ∈ U := Complex.mem_reProdIm.mpr
    ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  rw [← frontier_openBox_eq v hκ]
  refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
  rw [mem_singleton_iff.mp hx]
  have hyU : y ∉ U := by
    intro hyU
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := Complex.mem_reProdIm.mp hyU
    obtain ⟨h5, h6⟩ := hv
    rw [abs_le] at h5 h6
    have := edge_of_mem_frontier_sqBox (by norm_num : (0 : ℝ) < 1 / 20) hy
    rcases this with h | h <;> rw [abs_eq (by norm_num)] at h <;> simp only [κ] at * <;>
      rcases h with h | h <;> linarith
  have := lgdMinSet_dzzWall_le_of_exit μ δ hU hvU hyU (K := univ)
    (fun _ _ _ _ => subset_univ _)
  rwa [dzzWall_univ] at this

end DZZ
end LQGMetric
