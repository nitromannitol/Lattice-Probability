/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5Walls2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L54C
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5Walls1

/-!
# The walls of the DG chain and the walled P3.17 at all of them (DEC-123 §2, P-317K-ADAPT)

DZZ arXiv:1807.00422, `LBM_LGDarXiv.tex`, Prop 3.17 (l. 1505–1517) for the walled distances
(Remark 5.2, l. 2281–2284), restricted to pairs inside `K^ξ` (`DZZProp317In`, S3P317E;
decision DEC-123 §2, finding 1 of P2-DZZ317K).

* **`DZZProp317Walls`**, **`dgWalls`**: exactly as stated in DEC-123 §2;
* `tildeBox_mem_dgWalls`, `sqBox_mem_dgWalls`;
* `mem_kXi_sqBox_near` (copy of `mem_kXi_sqBox`, S5L54G0, which is downstream of this file);
* **`l54_pair_kXi`**: the pairs `({u}, B δ)` of the L5.4 union bound (`l54_isXiAdmissible`,
  S5L54C) lie in `(𝕍_{u,1/10})^ξ` for `ξ ≤ 1/40`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set

namespace LQGMetric
namespace DZZ

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Walled DZZ P3.17 at every wall of a class `𝒦` (pairs inside `K^ξ`), D123. -/
def DZZProp317Walls (P : Measure Ω) (μ : Ω → Measure ℂ) (ξ : ℝ) (𝒦 : Set (Set ℂ)) : Prop :=
  ∀ K ∈ 𝒦, DZZProp317In P (fun ω => dzzWall K (μ ω)) K ξ

/-- The walls of the DG chain: the axis-parallel closed squares of side `1/10` centred within
sup-distance `1/20` of `(1/2, 1/2)` (the L5.4 walls `sqBox u (1/10)` and `legWalls u`, `u ∈ 𝕍̄`;
D128: only these are used, as in DZZ Remark 5.2 / L5.4, l. 2557–2563), and the tilde boxes of
pairs of `𝕍̄`. -/
def dgWalls : Set (Set ℂ) :=
  {K | ∃ c : ℂ, K = sqBox c (1 / 10) ∧ |c.re - 1 / 2| ≤ 1 / 20 ∧ |c.im - 1 / 2| ≤ 1 / 20} ∪
    {K | ∃ u ∈ dzzVbar, ∃ v ∈ dzzVbar, u ≠ v ∧ K = tildeBox u v}

lemma tildeBox_mem_dgWalls {u v : ℂ} (hu : u ∈ dzzVbar) (hv : v ∈ dzzVbar) (huv : u ≠ v) :
    tildeBox u v ∈ dgWalls :=
  Or.inr ⟨u, hu, v, hv, huv, rfl⟩

/-- A square of side `1/10` centred within `1/20` (sup-distance) of `(1/2, 1/2)` is a wall. -/
lemma sqBox_mem_dgWalls {c : ℂ} (hre : |c.re - 1 / 2| ≤ 1 / 20) (him : |c.im - 1 / 2| ≤ 1 / 20) :
    sqBox c (1 / 10) ∈ dgWalls :=
  Or.inl ⟨c, rfl, hre, him⟩

lemma dzzProp317In_tildeBox_of_walls {P : Measure Ω} {μ : Ω → Measure ℂ} {ξ : ℝ}
    (h : DZZProp317Walls P μ ξ dgWalls) {u v : ℂ} (hu : u ∈ dzzVbar) (hv : v ∈ dzzVbar)
    (huv : u ≠ v) : DZZProp317In P (fun ω => dzzWall (tildeBox u v) (μ ω)) (tildeBox u v) ξ :=
  h _ (tildeBox_mem_dgWalls hu hv huv)

lemma dzzProp317In_sqBox_of_walls {P : Measure Ω} {μ : Ω → Measure ℂ} {ξ : ℝ}
    (h : DZZProp317Walls P μ ξ dgWalls) {u : ℂ} (hu : u ∈ dzzVbar) :
    DZZProp317In P (fun ω => dzzWall (sqBox u (1 / 10)) (μ ω)) (sqBox u (1 / 10)) ξ := by
  obtain ⟨h1, h2⟩ := near_of_mem_dzzVbar hu
  exact h _ (sqBox_mem_dgWalls (h1.trans (by norm_num)) (h2.trans (by norm_num)))

/-- Points at sup-distance `≤ l/2 − ξ` from the centre of `𝕍_{c,l}` lie in `(𝕍_{c,l})^ξ`
(proof copied from `mem_kXi_sqBox`, S5L54G0, P2-DZZ53T). -/
lemma mem_kXi_sqBox_near {c z : ℂ} {l ξ : ℝ} (hre : |z.re - c.re| ≤ l / 2 - ξ)
    (him : |z.im - c.im| ≤ l / 2 - ξ) : z ∈ kXi (sqBox c l) ξ := by
  have hne : (sqBox c l)ᶜ.Nonempty := by
    refine ⟨c + ((|l| + 1 : ℝ) : ℂ), fun h => ?_⟩
    have h1 := h.1
    rw [show (c + ((|l| + 1 : ℝ) : ℂ)).re - c.re = |l| + 1 by simp,
      abs_of_pos (by positivity)] at h1
    linarith [le_abs_self l, abs_nonneg l]
  refine (Metric.le_infDist hne).2 fun y hy => ?_
  rw [mem_compl_iff] at hy
  rw [dist_eq_norm]
  by_contra hlt
  push Not at hlt
  apply hy
  have h1 := Complex.abs_re_le_norm (z - y)
  have h2 := Complex.abs_im_le_norm (z - y)
  rw [Complex.sub_re] at h1
  rw [Complex.sub_im] at h2
  rw [abs_le] at hre him h1 h2
  exact ⟨abs_le.2 ⟨by linarith, by linarith⟩, abs_le.2 ⟨by linarith, by linarith⟩⟩

lemma sqBox_twentieth_subset_kXi (u : ℂ) {ξ : ℝ} (hξ1 : ξ ≤ 1 / 40) :
    sqBox u (1 / 20) ⊆ kXi (sqBox u (1 / 10)) ξ := fun z hz =>
  mem_kXi_sqBox_near (hz.1.trans (by linarith)) (hz.2.trans (by linarith))

/-- The pairs of the L5.4 union bound (`l54_isXiAdmissible`, S5L54C) lie in `(𝕍_{u,1/10})^ξ`. -/
lemma l54_pair_kXi {ξ δ₁ : ℝ} (hξ1 : ξ ≤ 1 / 40) {u : ℂ} (B : ℝ → Set ℂ)
    (hB : ∀ δ ∈ Ioo (0 : ℝ) 1, δ < δ₁ → B δ ⊆ frontier (sqBox u (1 / 20))) :
    ∀ δ ∈ Ioo (0 : ℝ) 1, ({u} : Set ℂ) ⊆ kXi (sqBox u (1 / 10)) ξ ∧
      (if δ < δ₁ then B δ else {l54Pt u}) ⊆ kXi (sqBox u (1 / 10)) ξ := by
  intro δ hδ
  have hF : frontier (sqBox u (1 / 20)) ⊆ kXi (sqBox u (1 / 10)) ξ :=
    (isClosed_sqBox u _).frontier_subset.trans (sqBox_twentieth_subset_kXi u hξ1)
  refine ⟨singleton_subset_iff.mpr (sqBox_twentieth_subset_kXi u hξ1
    ⟨by norm_num, by norm_num⟩), ?_⟩
  split_ifs with h
  · exact (hB δ hδ h).trans hF
  · exact singleton_subset_iff.mpr (hF (l54Pt_mem_frontier u))

end DZZ
end LQGMetric
