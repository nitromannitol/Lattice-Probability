/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L54F3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L54F1

/-!
# The truncation of the leg at the first ball meeting `∂𝕍_{u,λ}` (P2-DZZ61K, D117 §2(a)(ii))

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 5.4, l. 2562
("with high probability, balls intersecting both `∂𝕍_{u,λ}` and `∂𝕍_{u,2λ}` have LQG measure
larger than `2δ²`") and (eq-geodesic-range) l. 2340–2345, in the corrected form of DEC-117
§2(a)(ii): `dzzLegTruncC_of_mem` proves `DZZLegTruncC u` for `u ∈ 𝕍̄` (stadium walls `legWallC`;
D123 transfers it to `legWall` in S5D123).

Argument (DEC-117 §2(a)(ii); the first-hitting-time technique is that of
`lgdMinSet_dzzWall_le_of_exit`, S3P32X): take a chain of balls of mass `≤ δ²` for
`D̄^{u,2λ}(u, y)`, `y ∈ ∂𝕍_{u,λ}`, with path `p`. All its balls lie in `𝕍_{u,2λ} ⊆ 𝕍` and, by the
big-balls condition, have radius `< λ/4`. Let `s₀` be the first time `p` hits the closure of the
union `V` of the balls meeting `∂𝕍_{u,λ}`. Before `s₀` the path stays in `𝕍_{u,λ}` and its balls do
not meet `∂𝕍_{u,λ}`, so they lie in `𝕍_{u,λ}`. At `s₀` the ball `B_k` containing `p(s₀)` meets a
ball `B_b` meeting `∂𝕍_{u,λ}` at some `w ∈ S_i`; `B_b ⊆ N_{λ/2}(S_i)` (radius `< λ/4`). Then
`p|[0,s₀]`, a segment in `B_k` and a segment in `B_b` form a path from `u` to `w ∈ S_i` covered by
balls of the original chain lying in `legWallC u λ S_i`. The step is our own elementary write-up
of DEC-117's argument (DZZ give no proof of the corrected form).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

lemma sqBox_tenth_subset_dzzV {u : ℂ} (hu : u ∈ dzzVbar) : sqBox u (1 / 10) ⊆ dzzV := by
  obtain ⟨h1, h2⟩ := near_of_mem_dzzVbar hu
  intro z ⟨h3, h4⟩
  rw [abs_le] at h1 h2 h3 h4
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- A preconnected set meeting a closed set `K` and its complement meets `∂K`. -/
lemma exists_mem_frontier_of_isPreconnected {A K : Set ℂ} (hA : IsPreconnected A)
    (hK : IsClosed K) (h1 : (A ∩ K).Nonempty) (h2 : (A \ K).Nonempty) :
    (A ∩ frontier K).Nonempty := by
  by_contra hne
  rw [not_nonempty_iff_eq_empty] at hne
  have hsub : A ⊆ interior K ∪ Kᶜ := fun z hz => by
    by_cases hzK : z ∈ K
    · left
      by_contra hzi
      have : z ∈ A ∩ frontier K := ⟨hz, by rw [frontier, hK.closure_eq]; exact ⟨hzK, hzi⟩⟩
      rw [hne] at this; exact this
    · exact Or.inr hzK
  obtain ⟨z, hzA, hzK⟩ := h1
  have hzi : z ∈ interior K := by
    rcases hsub hzA with h | h
    · exact h
    · exact absurd hzK h
  have := hA.subset_left_of_subset_union isOpen_interior hK.isOpen_compl
    (disjoint_compl_right.mono_left interior_subset) hsub ⟨z, hzA, hzi⟩
  obtain ⟨y, hyA, hyK⟩ := h2
  exact hyK (interior_subset (this hyA))

/-- `DZZLegTrunc` (S5L54F1) with DEC-117's stadium wall `legWallC` in place of `legWall`. -/
def DZZLegTruncC (u : ℂ) : Prop :=
  ∀ (ν : Measure ℂ) (δ : ℝ), (∀ (x : ℂ) (ρ : ℝ), 1 / 80 ≤ ρ → Metric.ball x ρ ⊆ dzzV →
      ENNReal.ofReal (2 * δ ^ 2) < ν (Metric.ball x ρ)) →
    ∀ {I : Type} (S : I → Set ℂ), (∀ i, S i ⊆ frontier (sqBox u (1 / 20))) →
      frontier (sqBox u (1 / 20)) ⊆ ⋃ i, S i →
      ∃ i, lgdMinSet (dzzWall (legWallC u (1 / 20) (S i)) ν) δ {u} (S i) ≤
        lgdMinSet (dzzWall (sqBox u (1 / 10)) ν) δ {u} (frontier (sqBox u (1 / 20)))

/-- **Truncation lemma** (DEC-117 §2(a)(ii), P-BIG): `DZZLegTruncC u` for `u ∈ 𝕍̄` (the stadium
walls; `dzzLegTrunc_of_mem` in S5D123 transfers it to the D123 walls `legWall`). -/
theorem dzzLegTruncC_of_mem {u : ℂ} (hu : u ∈ dzzVbar) : DZZLegTruncC u := by
  classical
  intro ν δ hB I S hS hcov
  set F := frontier (sqBox u (1 / 20)) with hFdef
  set K₀ := sqBox u (1 / 20) with hK₀def
  have hK₀ : IsClosed K₀ := isClosed_sqBox u _
  have hFK : F ⊆ K₀ := hK₀.frontier_subset
  have huK : u ∈ K₀ := ⟨by rw [sub_self, abs_zero]; norm_num, by rw [sub_self, abs_zero]; norm_num⟩
  haveI : Nonempty I := by
    obtain ⟨i, -⟩ := mem_iUnion.mp (hcov (l54Pt_mem_frontier u)); exact ⟨i⟩
  set f : I → ℕ∞ := fun i => lgdMinSet (dzzWall (legWallC u (1 / 20) (S i)) ν) δ {u} (S i)
    with hfdef
  suffices key : ∀ y ∈ F, ∀ N : ℕ, (∃ (c : Fin N → ℚ × ℚ) (ρ : Fin N → ℝ) (p : Path u y),
      (∀ j, 0 < ρ j ∧ dzzWall (sqBox u (1 / 10)) ν (ball (ratPt (c j)) (ρ j)) ≤
        ENNReal.ofReal (δ ^ 2)) ∧ ∀ t, ∃ j, p t ∈ ball (ratPt (c j)) (ρ j)) →
      ∃ i, f i ≤ N by
    have hle : iInf f ≤ lgdMinSet (dzzWall (sqBox u (1 / 10)) ν) δ {u} F := by
      refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
      rw [mem_singleton_iff.mp hx]
      unfold lgdDZZ
      refine le_iInf₂ fun N hN => ?_
      obtain ⟨i, hi⟩ := key y hy N hN
      exact (iInf_le f i).trans hi
    obtain ⟨i, hi⟩ := ciInf_mem f
    refine ⟨i, ?_⟩
    show f i ≤ _
    rw [hi]; exact hle
  intro y hy N ⟨c, ρ, p, h1, h2⟩
  set B : Fin N → Set ℂ := fun j => ball (ratPt (c j)) (ρ j) with hBdef
  have hBK : ∀ j, B j ⊆ sqBox u (1 / 10) := fun j => by
    by_contra h
    have := (h1 j).2
    rw [dzzWall_ball_of_not_subset (isClosed_sqBox u _) ν h] at this
    exact ENNReal.ofReal_ne_top (top_le_iff.mp this)
  have hBm : ∀ j, ν (B j) ≤ ENNReal.ofReal (δ ^ 2) := fun j => by
    have := (h1 j).2; rwa [dzzWall_ball_of_subset ν (hBK j)] at this
  have hρ : ∀ j, ρ j < 1 / 80 := fun j => by
    by_contra h; push_neg at h
    have h3 := hB (ratPt (c j)) (ρ j) h ((hBK j).trans (sqBox_tenth_subset_dzzV hu))
    have h4 : ENNReal.ofReal (δ ^ 2) ≤ ENNReal.ofReal (2 * δ ^ 2) :=
      ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg δ])
    exact absurd ((hBm j).trans h4) (not_le.mpr h3)
  set bad : Set (Fin N) := {j | (B j ∩ F).Nonempty} with hbaddef
  set V : Set ℂ := ⋃ j ∈ bad, B j with hVdef
  have hcovP : ∀ s ∈ Icc (0 : ℝ) 1, ∃ j, p.extend s ∈ B j := fun s hs => by
    obtain ⟨j, hj⟩ := h2 ⟨s, hs⟩
    exact ⟨j, by rw [Path.extend_apply p hs]; exact hj⟩
  have hFV : ∀ s ∈ Icc (0 : ℝ) 1, p.extend s ∈ F → p.extend s ∈ V := fun s hs hsF => by
    obtain ⟨j, hj⟩ := hcovP s hs
    exact mem_biUnion (show j ∈ bad from ⟨_, hj, hsF⟩) hj
  -- the first time `s₀` the path hits `closure V`
  set T : Set ℝ := Icc 0 1 ∩ p.extend ⁻¹' closure V with hTdef
  have hTc : IsClosed T := isClosed_Icc.inter (isClosed_closure.preimage p.continuous_extend)
  have h1T : (1 : ℝ) ∈ T := ⟨⟨zero_le_one, le_rfl⟩, subset_closure
    (hFV 1 ⟨zero_le_one, le_rfl⟩ (by rw [Path.extend_one]; exact hy))⟩
  have hTb : BddBelow T := ⟨0, fun s hs => hs.1.1⟩
  set s₀ := sInf T with hs₀def
  have hs₀T : s₀ ∈ T := hTc.csInf_mem ⟨1, h1T⟩ hTb
  have hs₀0 : 0 ≤ s₀ := hs₀T.1.1
  have hs₀1 : s₀ ≤ 1 := csInf_le hTb h1T
  have hbefore : ∀ s, 0 ≤ s → s < s₀ → p.extend s ∉ closure V := fun s hs hss hV =>
    absurd (csInf_le hTb ⟨⟨hs, hss.le.trans hs₀1⟩, hV⟩) (not_le.mpr hss)
  -- up to `s₀` the path stays in `𝕍_{u,λ}`
  have hinK : ∀ s, 0 ≤ s → s ≤ s₀ → p.extend s ∈ K₀ := fun s hs hss => by
    by_contra hsK
    have hpre : IsPreconnected (p.extend '' Icc 0 s) :=
      isPreconnected_Icc.image _ p.continuous_extend.continuousOn
    obtain ⟨z, ⟨s', hs', rfl⟩, hzF⟩ := exists_mem_frontier_of_isPreconnected hpre hK₀
      ⟨u, ⟨0, ⟨le_rfl, hs⟩, Path.extend_zero p⟩, huK⟩ ⟨p.extend s, ⟨s, ⟨hs, le_rfl⟩, rfl⟩, hsK⟩
    have hs'1 : s' ∈ Icc (0 : ℝ) 1 := ⟨hs'.1, hs'.2.trans (hss.trans hs₀1)⟩
    have : s₀ ≤ s' := csInf_le hTb ⟨hs'1, subset_closure (hFV s' hs'1 hzF)⟩
    have he : s' = s := le_antisymm hs'.2 (hss.trans this)
    rw [he] at hzF
    exact hsK (hFK hzF)
  -- balls not meeting `∂𝕍_{u,λ}` but meeting `𝕍_{u,λ}` lie in `𝕍_{u,λ}`
  have hgood : ∀ j, j ∉ bad → (B j ∩ K₀).Nonempty → B j ⊆ K₀ := fun j hj hm => by
    by_contra hns
    obtain ⟨z, hz, hzK⟩ := not_subset.mp hns
    exact hj (exists_mem_frontier_of_isPreconnected (convex_ball _ _).isPreconnected hK₀ hm
      ⟨z, hz, hzK⟩)
  have hs₀I : s₀ ∈ Icc (0 : ℝ) 1 := ⟨hs₀0, hs₀1⟩
  obtain ⟨k, hk⟩ := hcovP s₀ hs₀I
  have hpK : p.extend s₀ ∈ K₀ := hinK s₀ hs₀0 le_rfl
  -- a ball `B_b` meeting `∂𝕍_{u,λ}` and `B_k`
  obtain ⟨b, hb, hkb, hbk⟩ : ∃ b ∈ bad, (B k ∩ B b).Nonempty ∧ (k ∈ bad → b = k) := by
    by_cases hkbad : k ∈ bad
    · exact ⟨k, hkbad, ⟨_, hk, hk⟩, fun _ => rfl⟩
    · obtain ⟨z, hzk, hzV⟩ := mem_closure_iff.mp hs₀T.2 (B k) isOpen_ball hk
      obtain ⟨b, hb, hzb⟩ := mem_iUnion₂.mp hzV
      exact ⟨b, hb, ⟨z, hzk, hzb⟩, fun h => absurd h hkbad⟩
  obtain ⟨w, hwb, hwF⟩ := hb
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcov hwF)
  set W := legWallC u (1 / 20) (S i) with hWdef
  have hK₀W : K₀ ⊆ W := subset_union_left
  have hbW : B b ⊆ W := fun z hz => by
    refine Or.inr (mem_cthickening_of_dist_le z w _ _ hi ?_)
    have e1 : dist z (ratPt (c b)) < ρ b := hz
    have e2 : dist w (ratPt (c b)) < ρ b := hwb
    have := dist_triangle_right z w (ratPt (c b))
    have := hρ b
    linarith
  have hkW : B k ⊆ W := by
    by_cases hkbad : k ∈ bad
    · rw [← hbk hkbad]; exact hbW
    · exact (hgood k hkbad ⟨_, hk, hpK⟩).trans hK₀W
  have hpre : ∀ s, 0 ≤ s → s < s₀ → ∀ j, p.extend s ∈ B j → B j ⊆ W := fun s hs hss j hj => by
    have hjbad : j ∉ bad := fun hjb => hbefore s hs hss (subset_closure (mem_biUnion hjb hj))
    exact (hgood j hjbad ⟨_, hj, hinK s hs hss.le⟩).trans hK₀W
  -- the new path `u → p(s₀) → q → w`
  obtain ⟨q, hqk, hqb⟩ := hkb
  set Q₁ : Path u (p.extend s₀) := (p.truncateOfLE hs₀0).cast (by simp) rfl with hQ₁
  have hQval : ∀ s, ∃ r ∈ Icc (0 : ℝ) s₀, Q₁ s = p.extend r := fun s =>
    ⟨min (max (s : ℝ) 0) s₀, ⟨le_min (le_max_right _ _) hs₀0, min_le_right _ _⟩, rfl⟩
  have hJ₂ := ((convex_ball (ratPt (c k)) (ρ k)).isPathConnected ⟨_, hk⟩).joinedIn _ hk _ hqk
  have hJ₃ := ((convex_ball (ratPt (c b)) (ρ b)).isPathConnected ⟨_, hqb⟩).joinedIn _ hqb _ hwb
  set R : Path u w := Q₁.trans (hJ₂.somePath.trans hJ₃.somePath) with hR
  have hRcov : ∀ t, ∃ j, R t ∈ B j ∧ B j ⊆ W := fun t => by
    have hRt : R t ∈ range R := mem_range_self t
    rw [hR, Path.trans_range, Path.trans_range] at hRt
    rcases hRt with ⟨s, hs⟩ | ⟨s, hs⟩ | ⟨s, hs⟩
    · obtain ⟨r, hr, hQr⟩ := hQval s
      rw [← hs, hQr]
      rcases hr.2.lt_or_eq with h | h
      · obtain ⟨j, hj⟩ := hcovP r ⟨hr.1, hr.2.trans hs₀1⟩
        exact ⟨j, hj, hpre r hr.1 h j hj⟩
      · rw [h]; exact ⟨k, hk, hkW⟩
    · exact ⟨k, hs ▸ hJ₂.somePath_mem s, hkW⟩
    · exact ⟨b, hs ▸ hJ₃.somePath_mem s, hbW⟩
  -- the chain: the original balls, those leaving `W` replaced by `B_b`
  set j' : Fin N → Fin N := fun j => if B j ⊆ W then j else b with hj'
  have hj'W : ∀ j, B (j' j) ⊆ W := fun j => by
    by_cases h : B j ⊆ W
    · have e : j' j = j := by simp only [hj', if_pos h]
      rw [e]; exact h
    · have e : j' j = b := by simp only [hj', if_neg h]
      rw [e]; exact hbW
  have hD : lgdDZZ (dzzWall W ν) δ u w ≤ N := by
    refine iInf₂_le N ⟨fun j => c (j' j), fun j => ρ (j' j), R, fun j => ⟨(h1 (j' j)).1, ?_⟩, ?_⟩
    · show dzzWall W ν (B (j' j)) ≤ _
      rw [dzzWall_ball_of_subset ν (hj'W j)]; exact hBm (j' j)
    · intro t
      obtain ⟨j, hj, hjW⟩ := hRcov t
      refine ⟨j, ?_⟩
      have e : j' j = j := by simp only [hj', if_pos hjW]
      show R t ∈ B (j' j)
      rw [e]; exact hj
  exact ⟨i, (iInf₂_le_of_le u (mem_singleton u) (iInf₂_le w hi)).trans hD⟩

end DZZ
end LQGMetric
