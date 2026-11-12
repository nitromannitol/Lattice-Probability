/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3L20 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L12
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L8
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L12Chain
import LatticeProb.Bonanno.LQGMetric.Dimension.LGDBasic

/-!
# DG Lemma 3.20 (`lem-annulus-lower`): deterministic part (P2-DG105h, D105 P9)

Ding–Gwynne, arXiv:1807.01072, `metric-comparison-final.tex`, Lemma 3.20 (DG:1625–1636):
"with probability tending to 1 as `ε → 0`, `D^ε_{ĥ^tr}(𝕊, ∂𝕊(1/2)) ≥ ε^{−1/(d_γ+ζ)}`"; proof
(DG:1633–1635): DZZ Proposition 3.17 + Lemma 6.1 for the zero-boundary GFF, and DG Lemma 3.2.

DG's distance is unrestricted (no domain), while `μ_{ĥ^tr}` (`muTr`) lives on the box of DG Lemma
3.1. The passage from DZZ's `min_{x ∈ ∂𝕍̄_{u,α}, y ∈ ∂𝕍̄_u} D_δ(x,y)` to DG's set distance is
deterministic given that the balls of small `μ_{ĥ^tr}`-mass meeting the outer box stay in a
neighbourhood (`l320_core`):
* `exists_cross_subpath`: a path from `z ∈ A` (closed) to `w ∉ V` (open, `A ⊆ V`) has a sub-path
  from `∂A` to `∂V` inside `closure V` (last exit from `A` before the first exit from `V`; the
  first-exit construction as in `DZZ.lgdMinSet_dzzWall_le_of_exit`);
* `lgdDZZ_le_of_path_cover`: a cover of a path by `N` arbitrary open balls gives a cover by `N`
  smaller balls with rational centres (compactness), so DG's `dgLGD` (any centres) dominates
  DZZ's `lgdDZZ` (rational centres);
* `l320_heavy`: a ball meeting `B̄(u, 1/20)` and leaving `B̄(u, 1/10)` contains a grid ball
  `B(w, g)` (`g ≤ 1/400`, `w ∈ gℤ²`, `|w − u| ≤ 1/16 + g`), so it is heavy when all such grid
  balls are (DG's scheme DG:1131–1137 for the probability of the latter).
Own elementary geometric glue.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DG

/-- **last exit from `A` before the first exit from `V`** -/
lemma exists_cross_subpath {z w : ℂ} (P : Path z w) {A V : Set ℂ} (hA : IsClosed A)
    (hV : IsOpen V) (hAV : A ⊆ V) (hz : z ∈ A) (hw : w ∉ V) :
    ∃ t₀ t₁ : ℝ, 0 ≤ t₀ ∧ t₀ ≤ t₁ ∧ t₁ ≤ 1 ∧ P.extend t₀ ∈ frontier A ∧
      P.extend t₁ ∈ frontier V ∧ ∀ r ∈ Icc t₀ t₁, P.extend r ∈ closure V := by
  -- first exit `t₁` from `V`
  set T : Set ℝ := Icc 0 1 ∩ (P.extend ⁻¹' Vᶜ) with hT
  have hTc : IsClosed T := isClosed_Icc.inter (hV.isClosed_compl.preimage P.continuous_extend)
  have h1T : (1 : ℝ) ∈ T := ⟨⟨zero_le_one, le_rfl⟩, by simpa using hw⟩
  have hTb : BddBelow T := ⟨0, fun s hs => hs.1.1⟩
  set t₁ := sInf T with ht₁
  have ht₁T : t₁ ∈ T := hTc.csInf_mem ⟨1, h1T⟩ hTb
  have ht₁1 : t₁ ≤ 1 := csInf_le hTb h1T
  have hbefore : ∀ s, 0 ≤ s → s < t₁ → P.extend s ∈ V := by
    intro s hs hss
    by_contra hsU
    exact absurd (csInf_le hTb ⟨⟨hs, hss.le.trans ht₁1⟩, hsU⟩) (not_le.mpr hss)
  have hpos : 0 < t₁ := by
    refine lt_of_le_of_ne ht₁T.1.1 fun h => ?_
    have := ht₁T.2
    rw [← h] at this
    simp only [mem_preimage, mem_compl_iff, Path.extend_zero] at this
    exact this (hAV hz)
  have hcl : P.extend t₁ ∈ closure V := by
    have ht : Tendsto P.extend (𝓝[<] t₁) (𝓝 (P.extend t₁)) :=
      (P.continuous_extend.tendsto t₁).mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsLT hpos] with s hs
    exact hbefore s hs.1.le hs.2
  have hfr1 : P.extend t₁ ∈ frontier V := by
    rw [hV.frontier_eq]; exact ⟨hcl, ht₁T.2⟩
  -- last visit `t₀ ≤ t₁` of `A`
  set S : Set ℝ := Icc 0 t₁ ∩ (P.extend ⁻¹' A) with hS
  have hSc : IsClosed S := isClosed_Icc.inter (hA.preimage P.continuous_extend)
  have h0S : (0 : ℝ) ∈ S := ⟨⟨le_rfl, hpos.le⟩, by simpa using hz⟩
  have hSb : BddAbove S := ⟨t₁, fun s hs => hs.1.2⟩
  set t₀ := sSup S with ht₀
  have ht₀S : t₀ ∈ S := hSc.csSup_mem ⟨0, h0S⟩ hSb
  have ht₀0 : 0 ≤ t₀ := le_csSup hSb h0S
  have ht₀1 : t₀ ≤ t₁ := ht₀S.1.2
  have ht₀lt : t₀ < t₁ := by
    refine lt_of_le_of_ne ht₀1 fun h => ?_
    have := ht₀S.2
    rw [h] at this
    exact ht₁T.2 (hAV this)
  have hafter : ∀ s, t₀ < s → s ≤ t₁ → P.extend s ∉ A := by
    intro s hs hst hsA
    exact absurd (le_csSup hSb ⟨⟨ht₀0.trans hs.le, hst⟩, hsA⟩) (not_le.mpr hs)
  have hfr0 : P.extend t₀ ∈ frontier A := by
    rw [frontier_eq_closure_inter_closure]
    refine ⟨subset_closure ht₀S.2, ?_⟩
    have ht : Tendsto P.extend (𝓝[>] t₀) (𝓝 (P.extend t₀)) :=
      (P.continuous_extend.tendsto t₀).mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto ht ?_
    filter_upwards [Ioo_mem_nhdsGT ht₀lt] with s hs
    exact hafter s hs.1 hs.2.le
  refine ⟨t₀, t₁, ht₀0, ht₀1, ht₁1, hfr0, hfr1, fun r hr => ?_⟩
  rcases hr.2.lt_or_eq with h | h
  · exact subset_closure (hbefore r (ht₀0.trans hr.1) h)
  · rw [h]; exact hcl

/-- **from any centres to rational centres**: a path covered by `N` open balls, those meeting it
of `ν`-mass `≤ δ²`, has `lgdDZZ ν δ ≤ N` -/
lemma lgdDZZ_le_of_path_cover {ν : Measure ℂ} {δ : ℝ} {x y : ℂ} (Q : Path x y) {N : ℕ}
    (c : Fin N → ℂ) (ρ : Fin N → ℝ) (hρ : ∀ i, 0 < ρ i)
    (hcov : ∀ s, ∃ i, Q s ∈ ball (c i) (ρ i))
    (hm : ∀ i, (∃ s, Q s ∈ ball (c i) (ρ i)) → ν (ball (c i) (ρ i)) ≤ ENNReal.ofReal (δ ^ 2)) :
    lgdDZZ ν δ x y ≤ N := by
  classical
  -- a uniform shrinking factor
  set U : ℕ → Set ℂ := fun n => ⋃ i, ball (c i) (ρ i * (1 - 1 / ((n : ℝ) + 2))) with hU
  have hmono : Monotone U := by
    intro n m hnm
    refine iUnion_mono fun i => ball_subset_ball ?_
    have : 1 / ((m : ℝ) + 2) ≤ 1 / ((n : ℝ) + 2) :=
      one_div_le_one_div_of_le (by positivity) (by exact_mod_cast (by omega : n + 2 ≤ m + 2))
    nlinarith [hρ i]
  obtain ⟨n, hn⟩ := (isCompact_range Q.continuous).elim_directed_cover U
    (fun n => isOpen_iUnion fun i => isOpen_ball) (by
      rintro _ ⟨s, rfl⟩
      obtain ⟨i, hi⟩ := hcov s
      have hd : 0 < 1 - dist (Q s) (c i) / ρ i := by
        rw [sub_pos, div_lt_one (hρ i)]; exact hi
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt hd
      refine mem_iUnion.2 ⟨n, mem_iUnion.2 ⟨i, ?_⟩⟩
      rw [mem_ball]
      have h2 : 1 / ((n : ℝ) + 2) ≤ 1 / ((n : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      have h3 : dist (Q s) (c i) / ρ i < 1 - 1 / ((n : ℝ) + 2) := by linarith
      rwa [div_lt_iff₀ (hρ i), mul_comm] at h3) hmono.directed_le
  set κ : ℝ := 1 / (2 * ((n : ℝ) + 2)) with hκ
  have hκ0 : 0 < κ := by positivity
  have hq : ∀ i, ∃ q : ℚ × ℚ, dist (ratPt q) (c i) < ρ i * κ := fun i =>
    exists_ratPt_dist_lt (c i) (mul_pos (hρ i) hκ0)
  choose q hq using hq
  set ρ' : Fin N → ℝ := fun i => ρ i * (1 - κ) with hρ'
  have hκ1 : κ < 1 / 2 := by
    rw [hκ, one_div_lt_one_div (by positivity) (by norm_num)]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hρ'0 : ∀ i, 0 < ρ' i := fun i => mul_pos (hρ i) (by linarith)
  have hsub : ∀ i, ball (ratPt (q i)) (ρ' i) ⊆ ball (c i) (ρ i) := by
    intro i
    refine ball_subset_ball' ?_
    have := hq i
    simp only [hρ']; nlinarith [hρ i]
  have hcov' : ∀ s, ∃ i, Q s ∈ ball (ratPt (q i)) (ρ' i) := by
    intro s
    obtain ⟨i, hi⟩ := mem_iUnion.1 (hn (mem_range_self s))
    refine ⟨i, ?_⟩
    rw [mem_ball] at hi ⊢
    have e : 1 / ((n : ℝ) + 2) = 2 * κ := by rw [hκ]; field_simp
    rw [e] at hi
    calc dist (Q s) (ratPt (q i)) ≤ dist (Q s) (c i) + dist (c i) (ratPt (q i)) :=
          dist_triangle _ _ _
      _ < ρ i * (1 - 2 * κ) + ρ i * κ := by rw [dist_comm (c i)]; exact add_lt_add hi (hq i)
      _ = ρ' i := by simp only [hρ']; ring
  -- keep the balls meeting `Q`
  obtain ⟨i₀, hi₀⟩ := hcov' 0
  set I : Set (Fin N) := {i | ∃ s, Q s ∈ ball (ratPt (q i)) (ρ' i)} with hI
  set j : Fin N → Fin N := fun i => if i ∈ I then i else i₀ with hj
  have hjI : ∀ i, j i ∈ I := by
    intro i
    by_cases h : i ∈ I
    · have e : j i = i := by simp [hj, h]
      rw [e]; exact h
    · have e : j i = i₀ := by simp [hj, h]
      rw [e]; exact ⟨0, hi₀⟩
  unfold lgdDZZ
  refine iInf₂_le N ⟨fun i => q (j i), fun i => ρ' (j i), Q, fun i => ⟨hρ'0 _, ?_⟩, ?_⟩
  · obtain ⟨s, hs⟩ := hjI i
    exact (measure_mono (hsub (j i))).trans (hm (j i) ⟨s, hsub (j i) hs⟩)
  · intro s
    obtain ⟨i, hi⟩ := hcov' s
    have hiI : i ∈ I := ⟨s, hi⟩
    refine ⟨i, ?_⟩
    have e : j i = i := by simp [hj, hiI]
    show Q s ∈ ball (ratPt (q (j i))) (ρ' (j i))
    rw [e]; exact hi

/-- **heavy balls** (`g ≤ 1/400`): a ball meeting `B̄(u, 1/20)` and not contained in
`B̄(u, 1/10)` contains a grid ball `B(w, g)`, `w ∈ gℤ²`, `|w − u| ≤ 1/16 + g` -/
lemma l320_heavy {μ : Measure ℂ} {u : ℂ} {g t : ℝ} (hg : 0 < g) (hg' : g ≤ 1 / 400)
    (hgrid : ∀ i j : ℤ, ‖(⟨i * g, j * g⟩ : ℂ) - u‖ ≤ (1 / 16 - 2 * g) + 3 * g →
      ENNReal.ofReal t < μ (ball ⟨i * g, j * g⟩ g))
    {x : ℂ} {ρ : ℝ} {p : ℂ} (hp : p ∈ ball x ρ) (hpu : ‖p - u‖ ≤ 1 / 20)
    (hnot : ¬ ball x ρ ⊆ closedBall u (1 / 10)) : ENNReal.ofReal t < μ (ball x ρ) := by
  obtain ⟨q, hq, hqu⟩ := not_subset.1 hnot
  rw [mem_closedBall, not_le, dist_eq_norm] at hqu
  rw [mem_ball, dist_eq_norm] at hp hq
  have hpq : 1 / 20 < ‖q - p‖ := by
    have := norm_sub_le_norm_sub_add_norm_sub q p u
    have e : ‖p - u‖ = ‖u - p‖ := norm_sub_rev _ _
    linarith [norm_sub_le (q - u) (p - u), (by abel : q - u - (p - u) = q - p)]
  have hρ : 1 / 40 < ρ := by
    have := norm_sub_le_norm_sub_add_norm_sub q x p
    rw [norm_sub_rev x p] at this
    linarith
  -- a point `p'` with `B(p', 1/80) ⊆ B(x, ρ)` and `|p' − p| ≤ 1/80`
  obtain ⟨p', hp'1, hp'2⟩ : ∃ p' : ℂ, ball p' (1 / 80) ⊆ ball x ρ ∧ ‖p' - p‖ ≤ 1 / 80 := by
    by_cases hd : ‖x - p‖ ≤ 1 / 80
    · exact ⟨x, ball_subset_ball (by linarith), hd⟩
    · replace hd := not_le.1 hd
      have hdρ : ‖x - p‖ < ρ := by rw [norm_sub_rev]; exact hp
      set d := ‖x - p‖
      have hd0 : 0 < d := by linarith
      refine ⟨p + ((1 / 80 / d : ℝ) : ℂ) * (x - p), ball_subset_ball' ?_, ?_⟩
      · rw [dist_eq_norm]
        have e : p + ((1 / 80 / d : ℝ) : ℂ) * (x - p) - x = ((1 - 1 / 80 / d : ℝ) : ℂ) * (p - x) := by
          push_cast; ring
        rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_sub_rev p x,
          abs_of_nonneg (by rw [sub_nonneg, div_le_one hd0]; linarith)]
        have : (1 - 1 / 80 / d) * d = d - 1 / 80 := by field_simp
        rw [this]; linarith
      · rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (by positivity)]
        rw [div_mul_cancel₀ _ hd0.ne']
  obtain ⟨i, j, hij⟩ := DZZ.exists_grid_near p' hg
  have hball : ball (⟨i * g, j * g⟩ : ℂ) g ⊆ ball x ρ := by
    refine (ball_subset_ball' ?_).trans hp'1
    rw [dist_eq_norm]; linarith
  have hwu : ‖(⟨i * g, j * g⟩ : ℂ) - u‖ ≤ (1 / 16 - 2 * g) + 3 * g := by
    have h1 := norm_sub_le_norm_sub_add_norm_sub (⟨i * g, j * g⟩ : ℂ) p' u
    have h2 := norm_sub_le_norm_sub_add_norm_sub p' p u
    linarith
  exact (hgrid i j hwu).trans_le (measure_mono hball)

lemma isClosed_l312Box (c : ℂ) (l : ℝ) : IsClosed (l312Box c l) := by
  show IsClosed ({z : ℂ | |z.re - c.re| ≤ l / 2} ∩ {z : ℂ | |z.im - c.im| ≤ l / 2})
  exact (isClosed_le (by fun_prop) continuous_const).inter
    (isClosed_le (by fun_prop) continuous_const)

/-- **DZZ's boundary-to-boundary distance bounds DG's set distance** (DG:1633–1635): if every
ball meeting the outer box `𝕍̄_u` with `μ_T`-mass `≤ ε` has `ν`-mass `≤ δ²`, then for `z` in the
inner box `𝕍̄_{u,α}` and `w ∈ ∂𝕍̄_u`,
`min_{x ∈ ∂𝕍̄_{u,α}, y ∈ ∂𝕍̄_u} D_δ(ν)(x,y) ≤ D^ε_{μ_T}(z, w)` (unrestricted). -/
lemma l320_core {μT ν : Measure ℂ} {u z w : ℂ} {α ε δ : ℝ} (hα : α < 1)
    (hz : z ∈ l312Box u (α / 20)) (hw : w ∈ frontier (l312Box u (1 / 20)))
    (hheavy : ∀ x ρ, (∃ p ∈ ball x ρ, p ∈ l312Box u (1 / 20)) →
      μT (ball x ρ) ≤ ENNReal.ofReal ε → ν (ball x ρ) ≤ ENNReal.ofReal (δ ^ 2)) :
    DZZ.lgdMinSet ν δ (frontier (l312Box u (α / 20))) (frontier (l312Box u (1 / 20))) ≤
      dgLGD μT ε univ z w := by
  have hOc := isClosed_l312Box u (1 / 20)
  have hAO : l312Box u (α / 20) ⊆ interior (l312Box u (1 / 20)) := by
    have hopen : IsOpen {z : ℂ | |z.re - u.re| < 1 / 20 / 2 ∧ |z.im - u.im| < 1 / 20 / 2} := by
      show IsOpen ({z : ℂ | |z.re - u.re| < 1 / 20 / 2} ∩ {z : ℂ | |z.im - u.im| < 1 / 20 / 2})
      exact (isOpen_lt (by fun_prop) continuous_const).inter
        (isOpen_lt (by fun_prop) continuous_const)
    refine subset_trans ?_ (interior_maximal (fun z hz => ⟨hz.1.le, hz.2.le⟩) hopen)
    intro z hz
    have h : α / 20 / 2 < 1 / 20 / 2 := by linarith
    exact ⟨hz.1.trans_lt h, hz.2.trans_lt h⟩
  unfold DZZ.lgdMinSet dgLGD
  refine le_iInf₂ fun N hN => ?_
  obtain ⟨c, ρ, P, h1, h2⟩ := hN
  obtain ⟨t₀, t₁, h0, h01, h11, hf0, hf1, hin⟩ :=
    exists_cross_subpath P (isClosed_l312Box u (α / 20)) isOpen_interior hAO hz hw.2
  set Q := P.truncateOfLE h01 with hQ
  have hQval : ∀ s, ∃ r ∈ Icc t₀ t₁, Q s = P.extend r := fun s =>
    ⟨min (max (s : ℝ) t₀) t₁, ⟨le_min (le_max_right _ _) h01, min_le_right _ _⟩, rfl⟩
  have hQO : ∀ s, Q s ∈ l312Box u (1 / 20) := fun s => by
    obtain ⟨r, hr, e⟩ := hQval s
    rw [e]; exact closure_minimal interior_subset hOc (hin r hr)
  have hcov : ∀ s, ∃ i, Q s ∈ ball (c i) (ρ i) := by
    intro s
    obtain ⟨r, hr, e⟩ := hQval s
    obtain ⟨i, hi⟩ := h2 ⟨r, h0.trans hr.1, hr.2.trans h11⟩
    refine ⟨i, ?_⟩
    rw [e, Path.extend_apply P ⟨h0.trans hr.1, hr.2.trans h11⟩]
    exact hi
  have hD := lgdDZZ_le_of_path_cover Q c ρ (fun i => (h1 i).1) hcov
    (fun i ⟨s, hs⟩ => hheavy _ _ ⟨Q s, hs, hQO s⟩ (h1 i).2.2)
  exact (iInf₂_le _ hf0).trans ((iInf₂_le _ (frontier_interior_subset hf1)).trans hD)

end DG
end LQGMetric
