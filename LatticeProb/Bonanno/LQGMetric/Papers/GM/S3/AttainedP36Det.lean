/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S3.AttainedP36Det at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.AttainedTele
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.AttainedSub
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.DefsLemmas

/-!
# GM Prop 3.6, Steps 2–3 for one pair of points (task P2-M2F2, WP-M2f, row 8 of `blueprint/M2.md`)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
proof of Proposition 3.6, l. 1440–1488.

`p36_pair`: deterministic form of GM's Steps 2–3 for one pair `𝕫, 𝕨` with a unique
`D_h`-geodesic `η`: if every point of `B_ρ(0)` (containing the range of `η`) lies in `B_{r/2}(w)`
for a good ball (`r ∈ [r_min, ε𝕣]`, `𝖤_r(w)` occurs), and `D_h(x,y) ≤ ω` for `x, y ∈ B_ρ(0)` with
`|x − y| ≤ 4ε𝕣`, then `D̃_h(𝕫,𝕨) ≤ (C' + A/(A+1)(C_* − C')) D_h(𝕫,𝕨) + 3C_*ω`.

We parametrize `η` by `D_h`-length (`P(τ) = η(τ/D_h(𝕫,𝕨))`), take `a₀` = last time
`|P − 𝕫| ≤ 2ε𝕣` and `b₀` = first time after `a₀` with `|P − 𝕨| ≤ 2ε𝕣` (GM's `J̲`, `J̄`, (3.15)),
and apply `tele_core` (GM (3.17)) on `[a₀, b₀]`; the comparison input (3.14) comes from condition 1
of `𝖤_r(w)` and GM.S3.7 (`gm_S3_7`), the shortcut input from condition 3. The three end pieces
(`𝕫 → P(a₀)`, the last incomplete step, `P(b₀) → 𝕨`) each cost `≤ C_*ω` (GM (3.18)).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- the closed annulus lies in the closure of the open annulus -/
lemma mem_closure_annulus_of {w x : ℂ} {r₁ r₂ : ℝ} (h0 : 0 < r₁) (h12 : r₁ < r₂)
    (h1 : r₁ ≤ ‖x - w‖) (h2 : ‖x - w‖ ≤ r₂) : x ∈ closure (annulus w r₁ r₂ : Set ℂ) := by
  set ρ := ‖x - w‖ with hρ
  have hρ0 : 0 < ρ := h0.trans_le h1
  set m := (r₁ + r₂) / 2 with hm
  let f : ℝ → ℂ := fun t => w + (((ρ + t * (m - ρ)) / ρ : ℝ) : ℂ) * (x - w)
  have hf : Continuous f := by fun_prop
  have hf0 : f 0 = x := by
    simp only [f, zero_mul, add_zero, div_self hρ0.ne', Complex.ofReal_one, one_mul]; ring
  refine mem_closure_of_tendsto (f := f) (b := 𝓝[>] (0 : ℝ)) ?_ ?_
  · rw [← hf0]; exact hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 from one_pos)] with t ht
    have hpos : 0 < ρ + t * (m - ρ) := by nlinarith [ht.1, ht.2]
    have hn : ‖f t - w‖ = ρ + t * (m - ρ) := by
      simp only [f, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (div_pos hpos hρ0)]
      rw [← hρ, div_mul_cancel₀ _ hρ0.ne']
    show r₁ < ‖f t - w‖ ∧ ‖f t - w‖ < r₂
    rw [hn]
    constructor <;> nlinarith [ht.1, ht.2]

/-- a lower bound on the open interval extends to the closed one -/
lemma le_on_Icc_of_Ioo {g : ℝ → ℝ} {a b c : ℝ} (hab : a < b) (hg : ContinuousOn g (Icc a b))
    (h : ∀ t ∈ Ioo a b, c ≤ g t) : ∀ t ∈ Icc a b, c ≤ g t := by
  have hS : IsClosed (Icc a b ∩ g ⁻¹' Ici c) :=
    hg.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hsub := closure_minimal (s := Ioo a b) (t := Icc a b ∩ g ⁻¹' Ici c)
    (fun t ht => ⟨Ioo_subset_Icc_self ht, h t ht⟩) hS
  rw [closure_Ioo hab.ne] at hsub
  exact fun t ht => (hsub ht).2

/-- **GM Prop 3.6, Steps 2–3** (l. 1440–1488) for one pair `𝕫, 𝕨` with a unique geodesic. -/
theorem p36_pair {D D' : DistC → ContMetric} {g : DistC}
    (hex : ∀ a b : ℂ, ∃ η, (D g).IsGeod01 a b η)
    {α A Cs C' : ℝ} (hα : 1 / 2 < α) (hα1 : α < 1) (hA : 0 ≤ A) (hC0 : 0 ≤ C')
    (hCC : C' ≤ Cs) (hratio : ∀ x y, (D' g).1 (x, y) ≤ Cs * (D g).1 (x, y))
    {z w : ℂ} (hu : UniqueGeod (D g) z w) {ρ e rmin ω : ℝ} (hrmin : 0 < rmin)
    (hzw : 4 * e < ‖z - w‖)
    (hconf : ∀ η, IsGeod01 (D g) z w η → range η ⊆ ball 0 ρ)
    (hcov : ∀ x ∈ ball (0 : ℂ) ρ, ∃ v r, (rmin ≤ r ∧ r ≤ e ∧ g ∈ goodAnnulus D D' α A C' r v) ∧
      x ∈ ball v (r / 2))
    (hmod : ∀ x ∈ ball (0 : ℂ) ρ, ∀ y ∈ ball (0 : ℂ) ρ, ‖x - y‖ ≤ 4 * e → (D g).1 (x, y) ≤ ω) :
    (D' g).1 (z, w) ≤ (C' + A / (A + 1) * (Cs - C')) * (D g).1 (z, w) + 3 * Cs * ω := by
  set Dg := D g
  set D'g := D' g
  obtain ⟨η, hη, huη⟩ := hu
  have hu' : Dg.GeodUnique z w := fun a b ha hb => (huη a ha).trans (huη b hb).symm
  have hzw0 : z ≠ w := by
    intro h; rw [h, sub_self, norm_zero] at hzw
    have : 0 ≤ e := by
      by_contra hn; push Not at hn
      obtain ⟨v, r, ⟨h1, h2, -⟩, -⟩ := hcov z (hconf η hη ⟨0, hη.1⟩)
      linarith
    linarith
  set L := Dg.1 (z, w) with hL
  have hL0 : 0 < L := dist_pos_of_ne Dg hzw0
  set P : ℝ → ℂ := fun τ => η (pj (τ / L)) with hPdef
  have hP : ContinuousOn P (Icc 0 L) :=
    (η.continuous.comp (continuous_projIcc.comp (continuous_id.div_const L))).continuousOn
  have hpj : ∀ τ ∈ Icc 0 L, ((pj (τ / L) : unitInterval) : ℝ) = τ / L := fun τ hτ =>
    pj_coe_of_mem ⟨div_nonneg hτ.1 hL0.le, (div_le_one hL0).2 hτ.2⟩
  have hgeo : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, Dg.1 (P s, P t) = |t - s| := by
    intro s hs t ht
    show Dg.1 (η (pj (s / L)), η (pj (t / L))) = _
    rw [hη.2.2, hpj s hs, hpj t ht, ← hL, ← sub_div, abs_div, abs_of_pos hL0,
      div_mul_cancel₀ _ hL0.ne']
  have hP0 : P 0 = z := by
    show η (pj (0 / L)) = z
    rw [zero_div, pj_eq_of_mem ⟨le_rfl, zero_le_one⟩]; exact hη.1
  have hPL : P L = w := by
    show η (pj (L / L)) = w
    rw [div_self hL0.ne', pj_eq_of_mem ⟨zero_le_one, le_rfl⟩]; exact hη.2.1
  have hPin : ∀ τ, P τ ∈ ball (0 : ℂ) ρ := fun τ => hconf η hη ⟨_, rfl⟩
  have he0 : 0 ≤ e := by
    obtain ⟨v, r, ⟨h1, h2, -⟩, -⟩ := hcov z (hP0 ▸ hPin 0)
    linarith
  have hω : 0 ≤ ω := by
    have := hmod z (hP0 ▸ hPin 0) z (hP0 ▸ hPin 0) (by rw [sub_self, norm_zero]; linarith)
    rwa [Dg.2.self_eq_zero] at this
  -- `a₀`: the last time with `|P − 𝕫| ≤ 2e`
  set S₁ := Icc 0 L ∩ P ⁻¹' closedBall z (2 * e) with hS₁
  have hS₁c : IsClosed S₁ := hP.preimage_isClosed_of_isClosed isClosed_Icc isClosed_closedBall
  have h0S₁ : (0 : ℝ) ∈ S₁ := ⟨⟨le_rfl, hL0.le⟩, by
    show P 0 ∈ closedBall z (2 * e); rw [hP0]; exact mem_closedBall_self (by linarith)⟩
  have hS₁b : BddAbove S₁ := ⟨L, fun t ht => ht.1.2⟩
  set a₀ := sSup S₁ with ha₀
  have ha₀S : a₀ ∈ S₁ := hS₁c.csSup_mem ⟨0, h0S₁⟩ hS₁b
  have ha₀0 : 0 ≤ a₀ := ha₀S.1.1
  have hafter₁ : ∀ t ∈ Ioc a₀ L, 2 * e < ‖P t - z‖ := by
    intro t ht
    by_contra hn; push Not at hn
    exact absurd (le_csSup hS₁b ⟨⟨by linarith [ht.1], ht.2⟩, by
      rw [mem_preimage, mem_closedBall, dist_eq_norm]; exact hn⟩) (not_le.2 ht.1)
  have hPa₀z : ‖P a₀ - z‖ ≤ 2 * e := by
    have := ha₀S.2; rwa [mem_preimage, mem_closedBall, dist_eq_norm] at this
  have hPa₀w : 2 * e < ‖P a₀ - w‖ := by
    have := norm_sub_norm_le (z - w) (P a₀ - w)
    rw [sub_sub_sub_cancel_right] at this
    rw [norm_sub_rev z (P a₀)] at this
    linarith
  have ha₀L : a₀ < L := by
    rcases eq_or_lt_of_le ha₀S.1.2 with h | h
    · rw [h, hPL] at hPa₀w; rw [sub_self, norm_zero] at hPa₀w; linarith
    · exact h
  -- `b₀`: the first time after `a₀` with `|P − 𝕨| ≤ 2e`
  set S₂ := Icc a₀ L ∩ P ⁻¹' closedBall w (2 * e) with hS₂
  have hS₂c : IsClosed S₂ := (hP.mono (Icc_subset_Icc ha₀0 le_rfl)).preimage_isClosed_of_isClosed
    isClosed_Icc isClosed_closedBall
  have hLS₂ : L ∈ S₂ := ⟨⟨ha₀L.le, le_rfl⟩, by
    show P L ∈ closedBall w (2 * e); rw [hPL]; exact mem_closedBall_self (by linarith)⟩
  have hS₂b : BddBelow S₂ := ⟨a₀, fun t ht => ht.1.1⟩
  set b₀ := sInf S₂ with hb₀
  have hb₀S : b₀ ∈ S₂ := hS₂c.csInf_mem ⟨L, hLS₂⟩ hS₂b
  have hb₀L : b₀ ≤ L := hb₀S.1.2
  have hPb₀w : ‖P b₀ - w‖ ≤ 2 * e := by
    have := hb₀S.2; rwa [mem_preimage, mem_closedBall, dist_eq_norm] at this
  have hab : a₀ < b₀ := by
    rcases eq_or_lt_of_le hb₀S.1.1 with h | h
    · rw [← h] at hPb₀w; linarith
    · exact h
  have hbefore₂ : ∀ t ∈ Ico a₀ b₀, 2 * e < ‖P t - w‖ := by
    intro t ht
    by_contra hn; push Not at hn
    exact absurd (csInf_le hS₂b ⟨⟨ht.1, by linarith [ht.2]⟩, by
      rw [mem_preimage, mem_closedBall, dist_eq_norm]; exact hn⟩) (not_le.2 ht.2)
  have hfz : ∀ a ∈ Icc a₀ b₀, 2 * e ≤ ‖P a - z‖ :=
    le_on_Icc_of_Ioo (g := fun t => ‖P t - z‖) hab
      ((hP.mono (Icc_subset_Icc ha₀0 hb₀L)).sub continuousOn_const).norm
      (fun t ht => (hafter₁ t ⟨ht.1, by linarith [ht.2]⟩).le)
  have hfw : ∀ a ∈ Icc a₀ b₀, 2 * e ≤ ‖P a - w‖ :=
    le_on_Icc_of_Ioo (g := fun t => ‖P t - w‖) hab
      ((hP.mono (Icc_subset_Icc ha₀0 hb₀L)).sub continuousOn_const).norm
      (fun t ht => (hbefore₂ t ⟨ht.1.le, ht.2⟩).le)
  -- the good balls
  set Good : ℂ → ℝ → Prop := fun v r => rmin ≤ r ∧ r ≤ e ∧ g ∈ goodAnnulus D D' α A C' r v
  have hfar1 : ∀ x : ℂ, ∀ a ∈ Icc a₀ b₀, ∀ v r, Good v r → P a ∈ ball v (r / 2) →
      2 * e ≤ ‖P a - x‖ → x ∉ ball v r := by
    intro x a _ v r hg hPa hx hxv
    rw [mem_ball, dist_eq_norm] at hPa hxv
    have := norm_add_le (P a - v) (v - x)
    rw [sub_add_sub_cancel] at this
    rw [norm_sub_rev v x] at this
    linarith [hg.2.1]
  have hcomp : ∀ v r, Good v r → ∀ s t, 0 ≤ s → s ≤ t → t ≤ L → P s ∈ sphere v (α * r) →
      P t ∈ sphere v r → (∀ u ∈ Icc s t, P u ∈ closedBall v r ∧ P u ∉ ball v (α * r)) →
      D'g.1 (P s, P t) ≤ C' * (t - s) := by
    intro v r hg s t hs hst htL hPs hPt hann
    have hr : 0 < r := hrmin.trans_le hg.1
    have hsI : s ∈ Icc 0 L := ⟨hs, hst.trans htL⟩
    have htI : t ∈ Icc 0 L := ⟨hs.trans hst, htL⟩
    have hle : pj (s / L) ≤ pj (t / L) :=
      monotone_projIcc _ (div_le_div_of_nonneg_right hst hL0.le)
    obtain ⟨hU, hR⟩ := gm_S3_7 hex hη hu' hle
    have hUG : UniqueGeodIn Dg (P s) (P t) (closure (annulus v (α * r) r : Set ℂ)) := by
      refine ⟨hU, fun γ hγ => (hR γ hγ).trans ?_⟩
      rintro _ ⟨x, ⟨hx1, hx2⟩, rfl⟩
      have hx1' : s / L ≤ (x : ℝ) := by rw [← hpj s hsI]; exact hx1
      have hx2' : (x : ℝ) ≤ t / L := by rw [← hpj t htI]; exact hx2
      have hu : (x : ℝ) * L ∈ Icc s t := by
        constructor
        · rwa [div_le_iff₀ hL0] at hx1'
        · rwa [le_div_iff₀ hL0] at hx2'
      have hxe : η x = P ((x : ℝ) * L) := by
        show η x = η (pj ((x : ℝ) * L / L))
        rw [mul_div_cancel_right₀ _ hL0.ne', pj_eq_of_mem x.2]
      obtain ⟨h1, h2⟩ := hann _ hu
      rw [hxe]
      rw [mem_closedBall, dist_eq_norm] at h1
      rw [mem_ball, dist_eq_norm, not_lt] at h2
      exact mem_closure_annulus_of (by nlinarith) (by nlinarith) h2 h1
    have := hg.2.2.1.1 (P s) hPs (P t) hPt hUG
    rwa [hgeo s hsI t htI, abs_of_nonneg (sub_nonneg.2 hst)] at this
  have hK := tele_core Dg D'g hP hgeo hα hα1 hA hC0 hCC hratio Good hrmin (fun v r hg => hg.1)
    (fun v r hg => by
      obtain ⟨a', b', G, -, -, -, hd, hl⟩ := hg.2.2.2
      exact ⟨a', b', G, hd, hl⟩)
    hcomp ha₀0 hab.le hb₀L hω
    (fun a _ => hcov (P a) (hPin a))
    (fun a ha v r hg hPa => ⟨by rw [hP0]; exact hfar1 z a ha v r hg hPa (hfz a ha),
      by rw [hPL]; exact hfar1 w a ha v r hg hPa (hfw a ha)⟩)
    (fun a ha v r hg hPa hPb => by
      have h1 := hgeo a ⟨ha₀0.trans ha.1, ha.2.trans hb₀L⟩ b₀ ⟨ha₀0.trans hab.le, hb₀L⟩
      rw [abs_of_nonneg (by linarith [ha.2])] at h1
      rw [← h1]
      refine hmod _ (hPin a) _ (hPin b₀) ?_
      rw [mem_ball, dist_eq_norm] at hPa hPb
      have := norm_add_le (P a - v) (v - P b₀)
      rw [sub_add_sub_cancel, norm_sub_rev v] at this
      linarith [hg.2.1])
  -- the two end pieces
  have hend1 : D'g.1 (z, P a₀) ≤ Cs * ω := by
    refine (hratio _ _).trans (mul_le_mul_of_nonneg_left ?_ (hC0.trans hCC))
    refine hmod _ (hP0 ▸ hPin 0) _ (hPin a₀) ?_
    rw [norm_sub_rev]; linarith
  have hend2 : D'g.1 (P b₀, w) ≤ Cs * ω := by
    refine (hratio _ _).trans (mul_le_mul_of_nonneg_left ?_ (hC0.trans hCC))
    refine hmod _ (hPin b₀) _ (hPL ▸ hPin L) ?_
    linarith
  have hKpos : 0 ≤ C' + A / (A + 1) * (Cs - C') := by
    have : 0 ≤ A / (A + 1) := div_nonneg hA (by linarith)
    nlinarith
  have hbl : b₀ - a₀ ≤ L := by linarith
  have t1 := D'g.2.triangle z (P a₀) w
  have t2 := D'g.2.triangle (P a₀) (P b₀) w
  nlinarith [mul_le_mul_of_nonneg_left hbl hKpos]

end LQGMetric.GM
