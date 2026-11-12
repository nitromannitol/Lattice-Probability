/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DG.S3P9Top at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L13V
import LatticeProb.Bonanno.LQGMetric.Papers.DG.S3L11Det
import LatticeProb.Bonanno.LQGMetric.Topo.SectorRect
import Mathlib.Topology.Subpath

/-!
# DG Proposition 3.9: crossing paths and their ball counts (P2-DG105j)

Deterministic tools for the proof of DG Proposition 3.9 (Ding–Gwynne, arXiv:1807.01072,
`metric-comparison-final.tex`, DG:1346–1360): a path `P_R` realizing
`D^ε(∂_L R, ∂_R R; R') ≤ M` (resp. `∂_B`, `∂_T`) gives `D^ε(u, v; Q) ≤ M` for all `u, v` on it
(subpaths), and a left–right crossing of a horizontal strip meets a bottom–top crossing of a
vertical strip (DG:1352–1356, "`X_S` is connected", "`X_{S̃} ∩ X_S ≠ ∅`"), from the continuum
crossing lemma `Sector.lr_tb_meet` applied to sub-arcs inside the common rectangle (the sub-arc
extraction is an own elementary argument via the intermediate value theorem).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal unitInterval

namespace LQGMetric
namespace DG

/-- a sub-interval `[s₁, s₂] ⊆ [0,1]` on which `f` runs from `a` to `a'` inside `[a, a']` -/
lemma p39_sub_Icc {f : ℝ → ℝ} (hf : Continuous f) {a a' : ℝ} (h0 : f 0 ≤ a) (haa : a ≤ a')
    (h1 : a' ≤ f 1) : ∃ s₁ s₂ : ℝ, 0 ≤ s₁ ∧ s₁ ≤ s₂ ∧ s₂ ≤ 1 ∧ f s₁ = a ∧ f s₂ = a' ∧
      ∀ t ∈ Icc s₁ s₂, f t ∈ Icc a a' := by
  set T := {t ∈ Icc (0 : ℝ) 1 | f t = a'} with hT
  have hTc : IsClosed T := isClosed_Icc.inter (isClosed_eq hf continuous_const)
  have hTne : T.Nonempty := by
    obtain ⟨t, ht, e⟩ := intermediate_value_Icc (zero_le_one' ℝ) hf.continuousOn
      ⟨h0.trans haa, h1⟩
    exact ⟨t, ht, e⟩
  have hTb : BddBelow T := ⟨0, fun t ht => ht.1.1⟩
  set s₂ := sInf T
  have hs₂ : s₂ ∈ T := hTc.csInf_mem hTne hTb
  -- `f ≤ a'` on `[0, s₂]`
  have hle : ∀ t ∈ Icc 0 s₂, f t ≤ a' := by
    intro t ht
    by_contra hlt
    push Not at hlt
    obtain ⟨u, hu, e⟩ := intermediate_value_Icc ht.1 hf.continuousOn ⟨h0.trans haa, hlt.le⟩
    have : s₂ ≤ u := csInf_le hTb ⟨⟨hu.1, hu.2.trans (ht.2.trans hs₂.1.2)⟩, e⟩
    have hut : u = t := le_antisymm hu.2 (ht.2.trans this)
    rw [hut] at e
    exact absurd e hlt.ne'
  set S := {t ∈ Icc (0 : ℝ) s₂ | f t = a} with hS
  have hSc : IsClosed S := isClosed_Icc.inter (isClosed_eq hf continuous_const)
  have hSne : S.Nonempty := by
    obtain ⟨t, ht, e⟩ := intermediate_value_Icc hs₂.1.1 hf.continuousOn
      ⟨h0, haa.trans_eq hs₂.2.symm⟩
    exact ⟨t, ht, e⟩
  have hSb : BddAbove S := ⟨s₂, fun t ht => ht.1.2⟩
  set s₁ := sSup S
  have hs₁ : s₁ ∈ S := hSc.csSup_mem hSne hSb
  refine ⟨s₁, s₂, hs₁.1.1, hs₁.1.2, hs₂.1.2, hs₁.2, hs₂.2, fun t ht => ⟨?_, ?_⟩⟩
  · by_contra hlt
    push Not at hlt
    obtain ⟨u, hu, e⟩ := intermediate_value_Icc ht.2 hf.continuousOn
      ⟨hlt.le, haa.trans_eq hs₂.2.symm⟩
    have : u ≤ s₁ := le_csSup hSb ⟨⟨hs₁.1.1.trans (ht.1.trans hu.1), hu.2⟩, e⟩
    have hut : u = t := le_antisymm (this.trans ht.1) hu.1
    rw [hut] at e
    exact absurd e hlt.ne
  · exact hle t ⟨hs₁.1.1.trans ht.1, ht.2⟩

/-- **Crossing of strips** (DG:1352–1356): a path in the horizontal strip `ℝ × [y₀, y₁]` from
`re ≤ a` to `re ≥ a'` meets a path in the vertical strip `[a, a'] × ℝ` from `im ≤ y₀` to
`im ≥ y₁`. -/
theorem p39_cross {z w z' w' : ℂ} (γ : Path z w) (η : Path z' w') {a a' y₀ y₁ : ℝ}
    (haa : a ≤ a') (hyy : y₀ ≤ y₁) (hz : z.re ≤ a) (hw : a' ≤ w.re)
    (hγ : ∀ t, (γ t).im ∈ Icc y₀ y₁) (hz' : z'.im ≤ y₀) (hw' : y₁ ≤ w'.im)
    (hη : ∀ t, (η t).re ∈ Icc a a') : (range γ ∩ range η).Nonempty := by
  have hγe : ∀ t, (γ.extend t).im ∈ Icc y₀ y₁ := fun t => by
    obtain ⟨s, hs⟩ : γ.extend t ∈ range γ := by rw [← Path.extend_range]; exact ⟨t, rfl⟩
    rw [← hs]; exact hγ s
  have hηe : ∀ t, (η.extend t).re ∈ Icc a a' := fun t => by
    obtain ⟨s, hs⟩ : η.extend t ∈ range η := by rw [← Path.extend_range]; exact ⟨t, rfl⟩
    rw [← hs]; exact hη s
  obtain ⟨s₁, s₂, -, hs12, -, e1, e2, hs⟩ := p39_sub_Icc
    (Complex.continuous_re.comp γ.continuous_extend) (f := fun t => (γ.extend t).re)
    (by simpa using hz) haa (by simpa using hw)
  obtain ⟨t₁, t₂, -, ht12, -, f1, f2, ht⟩ := p39_sub_Icc
    (Complex.continuous_im.comp η.continuous_extend) (f := fun t => (η.extend t).im)
    (by simpa using hz') hyy (by simpa using hw')
  obtain ⟨p, hpL, hpM⟩ := Sector.lr_tb_meet haa hyy
    (L := γ.extend '' Icc s₁ s₂) (M := η.extend '' Icc t₁ t₂)
    (isCompact_Icc.image γ.continuous_extend)
    (isPreconnected_Icc.image _ γ.continuous_extend.continuousOn)
    (by rintro _ ⟨t, htt, rfl⟩; exact ⟨hs t htt, hγe t⟩)
    ⟨_, ⟨s₁, left_mem_Icc.2 hs12, rfl⟩, e1⟩ ⟨_, ⟨s₂, right_mem_Icc.2 hs12, rfl⟩, e2⟩
    (isCompact_Icc.image η.continuous_extend)
    (isPreconnected_Icc.image _ η.continuous_extend.continuousOn)
    (by rintro _ ⟨t, htt, rfl⟩; exact ⟨hηe t, ht t htt⟩)
    ⟨_, ⟨t₂, right_mem_Icc.2 ht12, rfl⟩, f2⟩ ⟨_, ⟨t₁, left_mem_Icc.2 ht12, rfl⟩, f1⟩
  obtain ⟨u, -, rfl⟩ := hpL
  refine ⟨γ.extend u, ?_, ?_⟩
  · rw [← Path.extend_range]; exact ⟨u, rfl⟩
  · obtain ⟨v, -, hv⟩ := hpM
    rw [← hv, ← Path.extend_range]; exact ⟨v, rfl⟩

variable {μ : Measure ℂ} {ε : ℝ}

/-- triangle inequality for `D^ε(·,·;U)` -/
lemma p39_tri {U : Set ℂ} (z x w : ℂ) :
    (dgLGD μ ε U z w : ℝ≥0∞) ≤ (dgLGD μ ε U z x : ℝ≥0∞) + dgLGD μ ε U x w := by
  by_cases h1 : dgLGD μ ε U z x = ⊤
  · rw [h1]; simp
  by_cases h2 : dgLGD μ ε U x w = ⊤
  · rw [h2]; simp
  obtain ⟨N₁, hw₁, e₁⟩ := exists_wit_of_dgLGD_ne_top h1
  obtain ⟨N₂, hw₂, e₂⟩ := exists_wit_of_dgLGD_ne_top h2
  rw [e₁, e₂]
  have := dgLGD_le_of_wit (hw₁.trans hw₂)
  calc (dgLGD μ ε U z w : ℝ≥0∞) ≤ ((N₁ + N₂ : ℕ) : ℕ∞) := ENat.toENNReal_le.2 this
    _ = _ := by push_cast; rfl

/-- symmetry of `D^ε(·,·;U)` (reverse the path) -/
lemma p39_symm {U : Set ℂ} (z w : ℂ) : dgLGD μ ε U w z ≤ dgLGD μ ε U z w := by
  unfold dgLGD
  refine le_iInf₂ fun N hN => ?_
  obtain ⟨x, ρ, P, hb, hc⟩ := hN
  exact iInf₂_le N ⟨x, ρ, P.symm, hb, fun t => by
    obtain ⟨i, hi⟩ := hc (unitInterval.symm t); exact ⟨i, by rw [Path.symm_apply]; exact hi⟩⟩

/-- one admissible ball joins any two of its points -/
lemma p39_ball {U : Set ℂ} {x : ℂ} {r : ℝ} (hr : 0 < r) (hB : Metric.ball x r ⊆ closure U)
    (hm : μ (Metric.ball x r) ≤ ENNReal.ofReal ε) {u v : ℂ} (hu : u ∈ Metric.ball x r)
    (hv : v ∈ Metric.ball x r) : (dgLGD μ ε U u v : ℝ≥0∞) ≤ 1 := by
  have hj := (convex_ball x r).isPathConnected ⟨x, Metric.mem_ball_self hr⟩ |>.joinedIn u hu v hv
  have hw : LGDWit μ ε U u v 1 :=
    ⟨fun _ => x, fun _ => r, hj.somePath, fun _ => ⟨hr, hB, hm⟩,
      fun t => ⟨0, hj.somePath_mem t⟩⟩
  have := dgLGD_le_of_wit hw
  exact (ENat.toENNReal_le.2 this).trans_eq (by simp)

/-- **a horizontal crossing**: a path `γ` from `re ≤ x₀` to `re ≥ x₁` in the strip
`im ∈ [y₀, y₁]`, any two points of which are at `D^ε(·,·;U)`-distance `≤ M` -/
def P39H (μ : Measure ℂ) (ε : ℝ) (U : Set ℂ) (M x₀ x₁ y₀ y₁ : ℝ) (K : Set ℂ) : Prop :=
  ∃ (z w : ℂ) (γ : Path z w), range γ = K ∧ z.re ≤ x₀ ∧ x₁ ≤ w.re ∧
    (∀ t, (γ t).im ∈ Icc y₀ y₁) ∧ ∀ p ∈ K, ∀ q ∈ K, (dgLGD μ ε U p q : ℝ≥0∞) ≤ ENNReal.ofReal M

/-- **a vertical crossing**: a path from `im ≤ y₀` to `im ≥ y₁` in the strip `re ∈ [x₀, x₁]` -/
def P39V (μ : Measure ℂ) (ε : ℝ) (U : Set ℂ) (M x₀ x₁ y₀ y₁ : ℝ) (K : Set ℂ) : Prop :=
  ∃ (z w : ℂ) (γ : Path z w), range γ = K ∧ z.im ≤ y₀ ∧ y₁ ≤ w.im ∧
    (∀ t, (γ t).re ∈ Icc x₀ x₁) ∧ ∀ p ∈ K, ∀ q ∈ K, (dgLGD μ ε U p q : ℝ≥0∞) ≤ ENNReal.ofReal M

variable {U : Set ℂ} {M x₀ x₁ y₀ y₁ : ℝ} {K K' : Set ℂ}

lemma P39H.dist (h : P39H μ ε U M x₀ x₁ y₀ y₁ K) {p q : ℂ} (hp : p ∈ K) (hq : q ∈ K) :
    (dgLGD μ ε U p q : ℝ≥0∞) ≤ ENNReal.ofReal M := by
  obtain ⟨-, -, -, -, -, -, -, h⟩ := h; exact h p hp q hq

lemma P39V.dist (h : P39V μ ε U M x₀ x₁ y₀ y₁ K) {p q : ℂ} (hp : p ∈ K) (hq : q ∈ K) :
    (dgLGD μ ε U p q : ℝ≥0∞) ≤ ENNReal.ofReal M := by
  obtain ⟨-, -, -, -, -, -, -, h⟩ := h; exact h p hp q hq

lemma P39H.im_mem (h : P39H μ ε U M x₀ x₁ y₀ y₁ K) {p : ℂ} (hp : p ∈ K) : p.im ∈ Icc y₀ y₁ := by
  obtain ⟨z₀, w₀, γ, hK, -, -, hγ, -⟩ := h
  rw [← hK] at hp
  obtain ⟨t, rfl⟩ := hp; exact hγ t

lemma P39V.re_mem (h : P39V μ ε U M x₀ x₁ y₀ y₁ K) {p : ℂ} (hp : p ∈ K) : p.re ∈ Icc x₀ x₁ := by
  obtain ⟨z₀, w₀, γ, hK, -, -, hγ, -⟩ := h
  rw [← hK] at hp
  obtain ⟨t, rfl⟩ := hp; exact hγ t

/-- a horizontal crossing meets a vertical crossing whose strip lies inside its crossing range
and which crosses its strip -/
theorem P39H.meet {M' x₀' x₁' y₀' y₁' : ℝ} (hH : P39H μ ε U M x₀ x₁ y₀ y₁ K)
    (hV : P39V μ ε U M' x₀' x₁' y₀' y₁' K') (h1 : x₀ ≤ x₀') (h2 : x₀' ≤ x₁') (h3 : x₁' ≤ x₁)
    (h4 : y₀' ≤ y₀) (h5 : y₀ ≤ y₁) (h6 : y₁ ≤ y₁') : (K ∩ K').Nonempty := by
  obtain ⟨z, w, γ, rfl, hz, hw, hγ, -⟩ := hH
  obtain ⟨z', w', η, rfl, hz', hw', hη, -⟩ := hV
  exact p39_cross γ η h2 h5 (hz.trans h1) (h3.trans hw) hγ (hz'.trans h4) (h6.trans hw')
    (fun t => ⟨(hη t).1, (hη t).2⟩)

/-- the witness path of `D^ε(A, B; R') ≤ M` (`R'` closed, `R' ⊆ Q`): every two of its points
are at `D^ε(·,·;Q)`-distance `≤ M` -/
lemma p39_path_of_set {Q R A B : Set ℂ} (hR : IsClosed R) (hRQ : R ⊆ Q) {M : ℝ}
    (h : (l313Set μ ε R A B : ℝ≥0∞) ≤ ENNReal.ofReal M) :
    ∃ z ∈ A, ∃ w ∈ B, ∃ γ : Path z w, (∀ t, γ t ∈ R) ∧
      ∀ p ∈ range γ, ∀ q ∈ range γ, (dgLGD μ ε Q p q : ℝ≥0∞) ≤ ENNReal.ofReal M := by
  have hne : l313Set μ ε R A B ≠ ⊤ := by
    intro e; rw [e, ENat.toENNReal_top] at h; exact ENNReal.ofReal_ne_top (top_le_iff.1 h)
  have hlt : l313Set μ ε R A B < l313Set μ ε R A B + 1 := ENat.lt_add_one_iff hne |>.2 le_rfl
  obtain ⟨z, hlt'⟩ := iInf_lt_iff.1 hlt
  obtain ⟨hz, hlt''⟩ := iInf_lt_iff.1 hlt'
  obtain ⟨w, hlt3⟩ := iInf_lt_iff.1 hlt''
  obtain ⟨hw, hlt4⟩ := iInf_lt_iff.1 hlt3
  have hle : dgLGD μ ε R z w ≤ l313Set μ ε R A B := (ENat.lt_add_one_iff hne).1 hlt4
  have hne' : dgLGD μ ε R z w ≠ ⊤ := ne_top_of_le_ne_top hne hle
  obtain ⟨N, ⟨x, ρ, γ, hb, hc⟩, e⟩ := exists_wit_of_dgLGD_ne_top hne'
  have hRc : closure R = R := hR.closure_eq
  refine ⟨z, hz, w, hw, γ, fun t => ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hc t
    exact hRc ▸ (hb i).2.1 hi
  · rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
    have hw' : LGDWit μ ε Q (γ s) (γ t) N := by
      refine ⟨x, ρ, γ.subpath s t, fun i => ⟨(hb i).1, (hb i).2.1.trans
        (hRc.symm ▸ hRQ.trans subset_closure), (hb i).2.2⟩, fun u => ?_⟩
      have : (γ.subpath s t) u ∈ range γ := by
        have h' : (γ.subpath s t) u ∈ range (γ.subpath s t) := ⟨u, rfl⟩
        rw [Path.range_subpath] at h'
        obtain ⟨v, -, hv⟩ := h'
        exact ⟨v, hv⟩
      obtain ⟨v, hv⟩ := this
      obtain ⟨i, hi⟩ := hc v
      exact ⟨i, hv ▸ hi⟩
    calc (dgLGD μ ε Q (γ s) (γ t) : ℝ≥0∞) ≤ (N : ℕ∞) := ENat.toENNReal_le.2 (dgLGD_le_of_wit hw')
      _ = (dgLGD μ ε R z w : ℝ≥0∞) := by rw [e]
      _ ≤ l313Set μ ε R A B := ENat.toENNReal_le.2 hle
      _ ≤ _ := h

end DG
end LQGMetric
