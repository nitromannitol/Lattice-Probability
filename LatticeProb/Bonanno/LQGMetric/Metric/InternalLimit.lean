/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Metric.InternalLimit at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Metric.InternalOps
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Locally equal metrics have equal internal metrics (DFGPS Lemma 2.11, deterministic core)

* `curveLength_comp_eq_of_locally` : if `f : X → Z` preserves the distances between points of
  the curve `P` at nearby times, then `len(f ∘ P) = len(P)` (length is local: split `[a, b]`
  into pieces shorter than a Lebesgue number and use additivity).
* `internalEDist_eq_of_locally_eq` : if `e : Y₁ ≃ₜ Y₂` (subspaces of two pseudo-emetric spaces)
  preserves distances locally (each point of `Y₁` has a neighbourhood on which `e` is an
  isometry), then `e` preserves the internal metrics: `d₂(e x, e y; Y₂) = d₁(x, y; Y₁)`.

This is the last step of the proof of **DFGPS Lemma 2.11** (`lem-internal-conv`,
`lqg-metric-estimates-final.tex`:980–988): "the `D`-length of any path in `V` which lies at
positive Euclidean distance from `∂V` is the same as its `D̃`-length … we conclude that
`D(·,·;V) = D̃(·,·;V)`". (We need neither that `D, D̃` are length metrics nor the positive
distance to `∂V`: lengths of curves are local, BBI Prop. 2.3.4(i)–(ii).)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Set Filter Topology unitInterval Metric
open scoped ENNReal

namespace LQGMetric.MetricGeometry

variable {X : Type*} [PseudoEMetricSpace X] {Z : Type*} [PseudoEMetricSpace Z]

theorem eVariationOn_comp_eq_of_edist_eq {f : X → Z} {P : ℝ → X} {s : Set ℝ}
    (h : ∀ x ∈ s, ∀ y ∈ s, edist (f (P x)) (f (P y)) = edist (P x) (P y)) :
    eVariationOn (f ∘ P) s = eVariationOn P s := by
  unfold eVariationOn
  congr 1
  funext p
  exact Finset.sum_congr rfl fun i _ => h _ (p.2.2.2 _) _ (p.2.2.2 _)

/-- **Length is local.** If `f` preserves the distances `d(P s, P s')` for `s, s'` close to each
time `t ∈ [a, b]`, then `len(f ∘ P; [a, b]) = len(P; [a, b])`. -/
theorem curveLength_comp_eq_of_locally {f : X → Z} {P : ℝ → X} {a b : ℝ}
    (hloc : ∀ t ∈ Icc a b, ∃ ε > 0, ∀ s ∈ Icc a b, ∀ s' ∈ Icc a b, dist s t < ε →
      dist s' t < ε → edist (f (P s)) (f (P s')) = edist (P s) (P s')) :
    curveLength (f ∘ P) a b = curveLength P a b := by
  rcases lt_or_ge b a with hba | hab
  · rw [curveLength_of_ge _ hba.le, curveLength_of_ge _ hba.le]
  choose! ε hε hεloc using hloc
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric (c := fun t : Icc a b => ball (t : ℝ) (ε t))
    isCompact_Icc (fun _ => isOpen_ball) fun t ht => mem_iUnion.2 ⟨⟨t, ht⟩, mem_ball_self (hε t ht)⟩
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / δ)
  have hN0 : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg (sub_nonneg.2 hab) hδ.le) hN
  set h := (b - a) / N with hh
  have hh0 : 0 ≤ h := div_nonneg (sub_nonneg.2 hab) hN0.le
  have hhδ : h < δ := by
    rw [hh, div_lt_iff₀ hN0]
    rw [div_lt_iff₀ hδ] at hN
    linarith
  set u : ℕ → ℝ := fun i => min (a + i * h) b with hu
  have humono : Monotone u := fun i j hij =>
    min_le_min_right _ (add_le_add_right (mul_le_mul_of_nonneg_right (Nat.cast_le.2 hij) hh0) a)
  have hu0 : u 0 = a := by simp [hu, hab]
  have huN : u N = b := by
    simp only [hu, hh]
    rw [mul_div_cancel₀ _ hN0.ne']
    simp
  have humem : ∀ i, u i ∈ Icc a b := fun i =>
    ⟨le_min (le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg i) hh0)) hab, min_le_right _ _⟩
  have hpiece : ∀ i, curveLength (f ∘ P) (u i) (u (i + 1)) = curveLength P (u i) (u (i + 1)) := by
    intro i
    obtain ⟨⟨t, ht⟩, hball⟩ := hleb (u i) (humem i)
    have hsub : ∀ s ∈ Icc (u i) (u (i + 1)), s ∈ Icc a b ∧ dist s t < ε t := by
      intro s hs
      have hs' : s ∈ Icc a b := ⟨(humem i).1.trans hs.1, hs.2.trans (humem (i + 1)).2⟩
      refine ⟨hs', ?_⟩
      have hle : u (i + 1) ≤ u i + h := by
        simp only [hu]
        rcases le_total (a + i * h) b with h1 | h1
        · rw [min_eq_left h1]
          refine (min_le_left _ _).trans ?_
          push_cast
          linarith
        · rw [min_eq_right h1]
          exact (min_le_right _ _).trans (by linarith)
      have : s ∈ ball (u i) δ := by
        rw [mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith [hs.1, hs.2]
      exact hball this
    exact eVariationOn_comp_eq_of_edist_eq fun x hx y hy =>
      hεloc t ht x (hsub x hx).1 y (hsub y hy).1 (hsub x hx).2 (hsub y hy).2
  have h1 := sum_curveLength_eq (f ∘ P) humono N
  have h2 := sum_curveLength_eq P humono N
  rw [hu0, huN] at h1 h2
  rw [← h1, ← h2]
  exact Finset.sum_congr rfl fun i _ => hpiece i

/-! ### Transfer of internal metrics along a local isometry -/

section Transfer

variable {Y₁ : Set X} {Y₂ : Set Z}

/-- A path in `Y₁`, pushed through `e : Y₁ ≃ₜ Y₂`. -/
def pushPath (e : Y₁ ≃ₜ Y₂) {x y : X} (γ : Path x y) (hγ : ∀ t, γ t ∈ Y₁) :
    Path (e ⟨x, by simpa using hγ 0⟩ : Z) (e ⟨y, by simpa using hγ 1⟩ : Z) where
  toFun t := (e ⟨γ t, hγ t⟩ : Z)
  continuous_toFun := continuous_subtype_val.comp (e.continuous.comp (γ.continuous.subtype_mk _))
  source' := congrArg (fun p => (e p : Z)) (Subtype.ext γ.source)
  target' := congrArg (fun p => (e p : Z)) (Subtype.ext γ.target)

/-- `e` is a **local isometry**: each point has a neighbourhood on which `e` preserves distances. -/
def IsLocalIsometryOn (e : Y₁ ≃ₜ Y₂) : Prop :=
  ∀ z : Y₁, ∃ N ∈ 𝓝 z, ∀ u ∈ N, ∀ v ∈ N, edist (e u : Z) (e v) = edist (u : X) v

theorem IsLocalIsometryOn.symm {e : Y₁ ≃ₜ Y₂} (he : IsLocalIsometryOn e) :
    IsLocalIsometryOn e.symm := by
  intro z
  obtain ⟨N, hN, hNe⟩ := he (e.symm z)
  refine ⟨e.symm ⁻¹' N, e.symm.continuous.continuousAt.preimage_mem_nhds hN, fun u hu v hv => ?_⟩
  have := hNe _ hu _ hv
  rw [e.apply_symm_apply, e.apply_symm_apply] at this
  exact this.symm

theorem pathLength_pushPath {e : Y₁ ≃ₜ Y₂} (he : IsLocalIsometryOn e) {x y : X} (γ : Path x y)
    (hγ : ∀ t, γ t ∈ Y₁) : pathLength (pushPath e γ hγ) = pathLength γ := by
  let P' : ℝ → Y₁ := fun t => ⟨γ.extend t, hγ _⟩
  have hP' : Continuous P' := γ.continuous_extend.subtype_mk _
  change curveLength ((fun p : Y₁ => (e p : Z)) ∘ P') 0 1 = curveLength P' 0 1
  refine curveLength_comp_eq_of_locally fun t _ => ?_
  obtain ⟨N, hN, hNe⟩ := he (P' t)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hP'.continuousAt.preimage_mem_nhds hN)
  exact ⟨ε, hε, fun s _ s' _ hs hs' => hNe _ (hball hs) _ (hball hs')⟩

theorem internalEDist_le_of_isLocalIsometryOn {e : Y₁ ≃ₜ Y₂} (he : IsLocalIsometryOn e)
    (x y : Y₁) : internalEDist Y₂ (e x : Z) (e y) ≤ internalEDist Y₁ (x : X) y :=
  le_iInf fun γ => (internalEDist_le_pathLength (Y := Y₂)
    (pushPath e γ.1 γ.2 : Path (e x : Z) (e y)) fun _ => (e _).2).trans_eq
    (pathLength_pushPath he γ.1 γ.2)

/-- **Local isometries preserve internal metrics** (last step of DFGPS Lemma 2.11, tex:986–988):
if `e : Y₁ ≃ₜ Y₂` preserves distances near every point, then
`d₂(e x, e y; Y₂) = d₁(x, y; Y₁)`. -/
theorem internalEDist_eq_of_isLocalIsometryOn {e : Y₁ ≃ₜ Y₂} (he : IsLocalIsometryOn e)
    (x y : Y₁) : internalEDist Y₂ (e x : Z) (e y) = internalEDist Y₁ (x : X) y := by
  refine le_antisymm (internalEDist_le_of_isLocalIsometryOn he x y) ?_
  have := internalEDist_le_of_isLocalIsometryOn he.symm (e x) (e y)
  rwa [e.symm_apply_apply, e.symm_apply_apply] at this

end Transfer

end LQGMetric.MetricGeometry
