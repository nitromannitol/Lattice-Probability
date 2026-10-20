/-
Adapted from Leonardo Bonanno’s formalizations:
https://github.com/leobon12/lean-formalizations
Source: LQGMetric/Metric/InternalLimit.lean.
-/
import LatticeProb.Topology.Length.InternalOps
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Local isometries preserve curve lengths and internal metrics

Let `X` and `Z` be pseudo-emetric spaces, `Y₁ : Set X`, `Y₂ : Set Z`, and `e : Y₁ ≃ₜ Y₂` a
homeomorphism. The map `e` is a local isometry (`IsLocalIsometryOn e`) if every point of `Y₁`
has a neighbourhood in `Y₁` on which `e` preserves edist. This file proves the following.

* `curveLength_comp_eq_of_locally`: if `f : X → Z` preserves the distances between the points of
  a curve `P` at nearby times, then `f ∘ P` has the same length as `P` on `[a, b]`. The proof
  splits `[a, b]` into finitely many pieces, each short enough for the hypothesis to apply on it,
  and uses additivity of the length over these pieces.
* `pathLength_pushPath`: pushing a path in `Y₁` through a local isometry `e` preserves its length.
* `internalEDist_eq_of_isLocalIsometryOn`: a local isometry preserves internal metrics, that is,
  `internalEDist Y₂ (e x) (e y) = internalEDist Y₁ x y`.

The identity map of the open interval `(0, 1)` in `ℝ` is a local isometry; the namespace
`LatticeProb.MetricGeometry.InternalLimitExample` applies the theorem to it.
-/

open Set Filter Topology unitInterval Metric
open scoped ENNReal

namespace LatticeProb.MetricGeometry

variable {X : Type*} [PseudoEMetricSpace X] {Z : Type*} [PseudoEMetricSpace Z]

/-- If `f` preserves the distances between the points of `P` on `s`, then the variation of
`f ∘ P` on `s` equals the variation of `P` on `s`. -/
theorem eVariationOn_comp_eq_of_edist_eq {f : X → Z} {P : ℝ → X} {s : Set ℝ}
    (h : ∀ x ∈ s, ∀ y ∈ s, edist (f (P x)) (f (P y)) = edist (P x) (P y)) :
    eVariationOn (f ∘ P) s = eVariationOn P s := by
  unfold eVariationOn
  congr 1
  funext p
  exact Finset.sum_congr rfl fun i _ => h _ (p.2.2.2 _) _ (p.2.2.2 _)

/-- **Length is local.** If, for every `t ∈ [a, b]`, the map `f` preserves the distances
`edist (P s) (P s')` for all `s, s' ∈ [a, b]` close to `t`, then `f ∘ P` and `P` have the same
length on `[a, b]`. -/
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

/-- Pushing a path `γ` from `x` to `y` in `X`, whose image lies in `Y₁`, through a homeomorphism
`e : Y₁ ≃ₜ Y₂` gives the path `e ∘ γ` from `e x` to `e y` in `Z`. -/
def pushPath (e : Y₁ ≃ₜ Y₂) {x y : X} (γ : Path x y) (hγ : ∀ t, γ t ∈ Y₁) :
    Path (e ⟨x, by simpa using hγ 0⟩ : Z) (e ⟨y, by simpa using hγ 1⟩ : Z) where
  toFun t := (e ⟨γ t, hγ t⟩ : Z)
  continuous_toFun := continuous_subtype_val.comp (e.continuous.comp (γ.continuous.subtype_mk _))
  source' := congrArg (fun p => (e p : Z)) (Subtype.ext γ.source)
  target' := congrArg (fun p => (e p : Z)) (Subtype.ext γ.target)

/-- A homeomorphism `e : Y₁ ≃ₜ Y₂` between subsets of pseudo-emetric spaces is a **local
isometry** if every point `z` of `Y₁` has a neighbourhood `N` in `Y₁` such that
`edist (e u) (e v) = edist u v` for all `u, v ∈ N`. -/
def IsLocalIsometryOn (e : Y₁ ≃ₜ Y₂) : Prop :=
  ∀ z : Y₁, ∃ N ∈ 𝓝 z, ∀ u ∈ N, ∀ v ∈ N, edist (e u : Z) (e v) = edist (u : X) v

/-- The inverse of a local isometry is a local isometry. -/
theorem IsLocalIsometryOn.symm {e : Y₁ ≃ₜ Y₂} (he : IsLocalIsometryOn e) :
    IsLocalIsometryOn e.symm := by
  intro z
  obtain ⟨N, hN, hNe⟩ := he (e.symm z)
  refine ⟨e.symm ⁻¹' N, e.symm.continuous.continuousAt.preimage_mem_nhds hN, fun u hu v hv => ?_⟩
  have := hNe _ hu _ hv
  rw [e.apply_symm_apply, e.apply_symm_apply] at this
  exact this.symm

/-- A local isometry preserves the length of every path in `Y₁`: the pushed path
`pushPath e γ hγ` has the same length as `γ`. -/
theorem pathLength_pushPath {e : Y₁ ≃ₜ Y₂} (he : IsLocalIsometryOn e) {x y : X} (γ : Path x y)
    (hγ : ∀ t, γ t ∈ Y₁) : pathLength (pushPath e γ hγ) = pathLength γ := by
  let P' : ℝ → Y₁ := fun t => ⟨γ.extend t, hγ _⟩
  have hP' : Continuous P' := γ.continuous_extend.subtype_mk _
  change curveLength ((fun p : Y₁ => (e p : Z)) ∘ P') 0 1 = curveLength P' 0 1
  refine curveLength_comp_eq_of_locally fun t _ => ?_
  obtain ⟨N, hN, hNe⟩ := he (P' t)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (hP'.continuousAt.preimage_mem_nhds hN)
  exact ⟨ε, hε, fun s _ s' _ hs hs' => hNe _ (hball hs) _ (hball hs')⟩

/-- Internal distances can only decrease under a local isometry: the internal distance in `Y₂`
between the images of `x` and `y` is at most the internal distance in `Y₁` between `x` and `y`. -/
theorem internalEDist_le_of_isLocalIsometryOn {e : Y₁ ≃ₜ Y₂} (he : IsLocalIsometryOn e)
    (x y : Y₁) : internalEDist Y₂ (e x : Z) (e y) ≤ internalEDist Y₁ (x : X) y :=
  le_iInf fun γ => (internalEDist_le_pathLength (Y := Y₂)
    (pushPath e γ.1 γ.2 : Path (e x : Z) (e y)) fun _ => (e _).2).trans_eq
    (pathLength_pushPath he γ.1 γ.2)

/-- **Local isometries preserve internal metrics.** If `e : Y₁ ≃ₜ Y₂` is a local isometry, then
for all `x y : Y₁`, `internalEDist Y₂ (e x) (e y) = internalEDist Y₁ x y`. -/
theorem internalEDist_eq_of_isLocalIsometryOn {e : Y₁ ≃ₜ Y₂} (he : IsLocalIsometryOn e)
    (x y : Y₁) : internalEDist Y₂ (e x : Z) (e y) = internalEDist Y₁ (x : X) y := by
  refine le_antisymm (internalEDist_le_of_isLocalIsometryOn he x y) ?_
  have := internalEDist_le_of_isLocalIsometryOn he.symm (e x) (e y)
  rwa [e.symm_apply_apply, e.symm_apply_apply] at this

end Transfer

namespace InternalLimitExample

/-- The identity homeomorphism of the open interval `(0, 1)` in `ℝ` is a local isometry: every
point has the neighbourhood `univ` on which the identity preserves edist. -/
theorem isLocalIsometryOn_refl : IsLocalIsometryOn (Homeomorph.refl (Ioo (0 : ℝ) 1)) := by
  intro z
  exact ⟨univ, univ_mem, fun _ _ _ _ => rfl⟩

/-- Applying `internalEDist_eq_of_isLocalIsometryOn` to the identity of `(0, 1)`: the internal
distance in `(0, 1)` is unchanged by the identity map. -/
theorem internalEDist_refl_eq (x y : Ioo (0 : ℝ) 1) :
    internalEDist (Ioo (0 : ℝ) 1) ((Homeomorph.refl (Ioo (0 : ℝ) 1) x : Ioo (0 : ℝ) 1) : ℝ)
      ((Homeomorph.refl (Ioo (0 : ℝ) 1) y : Ioo (0 : ℝ) 1) : ℝ) =
      internalEDist (Ioo (0 : ℝ) 1) (x : ℝ) (y : ℝ) :=
  internalEDist_eq_of_isLocalIsometryOn isLocalIsometryOn_refl x y

end InternalLimitExample

end LatticeProb.MetricGeometry
