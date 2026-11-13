/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMSMain.T13Path at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.Lemma33

/-!
# Bounded convexity and the regularity of the test function of [18] Theorem 1.3

Source: [18] Theorem 1.3 : `f` is continuously differentiable on `D`,
`∇f` is Lipschitz continuous, and `D` has **bounded convexity**: there is `C = C(D) > 0` such that any two points
`z, w ∈ D` can be joined by a path in `D` of Euclidean length at most `C|z − w|`. The boundary data (1.6) evaluate
`f` on `∂D`, so `f` is continuous on `D̄` (`[18]`: "let `f : D → ℂ` be a continuous function"). The proof uses:
"`f` extends Lipschitz to `D̄`, by bounded convexity".

* `BoundedConvexity D` — the path condition, with the length of a path `p : [0, 1] → D` its total variation
  `eVariationOn p (Icc 0 1)`;
* `t13_eVariationOn_comp_le` — `Var(f ∘ p) ≤ G · Var(p)` for a continuous path in an open set where `‖∇f‖ ≤ G`
  (local Lipschitz bounds on small balls, glued along a uniform subdivision);
* `t13_abs_sub_le_of_boundedConvexity` — `|f z − f w| ≤ G C⁺ |z − w|` on `D`;
* `t13_abs_sub_le_closure` — the same Lipschitz bound on `D̄` for `f` continuous on `D̄`;
* `t13_exists_fderiv_nnnorm_le` — a Lipschitz gradient on a bounded set is bounded;
* `t13_fderiv_eq_zero_of_eucEnergy_eq_zero` — `Energy(f; D) = 0` forces `∇f = 0` on `D` (continuous gradient).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.GMSMain

open MatedCRTHarmonic

/-- **`C`-bounded convexity** ([18] Section 3.2, condition 2 of `𝒞_C`, `[18]`): any two points `z, w ∈ D`
are joined by a continuous path in `D` of length at most `C |z − w|`. -/
def BoundedConvexityWith (C : ℝ) (D : Set ℂ) : Prop :=
  ∀ z ∈ D, ∀ w ∈ D, ∃ p : ℝ → ℂ, ContinuousOn p (Icc 0 1) ∧ p 0 = z ∧ p 1 = w ∧
    MapsTo p (Icc 0 1) D ∧ eVariationOn p (Icc 0 1) ≤ ENNReal.ofReal (C * dist z w)

/-- **The variation of `f ∘ p` along a path in an open set where `‖∇f‖ ≤ G`** is at most `G` times the length of
the path. -/
theorem t13_eVariationOn_comp_le {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℝ} (hf : DifferentiableOn ℝ f U)
    {G : ℝ≥0} (hG : ∀ z ∈ U, ‖fderiv ℝ f z‖₊ ≤ G) {p : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hp : ContinuousOn p (Icc a b)) (hpU : MapsTo p (Icc a b) U) :
    eVariationOn (f ∘ p) (Icc a b) ≤ G * eVariationOn p (Icc a b) := by
  have hK : IsCompact (p '' Icc a b) := isCompact_Icc.image_of_continuousOn hp
  obtain ⟨δ, hδ, hthick⟩ := hK.exists_thickening_subset_open hU (image_subset_iff.2 hpU)
  have hUC := isCompact_Icc.uniformContinuousOn_of_continuous hp
  obtain ⟨η, hη, hUCη⟩ := Metric.uniformContinuousOn_iff.1 hUC δ hδ
  -- the local claim on short subintervals
  have hloc : ∀ s t : ℝ, a ≤ s → s ≤ t → t ≤ b → t - s < η →
      eVariationOn (f ∘ p) (Icc s t) ≤ G * eVariationOn p (Icc s t) := by
    intro s t has hst htb hη'
    have hs : s ∈ Icc a b := ⟨has, hst.trans htb⟩
    have hball : ball (p s) δ ⊆ U := by
      refine (ball_subset_thickening ?_ δ).trans hthick
      exact mem_image_of_mem p hs
    have hlip : LipschitzOnWith G f (ball (p s) δ) :=
      Convex.lipschitzOnWith_of_nnnorm_fderiv_le
        (fun z hz => hf.differentiableAt (hU.mem_nhds (hball hz)))
        (fun z hz => hG z (hball hz)) (convex_ball _ _)
    have hmaps : MapsTo p (Icc s t) (ball (p s) δ) := by
      intro u hu
      have hu' : u ∈ Icc a b := ⟨has.trans hu.1, hu.2.trans htb⟩
      rw [mem_ball]
      refine hUCη u hu' s hs ?_
      rw [Real.dist_eq, abs_of_nonneg (by linarith [hu.1])]
      linarith [hu.2]
    exact hlip.comp_eVariationOn_le hmaps
  -- a uniform subdivision
  obtain ⟨N, hN⟩ := exists_nat_gt ((b - a) / η)
  have hNpos : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg (by linarith) hη.le) hN
  set h : ℝ := (b - a) / N with hhdef
  have hh0 : 0 ≤ h := div_nonneg (by linarith) hNpos.le
  have hhη : h < η := by
    rw [hhdef, div_lt_iff₀ hNpos]
    rw [div_lt_iff₀ hη] at hN
    linarith
  have hNh : a + N * h = b := by rw [hhdef]; field_simp; ring
  have hind : ∀ i : ℕ, i ≤ N →
      eVariationOn (f ∘ p) (Icc a (a + i * h)) ≤ G * eVariationOn p (Icc a (a + i * h)) := by
    intro i
    induction i with
    | zero =>
      intro _
      simp only [CharP.cast_eq_zero, zero_mul, add_zero, Icc_self]
      rw [eVariationOn.subsingleton _ subsingleton_singleton]
      exact bot_le
    | succ i ih =>
      intro hi
      have hi' : (i : ℝ) + 1 ≤ N := by exact_mod_cast hi
      have h1 : a ≤ a + i * h := by have : (0 : ℝ) ≤ i * h := by positivity
                                    linarith
      have h2 : a + i * h ≤ a + (i + 1 : ℕ) * h := by push_cast; nlinarith
      have h3 : a + (i + 1 : ℕ) * h ≤ b := by
        rw [← hNh]; push_cast; nlinarith
      have hfadd := eVariationOn.Icc_add_Icc (f ∘ p) (s := univ) h1 h2 (mem_univ _)
      have hpadd := eVariationOn.Icc_add_Icc p (s := univ) h1 h2 (mem_univ _)
      simp only [univ_inter] at hfadd hpadd
      rw [← hfadd, ← hpadd, mul_add]
      refine add_le_add (ih (by omega)) (hloc _ _ h1 h2 h3 ?_)
      push_cast
      linarith
  have := hind N le_rfl
  rwa [hNh] at this

/-- **Mean value inequality along a rectifiable path**: `|f (p b) − f (p a)| ≤ G · length(p)`. -/
theorem t13_abs_sub_le_of_path {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℝ} (hf : DifferentiableOn ℝ f U)
    {G : ℝ≥0} (hG : ∀ z ∈ U, ‖fderiv ℝ f z‖₊ ≤ G) {p : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hp : ContinuousOn p (Icc a b)) (hpU : MapsTo p (Icc a b) U) {ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hlen : eVariationOn p (Icc a b) ≤ ENNReal.ofReal ℓ) :
    |f (p b) - f (p a)| ≤ G * ℓ := by
  have h1 := eVariationOn.edist_le (f ∘ p) (left_mem_Icc.2 hab) (right_mem_Icc.2 hab)
  have h2 : eVariationOn (f ∘ p) (Icc a b) ≤ (G : ℝ≥0∞) * ENNReal.ofReal ℓ :=
    (t13_eVariationOn_comp_le hU hf hG hab hp hpU).trans (by gcongr)
  have h3 := h1.trans h2
  rw [edist_dist, Real.dist_eq, Function.comp_apply, Function.comp_apply, abs_sub_comm,
    ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)] at h3
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3

end MatedCRTHarmonic.GMSMain
