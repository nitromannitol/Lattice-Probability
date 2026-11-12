/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.LQGCoord.WPCirc at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTPort.Foundations.ConeArea6C
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaExistenceTRL
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.AreaExistence

/-!
# Whole-plane circle averages: covariances, laws, independence, and the two-radius hypotheses

For a whole-plane GFF `X` (LQGMetric `IsWholePlaneGFF`, any additive constant) the
circle-average increments `cInc X r z s w = X_r(z) − X_s(w)` are jointly centred Gaussian with
covariance `incCov` (LQGMetric `map_cInc`, `covariance_cInc`, `isGaussianProcess_incProc`;
Duplantier–Sheffield arXiv:0808.1560 §3.1). This file records the explicit covariances used by
the area estimates (`circCov z a w b = ⨍_{∂B(z,a)} log max(b, |w − ·|)`, the mean value property of
`log|·|`, through MoTPort's `circCov_eq_of_inside/outside`):

* inside a normalization disc `B̄(0, δ)`: `Var(X_s(z) − X_δ(0)) = log(δ/s)` (`incCov_inner_self`);
* same centre: `Var(X_a(z) − X_b(z)) = log(b/a)` (`incCov_same_self`);
* vanishing covariances for nested circles at the same centre and for far-apart centres;

and the hypotheses `TRLHypC` of QuantumZipper's planar two-radius lemma for an **arbitrary** pair
of radii `ε₁ ≤ ε₂ ≤ 2ε₁` (`trlHyp_pair`; MoTPort's `levelHyp_wpU` is the dyadic case
`ε₂ = 2ε₁ = 2^{-k}`). Own elementary computations.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal Real

namespace MatedCRTHarmonic.LQGCoord

open LQGMetric LQGMetric.CircleAvg QuantumZipper QuantumZipper.TwoRadiusC
open MatedCRTHarmonic.MoTPort.ConeArea6 (circCov_eq_of_inside circCov_eq_of_outside
  circCov_same indepFun_incProc)

/-! ## Circle covariances -/

/-- a circle inside the normalization disc -/
lemma circCov_inside_zero {z : ℂ} {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) (h : ‖z‖ + a ≤ δ) :
    circCov z a 0 δ = Real.log δ := by
  refine circCov_eq_of_inside ha hδ fun x hx => ?_
  rw [mem_sphere_iff_norm] at hx
  have := norm_sub_norm_le x z
  rw [zero_sub, norm_neg]
  linarith

/-- the normalization circle seen from a circle inside it -/
lemma circCov_zero_inside {z : ℂ} {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) (h : ‖z‖ + a ≤ δ) :
    circCov 0 δ z a = Real.log δ := by
  rw [circCov_eq_of_outside hδ ha fun x hx => ?_]
  · rw [zero_sub, norm_neg, max_eq_left (by linarith [norm_nonneg z, ha.le])]
  · rw [mem_sphere_iff_norm, sub_zero] at hx
    have := norm_sub_norm_le x z
    rw [norm_sub_rev] at this
    linarith

lemma circCov_self_same {z : ℂ} {a : ℝ} (ha : 0 < a) : circCov z a z a = Real.log a := by
  rw [circCov_same ha ha, max_self]

/-- disjoint circles -/
lemma circCov_far {t u : ℂ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (h : a + b ≤ ‖t - u‖) :
    circCov t a u b = Real.log ‖t - u‖ := by
  rw [circCov_eq_of_outside ha hb fun x hx => ?_, max_eq_right (by linarith)]
  rw [mem_sphere_iff_norm, norm_sub_rev] at hx
  have := norm_sub_norm_le (t - u) (t - x)
  rw [show t - u - (t - x) = x - u by ring, norm_sub_rev x u] at this
  linarith

/-! ## Variances and vanishing covariances -/

/-- `Var(X_s(z) − X_δ(0)) = log(δ/s)` for `B̄(z, s) ⊆ B̄(0, δ)` -/
lemma incCov_inner_self {z : ℂ} {s δ : ℝ} (hs : 0 < s) (h : ‖z‖ + s ≤ δ) :
    incCov z s 0 δ z s 0 δ = Real.log (δ / s) := by
  have hδ : 0 < δ := by linarith [norm_nonneg z]
  simp only [incCov]
  rw [circCov_self_same hs, circCov_inside_zero hs hδ h, circCov_zero_inside hs hδ h,
    circCov_self_same hδ, Real.log_div hδ.ne' hs.ne']
  ring

/-- `Var(X_a(z) − X_b(z)) = log(b/a)` for `0 < a ≤ b` -/
lemma incCov_same_self {z : ℂ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    incCov z a z b z a z b = Real.log (b / a) := by
  have hb : 0 < b := ha.trans_le hab
  simp only [incCov]
  rw [circCov_self_same ha, circCov_same ha hb, circCov_same hb ha, circCov_self_same hb,
    max_eq_left hab, max_eq_right hab, Real.log_div hb.ne' ha.ne']
  ring

/-- nested circles at the same centre, against the normalization: `Cov(X_a(z) − X_b(z),
X_c(z) − X_δ(0)) = 0` for `a, c ≤ b` and `B̄(z, b) ⊆ B̄(0, δ)` (here `c = b`) -/
lemma incCov_nested_inner {z : ℂ} {a b δ : ℝ} (ha : 0 < a) (hab : a ≤ b) (h : ‖z‖ + b ≤ δ) :
    incCov z a z b z b 0 δ = 0 := by
  have hb : 0 < b := ha.trans_le hab
  have hδ : 0 < δ := by linarith [norm_nonneg z]
  simp only [incCov]
  rw [circCov_same ha hb, circCov_inside_zero ha hδ (by linarith), circCov_self_same hb,
    circCov_inside_zero hb hδ h, max_eq_left hab]
  ring

/-- nested increments at the same centre: `Cov(X_a(z) − X_b(z), X_b(z) − X_c(z)) = 0` for
`a ≤ b ≤ c` -/
lemma incCov_nested_band {z : ℂ} {a b c : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbc : b ≤ c) :
    incCov z a z b z b z c = 0 := by
  have hb : 0 < b := ha.trans_le hab
  have hc : 0 < c := hb.trans_le hbc
  simp only [incCov]
  rw [circCov_same ha hb, circCov_same ha hc, circCov_self_same hb, circCov_same hb hc,
    max_eq_left hab, max_eq_left (hab.trans hbc), max_eq_left hbc]
  ring

/-- far-apart increment against the normalized value: `Cov(X_a(t) − X_b(t), X_b(u) − X_δ(0)) = 0`
for `a ≤ b`, `2b ≤ ‖t − u‖`, `B̄(t, b), B̄(u, b) ⊆ B̄(0, δ)` -/
lemma incCov_far_inner {t u : ℂ} {a b δ : ℝ} (ha : 0 < a) (hab : a ≤ b) (htu : 2 * b ≤ ‖t - u‖)
    (ht : ‖t‖ + b ≤ δ) :
    incCov t a t b u b 0 δ = 0 := by
  have hb : 0 < b := ha.trans_le hab
  have hδ : 0 < δ := by linarith [norm_nonneg t]
  simp only [incCov]
  rw [circCov_far ha hb (by linarith), circCov_inside_zero ha hδ (by linarith),
    circCov_far hb hb (by linarith), circCov_inside_zero hb hδ ht]
  ring

/-- far-apart increments: `Cov(X_a(t) − X_b(t), X_a(u) − X_b(u)) = 0` for `a ≤ b ≤ ‖t − u‖/2` -/
lemma incCov_far_far {t u : ℂ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (htu : 2 * b ≤ ‖t - u‖) :
    incCov t a t b u a u b = 0 := by
  have hb : 0 < b := ha.trans_le hab
  simp only [incCov]
  rw [circCov_far ha ha (by linarith), circCov_far ha hb (by linarith),
    circCov_far hb ha (by linarith), circCov_far hb hb (by linarith)]
  ring

/-! ## Laws and independence -/

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → DistC}

lemma hasLaw_cInc (hX : IsWholePlaneGFF X P) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (z w : ℂ) :
    HasLaw (cInc X r z s w) (gaussianReal 0 (incCov z r w s z r w s).toNNReal) P :=
  ⟨(measurable_cInc hX _ _ _ _).aemeasurable, (map_cInc hX hr hs z w).1⟩

/-- the law of the normalized circle average `X_s(z) − X_δ(0)` -/
lemma hasLaw_cInc_inner (hX : IsWholePlaneGFF X P) {z : ℂ} {s δ : ℝ} (hs : 0 < s)
    (h : ‖z‖ + s ≤ δ) :
    HasLaw (cInc X s z δ 0) (gaussianReal 0 (Real.log (δ / s)).toNNReal) P := by
  have hδ : 0 < δ := by linarith [norm_nonneg z]
  have := hasLaw_cInc hX hs hδ z 0
  rwa [incCov_inner_self hs h] at this

/-- the law of a same-centre increment `X_a(z) − X_b(z)` -/
lemma hasLaw_cInc_same (hX : IsWholePlaneGFF X P) {z : ℂ} {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    HasLaw (cInc X a z b z) (gaussianReal 0 (Real.log (b / a)).toNNReal) P := by
  have := hasLaw_cInc hX ha (ha.trans_le hab) z z
  rwa [incCov_same_self ha hab] at this

/-- the joint measurability of `(t, ω) ↦ X_s(t) − X_δ(w)` -/
lemma measurable_cInc_joint (hX : IsWholePlaneGFF X P) (s δ : ℝ) (w : ℂ) :
    Measurable (fun p : ℂ × Ω => cInc X s p.1 δ w p.2) := by
  have h1 : Measurable fun p : ℂ × Ω => circleAvg (X p.2) s p.1 :=
    measurable_circleAvg.comp (f := fun p : ℂ × Ω => (X p.2, s, p.1))
      ((hX.measurable.comp measurable_snd).prodMk (measurable_const.prodMk measurable_fst))
  have h2 : Measurable fun p : ℂ × Ω => circleAvg (X p.2) δ w :=
    measurable_circleAvg.comp (f := fun p : ℂ × Ω => (X p.2, δ, w))
      ((hX.measurable.comp measurable_snd).prodMk (measurable_const.prodMk measurable_const))
  exact h1.sub h2

/-- the joint measurability of `(t, ω) ↦ X_a(t) − X_b(t)` -/
lemma measurable_cInc_joint_same (hX : IsWholePlaneGFF X P) (a b : ℝ) :
    Measurable (fun p : ℂ × Ω => cInc X a p.1 b p.1 p.2) := by
  have h1 : Measurable fun p : ℂ × Ω => circleAvg (X p.2) a p.1 :=
    measurable_circleAvg.comp (f := fun p : ℂ × Ω => (X p.2, a, p.1))
      ((hX.measurable.comp measurable_snd).prodMk (measurable_const.prodMk measurable_fst))
  have h2 : Measurable fun p : ℂ × Ω => circleAvg (X p.2) b p.1 :=
    measurable_circleAvg.comp (f := fun p : ℂ × Ω => (X p.2, b, p.1))
      ((hX.measurable.comp measurable_snd).prodMk (measurable_const.prodMk measurable_fst))
  exact h1.sub h2

/-! ## The two-radius hypotheses for a pair of radii -/

/-- **The two-radius hypotheses** for the whole-plane GFF, the pair of radii `ε₁ ≤ ε₂ ≤ 2ε₁`, the
normalization `X_δ(0)` and a region `S` with `B̄(t, ε₂) ⊆ B̄(0, δ)` for `t ∈ S`: the coarse value
`U_t = X_{ε₂}(t) − X_δ(0)` (variance `log(δ/ε₂) = 2L`, `K = 0`), the increment
`Δ_t = X_{ε₁}(t) − X_{ε₂}(t)` (variance `log(ε₂/ε₁) ≤ log 2`), decorrelated beyond `2ε₂`. -/
theorem trlHyp_pair (hX : IsWholePlaneGFF X P) {δ ε₁ ε₂ : ℝ} (hδ : 0 < δ) (hε₁ : 0 < ε₁)
    (h12 : ε₁ ≤ ε₂) (h21 : ε₂ ≤ 2 * ε₁) {S : Set ℂ} (hS : ∀ t ∈ S, ‖t‖ + ε₂ ≤ δ) :
    TRLHypC P S (2 * ε₂) 0 (Real.log 2) (fun _ => 1 / 2 * Real.log (δ / ε₂))
      (fun _ => (Real.log (δ / ε₂)).toNNReal) (fun _ => (Real.log (ε₂ / ε₁)).toNNReal)
      (fun t ω => cInc X ε₂ t δ 0 ω) (fun t ω => cInc X ε₁ t ε₂ t ω) := by
  have hε₂ : 0 < ε₂ := hε₁.trans_le h12
  have hlog12 : 0 ≤ Real.log (ε₂ / ε₁) := Real.log_nonneg ((one_le_div hε₁).2 h12)
  let iU : ℂ → IncIdx := fun t => ((⟨ε₂, hε₂⟩, t), (⟨δ, hδ⟩, 0))
  let iΔ : ℂ → IncIdx := fun t => ((⟨ε₁, hε₁⟩, t), (⟨ε₂, hε₂⟩, t))
  refine
    { measU := measurable_cInc_joint hX ε₂ δ 0
      measΔ := measurable_cInc_joint_same hX ε₁ ε₂
      measL := measurable_const
      measw := measurable_const
      lawU := fun t ht => hasLaw_cInc_inner hX hε₂ (hS t ht)
      lawΔ := fun t _ => hasLaw_cInc_same hX hε₁ h12
      varU := fun t ht => ?_
      varΔ := fun t _ => ?_
      indep := fun t ht => ?_
      decor := fun t ht u hu htu => ?_ }
  · have h0 : 0 ≤ Real.log (δ / ε₂) :=
      Real.log_nonneg ((one_le_div hε₂).2 (by linarith [hS t ht, norm_nonneg t]))
    rw [Real.coe_toNNReal _ h0]; linarith
  · rw [Real.coe_toNNReal _ hlog12]
    exact Real.log_le_log (div_pos hε₂ hε₁) (by rw [div_le_iff₀ hε₁]; linarith)
  · have hI := indepFun_incProc hX (fun _ : Unit => iΔ t) (fun _ : Unit => iU t)
      (fun _ _ => incCov_nested_inner hε₁ h12 (hS t ht))
    exact hI.comp (measurable_pi_apply ()) (measurable_pi_apply ())
  · have hI := indepFun_incProc hX (fun _ : Unit => iΔ t) ![iU t, iU u, iΔ u]
      (fun _ i => by
        fin_cases i
        · exact incCov_nested_inner hε₁ h12 (hS t ht)
        · exact incCov_far_inner hε₁ h12 htu (hS t ht)
        · exact incCov_far_far hε₁ h12 htu)
    have hφ : Measurable (fun v : Fin 3 → ℝ => (v 0, v 1, v 2)) :=
      (measurable_pi_apply 0).prodMk ((measurable_pi_apply 1).prodMk (measurable_pi_apply 2))
    exact hI.comp (measurable_pi_apply ()) hφ

end MatedCRTHarmonic.LQGCoord
