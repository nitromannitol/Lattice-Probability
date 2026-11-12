import Mathlib
import LatticeProb.Prob.GaussianProductVectors
import LatticeProb.Prob.ProductCovariance
import LatticeProb.Prob.GaussKahaneExpNeg
import LatticeProb.LQG.LQGSubSquareCovariance

/-!
# Gaussian vectors for the comparison of two sub-squares

Let `h` be a whole-plane GFF, `R = 2^{-k}` with `k ≥ 4`, `δ > 0`, and let `z_0, z_1` be the centres of the
two half-size sub-squares of `[-1/8, 1/8]²`.  For a finite family of points `pt i ∈ [-1/8, 1/8]²` with labels
`piece i ∈ {0, 1}` consider

* the field vector `X_i = γ h_{Rδ}(R pt_i + z_{piece i})` on `(Ω, P)`;
* the comparison vector `Y_i = γ (h_R(z_{piece i}) + h'_{piece i, δ}(pt_i) + g)` on
  `(Ω × ℝ) × Ω²` with the product measure `(P ⊗ N(0,1)) ⊗ P²`, where `h'_s` is the `s`-th independent
  copy of the field and `g` the real Gaussian.

Both are centred Gaussian vectors, with `Cov(Y_i, Y_j) - Cov(X_i, X_j) ≥ 0` coordinatewise
(`IsWholePlaneGFF.covariance_subSquareField_le`).  Kahane's convexity inequality
(`kahane_convexity_exp_neg`) then compares the Laplace functionals of the two vectors
(`IsWholePlaneGFF.integral_exp_neg_subSquareField_le`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set

namespace LatticeProb.Gauss

open LatticeProb LatticeProb.LQG LQGDyadicScaling

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ} {ι : Type*}

/-- The vector `γ h_ε(R pt_i + z_{piece i})` of scaled circle averages on the grid. -/
def subSquareField (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (R ε : ℝ) (piece : ι → Fin 2) (pt : ι → ℂ)
    (ω : Ω) (i : ι) : ℝ :=
  γ * hcirc ω ε ((R : ℂ) * pt i + lqgSquareCentre (piece i))

/-- The comparison vector `γ (h_R(z_{piece i}) + h'_{piece i, δ}(pt_i) + g)` on
`(Ω × ℝ) × (Fin 2 → Ω)`. -/
def subSquareComparison (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (R δ : ℝ) (piece : ι → Fin 2)
    (pt : ι → ℂ) (x : (Ω × ℝ) × (Fin 2 → Ω)) (i : ι) : ℝ :=
  γ * (hcirc x.1.1 R (lqgSquareCentre (piece i)) + hcirc (x.2 (piece i)) δ (pt i) + x.1.2)

/-- The product probability space carrying the comparison vector. -/
abbrev subSquareMeasure (P : Measure Ω) : Measure ((Ω × ℝ) × (Fin 2 → Ω)) :=
  (P.prod (gaussianReal 0 1)).prod (Measure.pi fun _ : Fin 2 => P)

theorem IsWholePlaneGFF.hasGaussianLaw_subSquareField [Fintype ι] (hh : IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    {R ε : ℝ} (hε : 0 < ε) (piece : ι → Fin 2) (pt : ι → ℂ) :
    HasGaussianLaw (fun ω i => subSquareField γ hcirc R ε piece pt ω i) P := by
  have hv : HasGaussianLaw (fun ω i => hcirc ω ε ((R : ℂ) * pt i + lqgSquareCentre (piece i))) P :=
    hasGaussianLaw_vector_of_isGaussianProcess hh.isGaussianProcess
      (fun i => (⟨.circle ε ((R : ℂ) * pt i + lqgSquareCentre (piece i)), hε⟩ :
        GFFObservable.Admissible))
  have := hv.fun_smul γ
  convert this using 2 with ω
  funext i
  simp [subSquareField]

theorem IsWholePlaneGFF.hasGaussianLaw_subSquareComparison [Fintype ι] (hh : IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) (piece : ι → Fin 2) (pt : ι → ℂ) :
    HasGaussianLaw (fun x i => subSquareComparison γ hcirc R δ piece pt x i) (subSquareMeasure P) := by
  have hP := hh.isProbabilityMeasure
  have hA : HasGaussianLaw (fun ω (s : Fin 2) => hcirc ω R (lqgSquareCentre s)) P :=
    hasGaussianLaw_vector_of_isGaussianProcess hh.isGaussianProcess
      (fun s => (⟨.circle R (lqgSquareCentre s), hR⟩ : GFFObservable.Admissible))
  have hB : HasGaussianLaw (fun ω (i : ι) => hcirc ω δ (pt i)) P :=
    hasGaussianLaw_vector_of_isGaussianProcess hh.isGaussianProcess
      (fun i => (⟨.circle δ (pt i), hδ⟩ : GFFObservable.Admissible))
  have hU := hasGaussianLaw_prod_map hA
    (IsGaussian.hasGaussianLaw_id : HasGaussianLaw (id : ℝ → ℝ) (gaussianReal 0 1))
  have hC' := hasGaussianLaw_pi_comp (κ := Fin 2) hB
  have hW := hasGaussianLaw_prod_map hU hC'
  let T : Type _ := ((Fin 2 → ℝ) × ℝ) × (Fin 2 → ι → ℝ)
  let πa : T →L[ℝ] (Fin 2 → ℝ) :=
    (ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _)
  let πg : T →L[ℝ] ℝ := (ContinuousLinearMap.snd ℝ _ _).comp (ContinuousLinearMap.fst ℝ _ _)
  let πb : T →L[ℝ] (Fin 2 → ι → ℝ) := ContinuousLinearMap.snd ℝ _ _
  let L : T →L[ℝ] (ι → ℝ) :=
    ContinuousLinearMap.pi fun i : ι => γ • (
      (ContinuousLinearMap.proj (piece i)).comp πa +
        ((ContinuousLinearMap.proj i).comp
          ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ι → ℝ) (piece i)).comp πb)) + πg)
  have := hW.map L
  convert this using 1
  funext x i
  simp [L, πa, πb, πg, subSquareComparison]
  try ring

section Projections

variable [IsProbabilityMeasure P]

theorem measurePreserving_subSquare_fst :
    MeasurePreserving (fun x : (Ω × ℝ) × (Fin 2 → Ω) => x.1.1) (subSquareMeasure P) P :=
  (measurePreserving_fst (μ := P) (ν := gaussianReal 0 1)).comp
    (measurePreserving_fst (μ := P.prod (gaussianReal 0 1)) (ν := Measure.pi fun _ : Fin 2 => P))

theorem measurePreserving_subSquare_gauss :
    MeasurePreserving (fun x : (Ω × ℝ) × (Fin 2 → Ω) => x.1.2) (subSquareMeasure P)
      (gaussianReal 0 1) :=
  (measurePreserving_snd (μ := P) (ν := gaussianReal 0 1)).comp
    (measurePreserving_fst (μ := P.prod (gaussianReal 0 1)) (ν := Measure.pi fun _ : Fin 2 => P))

theorem measurePreserving_subSquare_eval (s : Fin 2) :
    MeasurePreserving (fun x : (Ω × ℝ) × (Fin 2 → Ω) => x.2 s) (subSquareMeasure P) P :=
  (measurePreserving_eval (fun _ : Fin 2 => P) s).comp
    (measurePreserving_snd (μ := P.prod (gaussianReal 0 1)) (ν := Measure.pi fun _ : Fin 2 => P))

end Projections

theorem IsWholePlaneGFF.integral_subSquareField (hh : IsWholePlaneGFF P hC hcirc) (γ : ℝ) {R ε : ℝ}
    (hε : 0 < ε) (piece : ι → Fin 2) (pt : ι → ℂ) (i : ι) :
    ∫ ω, subSquareField γ hcirc R ε piece pt ω i ∂P = 0 := by
  have hm : ∫ ω, hcirc ω ε ((R : ℂ) * pt i + lqgSquareCentre (piece i)) ∂P = 0 :=
    hh.integral_eq_zero (.circle ε _) hε
  unfold subSquareField
  rw [integral_const_mul, hm, mul_zero]

theorem IsWholePlaneGFF.integral_subSquareComparison (hh : IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) (piece : ι → Fin 2) (pt : ι → ℂ) (i : ι) :
    ∫ x, subSquareComparison γ hcirc R δ piece pt x i ∂(subSquareMeasure P) = 0 := by
  have hP := hh.isProbabilityMeasure
  have ma : MemLp (fun ω => hcirc ω R (lqgSquareCentre (piece i))) 2 P := hh.memLp_two_circle hR _
  have mb : MemLp (fun ω => hcirc ω δ (pt i)) 2 P := hh.memLp_two_circle hδ _
  have mg : MemLp (fun t : ℝ => t) 2 (gaussianReal 0 1) := memLp_id_gaussianReal 2
  have ia : Integrable (fun x : (Ω × ℝ) × (Fin 2 → Ω) => hcirc x.1.1 R (lqgSquareCentre (piece i)))
      (subSquareMeasure P) :=
    (ma.comp_measurePreserving (measurePreserving_subSquare_fst (P := P))).integrable (by norm_num)
  have ib : Integrable (fun x : (Ω × ℝ) × (Fin 2 → Ω) => hcirc (x.2 (piece i)) δ (pt i))
      (subSquareMeasure P) :=
    (mb.comp_measurePreserving (measurePreserving_subSquare_eval (P := P) (piece i))).integrable
      (by norm_num)
  have ig : Integrable (fun x : (Ω × ℝ) × (Fin 2 → Ω) => x.1.2) (subSquareMeasure P) :=
    (mg.comp_measurePreserving (measurePreserving_subSquare_gauss (P := P))).integrable
      (by norm_num)
  have iab : Integrable (fun x : (Ω × ℝ) × (Fin 2 → Ω) =>
      hcirc x.1.1 R (lqgSquareCentre (piece i)) + hcirc (x.2 (piece i)) δ (pt i))
      (subSquareMeasure P) := ia.add ib
  have ha : ∫ x, hcirc x.1.1 R (lqgSquareCentre (piece i)) ∂(subSquareMeasure P) = 0 := by
    rw [integral_comp_measurePreserving (X := fun ω => hcirc ω R (lqgSquareCentre (piece i)))
      measurePreserving_subSquare_fst ma.aestronglyMeasurable]
    exact hh.integral_eq_zero (.circle R _) hR
  have hb : ∫ x, hcirc (x.2 (piece i)) δ (pt i) ∂(subSquareMeasure P) = 0 := by
    rw [integral_comp_measurePreserving (X := fun ω => hcirc ω δ (pt i))
      (measurePreserving_subSquare_eval (piece i)) mb.aestronglyMeasurable]
    exact hh.integral_eq_zero (.circle δ _) hδ
  have hg : ∫ x, x.1.2 ∂(subSquareMeasure P) = 0 := by
    rw [integral_comp_measurePreserving (X := fun t : ℝ => t) measurePreserving_subSquare_gauss
      mg.aestronglyMeasurable]
    exact integral_id_gaussianReal
  unfold subSquareComparison
  rw [integral_const_mul, integral_add iab ig, integral_add ia ib, ha, hb, hg]
  simp

/-- **Covariance of the comparison vector**:
`Cov(Y_i, Y_j) = γ² (Cov(h_R(z_{p_i}), h_R(z_{p_j})) + 1) + 1_{p_i = p_j} γ² Cov(h_δ(pt_i), h_δ(pt_j))`. -/
theorem IsWholePlaneGFF.covariance_subSquareComparison (hh : IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) (piece : ι → Fin 2) (pt : ι → ℂ) (i j : ι) :
    cov[fun x => subSquareComparison γ hcirc R δ piece pt x i,
        fun x => subSquareComparison γ hcirc R δ piece pt x j; subSquareMeasure P] =
      γ ^ 2 * (cov[fun ω => hcirc ω R (lqgSquareCentre (piece i)),
          fun ω => hcirc ω R (lqgSquareCentre (piece j)); P] + 1) +
        (if piece i = piece j then γ ^ 2 * cov[fun ω => hcirc ω δ (pt i),
          fun ω => hcirc ω δ (pt j); P] else 0) := by
  have hP := hh.isProbabilityMeasure
  have ma : ∀ s : Fin 2, MemLp (fun ω => γ * hcirc ω R (lqgSquareCentre s)) 2 P := fun s =>
    (hh.memLp_two_circle hR _).const_mul γ
  have mb : ∀ i : ι, MemLp (fun ω => γ * hcirc ω δ (pt i)) 2 P := fun i =>
    (hh.memLp_two_circle hδ _).const_mul γ
  have mg : MemLp (fun t : ℝ => γ * t) 2 (gaussianReal 0 1) :=
    (memLp_id_gaussianReal 2 : MemLp (fun t : ℝ => t) 2 (gaussianReal 0 1)).const_mul γ
  have mF : ∀ i : ι, MemLp (fun y : Ω × ℝ => γ * hcirc y.1 R (lqgSquareCentre (piece i)) + γ * y.2) 2
      (P.prod (gaussianReal 0 1)) := fun i =>
    ((ma (piece i)).comp_measurePreserving measurePreserving_fst).add
      (mg.comp_measurePreserving measurePreserving_snd)
  have mG : ∀ i : ι, MemLp (fun w : Fin 2 → Ω => γ * hcirc (w (piece i)) δ (pt i)) 2
      (Measure.pi fun _ : Fin 2 => P) := fun i =>
    (mb i).comp_measurePreserving (measurePreserving_eval (fun _ : Fin 2 => P) (piece i))
  have e : ∀ i : ι, (fun x : (Ω × ℝ) × (Fin 2 → Ω) => subSquareComparison γ hcirc R δ piece pt x i) =
      fun x => (γ * hcirc x.1.1 R (lqgSquareCentre (piece i)) + γ * x.1.2) +
        γ * hcirc (x.2 (piece i)) δ (pt i) := by
    intro i; funext x; simp only [subSquareComparison]; ring
  have step1 := covariance_prod_add (μ := P.prod (gaussianReal 0 1))
    (ν := Measure.pi fun _ : Fin 2 => P) (mF i) (mF j) (mG i) (mG j)
  have step2 := covariance_prod_add (μ := P) (ν := gaussianReal 0 1)
    (F := fun ω => γ * hcirc ω R (lqgSquareCentre (piece i)))
    (F' := fun ω => γ * hcirc ω R (lqgSquareCentre (piece j))) (G := fun t : ℝ => γ * t)
    (G' := fun t : ℝ => γ * t) (ma (piece i)) (ma (piece j)) mg mg
  have step3 := covariance_pi_eval_comp (P := P) (piece i) (piece j) (mb i) (mb j)
  have hvar : cov[fun t : ℝ => γ * t, fun t : ℝ => γ * t; gaussianReal 0 1] = γ ^ 2 := by
    rw [covariance_const_mul_left, covariance_const_mul_right,
      show (fun t : ℝ => t) = id from rfl, covariance_self aemeasurable_id, variance_id_gaussianReal]
    simp; ring
  rw [e i, e j, step1, step2, step3, hvar, covariance_const_mul_left, covariance_const_mul_right]
  split_ifs with h
  · rw [covariance_const_mul_left, covariance_const_mul_right]; ring
  · ring

/-- Entrywise comparison `Cov(X_i, X_j) ≤ Cov(Y_i, Y_j)` for `R = 2^{-k}`, `k ≥ 4`, points of the
square `[-1/8, 1/8]²` and `δ ≤ 1/2`. -/
theorem IsWholePlaneGFF.covariance_subSquareField_le (hh : IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    {k : ℕ} (hk : 4 ≤ k) {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (piece : ι → Fin 2) (pt : ι → ℂ)
    (hpt : ∀ i, pt i ∈ lqgSquare) (i j : ι) :
    cov[fun ω => subSquareField γ hcirc (dyadicScale k) (dyadicScale k * δ) piece pt ω i,
        fun ω => subSquareField γ hcirc (dyadicScale k) (dyadicScale k * δ) piece pt ω j; P] ≤
      cov[fun x => subSquareComparison γ hcirc (dyadicScale k) δ piece pt x i,
        fun x => subSquareComparison γ hcirc (dyadicScale k) δ piece pt x j; subSquareMeasure P] := by
  have hP := hh.isProbabilityMeasure
  have hR := dyadicScale_pos' k
  have hε : 0 < dyadicScale k * δ := mul_pos hR hδ
  have hz : ∀ s : Fin 2, ‖lqgSquareCentre s‖ + dyadicScale k ≤ 1 := fun s =>
    norm_lqgSquareCentre_add_dyadicScale_le_one hk s
  have hn : ∀ i, ‖pt i‖ + δ ≤ 1 := fun i => by
    have : ‖pt i‖ ≤ 1 / 4 := by simpa using lqgSquare_subset_closedBall (hpt i)
    linarith
  have hx : ∀ i, ‖(dyadicScale k : ℂ) * pt i + lqgSquareCentre (piece i)‖ + dyadicScale k * δ ≤ 1 :=
    fun i => norm_rescaled_add_le hR (hz _) (hn i)
  rw [hh.covariance_subSquareComparison γ hR hδ]
  have hX : cov[fun ω => subSquareField γ hcirc (dyadicScale k) (dyadicScale k * δ) piece pt ω i,
        fun ω => subSquareField γ hcirc (dyadicScale k) (dyadicScale k * δ) piece pt ω j; P] =
      γ ^ 2 * cov[fun ω => hcirc ω (dyadicScale k * δ)
          ((dyadicScale k : ℂ) * pt i + lqgSquareCentre (piece i)),
        fun ω => hcirc ω (dyadicScale k * δ)
          ((dyadicScale k : ℂ) * pt j + lqgSquareCentre (piece j)); P] := by
    unfold subSquareField
    rw [covariance_const_mul_left, covariance_const_mul_right]; ring
  rw [hX]
  by_cases h : piece i = piece j
  · rw [h]
    simp only [eq_self, ↓reduceIte]
    have h1 := hh.covariance_circle_rescaled hR hδ (hz (piece j)) (w := pt i) (w' := pt j)
      (by linarith [hn i]) (by linarith [hn j])
    have h2 : cov[fun ω => hcirc ω (dyadicScale k) (lqgSquareCentre (piece j)),
        fun ω => hcirc ω (dyadicScale k) (lqgSquareCentre (piece j)); P] = -Real.log (dyadicScale k) := by
      rw [covariance_self (hh.hasGaussianLaw_circle hR _).aemeasurable,
        hh.variance_circle_inside hR (by linarith [hz (piece j)])]
    rw [h1, h2]
    nlinarith [sq_nonneg γ]
  · simp only [h, ↓reduceIte]
    have h1 := hh.covariance_circle_across_pieces hk hε h (hpt i) (hpt j) (hx i) (hx j)
    have := mul_le_mul_of_nonneg_left h1 (sq_nonneg γ)
    linarith

/-- `Var X_i = -γ² log ε`. -/
theorem IsWholePlaneGFF.variance_subSquareField (hh : IsWholePlaneGFF P hC hcirc) (γ : ℝ) {R ε : ℝ}
    (hε : 0 < ε) (piece : ι → Fin 2) (pt : ι → ℂ) (i : ι)
    (hx : ‖(R : ℂ) * pt i + lqgSquareCentre (piece i)‖ + ε ≤ 1) :
    Var[fun ω => subSquareField γ hcirc R ε piece pt ω i; P] = γ ^ 2 * (-Real.log ε) := by
  have hc := (hh.hasGaussianLaw_circle hε ((R : ℂ) * pt i + lqgSquareCentre (piece i))).aemeasurable
  unfold subSquareField
  rw [← covariance_self (hc.const_mul γ), covariance_const_mul_left, covariance_const_mul_right,
    covariance_self hc, hh.variance_circle_inside hε hx]
  ring

/-- `Var Y_i = γ² (1 - log R - log δ)`. -/
theorem IsWholePlaneGFF.variance_subSquareComparison (hh : IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    {R δ : ℝ} (hR : 0 < R) (hδ : 0 < δ) (piece : ι → Fin 2) (pt : ι → ℂ) (i : ι)
    (hz : ‖lqgSquareCentre (piece i)‖ + R ≤ 1) (hn : ‖pt i‖ + δ ≤ 1) :
    Var[fun x => subSquareComparison γ hcirc R δ piece pt x i; subSquareMeasure P] =
      γ ^ 2 * (1 - Real.log R - Real.log δ) := by
  have hP := hh.isProbabilityMeasure
  have m1 : Measurable fun x : (Ω × ℝ) × (Fin 2 → Ω) => hcirc x.1.1 R (lqgSquareCentre (piece i)) :=
    (hh.measurable_circle R _ hR).comp (measurable_fst.comp measurable_fst)
  have m2 : Measurable fun x : (Ω × ℝ) × (Fin 2 → Ω) => hcirc (x.2 (piece i)) δ (pt i) :=
    (hh.measurable_circle δ _ hδ).comp ((measurable_pi_apply (piece i)).comp measurable_snd)
  have m3 : Measurable fun x : (Ω × ℝ) × (Fin 2 → Ω) => x.1.2 :=
    measurable_snd.comp measurable_fst
  have hm : AEMeasurable (fun x => subSquareComparison γ hcirc R δ piece pt x i)
      (subSquareMeasure P) := ((m1.add m2).add m3).const_mul γ |>.aemeasurable
  rw [← covariance_self hm, hh.covariance_subSquareComparison γ hR hδ,
    covariance_self (hh.hasGaussianLaw_circle hR _).aemeasurable,
    covariance_self (hh.hasGaussianLaw_circle hδ _).aemeasurable,
    hh.variance_circle_inside hR hz, hh.variance_circle_inside hδ hn]
  simp only [eq_self, ↓reduceIte]
  ring

/-- **Kahane comparison for the grid vectors.** The Laplace functional of the exponentiated vector `X`
is at most that of the exponentiated comparison vector `Y`. -/
theorem IsWholePlaneGFF.integral_exp_neg_subSquareField_le [Fintype ι] [Nonempty ι]
    (hh : IsWholePlaneGFF P hC hcirc) (γ : ℝ) {lam : ℝ} (hl : 0 ≤ lam) {k : ℕ} (hk : 4 ≤ k) {δ : ℝ}
    (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) (piece : ι → Fin 2) (pt : ι → ℂ) (hpt : ∀ i, pt i ∈ lqgSquare)
    {p : ι → ℝ} (hp : ∀ i, 0 < p i) :
    ∫ ω, Real.exp (-lam * ∑ i, p i * Real.exp (subSquareField γ hcirc (dyadicScale k)
        (dyadicScale k * δ) piece pt ω i - Var[fun ω => subSquareField γ hcirc (dyadicScale k)
          (dyadicScale k * δ) piece pt ω i; P] / 2)) ∂P ≤
      ∫ x, Real.exp (-lam * ∑ i, p i * Real.exp (subSquareComparison γ hcirc (dyadicScale k) δ piece
        pt x i - Var[fun x => subSquareComparison γ hcirc (dyadicScale k) δ piece pt x i;
          subSquareMeasure P] / 2)) ∂(subSquareMeasure P) := by
  have hR := dyadicScale_pos' k
  exact Kahane.kahane_convexity_exp_neg hl hp
    (hh.hasGaussianLaw_subSquareField γ (mul_pos hR hδ) piece pt)
    (hh.hasGaussianLaw_subSquareComparison γ hR hδ piece pt)
    (fun i => hh.integral_subSquareField γ (mul_pos hR hδ) piece pt i)
    (fun i => hh.integral_subSquareComparison γ hR hδ piece pt i)
    (fun i j => hh.covariance_subSquareField_le γ hk hδ hδ2 piece pt hpt i j)

end LatticeProb.Gauss
