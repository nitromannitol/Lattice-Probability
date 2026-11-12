import Mathlib
import LatticeProb.LQG.LQGSubSquareLimit
import LatticeProb.LQG.LQGNegSplit
import LatticeProb.LQG.LQGNegSmall
import LatticeProb.Prob.ProductLaplaceFactor

/-!
# The recursion for Laplace transforms of the mass of the square

For a whole-plane GFF, `k ≥ 4` and `m ≥ 1`, let `Z_n` be the mass of the square `[-1/8, 1/8]²`
for the approximation of the Liouville measure at scale `2^{-n}`.  If `L` bounds the Laplace
transforms of `Z_m` (for the same field), then for `λ > 0`
`E exp (-λ Z_{k+m}) ≤ E ∏_{s < 2} L (λ W_s)`,
where `W_s = e^{γ g - γ²/2} 2^{-k(2+γ²/2)} e^{γ h_{2^{-k}}(z_s)}` is the lognormal weight of the
`s`-th dyadic sub-square, `g` a standard Gaussian independent of the field.

* `IsWholePlaneGFF.exists_measurable_ae_eq_toReal_lqgApproxMass`: the mass of a measurable set has
  a measurable version.
* `integral_exp_neg_lqgSquareMass_le_prod`: the recursion.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Set
open scoped ENNReal

namespace LatticeProb.Gauss

open LatticeProb LatticeProb.LQG LQGDyadicScaling

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {hC : Ω → (ℂ → ℝ) → ℝ}
  {hcirc : Ω → ℝ → ℂ → ℝ}

/-- The lognormal weight `e^{γ g - γ²/2} R^{2+γ²/2} e^{γ h_R(z_s)}` of the `s`-th sub-square,
`R = 2^{-k}`, as a function of the pair `(field, Gaussian)`. -/
def subSquareLognormal (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (k : ℕ) (a : Ω × ℝ) (s : Fin 2) : ℝ :=
  Real.exp (γ * a.2 - γ ^ 2 / 2) * dyadicScale k ^ (2 + γ ^ 2 / 2) *
    Real.exp (γ * hcirc a.1 (dyadicScale k) (lqgSquareCentre s))

omit [MeasurableSpace Ω] in
theorem subSquareWeight_eq_subSquareLognormal (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (k : ℕ)
    (x : (Ω × ℝ) × (Fin 2 → Ω)) (s : Fin 2) :
    subSquareWeight γ hcirc k x s = subSquareLognormal γ hcirc k x.1 s := rfl

omit [MeasurableSpace Ω] in
theorem subSquareLognormal_pos (γ : ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (k : ℕ) (a : Ω × ℝ) (s : Fin 2) :
    0 < subSquareLognormal γ hcirc k a s :=
  mul_pos (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (dyadicScale_pos' k) _)) (Real.exp_pos _)

theorem IsWholePlaneGFF.measurable_subSquareLognormal (hh : IsWholePlaneGFF P hC hcirc) (γ : ℝ)
    (k : ℕ) (s : Fin 2) : Measurable fun a : Ω × ℝ => subSquareLognormal γ hcirc k a s := by
  have h1 : Measurable fun a : Ω × ℝ => hcirc a.1 (dyadicScale k) (lqgSquareCentre s) :=
    (hh.measurable_circle _ _ (dyadicScale_pos' k)).comp measurable_fst
  unfold subSquareLognormal
  exact ((Real.measurable_exp.comp ((measurable_const.mul measurable_snd).sub
    measurable_const)).mul measurable_const).mul (Real.measurable_exp.comp (measurable_const.mul h1))

/-- **Measurable version of the mass of a set.** For a whole-plane GFF and a measurable
`f : ℂ → ℝ≥0∞`, the real-valued mass `ω ↦ (∫ f dμ_n(ω)).toReal` agrees almost surely with a
nonnegative measurable function. -/
theorem IsWholePlaneGFF.exists_measurable_ae_eq_toReal_lqgApproxMass
    (hh : IsWholePlaneGFF P hC hcirc) (γ : ℝ) (n : ℕ) {f : ℂ → ℝ≥0∞} (hf : Measurable f) :
    ∃ Z : Ω → ℝ, Measurable Z ∧ (∀ ω, 0 ≤ Z ω) ∧
      ∀ᵐ ω ∂P, Z ω = (lqgApproxMass γ (hcirc ω) f n).toReal := by
  obtain ⟨dens, hdm, hae⟩ := LatticeProb.LQG.IsWholePlaneGFF.exists_density_representation hh γ n
  refine ⟨fun ω => (∫⁻ x, dens x ω * f x).toReal, ?_, fun ω => ENNReal.toReal_nonneg, ?_⟩
  · have hF : Measurable fun p : ℂ × Ω => dens p.1 p.2 * f p.1 :=
      hdm.mul (hf.comp measurable_fst)
    exact (Measurable.lintegral_prod_left' hF).ennreal_toReal
  · filter_upwards [hae] with ω hω
    rw [(hω.2 f hf)]

theorem lqgApprox_eq_lqgApproxMass_indicator (γ : ℝ) (h : ℝ → ℂ → ℝ) (n : ℕ) {S : Set ℂ}
    (hS : MeasurableSet S) :
    lqgApprox γ h (dyadicScale n) S = lqgApproxMass γ h (S.indicator 1) n := by
  unfold lqgApproxMass
  rw [lintegral_indicator_one hS]

/-- The two sub-squares carry at most the mass of the square, in real terms. -/
theorem sum_toReal_lqgApprox_subSquare_le {γ : ℝ} {h : ℝ → ℂ → ℝ} {ε : ℝ} (hc : Continuous (h ε))
    {k : ℕ} (hk : 4 ≤ k) :
    ∑ s : Fin 2, (lqgApprox γ h ε (lqgSubSquare k s)).toReal ≤
      (lqgApprox γ h ε lqgSquare).toReal := by
  have hloc : IsLocallyFiniteMeasure (lqgApprox γ h ε) := by
    unfold lqgApprox
    exact IsLocallyFiniteMeasure.withDensity_ofReal
      (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hc)))
  have hfin : lqgApprox γ h ε lqgSquare ≠ ∞ :=
    ((measure_mono lqgSquare_subset_closedBall).trans_lt
      (isCompact_closedBall (0 : ℂ) (1 / 4)).measure_lt_top).ne
  have h0 : lqgApprox γ h ε (lqgSubSquare k 0) ≠ ∞ :=
    ((measure_mono (lqgSubSquare_subset hk 0)).trans_lt hfin.lt_top).ne
  have h1 : lqgApprox γ h ε (lqgSubSquare k 1) ≠ ∞ :=
    ((measure_mono (lqgSubSquare_subset hk 1)).trans_lt hfin.lt_top).ne
  rw [Fin.sum_univ_two, ← ENNReal.toReal_add h0 h1,
    ← measure_union (disjoint_lqgSubSquare hk) (measurableSet_lqgSubSquare k 1)]
  exact ENNReal.toReal_mono hfin
    (measure_mono (Set.union_subset (lqgSubSquare_subset hk 0) (lqgSubSquare_subset hk 1)))

/-- **Recursion for the Laplace transform of the mass of the square.** Let `P` be the law of a
whole-plane GFF, `γ ≠ 0`, `k ≥ 4`, `m ≥ 1`, and let `L` be measurable with values `≤ 1` on
`(0, ∞)` and such that `E exp (-ν Z_m) ≤ L ν` for `ν > 0`, where `Z_n` is the mass of
`[-1/8, 1/8]²` for the approximation at scale `2^{-n}`.  Then for `λ > 0`
`E exp (-λ Z_{k+m}) ≤ E ∏_{s < 2} L (λ W_s)`, the expectation on the right being over the field
and an independent standard Gaussian. -/
theorem IsWholePlaneGFF.integral_exp_neg_lqgSquareMass_le_prod (hh : IsWholePlaneGFF P hC hcirc)
    {γ : ℝ} (hγ : γ ≠ 0) {k : ℕ} (hk : 4 ≤ k) {m : ℕ} (hm : 1 ≤ m) (L : ℝ → ℝ)
    (hLm : Measurable L) (hL1 : ∀ ν, 0 < ν → L ν ≤ 1)
    (hL : ∀ ν : ℝ, 0 < ν → ∫ ω, Real.exp (-(ν *
      (lqgApproxMass γ (hcirc ω) (lqgSquare.indicator 1) m).toReal)) ∂P ≤ L ν)
    {lam : ℝ} (hlam : 0 < lam) :
    ∫ ω, Real.exp (-(lam *
        (lqgApproxMass γ (hcirc ω) (lqgSquare.indicator 1) (k + m)).toReal)) ∂P ≤
      ∫ a : Ω × ℝ, ∏ s : Fin 2, L (lam * subSquareLognormal γ hcirc k a s)
        ∂(P.prod (gaussianReal 0 1)) := by
  have : IsProbabilityMeasure P := hh.isProbabilityMeasure
  have hmeasT : Measurable (lqgSquare.indicator (1 : ℂ → ℝ≥0∞)) :=
    measurable_const.indicator measurableSet_lqgSquare
  -- measurable version of the mass at level `m`
  obtain ⟨Z, hZm, hZ0, hZae⟩ := hh.exists_measurable_ae_eq_toReal_lqgApproxMass γ m hmeasT
  have hL' : ∀ ν : ℝ, 0 < ν → ∫ ω, Real.exp (-(ν * Z ω)) ∂P ≤ L ν := by
    intro ν hν
    refine le_trans (le_of_eq (integral_congr_ae ?_)) (hL ν hν)
    filter_upwards [hZae] with ω hω
    rw [hω]
  have hLnn : ∀ ν : ℝ, 0 < ν → 0 ≤ L ν := fun ν hν =>
    le_trans (integral_nonneg fun _ => (Real.exp_pos _).le) (hL' ν hν)
  -- the product bound
  have hint : Integrable (fun a : Ω × ℝ => ∏ s : Fin 2, L (lam * subSquareLognormal γ hcirc k a s))
      (P.prod (gaussianReal 0 1)) := by
    refine Integrable.of_bound (C := 1) ?_ ?_
    · exact (Finset.measurable_prod _ fun s _ => hLm.comp
        (measurable_const.mul (hh.measurable_subSquareLognormal γ k s))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun a => ?_
      have hp : ∀ s : Fin 2, 0 < lam * subSquareLognormal γ hcirc k a s := fun s =>
        mul_pos hlam (subSquareLognormal_pos γ hcirc k a s)
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg fun s _ => hLnn _ (hp s))]
      rw [Fin.prod_univ_two]
      simpa using mul_le_mul (hL1 _ (hp 0)) (hL1 _ (hp 1)) (hLnn _ (hp 1)) zero_le_one
  have hfactor := integral_exp_neg_sum_prod_le (P.prod (gaussianReal 0 1)) P
    (fun s a => subSquareLognormal γ hcirc k a s) Z
    (fun s => hh.measurable_subSquareLognormal γ k s)
    (fun s a => subSquareLognormal_pos γ hcirc k a s) hZm hZ0 L hL' hlam hint
  -- almost surely finite masses and the sub-square inequality
  have hz : ∀ᵐ ω ∂P, Continuous (hcirc ω (dyadicScale (k + m))) :=
    hh.ae_continuous_circle_fixed (dyadicScale_pos' (k + m))
  have hmeasS : ∀ s : Fin 2, Measurable ((lqgSubSquare k s).indicator (1 : ℂ → ℝ≥0∞)) := fun s =>
    measurable_const.indicator (measurableSet_lqgSubSquare k s)
  have hSm : ∀ s : Fin 2, ∃ Zs : Ω → ℝ, Measurable Zs ∧ (∀ ω, 0 ≤ Zs ω) ∧ ∀ᵐ ω ∂P,
      Zs ω = (lqgApprox γ (hcirc ω) (dyadicScale (k + m)) (lqgSubSquare k s)).toReal := by
    intro s
    obtain ⟨Zs, hm', hn', hae⟩ :=
      hh.exists_measurable_ae_eq_toReal_lqgApproxMass γ (k + m) (hmeasS s)
    refine ⟨Zs, hm', hn', ?_⟩
    filter_upwards [hae] with ω hω
    rw [hω, lqgApprox_eq_lqgApproxMass_indicator γ _ _ (measurableSet_lqgSubSquare k s)]
  choose Zs hZsm hZs0 hZsae using hSm
  have hZsae' : ∀ᵐ ω ∂P, ∀ s : Fin 2,
      Zs s ω = (lqgApprox γ (hcirc ω) (dyadicScale (k + m)) (lqgSubSquare k s)).toReal :=
    ae_all_iff.2 hZsae
  have hgint : Integrable (fun ω => Real.exp (-lam * ∑ s : Fin 2,
      (lqgApprox γ (hcirc ω) (dyadicScale (k + m)) (lqgSubSquare k s)).toReal)) P := by
    have hmeas' : Measurable fun ω => Real.exp (-lam * ∑ s : Fin 2, Zs s ω) :=
      Real.measurable_exp.comp (measurable_const.mul (Finset.measurable_sum _ fun s _ => hZsm s))
    have hb : Integrable (fun ω => Real.exp (-lam * ∑ s : Fin 2, Zs s ω)) P := by
      refine Integrable.of_bound (C := 1) hmeas'.aestronglyMeasurable ?_
      refine Filter.Eventually.of_forall fun ω => ?_
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
      have : 0 ≤ ∑ s : Fin 2, Zs s ω := Finset.sum_nonneg fun s _ => hZs0 s ω
      nlinarith
    refine hb.congr ?_
    filter_upwards [hZsae'] with ω hω
    simp only [hω]
  have hmain1 : ∫ ω, Real.exp (-(lam *
        (lqgApproxMass γ (hcirc ω) (lqgSquare.indicator 1) (k + m)).toReal)) ∂P ≤
      ∫ ω, Real.exp (-lam * ∑ s : Fin 2,
        (lqgApprox γ (hcirc ω) (dyadicScale (k + m)) (lqgSubSquare k s)).toReal) ∂P := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)
      hgint ?_
    filter_upwards [hz] with ω hω
    refine Real.exp_le_exp.2 ?_
    have h1 : ∑ s : Fin 2, (lqgApprox γ (hcirc ω) (dyadicScale (k + m)) (lqgSubSquare k s)).toReal ≤
        (lqgApproxMass γ (hcirc ω) (lqgSquare.indicator 1) (k + m)).toReal := by
      rw [lqgApproxMass_lqgSquare]
      exact sum_toReal_lqgApprox_subSquare_le hω hk
    nlinarith [mul_le_mul_of_nonneg_left h1 hlam.le]
  have hmain2 := hh.integral_exp_neg_subSquareMass_le hγ hlam.le hk hm
  have hae2 : ∀ᵐ x ∂(subSquareMeasure P), ∀ s : Fin 2, Z (x.2 s) =
      (lqgApproxMass γ (hcirc (x.2 s)) (lqgSquare.indicator 1) m).toReal := by
    rw [ae_all_iff]
    intro s
    have hmp : MeasurePreserving (fun x : (Ω × ℝ) × (Fin 2 → Ω) => x.2 s) (subSquareMeasure P) P :=
      (measurePreserving_eval (fun _ : Fin 2 => P) s).comp measurePreserving_snd
    exact hmp.quasiMeasurePreserving.ae hZae
  have hmain3 : ∫ x, Real.exp (-lam * ∑ s : Fin 2, subSquareWeight γ hcirc k x s *
        (lqgApproxMass γ (hcirc (x.2 s)) (lqgSquare.indicator 1) m).toReal)
        ∂(subSquareMeasure P) =
      ∫ x : (Ω × ℝ) × (Fin 2 → Ω), Real.exp (-(lam * ∑ s : Fin 2,
        subSquareLognormal γ hcirc k x.1 s * Z (x.2 s))) ∂(subSquareMeasure P) := by
    refine integral_congr_ae ?_
    filter_upwards [hae2] with x hx
    have hs : (∑ s : Fin 2, subSquareWeight γ hcirc k x s *
        (lqgApproxMass γ (hcirc (x.2 s)) (lqgSquare.indicator 1) m).toReal) =
        ∑ s : Fin 2, subSquareLognormal γ hcirc k x.1 s * Z (x.2 s) :=
      Finset.sum_congr rfl fun s _ => by rw [hx s]; rfl
    rw [neg_mul, hs]
  exact hmain1.trans (hmain2.trans ((le_of_eq hmain3).trans hfactor))

end LatticeProb.Gauss
