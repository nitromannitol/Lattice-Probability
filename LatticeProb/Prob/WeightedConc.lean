/-
Weighted exponential concentration on a product measure.

The logarithmic moment generating function of a weighted sum of independent
centred variables with an exponential moment is Gaussian, for parameters small
against the largest weight; the one-site law is sub-Gaussian on the range
`θ₀/2` by `LatticeProb/Prob/SubGaussian.lean`, the property passes to
independent weighted sums, and the weights only have to be small enough that
every `λ ℓ_i` stays in the range.  From the exponential form of
`LatticeProb/Prob/EfronStein.lean` the same argument gives the deviation bound
for a coordinate-Lipschitz function of the whole configuration, and its
Bernstein tail by Chernoff.
-/
import Mathlib
import LatticeProb.Prob.SubGaussian
import LatticeProb.Prob.EfronStein

open MeasureTheory

namespace LatticeProb

/-- `‖ℓ‖_{ℓ²} = (∑_i ℓ_i²)^{1/2}`. -/
noncomputable def lTwoNorm {N : ℕ} (ℓ : Fin N → ℝ) : ℝ :=
  Real.sqrt (∑ i, ℓ i ^ 2)

/-- `‖ℓ‖_{ℓ^∞} = max_i ℓ_i`, as a supremum over the finite index type. -/
noncomputable def lInfNorm {N : ℕ} (ℓ : Fin N → ℝ) : ℝ := ⨆ i, ℓ i

/-- Part (c) of `lem:weighted-exp-conc`. -/
theorem weighted_exp_conc_mgf (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (N : ℕ) (ν : Measure ℝ), IsProbabilityMeasure ν → ∫ z, z ∂ν = 0 →
        Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
        ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
        ∀ ℓ : Fin N → ℝ, (∀ i, 0 ≤ ℓ i) → (∃ i, ℓ i ≠ 0) →
          ∀ lam : ℝ, |lam| * lInfNorm ℓ ≤ c →
            Integrable (fun ξ => Real.exp (lam * ∑ i, ℓ i * ξ i))
                (Measure.pi fun _ : Fin N => ν) ∧
              Real.log (∫ ξ, Real.exp (lam * ∑ i, ℓ i * ξ i)
                  ∂(Measure.pi fun _ : Fin N => ν)) ≤
                C * lam ^ 2 * lTwoNorm ℓ ^ 2 := by
  refine ⟨θ₀ / 2, 16 / θ₀ ^ 2 * max K₀ 1, by linarith, by positivity, ?_⟩
  intro N ν hprob hmean hexp hK ℓ hℓ hne lam hlam
  haveI := hprob
  have hid : Integrable id ν := integrable_id_of_exp_moment ν θ₀ hθ₀ hexp
  have hK' : ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ max K₀ 1 := le_trans hK (le_max_left _ _)
  have hSG : SubGaussianOn id (16 / θ₀ ^ 2 * max K₀ 1) (θ₀ / 2) ν :=
    subGaussianOn_of_exp_moment ν θ₀ (max K₀ 1) hθ₀ hexp hK' hid hmean
  have hbdd : BddAbove (Set.range ℓ) := Finite.bddAbove_range ℓ
  have hlami : ∀ i, |lam * ℓ i| ≤ θ₀ / 2 := by
    intro i
    rw [abs_mul, abs_of_nonneg (hℓ i)]
    refine le_trans ?_ hlam
    exact mul_le_mul_of_nonneg_left (le_ciSup hbdd i) (abs_nonneg lam)
  have hfac : ∀ ξ : Fin N → ℝ, Real.exp (lam * ∑ i, ℓ i * ξ i)
      = ∏ i, Real.exp (lam * ℓ i * ξ i) := by
    intro ξ
    rw [← Real.exp_sum, Finset.mul_sum]
    exact congrArg Real.exp (Finset.sum_congr rfl fun i _ => by ring)
  have hintprod : Integrable (fun ξ : Fin N → ℝ => ∏ i, Real.exp (lam * ℓ i * ξ i))
      (Measure.pi fun _ : Fin N => ν) :=
    Integrable.fintype_prod (fun i => (hSG (lam * ℓ i) (hlami i)).1)
  have hint : Integrable (fun ξ : Fin N → ℝ => Real.exp (lam * ∑ i, ℓ i * ξ i))
      (Measure.pi fun _ : Fin N => ν) :=
    hintprod.congr (Filter.Eventually.of_forall fun ξ => (hfac ξ).symm)
  refine ⟨hint, ?_⟩
  have hbound := integral_exp_weighted_sum_le ν (16 / θ₀ ^ 2 * max K₀ 1) (θ₀ / 2) hSG ℓ lam hlami
  have hpos : 0 < ∫ ξ, Real.exp (lam * ∑ i, ℓ i * ξ i) ∂(Measure.pi fun _ : Fin N => ν) := by
    rw [integral_pos_iff_support_of_nonneg (fun ξ => (Real.exp_pos _).le) hint]
    have hsupp : Function.support
        (fun ξ : Fin N → ℝ => Real.exp (lam * ∑ i, ℓ i * ξ i)) = Set.univ := by
      ext ξ
      simp [Function.mem_support, (Real.exp_pos _).ne']
    rw [hsupp]
    simp
  have hlog := Real.log_le_log hpos hbound
  rw [Real.log_exp] at hlog
  refine le_trans hlog (le_of_eq ?_)
  have hsq : lTwoNorm ℓ ^ 2 = ∑ i, ℓ i ^ 2 := by
    unfold lTwoNorm
    exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  rw [hsq]


/-! ### The two norms of the weight vector -/

theorem le_lInfNorm {N : ℕ} (ℓ : Fin N → ℝ) (i : Fin N) : ℓ i ≤ lInfNorm ℓ :=
  le_ciSup (Finite.bddAbove_range ℓ) i

theorem lInfNorm_pos {N : ℕ} (ℓ : Fin N → ℝ) (hℓ : ∀ i, 0 ≤ ℓ i) (hne : ∃ i, ℓ i ≠ 0) :
    0 < lInfNorm ℓ := by
  obtain ⟨i, hi⟩ := hne
  exact lt_of_lt_of_le (lt_of_le_of_ne (hℓ i) (Ne.symm hi)) (le_lInfNorm ℓ i)

theorem lTwoNorm_sq {N : ℕ} (ℓ : Fin N → ℝ) : lTwoNorm ℓ ^ 2 = ∑ i, ℓ i ^ 2 := by
  unfold lTwoNorm
  exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)

theorem lTwoNorm_pos {N : ℕ} (ℓ : Fin N → ℝ) (_hℓ : ∀ i, 0 ≤ ℓ i) (hne : ∃ i, ℓ i ≠ 0) :
    0 < lTwoNorm ℓ := by
  obtain ⟨i, hi⟩ := hne
  refine Real.sqrt_pos.mpr ?_
  refine lt_of_lt_of_le (b := ℓ i ^ 2) (by positivity) ?_
  exact Finset.single_le_sum (f := fun j => ℓ j ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ i)

/-! ### Part (d) -/

/-- The exponential deviation bound for a coordinate-Lipschitz function of a
product measure.  The existential over the constant that the original statement
carried was vacuous, the constant appearing nowhere in the conclusion, so it is
dropped here. -/
theorem weighted_exp_conc_exp (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀) :
      ∀ (N : ℕ) (ν : Measure ℝ), IsProbabilityMeasure ν →
        Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
        ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
        ∀ F : (Fin N → ℝ) → ℝ, Measurable F →
        ∀ ℓ : Fin N → ℝ, (∀ i, 0 ≤ ℓ i) → (∃ i, ℓ i ≠ 0) →
          (∀ (ξ : Fin N → ℝ) (i : Fin N) (y : ℝ),
            |F ξ - F (Function.update ξ i y)| ≤ ℓ i * |ξ i - y|) →
          ∀ lam : ℝ, |lam| * lInfNorm ℓ < θ₀ →
            Integrable (fun ξ => Real.exp (lam * (F ξ -
                ∫ η, F η ∂(Measure.pi fun _ : Fin N => ν))))
                (Measure.pi fun _ : Fin N => ν) ∧
              ∫ ξ, Real.exp (lam * (F ξ - ∫ η, F η ∂(Measure.pi fun _ : Fin N => ν)))
                  ∂(Measure.pi fun _ : Fin N => ν) ≤
                Real.exp (4 * (Real.exp K₀ * K₀) / (θ₀ - |lam| * lInfNorm ℓ) ^ 2 * lam ^ 2 *
                  lTwoNorm ℓ ^ 2) := by
  intro N ν hprob hexp hK F hFm ℓ hℓ hne hLip lam hlam
  haveI := hprob
  have hL0 : 0 < lInfNorm ℓ := lInfNorm_pos ℓ hℓ hne
  have hnn : 0 ≤ |lam| * lInfNorm ℓ := mul_nonneg (abs_nonneg lam) hL0.le
  have hδ : 0 < θ₀ - |lam| * lInfNorm ℓ := by linarith
  have hδθ : θ₀ - |lam| * lInfNorm ℓ ≤ θ₀ := by linarith
  have hgap : ∀ i, |lam| * ℓ i ≤ θ₀ - (θ₀ - |lam| * lInfNorm ℓ) := by
    intro i
    have := mul_le_mul_of_nonneg_left (le_lInfNorm ℓ i) (abs_nonneg lam)
    linarith
  have hgap' : ∀ i, |lam| * ℓ i ≤ θ₀ := fun i => le_trans (hgap i) (by linarith)
  refine ⟨integrable_exp_lip ν θ₀ hexp F hFm ℓ hLip lam hgap' _, ?_⟩
  have h := exp_conc_pi ν θ₀ K₀ (θ₀ - |lam| * lInfNorm ℓ) hθ₀ hδ hδθ hexp hK lam
    N F hFm ℓ hℓ hLip hgap
  rw [lTwoNorm_sq]
  exact h

/-! ### Part (b) -/

theorem measure_le_ofReal {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (S : Set Ω) (B : ℝ) (hB : μ.real S ≤ B) :
    μ S ≤ ENNReal.ofReal B := by
  have hne : μ S ≠ ⊤ := measure_ne_top μ S
  rw [← ENNReal.ofReal_toReal hne]
  exact ENNReal.ofReal_le_ofReal hB

/-- Part (b) of `lem:weighted-exp-conc`, by Chernoff from part (d). -/
theorem weighted_exp_conc_tail (θ₀ K₀ : ℝ) (hθ₀ : 0 < θ₀) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (N : ℕ) (ν : Measure ℝ), IsProbabilityMeasure ν →
        Integrable (fun z => Real.exp (θ₀ * |z|)) ν →
        ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K₀ →
        ∀ F : (Fin N → ℝ) → ℝ, Measurable F →
        ∀ ℓ : Fin N → ℝ, (∀ i, 0 ≤ ℓ i) → (∃ i, ℓ i ≠ 0) →
          (∀ (ξ : Fin N → ℝ) (i : Fin N) (y : ℝ),
            |F ξ - F (Function.update ξ i y)| ≤ ℓ i * |ξ i - y|) →
          ∀ r : ℝ, 0 ≤ r →
            (Measure.pi fun _ : Fin N => ν)
                {ξ | r ≤ |F ξ - ∫ η, F η ∂(Measure.pi fun _ : Fin N => ν)|} ≤
              ENNReal.ofReal (C * Real.exp (-(c * min (r ^ 2 / lTwoNorm ℓ ^ 2)
                (r / lInfNorm ℓ)))) := by
  set K : ℝ := max K₀ 1 with hKdef
  have hK1 : (1 : ℝ) ≤ K := le_max_right _ _
  set C₀ : ℝ := 16 * (Real.exp K * K) / θ₀ ^ 2 with hC₀def
  have hC₀ : 0 < C₀ := by
    rw [hC₀def]
    have : (0 : ℝ) < K := by linarith
    positivity
  refine ⟨min (1 / (4 * C₀)) (θ₀ / 4), 2, lt_min (by positivity) (by positivity),
    by norm_num, ?_⟩
  intro N ν hprob hexp hK' F hFm ℓ hℓ hne hLip r hr
  haveI := hprob
  have hKle : ∫ z, Real.exp (θ₀ * |z|) ∂ν ≤ K := le_trans hK' (le_max_left _ _)
  have hL0 : 0 < lInfNorm ℓ := lInfNorm_pos ℓ hℓ hne
  have hL2 : 0 < lTwoNorm ℓ := lTwoNorm_pos ℓ hℓ hne
  set μ : Measure (Fin N → ℝ) := Measure.pi fun _ : Fin N => ν with hμdef
  have hSGgen : ∀ H : (Fin N → ℝ) → ℝ, Measurable H →
      (∀ (ξ : Fin N → ℝ) (i : Fin N) (y : ℝ),
        |H ξ - H (Function.update ξ i y)| ≤ ℓ i * |ξ i - y|) →
      SubGaussianOn (fun ξ => H ξ - ∫ η, H η ∂μ) (C₀ * lTwoNorm ℓ ^ 2)
        (θ₀ / (2 * lInfNorm ℓ)) μ := by
    intro H hHm hHLip s hs
    have hprod : |s| * lInfNorm ℓ ≤ θ₀ / 2 := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * lInfNorm ℓ)] at hs
      have h2 : |s| * (2 * lInfNorm ℓ) = 2 * (|s| * lInfNorm ℓ) := by ring
      rw [h2] at hs
      linarith
    have hgap : ∀ i, |s| * ℓ i ≤ θ₀ - θ₀ / 2 := by
      intro i
      have h1 := mul_le_mul_of_nonneg_left (le_lInfNorm ℓ i) (abs_nonneg s)
      linarith
    have hgap' : ∀ i, |s| * ℓ i ≤ θ₀ := fun i => le_trans (hgap i) (by linarith)
    refine ⟨integrable_exp_lip ν θ₀ hexp H hHm ℓ hHLip s hgap' _, ?_⟩
    have h := exp_conc_pi ν θ₀ K (θ₀ / 2) hθ₀ (by linarith) (by linarith) hexp hKle s
      N H hHm ℓ hℓ hHLip hgap
    refine le_trans h (le_of_eq (congrArg Real.exp ?_))
    rw [hC₀def, lTwoNorm_sq]
    field_simp
    ring
  have hSG1 := hSGgen F hFm hLip
  have hSG2 := hSGgen (fun ξ => -F ξ) hFm.neg (fun ξ i y => by
    show |(-F ξ) - (-F (Function.update ξ i y))| ≤ ℓ i * |ξ i - y|
    have he : |(-F ξ) - (-F (Function.update ξ i y))|
        = |F ξ - F (Function.update ξ i y)| := by
      rw [← abs_neg]
      congr 1
      ring
    rw [he]
    exact hLip ξ i y)
  have hcpos : 0 < C₀ * lTwoNorm ℓ ^ 2 := by positivity
  have hs₀pos : 0 < θ₀ / (2 * lInfNorm ℓ) := by positivity
  have h1 := measure_ge_le_of_subGaussianOn μ _ _ _ hcpos hs₀pos hSG1 r hr
  have h2 := measure_ge_le_of_subGaussianOn μ _ _ _ hcpos hs₀pos hSG2 r hr
  set EF : ℝ := ∫ η, F η ∂μ with hEFdef
  have hnegint : ∫ η, (fun ξ => -F ξ) η ∂μ = -EF := by
    show ∫ η, -F η ∂μ = -EF
    rw [integral_neg, hEFdef]
  rw [hnegint] at h2
  set B : ℝ := Real.exp (-min (r ^ 2 / (4 * (C₀ * lTwoNorm ℓ ^ 2)))
    (θ₀ / (2 * lInfNorm ℓ) * r / 2)) with hBdef
  have hB1 : μ {ξ | r ≤ F ξ - EF} ≤ ENNReal.ofReal B :=
    measure_le_ofReal μ _ B h1
  have hB2 : μ {ξ | r ≤ -F ξ - -EF} ≤ ENNReal.ofReal B :=
    measure_le_ofReal μ _ B h2
  have hsubset : {ξ : Fin N → ℝ | r ≤ |F ξ - EF|}
      ⊆ {ξ | r ≤ F ξ - EF} ∪ {ξ | r ≤ -F ξ - -EF} := by
    intro ξ hξ
    rcases abs_cases (F ξ - EF) with ⟨he, _⟩ | ⟨he, _⟩
    · left
      show r ≤ F ξ - EF
      rw [← he]
      exact hξ
    · right
      show r ≤ -F ξ - -EF
      have : -F ξ - -EF = -(F ξ - EF) := by ring
      rw [this, ← he]
      exact hξ
  have hB0 : 0 ≤ B := (Real.exp_pos _).le
  have hfinal : B ≤ Real.exp (-(min (1 / (4 * C₀)) (θ₀ / 4) *
      min (r ^ 2 / lTwoNorm ℓ ^ 2) (r / lInfNorm ℓ))) := by
    refine Real.exp_le_exp.mpr ?_
    have hmin0 : 0 ≤ min (r ^ 2 / lTwoNorm ℓ ^ 2) (r / lInfNorm ℓ) :=
      le_min (by positivity) (by positivity)
    have hc0 : 0 ≤ min (1 / (4 * C₀)) (θ₀ / 4) :=
      le_min (by positivity) (by positivity)
    have hA : min (1 / (4 * C₀)) (θ₀ / 4) * min (r ^ 2 / lTwoNorm ℓ ^ 2) (r / lInfNorm ℓ)
        ≤ r ^ 2 / (4 * (C₀ * lTwoNorm ℓ ^ 2)) := by
      have hstep : min (1 / (4 * C₀)) (θ₀ / 4) *
          min (r ^ 2 / lTwoNorm ℓ ^ 2) (r / lInfNorm ℓ)
          ≤ (1 / (4 * C₀)) * (r ^ 2 / lTwoNorm ℓ ^ 2) :=
        mul_le_mul (min_le_left _ _) (min_le_left _ _) hmin0 (by positivity)
      refine le_trans hstep (le_of_eq ?_)
      field_simp
    have hBb : min (1 / (4 * C₀)) (θ₀ / 4) * min (r ^ 2 / lTwoNorm ℓ ^ 2) (r / lInfNorm ℓ)
        ≤ θ₀ / (2 * lInfNorm ℓ) * r / 2 := by
      have hstep : min (1 / (4 * C₀)) (θ₀ / 4) *
          min (r ^ 2 / lTwoNorm ℓ ^ 2) (r / lInfNorm ℓ)
          ≤ (θ₀ / 4) * (r / lInfNorm ℓ) :=
        mul_le_mul (min_le_right _ _) (min_le_right _ _) hmin0 (by positivity)
      refine le_trans hstep (le_of_eq ?_)
      field_simp
      ring
    have := le_min hA hBb
    linarith
  calc μ {ξ : Fin N → ℝ | r ≤ |F ξ - EF|}
      ≤ μ ({ξ | r ≤ F ξ - EF} ∪ {ξ | r ≤ -F ξ - -EF}) := measure_mono hsubset
    _ ≤ μ {ξ | r ≤ F ξ - EF} + μ {ξ | r ≤ -F ξ - -EF} := measure_union_le _ _
    _ ≤ ENNReal.ofReal B + ENNReal.ofReal B := add_le_add hB1 hB2
    _ = ENNReal.ofReal (2 * B) := by
        rw [← ENNReal.ofReal_add hB0 hB0]
        congr 1
        ring
    _ ≤ ENNReal.ofReal (2 * Real.exp (-(min (1 / (4 * C₀)) (θ₀ / 4) *
          min (r ^ 2 / lTwoNorm ℓ ^ 2) (r / lInfNorm ℓ)))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        linarith [hfinal]

end LatticeProb
