/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.GFF.K3.GreenLower2 at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.GreenLower1
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.ZeroRegularization

/-!
# GFF-K3, node H4 (part 2): smooth approximation of admissible measures in the `B`-norm

`σε μ ε` has the smooth density `φσ μ ε a = ∫ ηε ε (a - (y + 2εi)) dμ(y)`, compactly supported in
`{Im ≥ ε}`. `exists_σε_close`: `kernelCov2 greenH (μ, σε μ ε) (μ, σε μ ε)` is as small as desired.
Route: Fatou for `B(μ, σε)` (the mollified kernel is `≥ log‖c - x̄‖ - log max(ε, ‖c - x‖)`),
superharmonicity (`Kε_le`) and dominated convergence for `B(σε, σε)`.
-/

noncomputable section

open MeasureTheory Filter Set Topology Real
open scoped ENNReal NNReal ComplexConjugate

namespace QuantumZipper.K3

attribute [local irreducible] Zη

/-- The shifted centre `y + 2εi`. -/
def cε (ε : ℝ) (y : ℂ) : ℂ := y + ((2 * ε : ℝ) : ℂ) * Complex.I

lemma cε_im (ε : ℝ) (y : ℂ) : (cε ε y).im = y.im + 2 * ε := by simp [cε]

lemma continuous_cε (ε : ℝ) : Continuous (cε ε) := by unfold cε; fun_prop

/-- The smooth density. -/
def φσ (μ : Measure ℂ) (ε : ℝ) (a : ℂ) : ℝ := ∫ y, ηε ε (a - cε ε y) ∂μ

/-- The smoothed measure. -/
def σε (μ : Measure ℂ) (ε : ℝ) : Measure ℂ :=
  volume.withDensity fun a => ENNReal.ofReal (φσ μ ε a)

section Props

variable {μ : Measure ℂ} {ε : ℝ}

lemma contDiff_φσ [IsFiniteMeasure μ] (hε : 0 < ε) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (φσ μ ε) :=
  contDiff_infty.mpr fun n =>
    contDiff_integral_comp_sub μ (continuous_cε ε) n (contDiff_ηε ε) (hasCompactSupport_ηε hε)

lemma φσ_nonneg (hε : 0 < ε) (a : ℂ) : 0 ≤ φσ μ ε a :=
  integral_nonneg fun y => ηε_nonneg hε _

/-- The compact set carrying `σε`. -/
def Kσ (K : Set ℂ) (ε : ℝ) : Set ℂ :=
  (fun q : ℂ × ℂ => cε ε q.1 + q.2) '' (K ×ˢ Metric.closedBall 0 ε)

lemma isCompact_Kσ {K : Set ℂ} (hK : IsCompact K) (ε : ℝ) : IsCompact (Kσ K ε) :=
  (hK.prod (isCompact_closedBall 0 ε)).image (by unfold cε; fun_prop)

lemma Kσ_subset {K : Set ℂ} (hKH : K ⊆ Hbar) (hε : 0 < ε) : Kσ K ε ⊆ {a | ε ≤ a.im} := by
  rintro _ ⟨⟨y, v⟩, ⟨hy, hv⟩, rfl⟩
  have hy' : 0 ≤ y.im := hKH hy
  have hv' : ‖v‖ ≤ ε := by simpa using hv
  have h1 : -‖v‖ ≤ v.im := by
    have := Complex.abs_im_le_norm v; linarith [neg_abs_le v.im]
  show ε ≤ (cε ε y + v).im
  rw [Complex.add_im, cε_im]
  linarith

lemma φσ_eq_zero {K : Set ℂ} (hKc : μ Kᶜ = 0) (hε : 0 < ε) {a : ℂ} (ha : a ∉ Kσ K ε) :
    φσ μ ε a = 0 := by
  unfold φσ
  refine integral_eq_zero_of_ae ?_
  have hae : ∀ᵐ y ∂μ, y ∈ K := ae_iff.2 hKc
  filter_upwards [hae] with y hy
  refine ηε_eq_zero hε (not_lt.mp fun h => ha ⟨(y, a - cε ε y), ⟨hy, ?_⟩, by simp⟩)
  simpa using h.le

end Props

section Adm

variable {μ : Measure ℂ} {ε : ℝ}

lemma integrable_ηε_shift [IsFiniteMeasure μ] (hε : 0 < ε) (a : ℂ) :
    Integrable (fun y => ηε ε (a - cε ε y)) μ := by
  obtain ⟨C, hC⟩ := (contDiff_ηε ε).continuous.bounded_above_of_compact_support
    (hasCompactSupport_ηε hε)
  exact (integrable_const C).mono'
    ((contDiff_ηε ε).continuous.comp (continuous_const.sub (continuous_cε ε))).aestronglyMeasurable
    (ae_of_all _ fun y => hC _)

lemma ofReal_φσ [IsFiniteMeasure μ] (hε : 0 < ε) (a : ℂ) :
    ENNReal.ofReal (φσ μ ε a) = ∫⁻ y, ENNReal.ofReal (ηε ε (a - cε ε y)) ∂μ :=
  ofReal_integral_eq_lintegral_ofReal (integrable_ηε_shift hε a)
    (ae_of_all _ fun y => ηε_nonneg hε _)

lemma measurable_φσ [IsFiniteMeasure μ] (hε : 0 < ε) : Measurable (φσ μ ε) :=
  (contDiff_φσ hε).continuous.measurable

lemma measurable_ηε_shift (ε : ℝ) :
    Measurable fun q : ℂ × ℂ => ENNReal.ofReal (ηε ε (q.1 - cε ε q.2)) :=
  ENNReal.measurable_ofReal.comp ((contDiff_ηε ε).continuous.measurable.comp
    (measurable_fst.sub ((continuous_cε ε).measurable.comp measurable_snd)))

theorem lintegral_σε [IsFiniteMeasure μ] (hε : 0 < ε) {g : ℂ → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ b, g b ∂σε μ ε =
      ∫⁻ y, (∫⁻ b, g b * ENNReal.ofReal (ηε ε (b - cε ε y))) ∂μ := by
  unfold σε
  rw [show (fun a => ENNReal.ofReal (φσ μ ε a)) = ENNReal.ofReal ∘ φσ μ ε from rfl,
    lintegral_withDensity_eq_lintegral_mul _
    (ENNReal.measurable_ofReal.comp (measurable_φσ hε)) hg]
  have hη := measurable_ηε_shift ε
  have hm : Measurable (Function.uncurry fun (b y : ℂ) =>
      g b * ENNReal.ofReal (ηε ε (b - cε ε y))) :=
    (hg.comp measurable_fst).mul hη
  calc ∫⁻ b, ((fun a => ENNReal.ofReal (φσ μ ε a)) * g) b
      = ∫⁻ b, ∫⁻ y, g b * ENNReal.ofReal (ηε ε (b - cε ε y)) ∂μ := by
        refine lintegral_congr fun b => ?_
        simp only [Pi.mul_apply]
        have hb : Measurable fun y => ENNReal.ofReal (ηε ε (b - cε ε y)) := by
          have h1 := (contDiff_ηε ε).continuous.measurable
          have h2 := (continuous_cε ε).measurable
          fun_prop
        rw [ofReal_φσ hε, ← lintegral_mul_const _ hb]
        simp only [Function.comp_apply, mul_comm]
    _ = _ := lintegral_lintegral_swap hm.aemeasurable

theorem isAdmissibleH_σε (hμ : IsAdmissibleH μ) (hε : 0 < ε) : IsAdmissibleH (σε μ ε) := by
  obtain ⟨hμf, ⟨K, hK, hKH, hKc⟩, -⟩ := hμ
  have := hμf
  obtain ⟨C, hC⟩ := (contDiff_ηε ε).continuous.bounded_above_of_compact_support
    (hasCompactSupport_ηε hε)
  refine isAdmissibleH_withDensity (ENNReal.measurable_ofReal.comp (measurable_φσ hε))
    (M := ENNReal.ofReal (C * μ.real univ)) ENNReal.ofReal_lt_top
    (fun a => ENNReal.ofReal_le_ofReal ?_) (isCompact_Kσ hK ε) ?_
    (fun a ha => by rw [φσ_eq_zero hKc hε ha, ENNReal.ofReal_zero])
  · unfold φσ
    calc ∫ y, ηε ε (a - cε ε y) ∂μ ≤ ∫ _, C ∂μ :=
          integral_mono (integrable_ηε_shift hε a) (integrable_const C) fun y =>
            (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC (a - cε ε y))
      _ = C * μ.real univ := by rw [integral_const, smul_eq_mul, mul_comm]
  · intro a ha
    have h := Kσ_subset hKH hε ha
    show (0 : ℝ) ≤ a.im
    exact hε.le.trans h

lemma σε_ae_Hbar (hμ : IsAdmissibleH μ) (hε : 0 < ε) : ∀ᵐ a ∂σε μ ε, a ∈ Hbar := by
  obtain ⟨hμf, ⟨K, hK, hKH, hKc⟩, -⟩ := hμ
  have := hμf
  unfold σε
  rw [show (fun a => ENNReal.ofReal (φσ μ ε a)) = ENNReal.ofReal ∘ φσ μ ε from rfl,
    ae_withDensity_iff (ENNReal.measurable_ofReal.comp (measurable_φσ hε))]
  refine ae_of_all _ fun a ha => ?_
  by_contra hna
  apply ha
  show ENNReal.ofReal (φσ μ ε a) = 0
  have haK : a ∉ Kσ K ε := fun h => hna (show (0 : ℝ) ≤ a.im from hε.le.trans (Kσ_subset hKH hε h))
  rw [φσ_eq_zero hKc hε haK, ENNReal.ofReal_zero]

lemma σε_ae_ne (c : ℂ) : ∀ᵐ a ∂σε μ ε, a ≠ c := by
  rw [ae_iff]
  have : {a | ¬a ≠ c} = {c} := by ext a; simp
  rw [this]
  exact withDensity_absolutelyContinuous _ _ (measure_singleton c)

end Adm

/-! ## Kernel covariances as lintegrals -/

lemma ae_ne_of_admissible {μ : Measure ℂ} (hμ : IsAdmissibleH μ) (y : ℂ) : ∀ᵐ x ∂μ, x ≠ y := by
  rw [ae_iff]
  have : {a | ¬a ≠ y} = {y} := by ext a; simp
  rw [this]; exact noAtoms_of_isAdmissibleH hμ y

lemma ae_prod_offdiag {ν ν' : Measure ℂ} (hν : IsAdmissibleH ν) (hν' : IsAdmissibleH ν') :
    ∀ᵐ p ∂ν.prod ν', p.1 ∈ Hbar ∧ p.2 ∈ Hbar ∧ p.1 ≠ p.2 := by
  obtain ⟨hνf, ⟨K, hK, hKH, hKc⟩, -⟩ := id hν
  obtain ⟨hνf', ⟨K', hK', hKH', hKc'⟩, -⟩ := id hν'
  have := hνf; have := hνf'
  have h1 : ∀ᵐ p ∂ν.prod ν', p.1 ∈ K := by
    rw [ae_iff]
    have : {p : ℂ × ℂ | ¬p.1 ∈ K} = Kᶜ ×ˢ univ := by ext p; simp
    rw [this, Measure.prod_prod, hKc, zero_mul]
  have h2 : ∀ᵐ p ∂ν.prod ν', p.2 ∈ K' := by
    rw [ae_iff]
    have : {p : ℂ × ℂ | ¬p.2 ∈ K'} = univ ×ˢ K'ᶜ := by ext p; simp
    rw [this, Measure.prod_prod, hKc', mul_zero]
  have h3 : ∀ᵐ p ∂ν.prod ν', p.1 ≠ p.2 := by
    rw [ae_iff]
    have : {p : ℂ × ℂ | ¬p.1 ≠ p.2} = Set.diagonal ℂ := by ext p; simp [Set.diagonal]
    rw [this, Measure.prod_apply measurableSet_diagonal]
    have e : ∀ x : ℂ, ν' (Prod.mk x ⁻¹' Set.diagonal ℂ) = 0 := by
      intro x
      have : Prod.mk x ⁻¹' Set.diagonal ℂ = {x} := by ext y; simp [Set.diagonal, eq_comm]
      rw [this]; exact noAtoms_of_isAdmissibleH hν' x
    simp [e]
  filter_upwards [h1, h2, h3] with p hp1 hp2 hp3 using ⟨hKH hp1, hKH' hp2, hp3⟩

lemma kernelCov_eq_toReal {ν ν' : Measure ℂ} (hν : IsAdmissibleH ν) (hν' : IsAdmissibleH ν') :
    kernelCov greenH ν ν' = (∫⁻ x, ∫⁻ y, ENNReal.ofReal (greenH x y) ∂ν' ∂ν).toReal ∧
      ∫⁻ x, ∫⁻ y, ENNReal.ofReal (greenH x y) ∂ν' ∂ν < ⊤ := by
  have := hν.1; have := hν'.1
  have hint := integrable_greenH_prod hν hν'
  have hmeas : Measurable fun p : ℂ × ℂ => ENNReal.ofReal (greenH p.1 p.2) :=
    ENNReal.measurable_ofReal.comp measurable_greenH
  have hl : ∫⁻ x, ∫⁻ y, ENNReal.ofReal (greenH x y) ∂ν' ∂ν =
      ∫⁻ p, ENNReal.ofReal (greenH p.1 p.2) ∂ν.prod ν' := (lintegral_prod _ hmeas.aemeasurable).symm
  have hnn : 0 ≤ᵐ[ν.prod ν'] fun p => greenH p.1 p.2 := by
    filter_upwards [ae_prod_offdiag hν hν'] with p hp using greenH_nonneg hp.1 hp.2.1 hp.2.2
  refine ⟨?_, by rw [hl]; exact hint.lintegral_lt_top⟩
  have hp : ∫ p, greenH p.1 p.2 ∂(ν.prod ν') = ∫ x, ∫ y, greenH x y ∂ν' ∂ν := integral_prod _ hint
  unfold kernelCov
  rw [← hp, integral_eq_lintegral_of_nonneg_ae hnn hint.aestronglyMeasurable, hl]

/-! ## The comparison kernels -/

/-- Lower comparison kernel for `B(μ, σε)`. -/
def Lk (ε : ℝ) (x y : ℂ) : ℝ := Real.log ‖cε ε y - conj x‖ - Real.log (max ε ‖cε ε y - x‖)

lemma measurable_Lk (ε : ℝ) : Measurable fun p : ℂ × ℂ => Lk ε p.1 p.2 := by
  unfold Lk cε
  fun_prop

lemma norm_sub_conj_pos {x y : ℂ} (hx : x ∈ Hbar) (hy : y ∈ Hbar) (hxy : x ≠ y) :
    0 < ‖x - conj y‖ :=
  (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)).trans_le (norm_sub_le_norm_sub_conj hx hy)

lemma tendsto_Lk {x y : ℂ} (hx : x ∈ Hbar) (hy : y ∈ Hbar) (hxy : x ≠ y) :
    Tendsto (fun k : ℕ => Lk (1 / ((k : ℝ) + 1)) x y) atTop (𝓝 (greenH x y)) := by
  have hc : Continuous fun e : ℝ => cε e y := by unfold cε; fun_prop
  have h1 : ‖cε 0 y - conj x‖ ≠ 0 := by
    simpa [cε] using (norm_sub_conj_pos hy hx hxy.symm).ne'
  have h2 : max 0 ‖cε 0 y - x‖ ≠ 0 := by
    simp only [cε]; simp
    exact sub_ne_zero.mpr hxy.symm
  have hcont : ContinuousAt (fun e : ℝ => Lk e x y) 0 := by
    unfold Lk
    exact (((hc.sub continuous_const).norm.continuousAt).log h1).sub
      ((continuous_id.max (hc.sub continuous_const).norm).continuousAt.log h2)
  have hval : Lk 0 x y = greenH x y := by
    rw [greenH_symm]
    simp [Lk, cε, greenH, max_eq_right (norm_nonneg _)]
  rw [← hval]
  exact hcont.tendsto.comp tendsto_one_div_add_atTop_nhds_zero_nat

lemma tendsto_Uk {x y : ℂ} (hx : x ∈ Hbar) (hy : y ∈ Hbar) (hxy : x ≠ y) :
    Tendsto (fun k : ℕ => greenH (cε (1 / ((k : ℝ) + 1)) x) (cε (1 / ((k : ℝ) + 1)) y)) atTop
      (𝓝 (greenH x y)) := by
  have hc : ∀ z, Continuous fun e : ℝ => cε e z := fun z => by unfold cε; fun_prop
  have h1 : ‖cε 0 x - conj (cε 0 y)‖ ≠ 0 := by
    simpa [cε] using (norm_sub_conj_pos hx hy hxy).ne'
  have h2 : ‖cε 0 x - cε 0 y‖ ≠ 0 := by
    simpa [cε] using (norm_pos_iff.mpr (sub_ne_zero.mpr hxy)).ne'
  have hcont : ContinuousAt (fun e : ℝ => greenH (cε e x) (cε e y)) 0 := by
    unfold greenH
    exact ((((hc x).sub (Complex.continuous_conj.comp (hc y))).norm.continuousAt).log h1).sub
      ((((hc x).sub (hc y)).norm.continuousAt).log h2)
  have hval : greenH (cε 0 x) (cε 0 y) = greenH x y := by simp [cε]
  rw [← hval]
  exact hcont.tendsto.comp tendsto_one_div_add_atTop_nhds_zero_nat

/-! ## H4 -/

/-- **H4.** Admissible measures are `B`-limits of the smooth measures `σε μ ε`. -/
theorem exists_σε_close {μ : Measure ℂ} (hμ : IsAdmissibleH μ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ kernelCov2 greenH (μ, σε μ ε) (μ, σε μ ε) < δ := by
  obtain ⟨hμf, ⟨K, hK, hKH, hKc⟩, Cp, hCp, hpot⟩ := id hμ
  have := hμf
  set e : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with he
  have he0 : ∀ k, 0 < e k := fun k => Nat.one_div_pos_of_nat
  have he1 : ∀ k, e k ≤ 1 := fun k => by
    rw [he]; exact div_le_one_of_le₀ (by linarith [(k.cast_nonneg : (0 : ℝ) ≤ k)]) (by positivity)
  obtain ⟨hb_eq, hBμ_lt⟩ := kernelCov_eq_toReal hμ hμ
  set Bμ := ∫⁻ x, ∫⁻ y, ENNReal.ofReal (greenH x y) ∂μ ∂μ with hBμ
  set b := kernelCov greenH μ μ with hbdef
  have hb0 : 0 ≤ b := by rw [hb_eq]; exact ENNReal.toReal_nonneg
  have hBμ_eq : Bμ = ENNReal.ofReal b := by rw [hb_eq, ENNReal.ofReal_toReal hBμ_lt.ne]
  have hae := ae_prod_offdiag hμ hμ
  have hμK : ∀ᵐ y ∂μ, y ∈ K := ae_iff.2 hKc
  have hGm : Measurable fun p : ℂ × ℂ => ENNReal.ofReal (greenH p.1 p.2) :=
    ENNReal.measurable_ofReal.comp measurable_greenH
  have hBμ_prod : Bμ = ∫⁻ p, ENNReal.ofReal (greenH p.1 p.2) ∂μ.prod μ := by
    rw [hBμ, lintegral_prod _ hGm.aemeasurable]
  -- lower bound for `B(μ, σε)`
  have hlow : ∀ k, ∫⁻ p, ENNReal.ofReal (Lk (e k) p.1 p.2) ∂μ.prod μ ≤
      ∫⁻ x, ∫⁻ b, ENNReal.ofReal (greenH x b) ∂σε μ (e k) ∂μ := by
    intro k
    rw [lintegral_prod (f := fun p : ℂ × ℂ => ENNReal.ofReal (Lk (e k) p.1 p.2))
      (ENNReal.measurable_ofReal.comp (measurable_Lk _)).aemeasurable]
    refine lintegral_mono_ae ?_
    filter_upwards [hμK] with x hx
    rw [lintegral_σε (g := fun b => ENNReal.ofReal (greenH x b)) (he0 k) (ENNReal.measurable_ofReal.comp (measurable_greenH_left x))]
    refine lintegral_mono_ae ?_
    filter_upwards [hμK] with y hy
    have hy' : (0 : ℝ) ≤ y.im := hKH hy
    exact Kε_ge (he0 k) (hKH hx) (by rw [cε_im]; linarith)
  have hfatou : Bμ ≤ liminf (fun k => ∫⁻ p, ENNReal.ofReal (Lk (e k) p.1 p.2) ∂μ.prod μ) atTop := by
    calc Bμ = ∫⁻ p, ENNReal.ofReal (greenH p.1 p.2) ∂μ.prod μ := hBμ_prod
      _ = ∫⁻ p, liminf (fun k => ENNReal.ofReal (Lk (e k) p.1 p.2)) atTop ∂μ.prod μ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae] with p hp
          exact ((ENNReal.tendsto_ofReal (tendsto_Lk hp.1 hp.2.1 hp.2.2)).liminf_eq).symm
      _ ≤ _ := lintegral_liminf_le fun k => ENNReal.measurable_ofReal.comp (measurable_Lk _)
  -- upper bound for `B(σε, σε)`
  have hup : ∀ k, ∫⁻ a, ∫⁻ b, ENNReal.ofReal (greenH a b) ∂σε μ (e k) ∂σε μ (e k) ≤
      ∫⁻ p, ENNReal.ofReal (greenH (cε (e k) p.1) (cε (e k) p.2)) ∂μ.prod μ := by
    intro k
    have hε := he0 k
    have hmK : Measurable fun q : ℂ × ℂ => Kε (e k) q.1 (cε (e k) q.2) := by
      have hf : Measurable fun r : (ℂ × ℂ) × ℂ => ENNReal.ofReal (greenH r.1.1 r.2) *
          ENNReal.ofReal (ηε (e k) (r.2 - cε (e k) r.1.2)) := by
        have hg1 : Measurable fun p : ℂ × ℂ => greenH p.1 p.2 := measurable_greenH
        have hg2 := (contDiff_ηε (e k)).continuous.measurable
        have hg3 := (continuous_cε (e k)).measurable
        fun_prop
      exact hf.lintegral_prod_right' (ν := volume)
    have hUm : Measurable fun p : ℂ × ℂ =>
        ENNReal.ofReal (greenH (cε (e k) p.1) (cε (e k) p.2)) := by
      have hg1 : Measurable fun p : ℂ × ℂ => greenH p.1 p.2 := measurable_greenH
      have hg3 := (continuous_cε (e k)).measurable
      fun_prop
    haveI : SFinite (σε μ (e k)) := by unfold σε; infer_instance
    calc ∫⁻ a, ∫⁻ b, ENNReal.ofReal (greenH a b) ∂σε μ (e k) ∂σε μ (e k)
        = ∫⁻ a, ∫⁻ y, Kε (e k) a (cε (e k) y) ∂μ ∂σε μ (e k) :=
          lintegral_congr fun a => by
            rw [lintegral_σε (g := fun b => ENNReal.ofReal (greenH a b)) hε
              (ENNReal.measurable_ofReal.comp (measurable_greenH_left a))]
            simp only [Kε]
      _ = ∫⁻ y, ∫⁻ a, Kε (e k) a (cε (e k) y) ∂σε μ (e k) ∂μ :=
          lintegral_lintegral_swap hmK.aemeasurable
      _ ≤ ∫⁻ y, ∫⁻ a, ENNReal.ofReal (greenH (cε (e k) y) a) ∂σε μ (e k) ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hμK] with y hy
          have hy' : (0 : ℝ) ≤ y.im := hKH hy
          refine lintegral_mono_ae ?_
          filter_upwards [σε_ae_Hbar hμ hε, σε_ae_ne (cε (e k) y)] with a ha hne
          exact Kε_le hε ha (by rw [cε_im]; linarith) hne
      _ = ∫⁻ y, ∫⁻ x, Kε (e k) (cε (e k) y) (cε (e k) x) ∂μ ∂μ :=
          lintegral_congr fun y => by
            rw [lintegral_σε (g := fun b => ENNReal.ofReal (greenH (cε (e k) y) b)) hε
              (ENNReal.measurable_ofReal.comp (measurable_greenH_left _))]
            simp only [Kε]
      _ ≤ ∫⁻ y, ∫⁻ x, ENNReal.ofReal (greenH (cε (e k) x) (cε (e k) y)) ∂μ ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards [hμK] with y hy
          have hy' : (0 : ℝ) ≤ y.im := hKH hy
          refine lintegral_mono_ae ?_
          filter_upwards [hμK, ae_ne_of_admissible hμ y] with x hx hxy
          have hx' : (0 : ℝ) ≤ x.im := hKH hx
          refine Kε_le hε (show (0 : ℝ) ≤ (cε (e k) y).im by rw [cε_im]; linarith)
            (by rw [cε_im]; linarith) ?_
          intro h
          exact hxy (add_right_cancel h).symm
      _ = _ := (lintegral_prod_symm _ hUm.aemeasurable).symm
  -- dominated convergence for the upper bound
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  have hdct : Tendsto (fun k => ∫⁻ p, ENNReal.ofReal (greenH (cε (e k) p.1) (cε (e k) p.2))
      ∂μ.prod μ) atTop (𝓝 Bμ) := by
    rw [hBμ_prod]
    have hK2 : ∀ᵐ p ∂μ.prod μ, p.1 ∈ K ∧ p.2 ∈ K := by
      have h1 : ∀ᵐ p ∂μ.prod μ, p.1 ∈ K := by
        rw [ae_iff]
        have : {p : ℂ × ℂ | ¬p.1 ∈ K} = Kᶜ ×ˢ univ := by ext p; simp
        rw [this, Measure.prod_prod, hKc, zero_mul]
      have h2 : ∀ᵐ p ∂μ.prod μ, p.2 ∈ K := by
        rw [ae_iff]
        have : {p : ℂ × ℂ | ¬p.2 ∈ K} = univ ×ˢ Kᶜ := by ext p; simp
        rw [this, Measure.prod_prod, hKc, mul_zero]
      filter_upwards [h1, h2] with p a b using ⟨a, b⟩
    refine tendsto_lintegral_of_dominated_convergence
      (fun p => ENNReal.ofReal (Real.log (2 * R + 4)) + ENNReal.ofReal (-Real.log ‖p.1 - p.2‖))
      (fun k => by
        have hg1 : Measurable fun p : ℂ × ℂ => greenH p.1 p.2 := measurable_greenH
        have hg3 := (continuous_cε (e k)).measurable
        fun_prop) (fun k => ?_) ?_ ?_
    · filter_upwards [hK2] with p hp
      have hx : ‖p.1‖ ≤ R := by simpa using hR hp.1
      have hy : ‖p.2‖ ≤ R := by simpa using hR hp.2
      have hx' : (0 : ℝ) ≤ p.1.im := hKH hp.1
      have hy' : (0 : ℝ) ≤ p.2.im := hKH hp.2
      have hek := he0 k
      have hek1 := he1 k
      have hsub : cε (e k) p.1 - cε (e k) p.2 = p.1 - p.2 := by simp [cε]
      have hpos : 0 < ‖cε (e k) p.1 - conj (cε (e k) p.2)‖ := by
        have h1 := Complex.im_le_norm (cε (e k) p.1 - conj (cε (e k) p.2))
        have h2 : (cε (e k) p.1 - conj (cε (e k) p.2)).im = p.1.im + p.2.im + 4 * e k := by
          simp [cε]; ring
        linarith
      have hle : ‖cε (e k) p.1 - conj (cε (e k) p.2)‖ ≤ 2 * R + 4 := by
        have e1 : cε (e k) p.1 - conj (cε (e k) p.2) =
            p.1 - conj p.2 + ((4 * e k : ℝ) : ℂ) * Complex.I := by
          apply Complex.ext <;> simp [cε] <;> ring
        rw [e1]
        calc ‖p.1 - conj p.2 + ((4 * e k : ℝ) : ℂ) * Complex.I‖
            ≤ ‖p.1‖ + ‖conj p.2‖ + ‖((4 * e k : ℝ) : ℂ) * Complex.I‖ :=
              (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
          _ ≤ 2 * R + 4 := by
              rw [Complex.norm_conj, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
                Real.norm_eq_abs, abs_of_pos (by positivity)]
              linarith
      have hlog := Real.log_le_log hpos hle
      calc ENNReal.ofReal (greenH (cε (e k) p.1) (cε (e k) p.2))
          ≤ ENNReal.ofReal (Real.log (2 * R + 4) + -Real.log ‖p.1 - p.2‖) := by
            refine ENNReal.ofReal_le_ofReal ?_
            unfold greenH
            rw [hsub]
            linarith
        _ ≤ _ := ENNReal.ofReal_add_le
    · rw [lintegral_add_left (measurable_const), lintegral_const]
      refine ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (measure_ne_top _ _), ?_⟩
      rw [lintegral_prod_symm (fun a : ℂ × ℂ => ENNReal.ofReal (-Real.log ‖a.1 - a.2‖)) ((ENNReal.measurable_ofReal.comp
        (Real.measurable_log.comp (measurable_fst.sub measurable_snd).norm).neg).aemeasurable)]
      refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hCp.ne (measure_ne_top μ univ)) ?_
      calc ∫⁻ y, ∫⁻ x, ENNReal.ofReal (-Real.log ‖(x, y).1 - (x, y).2‖) ∂μ ∂μ
          ≤ ∫⁻ _, Cp ∂μ := lintegral_mono fun y => hpot y
        _ = Cp * μ univ := lintegral_const Cp
    · filter_upwards [hae] with p hp
      exact ENNReal.tendsto_ofReal (tendsto_Uk hp.1 hp.2.1 hp.2.2)
  -- combine
  have hev1 : ∀ᶠ k in atTop, ENNReal.ofReal (b - δ / 4) ≤
      ∫⁻ x, ∫⁻ y, ENNReal.ofReal (greenH x y) ∂σε μ (e k) ∂μ := by
    by_cases hb : b - δ / 4 ≤ 0
    · exact Eventually.of_forall fun k => by rw [ENNReal.ofReal_of_nonpos hb]; exact bot_le
    · have hlt : ENNReal.ofReal (b - δ / 4) <
          liminf (fun k => ∫⁻ p, ENNReal.ofReal (Lk (e k) p.1 p.2) ∂μ.prod μ) atTop := by
        refine lt_of_lt_of_le ?_ hfatou
        rw [hBμ_eq]
        exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
      filter_upwards [eventually_lt_of_lt_liminf hlt] with k hk
      exact hk.le.trans (hlow k)
  have hev2 : ∀ᶠ k in atTop, ∫⁻ a, ∫⁻ b, ENNReal.ofReal (greenH a b) ∂σε μ (e k) ∂σε μ (e k) <
      ENNReal.ofReal (b + δ / 4) := by
    have hlt : Bμ < ENNReal.ofReal (b + δ / 4) := by
      rw [hBμ_eq]; exact (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
    filter_upwards [hdct.eventually (gt_mem_nhds hlt)] with k hk
    exact (hup k).trans_lt hk
  obtain ⟨k, hk1, hk2⟩ := (hev1.and hev2).exists
  refine ⟨e k, he0 k, ?_⟩
  have hσ := isAdmissibleH_σε hμ (he0 k)
  obtain ⟨h1, h1lt⟩ := kernelCov_eq_toReal hμ hσ
  obtain ⟨h2, -⟩ := kernelCov_eq_toReal hσ hσ
  have hsym := ZeroReg.kernelCov_greenH_symm hσ hμ
  have r1 : b - δ / 4 ≤ kernelCov greenH μ (σε μ (e k)) := by
    rw [h1]; exact (ENNReal.ofReal_le_iff_le_toReal h1lt.ne).mp hk1
  have r2 : kernelCov greenH (σε μ (e k)) (σε μ (e k)) ≤ b + δ / 4 := by
    rw [h2]; exact ENNReal.toReal_le_of_le_ofReal (by linarith) hk2.le
  unfold kernelCov2
  simp only
  rw [hsym]
  linarith

end QuantumZipper.K3
