/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cM.Cert at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4FO.Events
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.LocalAreaCertBorel
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4cM.Cond

/-!
# A countable Borel certificate for the local GMC vague limit

Source: [18], Lemma 4.3: the GMC area on `V` is
determined by `h|_V`.

For an open `V ⊆ 𝔻`, a field `h` and a candidate measure `ν` on `V`, `L43MCert γ V h ν` is a countable
condition: MoTPort's certificate `ConeArea4.AreaCert` for the approximations of `h` translated by
`upJ : z ↦ z + 2i` (which moves `𝔻` into the upper half plane, where the dense test family
`GMCIdent3.denseF` lives), finiteness of `ν` on the cut sets, and convergence of the countably many tests
`openBump · g` (`g ∈ denseF`) to their `ν`-integrals.

* `isVagueLimitOn_of_cert`: the certificate implies that `ν` is the vague limit on `V` of the dyadic
  approximations of `h` (MoTPort's `areaGood_of_cert` gives some limit `ν₀`; `integral_eq_of_agree` shows that
  `ν₀` and `ν` have the same integrals against every test function);
* `cert_of_isVagueLimitOn`: conversely, a vague limit with eventually finite approximations on `closure V`;
* `isVagueLimitOn_of_restrictTo_eq`: local vague limits only depend on `h|_V`;
* `measurableSet_l43mCert`: the certificate for `ν = (e_* Leb)|_V` is a Borel condition on `(h, e)`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology TopologicalSpace
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4cM

open MatedCRTHarmonic LQGMetric QuantumZipper MatedCRTHarmonic.MoTPort

/-! ### The translation into the upper half plane -/

/-- The translation `z ↦ z + 2i`. -/
def upJ : ℂ ≃ₜ ℂ := Homeomorph.addRight (2 * Complex.I)

@[simp] theorem upJ_apply (z : ℂ) : upJ z = z + 2 * Complex.I := rfl

theorem upJ_image_subset_H {V : Set ℂ} (hV : V ⊆ ball (0 : ℂ) 1) : upJ '' V ⊆ QuantumZipper.H := by
  rintro _ ⟨w, hw, rfl⟩
  have hw' := hV hw
  rw [mem_ball, dist_zero_right] at hw'
  have him : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
  have h2 : (w + 2 * Complex.I).im = w.im + 2 := by simp
  show 0 < (upJ w).im
  rw [upJ_apply, h2]
  linarith [neg_abs_le w.im]

theorem isBounded_upJ_image {V : Set ℂ} (hV : V ⊆ ball (0 : ℂ) 1) :
    Bornology.IsBounded (upJ '' V) := by
  refine (isBounded_ball (x := 2 * Complex.I) (r := 1)).subset ?_
  rintro _ ⟨w, hw, rfl⟩
  have hw' := hV hw
  rw [mem_ball, dist_zero_right] at hw'
  rw [mem_ball, dist_eq_norm, upJ_apply, add_sub_cancel_right]
  exact hw'
theorem upJ_image_compl_nonempty {V : Set ℂ} (hV : V ⊆ ball (0 : ℂ) 1) : (upJ '' V)ᶜ.Nonempty :=
  ⟨0, fun h0 => by
    have := upJ_image_subset_H hV h0
    simp [QuantumZipper.H] at this⟩

theorem isOpen_upJ_image {V : Set ℂ} (hV : IsOpen V) : IsOpen (upJ '' V) := upJ.isOpenMap V hV

theorem upJ_symm_image_image (V : Set ℂ) : upJ.symm '' (upJ '' V) = V := by
  rw [← image_comp, Homeomorph.symm_comp_self, image_id]

theorem map_upJ_map_symm (μ : Measure ℂ) : (μ.map upJ).map upJ.symm = μ := by
  rw [Measure.map_map upJ.symm.measurable upJ.measurable, Homeomorph.symm_comp_self, Measure.map_id]

theorem preimage_upJ_subset {V K : Set ℂ} (hK : K ⊆ upJ '' V) : upJ ⁻¹' K ⊆ V := by
  intro z hz
  obtain ⟨w, hw, hwz⟩ := hK hz
  rwa [← upJ.injective hwz]

/-! ### The certificate -/

/-- The dyadic approximations of `h`, translated by `upJ`. -/
def shApprox (γ : ℝ) (h : DistC) (k : ℕ) : Measure ℂ := (CellScaling.lqgAreaApprox γ h k).map upJ

/-- **The countable certificate** that `ν` is the vague limit on `V` of the dyadic approximations of `h`. -/
def L43MCert (γ : ℝ) (V : Set ℂ) (h : DistC) (ν : Measure ℂ) : Prop :=
  ConeArea4.AreaCert (upJ '' V) (shApprox γ h) ∧
    (∀ n : ℕ, ν.map upJ (ConeArea4.cutSet (upJ '' V) n) < ⊤) ∧
    ∀ n : ℕ, ∀ g ∈ GMCIdent3.denseF,
      Tendsto (fun k => ∫ z, LQGMeas.openBump (upJ '' V) n z * g z ∂(shApprox γ h k)) atTop
        (𝓝 (∫ z, LQGMeas.openBump (upJ '' V) n z * g z ∂(ν.map upJ)))
/-- Two measures, finite on the compact subsets of `U`, with the same integrals against the countable family
`openBump U n · g` (`g ∈ denseF`), have the same integrals against every test function supported in `U`. -/
theorem integral_eq_of_agree {U : Set ℂ} (hU : IsOpen U) (hUH : U ⊆ QuantumZipper.H)
    (hUc : Uᶜ.Nonempty) (hUb : Bornology.IsBounded U) {m₁ m₂ : Measure ℂ}
    (hfin₁ : ∀ K, IsCompact K → K ⊆ U → m₁ K < ⊤) (hfin₂ : ∀ K, IsCompact K → K ⊆ U → m₂ K < ⊤)
    (hagree : ∀ n : ℕ, ∀ g ∈ GMCIdent3.denseF,
      ∫ z, LQGMeas.openBump U n z * g z ∂m₁ = ∫ z, LQGMeas.openBump U n z * g z ∂m₂)
    {f : ℂ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f) (hfU : tsupport f ⊆ U) :
    ∫ z, f z ∂m₁ = ∫ z, f z ∂m₂ := by
  obtain ⟨K, -, -, hfK, ⟨φ, hφF, hφ0, hφ1⟩, happrox⟩ :=
    GMCIdent3.denseF_dense.2 f ⟨hf, hfc, hfU.trans hUH⟩
  obtain ⟨n, -, hn⟩ := ConeArea4.exists_cutSet hU hUc hfc hfU
  set b := LQGMeas.openBump U n with hbdef
  have hb0 : ∀ z, 0 ≤ b z := LQGMeas.openBump_nonneg U n
  have hbc : Continuous b := LQGMeas.continuous_openBump U n
  have hbs : HasCompactSupport b := LQGMeas.hasCompactSupport_openBump hUb n
  have hbU : tsupport b ⊆ U := LQGMeas.tsupport_openBump_subset U n
  have hfeq : (fun z => f z) = fun z => b z * f z := by
    funext z
    by_cases hz : z ∈ tsupport f
    · rw [hn z hz, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]
  have hint : ∀ (m : Measure ℂ), (∀ K, IsCompact K → K ⊆ U → m K < ⊤) →
      ∀ {g : ℂ → ℝ}, Continuous g → Integrable (fun z => b z * g z) m := fun m hm g hg =>
    GoodSample.integrable_of_tsupport hm (hbc.mul hg) hbs.mul_right
      (tsupport_mul_subset_left.trans hbU)
  have hφc : Continuous φ := (GMCIdent3.denseF_dense.1 φ hφF).1
  have key : ∀ (m : Measure ℂ), (∀ K, IsCompact K → K ⊆ U → m K < ⊤) → ∀ η : ℝ, 0 < η →
      ∀ g ∈ GMCIdent3.denseF, tsupport g ⊆ K → (∀ z, |f z - g z| ≤ η) →
        |∫ z, f z ∂m - ∫ z, b z * g z ∂m| ≤ η * ∫ z, b z * φ z ∂m := by
    intro m hm η hη g hgF hgK hfg
    have hgc : Continuous g := (GMCIdent3.denseF_dense.1 g hgF).1
    have e1 : ∫ z, f z ∂m = ∫ z, b z * f z ∂m := congrArg (fun F : ℂ → ℝ => ∫ z, F z ∂m) hfeq
    have e2 : (∫ z, b z * f z ∂m) - ∫ z, b z * g z ∂m = ∫ z, (b z * f z - b z * g z) ∂m :=
      (integral_sub (hint m hm hf) (hint m hm hgc)).symm
    have e3 : η * ∫ z, b z * φ z ∂m = ∫ z, η * (b z * φ z) ∂m :=
      (integral_const_mul (μ := m) η (fun z => b z * φ z)).symm
    rw [e1, e2, e3, ← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le ((hint m hm hφc).const_mul η) (Eventually.of_forall fun z => ?_)
    rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg (hb0 z)]
    by_cases hzK : z ∈ K
    · have h1 : |f z - g z| ≤ η * φ z := (hfg z).trans (le_mul_of_one_le_right hη.le (hφ1 z hzK))
      calc b z * |f z - g z| ≤ b z * (η * φ z) := mul_le_mul_of_nonneg_left h1 (hb0 z)
        _ = η * (b z * φ z) := by ring
    · have hf0 : f z = 0 := image_eq_zero_of_notMem_tsupport fun h => hzK (hfK h)
      have hg0 : g z = 0 := image_eq_zero_of_notMem_tsupport fun h => hzK (hgK h)
      rw [hf0, hg0, sub_zero, abs_zero, mul_zero]
      exact mul_nonneg hη.le (mul_nonneg (hb0 z) (hφ0 z))
  set C := (∫ z, b z * φ z ∂m₁) + ∫ z, b z * φ z ∂m₂ with hC
  have hC0 : 0 ≤ C := add_nonneg (integral_nonneg fun z => mul_nonneg (hb0 z) (hφ0 z))
    (integral_nonneg fun z => mul_nonneg (hb0 z) (hφ0 z))
  refine eq_of_forall_dist_le fun ε hε => ?_
  set η := ε / (C + 1) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨g, hgF, hgK, hfg⟩ := happrox η hη0
  have h1 := key m₁ hfin₁ η hη0 g hgF hgK hfg
  have h2 := key m₂ hfin₂ η hη0 g hgF hgK hfg
  have h3 := hagree n g hgF
  rw [← hbdef] at h3
  have hηC : η * C ≤ ε := by
    rw [hη, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  rw [Real.dist_eq]
  calc |∫ z, f z ∂m₁ - ∫ z, f z ∂m₂|
      = |(∫ z, f z ∂m₁ - ∫ z, b z * g z ∂m₁) - (∫ z, f z ∂m₂ - ∫ z, b z * g z ∂m₂)| := by
        rw [h3]; congr 1; ring
    _ ≤ |∫ z, f z ∂m₁ - ∫ z, b z * g z ∂m₁| + |∫ z, f z ∂m₂ - ∫ z, b z * g z ∂m₂| := abs_sub _ _
    _ ≤ η * ∫ z, b z * φ z ∂m₁ + η * ∫ z, b z * φ z ∂m₂ := add_le_add h1 h2
    _ = η * C := by rw [hC]; ring
    _ ≤ ε := hηC

/-- **The certificate gives the local vague limit.** -/
theorem isVagueLimitOn_of_cert {γ : ℝ} {V : Set ℂ} (hVo : IsOpen V) (hV : V ⊆ ball (0 : ℂ) 1)
    {h : DistC} {ν : Measure ℂ} (hν0 : ν Vᶜ = 0) (hc : L43MCert γ V h ν) :
    IsVagueLimitOn V (CellScaling.lqgAreaApprox γ h) ν := by
  have hUo : IsOpen (upJ '' V) := isOpen_upJ_image hVo
  have hUH := upJ_image_subset_H hV
  have hUc := upJ_image_compl_nonempty hV
  have hUb := isBounded_upJ_image hV
  obtain ⟨⟨ν₀, hν₀⟩, -⟩ := ConeArea4.areaGood_of_cert hUo hUH hUc hc.1
  have hfinJ : ∀ K, IsCompact K → K ⊆ upJ '' V → ν.map upJ K < ⊤ := fun K hK hKU => by
    obtain ⟨n, hn, -⟩ := ConeArea4.exists_cutSet hUo hUc hK hKU
    exact (measure_mono hn).trans_lt (hc.2.1 n)
  have hVL : IsVagueLimitOn (upJ '' V) (shApprox γ h) (ν.map upJ) := by
    refine ⟨?_, hfinJ, fun f hf hfc hfU => ?_⟩
    · rw [Measure.map_apply upJ.measurable hUo.measurableSet.compl, preimage_compl,
        upJ.preimage_image]
      exact hν0
    · have hagree : ∀ n : ℕ, ∀ g ∈ GMCIdent3.denseF,
          ∫ z, LQGMeas.openBump (upJ '' V) n z * g z ∂ν₀ =
            ∫ z, LQGMeas.openBump (upJ '' V) n z * g z ∂(ν.map upJ) := by
        intro n g hg
        have hgc : Continuous g := (GMCIdent3.denseF_dense.1 g hg).1
        exact tendsto_nhds_unique (hν₀.2.2 _ ((LQGMeas.continuous_openBump _ n).mul hgc)
          (LQGMeas.hasCompactSupport_openBump hUb n).mul_right
          (tsupport_mul_subset_left.trans (LQGMeas.tsupport_openBump_subset _ n))) (hc.2.2 n g hg)
      have heq := integral_eq_of_agree hUo hUH hUc hUb hν₀.2.1 hfinJ hagree hf hfc hfU
      rw [← heq]
      exact hν₀.2.2 f hf hfc hfU
  have hback := LQGCone.isVagueLimitOn_map_homeomorph hUo hVL upJ.symm
  rw [upJ_symm_image_image, map_upJ_map_symm] at hback
  simpa only [shApprox, map_upJ_map_symm] using hback

/-- **A local vague limit with eventually finite approximations on `closure V` satisfies the certificate.** -/
theorem cert_of_isVagueLimitOn {γ : ℝ} {V : Set ℂ} (hVo : IsOpen V) (hV : V ⊆ ball (0 : ℂ) 1)
    {h : DistC} {ν : Measure ℂ} (hvl : IsVagueLimitOn V (CellScaling.lqgAreaApprox γ h) ν)
    (hfin : ∀ᶠ k in atTop, CellScaling.lqgAreaApprox γ h k (closure V) < ⊤) :
    L43MCert γ V h ν := by
  have hUb := isBounded_upJ_image hV
  have hVL : IsVagueLimitOn (upJ '' V) (shApprox γ h) (ν.map upJ) :=
    LQGCone.isVagueLimitOn_map_homeomorph hVo hvl upJ
  have hgood : ConeArea4.AreaGood (upJ '' V) (shApprox γ h) := by
    refine ⟨⟨ν.map upJ, hVL⟩, fun K hK hKU => ?_⟩
    filter_upwards [hfin] with k hk
    rw [shApprox, Measure.map_apply upJ.measurable hK.measurableSet]
    exact (measure_mono ((preimage_upJ_subset hKU).trans subset_closure)).trans_lt hk
  refine ⟨ConeArea4.cert_of_areaGood hUb hgood, fun n => hVL.2.1 _ (ConeArea4.isCompact_cutSet hUb n)
    (ConeArea4.cutSet_subset _ n), fun n g hg => ?_⟩
  have hgc : Continuous g := (GMCIdent3.denseF_dense.1 g hg).1
  exact hVL.2.2 _ ((LQGMeas.continuous_openBump _ n).mul hgc)
    (LQGMeas.hasCompactSupport_openBump hUb n).mul_right
    (tsupport_mul_subset_left.trans (LQGMeas.tsupport_openBump_subset _ n))

/-- **Local vague limits only depend on the restricted field** (the argument of the
`isVagueLimitOn_eq_restrict`, without a global limit). -/
theorem isVagueLimitOn_of_restrictTo_eq {γ : ℝ} {V : Opens ℂ} {h h' : DistC}
    (hres : restrictTo V h' = restrictTo V h) {ν : Measure ℂ}
    (hν : IsVagueLimitOn (V : Set ℂ) (CellScaling.lqgAreaApprox γ h') ν) :
    IsVagueLimitOn (V : Set ℂ) (CellScaling.lqgAreaApprox γ h) ν := by
  refine ⟨hν.1, hν.2.1, fun g hg hgc hgV => ?_⟩
  have hK : IsCompact (tsupport g) := hgc
  obtain ⟨δ, hδ, hδV⟩ : ∃ δ > 0, thickening (2 * δ) (tsupport g) ⊆ V := by
    rcases (tsupport g).eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, by rw [he, thickening_empty]; exact empty_subset _⟩
    obtain ⟨δ, hδ, hsub⟩ := hK.exists_thickening_subset_open V.isOpen hgV
    exact ⟨δ / 2, by positivity, by rw [show 2 * (δ / 2) = δ by ring]; exact hsub⟩
  set W : Opens ℂ := ⟨thickening δ (tsupport g), isOpen_thickening⟩
  have hWδ : (GMS4c.thickOpen W δ : Set ℂ) ⊆ V := by
    intro x hx
    apply hδV
    obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.1 hx
    obtain ⟨w, hw, hyw⟩ := mem_thickening_iff.1 hy
    exact mem_thickening_iff.2 ⟨w, hw, by
      calc dist x w ≤ dist x y + dist y w := dist_triangle _ _ _
        _ < δ + δ := add_lt_add hxy hyw
        _ = 2 * δ := by ring⟩
  have hres' : restrictTo (GMS4c.thickOpen W δ) h' = restrictTo (GMS4c.thickOpen W δ) h :=
    GMS4FO.restrictTo_eq_of_le hWδ hres
  obtain ⟨K, hKk⟩ := QuantumZipper.AtomlessUncond.exists_radius_lt hδ
  have happrox : ∀ k, K ≤ k →
      (CellScaling.lqgAreaApprox γ h' k).restrict W = (CellScaling.lqgAreaApprox γ h k).restrict W := by
    intro k hk
    have hsmall : CellScaling.dyadicScale k < δ := by
      rw [LQGCone.dyadicScale_eq_radius]
      exact hKk k hk
    rw [← GMS4c.localAreaApprox_restrictTo γ W δ h' k hsmall,
      ← GMS4c.localAreaApprox_restrictTo γ W δ h k hsmall, hres']
  have hgW : tsupport g ⊆ (W : Set ℂ) := self_subset_thickening hδ _
  have hg0 : ∀ z ∉ (W : Set ℂ), g z = 0 :=
    fun z hz => image_eq_zero_of_notMem_tsupport fun hzs => hz (hgW hzs)
  have hevent : (fun k => ∫ z, g z ∂(CellScaling.lqgAreaApprox γ h' k)) =ᶠ[atTop]
      (fun k => ∫ z, g z ∂(CellScaling.lqgAreaApprox γ h k)) := by
    filter_upwards [eventually_ge_atTop K] with k hk
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := CellScaling.lqgAreaApprox γ h' k) hg0,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero (μ := CellScaling.lqgAreaApprox γ h k) hg0,
      happrox k hk]
  exact (hν.2.2 g hg hgc hgV).congr' hevent

/-! ### Measurability -/

/-- The dyadic approximations are a Borel function of the field. -/
theorem measurable_lqgAreaApprox (γ : ℝ) (k : ℕ) :
    Measurable fun h : DistC => CellScaling.lqgAreaApprox γ h k := by
  have h1 : Measurable fun p : DistC × ℂ => circleAvg p.1 (CellScaling.dyadicScale k) p.2 :=
    measurable_circleAvg.comp (f := fun p : DistC × ℂ => (p.1, CellScaling.dyadicScale k, p.2))
      (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
  have hd : Measurable fun p : DistC × ℂ => ENNReal.ofReal (CellScaling.dyadicScale k ^ (γ ^ 2 / 2) *
      Real.exp (γ * circleAvg p.1 (CellScaling.dyadicScale k) p.2)) :=
    ENNReal.measurable_ofReal.comp ((Real.measurable_exp.comp (h1.const_mul γ)).const_mul _)
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  have e : (fun h : DistC => CellScaling.lqgAreaApprox γ h k s) = fun h => ∫⁻ z in s,
      ENNReal.ofReal (CellScaling.dyadicScale k ^ (γ ^ 2 / 2) *
        Real.exp (γ * circleAvg h (CellScaling.dyadicScale k) z)) :=
    funext fun h => withDensity_apply _ hs
  rw [e]
  exact hd.lintegral_prod_right'

theorem measurable_shApprox (γ : ℝ) (k : ℕ) : Measurable fun h : DistC => shApprox γ h k :=
  (Measure.measurable_map _ upJ.measurable).comp (measurable_lqgAreaApprox γ k)

theorem measurable_integral_shApprox (γ : ℝ) (k : ℕ) {G : ℂ → ℝ} (hG : Continuous G) :
    Measurable fun h : DistC => ∫ z, G z ∂(shApprox γ h k) := by
  have e : (fun h : DistC => ∫ z, G z ∂(shApprox γ h k)) =
      fun h => ∫ z, (G ∘ upJ) z ∂(MoTPort.areaApproxC γ h k) := by
    funext h
    rw [shApprox, integral_map upJ.measurable.aemeasurable hG.aestronglyMeasurable,
      LQGCone.lqgAreaApprox_eq_areaApproxC]
    rfl
  rw [e]
  exact ConeArea4.measurable_integral_areaApproxC γ k (hG.comp upJ.continuous).measurable

theorem measurable_eval_pair : Measurable fun p : C(ℝ, ℂ) × ℝ => p.1 p.2 :=
  continuous_eval.measurable

/-- The translated local push-forward area of a set is Borel in the curve. -/
theorem measurable_locPush_apply {V : Set ℂ} (hV : MeasurableSet V) {S : Set ℂ} (hS : MeasurableSet S) :
    Measurable fun e : C(ℝ, ℂ) => ((volume.map e).restrict V).map upJ S := by
  have hT : MeasurableSet {p : C(ℝ, ℂ) × ℝ | p.1 p.2 ∈ upJ ⁻¹' S ∩ V} :=
    measurable_eval_pair ((upJ.measurable hS).inter hV)
  have heq : (fun e : C(ℝ, ℂ) => ((volume.map e).restrict V).map upJ S) =
      fun e => volume (Prod.mk e ⁻¹' {p : C(ℝ, ℂ) × ℝ | p.1 p.2 ∈ upJ ⁻¹' S ∩ V}) := by
    funext e
    rw [Measure.map_apply upJ.measurable hS, Measure.restrict_apply (upJ.measurable hS),
      Measure.map_apply e.continuous.measurable ((upJ.measurable hS).inter hV)]
    rfl
  rw [heq]
  exact measurable_measure_prodMk_left hT

/-- Integrals against the translated local push-forward area are Borel in the curve. -/
theorem measurable_integral_locPush {V : Set ℂ} (hV : MeasurableSet V) {G : ℂ → ℝ} (hG : Continuous G) :
    Measurable fun e : C(ℝ, ℂ) => ∫ z, G z ∂(((volume.map e).restrict V).map upJ) := by
  have hF : Measurable (V.indicator fun x => G (upJ x)) :=
    ((hG.comp upJ.continuous).measurable).indicator hV
  have heq : (fun e : C(ℝ, ℂ) => ∫ z, G z ∂(((volume.map e).restrict V).map upJ)) =
      fun e => ∫ u, V.indicator (fun x => G (upJ x)) (e u) ∂volume := by
    funext e
    rw [integral_map upJ.measurable.aemeasurable hG.aestronglyMeasurable,
      ← integral_indicator hV, integral_map e.continuous.measurable.aemeasurable
        hF.aestronglyMeasurable]
  rw [heq]
  exact (hF.comp measurable_eval_pair).stronglyMeasurable.integral_prod_right'.measurable

/-- **The certificate for the local push-forward area is a Borel condition on `(h, e)`.** -/
theorem measurableSet_l43mCert (γ : ℝ) {V : Set ℂ} (hV : MeasurableSet V) :
    MeasurableSet {x : DistC × C(ℝ, ℂ) | L43MCert γ V x.1 ((volume.map x.2).restrict V)} := by
  have hbg : ∀ n : ℕ, ∀ g ∈ GMCIdent3.denseF,
      Continuous fun z => LQGMeas.openBump (upJ '' V) n z * g z := fun n g hg =>
    (LQGMeas.continuous_openBump _ n).mul (GMCIdent3.denseF_dense.1 g hg).1
  have hA : MeasurableSet {h : DistC | ConeArea4.AreaCert (upJ '' V) (shApprox γ h)} :=
    GMS4c.measurableSet_areaCert_of_measurable (upJ '' V) (fun h => shApprox γ h)
      (measurable_shApprox γ) fun n g hg k => measurable_integral_shApprox γ k (hbg n g hg)
  unfold L43MCert
  simp only [ofPred_and, ofPred_forall]
  refine (hA.preimage measurable_fst).inter ((MeasurableSet.iInter fun n => ?_).inter
    (MeasurableSet.iInter fun n => MeasurableSet.biInter GMCIdent3.denseF_countable fun g hg => ?_))
  · exact measurableSet_lt ((measurable_locPush_apply hV
      (ConeArea4.isClosed_cutSet _ n).measurableSet).comp measurable_snd) measurable_const
  · have hseq : ∀ k : ℕ, Measurable fun x : DistC × C(ℝ, ℂ) =>
        (∫ z, LQGMeas.openBump (upJ '' V) n z * g z ∂(shApprox γ x.1 k)) -
          ∫ z, LQGMeas.openBump (upJ '' V) n z * g z ∂(((volume.map x.2).restrict V).map upJ) :=
      fun k => ((measurable_integral_shApprox γ k (hbg n g hg)).comp measurable_fst).sub
        ((measurable_integral_locPush hV (hbg n g hg)).comp measurable_snd)
    have := measurableSet_tendsto (l := atTop) (𝓝 (0 : ℝ)) hseq
    simp only [tendsto_sub_nhds_zero_iff] at this
    exact this

end MatedCRTHarmonic.GMS4cM
