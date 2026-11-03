/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Field.GreenFn at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Field.ZeroBoundary
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.KernelForm4
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.K3.GreenH

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The Green function of a simply connected domain `U ⊆ ℍ` (task P2-ZB, WP-14)

For an open `U ⊆ ℍ` and a conformal map `m : U → ℍ` (QZ `K3.IsConformalOnto m U H`), the
covariance of the zero-boundary GFF on `U` is given by the conformally transported Green function
of `ℍ`,
`G_U(x, y) = G_ℍ(m x, m y) = log |m x − conj (m y)| − log |m x − m y|`
(`= −log|x − y| + harmonic`; normalization `−ΔG = 2πδ`, as `logCov`):

`zeroGFFTestCov_eq_green` : `⟨φ, ψ⟩_{H⁻¹(U)} = ∫∫ φ(x) ψ(y) G_ℍ(m x, m y) dx dy`.

Source: Sheffield, *Gaussian free fields for mathematicians* (math/0312099), §2.2 (conformal
invariance) and §3 (Green function of ℍ); Berestycki–Powell arXiv:2404.16642 Ch. 1 (Green
function and conformal invariance). The diagonal (`ℝ≥0∞`) form for one non-negative bounded
density is QZ's `K3.dualNormSq_eq_kerInt` (QZ/Proofs/GFF/K3/KernelForm4.lean, node C2); here it
is polarized (symmetry of `G_ℍ`, QZ `greenH_symm`) and extended to signed test functions
`φ = φ⁺ − φ⁻` (own bookkeeping, no new mathematics). The square `(0,1)²` has such a map
(`GreenFnSquare.lean`, Riemann mapping theorem of QZ).
-/

noncomputable section

open MeasureTheory ProbabilityTheory TopologicalSpace Set Function
open scoped ENNReal

namespace LQGMetric

open QuantumZipper QuantumZipper.K3

variable {U : Set ℂ} {m : ℂ → ℂ}

lemma confKer_swap (p : ℂ × ℂ) : confKer m U p.swap = confKer m U p := by
  simp only [confKer, Prod.fst_swap, Prod.snd_swap, greenH_symm]

lemma kerInt_comm (u v : ℂ → ℝ≥0∞) : kerInt m U u v = kerInt m U v u := by
  unfold kerInt
  rw [← lintegral_prod_swap]
  refine lintegral_congr fun p => ?_
  simp only [kerDens, Prod.fst_swap, Prod.snd_swap, confKer_swap]
  ring

lemma kerInt_add_add (hm : IsConformalOnto m U H) {u v : ℂ → ℝ≥0∞} (hu : Measurable u)
    (hv : Measurable v) :
    kerInt m U (u + v) (u + v) =
      kerInt m U u u + kerInt m U u v + kerInt m U v u + kerInt m U v v := by
  unfold kerInt
  have e : ∀ p, kerDens m U (u + v) (u + v) p =
      kerDens m U u u p + kerDens m U u v p + kerDens m U v u p + kerDens m U v v p := by
    intro p
    simp only [kerDens, indicator_add', Pi.add_apply]
    ring
  simp_rw [e]
  have m1 := measurable_kerDens hm hu hu
  have m2 := measurable_kerDens hm hu hv
  have m3 := measurable_kerDens hm hv hu
  rw [lintegral_add_left (f := fun p => kerDens m U u u p + kerDens m U u v p + kerDens m U v u p)
      ((m1.add m2).add m3),
    lintegral_add_left (f := fun p => kerDens m U u u p + kerDens m U u v p) (m1.add m2),
    lintegral_add_left m1]

/-- polarized C2: `dualCov` of two bounded densities is the kernel integral -/
theorem dualCov_withDensity_eq_kerInt (hm : IsConformalOnto m U H) (hUH : U ⊆ H)
    {u v : ℂ → ℝ≥0∞} {M N : ℝ≥0∞} {R S : ℝ} (hu : BddDens u M R) (hv : BddDens v N S) :
    dualCov U (zeroSpace U) (volume.withDensity u) (volume.withDensity v) =
      (kerInt m U u v).toReal := by
  have huv := hu.add hv
  have hN := dualNormSq_eq_kerInt hm hUH huv
  have hfin := dualNormSq_withDensity_lt_top hm hUH huv
  rw [hN, kerInt_add_add hm hu.meas hv.meas] at hfin
  have h1 : kerInt m U u u ≠ ⊤ := ne_top_of_le_ne_top hfin.ne
    (le_self_add.trans (le_self_add.trans le_self_add))
  have h2 : kerInt m U u v ≠ ⊤ := ne_top_of_le_ne_top hfin.ne
    (le_add_self.trans (le_self_add.trans le_self_add))
  have h3 : kerInt m U v u ≠ ⊤ := ne_top_of_le_ne_top hfin.ne (le_add_self.trans le_self_add)
  have h4 : kerInt m U v v ≠ ⊤ := ne_top_of_le_ne_top hfin.ne le_add_self
  unfold dualCov
  rw [← withDensity_add_left hu.meas, hN, kerInt_add_add hm hu.meas hv.meas,
    dualNormSq_eq_kerInt hm hUH hu, dualNormSq_eq_kerInt hm hUH hv,
    ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨h1, h2⟩, h3⟩) h4,
    ENNReal.toReal_add (ENNReal.add_ne_top.2 ⟨h1, h2⟩) h3, ENNReal.toReal_add h1 h2,
    kerInt_comm (u := v) (v := u)]
  ring

/-! ## Real form for test densities -/

lemma ofReal_eq_ofReal_max (t : ℝ) : ENNReal.ofReal t = ENNReal.ofReal (max t 0) := by
  rcases le_total 0 t with h | h
  · rw [max_eq_left h]
  · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]

lemma ae_ne_diag : ∀ᵐ p ∂((volume : Measure ℂ).prod volume), p.1 ≠ p.2 := by
  rw [ae_iff]
  have hd : MeasurableSet {p : ℂ × ℂ | ¬ p.1 ≠ p.2} := by
    simp only [ne_eq, not_not]; exact (isClosed_eq continuous_fst continuous_snd).measurableSet
  rw [Measure.prod_apply hd]
  refine lintegral_eq_zero_of_ae_eq_zero (Filter.Eventually.of_forall fun x => ?_)
  simp

/-- the real integrand `f⁺(x) g⁺(y) G_ℍ(m x, m y)` (with QZ's measurable modification of `m`) -/
def greenDensProd (m : ℂ → ℂ) (U : Set ℂ) (f g : ℂ → ℝ) (p : ℂ × ℂ) : ℝ :=
  max (f p.1) 0 * max (g p.2) 0 * greenH (confMod m U p.1) (confMod m U p.2)

lemma kerDens_eq_of_ne (hm : IsConformalOnto m U H) {f g : ℂ → ℝ} (hf : ∀ x ∉ U, f x = 0)
    (hg : ∀ x ∉ U, g x = 0) {p : ℂ × ℂ} (hp : p.1 ≠ p.2) :
    kerDens m U (fun z => ENNReal.ofReal (f z)) (fun z => ENNReal.ofReal (g z)) p =
      ENNReal.ofReal (greenDensProd m U f g p) ∧ 0 ≤ greenDensProd m U f g p := by
  by_cases h1 : p.1 ∈ U
  · by_cases h2 : p.2 ∈ U
    · have hm1 : m p.1 ∈ H := hm.image_eq ▸ mem_image_of_mem m h1
      have hm2 : m p.2 ∈ H := hm.image_eq ▸ mem_image_of_mem m h2
      have hne : m p.1 ≠ m p.2 := fun h => hp (hm.injOn h1 h2 h)
      have hG : 0 ≤ greenH (m p.1) (m p.2) :=
        greenH_nonneg (H_subset_Hbar_K3 hm1) (H_subset_Hbar_K3 hm2) hne
      have e1 : confMod m U p.1 = m p.1 := confMod_eqOn h1
      have e2 : confMod m U p.2 = m p.2 := confMod_eqOn h2
      have ha : 0 ≤ max (f p.1) 0 := le_max_right _ _
      have hb : 0 ≤ max (g p.2) 0 := le_max_right _ _
      refine ⟨?_, ?_⟩
      · simp only [kerDens, confKer, indicator_of_mem h1, indicator_of_mem h2, greenDensProd,
          e1, e2]
        rw [ofReal_eq_ofReal_max (f p.1), ofReal_eq_ofReal_max (g p.2),
          ENNReal.ofReal_mul (mul_nonneg ha hb), ENNReal.ofReal_mul ha, mul_assoc]
      · simp only [greenDensProd, e1, e2]; positivity
    · have : greenDensProd m U f g p = 0 := by simp [greenDensProd, hg _ h2]
      simp [kerDens, indicator_of_notMem h2, this]
  · have : greenDensProd m U f g p = 0 := by simp [greenDensProd, hf _ h1]
    simp [kerDens, indicator_of_notMem h1, this]

lemma measurable_greenDensProd (hm : IsConformalOnto m U H) {f g : ℂ → ℝ} (hf : Continuous f)
    (hg : Continuous g) : Measurable (greenDensProd m U f g) := by
  have hc := measurable_confMod hm
  have hG : Measurable fun p : ℂ × ℂ => greenH (confMod m U p.1) (confMod m U p.2) :=
    measurable_greenH.comp ((hc.comp measurable_fst).prodMk (hc.comp measurable_snd))
  exact (((hf.measurable.comp measurable_fst).max measurable_const).mul
    ((hg.measurable.comp measurable_snd).max measurable_const)).mul hG

lemma lintegral_greenDensProd (hm : IsConformalOnto m U H) {f g : ℂ → ℝ}
    (hf : ∀ x ∉ U, f x = 0) (hg : ∀ x ∉ U, g x = 0) :
    kerInt m U (fun z => ENNReal.ofReal (f z)) (fun z => ENNReal.ofReal (g z)) =
      ∫⁻ p, ENNReal.ofReal (greenDensProd m U f g p) ∂((volume : Measure ℂ).prod volume) :=
  lintegral_congr_ae (ae_ne_diag.mono fun _ hp => (kerDens_eq_of_ne hm hf hg hp).1)

lemma nonneg_greenDensProd (hm : IsConformalOnto m U H) {f g : ℂ → ℝ}
    (hf : ∀ x ∉ U, f x = 0) (hg : ∀ x ∉ U, g x = 0) :
    0 ≤ᵐ[(volume : Measure ℂ).prod volume] greenDensProd m U f g :=
  ae_ne_diag.mono fun _ hp => (kerDens_eq_of_ne hm hf hg hp).2

lemma kerInt_toReal_eq (hm : IsConformalOnto m U H) {f g : ℂ → ℝ} (hfc : Continuous f)
    (hgc : Continuous g) (hf : ∀ x ∉ U, f x = 0) (hg : ∀ x ∉ U, g x = 0) :
    (kerInt m U (fun z => ENNReal.ofReal (f z)) (fun z => ENNReal.ofReal (g z))).toReal =
      ∫ p, greenDensProd m U f g p ∂((volume : Measure ℂ).prod volume) := by
  rw [integral_eq_lintegral_of_nonneg_ae (nonneg_greenDensProd hm hf hg)
    (measurable_greenDensProd hm hfc hgc).aestronglyMeasurable, lintegral_greenDensProd hm hf hg]

lemma integrable_greenDensProd (hm : IsConformalOnto m U H) {f g : ℂ → ℝ} (hfc : Continuous f)
    (hgc : Continuous g) (hf : ∀ x ∉ U, f x = 0) (hg : ∀ x ∉ U, g x = 0)
    (hfin : kerInt m U (fun z => ENNReal.ofReal (f z)) (fun z => ENNReal.ofReal (g z)) ≠ ⊤) :
    Integrable (greenDensProd m U f g) ((volume : Measure ℂ).prod volume) :=
  ⟨(measurable_greenDensProd hm hfc hgc).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (nonneg_greenDensProd hm hf hg)).2
      (by rw [← lintegral_greenDensProd hm hf hg]; exact lt_top_iff_ne_top.2 hfin)⟩

/-! ## The covariance of the zero-boundary GFF as a Green integral -/

lemma bddDens_test {φ : ℂ → ℝ} (hc : Continuous φ) (hs : HasCompactSupport φ) :
    ∃ M R, BddDens (fun z => ENNReal.ofReal (φ z)) M R := by
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuous hc
  obtain ⟨R, hR⟩ := hs.isCompact.isBounded.subset_closedBall 0
  exact ⟨ENNReal.ofReal C, R, ⟨ENNReal.measurable_ofReal.comp hc.measurable, ENNReal.ofReal_lt_top,
    fun z => ENNReal.ofReal_le_ofReal ((le_abs_self _).trans
      (by simpa [Real.norm_eq_abs] using hC z)),
    fun z hz => by
      rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hR h)), ENNReal.ofReal_zero]⟩⟩

lemma kerInt_ne_top (hm : IsConformalOnto m U H) (hUH : U ⊆ H) {u v : ℂ → ℝ≥0∞} {M N : ℝ≥0∞}
    {R S : ℝ} (hu : BddDens u M R) (hv : BddDens v N S) : kerInt m U u v ≠ ⊤ := by
  have hfin := dualNormSq_withDensity_lt_top hm hUH (hu.add hv)
  rw [dualNormSq_eq_kerInt hm hUH (hu.add hv), kerInt_add_add hm hu.meas hv.meas] at hfin
  exact ne_top_of_le_ne_top hfin.ne (le_add_self.trans (le_self_add.trans le_self_add))

/-- **Green function representation** of the covariance of the zero-boundary GFF on a domain
`V ⊆ ℍ` with a conformal map `m : V → ℍ`:
`⟨φ, ψ⟩_{H⁻¹(V)} = ∫∫ φ(x) ψ(y) G_ℍ(m x, m y) dx dy`. -/
theorem zeroGFFTestCov_eq_green {V : Opens ℂ} (hUH : (V : Set ℂ) ⊆ H)
    (hm : IsConformalOnto m V H) (φ ψ : TestOn V) :
    zeroGFFTestCov V φ ψ =
      ∫ p, φ p.1 * ψ p.2 * greenH (m p.1) (m p.2) ∂((volume : Measure ℂ).prod volume) := by
  have hφ0 : ∀ x ∉ (V : Set ℂ), φ x = 0 := fun x hx => φ.zero_on_compl hx
  have hψ0 : ∀ x ∉ (V : Set ℂ), ψ x = 0 := fun x hx => ψ.zero_on_compl hx
  have hφn : ∀ x ∉ (V : Set ℂ), -φ x = 0 := fun x hx => by rw [hφ0 x hx, neg_zero]
  have hψn : ∀ x ∉ (V : Set ℂ), -ψ x = 0 := fun x hx => by rw [hψ0 x hx, neg_zero]
  obtain ⟨M1, R1, b1⟩ := bddDens_test φ.continuous φ.hasCompactSupport
  obtain ⟨M2, R2, b2⟩ := bddDens_test (φ := fun z => -φ z) φ.continuous.neg φ.hasCompactSupport.neg
  obtain ⟨M3, R3, b3⟩ := bddDens_test ψ.continuous ψ.hasCompactSupport
  obtain ⟨M4, R4, b4⟩ := bddDens_test (φ := fun z => -ψ z) ψ.continuous.neg ψ.hasCompactSupport.neg
  unfold zeroGFFTestCov testMeasPos testMeasNeg
  rw [dualCov_withDensity_eq_kerInt hm hUH b1 b3, dualCov_withDensity_eq_kerInt hm hUH b1 b4,
    dualCov_withDensity_eq_kerInt hm hUH b2 b3, dualCov_withDensity_eq_kerInt hm hUH b2 b4,
    kerInt_toReal_eq hm φ.continuous ψ.continuous hφ0 hψ0,
    kerInt_toReal_eq (f := fun z => φ z) (g := fun z => -ψ z) hm φ.continuous ψ.continuous.neg
      hφ0 hψn,
    kerInt_toReal_eq (f := fun z => -φ z) (g := fun z => ψ z) hm φ.continuous.neg ψ.continuous
      hφn hψ0,
    kerInt_toReal_eq (f := fun z => -φ z) (g := fun z => -ψ z) hm φ.continuous.neg
      ψ.continuous.neg hφn hψn]
  have i1 := integrable_greenDensProd hm φ.continuous ψ.continuous hφ0 hψ0
    (kerInt_ne_top hm hUH b1 b3)
  have i2 := integrable_greenDensProd (f := fun z => φ z) (g := fun z => -ψ z) hm φ.continuous
    ψ.continuous.neg hφ0 hψn (kerInt_ne_top hm hUH b1 b4)
  have i3 := integrable_greenDensProd (f := fun z => -φ z) (g := fun z => ψ z) hm
    φ.continuous.neg ψ.continuous hφn hψ0 (kerInt_ne_top hm hUH b2 b3)
  have i4 := integrable_greenDensProd (f := fun z => -φ z) (g := fun z => -ψ z) hm
    φ.continuous.neg ψ.continuous.neg hφn hψn (kerInt_ne_top hm hUH b2 b4)
  have hsum : ∫ p, (greenDensProd m V φ ψ p - greenDensProd m V (fun z => φ z) (fun z => -ψ z) p
      - greenDensProd m V (fun z => -φ z) (fun z => ψ z) p
      + greenDensProd m V (fun z => -φ z) (fun z => -ψ z) p) ∂((volume : Measure ℂ).prod volume) =
      ∫ p, greenDensProd m V φ ψ p ∂((volume : Measure ℂ).prod volume)
      - ∫ p, greenDensProd m V (fun z => φ z) (fun z => -ψ z) p ∂((volume : Measure ℂ).prod volume)
      - ∫ p, greenDensProd m V (fun z => -φ z) (fun z => ψ z) p ∂((volume : Measure ℂ).prod volume)
      + ∫ p, greenDensProd m V (fun z => -φ z) (fun z => -ψ z) p
          ∂((volume : Measure ℂ).prod volume) := by
    have j12 : Integrable (fun p => greenDensProd m V φ ψ p
        - greenDensProd m V (fun z => φ z) (fun z => -ψ z) p) ((volume : Measure ℂ).prod volume) :=
      i1.sub i2
    have j123 : Integrable (fun p => greenDensProd m V φ ψ p
        - greenDensProd m V (fun z => φ z) (fun z => -ψ z) p
        - greenDensProd m V (fun z => -φ z) (fun z => ψ z) p) ((volume : Measure ℂ).prod volume) :=
      j12.sub i3
    rw [integral_add j123 i4, integral_sub j12 i3, integral_sub i1 i2]
  rw [← hsum]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [greenDensProd]
  by_cases h1 : p.1 ∈ (V : Set ℂ)
  · by_cases h2 : p.2 ∈ (V : Set ℂ)
    · rw [confMod_eqOn h1, confMod_eqOn h2]
      have e : ∀ a b c d G : ℝ, a * b * G - a * d * G - c * b * G + c * d * G =
          (a - c) * (b - d) * G := fun _ _ _ _ _ => by ring
      rw [e, max_sub_max_neg_K3, max_sub_max_neg_K3]
    · simp [hψ0 _ h2]
  · simp [hφ0 _ h1]

end LQGMetric
