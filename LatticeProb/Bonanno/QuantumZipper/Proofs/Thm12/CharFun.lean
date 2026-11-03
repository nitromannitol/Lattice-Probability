/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Thm12.CharFun at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Statements.Thm12
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Regularization
import LatticeProb.Bonanno.QuantumZipper.Proofs.GFF.Admissible
import LatticeProb.Bonanno.QuantumZipper.Proofs.Analysis.Pushforward
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.ReverseHolo
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.ReverseFlow
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Probability.Process.FiniteDimensionalLaws
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Characteristic functions and the assembly of Theorem 1.2

Task CHARFUN (`PLAN.md` §5 M2, steps 1 and 4).

For a mass-zero test function `ρ` we compute the characteristic functions of the two random
fields of `theorem1_2` paired with `ρ`, and we show that characteristic functions of all
pairings determine `fieldLawMod0`.

* `charFun_lhs`: (a), the left-hand side.
* `charFun_rhs`: (b), the right-hand side equals `Phi κ T B P ρ`.
* `fieldLawMod0_eq_of_charFun`: (c), Cramér–Wold.
* `theorem1_2_of_phi`: (d), Theorem 1.2 modulo the semigroup identity `Φ_T = Φ_0`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Complex Set Filter
open scoped ENNReal NNReal Topology

namespace QuantumZipper
namespace CharFun

/-! ## Definitions -/

/-- The mean `(𝔥_T, ρ) = ∫ ρ 𝔥_T`. -/
def Xfun (κ : ℝ) (W : ℝ → ℝ) (T : ℝ) (ρ : ℂ → ℝ) : ℝ := ∫ z, ρ z * hTrev κ W T z

/-- The energy `E_T(ρ) = ∬ ρ(x) ρ(y) G(f_T x, f_T y)`. -/
def Efun (W : ℝ → ℝ) (T : ℝ) (ρ : ℂ → ℝ) : ℝ :=
  ∫ x, ∫ y, ρ x * ρ y * neumannH (revMap W T x) (revMap W T y)

/-- The characteristic functional `Φ_T(ρ) = E exp(i (𝔥_T, ρ) − E_T(ρ)/2)`. -/
def Phi {Ω : Type*} [MeasurableSpace Ω] (κ T : ℝ) (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (ρ : ℂ → ℝ) : ℂ :=
  ∫ ω, cexp (I * (Xfun κ (drive κ B ω) T ρ : ℂ) - (Efun (drive κ B ω) T ρ : ℂ) / 2) ∂P

/-- The energy of `ρ` pushed by a map `f`. -/
def Ef (f : ℂ → ℂ) (ρ : ℂ → ℝ) : ℝ := ∫ x, ∫ y, ρ x * ρ y * neumannH (f x) (f y)

/-- The measure `ρ⁺ dz`. -/
def tdens (ρ : ℂ → ℝ) : Measure ℂ := volume.withDensity fun z => ENNReal.ofReal (ρ z)

instance (a : ℂ → ℝ) : SFinite (tdens a) := by unfold tdens; infer_instance

theorem pairRaw_eq_tdens (x : FieldSample) (ρ : ℂ → ℝ) :
    pairRaw x ρ = x (tdens ρ) - x (tdens fun z => -ρ z) := rfl

theorem max_sub_max_neg (r : ℝ) : max r 0 - max (-r) 0 = r := by
  rcases le_total 0 r with h | h
  · simp [max_eq_left h, max_eq_right (neg_nonpos.2 h)]
  · simp [max_eq_right h, max_eq_left (neg_nonneg.2 h)]

/-! ## Densities -/

/-- Bundled facts about a density `a` (one of `±ρ`). -/
structure Dens (a : ℂ → ℝ) (K : Set ℂ) (M δ : ℝ) : Prop where
  cont : Continuous a
  supp : ∀ z ∉ K, a z = 0
  compact : IsCompact K
  delta : 0 < δ
  sub : K ⊆ {z | δ < z.im}
  bound : ∀ z, |a z| ≤ M

namespace Dens

variable {a : ℂ → ℝ} {K : Set ℂ} {M δ : ℝ}

theorem meas (hd : Dens a K M δ) : Measurable a := hd.cont.measurable

theorem dmeas (hd : Dens a K M δ) : Measurable fun z => ENNReal.ofReal (a z) :=
  ENNReal.measurable_ofReal.comp hd.meas

theorem dzero (hd : Dens a K M δ) : ∀ z ∉ K, ENNReal.ofReal (a z) = 0 := fun z hz => by
  rw [hd.supp z hz, ENNReal.ofReal_zero]

theorem subH (hd : Dens a K M δ) : K ⊆ H := fun z hz => show 0 < z.im from
  hd.delta.trans (hd.sub hz)

theorem tdens_compl (hd : Dens a K M δ) : tdens a Kᶜ = 0 := by
  have hs : MeasurableSet Kᶜ := hd.compact.isClosed.measurableSet.compl
  rw [tdens, withDensity_apply _ hs]
  exact (setLIntegral_congr_fun (g := fun _ => 0) hs fun z hz => hd.dzero z hz).trans (by simp)

theorem tdens_le (hd : Dens a K M δ) : tdens a ≤ (M.toNNReal : ℝ≥0∞) • volume := by
  calc tdens a ≤ volume.withDensity (fun _ => ENNReal.ofReal M) :=
        withDensity_mono (ae_of_all _ fun z =>
          ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hd.bound z)))
    _ = _ := withDensity_const _

theorem admissible (hd : Dens a K M δ) : IsAdmissibleH (tdens a) :=
  isAdmissibleH_withDensity hd.dmeas ENNReal.ofReal_lt_top
    (fun z => ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hd.bound z))) hd.compact
    (hd.subH.trans H_subset_Hbar) hd.dzero

theorem neg (hd : Dens a K M δ) : Dens (fun z => -a z) K M δ where
  cont := hd.cont.neg
  supp z hz := by simp [hd.supp z hz]
  compact := hd.compact
  delta := hd.delta
  sub := hd.sub
  bound z := by simpa using hd.bound z

end Dens

theorem tf_continuous (ρ : TestFun H) : Continuous ρ.1 := ρ.2.1.continuous

theorem exists_dens (ρ : TestFun H) : ∃ M δ : ℝ, Dens ρ.1 (tsupport ρ.1) M δ := by
  obtain ⟨C, hC⟩ := (tf_continuous ρ).bounded_above_of_compact_support ρ.2.2.1
  have hδ : ∃ δ : ℝ, 0 < δ ∧ tsupport ρ.1 ⊆ {z | δ < z.im} := by
    rcases (tsupport ρ.1).eq_empty_or_nonempty with he | hne
    · exact ⟨1, one_pos, by simp [he]⟩
    · obtain ⟨z0, hz0, hmin⟩ :=
        ρ.2.2.1.isCompact.exists_isMinOn hne Complex.continuous_im.continuousOn
      have h0 : 0 < z0.im := ρ.2.2.2 hz0
      refine ⟨z0.im / 2, by linarith, fun z hz => ?_⟩
      have : z0.im ≤ z.im := hmin hz
      show z0.im / 2 < z.im
      linarith
  obtain ⟨δ, hδ0, hδK⟩ := hδ
  exact ⟨C, δ, tf_continuous ρ, fun z hz => image_eq_zero_of_notMem_tsupport hz,
    ρ.2.2.1.isCompact, hδ0, hδK, fun z => by simpa [Real.norm_eq_abs] using hC z⟩

/-- Balanced masses for a mass-zero test function. -/
theorem tdens_univ_eq (ρ : TestFun0 H) :
    tdens ρ.1.1 univ = tdens (fun z => -ρ.1.1 z) univ := by
  obtain ⟨M, δ, hd⟩ := exists_dens ρ.1
  have hi : Integrable ρ.1.1 := (tf_continuous ρ.1).integrable_of_hasCompactSupport ρ.1.2.2.1
  have h := integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi
  rw [ρ.2] at h
  have := hd.admissible.1
  have := hd.neg.admissible.1
  have h1 : tdens ρ.1.1 univ ≠ ⊤ := measure_ne_top _ _
  have h2 : tdens (fun z => -ρ.1.1 z) univ ≠ ⊤ := measure_ne_top _ _
  rw [tdens, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h1 ⊢
  rw [tdens, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at h2 ⊢
  exact (ENNReal.toReal_eq_toReal_iff' h1 h2).1 (by linarith)

/-! ## Admissibility of dominated measures -/

theorem admissible_mono {μ ν : Measure ℂ} (h : μ ≤ ν) (hν : IsAdmissibleH ν) :
    IsAdmissibleH μ := by
  obtain ⟨hνf, ⟨K, hK, hKH, hKc⟩, C, hC, hbd⟩ := hν
  refine ⟨⟨(Measure.le_iff'.1 h univ).trans_lt (measure_lt_top ν univ)⟩,
    ⟨K, hK, hKH, nonpos_iff_eq_zero.1 ((Measure.le_iff'.1 h _).trans hKc.le)⟩, C, hC,
    fun y => (lintegral_mono' h le_rfl).trans (hbd y)⟩

theorem admissible_of_le_smul {μ : Measure ℂ} {M' : ℝ≥0} (hμ : μ ≤ (M' : ℝ≥0∞) • volume)
    {K' : Set ℂ} (hK' : IsCompact K') (hKH : K' ⊆ Hbar) (hμK : μ K'ᶜ = 0) :
    IsAdmissibleH μ := by
  have hν : IsAdmissibleH (volume.withDensity (K'.indicator fun _ => (M' : ℝ≥0∞))) :=
    isAdmissibleH_withDensity (M := (M' : ℝ≥0∞)) (measurable_const.indicator hK'.measurableSet)
      ENNReal.coe_lt_top (fun x => by by_cases hx : x ∈ K' <;> simp [hx]) hK' hKH
      (fun x hx => by simp [hx])
  refine admissible_mono ?_ hν
  rw [withDensity_indicator hK'.measurableSet, withDensity_const]
  calc μ = μ.restrict K' := (Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hμK)).symm
    _ ≤ ((M' : ℝ≥0∞) • volume).restrict K' := Measure.restrict_mono subset_rfl hμ
    _ = _ := Measure.restrict_smul _ _ _

/-! ## Good maps and pushforwards -/

/-- The properties of `revMap W T` (and of `id`) used for pushforwards. -/
structure GoodMap (f : ℂ → ℂ) : Prop where
  meas : Measurable f
  diff : DifferentiableOn ℂ f H
  inj : InjOn f H
  deriv_ne : ∀ z ∈ H, deriv f z ≠ 0
  im_le : ∀ z ∈ H, z.im ≤ (f z).im

theorem goodMap_id : GoodMap id where
  meas := measurable_id
  diff := differentiableOn_id
  inj := injOn_id _
  deriv_ne z _ := by simp
  im_le z _ := le_rfl

theorem goodMap_revMap {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T)
    (hm : Measurable (revMap W T)) : GoodMap (revMap W T) where
  meas := hm
  diff := differentiableOn_revMap W hW hT
  inj := injOn_revMap W hW hT
  deriv_ne _ hz := deriv_revMap_ne_zero W hW hT hz
  im_le z hz := im_le_im_revMap W hW z hz hT

variable {f : ℂ → ℂ} {a : ℂ → ℝ} {K : Set ℂ} {M δ : ℝ}

theorem push_facts (hf : GoodMap f) (hd : Dens a K M δ) :
    ∃ M' : ℝ≥0, (tdens a).map f ≤ (M' : ℝ≥0∞) • volume ∧ (tdens a).map f (f '' K)ᶜ = 0 ∧
      IsCompact (f '' K) ∧ f '' K ⊆ {z | δ < z.im} := by
  have hKH := hd.subH
  have hmap := map_withDensity_eq isOpen_H hf.diff hf.inj hf.meas hf.deriv_ne
    hd.compact.isClosed.measurableSet hKH hd.dmeas hd.dzero
  obtain ⟨c, hc, hbd, -, -⟩ := bounded_density isOpen_H hf.diff hf.inj hf.deriv_ne hd.compact
    hKH subset_rfl hd.dzero (M := ENNReal.ofReal M)
    (fun z _ => ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (hd.bound z)))
  have hK' : IsCompact (f '' K) := hd.compact.image_of_continuousOn (hf.diff.continuousOn.mono hKH)
  have hne : ENNReal.ofReal M / ENNReal.ofReal c ≠ ⊤ :=
    ENNReal.div_ne_top ENNReal.ofReal_ne_top (ENNReal.ofReal_pos.2 hc).ne'
  refine ⟨(ENNReal.ofReal M / ENNReal.ofReal c).toNNReal, ?_, ?_, hK', ?_⟩
  · rw [tdens, hmap, ENNReal.coe_toNNReal hne]
    calc _ ≤ volume.withDensity (fun _ => ENNReal.ofReal M / ENNReal.ofReal c) :=
          withDensity_mono (ae_of_all _ hbd)
      _ = _ := withDensity_const _
  · rw [Measure.map_apply hf.meas hK'.isClosed.measurableSet.compl]
    exact measure_mono_null (fun z hz hzK => hz ⟨z, hzK, rfl⟩) hd.tdens_compl
  · rintro _ ⟨z, hz, rfl⟩
    exact lt_of_lt_of_le (hd.sub hz) (hf.im_le z (hKH hz))

theorem push_admissible (hf : GoodMap f) (hd : Dens a K M δ) :
    IsAdmissibleH ((tdens a).map f) := by
  obtain ⟨M', hle, hc, hK', hsub⟩ := push_facts hf hd
  exact admissible_of_le_smul hle hK'
    (fun z hz => show 0 ≤ z.im from (hd.delta.trans (hsub hz)).le) hc

theorem push_reg {Ω : Type*} [MeasurableSpace Ω] {X : Ω → FieldSample} {P : Measure Ω}
    [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) (hf : GoodMap f)
    (hd : Dens a K M δ) :
    ∀ᵐ ω ∂P, evalReg (X ω) ((tdens a).map f) = X ω ((tdens a).map f) := by
  obtain ⟨M', hle, hc, hK', hsub⟩ := push_facts hf hd
  exact ae_evalReg_eq_of_le_smul_volume hX hle hK' hd.delta hsub hc

theorem push_univ (hf : GoodMap f) (a : ℂ → ℝ) :
    (tdens a).map f univ = tdens a univ := by
  rw [Measure.map_apply hf.meas MeasurableSet.univ, preimage_univ]

/-! ## The Gaussian step -/

theorem integral_cexp_diff {Ω : Type*} [MeasurableSpace Ω] {X : Ω → FieldSample}
    {P : Measure Ω} [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) {μ ν : Measure ℂ}
    (hμ : IsAdmissibleH μ) (hν : IsAdmissibleH ν) (hm : μ univ = ν univ) :
    ∫ ω, cexp (I * ((X ω μ - X ω ν : ℝ) : ℂ)) ∂P =
      cexp (-(kernelCov2 neumannH (μ, ν) (μ, ν) : ℂ) / 2) := by
  set Y : Ω → ℝ := fun ω => X ω μ - X ω ν with hY
  have hG : HasGaussianLaw Y P :=
    hX.gaussian.hasGaussianLaw_eval ⟨(μ, ν), hμ, hν, hm⟩
  have hmap := hG.map_eq_gaussianReal
  have hmean : P[Y] = 0 := hX.centered μ ν hμ hν hm
  have hvar : Var[Y; P] = kernelCov2 neumannH (μ, ν) (μ, ν) := by
    rw [← covariance_self hG.aemeasurable]
    exact hX.covariance_eq (μ, ν) (μ, ν) hμ hν hm hμ hν hm
  have hvnn : 0 ≤ Var[Y; P] := variance_nonneg _ _
  calc ∫ ω, cexp (I * ((X ω μ - X ω ν : ℝ) : ℂ)) ∂P = ∫ x, cexp (I * (x : ℂ)) ∂(P.map Y) := by
        rw [integral_map hG.aemeasurable (by fun_prop)]
    _ = charFun (P.map Y) 1 := by rw [charFun_apply_real]; simp [mul_comm]
    _ = _ := by
        rw [hmap, charFun_gaussianReal, hmean, Real.coe_toNNReal _ hvnn, hvar]
        congr 1
        push_cast
        ring

/-! ## The energy of pushforwards -/

theorem kernelCov_map (hfm : Measurable f) {a b : ℂ → ℝ} (ha : Measurable a) (hb : Measurable b)
    (hA : IsAdmissibleH ((tdens a).map f)) (hB : IsAdmissibleH ((tdens b).map f)) :
    Integrable (fun p : ℂ × ℂ => max (a p.1) 0 * max (b p.2) 0 * neumannH (f p.1) (f p.2))
        (volume.prod volume) ∧
      kernelCov neumannH ((tdens a).map f) ((tdens b).map f) =
        ∫ p, max (a p.1) 0 * max (b p.2) 0 * neumannH (f p.1) (f p.2) ∂(volume.prod volume) := by
  have hma : Measurable fun z => ENNReal.ofReal (a z) := ENNReal.measurable_ofReal.comp ha
  have hmb : Measurable fun z => ENNReal.ofReal (b z) := ENNReal.measurable_ofReal.comp hb
  have hN := integrable_neumannH_prod hA hB
  have hN1 : Integrable (fun p : ℂ × ℂ => neumannH p.1 p.2)
      (((tdens a).prod (tdens b)).map (Prod.map f f)) := by
    rwa [← Measure.map_prod_map _ _ hfm hfm]
  have hN2 := (integrable_map_measure measurable_neumannH.aestronglyMeasurable
    (hfm.prodMap hfm).aemeasurable).1 hN1
  rw [tdens, tdens, prod_withDensity hma hmb] at hN2
  have hlt : ∀ᵐ p ∂(volume.prod volume : Measure (ℂ × ℂ)),
      ENNReal.ofReal (a p.1) * ENNReal.ofReal (b p.2) < ⊤ :=
    ae_of_all _ fun p => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hm2 : Measurable fun p : ℂ × ℂ => ENNReal.ofReal (a p.1) * ENNReal.ofReal (b p.2) :=
    (hma.comp measurable_fst).mul (hmb.comp measurable_snd)
  rw [integrable_withDensity_iff_integrable_smul' hm2 hlt] at hN2
  have heq : ∀ p : ℂ × ℂ, (ENNReal.ofReal (a p.1) * ENNReal.ofReal (b p.2)).toReal •
      ((fun p : ℂ × ℂ => neumannH p.1 p.2) ∘ Prod.map f f) p =
      max (a p.1) 0 * max (b p.2) 0 * neumannH (f p.1) (f p.2) := by
    intro p
    simp [ENNReal.toReal_mul, ENNReal.toReal_ofReal', smul_eq_mul]
  refine ⟨hN2.congr (ae_of_all _ heq), ?_⟩
  calc kernelCov neumannH ((tdens a).map f) ((tdens b).map f)
        = ∫ p, neumannH p.1 p.2 ∂(((tdens a).map f).prod ((tdens b).map f)) :=
          (integral_prod _ hN).symm
    _ = ∫ p, neumannH p.1 p.2 ∂(((tdens a).prod (tdens b)).map (Prod.map f f)) := by
          rw [Measure.map_prod_map _ _ hfm hfm]
    _ = ∫ p, ((fun p : ℂ × ℂ => neumannH p.1 p.2) ∘ Prod.map f f) p
          ∂((tdens a).prod (tdens b)) := by
          rw [integral_map (hfm.prodMap hfm).aemeasurable
            measurable_neumannH.aestronglyMeasurable]
          rfl
    _ = _ := by
          rw [tdens, tdens, prod_withDensity hma hmb,
            integral_withDensity_eq_integral_toReal_smul hm2 hlt]
          exact integral_congr_ae (ae_of_all _ heq)

theorem kernelCov2_map (hf : GoodMap f) (hd : Dens a K M δ) :
    kernelCov2 neumannH ((tdens a).map f, (tdens fun z => -a z).map f)
        ((tdens a).map f, (tdens fun z => -a z).map f) = Ef f a := by
  have hA := push_admissible hf hd
  have hB := push_admissible hf hd.neg
  obtain ⟨i1, e1⟩ := kernelCov_map hf.meas hd.meas hd.meas hA hA
  obtain ⟨i2, e2⟩ := kernelCov_map hf.meas hd.meas hd.neg.meas hA hB
  obtain ⟨i3, e3⟩ := kernelCov_map hf.meas hd.neg.meas hd.meas hB hA
  obtain ⟨i4, e4⟩ := kernelCov_map hf.meas hd.neg.meas hd.neg.meas hB hB
  have hpt : ∀ p : ℂ × ℂ, a p.1 * a p.2 * neumannH (f p.1) (f p.2) =
      max (a p.1) 0 * max (a p.2) 0 * neumannH (f p.1) (f p.2) -
      max (a p.1) 0 * max (-a p.2) 0 * neumannH (f p.1) (f p.2) -
      max (-a p.1) 0 * max (a p.2) 0 * neumannH (f p.1) (f p.2) +
      max (-a p.1) 0 * max (-a p.2) 0 * neumannH (f p.1) (f p.2) := by
    intro p
    have h1 := max_sub_max_neg (a p.1)
    have h2 := max_sub_max_neg (a p.2)
    calc a p.1 * a p.2 * neumannH (f p.1) (f p.2)
        = (max (a p.1) 0 - max (-a p.1) 0) * (max (a p.2) 0 - max (-a p.2) 0) *
            neumannH (f p.1) (f p.2) := by rw [h1, h2]
      _ = _ := by ring
  have hint : Integrable (fun p : ℂ × ℂ => a p.1 * a p.2 * neumannH (f p.1) (f p.2))
      (volume.prod volume) := by
    have := ((i1.sub i2).sub i3).add i4
    exact this.congr (ae_of_all _ fun p => (hpt p).symm)
  have i12 : Integrable (fun p : ℂ × ℂ =>
      max (a p.1) 0 * max (a p.2) 0 * neumannH (f p.1) (f p.2) -
      max (a p.1) 0 * max (-a p.2) 0 * neumannH (f p.1) (f p.2)) (volume.prod volume) :=
    i1.sub i2
  have i123 : Integrable (fun p : ℂ × ℂ =>
      max (a p.1) 0 * max (a p.2) 0 * neumannH (f p.1) (f p.2) -
      max (a p.1) 0 * max (-a p.2) 0 * neumannH (f p.1) (f p.2) -
      max (-a p.1) 0 * max (a p.2) 0 * neumannH (f p.1) (f p.2)) (volume.prod volume) :=
    i12.sub i3
  have hprod : Ef f a = ∫ p, a p.1 * a p.2 * neumannH (f p.1) (f p.2) ∂(volume.prod volume) :=
    (integral_prod _ hint).symm
  unfold kernelCov2
  simp only
  rw [e1, e2, e3, e4, hprod, integral_congr_ae (ae_of_all _ hpt), integral_add i123 i4,
    integral_sub i12 i3, integral_sub i1 i2]

/-- The conditional characteristic function of the GFF part, for a good map `f`. -/
theorem cond_charFun {Ω : Type*} [MeasurableSpace Ω] {X : Ω → FieldSample} {P : Measure Ω}
    [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) (hf : GoodMap f) (ρ : TestFun0 H) :
    ∫ ω, cexp (I * ((X ω ((tdens ρ.1.1).map f) -
        X ω ((tdens fun z => -ρ.1.1 z).map f) : ℝ) : ℂ)) ∂P = cexp (-(Ef f ρ.1.1 : ℂ) / 2) := by
  obtain ⟨M, δ, hd⟩ := exists_dens ρ.1
  rw [integral_cexp_diff hX (push_admissible hf hd) (push_admissible hf hd.neg)
    (by rw [push_univ hf, push_univ hf, tdens_univ_eq]), kernelCov2_map hf hd]

/-! ## Deterministic pairings -/

theorem continuous_mul_of_tsupport {φ g : ℂ → ℝ} (hφ : Continuous φ) (hs : tsupport φ ⊆ H)
    (hg : ContinuousOn g H) : Continuous fun z => φ z * g z := by
  refine continuous_iff_continuousAt.2 fun z => ?_
  by_cases hz : z ∈ H
  · exact hφ.continuousAt.mul (hg.continuousAt (isOpen_H.mem_nhds hz))
  · have h0 : φ =ᶠ[𝓝 z] 0 := notMem_tsupport_iff_eventuallyEq.1 (fun h => hz (hs h))
    refine (continuousAt_const (y := (0 : ℝ))).congr ?_
    filter_upwards [h0] with w hw
    simp [hw]

theorem integrable_comp_mul {ψ : ℝ → ℝ} (hψ : Continuous ψ) (hψ0 : ψ 0 = 0) (ρ : TestFun H)
    {g : ℂ → ℝ} (hg : ContinuousOn g H) : Integrable fun z => ψ (ρ.1 z) * g z := by
  have hc : Continuous (ψ ∘ ρ.1) := hψ.comp (tf_continuous ρ)
  have hs : tsupport (ψ ∘ ρ.1) ⊆ H := (tsupport_comp_subset hψ0 _).trans ρ.2.2.2
  exact (continuous_mul_of_tsupport hc hs hg).integrable_of_hasCompactSupport
    ((ρ.2.2.1.comp_left hψ0).mul_right)

theorem ofFun_tdens (g : ℂ → ℝ) (a : ℂ → ℝ) (ha : Measurable a) :
    ofFun g (tdens a) = ∫ z, max (a z) 0 * g z := by
  rw [ofFun, tdens, integral_withDensity_eq_integral_toReal_smul
    (f := fun z => ENNReal.ofReal (a z)) (ENNReal.measurable_ofReal.comp ha) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  simp [ENNReal.toReal_ofReal', smul_eq_mul]

theorem pairRaw_ofFun {g : ℂ → ℝ} (hg : ContinuousOn g H) (ρ : TestFun H) :
    pairRaw (ofFun g) ρ.1 = ∫ z, ρ.1 z * g z := by
  have hm := (tf_continuous ρ).measurable
  have h1 : Integrable fun z => max (ρ.1 z) 0 * g z :=
    integrable_comp_mul (ψ := fun r => max r 0) (continuous_id.max continuous_const) (by simp) ρ hg
  have h2 : Integrable fun z => max (-ρ.1 z) 0 * g z :=
    integrable_comp_mul (ψ := fun r => max (-r) 0) (continuous_neg.max continuous_const)
      (by simp) ρ hg
  rw [pairRaw_eq_tdens, ofFun_tdens g _ hm, ofFun_tdens g (fun z => -ρ.1 z) hm.neg,
    ← integral_sub h1 h2]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only
  rw [← sub_mul, max_sub_max_neg]

theorem continuousOn_h0rev (κ : ℝ) : ContinuousOn (h0rev κ) H := by
  unfold h0rev
  refine continuousOn_const.mul (ContinuousOn.log continuous_norm.continuousOn fun z hz => ?_)
  have : z ≠ 0 := fun h => by simp [h, H] at hz
  exact norm_ne_zero_iff.2 this

/-! ## (a) The left-hand side -/

/-- **(a)** The characteristic function of the left-hand field `𝔥₀ + h̃` paired with `ρ`. -/
theorem charFun_lhs (κ : ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : Ω → FieldSample) (hX : IsFreeGFFModConstH X P)
    (ρ : TestFun0 H) :
    ∫ ω, cexp (I * (pairRaw (ofFun (h0rev κ) + X ω) ρ.1.1 : ℂ)) ∂P =
      cexp (I * ((∫ z, ρ.1.1 z * h0rev κ z : ℝ) : ℂ) -
        ((∫ x, ∫ y, ρ.1.1 x * ρ.1.1 y * neumannH x y : ℝ) : ℂ) / 2) := by
  have hsplit : ∀ ω, pairRaw (ofFun (h0rev κ) + X ω) ρ.1.1 =
      (∫ z, ρ.1.1 z * h0rev κ z) + (X ω ((tdens ρ.1.1).map id) -
        X ω ((tdens fun z => -ρ.1.1 z).map id)) := by
    intro ω
    rw [← pairRaw_ofFun (continuousOn_h0rev κ) ρ.1, pairRaw_eq_tdens, pairRaw_eq_tdens,
      Measure.map_id, Measure.map_id]
    simp only [Pi.add_apply]
    ring
  simp_rw [hsplit, ofReal_add, mul_add, Complex.exp_add]
  rw [integral_const_mul, cond_charFun hX goodMap_id ρ, ← Complex.exp_add]
  congr 1
  simp only [Ef, id]
  ring

/-! ## A version of the Brownian motion with measurable coordinates and continuous paths -/

theorem exists_good_version {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) :
    ∃ B' : ℝ≥0 → Ω → ℝ, (∀ t, Measurable (B' t)) ∧ (∀ ω, Continuous fun t => B' t ω) ∧
      ∀ᵐ ω ∂P, ∀ t, B' t ω = B t ω := by
  have hae : ∀ t, AEMeasurable (B t) P := fun t =>
    (hB.isGaussianProcess.hasGaussianLaw_eval t).aemeasurable
  obtain ⟨s, hsc, hsd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  set Bm : ℝ≥0 → Ω → ℝ := fun t => (hae t).mk (B t) with hBm
  set good : Ω → Prop := fun ω => (∀ q ∈ s, Bm q ω = B q ω) ∧ Continuous fun t => B t ω
    with hgood
  have hN : ∀ᵐ ω ∂P, good ω := by
    have h1 : ∀ᵐ ω ∂P, ∀ q ∈ s, Bm q ω = B q ω :=
      (ae_ball_iff hsc).2 fun q _ => (hae q).ae_eq_mk.symm
    filter_upwards [h1, hB.cont] with ω h1 h2 using ⟨h1, h2⟩
  set S : Set Ω := (toMeasurable P {ω | ¬ good ω})ᶜ with hS_def
  have hS : MeasurableSet S := (measurableSet_toMeasurable _ _).compl
  have hSae : ∀ᵐ ω ∂P, ω ∈ S := by
    refine compl_mem_ae_iff.2 ?_
    rw [measure_toMeasurable]
    exact ae_iff.1 hN
  have hSg : ∀ ω ∈ S, good ω := fun ω hω => by
    by_contra h
    exact hω (subset_toMeasurable _ _ h)
  refine ⟨fun t ω => S.indicator (fun ω => B t ω) ω, fun t => ?_, fun ω => ?_, ?_⟩
  · obtain ⟨x, hxs, hx⟩ := mem_closure_iff_seq_limit.1 (hsd t)
    refine measurable_of_tendsto_metrizable (f := fun n ω => S.indicator (Bm (x n)) ω)
      (fun n => (hae (x n)).measurable_mk.indicator hS) (tendsto_pi_nhds.2 fun ω => ?_)
    by_cases hω : ω ∈ S
    · simp only [indicator_of_mem hω]
      have hg := hSg ω hω
      have : (fun n => Bm (x n) ω) = fun n => B (x n) ω := funext fun n => hg.1 _ (hxs n)
      rw [this]
      exact (hg.2.tendsto t).comp hx
    · simp only [indicator_of_notMem hω]
      exact tendsto_const_nhds
  · by_cases hω : ω ∈ S
    · simp only [indicator_of_mem hω]; exact (hSg ω hω).2
    · simp only [indicator_of_notMem hω]; exact continuous_const
  · filter_upwards [hSae] with ω hω t
    simp [indicator_of_mem hω]

/-! ## Continuous drivers on `[0, T]` -/

/-- The driver `√κ f` built from a continuous path `f` on `[0, T]`. -/
def Wof (κ T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, ℝ)) : ℝ → ℝ :=
  fun r => Real.sqrt κ * f (projIcc 0 T hT r)

theorem continuous_Wof (κ T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, ℝ)) :
    Continuous (Wof κ T hT f) :=
  continuous_const.mul (f.continuous.comp continuous_projIcc)

/-- The restriction to `[0,T]` of a continuous path. -/
def pathC (T : ℝ) {Ω : Type*} (B : ℝ≥0 → Ω → ℝ) (hc : ∀ ω, Continuous fun t => B t ω)
    (ω : Ω) : C(Icc (0 : ℝ) T, ℝ) :=
  ⟨fun x => B x.1.toNNReal ω, (hc ω).comp (continuous_real_toNNReal.comp continuous_subtype_val)⟩

theorem measurable_pathC (T : ℝ) {Ω : Type*} [MeasurableSpace Ω] {B : ℝ≥0 → Ω → ℝ}
    (hB : ∀ t, Measurable (B t)) (hc : ∀ ω, Continuous fun t => B t ω) :
    Measurable (pathC T B hc) :=
  ContinuousMap.measurable_iff_eval.2 fun _ => hB _

theorem revMap_drive_eq (κ T : ℝ) (hT : 0 ≤ T) {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (hc : ∀ ω, Continuous fun t => B t ω) (ω : Ω) :
    revMap (drive κ B ω) T = revMap (Wof κ T hT (pathC T B hc ω)) T := by
  funext z
  apply ReverseFlow.revMap_congr_drive
  intro r hr
  simp [drive, Wof, pathC, projIcc_of_mem hT hr]

theorem hTrev_congr {W W' : ℝ → ℝ} {T : ℝ} (h : revMap W T = revMap W' T) (κ : ℝ) :
    hTrev κ W T = hTrev κ W' T := by
  funext z; simp only [hTrev, h]

theorem Xfun_congr {W W' : ℝ → ℝ} {T : ℝ} (h : revMap W T = revMap W' T) (κ : ℝ)
    (ρ : ℂ → ℝ) : Xfun κ W T ρ = Xfun κ W' T ρ := by
  simp only [Xfun, hTrev_congr h]

theorem Efun_congr {W W' : ℝ → ℝ} {T : ℝ} (h : revMap W T = revMap W' T) (ρ : ℂ → ℝ) :
    Efun W T ρ = Efun W' T ρ := by
  simp only [Efun, h]

theorem revMap_of_not_mem {W : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T) {z : ℂ} (hz : ¬ 0 < z.im) :
    revMap W T z = 0 := by
  unfold revMap
  rw [dif_neg]
  rintro ⟨u, hu⟩
  obtain ⟨h1, h2⟩ := hu.2 0 ⟨le_rfl, hT⟩
  rw [h2, intervalIntegral.integral_same] at h1
  exact hz (by simpa using h1)

/-! ## Joint measurability in the driver and the point -/

/-- The reverse flow as a function of (driver path, point). -/
def Fm (κ T : ℝ) (hT : 0 ≤ T) (p : C(Icc (0 : ℝ) T, ℝ) × ℂ) : ℂ :=
  revMap (Wof κ T hT p.1) T p.2

theorem continuousOn_Fm (κ T : ℝ) (hT : 0 ≤ T) : ContinuousOn (Fm κ T hT) (univ ×ˢ H) := by
  rintro ⟨f0, z0⟩ hp
  refine ContinuousAt.continuousWithinAt ?_
  have hz0 : 0 < z0.im := hp.2
  set δ := z0.im / 2 with hδdef
  have hδ : 0 < δ := by positivity
  set L := Real.exp (2 * T / δ ^ 2) with hLdef
  have hL : 0 < L := Real.exp_pos _
  rw [Metric.continuousAt_iff]
  intro ε hε
  have hc : 0 < (Real.sqrt κ + 1) * L := by positivity
  set η := ε / ((Real.sqrt κ + 1) * L) with hηdef
  have hη : 0 < η := div_pos hε hc
  refine ⟨min δ η, lt_min hδ hη, ?_⟩
  rintro ⟨f, z⟩ hd
  obtain ⟨hd1, hd2⟩ := lt_min_iff.1 hd
  rw [Prod.dist_eq, max_lt_iff] at hd1 hd2
  have him : δ ≤ z.im := by
    have h1 : |(z - z0).im| ≤ ‖z - z0‖ := abs_im_le_norm (z - z0)
    rw [Complex.sub_im] at h1
    have h2 : ‖z - z0‖ < δ := by simpa [dist_eq_norm] using hd1.2
    linarith [(abs_le.1 h1).1]
  have hδz0 : δ ≤ z0.im := by linarith
  have hW : ∀ r ∈ Icc (0 : ℝ) T,
      |Wof κ T hT f r - Wof κ T hT f0 r| ≤ Real.sqrt κ * dist f f0 := by
    intro r _
    simp only [Wof]
    rw [← mul_sub, abs_mul, abs_of_nonneg (Real.sqrt_nonneg κ), ← Real.dist_eq]
    exact mul_le_mul_of_nonneg_left (ContinuousMap.dist_apply_le_dist _) (Real.sqrt_nonneg κ)
  have e1 : ‖Fm κ T hT (f, z) - Fm κ T hT (f0, z)‖ ≤ Real.sqrt κ * dist f f0 * L := by
    have := ReverseFlow.norm_revMap_sub_revMap_le (Wof κ T hT f) (Wof κ T hT f0)
      (continuous_Wof κ T hT f) (continuous_Wof κ T hT f0) z (by linarith) hT hW
    refine this.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity))
    exact div_le_div_of_nonneg_left (by linarith) (by positivity)
      (pow_le_pow_left₀ hδ.le him 2)
  have e2 : ‖Fm κ T hT (f0, z) - Fm κ T hT (f0, z0)‖ ≤ ‖z - z0‖ * L :=
    ReverseFlow.norm_revMap_sub_revMap_point (Wof κ T hT f0) (continuous_Wof κ T hT f0) hδ
      him hδz0 hT
  have h3 : Real.sqrt κ * dist f f0 * L ≤ Real.sqrt κ * η * L := by
    gcongr; exact hd2.1.le
  have h4 : ‖z - z0‖ * L < η * L := by
    have : ‖z - z0‖ < η := by simpa [dist_eq_norm] using hd2.2
    exact mul_lt_mul_of_pos_right this hL
  have h5 : Real.sqrt κ * η * L + η * L = ε := by
    rw [hηdef]; field_simp
  calc dist (Fm κ T hT (f, z)) (Fm κ T hT (f0, z0))
      = ‖Fm κ T hT (f, z) - Fm κ T hT (f0, z0)‖ := dist_eq_norm _ _
    _ ≤ ‖Fm κ T hT (f, z) - Fm κ T hT (f0, z)‖ + ‖Fm κ T hT (f0, z) - Fm κ T hT (f0, z0)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ < ε := by linarith

theorem measurable_Fm (κ T : ℝ) (hT : 0 ≤ T) : Measurable (Fm κ T hT) := by
  classical
  have : Fm κ T hT = (univ ×ˢ H).piecewise (Fm κ T hT) (fun _ => 0) := by
    funext p
    by_cases hp : p ∈ univ ×ˢ H
    · exact (piecewise_eq_of_mem _ _ _ hp).symm
    · rw [piecewise_eq_of_notMem _ _ _ hp]
      exact revMap_of_not_mem hT (fun h => hp ⟨mem_univ _, h⟩)
  rw [this]
  exact (continuousOn_Fm κ T hT).measurable_piecewise continuousOn_const
    (MeasurableSet.univ.prod isOpen_H.measurableSet)

theorem measurable_revMap_Wof (κ T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, ℝ)) :
    Measurable (revMap (Wof κ T hT f) T) :=
  show Measurable fun z => Fm κ T hT (f, z) from
    (measurable_Fm κ T hT).comp (measurable_const.prodMk measurable_id)

/-- Step sizes for difference quotients. -/
def hstep (n : ℕ) : ℂ := ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)

/-- A jointly measurable version of `deriv (revMap W T)`. -/
def Dm (κ T : ℝ) (hT : 0 ≤ T) (p : C(Icc (0 : ℝ) T, ℝ) × ℂ) : ℂ :=
  limUnder atTop fun n => (hstep n)⁻¹ • (Fm κ T hT (p.1, p.2 + hstep n) - Fm κ T hT p)

theorem measurable_Dm (κ T : ℝ) (hT : 0 ≤ T) : Measurable (Dm κ T hT) := by
  refine (StronglyMeasurable.limUnder fun n => ?_).measurable
  refine Measurable.stronglyMeasurable ?_
  exact (((measurable_Fm κ T hT).comp (measurable_fst.prodMk
    (measurable_snd.add_const _))).sub (measurable_Fm κ T hT)).const_smul ((hstep n)⁻¹ : ℂ)

theorem Dm_eq (κ T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, ℝ)) {z : ℂ} (hz : z ∈ H) :
    Dm κ T hT (f, z) = deriv (revMap (Wof κ T hT f) T) z := by
  have hd := hasDerivAt_revMap (Wof κ T hT f) (continuous_Wof κ T hT f) hT hz
  have ht := hd.tendsto_slope_zero
  have hs : Tendsto hstep atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n =>
      mem_compl_singleton_iff.2 (ofReal_ne_zero.2 (by positivity))⟩
    have := (continuous_ofReal.tendsto 0).comp
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    rw [Complex.ofReal_zero] at this
    exact this
  rw [hd.deriv]
  exact (ht.comp hs).limUnder_eq

/-- A jointly measurable version of `hTrev`. -/
def hTm (κ T : ℝ) (hT : 0 ≤ T) (p : C(Icc (0 : ℝ) T, ℝ) × ℂ) : ℝ :=
  h0rev κ (Fm κ T hT p) + Qc (Real.sqrt κ) * Real.log ‖Dm κ T hT p‖

theorem measurable_hTm (κ T : ℝ) (hT : 0 ≤ T) : Measurable (hTm κ T hT) := by
  unfold hTm h0rev
  exact (measurable_const.mul (Real.measurable_log.comp
    (measurable_Fm κ T hT).norm)).add (measurable_const.mul (Real.measurable_log.comp
    (measurable_Dm κ T hT).norm))

theorem hTm_eq (κ T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, ℝ)) {z : ℂ} (hz : z ∈ H) :
    hTm κ T hT (f, z) = hTrev κ (Wof κ T hT f) T z := by
  simp only [hTm, hTrev, Dm_eq κ T hT f hz]
  rfl

theorem measurable_evalReg_push (κ T : ℝ) (hT : 0 ≤ T) (a : ℂ → ℝ) :
    Measurable fun p : C(Icc (0 : ℝ) T, ℝ) × FieldSample =>
      evalReg p.2 ((tdens a).map (revMap (Wof κ T hT p.1) T)) := by
  have heq : ∀ p : C(Icc (0 : ℝ) T, ℝ) × FieldSample,
      evalReg p.2 ((tdens a).map (revMap (Wof κ T hT p.1) T)) =
        limUnder atTop fun k => ∫ z, avgReg p.2 k (Fm κ T hT (p.1, z)) ∂(tdens a) := by
    intro p
    unfold evalReg
    congr 1
    funext k
    rw [integral_map (measurable_revMap_Wof κ T hT p.1).aemeasurable
      (show Measurable fun w => avgReg p.2 k w from
        (measurable_avgReg k).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable]
    rfl
  rw [show (fun p : C(Icc (0 : ℝ) T, ℝ) × FieldSample =>
      evalReg p.2 ((tdens a).map (revMap (Wof κ T hT p.1) T))) = _ from funext heq]
  refine (StronglyMeasurable.limUnder fun k => ?_).measurable
  have hm : Measurable fun q : (C(Icc (0 : ℝ) T, ℝ) × FieldSample) × ℂ =>
      avgReg q.1.2 k (Fm κ T hT (q.1.1, q.2)) :=
    (measurable_avgReg k).comp ((measurable_snd.comp measurable_fst).prodMk
      ((measurable_Fm κ T hT).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)))
  exact hm.stronglyMeasurable.integral_prod_right'

/-! ## The right-hand field for a fixed driver path -/

/-- The right-hand field of Theorem 1.2 for a fixed driver path `f` and GFF sample `x`. -/
def Y2f (κ T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, ℝ)) (x : FieldSample) : FieldSample :=
  ofFun (hTrev κ (Wof κ T hT f) T) + coordChange x (revMap (Wof κ T hT f) T) 0

theorem pairRaw_Y2f (κ T : ℝ) (hT : 0 ≤ T) (ρ : ℂ → ℝ) (f : C(Icc (0 : ℝ) T, ℝ))
    (x : FieldSample) :
    pairRaw (Y2f κ T hT f x) ρ =
      (ofFun (hTrev κ (Wof κ T hT f) T) (tdens ρ) -
        ofFun (hTrev κ (Wof κ T hT f) T) (tdens fun z => -ρ z)) +
      (evalReg x ((tdens ρ).map (revMap (Wof κ T hT f) T)) -
        evalReg x ((tdens fun z => -ρ z).map (revMap (Wof κ T hT f) T))) := by
  simp only [pairRaw_eq_tdens, Y2f, coordChange, Pi.add_apply, zero_mul, add_zero]
  ring

theorem ofFun_hTrev_eq (κ T : ℝ) (hT : 0 ≤ T) {a : ℂ → ℝ} {K : Set ℂ} {M δ : ℝ}
    (hd : Dens a K M δ) (f : C(Icc (0 : ℝ) T, ℝ)) :
    ofFun (hTrev κ (Wof κ T hT f) T) (tdens a) = ∫ z, hTm κ T hT (f, z) ∂(tdens a) := by
  unfold ofFun
  refine integral_congr_ae ?_
  have : ∀ᵐ z ∂(tdens a), z ∈ K := ae_iff.2 hd.tdens_compl
  filter_upwards [this] with z hz
  exact (hTm_eq κ T hT f (hd.subH hz)).symm

theorem measurable_pair_Y2f (κ T : ℝ) (hT : 0 ≤ T) (ρ : TestFun H) :
    Measurable fun p : C(Icc (0 : ℝ) T, ℝ) × FieldSample => pairRaw (Y2f κ T hT p.1 p.2) ρ.1 := by
  obtain ⟨M, δ, hd⟩ := exists_dens ρ
  have heq : ∀ p : C(Icc (0 : ℝ) T, ℝ) × FieldSample, pairRaw (Y2f κ T hT p.1 p.2) ρ.1 =
      ((∫ z, hTm κ T hT (p.1, z) ∂(tdens ρ.1)) -
        ∫ z, hTm κ T hT (p.1, z) ∂(tdens fun z => -ρ.1 z)) +
      (evalReg p.2 ((tdens ρ.1).map (revMap (Wof κ T hT p.1) T)) -
        evalReg p.2 ((tdens fun z => -ρ.1 z).map (revMap (Wof κ T hT p.1) T))) := by
    intro p
    rw [pairRaw_Y2f, ofFun_hTrev_eq κ T hT hd, ofFun_hTrev_eq κ T hT hd.neg]
  rw [show (fun p : C(Icc (0 : ℝ) T, ℝ) × FieldSample => pairRaw (Y2f κ T hT p.1 p.2) ρ.1) =
    _ from funext heq]
  have hi : ∀ a : ℂ → ℝ, Measurable fun p : C(Icc (0 : ℝ) T, ℝ) × FieldSample =>
      ∫ z, hTm κ T hT (p.1, z) ∂(tdens a) := fun a =>
    ((measurable_hTm κ T hT).stronglyMeasurable.integral_prod_right').measurable.comp
      measurable_fst
  exact ((hi _).sub (hi _)).add
    ((measurable_evalReg_push κ T hT _).sub (measurable_evalReg_push κ T hT _))

theorem continuousOn_hTrev (κ : ℝ) {W : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T) :
    ContinuousOn (hTrev κ W T) H := by
  have hd := differentiableOn_revMap W hW hT
  show ContinuousOn (fun z => h0rev κ (revMap W T z) +
    Qc (Real.sqrt κ) * Real.log ‖deriv (revMap W T) z‖) H
  refine ((continuousOn_h0rev κ).comp hd.continuousOn fun z hz => ?_).add
    (continuousOn_const.mul ?_)
  · show 0 < (revMap W T z).im
    exact lt_of_lt_of_le hz (im_le_im_revMap W hW z hz hT)
  · exact ContinuousOn.log ((hd.deriv isOpen_H).continuousOn.norm) fun z hz =>
      norm_ne_zero_iff.2 (deriv_revMap_ne_zero W hW hT hz)

theorem goodMap_Wof (κ T : ℝ) (hT : 0 ≤ T) (f : C(Icc (0 : ℝ) T, ℝ)) :
    GoodMap (revMap (Wof κ T hT f) T) :=
  goodMap_revMap (continuous_Wof κ T hT f) hT (measurable_revMap_Wof κ T hT f)

theorem cond_Y2f (κ T : ℝ) (hT : 0 ≤ T) {Ω : Type*} [MeasurableSpace Ω] {X : Ω → FieldSample}
    {P : Measure Ω} [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P) (ρ : TestFun H)
    (f : C(Icc (0 : ℝ) T, ℝ)) :
    ∀ᵐ ω ∂P, pairRaw (Y2f κ T hT f (X ω)) ρ.1 = Xfun κ (Wof κ T hT f) T ρ.1 +
      (X ω ((tdens ρ.1).map (revMap (Wof κ T hT f) T)) -
        X ω ((tdens fun z => -ρ.1 z).map (revMap (Wof κ T hT f) T))) := by
  obtain ⟨M, δ, hd⟩ := exists_dens ρ
  have hg := goodMap_Wof κ T hT f
  have hc := pairRaw_ofFun (continuousOn_hTrev κ (continuous_Wof κ T hT f) hT) ρ
  rw [pairRaw_eq_tdens] at hc
  filter_upwards [push_reg hX hg hd, push_reg hX hg hd.neg] with ω h1 h2
  rw [pairRaw_Y2f, h1, h2, hc]
  rfl

theorem cond_charFun_Y2f (κ T : ℝ) (hT : 0 ≤ T) {Ω : Type*} [MeasurableSpace Ω]
    {X : Ω → FieldSample} {P : Measure Ω} [IsProbabilityMeasure P]
    (hX : IsFreeGFFModConstH X P) (ρ : TestFun0 H) (f : C(Icc (0 : ℝ) T, ℝ)) :
    ∫ ω, cexp (I * (pairRaw (Y2f κ T hT f (X ω)) ρ.1.1 : ℂ)) ∂P =
      cexp (I * (Xfun κ (Wof κ T hT f) T ρ.1.1 : ℂ) - (Efun (Wof κ T hT f) T ρ.1.1 : ℂ) / 2) := by
  have h : ∫ ω, cexp (I * (pairRaw (Y2f κ T hT f (X ω)) ρ.1.1 : ℂ)) ∂P =
      ∫ ω, cexp (I * ((Xfun κ (Wof κ T hT f) T ρ.1.1 +
        (X ω ((tdens ρ.1.1).map (revMap (Wof κ T hT f) T)) -
          X ω ((tdens fun z => -ρ.1.1 z).map (revMap (Wof κ T hT f) T))) : ℝ) : ℂ)) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [cond_Y2f κ T hT hX ρ.1 f] with ω hω
    rw [hω]
  rw [h]
  simp_rw [ofReal_add, mul_add, Complex.exp_add]
  rw [integral_const_mul, cond_charFun hX (goodMap_Wof κ T hT f) ρ, ← Complex.exp_add]
  congr 1
  simp only [Efun, Ef]
  ring

/-! ## Independence and the product law -/

theorem integral_indep {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {g : Ω → α} {Y : Ω → β}
    (hg : Measurable g) (hY : Measurable Y) (hind : IndepFun g Y P) {G : α × β → ℂ}
    (hG : Measurable G) (hb : ∀ p, ‖G p‖ ≤ 1) :
    ∫ ω, G (g ω, Y ω) ∂P = ∫ ω, (∫ ω', G (g ω, Y ω') ∂P) ∂P := by
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hg.aemeasurable hY.aemeasurable).1 hind
  have hint : Integrable G ((P.map g).prod (P.map Y)) :=
    Integrable.of_bound hG.aestronglyMeasurable 1 (ae_of_all _ hb)
  calc ∫ ω, G (g ω, Y ω) ∂P = ∫ p, G p ∂(P.map fun ω => (g ω, Y ω)) :=
        (integral_map (hg.prodMk hY).aemeasurable hG.aestronglyMeasurable).symm
    _ = ∫ p, G p ∂((P.map g).prod (P.map Y)) := by rw [hprod]
    _ = ∫ a, ∫ b, G (a, b) ∂(P.map Y) ∂(P.map g) := integral_prod _ hint
    _ = ∫ ω, ∫ b, G (g ω, b) ∂(P.map Y) ∂P :=
        integral_map hg.aemeasurable
          (hG.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
    _ = ∫ ω, (∫ ω', G (g ω, Y ω') ∂P) ∂P := by
        congr 1
        funext ω
        exact integral_map hY.aemeasurable
          (hG.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable

theorem ae_indep {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {g : Ω → α} {Y : Ω → β}
    (hg : Measurable g) (hY : Measurable Y) (hind : IndepFun g Y P) {E : Set (α × β)}
    (hE : MeasurableSet E) (h : ∀ a, ∀ᵐ ω ∂P, (a, Y ω) ∈ E) :
    ∀ᵐ ω ∂P, (g ω, Y ω) ∈ E := by
  have hprod := (indepFun_iff_map_prod_eq_prod_map_map hg.aemeasurable hY.aemeasurable).1 hind
  have : ∀ᵐ p ∂(P.map fun ω => (g ω, Y ω)), p ∈ E := by
    rw [hprod]
    exact (Measure.ae_prod_mem_iff_ae_ae_mem hE).2 (ae_of_all _ fun a =>
      (ae_map_iff hY.aemeasurable (measurable_prodMk_left hE)).2 (h a))
  exact (ae_map_iff (hg.prodMk hY).aemeasurable hE).1 this

theorem indepFun_pathC (T : ℝ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample} (hind : IndepFun (pathOf B) X P)
    (hc : ∀ ω, Continuous fun t => B t ω) : IndepFun (pathC T B hc) X P := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at hind ⊢
  intro s t hs ht
  have key : ∃ s', MeasurableSet s' ∧ pathOf B ⁻¹' s' = pathC T B hc ⁻¹' s := by
    let _ : MeasurableSpace Ω := MeasurableSpace.comap (pathOf B) MeasurableSpace.pi
    have hgm : Measurable (pathC T B hc) := ContinuousMap.measurable_iff_eval.2 fun x =>
      show Measurable ((fun f : ℝ≥0 → ℝ => f x.1.toNNReal) ∘ pathOf B) from
        (measurable_pi_apply _).comp (comap_measurable (pathOf B))
    exact hgm hs
  obtain ⟨s', hs', hpre⟩ := key
  rw [← hpre]
  exact hind s' t hs' ht

/-! ## (b) The right-hand side -/

/-- **(b)** The characteristic function of the right-hand field `𝔥_T + h̃∘f_T` paired with a
mass-zero test function `ρ` is `Φ_T(ρ)`. -/
theorem charFun_rhs (κ T : ℝ) (hT : 0 ≤ T) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample)
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P)
    (ρ : TestFun0 H) :
    ∫ ω, cexp (I * (pairRaw (ofFun (hTrev κ (drive κ B ω) T) +
        coordChange (X ω) (revMap (drive κ B ω) T) 0) ρ.1.1 : ℂ)) ∂P = Phi κ T B P ρ.1.1 := by
  obtain ⟨B', hB'm, hB'c, hB'eq⟩ := exists_good_version hB
  have hdrive : ∀ᵐ ω ∂P, drive κ B' ω = drive κ B ω :=
    hB'eq.mono fun ω h => funext fun t => by simp [drive, h]
  have hind' : IndepFun (pathOf B') X P :=
    hind.congr (hB'eq.mono fun ω h => (funext fun t => (h t).symm : pathOf B ω = pathOf B' ω))
      (ae_eq_refl _)
  set g := pathC T B' hB'c with hg_def
  have hgm : Measurable g := measurable_pathC T hB'm hB'c
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  have hig : IndepFun g X P := indepFun_pathC T hind' hB'c
  have hrev : ∀ ω, revMap (drive κ B' ω) T = revMap (Wof κ T hT (g ω)) T :=
    revMap_drive_eq κ T hT B' hB'c
  set G : C(Icc (0 : ℝ) T, ℝ) × FieldSample → ℂ :=
    fun p => cexp (I * (pairRaw (Y2f κ T hT p.1 p.2) ρ.1.1 : ℂ)) with hG_def
  have hGm : Measurable G := Complex.measurable_exp.comp (measurable_const.mul
    (Complex.measurable_ofReal.comp (measurable_pair_Y2f κ T hT ρ.1)))
  have hGb : ∀ p, ‖G p‖ ≤ 1 := fun p => by
    simp [G, Complex.norm_exp, Complex.mul_re]
  calc _ = ∫ ω, G (g ω, X ω) ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [hdrive] with ω h
        simp only [G, Y2f]
        rw [← h, hTrev_congr (hrev ω) κ, hrev ω]
    _ = ∫ ω, (∫ ω', G (g ω, X ω') ∂P) ∂P := integral_indep hgm hXm hig hGm hGb
    _ = ∫ ω, cexp (I * (Xfun κ (Wof κ T hT (g ω)) T ρ.1.1 : ℂ) -
          (Efun (Wof κ T hT (g ω)) T ρ.1.1 : ℂ) / 2) ∂P := by
        congr 1
        funext ω
        exact cond_charFun_Y2f κ T hT hX ρ (g ω)
    _ = Phi κ T B P ρ.1.1 := by
        unfold Phi
        refine integral_congr_ae ?_
        filter_upwards [hdrive] with ω h
        rw [← h, Xfun_congr (hrev ω), Efun_congr (hrev ω)]

/-! ## Linearity of the pairings -/

/-- A random field is (almost surely) linear in the mass-zero test function: the explicit
linearity hypothesis of `fieldLawMod0_eq_of_charFun`. -/
def LinearPairing {Ω : Type*} [MeasurableSpace Ω] (Y : Ω → FieldSample) (P : Measure Ω) :
    Prop :=
  ∀ (ρ₁ ρ₂ ρ₃ : TestFun0 H) (a : ℝ), (∀ z, ρ₃.1.1 z = a * ρ₁.1.1 z + ρ₂.1.1 z) →
    ∀ᵐ ω ∂P, pairRaw (Y ω) ρ₃.1.1 = a * pairRaw (Y ω) ρ₁.1.1 + pairRaw (Y ω) ρ₂.1.1

theorem ofReal_max_zero (x : ℝ) : ENNReal.ofReal (max x 0) = ENNReal.ofReal x := by
  rcases le_total 0 x with h | h
  · rw [max_eq_left h]
  · rw [max_eq_right h, ENNReal.ofReal_zero, ENNReal.ofReal_of_nonpos h]

theorem tdens_three (b : ℝ≥0) {φ ψ χ : ℂ → ℝ} (hφ : Measurable φ) (hψ : Measurable ψ)
    (_hχ : Measurable χ) :
    tdens φ + b • tdens ψ + tdens χ = volume.withDensity fun z =>
      ENNReal.ofReal (max (φ z) 0 + b * max (ψ z) 0 + max (χ z) 0) := by
  have mφ : Measurable fun z => ENNReal.ofReal (φ z) := ENNReal.measurable_ofReal.comp hφ
  have mψ : Measurable fun z => ENNReal.ofReal (ψ z) := ENNReal.measurable_ofReal.comp hψ
  unfold tdens
  rw [ENNReal.smul_def, ← withDensity_smul _ mψ, ← withDensity_add_left mφ,
    ← withDensity_add_left (mφ.add (mψ.const_smul _))]
  congr 1
  funext z
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
    ofReal_max_zero, ofReal_max_zero, ofReal_max_zero, ENNReal.ofReal_coe_nnreal]

theorem ae_lin_core {Ω : Type*} [MeasurableSpace Ω] {X : Ω → FieldSample} {P : Measure Ω}
    (hX : IsFreeGFFModConstH X P) {m3p m3m mu mv m2p m2m : Measure ℂ}
    (h3p : IsAdmissibleH m3p) (h3m : IsAdmissibleH m3m) (hmu : IsAdmissibleH mu)
    (hmv : IsAdmissibleH mv) (h2p : IsAdmissibleH m2p) (h2m : IsAdmissibleH m2m) (b : ℝ≥0)
    (hid : m3p + b • mv + m2m = m3m + b • mu + m2p) :
    ∀ᵐ ω ∂P, X ω m3p - X ω m3m = b * (X ω mu - X ω mv) + (X ω m2p - X ω m2m) := by
  have hs : ∀ {μ : Measure ℂ}, IsAdmissibleH μ → IsAdmissibleH (b • μ) := fun hμ => by
    rw [ENNReal.smul_def]; exact isAdmissibleH_smul hμ ENNReal.coe_lt_top
  have hN₁ : IsAdmissibleH (b • mv + (1 : ℝ≥0) • m2m) :=
    isAdmissibleH_add (hs hmv) (by rw [one_smul]; exact h2m)
  have hN₂ : IsAdmissibleH (b • mu + (1 : ℝ≥0) • m2p) :=
    isAdmissibleH_add (hs hmu) (by rw [one_smul]; exact h2p)
  have hM : (1 : ℝ≥0) • m3p + (1 : ℝ≥0) • (b • mv + (1 : ℝ≥0) • m2m) =
      (1 : ℝ≥0) • m3m + (1 : ℝ≥0) • (b • mu + (1 : ℝ≥0) • m2p) := by
    simp only [one_smul]
    rw [← add_assoc, ← add_assoc, hid]
  filter_upwards [hX.linear m3p _ h3p hN₁ 1 1, hX.linear mv m2m hmv h2m b 1,
    hX.linear m3m _ h3m hN₂ 1 1, hX.linear mu m2p hmu h2p b 1] with ω hA hB hC hD
  rw [hM] at hA
  push_cast at hA hB hC hD
  linear_combination -(hA - hC) - hB + hD

theorem tdens_map_comb {f : ℂ → ℂ} (hf : Measurable f) (b : ℝ≥0) {r3 v r2 u : ℂ → ℝ}
    (h3 : Measurable r3) (hv : Measurable v) (h2 : Measurable r2) (hu : Measurable u)
    (h : ∀ z, max (r3 z) 0 + b * max (v z) 0 + max (-r2 z) 0 =
      max (-r3 z) 0 + b * max (u z) 0 + max (r2 z) 0) :
    (tdens r3).map f + b • (tdens v).map f + (tdens fun z => -r2 z).map f =
      (tdens fun z => -r3 z).map f + b • (tdens u).map f + (tdens r2).map f := by
  have hid : tdens r3 + b • tdens v + tdens (fun z => -r2 z) =
      tdens (fun z => -r3 z) + b • tdens u + tdens r2 := by
    rw [tdens_three b h3 hv (show Measurable fun z => -r2 z from h2.neg),
      tdens_three b (show Measurable fun z => -r3 z from h3.neg) hu h2]
    congr 1
    funext z
    rw [h z]
  have := congrArg (Measure.map f) hid
  simpa only [Measure.map_add _ _ hf, Measure.map_smul _ hf.aemeasurable] using this

/-- Linearity of the balanced GFF pairings with pushforwards under a good map. -/
theorem ae_lin_push {Ω : Type*} [MeasurableSpace Ω] {X : Ω → FieldSample} {P : Measure Ω}
    (hX : IsFreeGFFModConstH X P) {f : ℂ → ℂ} (hf : GoodMap f) (ρ₁ ρ₂ ρ₃ : TestFun H) (a : ℝ)
    (h : ∀ z, ρ₃.1 z = a * ρ₁.1 z + ρ₂.1 z) :
    ∀ᵐ ω ∂P, X ω ((tdens ρ₃.1).map f) - X ω ((tdens fun z => -ρ₃.1 z).map f) =
      a * (X ω ((tdens ρ₁.1).map f) - X ω ((tdens fun z => -ρ₁.1 z).map f)) +
      (X ω ((tdens ρ₂.1).map f) - X ω ((tdens fun z => -ρ₂.1 z).map f)) := by
  obtain ⟨M₁, δ₁, d₁⟩ := exists_dens ρ₁
  obtain ⟨M₂, δ₂, d₂⟩ := exists_dens ρ₂
  obtain ⟨M₃, δ₃, d₃⟩ := exists_dens ρ₃
  have hreal : ∀ z, max (ρ₃.1 z) 0 - max (-ρ₃.1 z) 0 -
      a * (max (ρ₁.1 z) 0 - max (-ρ₁.1 z) 0) - (max (ρ₂.1 z) 0 - max (-ρ₂.1 z) 0) = 0 := by
    intro z
    rw [max_sub_max_neg, max_sub_max_neg, max_sub_max_neg, h z]
    ring
  rcases le_total 0 a with ha | ha
  · have hb : ((a.toNNReal : ℝ≥0) : ℝ) = a := Real.coe_toNNReal a ha
    have hid := tdens_map_comb hf.meas a.toNNReal d₃.meas d₁.neg.meas d₂.meas d₁.meas
      (fun z => by rw [hb]; linear_combination hreal z)
    filter_upwards [ae_lin_core hX (push_admissible hf d₃) (push_admissible hf d₃.neg)
      (push_admissible hf d₁) (push_admissible hf d₁.neg) (push_admissible hf d₂)
      (push_admissible hf d₂.neg) a.toNNReal hid] with ω hω
    rw [hω, hb]
  · have hb : (((-a).toNNReal : ℝ≥0) : ℝ) = -a := Real.coe_toNNReal (-a) (by linarith)
    have hid := tdens_map_comb hf.meas (-a).toNNReal d₃.meas d₁.meas d₂.meas d₁.neg.meas
      (fun z => by rw [hb]; linear_combination hreal z)
    filter_upwards [ae_lin_core hX (push_admissible hf d₃) (push_admissible hf d₃.neg)
      (push_admissible hf d₁.neg) (push_admissible hf d₁) (push_admissible hf d₂)
      (push_admissible hf d₂.neg) (-a).toNNReal hid] with ω hω
    rw [hω, hb]
    ring

theorem pairRaw_add (x y : FieldSample) (ρ : ℂ → ℝ) :
    pairRaw (x + y) ρ = pairRaw x ρ + pairRaw y ρ := by
  simp only [pairRaw, Pi.add_apply]; ring

theorem integral_lin {g : ℂ → ℝ} (hg : ContinuousOn g H) (ρ₁ ρ₂ ρ₃ : TestFun H) (a : ℝ)
    (h : ∀ z, ρ₃.1 z = a * ρ₁.1 z + ρ₂.1 z) :
    ∫ z, ρ₃.1 z * g z = a * (∫ z, ρ₁.1 z * g z) + ∫ z, ρ₂.1 z * g z := by
  have i1 : Integrable fun z => ρ₁.1 z * g z :=
    integrable_comp_mul (ψ := id) continuous_id rfl ρ₁ hg
  have i2 : Integrable fun z => ρ₂.1 z * g z :=
    integrable_comp_mul (ψ := id) continuous_id rfl ρ₂ hg
  rw [← integral_const_mul, ← integral_add (i1.const_mul a) i2]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [h z]
  ring

/-- Linearity of the left-hand field of Theorem 1.2. -/
theorem linear_lhs (κ : ℝ) {Ω : Type*} [MeasurableSpace Ω] {X : Ω → FieldSample}
    {P : Measure Ω} (hX : IsFreeGFFModConstH X P) :
    LinearPairing (fun ω => ofFun (h0rev κ) + X ω) P := by
  intro ρ₁ ρ₂ ρ₃ a h
  filter_upwards [ae_lin_push hX goodMap_id ρ₁.1 ρ₂.1 ρ₃.1 a h] with ω hω
  simp only [Measure.map_id] at hω
  simp only [pairRaw_add, pairRaw_ofFun (continuousOn_h0rev κ), pairRaw_eq_tdens (X ω)]
  rw [integral_lin (continuousOn_h0rev κ) ρ₁.1 ρ₂.1 ρ₃.1 a h, hω]
  ring

/-- Linearity of the right-hand field for fixed driver path, almost surely in the GFF. -/
theorem linear_Y2f (κ T : ℝ) (hT : 0 ≤ T) {Ω : Type*} [MeasurableSpace Ω] {X : Ω → FieldSample}
    {P : Measure Ω} [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    (ρ₁ ρ₂ ρ₃ : TestFun0 H) (a : ℝ) (h : ∀ z, ρ₃.1.1 z = a * ρ₁.1.1 z + ρ₂.1.1 z)
    (f : C(Icc (0 : ℝ) T, ℝ)) :
    ∀ᵐ ω ∂P, pairRaw (Y2f κ T hT f (X ω)) ρ₃.1.1 =
      a * pairRaw (Y2f κ T hT f (X ω)) ρ₁.1.1 + pairRaw (Y2f κ T hT f (X ω)) ρ₂.1.1 := by
  filter_upwards [cond_Y2f κ T hT hX ρ₁.1 f, cond_Y2f κ T hT hX ρ₂.1 f,
    cond_Y2f κ T hT hX ρ₃.1 f, ae_lin_push hX (goodMap_Wof κ T hT f) ρ₁.1 ρ₂.1 ρ₃.1 a h]
    with ω h1 h2 h3 hω
  rw [h1, h2, h3, hω]
  simp only [Xfun]
  rw [integral_lin (continuousOn_hTrev κ (continuous_Wof κ T hT f) hT) ρ₁.1 ρ₂.1 ρ₃.1 a h]
  ring

/-- Linearity of the right-hand field of Theorem 1.2 (for a driver with continuous paths). -/
theorem linear_rhs (κ T : ℝ) (hT : 0 ≤ T) {Ω : Type*} [MeasurableSpace Ω] {X : Ω → FieldSample}
    {P : Measure Ω} [IsProbabilityMeasure P] (hX : IsFreeGFFModConstH X P)
    {g : Ω → C(Icc (0 : ℝ) T, ℝ)} (hg : Measurable g) (hind : IndepFun g X P) :
    LinearPairing (fun ω => Y2f κ T hT (g ω) (X ω)) P := by
  intro ρ₁ ρ₂ ρ₃ a h
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  have hE : MeasurableSet {p : C(Icc (0 : ℝ) T, ℝ) × FieldSample |
      pairRaw (Y2f κ T hT p.1 p.2) ρ₃.1.1 =
        a * pairRaw (Y2f κ T hT p.1 p.2) ρ₁.1.1 + pairRaw (Y2f κ T hT p.1 p.2) ρ₂.1.1} :=
    measurableSet_eq_fun (measurable_pair_Y2f κ T hT ρ₃.1)
      ((measurable_const.mul (measurable_pair_Y2f κ T hT ρ₁.1)).add
        (measurable_pair_Y2f κ T hT ρ₂.1))
  exact ae_indep hg hXm hind hE fun f => linear_Y2f κ T hT hX ρ₁ ρ₂ ρ₃ a h f

/-! ## (c) Characteristic functions determine `fieldLawMod0` -/

/-- The mass-zero test function `a ρ₁ + ρ₂`. -/
def tfComb (a : ℝ) (ρ₁ ρ₂ : TestFun0 H) : TestFun0 H :=
  ⟨⟨fun z => a * ρ₁.1.1 z + ρ₂.1.1 z, (contDiff_const.mul ρ₁.1.2.1).add ρ₂.1.2.1,
    (ρ₁.1.2.2.1.mul_left).add ρ₂.1.2.2.1, by
      have hs : Function.support (fun z => a * ρ₁.1.1 z + ρ₂.1.1 z) ⊆
          Function.support ρ₁.1.1 ∪ Function.support ρ₂.1.1 :=
        fun z hz => by
          by_contra hc
          simp only [mem_union, Function.mem_support, not_or, not_not] at hc
          simp [hc.1, hc.2] at hz
      exact (closure_mono hs).trans (by
        rw [closure_union]; exact union_subset ρ₁.1.2.2.2 ρ₂.1.2.2.2)⟩, by
    have i1 : Integrable ρ₁.1.1 :=
      (tf_continuous ρ₁.1).integrable_of_hasCompactSupport ρ₁.1.2.2.1
    have i2 : Integrable ρ₂.1.1 :=
      (tf_continuous ρ₂.1).integrable_of_hasCompactSupport ρ₂.1.2.2.1
    show ∫ z, (a * ρ₁.1.1 z + ρ₂.1.1 z) = 0
    rw [integral_add (i1.const_mul a) i2, integral_const_mul, ρ₁.2, ρ₂.2]
    ring⟩

/-- The zero mass-zero test function. -/
def tfZero : TestFun0 H :=
  ⟨⟨fun _ => 0, contDiff_const, HasCompactSupport.zero, by simp [tsupport]⟩, by simp⟩

theorem exists_tf_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (ρs : ι → TestFun0 H) :
    ∃ ρ : TestFun0 H, ∀ z, ρ.1.1 z = ∑ i ∈ s, c i * (ρs i).1.1 z := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨tfZero, fun z => by simp [tfZero]⟩
  | insert k s hk ih =>
    obtain ⟨ρ', hρ'⟩ := ih
    exact ⟨tfComb (c k) (ρs k) ρ', fun z => by
      rw [Finset.sum_insert hk]; simp [tfComb, hρ' z]⟩

theorem ae_pairRaw_sum {Ω : Type*} [MeasurableSpace Ω] {Y : Ω → FieldSample} {P : Measure Ω}
    (hl : LinearPairing Y P) {ι : Type*} (s : Finset ι) (c : ι → ℝ) (ρs : ι → TestFun0 H) :
    ∀ ρ : TestFun0 H, (∀ z, ρ.1.1 z = ∑ i ∈ s, c i * (ρs i).1.1 z) →
      ∀ᵐ ω ∂P, pairRaw (Y ω) ρ.1.1 = ∑ i ∈ s, c i * pairRaw (Y ω) (ρs i).1.1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro ρ hρ
    refine ae_of_all _ fun ω => ?_
    have h0 : ρ.1.1 = fun _ => 0 := funext fun z => by simpa using hρ z
    simp [pairRaw, h0]
  | insert k s hk ih =>
    intro ρ hρ
    obtain ⟨ρ', hρ'⟩ := exists_tf_sum s c ρs
    have hlin := hl (ρs k) ρ' ρ (c k) (fun z => by rw [hρ z, Finset.sum_insert hk, hρ' z])
    filter_upwards [ih ρ' hρ', hlin] with ω h1 h2
    rw [Finset.sum_insert hk, h2, h1]

/-- **(c)** Two random fields with measurable, almost surely linear pairings whose pairings with
every mass-zero test function have the same characteristic function have the same law modulo
additive constants (Cramér–Wold). -/
theorem fieldLawMod0_eq_of_charFun {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Y₁ Y₂ : Ω → FieldSample}
    (hm₁ : ∀ ρ : TestFun0 H, Measurable fun ω => pairRaw (Y₁ ω) ρ.1.1)
    (hm₂ : ∀ ρ : TestFun0 H, Measurable fun ω => pairRaw (Y₂ ω) ρ.1.1)
    (hl₁ : LinearPairing Y₁ P) (hl₂ : LinearPairing Y₂ P)
    (hc : ∀ ρ : TestFun0 H, ∫ ω, cexp (I * (pairRaw (Y₁ ω) ρ.1.1 : ℂ)) ∂P =
      ∫ ω, cexp (I * (pairRaw (Y₂ ω) ρ.1.1 : ℂ)) ∂P) :
    fieldLawMod0 H Y₁ P = fieldLawMod0 H Y₂ P := by
  classical
  unfold fieldLawMod0
  refine (map_eq_iff_forall_finset_map_restrict_eq
    (X := fun (ρ : TestFun0 H) ω => pairRaw (Y₁ ω) ρ.1.1)
    (Y := fun (ρ : TestFun0 H) ω => pairRaw (Y₂ ω) ρ.1.1)
    (measurable_pi_iff.2 hm₁).aemeasurable (measurable_pi_iff.2 hm₂).aemeasurable).2 ?_
  intro J
  have hF : ∀ {Y : Ω → FieldSample}, (∀ ρ : TestFun0 H, Measurable fun ω => pairRaw (Y ω) ρ.1.1) →
      Measurable fun ω => J.restrict fun ρ : TestFun0 H => pairRaw (Y ω) ρ.1.1 := fun hm =>
    measurable_pi_iff.2 fun i => hm i.1
  refine Measure.ext_of_charFunDual (funext fun L => ?_)
  set c : J → ℝ := fun i => L fun j => if i = j then 1 else 0 with hc_def
  have hL : ∀ x : J → ℝ, L x = ∑ i, x i * c i := fun x => by
    rw [show L x = L.toLinearMap x from rfl, LinearMap.pi_apply_eq_sum_univ]
    simp only [smul_eq_mul, hc_def]
    rfl
  obtain ⟨ρ, hρ⟩ := exists_tf_sum (Finset.univ : Finset J) c fun i => i.1
  have key : ∀ {Y : Ω → FieldSample}, (∀ ρ : TestFun0 H, Measurable fun ω => pairRaw (Y ω) ρ.1.1) →
      LinearPairing Y P →
      charFunDual (P.map fun ω => J.restrict fun ρ : TestFun0 H => pairRaw (Y ω) ρ.1.1) L =
        ∫ ω, cexp (I * (pairRaw (Y ω) ρ.1.1 : ℂ)) ∂P := by
    intro Y hm hl
    rw [charFunDual_apply, integral_map (hF hm).aemeasurable (by fun_prop)]
    refine integral_congr_ae ?_
    filter_upwards [ae_pairRaw_sum hl Finset.univ c (fun i => i.1) ρ hρ] with ω hω
    rw [hL, hω, mul_comm I]
    congr 2
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Finset.restrict, mul_comm]
  rw [key hm₁ hl₁, key hm₂ hl₂, hc ρ]

/-! ## The value of `Φ` at time `0` -/

theorem revMap_zero_eq {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {z : ℂ} (hz : z ∈ H) :
    revMap W 0 z = z := by
  obtain ⟨u, hu⟩ := exists_isReverseSol W hW z hz 0 le_rfl
  rw [revMap_eq W hW z le_rfl le_rfl hu]
  have := (hu.2 0 ⟨le_rfl, le_rfl⟩).2
  rw [this, intervalIntegral.integral_same, hW0]
  simp

theorem hTrev_zero_eq (κ : ℝ) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {z : ℂ}
    (hz : z ∈ H) : hTrev κ W 0 z = h0rev κ z := by
  rw [hTrev, revMap_zero_eq hW hW0 hz, log_norm_deriv_revMap W hW le_rfl hz,
    intervalIntegral.integral_same]
  simp

theorem tf_eq_zero_of_not_mem (ρ : TestFun H) {z : ℂ} (hz : z ∉ H) : ρ.1 z = 0 :=
  image_eq_zero_of_notMem_tsupport fun h => hz (ρ.2.2.2 h)

theorem Xfun_zero (κ : ℝ) {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) (ρ : TestFun H) :
    Xfun κ W 0 ρ.1 = ∫ z, ρ.1 z * h0rev κ z := by
  unfold Xfun
  congr 1
  funext z
  by_cases hz : z ∈ H
  · rw [hTrev_zero_eq κ hW hW0 hz]
  · simp [tf_eq_zero_of_not_mem ρ hz]

theorem Efun_zero {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) (ρ : TestFun H) :
    Efun W 0 ρ.1 = ∫ x, ∫ y, ρ.1 x * ρ.1 y * neumannH x y := by
  unfold Efun
  congr 1
  funext x
  congr 1
  funext y
  by_cases hx : x ∈ H
  · by_cases hy : y ∈ H
    · rw [revMap_zero_eq hW hW0 hx, revMap_zero_eq hW hW0 hy]
    · simp [tf_eq_zero_of_not_mem ρ hy]
  · simp [tf_eq_zero_of_not_mem ρ hx]

/-- `Φ_0(ρ) = exp(i (𝔥₀, ρ) − E₀(ρ)/2)`. -/
theorem Phi_zero (κ : ℝ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) (ρ : TestFun H) :
    Phi κ 0 B P ρ.1 = cexp (I * ((∫ z, ρ.1 z * h0rev κ z : ℝ) : ℂ) -
      ((∫ x, ∫ y, ρ.1 x * ρ.1 y * neumannH x y : ℝ) : ℂ) / 2) := by
  unfold Phi
  have : ∀ᵐ ω ∂P, cexp (I * (Xfun κ (drive κ B ω) 0 ρ.1 : ℂ) -
      (Efun (drive κ B ω) 0 ρ.1 : ℂ) / 2) = cexp (I * ((∫ z, ρ.1 z * h0rev κ z : ℝ) : ℂ) -
      ((∫ x, ∫ y, ρ.1 x * ρ.1 y * neumannH x y : ℝ) : ℂ) / 2) := by
    filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero] with ω h1 h2
    have hW : Continuous (drive κ B ω) :=
      continuous_const.mul (h1.comp continuous_real_toNNReal)
    have hW0 : drive κ B ω 0 = 0 := by simp [drive, h2]
    rw [Xfun_zero κ hW hW0 ρ, Efun_zero hW hW0 ρ]
  rw [integral_congr_ae this]
  simp

/-! ## (d) Theorem 1.2 modulo the semigroup identity -/

/-- Replacing the Brownian motion by a version with measurable coordinates and continuous paths:
the right-hand field of Theorem 1.2 agrees almost surely with `Y2f` along the restricted path. -/
theorem ae_rhs_eq_Y2f (κ T : ℝ) (hT : 0 ≤ T) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B B' : ℝ≥0 → Ω → ℝ} (hB'c : ∀ ω, Continuous fun t => B' t ω)
    (hB'eq : ∀ᵐ ω ∂P, ∀ t, B' t ω = B t ω) (X : Ω → FieldSample) :
    ∀ᵐ ω ∂P, ofFun (hTrev κ (drive κ B ω) T) + coordChange (X ω) (revMap (drive κ B ω) T) 0 =
      Y2f κ T hT (pathC T B' hB'c ω) (X ω) := by
  filter_upwards [hB'eq] with ω h
  have hd : drive κ B' ω = drive κ B ω := funext fun t => by simp [drive, h]
  have hrev := revMap_drive_eq κ T hT B' hB'c ω
  simp only [Y2f]
  rw [← hd, hTrev_congr hrev κ, hrev]

theorem measurable_pairRaw_lhs (κ : ℝ) {Ω : Type*} [MeasurableSpace Ω] {X : Ω → FieldSample}
    {P : Measure Ω} (hX : IsFreeGFFModConstH X P) (ρ : TestFun0 H) :
    Measurable fun ω => pairRaw (ofFun (h0rev κ) + X ω) ρ.1.1 := by
  have hm : ∀ μ : Measure ℂ, Measurable fun ω => (ofFun (h0rev κ) + X ω) μ := fun μ => by
    simp only [Pi.add_apply]
    exact measurable_const.add (hX.measurable_coord μ)
  exact measurable_pairRaw_comp hm ρ.1.1

/-- **(d)** Theorem 1.2 follows from the semigroup identity `Φ_T = Φ_0`. -/
theorem theorem1_2_of_phi
    (hPhi : ∀ κ T : ℝ, 0 < κ → 0 < T → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
      IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
      ∀ ρ : TestFun0 H, Phi κ T B P ρ.1.1 = Phi κ 0 B P ρ.1.1) :
    theorem1_2 := by
  unfold theorem1_2
  intro κ T hκ hT Ω mΩ P hP B X hB hX hind
  obtain ⟨B', hB'm, hB'c, hB'eq⟩ := exists_good_version hB
  have hind' : IndepFun (pathOf B') X P :=
    hind.congr (hB'eq.mono fun ω h => (funext fun t => (h t).symm : pathOf B ω = pathOf B' ω))
      (ae_eq_refl _)
  have hgm : Measurable (pathC T B' hB'c) := measurable_pathC T hB'm hB'c
  have hXm : Measurable X := measurable_pi_iff.2 hX.measurable_coord
  have hig : IndepFun (pathC T B' hB'c) X P := indepFun_pathC T hind' hB'c
  have hY := ae_rhs_eq_Y2f κ T hT.le hB'c hB'eq X
  have hlaw : fieldLawMod0 H (fun ω => ofFun (hTrev κ (drive κ B ω) T) +
      coordChange (X ω) (revMap (drive κ B ω) T) 0) P =
      fieldLawMod0 H (fun ω => Y2f κ T hT.le (pathC T B' hB'c ω) (X ω)) P := by
    unfold fieldLawMod0
    refine Measure.map_congr ?_
    filter_upwards [hY] with ω h
    rw [h]
  have hc : ∀ ρ : TestFun0 H,
      ∫ ω, cexp (I * (pairRaw (ofFun (h0rev κ) + X ω) ρ.1.1 : ℂ)) ∂P =
        ∫ ω, cexp (I * (pairRaw (Y2f κ T hT.le (pathC T B' hB'c ω) (X ω)) ρ.1.1 : ℂ)) ∂P := by
    intro ρ
    have h1 := charFun_lhs κ P X hX ρ
    have h2 := charFun_rhs κ T hT.le P B X hB hX hind ρ
    have h3 := hPhi κ T hκ hT P B X hB hX hind ρ
    have h4 := Phi_zero κ hB ρ.1
    have h5 : ∫ ω, cexp (I * (pairRaw (ofFun (hTrev κ (drive κ B ω) T) +
        coordChange (X ω) (revMap (drive κ B ω) T) 0) ρ.1.1 : ℂ)) ∂P =
        ∫ ω, cexp (I * (pairRaw (Y2f κ T hT.le (pathC T B' hB'c ω) (X ω)) ρ.1.1 : ℂ)) ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [hY] with ω h
      rw [h]
    rw [h1, ← h5, h2, h3, h4]
  refine Eq.trans ?_ hlaw.symm
  refine fieldLawMod0_eq_of_charFun (Y₁ := fun ω => ofFun (h0rev κ) + X ω)
    (Y₂ := fun ω => Y2f κ T hT.le (pathC T B' hB'c ω) (X ω)) ?_ ?_ ?_ ?_ ?_
  · exact measurable_pairRaw_lhs κ hX
  · intro ρ
    have h := (measurable_pair_Y2f κ T hT.le ρ.1).comp (hgm.prodMk hXm)
    exact h
  · exact linear_lhs κ hX
  · exact linear_rhs κ T hT.le hX hgm hig
  · exact hc

end CharFun
end QuantumZipper
