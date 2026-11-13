/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Thm14.FromThm13 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Statements.Thm14
import LatticeProb.Bonanno.QuantumZipper.Blueprint.External2
import LatticeProb.Bonanno.QuantumZipper.Proofs.Zipper.WeldingUniqueness
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.Algebra
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm14.DoubledHull

/-!
# Lemmas for Theorem 1.4(a) (blueprint node C1, part (a))

Sheffield, *Conformal weldings of random surfaces*, §1.4. Deterministic and probabilistic
ingredients of the identification of the welding of the reverse SLE hull:

1. the forward hull at time `T` depends only on the driver on `[0, T]`
   (`fwdHull_eq_of_eqOn`), and the trace of a simple chord on `(0, T]` is a simple curve hull
   (`isSimpleCurveHull_image_Ioc`);
2. the time reversal `revBM B T` of a Brownian motion is a Brownian motion
   (`isBrownianReal_revBM`), and the driver of `revBM B T` is the time-reversed increment of
   the driver of `B` (`drive_revBM`);
3. for a boundary measure `ν` without atoms, positive on open intervals and finite on compact
   intervals, the measures of `[c, r]` and `[r, c]` are continuous in `r`;
4. given a Carathéodory extension of the reverse Loewner map (`Blueprint.IsCaratheodoryRevExt`)
   and such a measure `ν` whose quantum lengths agree at identified boundary points, the
   welding homeomorphism is `s ↦ inf {r ≥ 0 | ν[s, 0] ≤ ν[0, r]}` on `[0₋, 0]`
   (`weldingHom_eq_sInf_of_car`), and `0₋ < 0` for a nonempty hull (`zeroMinus_neg_of_car`).
-/

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal ComplexConjugate

namespace QuantumZipper

namespace Thm14FromThm13

/-! ### Locality of the forward hull and simple chords -/

/-- The forward hull at time `T` only depends on the driving function on `[0,T]`. -/
theorem fwdHull_subset_of_eqOn {W W' : ℝ → ℝ} (hW : Continuous W) {T : ℝ} (hT : 0 ≤ T)
    (heq : EqOn W W' (Icc 0 T)) : fwdHull W T ⊆ fwdHull W' T := by
  intro z hz
  rw [LoewnerAlgebra.mem_fwdHull_iff hT] at hz ⊢
  refine ⟨hz.1, fun S hS ⟨v, hv⟩ => ?_⟩
  by_contra hST
  push Not at hST
  have hvT := isForwardSol_restrict hv hT hST.le
  have hvT' : IsForwardSol W z T v :=
    ⟨hvT.1, fun t ht => by rw [heq ht]; exact hvT.2 t ht⟩
  have him := (im_isForwardSol_le hW hz.1 hvT').2 T ⟨hT, le_rfl⟩
  obtain ⟨ε, hε, w, hw⟩ :=
    exists_isForwardSol_small (W := fun r => W (T + r) - W T) (by fun_prop) him
  have := hz.2 (T + ε) (by linarith) ⟨_, LoewnerAlgebra.isForwardSol_glue hT hε.le hvT' hw⟩
  linarith

theorem fwdHull_eq_of_eqOn {W W' : ℝ → ℝ} (hW : Continuous W) (hW' : Continuous W') {T : ℝ}
    (hT : 0 ≤ T) (heq : EqOn W W' (Icc 0 T)) : fwdHull W T = fwdHull W' T :=
  (fwdHull_subset_of_eqOn hW hT heq).antisymm (fwdHull_subset_of_eqOn hW' hT heq.symm)

/-- The image of `(0,T]` under a simple chord is a simple curve hull. -/
theorem isSimpleCurveHull_image_Ioc {η : ℝ → ℂ} (hη : IsSimpleChord η) {T : ℝ} (hT : 0 < T) :
    IsSimpleCurveHull (η '' Ioc 0 T) := by
  obtain ⟨h0, hc, hinj, hH, -⟩ := hη
  refine ⟨fun t => η (T * t), ?_, ?_, ?_, ?_, ?_⟩
  · exact hc.comp (continuous_const.mul continuous_id).continuousOn
      (fun t ht => by simp only [mem_Ici]; exact mul_nonneg hT.le ht.1)
  · intro x hx y hy hxy
    have := hinj (mem_Ici.2 (mul_nonneg hT.le hx.1)) (mem_Ici.2 (mul_nonneg hT.le hy.1)) hxy
    exact mul_left_cancel₀ hT.ne' this
  · simp [h0]
  · intro t ht
    exact hH _ (mul_pos hT ht.1)
  · ext z
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨s / T, ⟨div_pos hs.1 hT, (div_le_one hT).2 hs.2⟩, ?_⟩
      simp only
      rw [mul_div_cancel₀ _ hT.ne']
    · rintro ⟨t, ht, rfl⟩
      exact ⟨T * t, ⟨mul_pos hT ht.1, by nlinarith [ht.2]⟩, rfl⟩

/-! ### Time reversal of Brownian motion -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The time-reversed Brownian motion on `[0,τ]`, continued by `-B` afterwards:
`revBM B τ t = B(τ - t) - B(τ)` for `t ≤ τ`, and `B(0) - B(t)` for `t ≥ τ`. -/
def revBM (B : ℝ≥0 → Ω → ℝ) (τ : ℝ≥0) : ℝ≥0 → Ω → ℝ :=
  fun t ω => B (τ - min t τ) ω - B (max t τ) ω

theorem revBM_cov_arith (τ s t : ℝ≥0) (hst : s ≤ t) :
    ((min (τ - min s τ) (τ - min t τ) : ℝ≥0) : ℝ) - (min (τ - min s τ) (max t τ) : ℝ≥0)
      - ((min (max s τ) (τ - min t τ) : ℝ≥0) - (min (max s τ) (max t τ) : ℝ≥0)) = s := by
  rcases le_total t τ with ht | ht
  · have hs : s ≤ τ := hst.trans ht
    rw [min_eq_left hs, min_eq_left ht, max_eq_right hs, max_eq_right ht,
      min_eq_right (tsub_le_tsub_left hst τ), min_eq_left (tsub_le_self : τ - s ≤ τ),
      min_eq_right (tsub_le_self : τ - t ≤ τ), min_self, NNReal.coe_sub hs, NNReal.coe_sub ht]
    ring
  · rcases le_total s τ with hs | hs
    · rw [min_eq_left hs, min_eq_right ht, max_eq_right hs, max_eq_left ht, tsub_self,
        min_eq_right zero_le, min_eq_left ((tsub_le_self : τ - s ≤ τ).trans ht),
        min_eq_right zero_le, min_eq_left ht, NNReal.coe_sub hs]
      push_cast
      ring
    · rw [min_eq_right hs, min_eq_right ht, max_eq_left hs, max_eq_left ht, tsub_self,
        min_self, min_eq_left zero_le, min_eq_right zero_le, min_eq_left hst]
      push_cast
      ring

/-- The time-reversed Brownian motion is a Brownian motion. -/
theorem isBrownianReal_revBM {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (τ : ℝ≥0) : IsBrownianReal (revBM B τ) P where
  toIsPreBrownianReal := by
    have hG : IsGaussianProcess (revBM B τ) P := by
      classical
      exact hB.isGaussianProcess.of_isGaussianProcess fun t ↦ ⟨{τ - min t τ, max t τ},
        { toFun x := x ⟨τ - min t τ, by simp⟩ - x ⟨max t τ, by simp⟩
          map_add' x y := by simp only [Pi.add_apply]; ring
          map_smul' c x := by simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring },
        by simp [revBM]⟩
    refine hG.isPreBrownianReal_of_covariance (fun t ↦ ?_) (fun s t hst ↦ ?_)
    · simp only [revBM]
      rw [integral_sub, hB.integral_eval, hB.integral_eval, sub_zero]
      all_goals exact hB.integrable_eval _
    · have := hB.isGaussianProcess.isProbabilityMeasure
      unfold revBM
      rw [covariance_fun_sub_left, covariance_fun_sub_right, covariance_fun_sub_right,
        hB.covariance_eval, hB.covariance_eval, hB.covariance_eval, hB.covariance_eval]
      · exact revBM_cov_arith τ s t hst
      any_goals exact (hB.isGaussianProcess.hasGaussianLaw_eval _).memLp_two
      exact hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two
  cont := by
    filter_upwards [hB.cont] with ω h
    simp only [revBM]
    fun_prop

theorem toNNReal_sub_of_le {s T : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) :
    (T - s).toNNReal = T.toNNReal - s.toNNReal := by
  apply NNReal.coe_injective
  rw [NNReal.coe_sub (Real.toNNReal_le_toNNReal hsT), Real.coe_toNNReal _ (sub_nonneg.2 hsT),
    Real.coe_toNNReal _ (hs.trans hsT), Real.coe_toNNReal _ hs]

omit [MeasurableSpace Ω] in
theorem drive_revBM {κ T : ℝ} (B : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    EqOn (fun s => drive κ B ω (T - s) - drive κ B ω T) (drive κ (revBM B T.toNNReal) ω)
      (Icc 0 T) := by
  intro s hs
  have hle : s.toNNReal ≤ T.toNNReal := Real.toNNReal_le_toNNReal hs.2
  simp only [drive, revBM, min_eq_left hle, max_eq_right hle, ← toNNReal_sub_of_le hs.1 hs.2]
  ring

omit [MeasurableSpace Ω] in
theorem continuous_drive {κ : ℝ} {B : ℝ≥0 → Ω → ℝ} {ω : Ω} (h : Continuous (B · ω)) :
    Continuous (drive κ B ω) := by
  unfold drive
  exact continuous_const.mul (h.comp continuous_real_toNNReal)

/-! ### Measure-theoretic lemmas for the welding identification -/

section MeasureLemmas

variable {ν : Measure ℝ} (hatom : ∀ x, ν {x} = 0) (hpos : ∀ u v, u < v → 0 < ν (Ioo u v))
  (hfin : ∀ u v, ν (Icc u v) < ⊤)
include hpos hfin

theorem measure_Icc_lt_right {p u v : ℝ} (hpu : p ≤ u) (huv : u < v) :
    ν (Icc p u) < ν (Icc p v) := by
  have hsub : Icc p u ∪ Ioo u v ⊆ Icc p v := union_subset (Icc_subset_Icc_right huv.le)
    (fun x hx => ⟨hpu.trans hx.1.le, hx.2.le⟩)
  have hdis : Disjoint (Icc p u) (Ioo u v) :=
    Set.disjoint_left.2 fun x hx hx' => absurd hx.2 (not_le.2 hx'.1)
  calc ν (Icc p u) < ν (Icc p u) + ν (Ioo u v) :=
        ENNReal.lt_add_right (hfin p u).ne (hpos u v huv).ne'
    _ = ν (Icc p u ∪ Ioo u v) := (measure_union hdis measurableSet_Ioo).symm
    _ ≤ ν (Icc p v) := measure_mono hsub

theorem measure_Icc_lt_left {u v q : ℝ} (huv : u < v) (hvq : v ≤ q) :
    ν (Icc v q) < ν (Icc u q) := by
  have hsub : Icc v q ∪ Ioo u v ⊆ Icc u q := union_subset (Icc_subset_Icc_left huv.le)
    (fun x hx => ⟨hx.1.le, hx.2.le.trans hvq⟩)
  have hdis : Disjoint (Icc v q) (Ioo u v) :=
    Set.disjoint_left.2 fun x hx hx' => absurd hx.1 (not_le.2 hx'.2)
  calc ν (Icc v q) < ν (Icc v q) + ν (Ioo u v) :=
        ENNReal.lt_add_right (hfin v q).ne (hpos u v huv).ne'
    _ = ν (Icc v q ∪ Ioo u v) := (measure_union hdis measurableSet_Ioo).symm
    _ ≤ ν (Icc u q) := measure_mono hsub

omit hpos in
include hatom in
theorem continuous_measure_family (G : ℝ → Set ℝ) (hGfin : ∀ r, ν (G r) < ⊤)
    (hG : ∀ r r' δ, |r' - r| ≤ δ →
      G r' ⊆ G r ∪ Icc (r - δ) (r + δ) ∧ G r ⊆ G r' ∪ Icc (r - δ) (r + δ)) :
    Continuous fun r => (ν (G r)).toReal := by
  have : NullSingletonClass ν := ⟨hatom⟩
  have : IsFiniteMeasureOnCompacts ν := ⟨fun K hK => by
    obtain ⟨c, R, hR⟩ : ∃ c R : ℝ, K ⊆ Icc c R := by
      obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
      exact ⟨0 - R, 0 + R, by rwa [← Real.closedBall_eq_Icc]⟩
    exact (measure_mono hR).trans_lt (hfin c R)⟩
  rw [Metric.continuous_iff]
  intro r ε hε
  have ht := tendsto_measure_Icc ν r
  have hev : ∀ᶠ δ in 𝓝 (0 : ℝ), ν (Icc (r - δ) (r + δ)) < ENNReal.ofReal ε :=
    ht (Iio_mem_nhds (ENNReal.ofReal_pos.2 hε))
  obtain ⟨δ, hδ, hδP⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨δ / 2, by positivity, fun r' hr' => ?_⟩
  have hd : |r' - r| ≤ δ / 2 := (Real.dist_eq r' r ▸ hr').le
  obtain ⟨h1, h2⟩ := hG r r' (δ / 2) hd
  have hI : ν (Icc (r - δ / 2) (r + δ / 2)) < ENNReal.ofReal ε :=
    hδP (by rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith)
  have hIfin : ν (Icc (r - δ / 2) (r + δ / 2)) ≠ ⊤ := (hfin _ _).ne
  have hm : (ν (Icc (r - δ / 2) (r + δ / 2))).toReal < ε := ENNReal.toReal_lt_of_lt_ofReal hI
  have e1 : (ν (G r')).toReal ≤ (ν (G r)).toReal + (ν (Icc (r - δ / 2) (r + δ / 2))).toReal := by
    rw [← ENNReal.toReal_add (hGfin r).ne hIfin]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨(hGfin r).ne, hIfin⟩)
      ((measure_mono h1).trans (measure_union_le _ _))
  have e2 : (ν (G r)).toReal ≤ (ν (G r')).toReal + (ν (Icc (r - δ / 2) (r + δ / 2))).toReal := by
    rw [← ENNReal.toReal_add (hGfin r').ne hIfin]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨(hGfin r').ne, hIfin⟩)
      ((measure_mono h2).trans (measure_union_le _ _))
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor <;> linarith

omit hpos in
include hatom in
theorem continuous_measure_Icc_right (c : ℝ) : Continuous fun r => (ν (Icc c r)).toReal := by
  refine continuous_measure_family hatom hfin _ (fun r => hfin c r) fun r r' δ hd => ?_
  rw [abs_le] at hd
  constructor
  · intro x hx
    by_cases hxr : x ≤ r
    · exact Or.inl ⟨hx.1, hxr⟩
    · exact Or.inr ⟨by linarith, by linarith [hx.2]⟩
  · intro x hx
    by_cases hxr : x ≤ r'
    · exact Or.inl ⟨hx.1, hxr⟩
    · exact Or.inr ⟨by linarith, by linarith [hx.2]⟩

omit hpos in
include hatom in
theorem continuous_measure_Icc_left (c : ℝ) : Continuous fun r => (ν (Icc r c)).toReal := by
  refine continuous_measure_family hatom hfin _ (fun r => hfin r c) fun r r' δ hd => ?_
  rw [abs_le] at hd
  constructor
  · intro x hx
    by_cases hxr : r ≤ x
    · exact Or.inl ⟨hxr, hx.2⟩
    · exact Or.inr ⟨by linarith [hx.1], by linarith⟩
  · intro x hx
    by_cases hxr : r' ≤ x
    · exact Or.inl ⟨hxr, hx.2⟩
    · exact Or.inr ⟨by linarith [hx.1], by linarith⟩

end MeasureLemmas

/-! ### Step (iii): the welding homeomorphism is `weldR` -/

/-- Deterministic core of step (iii): the Carathéodory boundary correspondence, the two
clauses of Theorem 1.3 and the regularity of `ν` give `weldingHom W T = R_ν` on `[0₋,0]`,
where `R_ν(s) = inf {r ≥ 0 : ν[s,0] ≤ ν[0,r]}`. -/
theorem weldingHom_eq_sInf_of_car {W : ℝ → ℝ} {T : ℝ} {F : ℂ → ℂ} (hW : Continuous W) (hT : 0 < T)
    (hF : Blueprint.IsCaratheodoryRevExt W T F) {ν : Measure ℝ}
    (hatom : ∀ x, ν {x} = 0) (hpos : ∀ u v, u < v → 0 < ν (Ioo u v))
    (hfin : ∀ u v, ν (Icc u v) < ⊤)
    (h1 : ∀ z ∈ revHull W T, z ≠ revMapBdry W T 0 →
      ∃ xm xp : ℝ, xm < 0 ∧ 0 < xp ∧ revMapBdry W T xm = z ∧ revMapBdry W T xp = z)
    (h2 : ∀ xm xp : ℝ, xm < 0 → 0 < xp → revMapBdry W T xm = revMapBdry W T xp →
      revMapBdry W T xm ∈ revHull W T → ν (Icc xm 0) = ν (Icc 0 xp)) :
    ∀ s ∈ Icc (zeroMinus W T) 0,
      weldingHom W T s = sInf {r | 0 ≤ r ∧ ν (Icc s 0) ≤ ν (Icc 0 r)} := by
  obtain ⟨hFeq, hFc, -, -, hφa, hFre, hFinj⟩ := hF
  set a := zeroMinus W T with ha_def
  set b := zeroPlus W T with hb_def
  set φ := weldingHom W T with hφ_def
  have hHbar : ∀ x : ℝ, (x : ℂ) ∈ Hbar := fun x => by
    show (0 : ℝ) ≤ (x : ℂ).im
    simp
  -- boundary values of `revMap` are those of `F`
  have htend : ∀ x : ℝ,
      Tendsto (fun y : ℝ => revMap W T (x + y * Complex.I)) (𝓝[>] 0) (𝓝 (F x)) := by
    intro x
    have hpath : Tendsto (fun y : ℝ => (x : ℂ) + y * Complex.I) (𝓝[>] 0) (𝓝[Hbar] (x : ℂ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Continuous fun y : ℝ => (x : ℂ) + y * Complex.I := by fun_prop
        have h := this.tendsto 0
        simp only [Complex.ofReal_zero, zero_mul, add_zero] at h
        exact h.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with y hy
        show (0 : ℝ) ≤ ((x : ℂ) + y * Complex.I).im
        simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
          Complex.I_im, Complex.I_re, mul_zero, zero_add, mul_one]
        linarith [show (0 : ℝ) < y from hy]
    have hc := ((hFc x (hHbar x)).tendsto).comp hpath
    refine hc.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    apply hFeq
    show (0 : ℝ) < ((x : ℂ) + y * Complex.I).im
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, Complex.I_re, mul_zero, zero_add, mul_one]
    linarith [show (0 : ℝ) < y from hy]
  have hbdry : ∀ x : ℝ, revMapBdry W T x = F x := fun x => (htend x).limUnder_eq
  have him : ∀ x : ℝ, 0 ≤ (F x).im := by
    intro x
    refine ge_of_tendsto ((Complex.continuous_im.tendsto _).comp (htend x)) ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hyH : (0 : ℝ) < ((x : ℂ) + y * Complex.I).im := by
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re, mul_zero, zero_add, mul_one]
      linarith [show (0 : ℝ) < y from hy]
    exact (lt_of_lt_of_le hyH (im_le_im_revMap W hW _ hyH hT.le)).le
  have hφnn : ∀ t, 0 ≤ φ t := fun t => Real.sInf_nonneg (fun y hy => hy.1)
  have hφ0 : φ 0 = 0 :=
    le_antisymm (csInf_le ⟨0, fun y hy => hy.1⟩ ⟨le_rfl, rfl⟩) (hφnn 0)
  have ha0 : a ≤ 0 := WeldingUniqueness.zeroMinus_nonpos W T
  have hb0 : 0 ≤ b := Real.sInf_nonneg (fun y hy => hy.1.le)
  have hrel : ∀ x y : ℝ, F x = F y →
      x = y ∨ ∃ t ∈ Icc a 0, (x = t ∧ y = φ t) ∨ (x = φ t ∧ y = t) := by
    intro x y hxy
    rcases (hFinj _ (hHbar x) _ (hHbar y)).1 hxy with h | ⟨t, ht, h⟩
    · exact Or.inl (Complex.ofReal_injective h)
    · right
      refine ⟨t, ht, ?_⟩
      rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨Complex.ofReal_injective h1, Complex.ofReal_injective h2⟩
      · exact Or.inr ⟨Complex.ofReal_injective h1, Complex.ofReal_injective h2⟩
  have hFφ : ∀ t ∈ Icc a 0, F (φ t) = F t := fun t ht =>
    (hFinj _ (hHbar _) _ (hHbar _)).2 (Or.inr ⟨t, ht, Or.inr ⟨rfl, rfl⟩⟩)
  have hhull : ∀ x : ℝ, a < x → x < b → F x ∈ revHull W T := by
    intro x hax hxb
    have hne : (F x).im ≠ 0 := fun h => by
      rcases (hFre x).1 h with h' | h' <;> linarith
    refine ⟨lt_of_le_of_ne (him x) (Ne.symm hne), ?_⟩
    rintro ⟨z, hz, hzx⟩
    rw [← hFeq hz] at hzx
    have hz' : (0 : ℝ) < z.im := hz
    rcases (hFinj z (WeldingUniqueness.wu_H_subset_Hbar hz) x (hHbar x)).1 hzx with
      h | ⟨t, _, ⟨h, _⟩ | ⟨h, _⟩⟩
    · rw [h, Complex.ofReal_im] at hz'; exact lt_irrefl _ hz'
    · rw [h, Complex.ofReal_im] at hz'; exact lt_irrefl _ hz'
    · rw [h, Complex.ofReal_im] at hz'; exact lt_irrefl _ hz'
  -- points of `(a,0)` not welded to the tip
  have hgood : ∀ s, a < s → s < 0 → φ s ≠ 0 →
      0 < φ s ∧ φ s < b ∧ ν (Icc s 0) = ν (Icc 0 (φ s)) := by
    intro s has hs0 hφs
    have hin := hhull s has (by linarith)
    have hne : F s ≠ revMapBdry W T 0 := by
      rw [hbdry]
      intro h
      rcases hrel s 0 h with h | ⟨t, ht, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
      · linarith
      · subst h1; exact hφs h2.symm
      · linarith [hφnn t]
    obtain ⟨xm, xp, -, hxp, -, hxpE⟩ := h1 (F s) hin hne
    rw [hbdry] at hxpE
    have hxpφ : xp = φ s := by
      rcases hrel s xp hxpE.symm with h | ⟨t, ht, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
      · linarith
      · subst h1; exact h2
      · linarith [ht.2]
    rw [hxpφ] at hxp hxpE
    refine ⟨hxp, ?_, ?_⟩
    · by_contra hle
      push Not at hle
      have := (hFre (φ s)).2 (Or.inr hle)
      rw [hxpE] at this
      have h' : (0 : ℝ) < (F s).im := hin.1
      rw [this] at h'
      exact lt_irrefl _ h'
    · refine h2 s (φ s) hs0 hxp ?_ ?_
      · rw [hbdry, hbdry, hxpE]
      · rw [hbdry]; exact hin
  have hsurj : ∀ y, 0 < y → y < b → ∃ x, a < x ∧ x < 0 ∧ φ x = y := by
    intro y hy hyb
    have hin := hhull y (by linarith) hyb
    have hne : F y ≠ revMapBdry W T 0 := by
      rw [hbdry]
      intro h
      rcases hrel y 0 h with h | ⟨t, ht, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
      · linarith
      · linarith [ht.2]
      · subst h2; rw [hφ0] at h1; linarith
    obtain ⟨xm, xp, hxm, -, hxmE, -⟩ := h1 (F y) hin hne
    rw [hbdry] at hxmE
    rcases hrel xm y hxmE with h | ⟨t, ht, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · linarith
    · subst h1
      refine ⟨xm, ?_, hxm, h2.symm⟩
      rcases eq_or_lt_of_le ht.1 with h | h
      · rw [← h, hφa] at h2; linarith
      · exact h
    · linarith [hφnn t]
  -- no point of `(a,0)` is welded to the tip
  have hφne : ∀ s, a < s → s < 0 → φ s ≠ 0 := by
    intro s₀ has₀ hs₀ hφ₀
    set x₁ := (a + s₀) / 2 with hx₁
    have hx₁a : a < x₁ := by rw [hx₁]; linarith
    have hx₁s : x₁ < s₀ := by rw [hx₁]; linarith
    have hφx₁ : φ x₁ ≠ 0 := by
      intro h
      have : F x₁ = F s₀ := by
        rw [← hFφ x₁ ⟨hx₁a.le, by linarith⟩, h, ← hφ₀, hFφ s₀ ⟨has₀.le, hs₀.le⟩]
      rcases hrel x₁ s₀ this with h | ⟨t, ht, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
      · linarith
      · linarith [hφnn t]
      · linarith [hφnn t]
    obtain ⟨hy₁pos, hy₁b, hν₁⟩ := hgood x₁ hx₁a (by linarith) hφx₁
    have hlt : ν (Icc s₀ 0) < ν (Icc 0 (φ x₁)) :=
      hν₁ ▸ measure_Icc_lt_left hpos hfin hx₁s hs₀.le
    have hv0 : 0 < ν (Icc s₀ 0) :=
      (hpos s₀ 0 hs₀).trans_le (measure_mono Ioo_subset_Icc_self)
    have hG0 : (ν (Icc 0 0)).toReal = 0 := by rw [Icc_self, hatom, ENNReal.toReal_zero]
    have hlt' : (ν (Icc s₀ 0)).toReal < (ν (Icc 0 (φ x₁))).toReal :=
      (ENNReal.toReal_lt_toReal (hfin _ _).ne (hfin _ _).ne).2 hlt
    have hv0' : 0 < (ν (Icc s₀ 0)).toReal := ENNReal.toReal_pos hv0.ne' (hfin _ _).ne
    obtain ⟨y, hy, hyv⟩ := intermediate_value_Icc hy₁pos.le
      (continuous_measure_Icc_right hatom hfin 0).continuousOn
      (show (ν (Icc s₀ 0)).toReal ∈ Icc (ν (Icc 0 0)).toReal (ν (Icc 0 (φ x₁))).toReal from
        ⟨by rw [hG0]; exact hv0'.le, hlt'.le⟩)
    have hypos : 0 < y := by
      rcases eq_or_lt_of_le hy.1 with h | h
      · subst h
        have h' : (ν (Icc 0 0)).toReal = (ν (Icc s₀ 0)).toReal := hyv
        rw [hG0] at h'; linarith
      · exact h
    obtain ⟨x, hax, hx0, hφx⟩ := hsurj y hypos (by linarith [hy.2])
    obtain ⟨-, -, hνx⟩ := hgood x hax hx0 (by rw [hφx]; exact hypos.ne')
    rw [hφx] at hνx
    have heq : ν (Icc x 0) = ν (Icc s₀ 0) := by
      rw [hνx]
      exact (ENNReal.toReal_eq_toReal_iff' (hfin _ _).ne (hfin _ _).ne).1 hyv
    rcases lt_trichotomy x s₀ with h | h | h
    · exact (measure_Icc_lt_left hpos hfin h hs₀.le).ne' heq
    · rw [h, hφ₀] at hφx; linarith
    · exact (measure_Icc_lt_left hpos hfin h hx0.le).ne heq
  -- identification of the infimum
  have hident : ∀ s y, 0 ≤ y → ν (Icc s 0) = ν (Icc 0 y) →
      sInf {r | 0 ≤ r ∧ ν (Icc s 0) ≤ ν (Icc 0 r)} = y := by
    intro s y hy hν
    apply le_antisymm
    · exact csInf_le ⟨0, fun r hr => hr.1⟩ ⟨hy, hν.le⟩
    · refine le_csInf ⟨y, hy, hν.le⟩ ?_
      rintro r ⟨hr0, hr⟩
      by_contra hlt
      push Not at hlt
      exact (measure_Icc_lt_right hpos hfin hr0 hlt).not_ge (hν ▸ hr)
  intro s hs
  rcases eq_or_lt_of_le hs.2 with hs0 | hs0
  · rw [hs0, hφ0, hident 0 0 le_rfl rfl]
  rcases eq_or_lt_of_le hs.1 with has | has
  · -- the endpoint `s = 0₋`
    rw [← has, hφa]
    have hmem : 0 ≤ b ∧ ν (Icc a 0) ≤ ν (Icc 0 b) := by
      refine ⟨hb0, ?_⟩
      rw [← ENNReal.toReal_le_toReal (hfin _ _).ne (hfin _ _).ne]
      have hcont := (continuous_measure_Icc_left hatom hfin 0).continuousAt (x := a)
      refine le_of_tendsto (hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi a))) ?_
      filter_upwards [Ioo_mem_nhdsGT (show a < 0 by rw [has]; exact hs0)] with x hx
      obtain ⟨-, hxb, hνx⟩ := hgood x hx.1 hx.2 (hφne x hx.1 hx.2)
      rw [hνx]
      exact ENNReal.toReal_mono (hfin _ _).ne (measure_mono (Icc_subset_Icc_right hxb.le))
    apply le_antisymm
    · refine le_csInf ⟨b, hmem⟩ ?_
      rintro r ⟨hr0, hr⟩
      by_contra hlt
      push Not at hlt
      obtain ⟨x, hax, hx0, hφx⟩ := hsurj ((r + b) / 2) (by linarith) (by linarith)
      obtain ⟨-, -, hνx⟩ := hgood x hax hx0 (hφne x hax hx0)
      rw [hφx] at hνx
      have h3 : ν (Icc 0 r) < ν (Icc 0 ((r + b) / 2)) :=
        measure_Icc_lt_right hpos hfin hr0 (by linarith)
      have h4 : ν (Icc x 0) ≤ ν (Icc a 0) := measure_mono (Icc_subset_Icc_left hax.le)
      rw [hνx] at h4
      exact absurd (h4.trans hr) (not_le.2 h3)
    · exact csInf_le ⟨0, fun r hr => hr.1⟩ hmem
  · obtain ⟨hφpos, -, hν⟩ := hgood s has hs0 (hφne s has hs0)
    rw [hident s (φ s) hφpos.le hν]

/-- The Carathéodory extension of a nonempty reverse hull has `0₋ < 0` (the part `0₋ < 0` of
`WeldingConsistency.car_basic`, reproved here because that module imports this one). -/
theorem zeroMinus_neg_of_car {W : ℝ → ℝ} {T : ℝ} {F : ℂ → ℂ}
    (hF : Blueprint.IsCaratheodoryRevExt W T F) (hne : (revHull W T).Nonempty) :
    zeroMinus W T < 0 := by
  obtain ⟨p, hp⟩ := hne
  obtain ⟨x, hx, hxp⟩ := hF.2.2.1 (WeldingUniqueness.wu_H_subset_Hbar hp.1)
  have hxR : x.im = 0 := by
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ x.im from hx) with h | h
    · exact h.symm
    · exfalso
      exact hp.2 ⟨x, h, by rw [← hF.1 h]; exact hxp⟩
  have hxe : x = (x.re : ℂ) := Complex.ext rfl (by simp [hxR])
  have hpim : (F x.re).im ≠ 0 := by
    rw [← hxe, hxp]; exact ne_of_gt hp.1
  have h2 : ¬ (x.re ≤ zeroMinus W T ∨ zeroPlus W T ≤ x.re) := (hF.2.2.2.2.2.1 x.re).not.1 hpim
  push Not at h2
  rcases eq_or_lt_of_le (WeldingUniqueness.zeroMinus_nonpos W T) with h | h
  · exfalso
    have hφ0 : weldingHom W T 0 = 0 :=
      le_antisymm (csInf_le ⟨0, fun y hy => hy.1⟩ ⟨le_rfl, rfl⟩)
        (Real.sInf_nonneg (fun y hy => hy.1))
    have : zeroPlus W T = 0 := by rw [← hF.2.2.2.2.1, h, hφ0]
    linarith [h2.1, h2.2]
  · exact h

end Thm14FromThm13

end QuantumZipper
