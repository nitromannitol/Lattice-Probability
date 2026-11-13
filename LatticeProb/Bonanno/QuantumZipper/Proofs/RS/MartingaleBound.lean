/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.RS.MartingaleBound at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.RS.MartingaleBoundGen
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm11.NonSwallowing
import LatticeProb.Bonanno.QuantumZipper.Proofs.Thm12.OnePointExpansion
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.ReverseHolo
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeRestriction

/-!
# RS E1: the Rohde–Schramm martingale bound

Blueprint `blueprint/EXT_RS_BLUEPRINT.md`, §3, node E1.

`RS.rs_martingale_bound`: for a Brownian motion `B`, `0 < κ`, `0 ≤ r`, `0 ≤ T`, `z ∈ ℍ`, with
`u_T = revMap (drive κ B ω) T z`,
`E[|u_T'(z)|^λ (Im u_T)^ζ (Im u_T / |u_T|)^{−2r}] ≤ (Im z)^ζ (Im z / |z|)^{−2r}`,
`λ = rsLam κ r`, `ζ = rsZeta κ r`.

Proof (following the published proof, with the project's Itô-free Dynkin formula in place of
Itô's formula): the state `U_t = (u_t, log |u_t'|)` solves
`U_t = (z, 0) + ∫₀ᵗ rsDrift (Im z) (U_s) ds + B_t (−√κ, 0)` (`rsProc_integralEq`; the taming in
`rsDrift` is inactive because `Im u_t ≥ Im z`). The test function `rsTest κ r` has zero Dynkin
generator (`dynkinGen_rsTest`, file `MartingaleBoundGen`). The local Dynkin formula with stopping
(`FrozenMart.martingale_localDynkin_stopped`) on `K = {Im u ≥ Im z, |u| ≤ R, |L| ≤ 2T/(Im z)²}`,
stopped at the hitting time of `{|u| ≥ R}`, gives `E rsTest(U_{T ∧ τ_R}) = rsTest(z, 0)`. As
`R → ∞`, `τ_R = T` eventually (path continuity), and Fatou's lemma gives the bound. Finally
`log |u_T'| = Re ∫₀ᵀ 2/u_s²` (`log_norm_deriv_revMap`) identifies `rsTest (U_T)` with the RS
integrand.

Literature: S. Rohde, O. Schramm, *Basic properties of SLE*, Ann. Math. 161 (2005), Thm 3.2
(p. 10; arXiv math/0106036); A. Kemppainen, *Schramm–Loewner Evolution*, SpringerBriefs Math.
Phys. 24 (2017), Thm 5.5 (pp. 97–98), whose martingale `|h'|^p Y^{p − κr/2} (sin arg)^{−2r}` is
ours with `p = rsLam κ r`; G. Lawler, *Conformally Invariant Processes in the Plane*, AMS 2005,
Prop. 7.2 (p. 155) with `a = 2/κ`. Deviation from the sources: Kemppainen proves the martingale
property via Itô's formula and a time change (Lemma 5.6); here only the inequality `E M_T ≤ M_0`
is proved, by localization and Fatou (as in the blueprint).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace QuantumZipper
namespace RS

open FwdHolo FrozenMart

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-! ### The test function in Rohde–Schramm form -/

theorem rsTest_eq (κ r : ℝ) {u : ℂ} (hu : 0 < u.im) (L : ℝ) :
    rsTest κ r (u, L) = Real.exp (rsLam κ r * L) * u.im ^ rsZeta κ r *
      (u.im / ‖u‖) ^ (-2 * r) := by
  have hn : 0 < ‖u‖ := hu.trans_le (Complex.im_le_norm u)
  have hN : u.re ^ 2 + u.im ^ 2 = ‖u‖ ^ (2 : ℝ) := by
    rw [Real.rpow_two, Complex.sq_norm, Complex.normSq_apply]; ring
  simp only [rsTest]
  rw [hN, ← Real.rpow_mul hn.le, Real.div_rpow hu.le hn.le, Real.rpow_sub hu,
    show (-2 * r) = -(2 * r) by ring, Real.rpow_neg hn.le, Real.rpow_neg hu.le]
  field_simp

/-- The RS integrand is `rsTest` of `(u_T, Re ∫₀ᵀ 2/u_s²)`. -/
theorem rsTest_revMap {W : ℝ → ℝ} (hW : Continuous W) (κ r : ℝ) {T : ℝ} (hT : 0 ≤ T) {z : ℂ}
    (hz : z ∈ H) :
    rsTest κ r (revMap W T z, (∫ s in (0 : ℝ)..T, 2 / (revMap W s z) ^ 2).re) =
      ‖deriv (revMap W T) z‖ ^ rsLam κ r * (revMap W T z).im ^ rsZeta κ r *
        ((revMap W T z).im / ‖revMap W T z‖) ^ (-2 * r) := by
  have hu : 0 < (revMap W T z).im := (show (0 : ℝ) < z.im from hz).trans_le
    (im_le_im_revMap W hW z hz hT)
  rw [rsTest_eq κ r hu, ← log_norm_deriv_revMap W hW hT hz,
    Real.rpow_def_of_pos (norm_pos_iff.2 (deriv_revMap_ne_zero W hW hT hz)), mul_comm (rsLam κ r)]

/-! ### The state process -/

/-- The state process `(u_t, Re ∫₀ᵗ 2/u_s²) = (u_t, log |u_t'|)`. -/
def rsProc (κ : ℝ) (B : ℝ≥0 → Ω → ℝ) (z : ℂ) (t : ℝ≥0) (ω : Ω) : ℂ × ℝ :=
  (revMap (drive κ B ω) t z, (∫ s in (0 : ℝ)..t, 2 / (revMap (drive κ B ω) s z) ^ 2).re)

theorem rsProc_integralEq (hBc : ∀ ω, Continuous (B · ω)) (κ : ℝ) {z : ℂ} (hz : 0 < z.im)
    (ω : Ω) (t : ℝ≥0) :
    rsProc κ B z t ω = (z, 0) + (∫ r in (0 : ℝ)..t, rsDrift z.im (rsProc κ B z r.toNNReal ω))
      + B t ω • rsNoise κ := by
  set W := drive κ B ω with hWdef
  have hW : Continuous W := NonSwallow.continuous_drive_ns hBc κ ω
  have ht : (0 : ℝ) ≤ t := t.coe_nonneg
  set u : ℝ → ℂ := fun s => revMap W s z with hu
  have hucont : ContinuousOn u (Icc 0 t) := continuousOn_revMap_time W hW hz ht
  have hu0 : ∀ s ∈ Icc (0 : ℝ) t, u s ≠ 0 := fun s hs =>
    revMap_ne_zero_of_im hW hz hs.1
  have huim : ∀ s ∈ Icc (0 : ℝ) t, z.im ≤ (u s).im := fun s hs =>
    im_le_im_revMap W hW z hz hs.1
  set g : ℝ → ℂ × ℝ := fun s => (-(2 / u s), (2 / u s ^ 2).re) with hg
  have hg1 : ContinuousOn (fun s => 2 / u s) (Icc 0 t) := continuousOn_const.div hucont hu0
  have hg2 : ContinuousOn (fun s => 2 / u s ^ 2) (Icc 0 t) :=
    continuousOn_const.div (hucont.pow 2) fun s hs => pow_ne_zero 2 (hu0 s hs)
  have hgc : ContinuousOn g (Icc 0 t) :=
    hg1.neg.prodMk (Complex.continuous_re.comp_continuousOn hg2)
  have hint : IntervalIntegrable g MeasureTheory.volume 0 t :=
    ContinuousOn.intervalIntegrable (by rwa [uIcc_of_le ht])
  have heq : ∫ r in (0 : ℝ)..t, rsDrift z.im (rsProc κ B z r.toNNReal ω) =
      ∫ r in (0 : ℝ)..t, g r := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le ht] at hs
    have hs' : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal s hs.1
    simp only [rsDrift, rsProc, hs', hg]
    rw [proj_of_le (huim s hs)]
  rw [heq]
  have h1 : (∫ r in (0 : ℝ)..t, g r).1 = -∫ r in (0 : ℝ)..t, 2 / u r := by
    have := (ContinuousLinearMap.fst ℝ ℂ ℝ).intervalIntegral_comp_comm hint
    simp only [ContinuousLinearMap.coe_fst'] at this
    rw [← this]
    simp only [hg]
    exact intervalIntegral.integral_neg
  have h2 : (∫ r in (0 : ℝ)..t, g r).2 = (∫ r in (0 : ℝ)..t, 2 / u r ^ 2).re := by
    have := (ContinuousLinearMap.snd ℝ ℂ ℝ).intervalIntegral_comp_comm hint
    simp only [ContinuousLinearMap.coe_snd'] at this
    rw [← this]
    simp only [hg]
    have hint2 : IntervalIntegrable (fun s => 2 / u s ^ 2) MeasureTheory.volume 0 t :=
      ContinuousOn.intervalIntegrable (by rwa [uIcc_of_le ht])
    exact Complex.reCLM.intervalIntegral_comp_comm hint2
  refine Prod.ext ?_ ?_
  · simp only [rsProc, Prod.fst_add, Prod.smul_fst, rsNoise, h1]
    rw [OnePointExpansion.revMap_eq_sub_drift W hW hz ht]
    simp only [hWdef, drive, Real.toNNReal_coe, Complex.real_smul]
    push_cast
    ring
  · simp only [rsProc, Prod.snd_add, Prod.smul_snd, rsNoise, h2, smul_zero, add_zero, zero_add]
    rfl

/-! ### The core estimate for a nice version of the Brownian motion -/

theorem rs_core (hB : IsPreBrownianReal B P) (hBc : ∀ ω, Continuous (B · ω))
    (hBm : ∀ t, Measurable (B t)) (hB0 : ∀ ω, B 0 ω = 0) {κ r : ℝ} (hκ : 0 ≤ κ) (hr : 0 ≤ r)
    (T : ℝ≥0) {z : ℂ} (hz : 0 < z.im) :
    ∫⁻ ω, ENNReal.ofReal (rsTest κ r (rsProc κ B z T ω)) ∂P ≤
      ENNReal.ofReal (rsTest κ r (z, 0)) := by
  have hP : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  set y₀ := z.im with hy₀
  set U := rsProc κ B z with hUdef
  have hU : ∀ ω (t : ℝ≥0), U t ω = (z, 0) + (∫ r in (0 : ℝ)..t, rsDrift y₀ (U r.toNNReal ω))
      + B t ω • rsNoise κ := rsProc_integralEq hBc κ hz
  have hb := lipschitz_rsDrift hz
  have hbM := norm_rsDrift_le hz
  have hUc : ∀ ω, Continuous (U · ω) := Dynkin.continuous_of_integralEq hBc hb.continuous hbM hU
  have hU0 : ∀ ω, U 0 ω = (z, 0) := by
    intro ω
    rw [hU ω 0, hB0 ω]
    simp
  have hWc : ∀ ω, Continuous (drive κ B ω) := NonSwallow.continuous_drive_ns hBc κ
  have him : ∀ ω t, y₀ ≤ (U t ω).1.im := fun ω t =>
    im_le_im_revMap _ (hWc ω) z hz t.coe_nonneg
  set Lm : ℝ := 2 * T / y₀ ^ 2 with hLm
  have hL : ∀ ω (t : ℝ≥0), t ≤ T → |(U t ω).2| ≤ Lm := by
    intro ω t htT
    show |(∫ s in (0 : ℝ)..t, 2 / (revMap (drive κ B ω) s z) ^ 2).re| ≤ Lm
    refine (Complex.abs_re_le_norm _).trans ?_
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := 2 / y₀ ^ 2)
      fun s hs => ?_).trans ?_
    · rw [uIoc_of_le t.coe_nonneg] at hs
      have h1 : y₀ ≤ ‖revMap (drive κ B ω) s z‖ :=
        (im_le_im_revMap _ (hWc ω) z hz hs.1.le).trans (Complex.im_le_norm _)
      rw [norm_div, norm_pow, show ‖(2 : ℂ)‖ = 2 by norm_num]
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity) (by gcongr)
    · rw [sub_zero, abs_of_nonneg t.coe_nonneg, hLm]
      have : (t : ℝ) ≤ T := htT
      have h0 : 0 ≤ 2 / y₀ ^ 2 := by positivity
      calc 2 / y₀ ^ 2 * (t : ℝ) ≤ 2 / y₀ ^ 2 * T := mul_le_mul_of_nonneg_left this h0
        _ = 2 * T / y₀ ^ 2 := by ring
  -- the regions
  set R : ℕ → ℝ := fun n => ‖z‖ + n + 1 with hR
  set Cl : ℕ → Set (ℂ × ℝ) := fun n => {x | R n ≤ ‖x.1‖} with hCl
  set K : ℕ → Set (ℂ × ℝ) := fun n => {x | y₀ ≤ x.1.im ∧ ‖x.1‖ ≤ R n ∧ |x.2| ≤ Lm} with hK
  have hClc : ∀ n, IsClosed (Cl n) := fun n =>
    isClosed_le continuous_const (continuous_norm.comp continuous_fst)
  have hKc : ∀ n, IsClosed (K n) := fun n =>
    (isClosed_le continuous_const (Complex.continuous_im.comp continuous_fst)).inter
      ((isClosed_le (continuous_norm.comp continuous_fst) continuous_const).inter
        (isClosed_le (continuous_abs.comp continuous_snd) continuous_const))
  have hKO : ∀ n, K n ⊆ rsDom := fun n x hx => hz.trans_le hx.1
  have hLF : ∀ n, ∀ x ∈ K n, x ∉ Cl n → dynkinGen (rsDrift y₀) (rsNoise κ) (rsTest κ r) x = 0 :=
    fun n x hx _ => dynkinGen_rsTest hκ r (hz.trans_le hx.1) hx.1
  have hUK : ∀ n ω (t : ℝ≥0), t ≤ T → (∀ s < t, U s ω ∉ Cl n) → U t ω ∈ K n := by
    intro n ω t htT hs
    refine ⟨him ω t, ?_, hL ω t htT⟩
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with h0 | hpos
    · rw [← h0, hU0 ω]
      simp only [hR]
      have : (0 : ℝ) ≤ n := n.cast_nonneg
      linarith
    · have hcl : IsClosed {s : ℝ≥0 | ‖(U s ω).1‖ ≤ R n} :=
        isClosed_le (continuous_norm.comp (continuous_fst.comp (hUc ω))) continuous_const
      have hsub : Iio t ⊆ {s : ℝ≥0 | ‖(U s ω).1‖ ≤ R n} := fun s hst => by
        have := hs s hst
        simp only [hCl, mem_ofPred_eq, not_le] at this
        exact this.le
      have := (hcl.closure_subset_iff.2 hsub)
      rw [closure_Iio' (a := t) ⟨0, hpos⟩] at this
      exact this (le_refl t)
  set Mn : ℕ → ℝ := fun n => Real.exp (|rsLam κ r| * Lm) * y₀ ^ (rsZeta κ r - 2 * r) *
    (R n ^ 2) ^ r with hMn
  have hc : rsZeta κ r - 2 * r ≤ 0 := by
    simp only [rsZeta]; nlinarith [sq_nonneg r]
  have hFnn : ∀ x : ℂ × ℝ, 0 < x.1.im → 0 ≤ rsTest κ r x := fun x hx => by
    simp only [rsTest]
    have := Real.rpow_nonneg (show (0 : ℝ) ≤ x.1.re ^ 2 + x.1.im ^ 2 by positivity) r
    have := Real.rpow_nonneg hx.le (rsZeta κ r - 2 * r)
    positivity
  have hFM : ∀ n, ∀ x ∈ K n, |rsTest κ r x| ≤ Mn n := by
    intro n x hx
    obtain ⟨hx1, hx2, hx3⟩ := hx
    rw [abs_of_nonneg (hFnn x (hz.trans_le hx1))]
    simp only [rsTest, hMn]
    have hxim : 0 < x.1.im := hz.trans_le hx1
    have e1 : Real.exp (rsLam κ r * x.2) ≤ Real.exp (|rsLam κ r| * Lm) := by
      refine Real.exp_le_exp.2 ((le_abs_self _).trans ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hx3 (abs_nonneg _)
    have e2 : x.1.im ^ (rsZeta κ r - 2 * r) ≤ y₀ ^ (rsZeta κ r - 2 * r) :=
      Real.rpow_le_rpow_of_nonpos hz hx1 hc
    have hN : x.1.re ^ 2 + x.1.im ^ 2 ≤ R n ^ 2 := by
      have h := Complex.sq_norm x.1
      rw [Complex.normSq_apply] at h
      have hRn : 0 ≤ ‖x.1‖ := norm_nonneg _
      nlinarith
    have e3 : (x.1.re ^ 2 + x.1.im ^ 2) ^ r ≤ (R n ^ 2) ^ r :=
      Real.rpow_le_rpow (by positivity) hN hr
    have p2 : 0 ≤ x.1.im ^ (rsZeta κ r - 2 * r) := Real.rpow_nonneg hxim.le _
    have p3 : 0 ≤ (x.1.re ^ 2 + x.1.im ^ 2) ^ r := Real.rpow_nonneg (by positivity) _
    exact mul_le_mul (mul_le_mul e1 e2 p2 (Real.exp_pos _).le) e3 p3
      (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hz.le _))
  -- the stopped martingales
  set Fl := NonSwallow.bmFilt hBm with hFl
  have hmart : ∀ n, Martingale (fun t ω => rsTest κ r (U (min t (hittingBtwn U (Cl n) 0 T ω)) ω))
      Fl P := fun n =>
    martingale_localDynkin_stopped hB hBc Fl (NonSwallow.bmFilt_adapted hBm)
      (NonSwallow.bmFilt_le_past hBm) hb hbM hU isOpen_rsDom (hClc n) (hKc n) (hKO n)
      (contDiffOn_rsTest κ r) (hLF n) T (hUK n) (hFM n)
  set f : ℕ → Ω → ℝ := fun n ω => rsTest κ r (U (min T (hittingBtwn U (Cl n) 0 T ω)) ω) with hf
  have hfint : ∀ n, Integrable (f n) P := fun n => (hmart n).integrable T
  have hfexp : ∀ n, ∫ ω, f n ω ∂P = rsTest κ r (z, 0) := by
    intro n
    have hce := (hmart n).2 0 T (zero_le : (0 : ℝ≥0) ≤ T)
    have h1 : ∫ ω, f n ω ∂P = ∫ ω, rsTest κ r (U (min 0 (hittingBtwn U (Cl n) 0 T ω)) ω) ∂P := by
      rw [← integral_condExp (Fl.le 0)]
      exact integral_congr_ae hce
    rw [h1]
    simp only [zero_le, min_eq_left, hU0, integral_const, probReal_univ, one_smul]
  have hflin : ∀ n, ∫⁻ ω, ENNReal.ofReal (f n ω) ∂P = ENNReal.ofReal (rsTest κ r (z, 0)) := by
    intro n
    rw [← hfexp n, ofReal_integral_eq_lintegral_ofReal (hfint n) (ae_of_all _ fun ω => hFnn _ (hz.trans_le (him ω _)))]
  -- eventually the stopping time is `T`
  have hev : ∀ ω, ∀ᶠ n in atTop, f n ω = rsTest κ r (U T ω) := by
    intro ω
    obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).exists_bound_of_continuousOn
      (hUc ω).continuousOn
    filter_upwards [eventually_ge_atTop ⌈C⌉₊] with n hn
    have hnot : ¬ ∃ j ∈ Icc (0 : ℝ≥0) T, U j ω ∈ Cl n := by
      rintro ⟨j, hj, hjCl⟩
      have h1 := hC j hj
      have h2 : ‖(U j ω).1‖ ≤ ‖U j ω‖ := norm_fst_le _
      have h3 : C ≤ n := (Nat.le_ceil C).trans (by exact_mod_cast hn)
      have h4 : R n ≤ ‖(U j ω).1‖ := hjCl
      simp only [hR] at h4
      have : 0 ≤ ‖z‖ := norm_nonneg _
      linarith
    have hτ : hittingBtwn U (Cl n) 0 T ω = T := by
      simp only [hittingBtwn, if_neg hnot]
    simp only [hf, hτ, min_self]
  have hlim : ∀ ω, liminf (fun n => ENNReal.ofReal (f n ω)) atTop =
      ENNReal.ofReal (rsTest κ r (U T ω)) := by
    intro ω
    refine Tendsto.liminf_eq ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev ω] with n hn
    rw [hn]
  calc ∫⁻ ω, ENNReal.ofReal (rsTest κ r (U T ω)) ∂P
      = ∫⁻ ω, liminf (fun n => ENNReal.ofReal (f n ω)) atTop ∂P :=
        lintegral_congr fun ω => (hlim ω).symm
    _ ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal (f n ω) ∂P) atTop :=
        lintegral_liminf_le' fun n => (hfint n).aemeasurable.ennreal_ofReal
    _ ≤ ENNReal.ofReal (rsTest κ r (z, 0)) :=
        liminf_le_of_frequently_le' (Frequently.of_forall fun n => (hflin n).le)

/-! ### The Rohde–Schramm martingale bound -/

/-- **RS E1 (Rohde–Schramm, Thm 3.2; Kemppainen, Thm 5.5).** For a standard Brownian motion `B`,
`0 < κ`, `0 ≤ r`, `0 ≤ T` and `z ∈ ℍ`, with `u_T = revMap (drive κ B ω) T z`,
`E[|u_T'(z)|^λ (Im u_T)^ζ (Im u_T/|u_T|)^{−2r}] ≤ (Im z)^ζ (Im z/|z|)^{−2r}`, where
`λ = rsLam κ r` and `ζ = rsZeta κ r`. -/
theorem rs_martingale_bound {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P) {κ r T : ℝ} (hκ : 0 < κ) (hr : 0 ≤ r)
    (hT : 0 ≤ T) {z : ℂ} (hz : z ∈ H) :
    ∫⁻ ω, ENNReal.ofReal (‖deriv (revMap (drive κ B ω) T) z‖ ^ rsLam κ r
        * (revMap (drive κ B ω) T z).im ^ rsZeta κ r
        * ((revMap (drive κ B ω) T z).im / ‖revMap (drive κ B ω) T z‖) ^ (-2 * r)) ∂P
      ≤ ENNReal.ofReal (z.im ^ rsZeta κ r * (z.im / ‖z‖) ^ (-2 * r)) := by
  have hz' : 0 < z.im := hz
  obtain ⟨B', hB'm, hB'c, hB'eq⟩ := WedgeRes.exists_good_version hB
  set B'' : ℝ≥0 → Ω → ℝ := fun t ω => B' t ω - B' 0 ω with hB''
  have hB0 : ∀ᵐ ω ∂P, B 0 ω = 0 := hB.toIsPreBrownianReal.eval_zero_ae_eq_zero
  have hB''eq : ∀ᵐ ω ∂P, ∀ t, B'' t ω = B t ω := by
    filter_upwards [hB'eq, hB0] with ω h1 h2
    intro t
    simp only [hB'', h1, h2, sub_zero]
  have hB''pre : IsPreBrownianReal B'' P :=
    hB.toIsPreBrownianReal.congr fun t => hB''eq.mono fun ω h => (h t).symm
  have hB''m : ∀ t, Measurable (B'' t) := fun t =>
    (hB'm.comp measurable_prodMk_left).sub (hB'm.comp measurable_prodMk_left)
  have hB''c : ∀ ω, Continuous (B'' · ω) := fun ω => (hB'c ω).sub continuous_const
  have hB''0 : ∀ ω, B'' 0 ω = 0 := fun ω => sub_self _
  have hcore := rs_core hB''pre hB''c hB''m hB''0 hκ.le hr T.toNNReal hz'
  have hTT : ((T.toNNReal : ℝ≥0) : ℝ) = T := Real.coe_toNNReal T hT
  have hrhs : rsTest κ r (z, 0) = z.im ^ rsZeta κ r * (z.im / ‖z‖) ^ (-2 * r) := by
    rw [rsTest_eq κ r hz', mul_zero, Real.exp_zero, one_mul]
  rw [hrhs] at hcore
  refine le_of_eq_of_le (lintegral_congr_ae ?_) hcore
  filter_upwards [hB''eq] with ω hω
  have hdr : drive κ B'' ω = drive κ B ω := funext fun t => by simp only [drive, hω]
  have hWc : Continuous (drive κ B ω) := hdr ▸ NonSwallow.continuous_drive_ns hB''c κ ω
  simp only [rsProc, hTT, hdr]
  rw [rsTest_revMap hWc κ r hT hz]

end RS
end QuantumZipper
