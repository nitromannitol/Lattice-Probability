/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3D108R1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S2L5Kernel
import LatticeProb.Bonanno.LQGMetric.Field.HeatMollifyCont

/-!
# CONF Lemma 2.10, white-noise model on a general bounded open set: the kernel `K^I_U ρ`

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`, proof of Lemma 2.10 (C:722–731):
`h_{s,t} = √π ∫_{s²}^{t²} ∫_U p^U_{r/2}(z, w) W(dw, dr)` (Rhodes–Vargas, Lemma 5.4).
Paired with a bounded test function `ρ`, the kernel is

  `uKer U I ρ (s, w) = ∫ ρ(y) 1_I(s) p_U(s/2; y, w) dy`

(DZZ's `wndKernel`, integrated against `ρ`; for a square this is `DDDF.P29WN.zbKerFun`, which is
written with the image-series kernel). Here, for **any bounded open `U`** and any time set
`I ⊆ (0, ∞)` (including `I = (0, ∞)`, where the point kernels are not square integrable):

* `lintegral_triple_lt_top`: `∫∫∫ |ρ(y)| |σ(y')| K_y K_{y'} < ∞` (Chapman–Kolmogorov
  `lintegral_wndKernel_mul`, `∫ p_U(s; y, ·) ≤ 1` for `s ≤ 1`, `p_U(s) ≤ R²/(π s²)` for `s ≥ 1`);
* `memLp_uKer`, `uKerL2`;
* **`inner_uKerL2`**: `⟪K^I ρ, K^I σ⟫ = ∫∫ ρ(y) σ(y') ∫_I p_U(s; y, y') ds dy dy'` (CONF C:724–727,
  "by the Chapman–Kolmogorov equation"; cf. `DDDF.P29WN.inner_zbKerL2` for the square).

Generalisation of `DDDF.P29WN.zbKerFun`/`inner_zbKerL2` (square) and of `DZZ.inner_wndKernelL2`
(point kernels, `I ⊆ (c₀, ∞)`); own bookkeeping (Fubini–Tonelli).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal RealInnerProductSpace

namespace LQGMetric.CONF.ZBM

open KilledHeat WhiteNoise DZZ

/-- the white-noise kernel of the pairing with `ρ`: `(s, w) ↦ ∫ ρ(y) 1_I(s) p_U(s/2; y, w) dy` -/
def uKer (U : Set ℂ) (I : Set ℝ) (ρ : ℂ → ℝ) (p : ℝ × ℂ) : ℝ :=
  ∫ y, ρ y * wndKernel U I y p

variable {U : Set ℂ} {I : Set ℝ}

lemma measurable_wndKernel_comp (hU : IsOpen U) (hI : MeasurableSet I) {α : Type*}
    [MeasurableSpace α] {f : α → ℂ} {g : α → ℝ × ℂ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun a => wndKernel U I (f a) (g a)) := by
  have e : (fun a => wndKernel U I (f a) (g a)) =
      ((fun a => (g a).1) ⁻¹' I).indicator
        (fun a => killedHeat U ((g a).1 / 2).toNNReal (f a) (g a).2) := by
    funext a
    by_cases h : (g a).1 ∈ I <;> simp [wndKernel, h]
  rw [e]
  refine Measurable.indicator ?_ (hI.preimage (measurable_fst.comp hg))
  exact (measurable_killedHeat hU).comp
    (((measurable_fst.comp hg).div_const 2).real_toNNReal.prodMk
      (hf.prodMk (measurable_snd.comp hg)))

lemma measurable_killedHeat_comp (hU : IsOpen U) {α : Type*} [MeasurableSpace α] {t : α → ℝ}
    {f g : α → ℂ} (ht : Measurable t) (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a => killedHeat U (t a).toNNReal (f a) (g a) :=
  (measurable_killedHeat hU).comp (ht.real_toNNReal.prodMk (hf.prodMk hg))

lemma measurable_uKer (hU : IsOpen U) (hI : MeasurableSet I) {ρ : ℂ → ℝ} (hρ : Measurable ρ) :
    Measurable (uKer U I ρ) := by
  have h1 : Measurable fun x : (ℝ × ℂ) × ℂ => wndKernel U I x.2 x.1 :=
    measurable_wndKernel_comp hU hI measurable_snd measurable_fst
  have hm : Measurable fun x : (ℝ × ℂ) × ℂ => ρ x.2 * wndKernel U I x.2 x.1 :=
    (hρ.comp measurable_snd).mul h1
  exact (hm.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℂ))).measurable

/-- `∫ p_U(s; y, y') dy' ≤ 1` -/
lemma lintegral_killedHeat_le_one {s : ℝ} (hs : 0 < s) (y : ℂ) :
    ∫⁻ y', ENNReal.ofReal (killedHeat U s.toNNReal y y') ≤ 1 := by
  have hc : ((s.toNNReal : ℝ≥0) : ℝ) = s := Real.coe_toNNReal _ hs.le
  have hint : Integrable (fun w => heatKernel s y w) := by
    by_contra h
    have := integral_undef h
    rw [integral_heatKernel s hs y] at this
    exact one_ne_zero this
  calc ∫⁻ y', ENNReal.ofReal (killedHeat U s.toNNReal y y')
      ≤ ∫⁻ y', ENNReal.ofReal (heatKernel s y y') := by
        refine lintegral_mono fun y' => ENNReal.ofReal_le_ofReal ?_
        have := killedHeat_le_heatKernel U s.toNNReal y y'
        rwa [hc] at this
    _ = 1 := by
        rw [← ofReal_integral_eq_lintegral_ofReal hint
          (ae_of_all _ fun w => by
            have := heatKernel_nonneg' s.toNNReal y w; rwa [hc] at this),
          integral_heatKernel s hs y, ENNReal.ofReal_one]

variable {c : ℂ} {R : ℝ}

/-- the time integral of a weighted killed heat kernel, uniformly in the start point -/
lemma lintegral_time_weight_le (hU : IsOpen U) (hR : 0 ≤ R) (hUR : U ⊆ Metric.ball c R)
    {g : ℂ → ℝ≥0∞} (hg : Measurable g) {C : ℝ} (hgC : ∀ z, g z ≤ ENNReal.ofReal C) (y : ℂ) :
    ∫⁻ s in Ioi (0 : ℝ), ∫⁻ y', g y' * ENNReal.ofReal (killedHeat U s.toNNReal y y') ≤
      ENNReal.ofReal C * volume (Ioc (0 : ℝ) 1) + (∫⁻ z, g z) *
        ∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (R ^ 2 / Real.pi * s ^ (-2 : ℝ)) := by
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one, lintegral_union measurableSet_Ioi
    (Ioc_disjoint_Ioi le_rfl)]
  refine add_le_add ?_ ?_
  · calc ∫⁻ s in Ioc (0 : ℝ) 1, ∫⁻ y', g y' * ENNReal.ofReal (killedHeat U s.toNNReal y y')
        ≤ ∫⁻ s in Ioc (0 : ℝ) 1, ENNReal.ofReal C := by
          refine setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
          calc ∫⁻ y', g y' * ENNReal.ofReal (killedHeat U s.toNNReal y y')
              ≤ ∫⁻ y', ENNReal.ofReal C * ENNReal.ofReal (killedHeat U s.toNNReal y y') :=
                lintegral_mono fun y' => by gcongr; exact hgC y'
            _ = ENNReal.ofReal C * ∫⁻ y', ENNReal.ofReal (killedHeat U s.toNNReal y y') := by
                rw [lintegral_const_mul]
                exact (measurable_killedHeat_comp hU measurable_const measurable_const
                  measurable_id).ennreal_ofReal
            _ ≤ ENNReal.ofReal C * 1 := by gcongr; exact lintegral_killedHeat_le_one hs.1 y
            _ = ENNReal.ofReal C := mul_one _
      _ = ENNReal.ofReal C * volume (Ioc (0 : ℝ) 1) := setLIntegral_const _ _
  · calc ∫⁻ s in Ioi (1 : ℝ), ∫⁻ y', g y' * ENNReal.ofReal (killedHeat U s.toNNReal y y')
        ≤ ∫⁻ s in Ioi (1 : ℝ), (∫⁻ z, g z) * ENNReal.ofReal (R ^ 2 / Real.pi * s ^ (-2 : ℝ)) := by
          refine setLIntegral_mono' measurableSet_Ioi fun s (hs : 1 < s) => ?_
          rw [← lintegral_mul_const _ hg]
          exact lintegral_mono fun y' => by
            gcongr; exact killedHeat_le_rpow hR hUR (one_pos.trans hs) y y'
      _ = (∫⁻ z, g z) * ∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (R ^ 2 / Real.pi * s ^ (-2 : ℝ)) := by
          rw [lintegral_const_mul]
          exact (measurable_const.mul (measurable_id.pow_const _)).ennreal_ofReal

lemma tBnd_lt_top (C : ℝ) {M : ℝ≥0∞} (hM : M ≠ ∞) (R : ℝ) :
    ENNReal.ofReal C * volume (Ioc (0 : ℝ) 1) + M *
      ∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (R ^ 2 / Real.pi * s ^ (-2 : ℝ)) < ∞ := by
  have hint : IntegrableOn (fun s : ℝ => R ^ 2 / Real.pi * s ^ (-2 : ℝ)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos).const_mul _
  refine ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by simp),
    ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hM) hint.lintegral_lt_top⟩

lemma measurable_lintegral_time (hU : IsOpen U) {α : Type*} [MeasurableSpace α] {f g : α → ℂ}
    (hf : Measurable f) (hg : Measurable g) :
    Measurable fun a => ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (killedHeat U s.toNNReal (f a) (g a)) := by
  have hF : Measurable fun x : α × ℝ => ENNReal.ofReal (killedHeat U x.2.toNNReal (f x.1) (g x.1)) :=
    (measurable_killedHeat_comp hU measurable_snd (hf.comp measurable_fst)
      (hg.comp measurable_fst)).ennreal_ofReal
  exact hF.lintegral_prod_right' (ν := volume.restrict (Ioi (0 : ℝ)))

/-- the weighted double kernel integral over `(s, w)` -/
lemma lintegral_wnd_mul_le (hU : IsOpen U) (hI : MeasurableSet I) (hI0 : I ⊆ Ioi 0) (y y' : ℂ) :
    ∫⁻ p, ENNReal.ofReal (wndKernel U I y p) * ENNReal.ofReal (wndKernel U I y' p) ≤
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (killedHeat U s.toNNReal y y') := by
  rw [lintegral_wndKernel_mul hU hI hI0 y y']
  exact lintegral_mono_set hI0

set_option maxHeartbeats 1000000 in
/-- **the triple integral is finite** (order: `(s, w)` first, then `(y, y')`) -/
theorem lintegral_triple_lt_top (hU : IsOpen U) (hR : 0 ≤ R) (hUR : U ⊆ Metric.ball c R)
    (hI : MeasurableSet I) (hI0 : I ⊆ Ioi 0) {g h : ℂ → ℝ≥0∞} (hg : Measurable g)
    (hh : Measurable h) (hgi : ∫⁻ z, g z ≠ ∞) {C : ℝ} (hhC : ∀ z, h z ≤ ENNReal.ofReal C)
    (hhi : ∫⁻ z, h z ≠ ∞) :
    ∫⁻ x : (ℝ × ℂ) × (ℂ × ℂ), g x.2.1 * h x.2.2 * (ENNReal.ofReal (wndKernel U I x.2.1 x.1) *
      ENNReal.ofReal (wndKernel U I x.2.2 x.1)) < ∞ := by
  have hm : Measurable fun x : (ℝ × ℂ) × (ℂ × ℂ) => g x.2.1 * h x.2.2 *
      (ENNReal.ofReal (wndKernel U I x.2.1 x.1) * ENNReal.ofReal (wndKernel U I x.2.2 x.1)) :=
    ((hg.comp (measurable_fst.comp measurable_snd)).mul
      (hh.comp (measurable_snd.comp measurable_snd))).mul
      ((measurable_wndKernel_comp hU hI (measurable_fst.comp measurable_snd)
        measurable_fst).ennreal_ofReal.mul (measurable_wndKernel_comp hU hI
        (measurable_snd.comp measurable_snd) measurable_fst).ennreal_ofReal)
  rw [Measure.volume_eq_prod (α := ℝ × ℂ) (β := ℂ × ℂ),
    lintegral_prod_symm _ hm.aemeasurable]
  have hkm : Measurable fun q : ℂ × ℂ =>
      ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (killedHeat U s.toNNReal q.1 q.2) :=
    measurable_lintegral_time hU measurable_fst measurable_snd
  calc ∫⁻ q : ℂ × ℂ, ∫⁻ p : ℝ × ℂ, g q.1 * h q.2 * (ENNReal.ofReal (wndKernel U I q.1 p) *
        ENNReal.ofReal (wndKernel U I q.2 p))
      ≤ ∫⁻ q : ℂ × ℂ, g q.1 * h q.2 *
          ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (killedHeat U s.toNNReal q.1 q.2) := by
        refine lintegral_mono fun q => ?_
        refine (lintegral_const_mul (g q.1 * h q.2)
          ((measurable_wndKernel hU hI q.1).ennreal_ofReal.mul
          (measurable_wndKernel hU hI q.2).ennreal_ofReal)).trans_le ?_
        gcongr; exact lintegral_wnd_mul_le hU hI hI0 q.1 q.2
    _ = ∫⁻ y, g y * ∫⁻ y', h y' *
          ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (killedHeat U s.toNNReal y y') := by
        rw [Measure.volume_eq_prod (α := ℂ) (β := ℂ),
          lintegral_prod (f := fun q : ℂ × ℂ => g q.1 * h q.2 *
            ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (killedHeat U s.toNNReal q.1 q.2))
            (((hg.comp measurable_fst).mul (hh.comp measurable_snd)).mul hkm).aemeasurable]
        refine lintegral_congr fun y => ?_
        have hy : Measurable fun y' : ℂ => h y' *
            ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (killedHeat U s.toNNReal y y') :=
          hh.mul (measurable_lintegral_time hU measurable_const measurable_id)
        rw [← lintegral_const_mul (g y) hy]
        exact lintegral_congr fun y' => by ring
    _ = ∫⁻ y, g y * ∫⁻ s in Ioi (0 : ℝ), ∫⁻ y', h y' *
          ENNReal.ofReal (killedHeat U s.toNNReal y y') := by
        refine lintegral_congr fun y => ?_
        congr 1
        have hk : Measurable fun x : ℂ × ℝ =>
            h x.1 * ENNReal.ofReal (killedHeat U x.2.toNNReal y x.1) :=
          (hh.comp measurable_fst).mul (measurable_killedHeat_comp hU measurable_snd
            measurable_const measurable_fst).ennreal_ofReal
        have e : ∀ y', h y' * ∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (killedHeat U s.toNNReal y y') =
            ∫⁻ s in Ioi (0 : ℝ), h y' * ENNReal.ofReal (killedHeat U s.toNNReal y y') := fun y' =>
          (lintegral_const_mul _ (measurable_killedHeat_comp hU measurable_id
            measurable_const measurable_const).ennreal_ofReal).symm
        simp_rw [e]
        exact lintegral_lintegral_swap hk.aemeasurable
    _ ≤ ∫⁻ y, g y * (ENNReal.ofReal C * volume (Ioc (0 : ℝ) 1) + (∫⁻ z, h z) *
          ∫⁻ s in Ioi (1 : ℝ), ENNReal.ofReal (R ^ 2 / Real.pi * s ^ (-2 : ℝ))) :=
        lintegral_mono fun y => by gcongr; exact lintegral_time_weight_le hU hR hUR hh hhC y
    _ < ∞ := by
        rw [lintegral_mul_const _ hg]
        exact ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hgi) (tBnd_lt_top C hhi R)

lemma enorm_uKer_le (ρ : ℂ → ℝ) (p : ℝ × ℂ) :
    ‖uKer U I ρ p‖ₑ ≤ ∫⁻ y, ‖ρ y‖ₑ * ENNReal.ofReal (wndKernel U I y p) := by
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun y => ?_))
  rw [enorm_mul, Real.enorm_of_nonneg (wndKernel_nonneg _ _ _ _)]

lemma enorm_le_ofReal {ρ : ℂ → ℝ} {C : ℝ} (hC : ∀ z, |ρ z| ≤ C) (z : ℂ) :
    ‖ρ z‖ₑ ≤ ENNReal.ofReal C := by
  rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (hC z)

/-- the kernel `K^I_U ρ` is square integrable -/
theorem memLp_uKer (hU : IsOpen U) (hR : 0 ≤ R) (hUR : U ⊆ Metric.ball c R)
    (hI : MeasurableSet I) (hI0 : I ⊆ Ioi 0) {ρ : ℂ → ℝ} (hρ : Measurable ρ) {C : ℝ}
    (hC : ∀ z, |ρ z| ≤ C) (hρi : Integrable ρ) : MemLp (uKer U I ρ) 2 volume := by
  have hm := measurable_uKer hU hI hρ
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
  refine ⟨(hm.pow_const 2).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have hg : Measurable fun y => ‖ρ y‖ₑ := hρ.enorm
  have hG : Measurable fun x : (ℝ × ℂ) × ℂ => ‖ρ x.2‖ₑ * ENNReal.ofReal (wndKernel U I x.2 x.1) :=
    (hg.comp measurable_snd).mul (measurable_wndKernel_comp hU hI measurable_snd
      measurable_fst).ennreal_ofReal
  calc ∫⁻ p, ‖uKer U I ρ p ^ 2‖ₑ
      ≤ ∫⁻ p, (∫⁻ y, ‖ρ y‖ₑ * ENNReal.ofReal (wndKernel U I y p)) *
          ∫⁻ y, ‖ρ y‖ₑ * ENNReal.ofReal (wndKernel U I y p) := by
        refine lintegral_mono fun p => ?_
        rw [enorm_pow, pow_two]
        exact mul_le_mul' (enorm_uKer_le ρ p) (enorm_uKer_le ρ p)
    _ = ∫⁻ x : (ℝ × ℂ) × (ℂ × ℂ), ‖ρ x.2.1‖ₑ * ‖ρ x.2.2‖ₑ *
          (ENNReal.ofReal (wndKernel U I x.2.1 x.1) *
            ENNReal.ofReal (wndKernel U I x.2.2 x.1)) := by
        rw [Measure.volume_eq_prod (α := ℝ × ℂ) (β := ℂ × ℂ), lintegral_prod
          (f := fun x : (ℝ × ℂ) × (ℂ × ℂ) => ‖ρ x.2.1‖ₑ * ‖ρ x.2.2‖ₑ *
            (ENNReal.ofReal (wndKernel U I x.2.1 x.1) * ENNReal.ofReal (wndKernel U I x.2.2 x.1)))
          (((hg.comp (measurable_fst.comp measurable_snd)).mul
            (hg.comp (measurable_snd.comp measurable_snd))).mul
            ((measurable_wndKernel_comp hU hI (measurable_fst.comp measurable_snd)
              measurable_fst).ennreal_ofReal.mul (measurable_wndKernel_comp hU hI
              (measurable_snd.comp measurable_snd) measurable_fst).ennreal_ofReal)).aemeasurable]
        refine lintegral_congr fun p => ?_
        have hA : Measurable fun y => ‖ρ y‖ₑ * ENNReal.ofReal (wndKernel U I y p) :=
          hg.mul (measurable_wndKernel_comp hU hI measurable_id measurable_const).ennreal_ofReal
        rw [Measure.volume_eq_prod (α := ℂ) (β := ℂ), ← lintegral_prod_mul hA.aemeasurable
          hA.aemeasurable]
        exact lintegral_congr fun q => by simp only; ring
    _ < ∞ := lintegral_triple_lt_top hU hR hUR hI hI0 hg hg hρi.hasFiniteIntegral.ne
        (enorm_le_ofReal hC) hρi.hasFiniteIntegral.ne

open Classical in
/-- the `L²` class of `K^I_U ρ` (junk `0` if it is not square integrable) -/
def uKerL2 (U : Set ℂ) (I : Set ℝ) (ρ : ℂ → ℝ) : WNSpace :=
  if h : MemLp (uKer U I ρ) 2 volume then h.toLp _ else 0

lemma coeFn_uKerL2 {ρ : ℂ → ℝ} (h : MemLp (uKer U I ρ) 2 volume) :
    (uKerL2 U I ρ : ℝ × ℂ → ℝ) =ᵐ[volume] uKer U I ρ := by
  rw [uKerL2, dite_eq_left_of_eq_true (eq_true h)]
  exact h.coeFn_toLp

/-- `∫ K_y K_{y'} = ∫_I p_U(s; y, y') ds` as Bochner integrals -/
lemma integral_wnd_mul (hU : IsOpen U) (hI : MeasurableSet I) (hI0 : I ⊆ Ioi 0) (y y' : ℂ) :
    ∫ p, wndKernel U I y p * wndKernel U I y' p = ∫ s in I, killedHeat U s.toNNReal y y' := by
  rw [integral_eq_lintegral_of_nonneg_ae
      (ae_of_all _ fun p => mul_nonneg (wndKernel_nonneg _ _ _ _) (wndKernel_nonneg _ _ _ _))
      ((measurable_wndKernel hU hI y).mul (measurable_wndKernel hU hI y')).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun s => killedHeat_nonneg _ _ _ _)
      (measurable_killedHeat_time hU y y').aestronglyMeasurable]
  simp_rw [ENNReal.ofReal_mul (wndKernel_nonneg _ _ _ _)]
  rw [lintegral_wndKernel_mul hU hI hI0 y y']

/-- **CONF C:724–727 (Chapman–Kolmogorov)**: `⟪K^I ρ, K^I σ⟫ = ∫∫ ρ(y) σ(y') ∫_I p_U(s; y, y') ds` -/
theorem inner_uKerL2 (hU : IsOpen U) (hR : 0 ≤ R) (hUR : U ⊆ Metric.ball c R)
    (hI : MeasurableSet I) (hI0 : I ⊆ Ioi 0) {ρ σ : ℂ → ℝ} (hρ : Measurable ρ)
    (hσ : Measurable σ) {C : ℝ} (hρC : ∀ z, |ρ z| ≤ C) (hσC : ∀ z, |σ z| ≤ C)
    (hρi : Integrable ρ) (hσi : Integrable σ) :
    ⟪uKerL2 U I ρ, uKerL2 U I σ⟫ =
      ∫ q : ℂ × ℂ, ρ q.1 * σ q.2 * ∫ s in I, killedHeat U s.toNNReal q.1 q.2 := by
  have h1 := memLp_uKer hU hR hUR hI hI0 hρ hρC hρi
  have h2 := memLp_uKer hU hR hUR hI hI0 hσ hσC hσi
  rw [L2.inner_def]
  have e1 : (fun p => ⟪(uKerL2 U I ρ : ℝ × ℂ → ℝ) p, (uKerL2 U I σ : ℝ × ℂ → ℝ) p⟫) =ᵐ[volume]
      fun p => uKer U I ρ p * uKer U I σ p := by
    filter_upwards [coeFn_uKerL2 h1, coeFn_uKerL2 h2] with p e e'
    rw [e, e', real_inner_eq_re_inner, RCLike.inner_apply]
    simp [mul_comm]
  rw [integral_congr_ae e1]
  set F : (ℝ × ℂ) → (ℂ × ℂ) → ℝ := fun p q =>
    (ρ q.1 * wndKernel U I q.1 p) * (σ q.2 * wndKernel U I q.2 p) with hFdef
  have e2 : ∀ p, uKer U I ρ p * uKer U I σ p = ∫ q : ℂ × ℂ, F p q := fun p => by
    rw [Measure.volume_eq_prod (α := ℂ) (β := ℂ)]
    exact (integral_prod_mul (fun y => ρ y * wndKernel U I y p)
      (fun y => σ y * wndKernel U I y p)).symm
  simp_rw [e2]
  have hFm : Measurable (Function.uncurry F) :=
    ((hρ.comp (measurable_fst.comp measurable_snd)).mul (measurable_wndKernel_comp hU hI
      (measurable_fst.comp measurable_snd) measurable_fst)).mul
      ((hσ.comp (measurable_snd.comp measurable_snd)).mul (measurable_wndKernel_comp hU hI
      (measurable_snd.comp measurable_snd) measurable_fst))
  have hFi : Integrable (Function.uncurry F) ((volume : Measure (ℝ × ℂ)).prod
      (volume : Measure (ℂ × ℂ))) := by
    refine ⟨hFm.aestronglyMeasurable, ?_⟩
    unfold HasFiniteIntegral
    have ht := lintegral_triple_lt_top hU hR hUR hI hI0 hρ.enorm hσ.enorm
      hρi.hasFiniteIntegral.ne (enorm_le_ofReal hσC) hσi.hasFiniteIntegral.ne
    rw [Measure.volume_eq_prod (α := ℝ × ℂ) (β := ℂ × ℂ)] at ht
    refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun x => ?_)) ht
    simp only [Function.uncurry, hFdef, enorm_mul, Real.enorm_of_nonneg (wndKernel_nonneg _ _ _ _)]
    ring
  rw [integral_integral_swap hFi]
  refine integral_congr_ae (Eventually.of_forall fun q => ?_)
  simp only [hFdef]
  rw [← integral_wnd_mul hU hI hI0, ← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun p => by ring)

end LQGMetric.CONF.ZBM
