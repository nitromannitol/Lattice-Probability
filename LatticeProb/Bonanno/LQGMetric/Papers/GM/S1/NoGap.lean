/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S1.NoGap at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.Median
import LatticeProb.Bonanno.LQGMetric.Metric.WeylBasic
import LatticeProb.Bonanno.LQGMetric.Metric.WeylScaling
import LatticeProb.Bonanno.LQGMetric.Metric.InternalC

/-!
# GM.S1.18′: no gap in the law of the left–right crossing distance

Blueprint `blueprint/M1.md` §3 row 22; decision DEC-A D-A2 (iii) (`decisions/DEC-A.md`),
filling GM's "Therefore, the multiplicative constant factor is 1" (GM = arXiv:1905.00383v3,
`literature/src/1905.00383/uniqueness-final.tex` l. 590), which needs that `D_h(L, R)` has a
unique median.

`gm_S1_18`: for a weak γ-LQG metric `D`, a normalized whole-plane GFF `h` and `a < b`,
`P[D_h(L,R) ≤ a] > 0 ⇒ P[a < D_h(L,R) < b] > 0`. Proof (D-A2 (iii)):
* `f ∈ 𝓓(ℂ)` with `f ≥ 1` within distance `1/4` of `L` and `f_1(0) = 0` (`exists_noGap_test`);
* by Axiom III (one null set for all `f`), `θ(t) := D_{h+tf}(L,R) = (e^{ξ t f}·D_h)(L,R)`;
  `θ` is continuous (`crossFn_weyl_le`: `θ(t) ≤ e^{ξ|t−s|‖f‖∞} θ(s)`) and
  `θ(t) ≥ e^{ξ t} c₀ → ∞` (`le_weylScale_of_exit`, the inequality across an annulus in the proof
  of Gwynne, arXiv:1909.08588, Lemma 2.5, LaTeX l. 626–660, here with the `1/4`-neighbourhood
  of `L` in place of the annulus);
* IVT: on `{θ(0) ≤ a}` some rational `q > 0` has `θ(q) ∈ (a, b)`;
* Cameron–Martin (`measure_addFun_preimage_eq_zero`) transfers positivity from `h + qf` to `h`
  (`measure_Ioo_pos_of_shift`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric
namespace GM

/-- `ξ f ≤ ξ g + c` ⇒ `e^{ξ f}·D ≤ e^c (e^{ξ g}·D)`. -/
theorem weylScale_le_exp_mul {ξ c : ℝ} {f g : C(ℂ, ℝ)} {D : ContMetric}
    (hfg : ∀ x, ξ * f x ≤ ξ * g x + c) (z w : ℂ) :
    weylScale ξ f D z w ≤ ENNReal.ofReal (Real.exp c) * weylScale ξ g D z w := by
  have h0 : ENNReal.ofReal (Real.exp c) ≠ 0 := (ENNReal.ofReal_pos.2 (Real.exp_pos c)).ne'
  have ht : ENNReal.ofReal (Real.exp c) ≠ ⊤ := ENNReal.ofReal_ne_top
  simp only [weylScale, ENNReal.mul_iInf_of_ne h0 ht]
  refine iInf_mono fun L => iInf_mono fun P => iInf_mono fun _ => iInf_mono fun _ =>
    iInf_mono fun _ => iInf_mono fun _ => iInf_mono fun _ => ?_
  rw [← lintegral_const_mul' _ _ ht]
  refine setLIntegral_mono' measurableSet_Icc fun t _ => ?_
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith [hfg (P t)]))

lemma infDist_eq_zero_of_mem_leftSide {z : ℂ} (hz : z ∈ leftSide) :
    Metric.infDist z leftSide = 0 := Metric.infDist_zero_of_mem hz

/-- Every `D`-unit-speed path from `L` to a point at distance `≥ 1/4` from `L` spends time at
least `D(L, {dist(·, L) = 1/4})` in the `1/4`-neighbourhood of `L`; so `a ≤ ξ f` there gives
`(e^{ξ f}·D)(z, w) ≥ e^a c₀` (the inequality across an annulus in the proof of Gwynne,
arXiv:1909.08588, Lemma 2.5, LaTeX l. 626–660). -/
theorem le_weylScale_of_exit {ξ a c₀ : ℝ} {f : C(ℂ, ℝ)} {D : ContMetric}
    (hf : ∀ x, Metric.infDist x leftSide ≤ 4⁻¹ → a ≤ ξ * f x)
    (hc₀ : ∀ u ∈ leftSide, ∀ v, Metric.infDist v leftSide = 4⁻¹ → c₀ ≤ D.1 (u, v))
    {z w : ℂ} (hz : z ∈ leftSide) (hw : 4⁻¹ ≤ Metric.infDist w leftSide) :
    ENNReal.ofReal (Real.exp a * c₀) ≤ weylScale ξ f D z w := by
  rw [← weylScaleOn_univ]
  refine le_weylScaleOn fun Lp P hL hc hu h0 h1 _ => ?_
  have hPc : ContinuousOn P (Icc 0 Lp) := (D.continuous_unpt).comp_continuousOn hc
  set g : ℝ → ℝ := fun s => Metric.infDist (P s) leftSide with hg_def
  have hg : ContinuousOn g (Icc 0 Lp) :=
    (Metric.continuous_infDist_pt leftSide).comp_continuousOn hPc
  set S := Icc 0 Lp ∩ g ⁻¹' Ici 4⁻¹ with hS_def
  have hS : IsClosed S := hg.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hbdd : BddBelow S := ⟨0, fun s hs => hs.1.1⟩
  have hSne : S.Nonempty := ⟨Lp, ⟨⟨hL, le_rfl⟩, by simp only [mem_preimage, g, h1]; exact hw⟩⟩
  set s₀ := sInf S
  have hs₀ : s₀ ∈ S := hS.csInf_mem hSne hbdd
  have hg0 : g 0 = 0 := by simp only [g, h0]; exact infDist_eq_zero_of_mem_leftSide hz
  obtain ⟨s₁, hs₁, hgs₁⟩ : ∃ s₁ ∈ Icc 0 s₀, g s₁ = 4⁻¹ :=
    intermediate_value_Icc hs₀.1.1 (hg.mono (Icc_subset_Icc_right hs₀.1.2))
      ⟨by rw [hg0]; norm_num, hs₀.2⟩
  have hs₁S : s₁ ∈ S := ⟨⟨hs₁.1, hs₁.2.trans hs₀.1.2⟩, hgs₁.ge⟩
  have hs₁eq : s₁ = s₀ := le_antisymm hs₁.2 (csInf_le hbdd hs₁S)
  have hle : ∀ s ∈ Icc 0 s₀, g s ≤ 4⁻¹ := by
    intro s hs
    rcases eq_or_lt_of_le hs.2 with h | h
    · rw [h, ← hs₁eq, hgs₁]
    · by_contra hcon
      have hsS : s ∈ S := ⟨⟨hs.1, hs.2.trans hs₀.1.2⟩, (not_le.1 hcon).le⟩
      exact absurd (csInf_le hbdd hsS) (not_le.2 h)
  have hd : D.1 (P 0, P s₀) ≤ s₀ := by
    have := (MetricGeometry.lipschitzOnWith_of_hasUnitSpeedOn hu).dist_le_mul 0 ⟨le_rfl, hL⟩ s₀ hs₀.1
    simp only [Function.comp_apply, NNReal.coe_one, one_mul, Real.dist_eq, zero_sub,
      abs_neg, abs_of_nonneg hs₀.1.1] at this
    exact this
  have hc0 : c₀ ≤ D.1 (P 0, P s₀) := hc₀ _ (h0 ▸ hz) _ (hs₁eq ▸ hgs₁)
  calc ENNReal.ofReal (Real.exp a * c₀)
      ≤ ENNReal.ofReal (Real.exp a) * volume (Icc (0 : ℝ) s₀) := by
        rw [Real.volume_Icc, sub_zero, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
        exact ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_left (hc0.trans hd) (Real.exp_pos _).le)
    _ = ∫⁻ _ in Icc (0 : ℝ) s₀, ENNReal.ofReal (Real.exp a) := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ t in Icc (0 : ℝ) s₀, ENNReal.ofReal (Real.exp (ξ * f (P t))) :=
        setLIntegral_mono' measurableSet_Icc fun t ht =>
          ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (hf _ (hle t ht)))
    _ ≤ ∫⁻ t in Icc (0 : ℝ) Lp, ENNReal.ofReal (Real.exp (ξ * f (P t))) :=
        lintegral_mono_set (Icc_subset_Icc_right hs₀.1.2)

lemma isClosed_leftSide : IsClosed leftSide := by
  have : leftSide = {z : ℂ | z.re = 0} ∩ ({z : ℂ | 0 ≤ z.im} ∩ {z : ℂ | z.im ≤ 1}) := rfl
  rw [this]
  exact (isClosed_eq Complex.continuous_re continuous_const).inter
    ((isClosed_le continuous_const Complex.continuous_im).inter
      (isClosed_le Complex.continuous_im continuous_const))

lemma isCompact_leftSide : IsCompact leftSide :=
  Metric.isCompact_of_isClosed_isBounded isClosed_leftSide
    ((Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 2)).subset fun _ hz =>
      mem_closedBall_zero_iff.2 (norm_le_two_of_mem_leftSide hz))

/-- `c₀ := D(L, {dist(·, L) = 1/4}) > 0` -/
theorem exists_crossing_const (D : ContMetric) : ∃ c₀ : ℝ, 0 < c₀ ∧
    ∀ u ∈ leftSide, ∀ v, Metric.infDist v leftSide = 4⁻¹ → c₀ ≤ D.1 (u, v) := by
  set K := {v : ℂ | Metric.infDist v leftSide = 4⁻¹}
  have hLne : leftSide.Nonempty := ⟨0, zero_mem_leftSide⟩
  have hKc : IsCompact K := by
    refine Metric.isCompact_of_isClosed_isBounded
      (isClosed_eq (Metric.continuous_infDist_pt _) continuous_const)
      ((Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 3)).subset fun v hv => ?_)
    obtain ⟨u, hu, hd⟩ := (Metric.infDist_lt_iff hLne).1
      (show Metric.infDist v leftSide < 1 by rw [hv]; norm_num)
    have := norm_le_two_of_mem_leftSide hu
    rw [mem_closedBall_zero_iff]
    have : ‖v‖ ≤ ‖u‖ + dist v u := by
      rw [dist_eq_norm]; linarith [norm_le_norm_add_norm_sub' v u]
    linarith
  rcases (leftSide ×ˢ K).eq_empty_or_nonempty with he | hne
  · refine ⟨1, one_pos, fun u hu v hv => ?_⟩
    have hmem : (u, v) ∈ leftSide ×ˢ K := ⟨hu, hv⟩
    rw [he] at hmem
    exact absurd hmem (Set.notMem_empty _)
  · obtain ⟨p, hp, hmin⟩ := (isCompact_leftSide.prod hKc).exists_isMinOn hne
      D.1.continuous.continuousOn
    refine ⟨D.1 p, cm_pos_of_ne D ?_ |>.trans_eq' rfl, fun u hu v hv => hmin ⟨hu, hv⟩⟩
    intro hpe
    have h2 : Metric.infDist p.2 leftSide = 0 := by
      rw [← hpe]; exact infDist_eq_zero_of_mem_leftSide hp.1
    have := hp.2
    simp only [K, Set.mem_ofPred_eq] at this
    rw [h2] at this
    norm_num at this

lemma crossFn_mono {f g : ℂ × ℂ → ℝ} (hf : BddBelow (f '' (leftSide ×ˢ rightSide)))
    (hfg : ∀ p ∈ leftSide ×ˢ rightSide, f p ≤ g p) : crossFn f ≤ crossFn g :=
  le_crossFn fun p hp => (crossFn_le hf hp).trans (hfg p hp)

lemma quarter_le_infDist_of_mem_rightSide {w : ℂ} (hw : w ∈ rightSide) :
    4⁻¹ ≤ Metric.infDist w leftSide := by
  refine (Metric.le_infDist ⟨0, zero_mem_leftSide⟩).2 fun u hu => ?_
  have h1 : |w.re - u.re| ≤ dist w u := by
    rw [Complex.dist_eq, ← Complex.sub_re]; exact Complex.abs_re_le_norm _
  rw [hw.1, hu.1] at h1
  norm_num at h1
  linarith

section theta
variable {ξ : ℝ} {f : C(ℂ, ℝ)} {D₀ : ContMetric} {D' : ℝ → ContMetric}

/-- `θ(t) ≤ e^{ξ |t - s| M} θ(s)` for `θ(t) = (e^{ξ t f}·D₀)(L, R)`, `|f| ≤ M`. -/
theorem crossFn_weyl_le (hξ : 0 ≤ ξ) {M : ℝ} (hM : ∀ x, |f x| ≤ M)
    (hW : ∀ t z w, weylScale ξ (t • f) D₀ z w = ENNReal.ofReal ((D' t).1 (z, w))) (s t : ℝ) :
    crossFn (D' t).1 ≤ Real.exp (ξ * |t - s| * M) * crossFn (D' s).1 := by
  rw [← crossFn_smul (Real.exp_pos _).le]
  refine crossFn_mono (bddBelow_crossSet_of_nonneg (cm_nonneg (D' t))) fun p _ => ?_
  have hfx : ∀ x, ξ * (t • f) x ≤ ξ * (s • f) x + ξ * |t - s| * M := fun x => by
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
    have h2 : |t - s| * |f x| ≤ |t - s| * M := mul_le_mul_of_nonneg_left (hM x) (abs_nonneg _)
    have h1 : (t - s) * f x ≤ |t - s| * M := (le_abs_self _).trans (by rw [abs_mul]; exact h2)
    nlinarith [mul_le_mul_of_nonneg_left h1 hξ]
  have h := weylScale_le_exp_mul (D := D₀) hfx p.1 p.2
  rw [Pi.smul_apply, smul_eq_mul]
  rw [hW, hW, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.exp_pos _).le (cm_nonneg _ _))] at h
  exact h

/-- `θ` is continuous. -/
theorem continuous_crossFn_weyl (hξ : 0 ≤ ξ) {M : ℝ} (hM : ∀ x, |f x| ≤ M)
    (hW : ∀ t z w, weylScale ξ (t • f) D₀ z w = ENNReal.ofReal ((D' t).1 (z, w))) :
    Continuous fun t => crossFn (D' t).1 := by
  refine continuous_iff_continuousAt.2 fun s => ?_
  have hlo : Tendsto (fun t => Real.exp (-(ξ * |t - s| * M)) * crossFn (D' s).1) (𝓝 s)
      (𝓝 (crossFn (D' s).1)) := by
    have : Continuous fun t => Real.exp (-(ξ * |t - s| * M)) * crossFn (D' s).1 := by fun_prop
    simpa using this.tendsto s
  have hhi : Tendsto (fun t => Real.exp (ξ * |t - s| * M) * crossFn (D' s).1) (𝓝 s)
      (𝓝 (crossFn (D' s).1)) := by
    have : Continuous fun t => Real.exp (ξ * |t - s| * M) * crossFn (D' s).1 := by fun_prop
    simpa using this.tendsto s
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi (fun t => ?_)
    (fun t => crossFn_weyl_le hξ hM hW s t)
  have := crossFn_weyl_le hξ hM hW t s
  rw [abs_sub_comm] at this
  rw [Real.exp_neg, ← div_eq_inv_mul, div_le_iff₀ (Real.exp_pos _), mul_comm]
  exact this

/-- `θ(t) ≥ e^{ξ t} c₀` for `t ≥ 0` when `f ≥ 1` on the `1/4`-neighbourhood of `L`. -/
theorem exp_mul_le_crossFn_weyl (hf1 : ∀ x, Metric.infDist x leftSide ≤ 4⁻¹ → 1 ≤ f x)
    (hξ : 0 ≤ ξ)
    (hW : ∀ t z w, weylScale ξ (t • f) D₀ z w = ENNReal.ofReal ((D' t).1 (z, w)))
    {c₀ : ℝ} (hc₀ : ∀ u ∈ leftSide, ∀ v, Metric.infDist v leftSide = 4⁻¹ → c₀ ≤ D₀.1 (u, v))
    {t : ℝ} (ht : 0 ≤ t) : Real.exp (ξ * t) * c₀ ≤ crossFn (D' t).1 := by
  refine le_crossFn fun p hp => ?_
  have h := le_weylScale_of_exit (ξ := ξ) (a := ξ * t) (f := t • f) (fun x hx => by
      simp only [ContinuousMap.smul_apply, smul_eq_mul]
      have := hf1 x hx
      nlinarith [mul_nonneg hξ ht]) hc₀ hp.1 (quarter_le_infDist_of_mem_rightSide hp.2)
  rw [hW, ENNReal.ofReal_le_ofReal_iff (cm_nonneg _ _)] at h
  exact h

/-- The IVT step of DEC-A D-A2 (iii): if `θ(0) ≤ a < b`, then `θ(q) ∈ (a, b)` for some rational
`q > 0`. -/
theorem exists_rat_crossFn_weyl_mem (hf1 : ∀ x, Metric.infDist x leftSide ≤ 4⁻¹ → 1 ≤ f x)
    (hξ : 0 < ξ) {M : ℝ} (hM : ∀ x, |f x| ≤ M)
    (hW : ∀ t z w, weylScale ξ (t • f) D₀ z w = ENNReal.ofReal ((D' t).1 (z, w)))
    {a b : ℝ} (hab : a < b) (h0 : crossFn (D' 0).1 ≤ a) :
    ∃ q : ℚ, 0 < q ∧ crossFn (D' q).1 ∈ Ioo a b := by
  set θ := fun t : ℝ => crossFn (D' t).1
  have hθ : Continuous θ := continuous_crossFn_weyl hξ.le hM hW
  obtain ⟨c₀, hc₀, hc⟩ := exists_crossing_const D₀
  -- a time `T > 0` with `θ(T) > b`
  obtain ⟨T, hT0, hTb⟩ : ∃ T : ℝ, 0 < T ∧ b < θ T := by
    have htend : Tendsto (fun t : ℝ => Real.exp (ξ * t) * c₀) atTop atTop :=
      (Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hξ)).atTop_mul_const hc₀
    obtain ⟨T, hT⟩ := ((htend.eventually_gt_atTop b).and (eventually_gt_atTop 0)).exists
    exact ⟨T, hT.2, hT.1.trans_le (exp_mul_le_crossFn_weyl hf1 hξ.le hW hc hT.2.le)⟩
  obtain ⟨s, hs, hθs⟩ := intermediate_value_Icc hT0.le hθ.continuousOn
    (show (a + b) / 2 ∈ Icc (θ 0) (θ T) from ⟨by linarith, by linarith⟩)
  have hs0 : s ≠ 0 := fun h => by rw [h] at hθs; linarith
  have hsT : s ≠ T := fun h => by rw [h] at hθs; linarith
  have hU : IsOpen (Ioo 0 T ∩ θ ⁻¹' Ioo a b) := isOpen_Ioo.inter (isOpen_Ioo.preimage hθ)
  have hsU : s ∈ Ioo 0 T ∩ θ ⁻¹' Ioo a b :=
    ⟨⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), lt_of_le_of_ne hs.2 hsT⟩,
      by simp only [mem_preimage, hθs, mem_Ioo]; constructor <;> linarith⟩
  obtain ⟨q, hq1, hq2⟩ := Rat.denseRange_cast.exists_mem_open hU ⟨s, hsU⟩
  exact ⟨q, by exact_mod_cast hq1.1, hq2⟩

end theta

/-- The probabilistic step of DEC-A D-A2 (iii): a.s. on `{Z ≤ a}` some rational shift lands in
`(a, b)`; if each shifted law charging `(a, b)` forces `Z` to charge `(a, b)` (Cameron–Martin),
then `P[Z ≤ a] > 0` gives `P[a < Z < b] > 0`. -/
theorem measure_Ioo_pos_of_shift {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Z : Ω → ℝ}
    {Zq : ℚ → Ω → ℝ} {a b : ℝ}
    (hpath : ∀ᵐ ω ∂P, Z ω ≤ a → ∃ q : ℚ, 0 < q ∧ Zq q ω ∈ Ioo a b)
    (htr : ∀ q : ℚ, 0 < q → 0 < P {ω | Zq q ω ∈ Ioo a b} → 0 < P {ω | Z ω ∈ Ioo a b})
    (hpos : 0 < P {ω | Z ω ≤ a}) : 0 < P {ω | Z ω ∈ Ioo a b} := by
  by_contra hcon
  have hnull : ∀ q : ℚ, P {ω | 0 < q ∧ Zq q ω ∈ Ioo a b} = 0 := by
    intro q
    by_cases hq : 0 < q
    · by_contra hne
      refine hcon (htr q hq (pos_iff_ne_zero.2 fun h0 => hne ?_))
      exact measure_mono_null (fun ω hω => hω.2) h0
    · exact measure_mono_null (fun ω hω => absurd hω.1 hq) (measure_empty (μ := P))
  have hsub : {ω | Z ω ≤ a} ⊆ {ω | ¬ (Z ω ≤ a → ∃ q : ℚ, 0 < q ∧ Zq q ω ∈ Ioo a b)} ∪
      ⋃ q : ℚ, {ω | 0 < q ∧ Zq q ω ∈ Ioo a b} := by
    intro ω hω
    by_cases h : Z ω ≤ a → ∃ q : ℚ, 0 < q ∧ Zq q ω ∈ Ioo a b
    · obtain ⟨q, hq⟩ := h hω
      exact Or.inr (mem_iUnion.2 ⟨q, hq⟩)
    · exact Or.inl h
  have : P {ω | Z ω ≤ a} = 0 :=
    measure_mono_null hsub (measure_union_null (ae_iff.1 hpath) (measure_iUnion_null hnull))
  exact hpos.ne' this

lemma isCompact_rightSide : IsCompact rightSide := by
  have : rightSide = {z : ℂ | z.re = 1} ∩ ({z : ℂ | 0 ≤ z.im} ∩ {z : ℂ | z.im ≤ 1}) := rfl
  refine Metric.isCompact_of_isClosed_isBounded ?_
    ((Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 2)).subset fun _ hz =>
      mem_closedBall_zero_iff.2 (norm_le_two_of_mem_rightSide hz))
  rw [this]
  exact (isClosed_eq Complex.continuous_re continuous_const).inter
    ((isClosed_le continuous_const Complex.continuous_im).inter
      (isClosed_le Complex.continuous_im continuous_const))

/-- `d ↦ d(L, R)` is continuous on `C(ℂ × ℂ, ℝ)` (compact-open topology). -/
theorem continuous_crossFn : Continuous fun d : C(ℂ × ℂ, ℝ) => crossFn d := by
  set S := leftSide ×ˢ rightSide
  have hS : IsCompact S := isCompact_leftSide.prod isCompact_rightSide
  have : CompactSpace S := isCompact_iff_compactSpace.1 hS
  have : Nonempty S := crossSet_nonempty.to_subtype
  have hΦ : LipschitzWith 1 fun g : C(S, ℝ) => sInf (range g) := by
    refine LipschitzWith.of_dist_le_mul fun f g => ?_
    have hbf : BddBelow (range f) := (isCompact_range f.continuous).bddBelow
    have hbg : BddBelow (range g) := (isCompact_range g.continuous).bddBelow
    rw [NNReal.coe_one, one_mul, Real.dist_eq, abs_sub_le_iff]
    constructor
    · rw [sub_le_comm]
      refine le_csInf (range_nonempty g) ?_
      rintro _ ⟨p, rfl⟩
      have h1 := csInf_le hbf (mem_range_self p)
      have h2 := ContinuousMap.dist_apply_le_dist (f := f) (g := g) p
      rw [Real.dist_eq] at h2
      linarith [le_abs_self (f p - g p)]
    · rw [sub_le_comm]
      refine le_csInf (range_nonempty f) ?_
      rintro _ ⟨p, rfl⟩
      have h1 := csInf_le hbg (mem_range_self p)
      have h2 := ContinuousMap.dist_apply_le_dist (f := f) (g := g) p
      rw [Real.dist_eq] at h2
      linarith [neg_abs_le (f p - g p)]
  have heq : (fun d : C(ℂ × ℂ, ℝ) => crossFn d) =
      (fun g : C(S, ℝ) => sInf (range g)) ∘ fun d => d.restrict S := by
    funext d
    simp only [Function.comp_apply, crossFn, ContinuousMap.coe_restrict, Set.range_domRestrict]
    rfl
  rw [heq]
  exact hΦ.continuous.comp (ContinuousMap.continuous_restrict S)

theorem measurable_crossFn_contMetric : Measurable fun D : ContMetric => crossFn D.1 :=
  (continuous_crossFn.comp continuous_subtype_val).measurable

/-- **GM.S1.18′** (DEC-A D-A2 (iii)): no gap in the law of `D_h(L, R)`. -/
theorem gm_S1_18 : ∀ {γ : ℝ}, 0 < γ → ∀ {D : DistC → ContMetric} {c : ℝ → ℝ},
    IsWeakLQGMetric γ D c →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsNormalizedWPGFF h P → ∀ a b : ℝ, a < b →
    0 < P.map (fun ω => crossFn (D (h ω)).1) (Iic a) →
    0 < P.map (fun ω => crossFn (D (h ω)).1) (Ioo a b) := by
  intro γ hγ D c hD Ω _ P _ h hh a b hab hpos
  have hξ : 0 < xiGamma γ := xiGamma_pos hγ
  have hDm : Measurable fun g => crossFn (D g).1 := measurable_crossFn_contMetric.comp hD.measurable
  have hZm : Measurable fun ω => crossFn (D (h ω)).1 := hDm.comp hh.1.measurable
  rw [Measure.map_apply hZm measurableSet_Iic] at hpos
  rw [Measure.map_apply hZm measurableSet_Ioo]
  obtain ⟨f₀, hf1, hf0⟩ := exists_noGap_test
  obtain ⟨M, hM⟩ : ∃ M, ∀ x, |testCont f₀ x| ≤ M := by
    obtain ⟨C, hC⟩ := (testCont f₀).continuous.bounded_above_of_compact_support
      f₀.hasCompactSupport
    exact ⟨C, fun x => by simpa [Real.norm_eq_abs] using hC x⟩
  have hweyl := hD.weyl P h (isGFFPlusCont_of_normalized hh)
  refine measure_Ioo_pos_of_shift
    (Zq := fun (q : ℚ) ω => crossFn (D (addFun (h ω) ((q : ℝ) • testCont f₀))).1) ?_ ?_ hpos
  · filter_upwards [hweyl] with ω hω hZ
    exact exists_rat_crossFn_weyl_mem (D₀ := D (h ω))
      (D' := fun t => D (addFun (h ω) (t • testCont f₀))) hf1 hξ hM
      (fun t z w => hω (t • testCont f₀) z w) hab (by simpa [addFun_zero_eq] using hZ)
  · intro q _ hq
    by_contra hcon
    have h0 : P (h ⁻¹' {g | crossFn (D g).1 ∈ Ioo a b}) = 0 :=
      nonpos_iff_eq_zero.1 (not_lt.1 hcon)
    have hφ : Real.circleAverage (testCont ((q : ℝ) • f₀)) 0 1 = 0 := by
      have e : (testCont ((q : ℝ) • f₀) : ℂ → ℝ) = fun x => (q : ℝ) • testCont f₀ x := rfl
      rw [e, Real.circleAverage_fun_smul, hf0, smul_zero]
    have := measure_addFun_preimage_eq_zero hh hφ (hDm measurableSet_Ioo) h0
    have e : testCont ((q : ℝ) • f₀) = (q : ℝ) • testCont f₀ := rfl
    rw [e] at this
    exact hq.ne' this

end GM
end LQGMetric
