/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S4.P412iBorel at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S4.P412iSig

/-!
# `σ^ε_{t,𝕣}` as a Borel function of the metric and of the coded events `E_r(z)`

Source: CONF (arXiv:1905.00381, `confluence-final.tex`) (3.13), (3.16), (3.17), l. 1258–1302; used
in GM (arXiv:1905.00383v3) L4.15 Step 4, l. 2189 (D98 (b2), packet P-stop). Measurability input of
the piece method (`aeEventIn_of_saturated`) for `{σ_k ≤ s_{k+1}}` and the hits of `𝓑^•_{σ_k}`.

The events `E_r(z)` enter `σ` only at `r = 2^k ε𝕣`, `z = (ε𝕣/4)(a + ib)`; they are coded by
`e : ℤ × ℤ × ℤ → Bool` (`p412iEe`). For measurable radii `t, s : ContMetric → ℝ` (e.g.
`gmTauB 𝕫 R · c`), on `ContMetric × (ℤ × ℤ × ℤ → Bool)`:

* `p412i_measurable_rho`, `p412i_measurable_RK`: `ρ^n(z)` and `R^ε(𝓑^•_t)` are measurable;
* `p412i_sig_le_iff`, `p412i_sig_lt_iff`: rational characterizations of `σ ≤ s`, `σ < x`;
* **`p412i_measurableSet_sigLe`**: `{σ ≤ s}` is Borel; **`p412i_measurable_sig`**: `σ` is Borel;
* **`p412i_measurableSet_sigHit`**: `{𝓑^•_σ ∩ V ≠ ∅}` is Borel (`V` open).
All by countable operations (dense sequence `denseSeq ℂ`, `gmE_measurableSet_filledBall`,
`gm_filledBall_inter_open_iff`); own routine arguments (DEVIATIONS: none, measurability is implicit
in CONF).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric TopologicalSpace
open scoped ENNReal
open LQGMetric.Blueprint

namespace LQGMetric.GM

/-- the grid point `m(a + ib)` -/
def p412iGP (m : ℝ) (a b : ℤ) : ℂ := ⟨a * m, b * m⟩

/-- the event predicate coded by `e`: `E_r(z)` holds iff `r = 2^k R'`, `z = m(a + ib)`,
`e(k, a, b)` -/
def p412iEe (R' m : ℝ) (e : ℤ × ℤ × ℤ → Bool) (r : ℝ) (z : ℂ) : Prop :=
  ∃ i : ℤ × ℤ × ℤ, r = (2 : ℝ) ^ i.1 * R' ∧ z = p412iGP m i.2.1 i.2.2 ∧ e i = true

theorem p412i_measurableSet_Ee (R' m r : ℝ) (z : ℂ) :
    MeasurableSet {e : ℤ × ℤ × ℤ → Bool | p412iEe R' m e r z} := by
  have e1 : {e : ℤ × ℤ × ℤ → Bool | p412iEe R' m e r z} = ⋃ i : ℤ × ℤ × ℤ,
      {_e : ℤ × ℤ × ℤ → Bool | r = (2 : ℝ) ^ i.1 * R' ∧ z = p412iGP m i.2.1 i.2.2} ∩
        (fun e : ℤ × ℤ × ℤ → Bool => e i) ⁻¹' {true} := by
    ext e; simp only [p412iEe, mem_setOf_eq, mem_iUnion, mem_inter_iff, mem_preimage,
      mem_singleton_iff, and_assoc]
  rw [e1]
  exact MeasurableSet.iUnion fun i => (MeasurableSet.const _).inter
    (measurable_pi_apply i (measurableSet_singleton true))

theorem p412i_measurable_rho (R' m : ℝ) (z : ℂ) (n : ℕ) :
    Measurable fun e : ℤ × ℤ × ℤ → Bool => p412iRho (p412iEe R' m e) R' z n := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    classical
    simp only [p412iRho]
    refine Measurable.iInf fun k => ?_
    have e1 : (fun e : ℤ × ℤ × ℤ → Bool => ⨅ (_ : 6 * p412iRho (p412iEe R' m e) R' z n ≤
        ENNReal.ofReal ((2 : ℝ) ^ k * R')) (_ : p412iEe R' m e ((2 : ℝ) ^ k * R') z),
        ENNReal.ofReal ((2 : ℝ) ^ k * R')) = fun e => if (6 * p412iRho (p412iEe R' m e) R' z n ≤
        ENNReal.ofReal ((2 : ℝ) ^ k * R') ∧ p412iEe R' m e ((2 : ℝ) ^ k * R') z) then
        ENNReal.ofReal ((2 : ℝ) ^ k * R') else ⊤ := by
      funext e
      by_cases h1 : 6 * p412iRho (p412iEe R' m e) R' z n ≤ ENNReal.ofReal ((2 : ℝ) ^ k * R')
      · by_cases h2 : p412iEe R' m e ((2 : ℝ) ^ k * R') z
        · simp only [h1, h2, and_self, if_true, iInf_pos]
        · simp only [h2, and_false, if_false, iInf_neg, not_false_eq_true, iInf_top]
      · simp only [h1, false_and, if_false, iInf_neg, not_false_eq_true]
    rw [e1]
    exact Measurable.ite ((measurableSet_le (measurable_const.mul ih) measurable_const).inter
      (p412i_measurableSet_Ee R' m _ z)) measurable_const measurable_const

/-- `y ∈ 𝓑^•_{t(x)}(f x)` is measurable in `x` -/
theorem p412i_measurableSet_mem {X : Type*} [MeasurableSpace X] {f : X → ContMetric}
    {t : X → ℝ} (hf : Measurable f) (ht : Measurable t) (z₀ y : ℂ) :
    MeasurableSet {x | y ∈ filledBall (f x) z₀ (t x)} :=
  (gmE_measurableSet_filledBall z₀).preimage (hf.prodMk (ht.prodMk measurable_const))

/-- `𝓑^•_{t(x)}(f x) ∩ V ≠ ∅` is measurable in `x` (`V` open) -/
theorem p412i_measurableSet_hit {X : Type*} [MeasurableSpace X] {f : X → ContMetric}
    {t : X → ℝ} (hf : Measurable f) (ht : Measurable t) (z₀ : ℂ) {V : Set ℂ} (hV : IsOpen V) :
    MeasurableSet {x | (filledBall (f x) z₀ (t x) ∩ V).Nonempty} := by
  have e1 : {x | (filledBall (f x) z₀ (t x) ∩ V).Nonempty} =
      ⋃ i, {_x : X | denseSeq ℂ i ∈ V} ∩ {x | denseSeq ℂ i ∈ filledBall (f x) z₀ (t x)} := by
    ext x; simp only [mem_setOf_eq, gm_filledBall_inter_open_iff _ _ _ hV, mem_iUnion,
      mem_inter_iff]
  rw [e1]
  exact MeasurableSet.iUnion fun i => (MeasurableSet.const _).inter
    (p412i_measurableSet_mem hf ht z₀ _)

open Classical in
/-- the supremum over grid points of a set, as a supremum over `ℤ²` -/
theorem p412i_iSup_grid (m : ℝ) (A : Set ℂ) (f : ℂ → ℝ≥0∞) :
    (⨆ z ∈ gridPts m ∩ A, f z) =
      ⨆ (a : ℤ) (b : ℤ), if p412iGP m a b ∈ A then f (p412iGP m a b) else 0 := by
  refine le_antisymm (iSup₂_le fun z hz => ?_) (iSup_le fun a => iSup_le fun b => ?_)
  · obtain ⟨⟨a, b, rfl⟩, hA⟩ := hz
    refine le_iSup_of_le a (le_iSup_of_le b ?_)
    have : p412iGP m a b ∈ A := hA
    simp only [this, if_true]; exact le_rfl
  · split_ifs with hA
    · exact le_iSup₂_of_le (p412iGP m a b) ⟨⟨a, b, rfl⟩, hA⟩ le_rfl
    · exact bot_le

/-- `w ∈ B_δ(𝓑^•_{t(x)}(f x))` is measurable in `x` -/
theorem p412i_measurableSet_thick {X : Type*} [MeasurableSpace X] {f : X → ContMetric}
    {t : X → ℝ} (hf : Measurable f) (ht : Measurable t) (z₀ w : ℂ) (δ : ℝ) :
    MeasurableSet {x | w ∈ thickening δ (filledBall (f x) z₀ (t x))} := by
  have e1 : {x | w ∈ thickening δ (filledBall (f x) z₀ (t x))} =
      {x | (filledBall (f x) z₀ (t x) ∩ ball w δ).Nonempty} := by
    ext x
    simp only [mem_setOf_eq, mem_thickening_iff]
    exact ⟨fun ⟨y, hy, hd⟩ => ⟨y, hy, mem_ball.2 (by rwa [dist_comm])⟩,
      fun ⟨y, hy, hd⟩ => ⟨y, hy, by rw [dist_comm]; exact mem_ball.1 hd⟩⟩
  rw [e1]
  exact p412i_measurableSet_hit hf ht z₀ isOpen_ball

variable (z₀ : ℂ) {t s : ContMetric → ℝ} (ht : Measurable t) (hs : Measurable s) (N : ℕ)
  (R ε : ℝ)

/-- `R^ε(𝓑^•_t)` with coded events -/
abbrev p412iRKc (p : ContMetric × (ℤ × ℤ × ℤ → Bool)) : ℝ≥0∞ :=
  p412iRK (p412iEe (ε * R) (ε * R / 4) p.2) N R ε (filledBall p.1 z₀ (t p.1))

open Classical in
include ht in
theorem p412i_measurable_RK : Measurable (p412iRKc z₀ (t := t) N R ε) := by
  unfold p412iRKc p412iRK
  simp only [p412i_iSup_grid]
  refine (measurable_const.mul (Measurable.iSup fun a => Measurable.iSup fun b => ?_)).add
    measurable_const
  exact Measurable.ite (p412i_measurableSet_thick (f := Prod.fst) (t := fun p => t p.1)
    measurable_fst (ht.comp measurable_fst) z₀ _ _)
    ((p412i_measurable_rho _ _ _ N).comp measurable_snd) measurable_const

/-! ## Rational characterizations of `σ` -/

section Det
variable {d : ContMetric} {E : ℝ → ℂ → Prop}

/-- `{σ ≤ s}` through rational radii (`0 ≤ t ≤ s`) -/
theorem p412i_sig_le_iff {t s : ℝ} (ht0 : 0 ≤ t) (hts : t ≤ s) :
    p412iSig d z₀ E N R ε t ≤ ENNReal.ofReal s ↔ ∀ q : ℚ, s < q →
      enbhd (p412iRK E N R ε (filledBall d z₀ t)) (filledBall d z₀ t) ⊆ filledBall d z₀ q := by
  constructor
  · intro h q hq
    have hlt : p412iSig d z₀ E N R ε t < ENNReal.ofReal q :=
      lt_of_le_of_lt h ((ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hq)
    obtain ⟨s'', _, h2, h3⟩ : ∃ s'', t < s'' ∧ enbhd (p412iRK E N R ε (filledBall d z₀ t))
        (filledBall d z₀ t) ⊆ filledBall d z₀ s'' ∧ ENNReal.ofReal s'' < ENNReal.ofReal q := by
      simpa only [p412iSig, iInf_lt_iff, exists_prop] using hlt
    exact h2.trans (gm_filledBall_mono _ _ (ENNReal.ofReal_lt_ofReal_iff'.1 h3).1.le)
  · intro H
    refine le_of_forall_gt_imp_ge_of_dense fun c hc => ?_
    obtain ⟨q, _, h1, h2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 hc
    have h1' : ENNReal.ofReal s < ENNReal.ofReal q := h1
    have hsq : s < q := (ENNReal.ofReal_lt_ofReal_iff'.1 h1').1
    exact (iInf₂_le_of_le (q : ℝ) (by linarith) (iInf_le _ (H q hsq))).trans h2.le

/-- `{σ < x}` through rational radii -/
theorem p412i_sig_lt_iff {t : ℝ} (x : ℝ≥0∞) :
    p412iSig d z₀ E N R ε t < x ↔ ∃ q : ℚ, t < q ∧ ENNReal.ofReal q < x ∧
      enbhd (p412iRK E N R ε (filledBall d z₀ t)) (filledBall d z₀ t) ⊆ filledBall d z₀ q := by
  constructor
  · intro hlt
    obtain ⟨s'', h1, h2, h3⟩ : ∃ s'', t < s'' ∧ enbhd (p412iRK E N R ε (filledBall d z₀ t))
        (filledBall d z₀ t) ⊆ filledBall d z₀ s'' ∧ ENNReal.ofReal s'' < x := by
      simpa only [p412iSig, iInf_lt_iff, exists_prop] using hlt
    obtain ⟨q, _, hq1, hq2⟩ := ENNReal.lt_iff_exists_rat_btwn.1 h3
    have hq1' : ENNReal.ofReal s'' < ENNReal.ofReal q := hq1
    have hsq : s'' < q := (ENNReal.ofReal_lt_ofReal_iff'.1 hq1').1
    exact ⟨q, h1.trans hsq, hq2, h2.trans (gm_filledBall_mono _ _ hsq.le)⟩
  · rintro ⟨q, h1, h2, h3⟩
    exact lt_of_le_of_lt (iInf₂_le_of_le (q : ℝ) h1 (iInf_le _ h3)) h2

end Det

/-- `B_x(K) ⊆ F` (`F` closed) is read off the dense sequence -/
theorem p412i_enbhd_subset_iff {x : ℝ≥0∞} {K F : Set ℂ} (hF : IsClosed F) :
    enbhd x K ⊆ F ↔ ∀ i, Metric.infEDist (denseSeq ℂ i) K < x → denseSeq ℂ i ∈ F := by
  refine ⟨fun h i hi => h hi, fun H y hy => ?_⟩
  by_contra hyF
  have ho : IsOpen (enbhd x K ∩ Fᶜ) :=
    (isOpen_lt (Metric.continuous_infEDist) continuous_const).inter hF.isOpen_compl
  obtain ⟨i, hi⟩ := (denseRange_denseSeq ℂ).exists_mem_open ho ⟨y, hy, hyF⟩
  exact hi.2 (H i hi.1)

/-- `dist(y, 𝓑^•_t) < c` is read off the dense sequence -/
theorem p412i_infEDist_lt_iff (d : ContMetric) (t : ℝ) (y : ℂ) (c : ℝ≥0∞) :
    Metric.infEDist y (filledBall d z₀ t) < c ↔
      ∃ j, edist y (denseSeq ℂ j) < c ∧ denseSeq ℂ j ∈ filledBall d z₀ t := by
  constructor
  · intro h
    obtain ⟨x, hx, hxy⟩ := Metric.infEDist_lt_iff.1 h
    obtain ⟨j, hj1, hj2⟩ := (gm_filledBall_inter_open_iff d z₀ t Metric.isOpen_eball).1
      ⟨x, hx, Metric.mem_eball'.2 hxy⟩
    exact ⟨j, Metric.mem_eball'.1 hj1, hj2⟩
  · rintro ⟨j, hj1, hj2⟩
    exact lt_of_le_of_lt (Metric.infEDist_le_edist_of_mem hj2) hj1

theorem p412i_setOf_imp {X : Type*} (A B : X → Prop) :
    {x | A x → B x} = {x | A x}ᶜ ∪ {x | B x} := by
  ext x; simp only [mem_setOf_eq, mem_union, mem_compl_iff]; tauto

include ht in
/-- the admissibility of the radius `q` in `σ` is Borel -/
theorem p412i_measurableSet_adm (q : ℝ) :
    MeasurableSet {p : ContMetric × (ℤ × ℤ × ℤ → Bool) |
      enbhd (p412iRKc z₀ (t := t) N R ε p) (filledBall p.1 z₀ (t p.1)) ⊆ filledBall p.1 z₀ q} := by
  have hRK := p412i_measurable_RK z₀ ht N R ε
  simp only [p412i_enbhd_subset_iff (gm_filledBall_isClosed _ _ _), p412i_infEDist_lt_iff,
    setOf_forall]
  refine MeasurableSet.iInter fun i => ?_
  rw [p412i_setOf_imp]
  refine MeasurableSet.union (MeasurableSet.compl ?_) (p412i_measurableSet_mem measurable_fst
    measurable_const z₀ _)
  rw [setOf_exists]
  exact MeasurableSet.iUnion fun j => (measurableSet_lt measurable_const hRK).inter
    (p412i_measurableSet_mem measurable_fst (ht.comp measurable_fst) z₀ _)

include ht hs in
/-- **`{σ ≤ s}` is Borel** in (metric, coded events) -/
theorem p412i_measurableSet_sigLe (ht0 : ∀ d, 0 ≤ t d) (hts : ∀ d, t d ≤ s d) :
    MeasurableSet {p : ContMetric × (ℤ × ℤ × ℤ → Bool) |
      p412iSig p.1 z₀ (p412iEe (ε * R) (ε * R / 4) p.2) N R ε (t p.1) ≤
        ENNReal.ofReal (s p.1)} := by
  have e1 : {p : ContMetric × (ℤ × ℤ × ℤ → Bool) |
      p412iSig p.1 z₀ (p412iEe (ε * R) (ε * R / 4) p.2) N R ε (t p.1) ≤
        ENNReal.ofReal (s p.1)} = ⋂ q : ℚ, {p | s p.1 < q →
      enbhd (p412iRKc z₀ (t := t) N R ε p) (filledBall p.1 z₀ (t p.1)) ⊆
        filledBall p.1 z₀ q} := by
    ext p
    simp only [mem_setOf_eq, mem_iInter]
    exact p412i_sig_le_iff z₀ N R ε (ht0 p.1) (hts p.1)
  rw [e1]
  refine MeasurableSet.iInter fun q => ?_
  rw [p412i_setOf_imp]
  exact (measurableSet_lt (hs.comp measurable_fst) measurable_const).compl.union
    (p412i_measurableSet_adm z₀ ht N R ε q)

include ht in
/-- **`σ` is Borel** in (metric, coded events) -/
theorem p412i_measurable_sig : Measurable fun p : ContMetric × (ℤ × ℤ × ℤ → Bool) =>
    p412iSig p.1 z₀ (p412iEe (ε * R) (ε * R / 4) p.2) N R ε (t p.1) := by
  refine measurable_of_Iio fun x => ?_
  have e1 : (fun p : ContMetric × (ℤ × ℤ × ℤ → Bool) =>
      p412iSig p.1 z₀ (p412iEe (ε * R) (ε * R / 4) p.2) N R ε (t p.1)) ⁻¹' Iio x =
      ⋃ q : ℚ, ({p : ContMetric × (ℤ × ℤ × ℤ → Bool) | t p.1 < q} ∩
        {_p | ENNReal.ofReal q < x}) ∩ {p | enbhd (p412iRKc z₀ (t := t) N R ε p)
          (filledBall p.1 z₀ (t p.1)) ⊆ filledBall p.1 z₀ q} := by
    ext p
    simp only [mem_preimage, mem_Iio, mem_iUnion, mem_inter_iff, mem_setOf_eq, and_assoc]
    exact p412i_sig_lt_iff z₀ N R ε x
  rw [e1]
  exact MeasurableSet.iUnion fun q => ((measurableSet_lt (ht.comp measurable_fst)
    measurable_const).inter (MeasurableSet.const _)).inter (p412i_measurableSet_adm z₀ ht N R ε q)

include ht in
/-- **the hit events of `𝓑^•_σ` are Borel** in (metric, coded events) -/
theorem p412i_measurableSet_sigHit {V : Set ℂ} (hV : IsOpen V) :
    MeasurableSet {p : ContMetric × (ℤ × ℤ × ℤ → Bool) |
      (filledBallE p.1 z₀ (p412iSig p.1 z₀ (p412iEe (ε * R) (ε * R / 4) p.2) N R ε (t p.1)) ∩
        V).Nonempty} := by
  set σ := fun p : ContMetric × (ℤ × ℤ × ℤ → Bool) =>
    p412iSig p.1 z₀ (p412iEe (ε * R) (ε * R / 4) p.2) N R ε (t p.1) with hσdef
  have hσ : Measurable σ := p412i_measurable_sig z₀ ht N R ε
  have e1 : {p | (filledBallE p.1 z₀ (σ p) ∩ V).Nonempty} =
      ({p | σ p = ⊤} ∩ {_p | V.Nonempty}) ∪
        ({p | σ p = ⊤}ᶜ ∩ {p | (filledBall p.1 z₀ (σ p).toReal ∩ V).Nonempty}) := by
    ext p
    by_cases h : σ p = ⊤
    · simp [filledBallE, h]
    · simp [filledBallE, h]
  rw [e1]
  have hT : MeasurableSet {p | σ p = ⊤} := hσ (measurableSet_singleton ⊤)
  exact (hT.inter (MeasurableSet.const _)).union (hT.compl.inter
    (p412i_measurableSet_hit measurable_fst (ENNReal.measurable_toReal.comp hσ) z₀ hV))

end LQGMetric.GM
