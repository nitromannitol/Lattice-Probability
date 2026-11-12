/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.LM.T1_7V1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7L1
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7N1
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7G1
import LatticeProb.Bonanno.LQGMetric.Papers.LM.T1_7G2

/-!
# LM Theorem 1.7, packet P-VAR (b)–(c): the deterministic resampling bound

Gwynne–Miller, *Local metrics of the Gaussian free field* (arXiv:1905.00379,
`local-metrics-final.tex`), proof of Lemma 5.3 (l. 977–981) and Step 2 of the proof of
Theorem 1.7, (5.12)–(5.16) (l. 1038–1055), as repaired by decision D107 (`decisions/DEC-107.md`
§3(ii)–(iii)).

* `t17v_len_eq_of_internal_eq` (LM l. 979–980: "the `D'`-length of every path which is contained
  in some `S` is the same as its `D`-length"): through BBI Prop. 2.3.12(1)
  (`curveLength_eq_iSup_internalEDist`), the length of a curve in `S` only depends on `D(·,·;S)`.
* `t17v_lenMeas_eq_of_internal_eq`: hence `len(P ∩ S; D) = len(P ∩ S; D')` for the length measure
  `t17LenMeas` (P2-LM17b's G2 (iii)).
* `t17v_sum_squares` ((5.2), l. 950–953): when the grid part of `P` is null,
  `len(P; D) = ∑_S len(P ∩ S; D)` over the finitely many squares `t17Box ε R` that can meet `cl B_R`.
* `t17v_resample` ((5.12)–(5.15)): for `D'' ≤ c D` with the same internal metrics on every square
  but `S₀`, the square pieces of `P` agree off `S₀`, the `S₀` piece grows by at most `c`, and both
  lengths are the sums of their pieces (the grid stays null for `D''`, LM l. 973–974).
* `t17v_A_bound` ((5.16), D107 §3(ii)–(iii)): `(D''(z,w;B_m) − D(z,w;B_m))_+ ≤
  len(P; D) − D(z,w;B_m) + (c − 1) len(P ∩ S₀; D)` for every such curve `P ⊂ B_m` from `z` to `w`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric.LM

open MetricGeometry

/-- **LM l. 979–980**: a curve inside `S` has the same length for two metrics with the same
internal metric on `S` (BBI Prop. 2.3.12(1)). -/
theorem t17v_len_eq_of_internal_eq {d₁ d₂ : ContMetric} {S : Set ℂ}
    (hS : ∀ u ∈ S, ∀ v ∈ S, d₁.internal S u v = d₂.internal S u v)
    {P : ℝ → ℂ} {x y : ℝ} (hP : ContinuousOn P (Icc x y)) (hPS : MapsTo P (Icc x y) S) :
    d₁.len P x y = d₂.len P x y := by
  have h1 := curveLength_eq_iSup_internalEDist (X := d₁.Space) (Y := d₁.pt '' S)
    (P := d₁.pt ∘ P) (d₁.continuous_pt.comp_continuousOn hP) (fun t ht => ⟨P t, hPS ht, rfl⟩)
  have h2 := curveLength_eq_iSup_internalEDist (X := d₂.Space) (Y := d₂.pt '' S)
    (P := d₂.pt ∘ P) (d₂.continuous_pt.comp_continuousOn hP) (fun t ht => ⟨P t, hPS ht, rfl⟩)
  unfold ContMetric.len
  rw [h1, h2]
  exact iSup_congr fun p => Finset.sum_congr rfl fun i _ =>
    hS _ (hPS (p.2.2.2 _)) _ (hPS (p.2.2.2 _))

/-- the length measure has no atoms -/
lemma t17v_lenMeas_singleton {M : Type*} [PseudoEMetricSpace M] (g : ℝ → M) (a b t : ℝ) :
    t17LenMeas g a b {t} = 0 := by
  by_cases h : T17Curve g a b
  · rw [t17LenMeas_eq h, StieltjesFunction.measure_singleton,
      ((t17LenSF_continuous h).continuousAt.continuousWithinAt).leftLim_eq, sub_self,
      ENNReal.ofReal_zero]
  · simp [t17LenMeas, h]

/-- **`len(P ∩ S; D) = len(P ∩ S; D')`** when `D(·,·;S) = D'(·,·;S)` (`S` open) -/
theorem t17v_lenMeas_eq_of_internal_eq {d₁ d₂ : ContMetric} {S : Set ℂ} (hSo : IsOpen S)
    (hS : ∀ u ∈ S, ∀ v ∈ S, d₁.internal S u v = d₂.internal S u v)
    {P : ℝ → ℂ} {a b : ℝ} (hP : ContinuousOn P (Icc a b))
    (h₁ : T17Curve (d₁.pt ∘ P) a b) (h₂ : T17Curve (d₂.pt ∘ P) a b) :
    t17LenMeas (d₁.pt ∘ P) a b (Icc a b ∩ P ⁻¹' S) =
      t17LenMeas (d₂.pt ∘ P) a b (Icc a b ∩ P ⁻¹' S) := by
  set O := Ioo a b ∩ P ⁻¹' S with hOdef
  have hO : IsOpen O := (hP.mono Ioo_subset_Icc_self).isOpen_inter_preimage isOpen_Ioo hSo
  have heq := t17LenMeas_eq_on_open h₁ h₂ hO inter_subset_left fun x y _ hsub =>
    t17v_len_eq_of_internal_eq hS
      (hP.mono (hsub.trans (inter_subset_left.trans Ioo_subset_Icc_self)))
      (fun t ht => (hsub ht).2)
  have key : ∀ μ : Measure ℝ, μ {a} = 0 → μ {b} = 0 → μ (Icc a b ∩ P ⁻¹' S) = μ O := by
    intro μ ha hb
    refine le_antisymm ?_ (measure_mono (inter_subset_inter_left _ Ioo_subset_Icc_self))
    have hsub : Icc a b ∩ P ⁻¹' S ⊆ O ∪ ({a} ∪ {b}) := by
      rintro t ⟨⟨h1, h2⟩, h3⟩
      rcases h1.lt_or_eq with h1 | h1
      · rcases h2.lt_or_eq with h2 | h2
        · exact Or.inl ⟨⟨h1, h2⟩, h3⟩
        · exact Or.inr (Or.inr h2)
      · exact Or.inr (Or.inl h1.symm)
    calc μ (Icc a b ∩ P ⁻¹' S) ≤ μ (O ∪ ({a} ∪ {b})) := measure_mono hsub
      _ ≤ μ O + μ ({a} ∪ {b}) := measure_union_le _ _
      _ ≤ μ O + (μ {a} + μ {b}) := add_le_add le_rfl (measure_union_le _ _)
      _ = μ O := by rw [ha, hb, add_zero, add_zero]
  rw [key _ (t17v_lenMeas_singleton _ _ _ _) (t17v_lenMeas_singleton _ _ _ _),
    key _ (t17v_lenMeas_singleton _ _ _ _) (t17v_lenMeas_singleton _ _ _ _), heq]

/-- the squares that can meet `cl B_R(0)` when `θ ∈ [0,1]²` -/
def t17Box (ε R : ℝ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-(⌈R / ε⌉ + 1)) (⌈R / ε⌉ + 1) ×ˢ Finset.Icc (-(⌈R / ε⌉ + 1)) (⌈R / ε⌉ + 1)

/-- **(5.2)** (LM l. 950–953) for any measure on the time axis: if the grid part of the curve is
null, the measure of `[a, b]` is the sum over the squares. -/
theorem t17v_sum_squares (μ : Measure ℝ) {ε R : ℝ} (hε : 0 < ε) {θ : ℝ × ℝ}
    (hθ1 : θ.1 ∈ Icc (0 : ℝ) 1) (hθ2 : θ.2 ∈ Icc (0 : ℝ) 1) {P : ℝ → ℂ} (hP : Continuous P)
    {a b : ℝ} (hPR : MapsTo P (Icc a b) (Metric.closedBall 0 R))
    (hnull : μ (Icc a b ∩ P ⁻¹' t17Grid ε θ) = 0) :
    μ (Icc a b) = ∑ k ∈ t17Box ε R, μ (Icc a b ∩ P ⁻¹' t17Square ε θ k) :=
  t17_sum_pieces measurableSet_Icc hP.measurable (t17Box ε R) (t17Square ε θ)
    (fun k => (t17_isOpen_square ε θ k).measurableSet)
    (fun k _ l _ hkl => t17Square_disjoint hε θ hkl)
    (fun t ht hg => ⟨t17Idx ε θ (P t), t17_idx_mem hε hθ1 hθ2 (by simpa using hPR ht),
      t17_mem_square hε θ hg⟩) hnull

/-- `len(P ∩ S_k; D)` as a real number -/
def t17Piece (d : ContMetric) (P : ℝ → ℂ) (a b ε : ℝ) (θ : ℝ × ℝ) (k : ℤ × ℤ) : ℝ :=
  (t17LenMeas (d.pt ∘ P) a b (Icc a b ∩ P ⁻¹' t17Square ε θ k)).toReal

lemma t17v_edist_le {d d'' : ContMetric} {c : ℝ} (hc : 0 ≤ c)
    (hle : ∀ x y : ℂ, d''.1 (x, y) ≤ c * d.1 (x, y)) (x y : ℂ) :
    edist (d''.pt x) (d''.pt y) ≤ ENNReal.ofReal c * edist (d.pt x) (d.pt y) := by
  rw [ContMetric.edist_pt, ContMetric.edist_pt, ← ENNReal.ofReal_mul hc]
  exact ENNReal.ofReal_le_ofReal (hle x y)

/-- the curve stays a finite-length curve for `D'' ≤ c D` -/
lemma t17v_curve_of_le {d d'' : ContMetric} {c : ℝ} (hc : 0 ≤ c)
    (hle : ∀ x y : ℂ, d''.1 (x, y) ≤ c * d.1 (x, y)) {P : ℝ → ℂ} {a b : ℝ}
    (h : T17Curve (d.pt ∘ P) a b) (hP : ContinuousOn P (Icc a b)) :
    T17Curve (d''.pt ∘ P) a b ∧ d''.len P a b ≤ ENNReal.ofReal c * d.len P a b := by
  have hv : eVariationOn (d''.pt ∘ P) (Icc a b) ≤ ENNReal.ofReal c * eVariationOn (d.pt ∘ P) (Icc a b) :=
    t17_eVariationOn_le_mul fun x _ y _ => t17v_edist_le hc hle (P x) (P y)
  exact ⟨⟨h.1, d''.continuous_pt.comp_continuousOn hP,
    ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h.2.2) hv⟩, hv⟩

/-- **(5.12)–(5.15)**: the square pieces of `P` under `D` and under a resampled `D'' ≤ c D` with the
same internal metrics on all squares but `S_{k₀}`. -/
theorem t17v_resample {d d'' : ContMetric} {c : ℝ} (hc : 0 ≤ c)
    (hle : ∀ x y : ℂ, d''.1 (x, y) ≤ c * d.1 (x, y)) {ε R : ℝ} (hε : 0 < ε) {θ : ℝ × ℝ}
    (hθ1 : θ.1 ∈ Icc (0 : ℝ) 1) (hθ2 : θ.2 ∈ Icc (0 : ℝ) 1) {P : ℝ → ℂ} (hP : Continuous P)
    {a b : ℝ} (hab : a ≤ b) (hfin : d.len P a b ≠ ⊤)
    (hPR : MapsTo P (Icc a b) (Metric.closedBall 0 R))
    (hnull : t17LenMeas (d.pt ∘ P) a b (Icc a b ∩ P ⁻¹' t17Grid ε θ) = 0) {k₀ : ℤ × ℤ}
    (hS : ∀ k ∈ t17Box ε R, k ≠ k₀ → ∀ u ∈ t17Square ε θ k, ∀ v ∈ t17Square ε θ k,
      d.internal (t17Square ε θ k) u v = d''.internal (t17Square ε θ k) u v) :
    (∀ k ∈ t17Box ε R, k ≠ k₀ → t17Piece d'' P a b ε θ k = t17Piece d P a b ε θ k) ∧
      t17Piece d'' P a b ε θ k₀ ≤ c * t17Piece d P a b ε θ k₀ ∧
      (d''.len P a b).toReal = ∑ k ∈ t17Box ε R, t17Piece d'' P a b ε θ k ∧
      (d.len P a b).toReal = ∑ k ∈ t17Box ε R, t17Piece d P a b ε θ k ∧
      d''.len P a b ≠ ⊤ := by
  have hPc : ContinuousOn P (Icc a b) := hP.continuousOn
  have h : T17Curve (d.pt ∘ P) a b := ⟨hab, d.continuous_pt.comp_continuousOn hPc, hfin⟩
  obtain ⟨h'', hlen''⟩ := t17v_curve_of_le hc hle h hPc
  have hsm : t17LenMeas (d''.pt ∘ P) a b ≤ (Real.toNNReal c) • t17LenMeas (d.pt ∘ P) a b :=
    t17LenMeas_le_smul h h'' _ fun x _ y _ => t17v_edist_le hc hle (P x) (P y)
  have hnull'' : t17LenMeas (d''.pt ∘ P) a b (Icc a b ∩ P ⁻¹' t17Grid ε θ) = 0 := by
    refine le_antisymm ((hsm _).trans ?_) zero_le
    rw [Measure.smul_apply, hnull, smul_zero]
  have hfin'' : ∀ k, t17LenMeas (d''.pt ∘ P) a b (Icc a b ∩ P ⁻¹' t17Square ε θ k) ≠ ⊤ :=
    fun k => ne_top_of_le_ne_top h''.2.2 ((measure_mono inter_subset_left).trans
      (t17LenMeas_Icc h'').le)
  have hfin' : ∀ k, t17LenMeas (d.pt ∘ P) a b (Icc a b ∩ P ⁻¹' t17Square ε θ k) ≠ ⊤ :=
    fun k => ne_top_of_le_ne_top h.2.2 ((measure_mono inter_subset_left).trans
      (t17LenMeas_Icc h).le)
  have hsum : ∀ (e : ContMetric), T17Curve (e.pt ∘ P) a b →
      (∀ k, t17LenMeas (e.pt ∘ P) a b (Icc a b ∩ P ⁻¹' t17Square ε θ k) ≠ ⊤) →
      t17LenMeas (e.pt ∘ P) a b (Icc a b ∩ P ⁻¹' t17Grid ε θ) = 0 →
      (e.len P a b).toReal = ∑ k ∈ t17Box ε R, t17Piece e P a b ε θ k := by
    intro e he hfe hne
    have := t17v_sum_squares (t17LenMeas (e.pt ∘ P) a b) hε hθ1 hθ2 hP hPR hne
    rw [t17LenMeas_Icc he] at this
    unfold ContMetric.len curveLength t17Piece
    rw [this, ENNReal.toReal_sum fun k _ => hfe k]
  refine ⟨fun k hk hk0 => ?_, ?_, hsum d'' h'' hfin'' hnull'', hsum d h hfin' hnull,
    h''.2.2⟩
  · unfold t17Piece
    rw [t17v_lenMeas_eq_of_internal_eq (t17_isOpen_square ε θ k) (hS k hk hk0) hPc h h'']
  · unfold t17Piece
    have h1 := hsm (Icc a b ∩ P ⁻¹' t17Square ε θ k₀)
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h1
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top (hfin' k₀)) h1
    rwa [ENNReal.toReal_mul, ENNReal.coe_toReal, Real.coe_toNNReal _ hc] at h2

/-- **(5.16)** (LM l. 1046–1055; D107 §3(ii)–(iii)): for any metric `D`, a resampled
`D'' ≤ c D` agreeing with `D` on every square but `S_{k₀}`, and any curve `P ⊂ B_m(0) ∩ cl B_R(0)`
from `z` to `w` of finite `D`-length whose grid part is null:
`(D''(z,w;B_m) − D(z,w;B_m))_+ ≤ len(P;D) − D(z,w;B_m) + (c − 1) len(P ∩ S_{k₀}; D)`. -/
theorem t17v_A_bound {d d'' : ContMetric} {c : ℝ} (hc1 : 1 ≤ c)
    (hle : ∀ x y : ℂ, d''.1 (x, y) ≤ c * d.1 (x, y)) {ε R : ℝ} (hε : 0 < ε) {θ : ℝ × ℝ}
    (hθ1 : θ.1 ∈ Icc (0 : ℝ) 1) (hθ2 : θ.2 ∈ Icc (0 : ℝ) 1) {P : ℝ → ℂ} (hP : Continuous P)
    {a b : ℝ} (hab : a ≤ b) (hfin : d.len P a b ≠ ⊤)
    (hPR : MapsTo P (Icc a b) (Metric.closedBall 0 R)) {m : ℕ} {z w : ℂ}
    (hPm : MapsTo P (Icc a b) (Metric.ball 0 (m : ℝ))) (hPa : P a = z) (hPb : P b = w)
    (hnull : t17LenMeas (d.pt ∘ P) a b (Icc a b ∩ P ⁻¹' t17Grid ε θ) = 0) {k₀ : ℤ × ℤ}
    (hk₀ : k₀ ∈ t17Box ε R)
    (hS : ∀ k ∈ t17Box ε R, k ≠ k₀ → ∀ u ∈ t17Square ε θ k, ∀ v ∈ t17Square ε θ k,
      d.internal (t17Square ε θ k) u v = d''.internal (t17Square ε θ k) u v) :
    max ((t17F m z w d'').toReal - (t17F m z w d).toReal) 0 ≤
      (d.len P a b).toReal - (t17F m z w d).toReal + (c - 1) * t17Piece d P a b ε θ k₀ := by
  have hc : (0 : ℝ) ≤ c := zero_le_one.trans hc1
  obtain ⟨hne, hk, hs'', hs, hfin''⟩ :=
    t17v_resample hc hle hε hθ1 hθ2 hP hab hfin hPR hnull hS
  -- `D(z,w;B_m) ≤ len(P; D)` for any metric, through `chainInf ≤ internal ≤ len`
  have hint : ∀ e : ContMetric, t17F m z w e ≤ e.len P a b := by
    intro e
    refine (e.chainInf_le_internal Metric.isOpen_ball z w).trans ?_
    have := internalEDist_le_curveLength (X := e.Space) (Y := e.pt '' Metric.ball 0 (m : ℝ))
      (P := e.pt ∘ P) hab (e.continuous_pt.comp_continuousOn hP.continuousOn)
      (fun t ht => ⟨P t, hPm ht, rfl⟩)
    rw [← hPa, ← hPb]
    exact this
  have hF : (t17F m z w d).toReal ≤ (d.len P a b).toReal := ENNReal.toReal_mono hfin (hint d)
  have hF'' : (t17F m z w d'').toReal ≤ (d''.len P a b).toReal :=
    ENNReal.toReal_mono hfin'' (hint d'')
  have hℓ : 0 ≤ t17Piece d P a b ε θ k₀ := ENNReal.toReal_nonneg
  have := t17_A_le_b (t17Box ε R) hk₀ (t17Piece d P a b ε θ) (t17Piece d'' P a b ε θ)
    (c := c) (DS := (t17F m z w d'').toReal) (F := (t17F m z w d).toReal)
    (G := (d.len P a b).toReal) (e := 0) hne hk (hF''.trans_eq hs'') (by rw [hs, add_zero])
    (by nlinarith)
  simpa only [add_zero] using this

end LQGMetric.LM
