/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53Y3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53Q1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53M1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5Geom

/-!
# DZZ Lemma 5.3 part 1, R1: the near-diagonal cut-off and `P[bad_𝖡 ∣ A₀] ≤ C₁ K⁻²`
(P2-DZZ53Y, packet P-131F)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2495–2502 (the Tonelli bound for
(eq-z-open)), with the cut-off DV-D131-3 of decision D131: pairs `z, z' ∈ ∂𝖡` with
`|z − z'| < r` (DZZ's `r = s_𝖡 K⁻⁵`) are declared far; DZZ tacitly use `|z − z'| ≍ s_𝖡/K`
(l. 2474, 2533).

* `l53FarQ'`, `l53ZBadQ'`: the far relation and bad event with the cut-off; `l53ZBadQ_subset'`.
* `l53_near_le`: `μH¹(∂𝕍_{c,t} ∩ B(z, r)) ≤ 8 r`; `l53_frontier_ge`: `t ≤ μH¹(∂𝕍_{c,t})`.
* **`l53ZBadQ'_le`**: Tonelli (copy of `l53ZBadQ_le`, S5L53Q1, through `l53_far_count`) with the
  per-pair bound only for `|z − z'| ≥ r`: `(a − N) b μ(bad') ≤ p μH¹(Bd)²`.
* **`l53_bad_cond_le`**: in the mass-map form of S5L53Q1–Q2 (`l53ZBadQ`, `a = b = K⁻¹ μH¹(∂𝖡)`):
  if `16 r ≤ K⁻¹ t` and the far probability is `≤ p` for the pairs at distance `≥ r`, then
  `P[bad_𝖡 ∣ A₀] ≤ 2 p K²` (for `p = 2K⁻⁴` from `l53_far_bound`, S5L53Y2: `≤ 4 K⁻²`).
  DZZ's `r = t K⁻⁴` satisfies `16 r ≤ K⁻¹ t` once `K ≥ 16^{1/3}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise GMCIdent

variable {Ω : Type*}

/-- **DV-D131-3**: the far relation with the near-diagonal pairs `|z − z'| < r` declared far -/
def l53FarQ' (M : Ω → ℚ × ℚ → ℚ → ℝ≥0∞) (δ T r : ℝ) (ω : Ω) (z z' : ℂ) : Prop :=
  l53FarQ M δ T ω z z' ∨ dist z z' < r

/-- the bad event of (eq-z-open) for `l53FarQ'` -/
def l53ZBadQ' (M : Ω → ℚ × ℚ → ℚ → ℝ≥0∞) (δ T r : ℝ) (Bd : Set ℂ) (a b : ℝ≥0∞) : Set Ω :=
  {ω | b ≤ ((μH[1] : Measure ℂ).restrict Bd)
    {z | a ≤ ((μH[1] : Measure ℂ).restrict Bd) {z' | l53FarQ' M δ T r ω z z'}}}

lemma l53ZBadQ_subset' (M : Ω → ℚ × ℚ → ℚ → ℝ≥0∞) (δ T r : ℝ) (Bd : Set ℂ) (a b : ℝ≥0∞) :
    l53ZBadQ M δ T Bd a b ⊆ l53ZBadQ' M δ T r Bd a b := by
  intro ω hω
  refine le_trans hω (measure_mono fun z hz => le_trans hz (measure_mono fun z' hz' => ?_))
  exact Or.inl hz'

/-! ### Geometry of `∂𝕍_{c,t}` -/

lemma l53_abs_re_sub_le (z z' : ℂ) : |z'.re - z.re| ≤ dist z z' := by
  rw [dist_comm, dist_eq_norm, ← Complex.sub_re]; exact Complex.abs_re_le_norm _

lemma l53_abs_im_sub_le (z z' : ℂ) : |z'.im - z.im| ≤ dist z z' := by
  rw [dist_comm, dist_eq_norm, ← Complex.sub_im]; exact Complex.abs_im_le_norm _

/-- `μH¹(∂𝕍_{c,t} ∩ B(z, r)) ≤ 8 r` -/
lemma l53_near_le (c : ℂ) {t : ℝ} (ht : 0 < t) (z : ℂ) (r : ℝ) :
    μH[1] (frontier (sqBox c t) ∩ {z' | dist z z' < r}) ≤ 8 * ENNReal.ofReal r := by
  have hsub : frontier (sqBox c t) ∩ {z' | dist z z' < r} ⊆
      ({z' : ℂ | z'.im = c.im - t / 2 ∧ z.re - r ≤ z'.re ∧ z'.re ≤ z.re + r} ∪
        {z' : ℂ | z'.re = c.re - t / 2 ∧ z.im - r ≤ z'.im ∧ z'.im ≤ z.im + r}) ∪
      ({z' : ℂ | z'.im = c.im + t / 2 ∧ z.re - r ≤ z'.re ∧ z'.re ≤ z.re + r} ∪
        {z' : ℂ | z'.re = c.re + t / 2 ∧ z.im - r ≤ z'.im ∧ z'.im ≤ z.im + r}) := by
    rintro z' ⟨hz', hd⟩
    rw [frontier_sqBox ht] at hz'
    have h1 := l53_abs_re_sub_le z z'
    have h2 := l53_abs_im_sub_le z z'
    simp only [mem_ofPred_eq] at hd
    rw [abs_le] at h1 h2
    simp only [mem_union, Complex.mem_reProdIm, mem_singleton_iff] at hz'
    rcases hz' with ((⟨-, h⟩ | ⟨h, -⟩) | ⟨-, h⟩) | ⟨h, -⟩
    · exact Or.inl (Or.inl ⟨h, by linarith, by linarith⟩)
    · exact Or.inl (Or.inr ⟨h, by linarith, by linarith⟩)
    · exact Or.inr (Or.inl ⟨h, by linarith, by linarith⟩)
    · exact Or.inr (Or.inr ⟨h, by linarith, by linarith⟩)
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  refine (add_le_add (measure_union_le _ _) (measure_union_le _ _)).trans (le_of_eq ?_)
  rw [l53M_hline_eq, l53M_vline_eq, l53M_hline_eq, l53M_vline_eq]
  rcases le_total r 0 with hr | hr
  · simp [ENNReal.ofReal_of_nonpos hr]
    try linarith
  · rw [show z.re + r - (z.re - r) = 2 * r by ring, show z.im + r - (z.im - r) = 2 * r by ring,
      ENNReal.ofReal_mul (by norm_num)]
    simp only [ENNReal.ofReal_ofNat]
    ring

/-- `t ≤ μH¹(∂𝕍_{c,t})` (the bottom side) -/
lemma l53_frontier_ge (c : ℂ) {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal t ≤ μH[1] (frontier (sqBox c t)) := by
  have hsub : {z' : ℂ | z'.im = c.im - t / 2 ∧ c.re - t / 2 ≤ z'.re ∧ z'.re ≤ c.re + t / 2} ⊆
      frontier (sqBox c t) := by
    rintro z' ⟨h1, h2, h3⟩
    rw [frontier_sqBox ht]
    exact Or.inl (Or.inl (Or.inl ⟨⟨h2, h3⟩, h1⟩))
  refine le_trans (le_of_eq ?_) (measure_mono hsub)
  rw [l53M_hline_eq]; congr 1; ring

/-! ### Tonelli with the cut-off -/

variable [MeasurableSpace Ω]

/-- **The bad-event bound with the cut-off** (DZZ l. 2495–2500 with DV-D131-3; copy of
`l53ZBadQ_le`, S5L53Q1): the per-pair bound is needed only for `|z − z'| ≥ r`, at the price of
`N ≥ μH¹(Bd ∩ B(z, r))` in `a`. -/
theorem l53ZBadQ'_le (μ : Measure Ω) [SFinite μ] {M : Ω → ℚ × ℚ → ℚ → ℝ≥0∞}
    (hM : ∀ (c : ℚ × ℚ) (q : ℚ), Measurable fun ω => M ω c q) (δ T : ℝ)
    {Bd : Set ℂ} (hBm : MeasurableSet Bd) (hBd : μH[1] Bd ≠ ⊤) {r : ℝ} {N : ℝ≥0∞}
    (hN : ∀ z, μH[1] (Bd ∩ {z' | dist z z' < r}) ≤ N) {p : ℝ≥0∞}
    (hp : ∀ z ∈ Bd, ∀ z' ∈ Bd, r ≤ dist z z' → μ {ω | l53FarQ M δ T ω z z'} ≤ p)
    (a b : ℝ≥0∞) :
    (a - N) * b * μ (l53ZBadQ' M δ T r Bd a b) ≤ p * μH[1] Bd ^ 2 := by
  set m : Measure ℂ := (μH[1] : Measure ℂ).restrict Bd with hm
  have : IsFiniteMeasure m := ⟨by rw [hm, Measure.restrict_apply_univ]; exact hBd.lt_top⟩
  set S : Set ((Ω × ℂ) × ℂ) := {q | q.1.2 ∈ Bd ∧ q.2 ∈ Bd ∧ l53FarQ M δ T q.1.1 q.1.2 q.2 ∧
    r ≤ dist q.1.2 q.2} with hS
  have hdm : MeasurableSet {q : (Ω × ℂ) × ℂ | r ≤ dist q.1.2 q.2} :=
    measurableSet_le measurable_const (by fun_prop)
  have hSm : MeasurableSet S :=
    (measurable_fst.snd hBm).inter ((measurable_snd hBm).inter
      ((measurableSet_l53FarQ hM δ T).inter hdm))
  have hp' : ∀ z z', μ {ω | ((ω, z), z') ∈ S} ≤ p := by
    intro z z'
    by_cases hz : z ∈ Bd
    · by_cases hz' : z' ∈ Bd
      · by_cases hd : r ≤ dist z z'
        · exact le_trans (measure_mono fun ω hω => hω.2.2.1) (hp z hz z' hz' hd)
        · have : {ω | ((ω, z), z') ∈ S} = ∅ := by ext ω; simp [hS, hd]
          rw [this, measure_empty]; exact zero_le
      · have : {ω | ((ω, z), z') ∈ S} = ∅ := by ext ω; simp [hS, hz']
        rw [this, measure_empty]; exact zero_le
    · have : {ω | ((ω, z), z') ∈ S} = ∅ := by ext ω; simp [hS, hz]
      rw [this, measure_empty]; exact zero_le
  have hcount := l53_far_count μ m hSm hp' (a - N) b
  rw [hm, Measure.restrict_apply_univ] at hcount
  refine le_trans (mul_le_mul_of_nonneg_left (measure_mono fun ω hω => ?_) zero_le) hcount
  -- `ω ∈ bad'` ⇒ `ω ∈` the counting event at `a − N`
  simp only [l53ZBadQ', mem_ofPred_eq] at hω ⊢
  refine le_trans hω ?_
  rw [Measure.restrict_apply' hBm, Measure.restrict_apply' hBm]
  refine measure_mono fun z hz => ⟨?_, hz.2⟩
  obtain ⟨hz1, hzB⟩ := hz
  simp only [mem_ofPred_eq] at hz1 ⊢
  rw [Measure.restrict_apply' hBm] at hz1
  rw [tsub_le_iff_right]
  refine le_trans hz1 ?_
  have hsub : {z' | l53FarQ' M δ T r ω z z'} ∩ Bd ⊆
      {z' | ((ω, z), z') ∈ S} ∪ (Bd ∩ {z' | dist z z' < r}) := by
    rintro z' ⟨hf, hz'B⟩
    by_cases hd : r ≤ dist z z'
    · rcases hf with hf | hf
      · exact Or.inl ⟨hzB, hz'B, hf, hd⟩
      · exact absurd hf (not_lt.2 hd)
    · exact Or.inr ⟨hz'B, not_le.1 hd⟩
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans (add_le_add ?_ (hN z)))
  rw [Measure.restrict_apply' hBm]
  exact measure_mono fun z' hz' => ⟨hz', hz'.2.1⟩

variable {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **`P[bad_𝖡 ∣ A₀] ≤ 2 p K²`** (DZZ l. 2495–2502, (eq-z-open) part 2, with the cut-off
DV-D131-3), in the mass-map form of S5L53Q1–Q2: `Bd = ∂𝕍_{c,t}`, `a = b = K⁻¹ μH¹(Bd)`, the
mass map local to a white-noise region `R` disjoint from the conditioning region `R₀`. -/
theorem l53_bad_cond_le (hW : IsWhiteNoise P W) {R₀ R : Set (ℝ × ℂ)} (hR₀ : Disjoint R₀ R)
    {A₀ : Set Ω} (hA₀ : MeasurableSet[wnSigma W R₀] A₀) (h0 : P A₀ ≠ 0)
    {M : Ω → ℚ × ℚ → ℚ → ℝ≥0∞}
    (hloc : ∀ (c : ℚ × ℚ) (q : ℚ), Measurable[wnSigma W R] fun ω => M ω c q) (δ T : ℝ)
    (c : ℂ) {t : ℝ} (ht : 0 < t) {K : ℝ≥0∞} (hK0 : K ≠ 0) (hKt : K ≠ ⊤) {r : ℝ}
    (hrK : 16 * ENNReal.ofReal r ≤ K⁻¹ * ENNReal.ofReal t) {p : ℝ≥0∞}
    (hp : ∀ z ∈ frontier (sqBox c t), ∀ z' ∈ frontier (sqBox c t), r ≤ dist z z' →
      P {ω | l53FarQ M δ T ω z z'} ≤ p) :
    P[l53ZBadQ M δ T (frontier (sqBox c t)) (K⁻¹ * μH[1] (frontier (sqBox c t)))
      (K⁻¹ * μH[1] (frontier (sqBox c t))) | A₀] ≤ 2 * p * K ^ 2 := by
  have := hW.isProbabilityMeasure
  set Bd := frontier (sqBox c t) with hBdd
  have hBm : MeasurableSet Bd := isClosed_frontier.measurableSet
  have hBd : μH[1] Bd ≠ ⊤ := by
    have hsub : Bd ⊆ Bd ∩ {z' | dist c z' < 2 * t} := by
      intro z' hz'
      refine ⟨hz', ?_⟩
      have hz'' := (isClosed_sqBox c t).frontier_subset hz'
      simp only [sqBox, mem_ofPred_eq] at hz''
      simp only [mem_ofPred_eq]
      rw [dist_comm, dist_eq_norm]
      calc ‖z' - c‖ ≤ |(z' - c).re| + |(z' - c).im| := Complex.norm_le_abs_re_add_abs_im _
        _ ≤ t / 2 + t / 2 := by
          rw [Complex.sub_re, Complex.sub_im]; linarith [hz''.1, hz''.2]
        _ < 2 * t := by linarith
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top)
      ((measure_mono hsub).trans (l53_near_le c ht c (2 * t)))
  have hm0 : μH[1] Bd ≠ 0 :=
    (lt_of_lt_of_le (ENNReal.ofReal_pos.2 ht) (l53_frontier_ge c ht)).ne'
  have hmeas : MeasurableSet[wnSigma W R] (l53ZBadQ M δ T Bd (K⁻¹ * μH[1] Bd) (K⁻¹ * μH[1] Bd)) :=
    @measurableSet_l53ZBadQ Ω (wnSigma W R) M hloc δ T Bd hBd _ _
  rw [l53_cond_eq hW hR₀ hA₀ h0 hmeas]
  have hloc' : ∀ (c : ℚ × ℚ) (q : ℚ), Measurable fun ω => M ω c q :=
    fun c q => (hloc c q).mono (wnSigma_le hW R) le_rfl
  set a : ℝ≥0∞ := K⁻¹ * μH[1] Bd
  have hN : ∀ z, μH[1] (Bd ∩ {z' | dist z z' < r}) ≤ 8 * ENNReal.ofReal r :=
    fun z => l53_near_le c ht z r
  have hbd := l53ZBadQ'_le P hloc' δ T hBm hBd hN hp a a
  -- `a/2 ≤ a − 8r`
  have h8 : 8 * ENNReal.ofReal r ≤ a / 2 := by
    have h1 : 16 * ENNReal.ofReal r ≤ a :=
      hrK.trans (mul_le_mul_of_nonneg_left (l53_frontier_ge c ht) zero_le)
    rw [ENNReal.le_div_iff_mul_le (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)]
    calc 8 * ENNReal.ofReal r * 2 = 16 * ENNReal.ofReal r := by ring
      _ ≤ a := h1
  have hNt : 8 * ENNReal.ofReal r ≠ ⊤ := ENNReal.mul_ne_top ENNReal.ofNat_ne_top ENNReal.ofReal_ne_top
  have hhalf : a / 2 ≤ a - 8 * ENNReal.ofReal r := by
    refine ENNReal.le_sub_of_add_le_left hNt ?_
    calc 8 * ENNReal.ofReal r + a / 2 ≤ a / 2 + a / 2 := add_le_add h8 le_rfl
      _ = a := ENNReal.add_halves a
  set X := P (l53ZBadQ M δ T Bd a a)
  set Y := P (l53ZBadQ' M δ T r Bd a a)
  have hXY : X ≤ Y := measure_mono (l53ZBadQ_subset' M δ T r Bd a a)
  have h2 : 2 * (a / 2) = a := ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top
  have key : K⁻¹ * μH[1] Bd * (K⁻¹ * μH[1] Bd) * X ≤ (2 * p) * μH[1] Bd ^ 2 := by
    calc K⁻¹ * μH[1] Bd * (K⁻¹ * μH[1] Bd) * X = a * a * X := rfl
      _ ≤ a * a * Y := mul_le_mul_of_nonneg_left hXY zero_le
      _ = 2 * (a / 2) * a * Y := by rw [h2]
      _ = 2 * (a / 2 * a * Y) := by ring
      _ ≤ 2 * ((a - 8 * ENNReal.ofReal r) * a * Y) := by gcongr
      _ ≤ 2 * (p * μH[1] Bd ^ 2) := by gcongr
      _ = (2 * p) * μH[1] Bd ^ 2 := by ring
  exact l53_K_cancel hK0 hKt hm0 hBd key

end DZZ
end LQGMetric
