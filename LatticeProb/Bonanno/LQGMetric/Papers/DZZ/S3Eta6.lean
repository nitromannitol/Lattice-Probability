/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3Eta6 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3Eta5

/-!
# The independent-squares lower tail of DZZ (Eq.LD-lowerbound-approx-LGD) (P2-DZZETA)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1196–1206): `S` is partitioned into `K²` squares of
side `ε s'`; `K²/4` of them, `S̃_{i_j}`, have mutually independent `M̃_{γ,ε²s',η}(S̃_{i_j})` (since
`ε² s' log(1/(ε² s')) < ε s'`); with `𝒜_j = {(ε s')^{-2} M̃(S̃_{i_j}) > β}`, `P(𝒜_j) ≥ 1 − β C_{γ,−1}`,
and `P(∑_j (ε s')^{-2} M̃(S̃_{i_j}) ≤ β² K²/4) ≤ P(∑_j 1_{𝒜_j} ≤ β K²/4)`, bounded by a binomial tail.

* **`measure_sum_le_of_iIndepFun`** (generic): for independent `Y_i ≥ 0` (`N` of them) with
  `P(Y_i ≤ β) ≤ q ≤ 1`, `0 < β ≤ 1/2`: `P(∑ Y_i ≤ β² N) ≤ 2^N q^{⌊N/2⌋}` (on the event at most
  `β N ≤ N/2` of the `Y_i` exceed `β`; union bound over the sets of the others).
  DZZ's displayed bound `((1 + e^{-1})/2 · e^β)^{K²/4} ≤ e^{-K²}` (l. 1204) uses only
  `P(𝒜_j) ≥ 1/2` and is not correct as displayed (`(1 + e^{-1})/2 > e^{-4}`); we use
  `P(𝒜_j^c) ≤ β C_{γ,−1}` instead (DZZ's own bound, l. 1202), which gives a much smaller tail.
* `evenSq w h i j`: the closed square `w + h((2i, 2j) + [0,1]²)` (every other square of the
  partition into squares of side `h = ε s'`); `disjoint_thickening_evenSq`: for `2r ≤ h` their
  `r`-thickenings are pairwise disjoint.
* **`measure_sum_etaChaos_le`**: `P(∑_{i,j<k} (h/2)^{-2} M̃_{γ,δ,η}(evenSq w h i j) ≤ β² k²) ≤
  2^{k²} (β C)^{⌊k²/2⌋}` for `δ ≤ h/2`, `r ≤ R` on `(0, δ²)`, `2(R + ρ) ≤ h`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal NNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise KilledHeat GMCIdent GMCIdent5 GMCIdent6 DGMC QuantumZipper

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- **binomial lower tail for independent nonnegative variables** -/
theorem measure_sum_le_of_iIndepFun [IsProbabilityMeasure P] {ι : Type} [Fintype ι]
    [DecidableEq ι] {Y : ι → Ω → ℝ≥0∞} (hY : iIndepFun Y P) (hYm : ∀ i, Measurable (Y i))
    {β : ℝ≥0∞} (hβ0 : β ≠ 0) (hβ : β ≤ 2⁻¹) {q : ℝ≥0∞} (hq1 : q ≤ 1)
    (hq : ∀ i, P {ω | Y i ω ≤ β} ≤ q) :
    P {ω | ∑ i, Y i ω ≤ β ^ 2 * Fintype.card ι} ≤
      2 ^ Fintype.card ι * q ^ (Fintype.card ι / 2) := by
  set N := Fintype.card ι
  have hβt : β ≠ ⊤ := ne_top_of_le_ne_top (by simp) hβ
  set A : ι → Set Ω := fun i => {ω | Y i ω ≤ β}
  set 𝒯 := (Finset.univ : Finset ι).powerset.filter fun T => N ≤ 2 * T.card
  have hsub : {ω | ∑ i, Y i ω ≤ β ^ 2 * N} ⊆ ⋃ T ∈ 𝒯, ⋂ i ∈ T, A i := by
    intro ω hω
    set T := (Finset.univ : Finset ι).filter fun i => Y i ω ≤ β
    have hTc : ((Finset.univ.filter fun i => ¬ Y i ω ≤ β).card : ℝ≥0∞) * β ≤ β * (β * N) := by
      calc ((Finset.univ.filter fun i => ¬ Y i ω ≤ β).card : ℝ≥0∞) * β
          = (Finset.univ.filter fun i => ¬ Y i ω ≤ β).card • β := by rw [nsmul_eq_mul]
        _ ≤ ∑ i ∈ Finset.univ.filter fun i => ¬ Y i ω ≤ β, Y i ω :=
            Finset.card_nsmul_le_sum _ _ _ fun i hi =>
              (not_le.1 (Finset.mem_filter.1 hi).2).le
        _ ≤ ∑ i, Y i ω := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
        _ ≤ β ^ 2 * N := hω
        _ = β * (β * N) := by ring
    rw [mul_comm] at hTc
    have h1 : ((Finset.univ.filter fun i => ¬ Y i ω ≤ β).card : ℝ≥0∞) ≤ β * N :=
      (ENNReal.mul_le_mul_iff_right hβ0 hβt).1 hTc
    have h2 : 2 * ((Finset.univ.filter fun i => ¬ Y i ω ≤ β).card : ℝ≥0∞) ≤ N := by
      calc 2 * ((Finset.univ.filter fun i => ¬ Y i ω ≤ β).card : ℝ≥0∞) ≤ 2 * (2⁻¹ * N) := by
            gcongr; exact h1.trans (by gcongr)
        _ = N := by rw [← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top,
              one_mul]
    have h3 : 2 * (Finset.univ.filter fun i => ¬ Y i ω ≤ β).card ≤ N := by exact_mod_cast h2
    have h4 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset ι))
      (fun i => Y i ω ≤ β)
    rw [Finset.card_univ] at h4
    have h5 : T.card + (Finset.univ.filter fun i => ¬ Y i ω ≤ β).card = N := h4
    refine mem_iUnion₂.2 ⟨T, Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.subset_univ _),
      by omega⟩, mem_iInter₂.2 fun i hi => (Finset.mem_filter.1 hi).2⟩
  have hcard : 𝒯.card ≤ 2 ^ N := by
    refine (Finset.card_filter_le _ _).trans (le_of_eq ?_)
    rw [Finset.card_powerset, Finset.card_univ]
  calc P {ω | ∑ i, Y i ω ≤ β ^ 2 * N} ≤ P (⋃ T ∈ 𝒯, ⋂ i ∈ T, A i) := measure_mono hsub
    _ ≤ ∑ T ∈ 𝒯, P (⋂ i ∈ T, A i) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _T ∈ 𝒯, q ^ (N / 2) := by
        refine Finset.sum_le_sum fun T hT => ?_
        have hTN := (Finset.mem_filter.1 hT).2
        change P (⋂ i ∈ T, Y i ⁻¹' Iic β) ≤ _
        rw [hY.meas_biInter (fun i _ => ⟨Iic β, measurableSet_Iic, rfl⟩)]
        calc ∏ i ∈ T, P (A i) ≤ ∏ _i ∈ T, q := Finset.prod_le_prod' fun i _ => hq i
          _ = q ^ T.card := Finset.prod_const q
          _ ≤ q ^ (N / 2) := pow_le_pow_right_of_le_one' hq1 (by omega)
    _ = 𝒯.card * q ^ (N / 2) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 ^ N * q ^ (N / 2) := by gcongr; exact_mod_cast hcard

/-- every other square of side `h`: `w + h((2i, 2j) + [0,1]²)` -/
def evenSq (w : ℂ) (h : ℝ) (i j : ℕ) : Set ℂ :=
  {z | w.re + 2 * i * h ≤ z.re ∧ z.re ≤ w.re + (2 * i + 1) * h ∧
    w.im + 2 * j * h ≤ z.im ∧ z.im ≤ w.im + (2 * j + 1) * h}

lemma measurableSet_evenSq (w : ℂ) (h : ℝ) (i j : ℕ) : MeasurableSet (evenSq w h i j) := by
  unfold evenSq
  refine ((measurableSet_le measurable_const Complex.measurable_re).inter
    ((measurableSet_le Complex.measurable_re measurable_const).inter
    ((measurableSet_le measurable_const Complex.measurable_im).inter
    (measurableSet_le Complex.measurable_im measurable_const))))

lemma ball_subset_evenSq (w : ℂ) {h : ℝ} (_hh : 0 < h) (i j : ℕ) :
    ball (w + ⟨(2 * i + 1 / 2) * h, (2 * j + 1 / 2) * h⟩) (h / 2) ⊆ evenSq w h i j := by
  intro z hz
  rw [mem_ball, dist_eq_norm] at hz
  have h1 := (Complex.abs_re_le_norm _).trans_lt hz
  have h2 := (Complex.abs_im_le_norm _).trans_lt hz
  simp only [Complex.sub_re, Complex.add_re, Complex.sub_im, Complex.add_im] at h1 h2
  rw [abs_lt] at h1 h2
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

lemma volume_evenSq_ne_top (w : ℂ) (h : ℝ) (i j : ℕ) : volume (evenSq w h i j) ≠ ⊤ := by
  refine ne_top_of_le_ne_top (measure_closedBall_lt_top (x := w)
    (r := |w.re| + |w.im| + (2 * i + 1) * |h| + (2 * j + 1) * |h| + ‖w‖)).ne
    (measure_mono fun z hz => ?_)
  obtain ⟨h1, h2, h3, h4⟩ := hz
  rw [mem_closedBall, dist_eq_norm]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simp only [Complex.sub_re, Complex.sub_im]
  have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg _
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg _
  have e1 : |z.re - w.re| ≤ (2 * i + 1) * |h| := by
    rw [abs_le]; constructor <;> nlinarith [abs_nonneg h, le_abs_self h, neg_abs_le h]
  have e2 : |z.im - w.im| ≤ (2 * j + 1) * |h| := by
    rw [abs_le]; constructor <;> nlinarith [abs_nonneg h, le_abs_self h, neg_abs_le h]
  linarith [abs_nonneg w.re, abs_nonneg w.im, norm_nonneg w]

lemma le_dist_evenSq {w : ℂ} {h : ℝ} (hh : 0 < h) {i j i' j' : ℕ} (hne : (i, j) ≠ (i', j'))
    {z z' : ℂ} (hz : z ∈ evenSq w h i j) (hz' : z' ∈ evenSq w h i' j') : h ≤ dist z z' := by
  obtain ⟨a1, a2, a3, a4⟩ := hz
  obtain ⟨b1, b2, b3, b4⟩ := hz'
  rw [dist_eq_norm]
  rcases Nat.lt_trichotomy i i' with hi | rfl | hi
  · have : (i : ℝ) + 1 ≤ i' := by exact_mod_cast hi
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    rw [Complex.sub_re, abs_sub_comm]; refine le_trans ?_ (le_abs_self _); nlinarith
  · have hj : j ≠ j' := fun h' => hne (by rw [h'])
    rcases Nat.lt_or_gt_of_ne hj with hj | hj
    · have : (j : ℝ) + 1 ≤ j' := by exact_mod_cast hj
      refine le_trans ?_ (Complex.abs_im_le_norm _)
      rw [Complex.sub_im, abs_sub_comm]; refine le_trans ?_ (le_abs_self _); nlinarith
    · have : (j' : ℝ) + 1 ≤ j := by exact_mod_cast hj
      refine le_trans ?_ (Complex.abs_im_le_norm _)
      rw [Complex.sub_im]; refine le_trans ?_ (le_abs_self _); nlinarith
  · have : (i' : ℝ) + 1 ≤ i := by exact_mod_cast hi
    refine le_trans ?_ (Complex.abs_re_le_norm _)
    rw [Complex.sub_re]; refine le_trans ?_ (le_abs_self _); nlinarith

lemma disjoint_thickening_evenSq {w : ℂ} {h r : ℝ} (hh : 0 < h) (hr : 2 * r ≤ h) {i j i' j' : ℕ}
    (hne : (i, j) ≠ (i', j')) :
    Disjoint (thickening r (evenSq w h i j)) (thickening r (evenSq w h i' j')) := by
  rw [Set.disjoint_left]
  intro p hp hp'
  obtain ⟨z, hz, hpz⟩ := mem_thickening_iff.1 hp
  obtain ⟨z', hz', hpz'⟩ := mem_thickening_iff.1 hp'
  have := le_dist_evenSq hh hne hz hz'
  have := dist_triangle_left z z' p
  linarith

/-- **DZZ l. 1196–1206 (the probabilistic part)** for the η-chaos on the even squares -/
theorem measure_sum_etaChaos_le (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (δ R ρ h : ℝ) (w : ℂ) (k : ℕ), 0 < δ → 0 < h → δ ≤ h / 2 →
      (∀ u ∈ Ioo 0 (δ ^ 2), etaRad u ≤ R) → 0 < ρ → 2 * (R + ρ) ≤ h →
      ∀ β : ℝ≥0∞, β ≠ 0 → β ≤ 2⁻¹ → β * C ≤ 1 →
      P {ω | ∑ ij : Fin k × Fin k, (ENNReal.ofReal (h / 2) ^ 2)⁻¹ *
          etaChaos W γ δ (evenSq w h ij.1 ij.2) ω ≤ β ^ 2 * (k * k : ℕ)} ≤
        2 ^ (k * k) * (β * C) ^ (k * k / 2) := by
  obtain ⟨C, hC, hmom⟩ := measure_etaChaos_le_le hW hγ hγ2
  refine ⟨C, hC, fun δ R ρ h w k hδ hh hδh hR hρ hRh β hβ0 hβ hβC => ?_⟩
  have hP := hW.isProbabilityMeasure
  have hβt : β ≠ ⊤ := ne_top_of_le_ne_top (by simp) hβ
  set Y : Fin k × Fin k → Ω → ℝ≥0∞ := fun ij ω =>
    (ENNReal.ofReal (h / 2) ^ 2)⁻¹ * etaChaos W γ δ (evenSq w h ij.1 ij.2) ω
  have hind : iIndepFun (fun ij : Fin k × Fin k => etaChaos W γ δ (evenSq w h ij.1 ij.2)) P :=
    iIndepFun_etaChaos hW hR hρ γ (fun ij => measurableSet_evenSq _ _ _ _)
      fun ij ij' hne => disjoint_thickening_evenSq hh (by linarith) (fun he => hne (by
        ext
        · exact congrArg Prod.fst he
        · exact congrArg Prod.snd he))
  have hY : iIndepFun Y P := hind.comp (fun _ y => (ENNReal.ofReal (h / 2) ^ 2)⁻¹ * y)
    fun _ => measurable_const_mul _
  have h := measure_sum_le_of_iIndepFun hY
    (fun ij => (measurable_etaChaos hW γ δ _).const_mul _) hβ0 hβ hβC (fun ij =>
      hmom δ _ (h / 2) _ hδ (measurableSet_evenSq _ _ _ _) (volume_evenSq_ne_top _ _ _ _)
        (ball_subset_evenSq w hh _ _) hδh β hβ0 hβt)
  simpa only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] using h

end DZZ
end LQGMetric
