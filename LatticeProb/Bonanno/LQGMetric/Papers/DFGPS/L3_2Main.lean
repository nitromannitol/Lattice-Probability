/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L3_2Main at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_2Meas
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_2Node
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightA
import LatticeProb.Bonanno.LQGMetric.Metric.InternalC
import Mathlib.Topology.Order.IntermediateValue
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgProc
import Mathlib.Probability.Moments.Basic
import LatticeProb.Bonanno.LQGMetric.Blueprint.M2Defs
import LatticeProb.Bonanno.LQGMetric.Blueprint.DFGPSScaling
import LatticeProb.Bonanno.LQGMetric.Blueprint.LMResults
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.FieldAux
import Mathlib.Algebra.Order.Field.GeomSum
import LatticeProb.Bonanno.LQGDimension.LFPP.RecordsAux1

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
DFGPS = Dubédat–Falconet–Gwynne–Pfeffer–Sun, arXiv:1905.00380,
`literature/src/1905.00380/lqg-metric-estimates-final.tex` ("T"), Lemma 3.2
(`lem-good-annulus-all`, T:1452–1456) and its proof (T:1474–1481), following the paper:

* T:1475: `P[E_r(z;C)] ≥ p` for `C` large (`prob_annEvent`);
* T:1476: `E_r(z;C)` is determined by `(h − h_{3r}(z))|_{𝔸}` (`aeEventIn_annEvent`,
  `annEvent_translate` in `L3_2Meas.lean`);
* T:1477–1479: LM Lemma 3.1 (`Blueprint.LMLem3_1a`, = DFGPS Lemma 3.3) applied to the
  `⌊(ν log₂ ε⁻¹ − 1)/3⌋` radii `2^{-(k₀+3j)}𝕣 ∈ [ε^{1+ν}𝕣, ε𝕣]`, `k₀ = ⌈log₂ ε⁻¹⌉`, gives
  `P[no E_r(w;C)] ≤ c e^{−aK} = O(ε^{M̃})` for each `w` (`noGood_le`);
* T:1480–1481: union bound over the `O(ε^{−2(M+1+ν)})` points of
  `B_{𝕣ε^{−M}}(0) ∩ (ε^{1+ν}𝕣/4)ℤ²`, with `M̃ = M + 2(M + 1 + ν)` (`lem3_2`).

Details not spelled out in the paper (own elementary arguments): every `z ∈ B_{𝕣ε^{−M}}(0)` is
within `ε^{1+ν}𝕣/2` of a grid point of `B_{𝕣ε^{−M}}(0)`, obtained by rounding the coordinates of
`z` towards `0` (`exists_gridPt_trunc`); LM Lemma 3.1 is used with `s₁ = 1/6`, `s₂ = 5/6`,
radii `3·2^{-(k₀+3j)}𝕣` and `b = 1/2` (only "at least one good scale" is needed).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Metric Topology
open scoped ENNReal

namespace LQGMetric.DFGPS
open Blueprint

namespace L32M

/-- rounding towards `0`: `|km| ≤ |t|` and `|t − km| < m` -/
lemma exists_int_trunc {m : ℝ} (hm : 0 < m) (t : ℝ) :
    ∃ k : ℤ, |(k : ℝ) * m| ≤ |t| ∧ |t - k * m| < m := by
  rcases le_or_gt 0 t with ht | ht
  · refine ⟨⌊t / m⌋, ?_, ?_⟩
    · have h1 : (⌊t / m⌋ : ℝ) ≤ t / m := Int.floor_le _
      have h0 : (0 : ℝ) ≤ ⌊t / m⌋ := by exact_mod_cast Int.floor_nonneg.2 (div_nonneg ht hm.le)
      rw [le_div_iff₀ hm] at h1
      rw [abs_of_nonneg (mul_nonneg h0 hm.le), abs_of_nonneg ht]; exact h1
    · have h1 : (⌊t / m⌋ : ℝ) ≤ t / m := Int.floor_le _
      have h2 : t / m < ⌊t / m⌋ + 1 := Int.lt_floor_add_one _
      rw [le_div_iff₀ hm] at h1
      rw [div_lt_iff₀ hm] at h2
      rw [abs_lt]; constructor <;> nlinarith
  · refine ⟨⌈t / m⌉, ?_, ?_⟩
    · have h1 : t / m ≤ (⌈t / m⌉ : ℝ) := Int.le_ceil _
      have h0 : (⌈t / m⌉ : ℝ) ≤ 0 := by
        exact_mod_cast Int.ceil_le.2 (by push_cast; exact (div_neg_of_neg_of_pos ht hm).le)
      rw [div_le_iff₀ hm] at h1
      rw [abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg h0 hm.le), abs_of_neg ht]; linarith
    · have h1 : t / m ≤ (⌈t / m⌉ : ℝ) := Int.le_ceil _
      have h2 : (⌈t / m⌉ : ℝ) < t / m + 1 := Int.ceil_lt_add_one _
      rw [div_le_iff₀ hm] at h1
      have h2' : (⌈t / m⌉ : ℝ) * m < t + m := by
        have := (mul_lt_mul_iff_of_pos_right hm).2 h2
        rw [add_mul, div_mul_cancel₀ _ hm.ne', one_mul] at this; exact this
      rw [abs_lt]; constructor <;> linarith

/-- a grid point no farther from `0` than `z` and within `2m` of `z` -/
lemma exists_gridPt_trunc {m : ℝ} (hm : 0 < m) (z : ℂ) :
    ∃ p : ℤ × ℤ, ‖LQGDimension.LFPPRecords.gridPt m p‖ ≤ ‖z‖ ∧
      ‖z - LQGDimension.LFPPRecords.gridPt m p‖ < 2 * m := by
  obtain ⟨a, ha1, ha2⟩ := exists_int_trunc hm z.re
  obtain ⟨b, hb1, hb2⟩ := exists_int_trunc hm z.im
  have hpt : LQGDimension.LFPPRecords.gridPt m (a, b) = ⟨a * m, b * m⟩ := rfl
  have hn : ∀ w : ℂ, ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := fun w => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  set g := LQGDimension.LFPPRecords.gridPt m (a, b) with hg
  have hre : g.re = a * m := by rw [hpt]
  have him : g.im = b * m := by rw [hpt]
  refine ⟨(a, b), ?_, ?_⟩
  · have e1 := sq_le_sq.2 ha1
    have e2 := sq_le_sq.2 hb1
    have h2 : ‖g‖ ^ 2 ≤ ‖z‖ ^ 2 := by
      rw [hn g, hn z, hre, him]; linarith
    have := sq_le_sq.1 h2
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at this
  · have e1 : (z.re - a * m) ^ 2 < m ^ 2 := by
      rw [sq_lt_sq, abs_of_pos hm]; exact ha2
    have e2 : (z.im - b * m) ^ 2 < m ^ 2 := by
      rw [sq_lt_sq, abs_of_pos hm]; exact hb2
    have h2 : ‖z - g‖ ^ 2 < (2 * m) ^ 2 := by
      rw [hn, Complex.sub_re, Complex.sub_im, hre, him]; nlinarith
    have := sq_lt_sq.1 h2
    rwa [abs_of_nonneg (norm_nonneg _), abs_of_pos (by linarith)] at this

end L32M

open L32M in
/-- **DFGPS T:1477–1479** (LM Lemma 3.1 applied to `E_{ρ_j}(z;C)`): for each `a > 0` there are
`C > 1` and `c` such that for radii `ρ_{j+1} ≤ ρ_j/6`, the probability that `E_{ρ_j}(z;C)`
fails for all `j ∈ [1,K]` is at most `c e^{−aK}`. -/
theorem noGood_le (h31a : LMLem3_1a) {γ : ℝ} {D : DistC → ContMetric} {c : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c) {a : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 1 < C ∧ ∃ cc : ℝ, 0 < cc ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistC), IsWholePlaneGFF h P →
      ∀ ρ : ℕ → ℝ, (∀ j, 0 < ρ j) → (∀ j, ρ (j + 1) ≤ ρ j / 6) → ∀ (z : ℂ) (K : ℕ), 1 ≤ K →
        P {ω | ∀ j ∈ Finset.Icc 1 K, h ω ∉ annEvent (xiGamma γ) D c C (ρ j) z} ≤
          ENNReal.ofReal (cc * Real.exp (-a * K)) := by
  obtain ⟨pt, cc, hpt0, hpt1, hcc, HLM⟩ := h31a (1 / 6) (5 / 6) (by norm_num) (by norm_num)
    (by norm_num) a ha (1 / 2) (by norm_num) (by norm_num)
  obtain ⟨C, hC, HP⟩ := prob_annEvent hD (ε := ENNReal.ofReal (1 - pt))
    (ENNReal.ofReal_pos.2 (by linarith))
  refine ⟨C, hC, cc, hcc, ?_⟩
  intro Ω _ P _ h hh ρ hρ hρ6 z K hK
  have hz := hh.affineComp one_pos z
  have hm1 := measurable_circleAvg_left 1 0
  set hn : Ω → DistC := fun ω =>
    addConst (affineComp 1 z (h ω)) (-circleAvg (affineComp 1 z (h ω)) 1 0) with hn_def
  have hnN : IsNormalizedWPGFF hn P := by
    refine ⟨hz.addConst (hm1.comp hz.measurable).neg, ?_⟩
    filter_upwards [CircleAvg.ae_circleAvg_addConst_one_zero hz] with ω hω
    simp only [hn_def]
    rw [hω]; ring
  choose E hEm hEae using fun j => annEvent_translate hD C z (hρ j) P h hh
  have hAI : AnnulusIterHyp hn (1 / 6) (5 / 6) (fun j => 3 * ρ j) E := by
    refine ⟨fun k => by have := hρ k; positivity, antitone_nat_of_succ_le fun j => ?_,
      fun k => ?_, fun k => hEm k⟩
    · have := hρ6 j; have := hρ j
      show 3 * ρ (j + 1) ≤ 3 * ρ j
      linarith
    · have := hρ6 k; have := hρ k
      show 3 * ρ (k + 1) / (3 * ρ k) ≤ 1 / 6
      rw [div_le_iff₀ (by positivity)]; linarith
  have hEp : ∀ k, ENNReal.ofReal pt ≤ P (E k) := fun k => by
    rw [measure_congr (hEae k)]
    have hsum : P (h ⁻¹' annEvent (xiGamma γ) D c C (ρ k) z)ᶜ ≤ ENNReal.ofReal (1 - pt) :=
      (HP P h hh (ρ k) (hρ k) z).le
    have h1' : (1 : ℝ≥0∞) ≤ P (h ⁻¹' annEvent (xiGamma γ) D c C (ρ k) z) +
        P (h ⁻¹' annEvent (xiGamma γ) D c C (ρ k) z)ᶜ := by
      rw [← measure_univ (μ := P)]
      exact (measure_mono (union_compl_self _).symm.subset).trans (measure_union_le _ _)
    have h2' : ENNReal.ofReal pt + ENNReal.ofReal (1 - pt) = 1 := by
      rw [← ENNReal.ofReal_add hpt0.le (by linarith)]; simp
    rw [← h2'] at h1'
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1
      (h1'.trans (add_le_add le_rfl hsum))
  have HB := HLM P hn hnN _ E hAI hEp K
  have hall := ae_all_iff.2 hEae
  refine (measure_mono_ae ?_).trans HB
  filter_upwards [hall] with ω hω hno
  have h0 : countOcc E K ω = 0 := by
    classical
    unfold countOcc
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro j hj hjE
    have hg : ω ∈ h ⁻¹' annEvent (xiGamma γ) D c C (ρ j) z := by rw [← hω j]; exact hjE
    exact hno j hj hg
  show (countOcc E K ω : ℝ) < 1 / 2 * K
  rw [h0, Nat.cast_zero]
  have : (1 : ℝ) ≤ K := by exact_mod_cast hK
  linarith

open L32M in
/-- **DFGPS Lemma 3.2** (`lem-good-annulus-all`, T:1452–1456; proof T:1474–1481), from LM
Lemma 3.1 (1) (`LMLem3_1a`, = DFGPS Lemma 3.3). -/
theorem lem3_2 (h31a : LMLem3_1a) : Lem3_2 := by
  intro γ _ _ D c hD ν M hν hM
  set Mt : ℝ := M + 2 * (M + (1 + ν)) with hMt
  have hMt0 : 0 < Mt := by rw [hMt]; positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set a : ℝ := 3 * Real.log 2 * Mt / ν with ha_def
  have ha : 0 < a := by rw [ha_def]; positivity
  obtain ⟨C, hC, cc, hcc, H⟩ := noGood_le h31a hD ha
  refine ⟨C, hC, 81 * (cc * Real.exp (4 * a / 3)), (2 : ℝ) ^ (-(4 / ν)), by positivity, ?_⟩
  intro Ω _ P _ h hh 𝕣 h𝕣 ε hε
  obtain ⟨hε0, hεε⟩ := hε
  have h4ν : 0 < 4 / ν := by positivity
  have hε1 : ε < 1 :=
    hεε.trans (Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (neg_neg_of_pos h4ν))
  -- `L = log₂ ε⁻¹` and the scales
  set L := Real.logb 2 ε⁻¹ with hL
  have h2L : (2 : ℝ) ^ L = ε⁻¹ := Real.rpow_logb (by norm_num) (by norm_num) (inv_pos.2 hε0)
  have hLν : 4 / ν < L := by
    have : Real.logb 2 ε < Real.logb 2 ((2 : ℝ) ^ (-(4 / ν))) :=
      Real.logb_lt_logb one_lt_two hε0 hεε
    rw [Real.logb_rpow (by norm_num) (by norm_num)] at this
    rw [hL, Real.logb_inv]; linarith
  have hL0 : 0 < L := lt_trans h4ν hLν
  have hνL : 4 < ν * L := by
    rw [div_lt_iff₀ hν] at hLν; linarith
  set k₀ : ℕ := ⌈L⌉₊ with hk₀
  set K : ℕ := ⌊(ν * L - 1) / 3⌋₊ with hK
  have hK1 : 1 ≤ K := Nat.le_floor (by rw [Nat.cast_one, le_div_iff₀ (by norm_num)]; linarith)
  have hKle : (K : ℝ) ≤ (ν * L - 1) / 3 := Nat.floor_le (by linarith)
  have hKge : (ν * L - 1) / 3 < K + 1 := Nat.lt_floor_add_one _
  have hk0 : L ≤ k₀ := Nat.le_ceil L
  have hk0' : (k₀ : ℝ) < L + 1 := Nat.ceil_lt_add_one hL0.le
  set ρ : ℕ → ℝ := fun j => ((2 : ℝ) ^ (k₀ + 3 * j))⁻¹ * 𝕣 with hρ_def
  have hρ : ∀ j, 0 < ρ j := fun j => by positivity
  have hρ6 : ∀ j, ρ (j + 1) ≤ ρ j / 6 := fun j => by
    have e : ρ (j + 1) = ρ j / 8 := by
      simp only [hρ_def]
      rw [show k₀ + 3 * (j + 1) = (k₀ + 3 * j) + 3 by ring, pow_add]
      field_simp; norm_num
    rw [e]; have := hρ j; linarith
  have hadm : ∀ j ∈ Finset.Icc 1 K, ε ^ (1 + ν) * 𝕣 ≤ ρ j ∧ ρ j ≤ ε * 𝕣 := by
    intro j hj
    obtain ⟨-, hjK⟩ := Finset.mem_Icc.1 hj
    have hjK' : (j : ℝ) ≤ K := by exact_mod_cast hjK
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hn1 : L ≤ ((k₀ + 3 * j : ℕ) : ℝ) := by push_cast; linarith
    have hn2 : ((k₀ + 3 * j : ℕ) : ℝ) ≤ L * (1 + ν) := by
      have e : L * (1 + ν) = L + ν * L := by ring
      push_cast; rw [e]; linarith
    have hpos : 0 < (2 : ℝ) ^ (k₀ + 3 * j) := by positivity
    have hp : (2 : ℝ) ^ (k₀ + 3 * j) = (2 : ℝ) ^ ((k₀ + 3 * j : ℕ) : ℝ) :=
      (Real.rpow_natCast 2 _).symm
    constructor
    · refine mul_le_mul_of_nonneg_right ?_ h𝕣.le
      have e : ε ^ (1 + ν) = ((2 : ℝ) ^ (L * (1 + ν)))⁻¹ := by
        rw [Real.rpow_mul (by norm_num), h2L, Real.inv_rpow hε0.le, inv_inv]
      rw [e]
      refine inv_anti₀ hpos ?_
      rw [hp]; exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hn2
    · refine mul_le_mul_of_nonneg_right ?_ h𝕣.le
      calc ((2 : ℝ) ^ (k₀ + 3 * j))⁻¹ ≤ ((2 : ℝ) ^ L)⁻¹ := by
            refine inv_anti₀ (by positivity) ?_
            rw [hp]; exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hn1
        _ = ε := by rw [h2L, inv_inv]
  -- `e^{−aK} ≤ e^{4a/3} ε^{M̃}`
  have hexp : Real.exp (-a * K) ≤ Real.exp (4 * a / 3) * ε ^ Mt := by
    rw [Real.rpow_def_of_pos hε0, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have hLlog : L * Real.log 2 = -Real.log ε := by
      rw [hL, Real.logb, Real.log_inv]; field_simp
    have e : a * (ν * L) / 3 = Mt * (L * Real.log 2) := by
      rw [ha_def]; field_simp
    rw [hLlog] at e
    have hKge' : (ν * L - 4) / 3 ≤ K := by linarith
    have := mul_le_mul_of_nonneg_left hKge' ha.le
    nlinarith
  -- the grid and the union bound
  set m := ε ^ (1 + ν) * 𝕣 / 4 with hm_def
  have hx : 0 < ε ^ (1 + ν) := Real.rpow_pos_of_pos hε0 _
  have hm : 0 < m := by positivity
  set R := 𝕣 * ε ^ (-M) with hR_def
  have hR : 0 < R := by positivity
  set Bw : ℂ → Set Ω := fun w =>
    {ω | ∀ j ∈ Finset.Icc 1 K, h ω ∉ annEvent (xiGamma γ) D c C (ρ j) w} with hBw
  set G := (LQGDimension.LFPPRecords.gridBox m 0 R).filter
    fun p => ‖LQGDimension.LFPPRecords.gridPt m p‖ < R with hG
  have hsub : {ω | ¬ GoodCover (fun w r => h ω ∈ annEvent (xiGamma γ) D c C r w) ν M ε 𝕣} ⊆
      ⋃ p ∈ G, Bw (LQGDimension.LFPPRecords.gridPt m p) := by
    intro ω hω
    by_contra hn
    apply hω
    intro z hz
    obtain ⟨p, hp1, hp2⟩ := exists_gridPt_trunc hm z
    have hzR : ‖z‖ < R := mem_ball_zero_iff.1 hz
    have hpG : p ∈ G := Finset.mem_filter.2
      ⟨LQGDimension.LFPPRecords.mem_gridBox hm (by rw [sub_zero]; linarith), by linarith⟩
    have hnb : ω ∉ Bw (LQGDimension.LFPPRecords.gridPt m p) := fun hb =>
      hn (mem_biUnion hpG hb)
    simp only [hBw, mem_ofPred_eq, not_forall, not_not] at hnb
    obtain ⟨j, hj, hgood⟩ := hnb
    refine ⟨LQGDimension.LFPPRecords.gridPt m p,
      ⟨mem_ball_zero_iff.2 (by linarith), p.1, p.2, rfl⟩, ρ j, ⟨k₀ + 3 * j, rfl⟩,
      (hadm j hj).1, (hadm j hj).2, hgood, ?_⟩
    rw [mem_ball, dist_eq_norm]
    calc _ < 2 * m := hp2
      _ = 𝕣 * ε ^ (1 + ν) / 2 := by rw [hm_def]; ring
  have hterm : ∀ p ∈ G, P (Bw (LQGDimension.LFPPRecords.gridPt m p)) ≤
      ENNReal.ofReal (cc * Real.exp (-a * K)) := fun p _ => H P h hh ρ hρ hρ6 _ K hK1
  have hsx : 0 < ε ^ M * ε ^ (1 + ν) := by positivity
  have hcard : (G.card : ℝ) ≤ 81 * ((ε ^ M * ε ^ (1 + ν))⁻¹) ^ 2 := by
    refine (Nat.cast_le.2 (Finset.card_filter_le _ _)).trans
      ((LQGDimension.LFPPRecords.card_gridBox_le hm hR.le 0).trans ?_)
    have hx1 : 1 ≤ (ε ^ M * ε ^ (1 + ν))⁻¹ := (one_le_inv₀ hsx).2 (by
      have h1 := Real.rpow_le_one hε0.le hε1.le hM.le
      have h2 := Real.rpow_le_one hε0.le hε1.le (show 0 ≤ 1 + ν by linarith)
      nlinarith [Real.rpow_nonneg hε0.le M, Real.rpow_nonneg hε0.le (1 + ν)])
    have h8 : 2 * R / m = 8 * (ε ^ M * ε ^ (1 + ν))⁻¹ := by
      rw [hR_def, hm_def, Real.rpow_neg hε0.le]; field_simp; ring
    rw [h8]; nlinarith
  have hεMt : ε ^ Mt = ε ^ M * (ε ^ M * ε ^ (1 + ν)) ^ 2 := by
    rw [show Mt = M + (M + (1 + ν)) * 2 by rw [hMt]; ring, Real.rpow_add hε0,
      Real.rpow_mul hε0.le, Real.rpow_two, Real.rpow_add hε0]
  calc P {ω | ¬ GoodCover (fun w r => h ω ∈ annEvent (xiGamma γ) D c C r w) ν M ε 𝕣}
      ≤ P (⋃ p ∈ G, Bw (LQGDimension.LFPPRecords.gridPt m p)) := measure_mono hsub
    _ ≤ ∑ p ∈ G, P (Bw (LQGDimension.LFPPRecords.gridPt m p)) := measure_biUnion_finset_le _ _
    _ ≤ G.card • ENNReal.ofReal (cc * Real.exp (-a * K)) := Finset.sum_le_card_nsmul _ _ _ hterm
    _ = ENNReal.ofReal (G.card * (cc * Real.exp (-a * K))) := by
        rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    _ ≤ ENNReal.ofReal (81 * (cc * Real.exp (4 * a / 3)) * ε ^ M) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc (G.card : ℝ) * (cc * Real.exp (-a * K))
            ≤ 81 * ((ε ^ M * ε ^ (1 + ν))⁻¹) ^ 2 * (cc * (Real.exp (4 * a / 3) * ε ^ Mt)) :=
              mul_le_mul hcard (mul_le_mul_of_nonneg_left hexp hcc.le) (by positivity)
                (by positivity)
          _ = _ := by rw [hεMt]; field_simp

end LQGMetric.DFGPS
