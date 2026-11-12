/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S3.GoodAnnulusL38 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.GoodAnnulusL38Trans
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.GoodAnnulusLong
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.GoodAnnulusAround
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.DeterministicScale
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.TightE2Core
import Mathlib.Data.Nat.Nth

/-!
# GM Lemma 3.8 from Lemma 3.7 (task P2-M2E2)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
Lemma 3.8 (`lem-shorter-annulus`, l. 1366–1373) and its proof (l. 1375–1396): "let
`r_1, …, r_K` be the values of `r` from (B), enumerated in decreasing order. Note that
`K ≥ (ν − μ) log_8 ε⁻¹` [here `(ν − μ)/2 · log_8 ε⁻¹`, GA-5]. By Lemma 3.7, we can apply Lemma 2.6
[= LM Lemma 3.1] … if `P[𝖤_{r_k}(z)] ≥ p̃` for all `z` and `k ∈ [1,K]`, then (3.?) holds", followed
by the three per-scale bounds (conditions 2, 3: `gm_gaLong_prob`, `gm_gaAround_prob`; condition 1:
`prob_gaCompare_compl_le`).

Details:
* LM Lemma 3.1 (`Blueprint.LMLem3_1a`) is stated at the centre `0` for a normalized field; it is
  applied to `h(· + z) − h_1(z)` with `s₁ = 1/8`, `s₂ = 1/2`, radii `4 r_k`, `a = q log 8 /
  ((ν − μ)/2)`, `b = 1/2` (as in `Tight.gm_S2_4e`). The events are the events of Lemma 3.7 at
  `(z, r_k)`, transported by `fieldSigma_le_affineComp` (`aeEventIn_goodAnnulus_translate`).
* The scales `r_1 > r_2 > …` are enumerated with `Nat.nth`; the index `0` of LM's sequence is the
  first scale (not counted by `countOcc`), indices `≥ K` are padded with trivial events.
* Condition 1 at a general centre uses the measurability of condition 1 (D48), which needs
  geodesics between all pairs (GM.S1.1), hence the extra hypothesis `h38 : DFGPSLem3_8`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- the events of Lemma 3.7 at `(z, ρ)`, as events of the translated normalized field
`h(· + z) − h_1(z)` on `𝔸_{(4ρ)/8, (4ρ)/2}(0)` -/
theorem aeEventIn_goodAnnulus_translate (h37 : L3_7) {γ : ℝ} {D D' : DistC → ContMetric}
    {c : ℝ → ℝ} (hPS : PairSetting γ D D' c) {α : ℝ} (hα : 1 / 2 < α) (hα1 : α < 1) (A C' : ℝ)
    (z : ℂ) {ρ : ℝ} (hρ : 0 < ρ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsWholePlaneGFF h P) :
    ∃ E : Set Ω, MeasurableSet[fieldSigma (fun ω =>
        addConst (addConst (affineComp 1 z (h ω)) (-circleAvg (affineComp 1 z (h ω)) 1 0))
          (-circleAvg (addConst (affineComp 1 z (h ω)) (-circleAvg (affineComp 1 z (h ω)) 1 0))
            (4 * ρ) 0)) (annulus 0 (1 / 8 * (4 * ρ)) (1 / 2 * (4 * ρ)))] E ∧
      E =ᵐ[P] h ⁻¹' goodAnnulus D D' α A C' ρ z := by
  obtain ⟨F, hF, hFae⟩ := h37 hPS hα hα1 A C' z ρ hρ P h hh
  have hUV : ∀ y : ℂ, y ∈ annulus 0 (1 / 8 * (4 * ρ)) (1 / 2 * (4 * ρ)) ↔
      (1 : ℝ) • y + z ∈ annulus z (ρ / 2) (2 * ρ) := fun y => by
    show 1 / 8 * (4 * ρ) < ‖y - 0‖ ∧ ‖y - 0‖ < 1 / 2 * (4 * ρ) ↔
      ρ / 2 < ‖(1 : ℝ) • y + z - z‖ ∧ ‖(1 : ℝ) • y + z - z‖ < 2 * ρ
    simp only [sub_zero, one_smul, add_sub_cancel_right]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have hF2 := fieldSigma_le_affineComp one_pos hUV _ F hF
  obtain ⟨B, hB, hBF⟩ := hF2
  refine ⟨_, ⟨B, hB, rfl⟩, ?_⟩
  have hz := hh.affineComp one_pos z
  refine EventuallyEq.trans ?_ hFae.symm
  rw [← hBF]
  filter_upwards [CircleAvg.ae_circleAvg_addConst hz 0 (show (0 : ℝ) < 4 * ρ by positivity)]
    with ω hω
  simp only [mem_preimage]
  rw [affineComp_addConst one_pos, hω, Tight.circleAvg_affineComp_one, Tight.circleAvg_affineComp_one, GFFLaw.addConst_addConst]
  congr! 3
  ring

/-- `exp(−aN) ≤ ε^q` when `N ≥ (ν − μ)/2 · log_8 ε⁻¹` and `a = q log 8 / ((ν − μ)/2)` -/
lemma exp_count_le {q μ ν ε N : ℝ} (hq : 0 < q) (hμν : μ < ν) (hε : 0 < ε)
    (hN : (ν - μ) / 2 * Real.logb 8 ε⁻¹ ≤ N) :
    Real.exp (-(q * Real.log 8 / ((ν - μ) / 2)) * N) ≤ ε ^ q := by
  have hνμ : ν - μ ≠ 0 := by
    have : 0 < ν - μ := by linarith
    exact this.ne'
  have hl : Real.log 8 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  rw [Real.rpow_def_of_pos hε]
  apply Real.exp_le_exp.2
  have h1 : q * Real.log 8 / ((ν - μ) / 2) * ((ν - μ) / 2 * Real.logb 8 ε⁻¹) =
      -(Real.log ε * q) := by
    rw [Real.logb, Real.log_inv]; field_simp
  have h2 : q * Real.log 8 / ((ν - μ) / 2) * ((ν - μ) / 2 * Real.logb 8 ε⁻¹) ≤
      q * Real.log 8 / ((ν - μ) / 2) * N :=
    mul_le_mul_of_nonneg_left hN (div_nonneg (mul_nonneg hq.le (Real.log_pos (by norm_num)).le)
      (by linarith))
  linarith

/-- **GM Lemma 3.8** (`lem-shorter-annulus`, l. 1366–1396), from GM Lemma 3.7, LM Lemma 3.1 (1),
GM Prop 2.2, the closed-annulus GM Lemma 2.11 and GM.S1.1 (geodesics, via DFGPS Lemma 3.8). -/
theorem gm_L3_8 (h37 : L3_7) (h31a : LMLem3_1a) (h22 : P2_2) (h211 : L2_11c)
    (h38 : DFGPSLem3_8) : L3_8 := by
  intro γ D D' c hPS μ ν hμ hμν hν1 q hq
  obtain ⟨hγ0, hγ2, hD, hD'⟩ := id hPS
  have hd : 0 < (ν - μ) / 2 := by linarith
  set a : ℝ := q * Real.log 8 / ((ν - μ) / 2) with ha_def
  have ha : 0 < a := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 8)
    positivity
  obtain ⟨pt, cc, hpt0, hpt1, hcc, HLM⟩ := h31a (1 / 8) (1 / 2) (by norm_num) (by norm_num)
    (by norm_num) a ha (1 / 2) (by norm_num) (by norm_num)
  set p : ℝ := (1 - pt) / 3 with hp_def
  have hp0 : 0 < p := by rw [hp_def]; linarith
  have hp1 : p < 1 := by rw [hp_def]; linarith
  obtain ⟨α₀, hα₀, hα₀1, Hlong⟩ := gm_gaLong_prob h22 h211 hPS hp0 hp1
  refine ⟨α₀, p, ⟨by linarith, hα₀1⟩, ⟨hp0, hp1⟩, fun α hα => ?_⟩
  have hαlo : 1 / 2 < α := by linarith [hα.1]
  obtain ⟨A, hA, Haround⟩ := gm_gaAround_prob hD (α := α) (by linarith) hα.2
    (ENNReal.ofReal_pos.2 hp0)
  refine ⟨A, hA, max cc 1 * Real.exp a, by positivity, ?_⟩
  intro C' Ω _ P _ h hh R hR ε hε hB z
  -- the scales of (B)
  set Sel : Set ℕ := {k | ε ^ (1 + ν) ≤ (8 : ℝ)⁻¹ ^ k ∧ (8 : ℝ)⁻¹ ^ k ≤ ε ∧
    ENNReal.ofReal (1 - p) ≤ P (h ⁻¹' badScale D D' α ((8 : ℝ)⁻¹ ^ k * R) C')} with hSel
  have hBN : (ν - μ) / 2 * Real.logb 8 ε⁻¹ ≤ Sel.ncard := hB
  have hfin : Sel.Finite := by
    have hx : 0 < ε ^ (1 + ν) := Real.rpow_pos_of_pos hε.1 _
    obtain ⟨N0, hN0⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 8⁻¹)
      (by norm_num)).eventually (gt_mem_nhds hx)).exists_forall_of_atTop
    refine (finite_Iio N0).subset fun k hk => ?_
    obtain ⟨hk1, -, -⟩ := hk
    by_contra hk'
    exact absurd hk1 (not_le.2 (hN0 k (not_lt.1 hk')))
  set pr : ℕ → Prop := fun k => k ∈ Sel with hpr
  have hfin' : (Set.ofPred pr).Finite := hfin
  set N := hfin'.toFinset.card with hN_def
  have hNc : (N : ℝ) = Sel.ncard := by rw [Set.ncard_eq_toFinset_card Sel hfin]
  have hlog : 0 < Real.logb 8 ε⁻¹ :=
    Real.logb_pos (by norm_num) ((one_lt_inv₀ hε.1).2 hε.2)
  have hN1 : 1 ≤ N := by
    have : (0 : ℝ) < N := by rw [hNc]; nlinarith [mul_pos hd hlog]
    exact_mod_cast this
  have hexp : Real.exp (-a * N) ≤ ε ^ q := exp_count_le hq hμν hε.1 (by rw [hNc]; exact hBN)
  -- the enumeration `r_1 > r_2 > …` (index `j` ↦ `8^{-κ j}𝕣`)
  set κ : ℕ → ℕ := fun j => if j < N then Nat.nth pr j else Nat.nth pr (N - 1) + (j + 1 - N)
    with hκ
  have hκmono : StrictMono κ := by
    refine strictMono_nat_of_lt_succ fun j => ?_
    simp only [hκ]
    split_ifs with h1 h2 h2
    · exact Nat.nth_lt_nth_of_lt_card hfin' (Nat.lt_succ_self j) h2
    · rw [show N - 1 = j by omega]; omega
    · omega
    · omega
  have hκSel : ∀ j < N, κ j ∈ Sel := fun j hj => by
    simp only [hκ, hj, ↓reduceIte]
    exact Nat.nth_mem_of_lt_card hfin' hj
  set ρ : ℕ → ℝ := fun j => (8 : ℝ)⁻¹ ^ κ j * R with hρ
  have hρpos : ∀ j, 0 < ρ j := fun j => by positivity
  set rr : ℕ → ℝ := fun j => 4 * ρ j with hrr
  -- the translated normalized field
  have hz := hh.affineComp one_pos z
  have hm1 := measurable_circleAvg_left 1 0
  set hn : Ω → DistC := fun ω =>
    addConst (affineComp 1 z (h ω)) (-circleAvg (affineComp 1 z (h ω)) 1 0) with hn_def
  have hnN : IsNormalizedWPGFF hn P := by
    refine ⟨hz.addConst (hm1.comp hz.measurable).neg, ?_⟩
    filter_upwards [CircleAvg.ae_circleAvg_addConst_one_zero hz] with ω hω
    simp only [hn_def]
    rw [hω]; ring
  choose E hEm hEae using fun j =>
    aeEventIn_goodAnnulus_translate h37 hPS hαlo hα.2 A C' z (hρpos j) P h hh
  classical
  set E' : ℕ → Set Ω := fun j => if j < N then E j else univ with hE'
  have hAI : AnnulusIterHyp hn (1 / 8) (1 / 2) rr E' := by
    refine ⟨fun k => by positivity, fun i j hij => ?_, fun k => ?_, fun k => ?_⟩
    · have h8 : (8 : ℝ)⁻¹ ^ κ j ≤ 8⁻¹ ^ κ i :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (hκmono.monotone hij)
      show 4 * ((8 : ℝ)⁻¹ ^ κ j * R) ≤ 4 * ((8 : ℝ)⁻¹ ^ κ i * R)
      nlinarith
    · have h8 : (8 : ℝ)⁻¹ ^ κ (k + 1) ≤ 8⁻¹ ^ (κ k + 1) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (hκmono (Nat.lt_succ_self k))
      rw [pow_succ] at h8
      have hpos : 0 < rr k := by positivity
      rw [div_le_iff₀ hpos]
      show 4 * ((8 : ℝ)⁻¹ ^ κ (k + 1) * R) ≤ 1 / 8 * (4 * ((8 : ℝ)⁻¹ ^ κ k * R))
      nlinarith [mul_le_mul_of_nonneg_right h8 hR.le]
    · simp only [hE']
      split_ifs
      · exact hEm k
      · exact MeasurableSet.univ
  have hEp : ∀ k, ENNReal.ofReal pt ≤ P (E' k) := fun k => by
    simp only [hE']
    split_ifs with hk
    · rw [measure_congr (hEae k)]
      obtain ⟨-, -, hsel⟩ := hκSel k hk
      have hc := goodAnnulus_compl_le P h D D' α A C' (ρ k) z
      have h1 := prob_gaCompare_compl_le h38 hγ0 hγ2 hD hD' hh (α := α) (C' := C') (r := ρ k)
        z hsel
      have h2 := Hlong α hα P h hh (ρ k) (hρpos k) z
      have h3 := (Haround P h hh (ρ k) (hρpos k) z).le
      have hsum : P (h ⁻¹' goodAnnulus D D' α A C' (ρ k) z)ᶜ ≤ ENNReal.ofReal (1 - pt) := by
        refine hc.trans ((add_le_add (add_le_add h1 h2) h3).trans_eq ?_)
        rw [← ENNReal.ofReal_add hp0.le hp0.le, ← ENNReal.ofReal_add (by positivity) hp0.le]
        congr 1; rw [hp_def]; ring
      have h1' : (1 : ℝ≥0∞) ≤ P (h ⁻¹' goodAnnulus D D' α A C' (ρ k) z) +
          P (h ⁻¹' goodAnnulus D D' α A C' (ρ k) z)ᶜ := by
        rw [← measure_univ (μ := P)]
        exact (measure_mono (union_compl_self _).symm.subset).trans (measure_union_le _ _)
      have h2' : ENNReal.ofReal pt + ENNReal.ofReal (1 - pt) = 1 := by
        rw [← ENNReal.ofReal_add hpt0.le (by linarith)]; simp
      rw [← h2'] at h1'
      exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1
        (h1'.trans (add_le_add le_rfl hsum))
    · rw [measure_univ]; exact ENNReal.ofReal_le_one.2 hpt1.le
  have HB := HLM P hn hnN rr E' hAI hEp (N - 1)
  have hall := ae_all_iff.2 hEae
  rcases Nat.lt_or_ge 1 N with hN2 | hN2
  · refine (measure_mono_ae ?_).trans (HB.trans (ENNReal.ofReal_le_ofReal ?_))
    · filter_upwards [hall] with ω hω hno
      by_contra hcount
      push Not at hcount
      have hpos : (0 : ℝ) < countOcc E' (N - 1) ω := by
        have : (1 : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ N - 1)
        linarith
      obtain ⟨k, hk1, hkK, hkE⟩ :=
        Tight.exists_good_of_count E' (Nat.zero_le _) ω (by rw [Nat.cast_zero]; exact hpos)
      have hkN : k < N := by omega
      simp only [hE', hkN, ↓reduceIte] at hkE
      have hg : ω ∈ h ⁻¹' goodAnnulus D D' α A C' (ρ k) z := by rw [← hω k]; exact hkE
      obtain ⟨b1, b2, -⟩ := hκSel k hkN
      exact hno (κ k) b1 b2 hg
    · have hc : ((N - 1 : ℕ) : ℝ) = N - 1 := by
        rw [Nat.cast_sub hN1, Nat.cast_one]
      rw [hc]
      calc cc * Real.exp (-a * (N - 1)) = cc * Real.exp a * Real.exp (-a * N) := by
            rw [mul_assoc, ← Real.exp_add]; ring_nf
        _ ≤ max cc 1 * Real.exp a * ε ^ q := by
            gcongr
            exact le_max_left _ _
  · have hN : (N : ℝ) = 1 := by exact_mod_cast (by omega : N = 1)
    rw [hN] at hexp
    refine prob_le_one.trans ?_
    rw [← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    calc (1 : ℝ) = 1 * Real.exp a * Real.exp (-a * 1) := by
          rw [mul_assoc, ← Real.exp_add]; simp
      _ ≤ max cc 1 * Real.exp a * ε ^ q := by
          gcongr
          exact le_max_right _ _

end LQGMetric.GM
