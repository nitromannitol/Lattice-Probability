import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_2Main
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_5

/-! # No good scale among many: iterating events that are local on annuli

Let `h` be a whole-plane GFF and `z ∈ ℂ`. Consider events `G_j`, `j ≥ 1`, attached to radii `ρ_j` with
`ρ_{j+1} ≤ ρ_j / 6`, such that `G_j` is almost surely an event of the translated, normalized field
`h(· + z) - h_1(z)`, again normalized at radius `3 ρ_j`, restricted to the annulus `A_{ρ_j/2, 5 ρ_j / 2}(0)`
(`AeAnnulusEvent`), and `P[G_j] ≥ p` for a probability `p` which depends only on the decay rate. By the annulus iteration
lemma (Lemma 3.1 of Lupu-Miller / Lemma 2.6 of Gwynne-Miller, in the form `LMLem3_1a`), the probability that none of
`G_1, ..., G_K` occurs is at most `c e^{-a K}`.

Main results:
* `AeAnnulusEvent`: the locality hypothesis on `G_j`.
* `exists_prob_noGood_le_of_aeAnnulusEvent`: the exponential bound for `P[no G_j, 1 ≤ j ≤ K]`.
* `exists_prob_not_goodCover_le_of_aeAnnulusEvent`: union bound over the lattice, `P[good circles do not cover a ball] ≤ K ε^M`.
-/

namespace LatticeProb.LQG

open MeasureTheory Set LQGMetric LQGMetric.Blueprint LQGMetric.DFGPS LQGMetric.DFGPS.L32M
open scoped ENNReal

/-- The event `G` is almost surely equal to an event of the translated field `h(· + z) - h_1(z)`, normalized at radius
`3 ρ` and restricted to the annulus `A_{ρ/2, 5ρ/2}(0)` (the annulus `A_{(3ρ)/6, 5(3ρ)/6}(0)`). -/
def AeAnnulusEvent {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (h : Ω → DistC) (z : ℂ) (ρ : ℝ)
    (G : Set Ω) : Prop :=
  ∃ E : Set Ω, MeasurableSet[fieldSigma (fun ω =>
      addConst (addConst (affineComp 1 z (h ω)) (-circleAvg (affineComp 1 z (h ω)) 1 0))
        (-circleAvg (addConst (affineComp 1 z (h ω)) (-circleAvg (affineComp 1 z (h ω)) 1 0))
          (3 * ρ) 0)) (annulus 0 (1 / 6 * (3 * ρ)) (5 / 6 * (3 * ρ)))] E ∧ E =ᵐ[P] G

/-- **The probability of no good scale decays exponentially.** Given the annulus iteration lemma, for every `a > 0` there
are `p ∈ (0, 1)` and `c > 0` such that for every whole-plane GFF `h`, every `z`, radii with `ρ_{j+1} ≤ ρ_j / 6` and events
`G_j` which are local on annuli (`AeAnnulusEvent`) with `P[G_j] ≥ p`, the probability that none of `G_1, ..., G_K` occurs
is at most `c e^{-a K}`. -/
theorem exists_prob_noGood_le_of_aeAnnulusEvent (h31a : LMLem3_1a) {a : ℝ} (ha : 0 < a) :
    ∃ pt : ℝ, 0 < pt ∧ pt < 1 ∧ ∃ cc : ℝ, 0 < cc ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
        LQGMetric.IsWholePlaneGFF h P → ∀ ρ : ℕ → ℝ, (∀ j, 0 < ρ j) → (∀ j, ρ (j + 1) ≤ ρ j / 6) →
        ∀ (z : ℂ) (K : ℕ), 1 ≤ K → ∀ G : ℕ → Set Ω, (∀ j, ENNReal.ofReal pt ≤ P (G j)) →
        (∀ j, AeAnnulusEvent P h z (ρ j) (G j)) →
          P {ω | ∀ j ∈ Finset.Icc 1 K, ω ∉ G j} ≤ ENNReal.ofReal (cc * Real.exp (-a * K)) := by
  obtain ⟨pt, cc, hpt0, hpt1, hcc, HLM⟩ := h31a (1 / 6) (5 / 6) (by norm_num) (by norm_num)
    (by norm_num) a ha (1 / 2) (by norm_num) (by norm_num)
  refine ⟨pt, hpt0, hpt1, cc, hcc, ?_⟩
  intro Ω _ P _ h hh ρ hρ hρ6 z K hK G hGp hGl
  have hz := hh.affineComp one_pos z
  have hm1 := measurable_circleAvg_left 1 0
  set hn : Ω → DistC := fun ω =>
    addConst (affineComp 1 z (h ω)) (-circleAvg (affineComp 1 z (h ω)) 1 0) with hn_def
  have hnN : IsNormalizedWPGFF hn P := by
    refine ⟨hz.addConst (hm1.comp hz.measurable).neg, ?_⟩
    filter_upwards [CircleAvg.ae_circleAvg_addConst_one_zero hz] with ω hω
    simp only [hn_def]
    rw [hω]; ring
  choose E hEm hEae using hGl
  have hAI : AnnulusIterHyp hn (1 / 6) (5 / 6) (fun j => 3 * ρ j) E := by
    refine ⟨fun k => by have := hρ k; positivity, antitone_nat_of_succ_le fun j => ?_,
      fun k => ?_, fun k => hEm k⟩
    · have := hρ6 j; have := hρ j
      show 3 * ρ (j + 1) ≤ 3 * ρ j
      linarith
    · have := hρ6 k; have := hρ k
      show 3 * ρ (k + 1) / (3 * ρ k) ≤ 1 / 6
      rw [div_le_iff₀ (by positivity)]; linarith
  have hEp : ∀ k, ENNReal.ofReal pt ≤ P (E k) := fun k =>
    (hGp k).trans_eq (measure_congr (hEae k)).symm
  have HB := HLM P hn hnN _ E hAI hEp K
  have hall := ae_all_iff.2 hEae
  refine (measure_mono_ae ?_).trans HB
  filter_upwards [hall] with ω hω hno
  have h0 : countOcc E K ω = 0 := by
    classical
    unfold countOcc
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro j hj hjE
    have hg : ω ∈ G j := by rw [← hω j]; exact hjE
    exact hno j hj hg
  show (countOcc E K ω : ℝ) < 1 / 2 * K
  rw [h0, Nat.cast_zero]
  have : (1 : ℝ) ≤ K := by exact_mod_cast hK
  linarith

/-- **No uncovered ball.** Given the annulus iteration lemma, for all `ν, M > 0` there are `p ∈ (0, 1)`, `K` and `ε₀ > 0`
such that for every whole-plane GFF `h`, every `𝕣 > 0`, every `ε ∈ (0, ε₀)` and every family of events `G r w` which are
local on annuli (`AeAnnulusEvent`) with `P[G r w] ≥ p`, the probability that the good circles `∂B_r(w)`, `G r w`, do not
cover the ball `B_{𝕣 ε^{-M}}(0)` in the sense of `GoodCover` is at most `K ε^M`. -/
theorem exists_prob_not_goodCover_le_of_aeAnnulusEvent (h31a : LMLem3_1a) {ν M : ℝ} (hν : 0 < ν) (hM : 0 < M) :
    ∃ pt : ℝ, 0 < pt ∧ pt < 1 ∧ ∃ K ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
        LQGMetric.IsWholePlaneGFF h P → ∀ 𝕣 : ℝ, 0 < 𝕣 → ∀ ε ∈ Ioo (0 : ℝ) ε₀,
        ∀ Gf : ℝ → ℂ → Set Ω, (∀ r w, 0 < r → ENNReal.ofReal pt ≤ P (Gf r w)) →
        (∀ r w, 0 < r → AeAnnulusEvent P h w r (Gf r w)) →
          P {ω | ¬ GoodCover (fun w r => ω ∈ Gf r w) ν M ε 𝕣} ≤ ENNReal.ofReal (K * ε ^ M) := by
  set Mt : ℝ := M + 2 * (M + (1 + ν)) with hMt
  have hMt0 : 0 < Mt := by rw [hMt]; positivity
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set a : ℝ := 3 * Real.log 2 * Mt / ν with ha_def
  have ha : 0 < a := by rw [ha_def]; positivity
  obtain ⟨pt, hpt0, hpt1, cc, hcc, H⟩ := exists_prob_noGood_le_of_aeAnnulusEvent h31a ha
  refine ⟨pt, hpt0, hpt1, 81 * (cc * Real.exp (4 * a / 3)), (2 : ℝ) ^ (-(4 / ν)), by positivity, ?_⟩
  intro Ω _ P _ h hh 𝕣 h𝕣 ε hε Gf hGp hGl
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
    {ω | ∀ j ∈ Finset.Icc 1 K, ω ∉ Gf (ρ j) w} with hBw
  set G := (LQGDimension.LFPPRecords.gridBox m 0 R).filter
    fun p => ‖LQGDimension.LFPPRecords.gridPt m p‖ < R with hG
  have hsub : {ω | ¬ GoodCover (fun w r => ω ∈ Gf r w) ν M ε 𝕣} ⊆
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
    rw [Metric.mem_ball, dist_eq_norm]
    calc _ < 2 * m := hp2
      _ = 𝕣 * ε ^ (1 + ν) / 2 := by rw [hm_def]; ring
  have hterm : ∀ p ∈ G, P (Bw (LQGDimension.LFPPRecords.gridPt m p)) ≤
      ENNReal.ofReal (cc * Real.exp (-a * K)) := fun p _ =>
    H P h hh ρ hρ hρ6 _ K hK1 (fun j => Gf (ρ j) _) (fun j => hGp _ _ (hρ j)) (fun j => hGl _ _ (hρ j))
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
  calc P {ω | ¬ GoodCover (fun w r => ω ∈ Gf r w) ν M ε 𝕣}
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

end LatticeProb.LQG
