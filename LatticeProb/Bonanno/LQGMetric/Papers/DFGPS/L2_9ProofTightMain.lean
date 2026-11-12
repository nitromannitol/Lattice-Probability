/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L2_9ProofTightMain at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_9ProofMeas

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 2.9, second conjunct: tightness on `W̄` (T:909–925)

Assembly of `L2_9ProofTight.lean` (one-square modulus from Lemma 2.8, separation of the squares,
the point `u ∈ S ∩ S'`) and the tightness criterion `LFPP.isTightMeasureSet_of_modulus`
(DFGPS (2.8)); measurability from `aemeasurable_lfppSqC_union`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS

open Blueprint LFPP

/-- **DFGPS Lemma 2.9, second conjunct** (T:909–925): tightness of the laws of
`𝔞_ε⁻¹ D_h^ε(·,·;W̄)`, `ε ∈ (0,1)`, for a dyadic domain `W` with connected closure. -/
theorem lem2_9_tight (h28 : Lem2_8) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {W : Set ℂ}
    (hW : IsDyadicDomain W) (hWc : IsConnected (closure W)) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsGFFPlusBddCont h P) :
    IsTightMeasureSet {μ | ∃ ε ∈ Ioo (0 : ℝ) 1,
      μ = P.map fun ω => lfppSqC (xiGamma γ) ε (h ω) (closure W)} := by
  obtain ⟨𝒮, h𝒮, rfl⟩ := hW
  rw [closure_dyadicDomain_eq h𝒮] at hWc ⊢
  have hsq := dyadic_squares_closedSq h𝒮
  set K := ⋃ S ∈ 𝒮, S
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 (isCompact_biUnion_closedSq 𝒮 hsq)
  haveI : ConnectedSpace K := isConnected_iff_connectedSpace.1 hWc
  set ξ := xiGamma γ
  have hval : ∀ ε (g : DistC), Continuous (heatMollify ε g) → ∀ p : K × K,
      lfppSqC ξ ε g K p = (aEpsDF ξ ε)⁻¹ * (lfppDOn ξ (heatMollify ε g) K p.1 p.2).toReal :=
    fun ε g hc p => toCMap_apply_of_continuous
      (continuous_lfppDOn_union_toReal hc 𝒮 hsq hWc.isPreconnected _) p
  refine LFPP.isTightMeasureSet_of_modulus _ ?_ ?_
  · rintro μ ⟨ε, hε, rfl⟩
    change Measure.map _ P (pmetSet K)ᶜ = 0
    have hm : AEMeasurable (fun ω => lfppSqC ξ ε (h ω) K) P :=
      aemeasurable_lfppSqC_union hh.1 ((hh.ae_tendstoLocallyUniformly_heatMollify ε
        hε.1.ne').mono fun ω hω => hω.2) 𝒮 hsq hWc.isPreconnected
    rw [Measure.map_apply_of_aemeasurable hm (isClosed_pmetSet K).isOpen_compl.measurableSet]
    refine measure_eq_zero_iff_ae_notMem.2 ?_
    filter_upwards [hh.ae_tendstoLocallyUniformly_heatMollify ε hε.1.ne'] with ω hω hbad
    apply hbad
    have hfin := lfppDOn_union_ne_top (ξ := ξ) hω.2 𝒮 hsq hWc.isPreconnected
    obtain ⟨δ, hδ, B, hB0, hB⟩ := exists_lfppDOn_union_le (ξ := ξ) hω.2 𝒮 hsq
    refine ⟨fun x => ?_, fun x y z => ?_⟩
    · rw [hval ε _ hω.2]
      have := hB x x.2 x x.2 (by simpa using hδ)
      simp only [sub_self, norm_zero, mul_zero, ENNReal.ofReal_zero, nonpos_iff_eq_zero] at this
      dsimp only
      rw [this, ENNReal.toReal_zero, mul_zero]
    · rw [hval ε _ hω.2, hval ε _ hω.2, hval ε _ hω.2, ← mul_add,
        ← ENNReal.toReal_add (hfin x x.2 y y.2) (hfin y y.2 z z.2)]
      exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono
        (ENNReal.add_ne_top.2 ⟨hfin x x.2 y y.2, hfin y y.2 z z.2⟩) (lfppDOn_triangle _ _ _))
        (inv_nonneg.2 (aEpsDF_nonneg_sq ξ ε))
  · intro ζ hζ
    set η := ζ / ((𝒮.card : ℝ) + 1)
    have hη : 0 < η := by positivity
    set bad : ℝ → ℝ → Set ℂ → Set Ω := fun δ ε S => {ω | ¬ ∀ z ∈ S, ∀ w ∈ S, ‖w - z‖ ≤ δ →
      (aEpsDF ξ ε)⁻¹ * (lfppDOn ξ (heatMollify ε (h ω)) S z w).toReal ≤ ζ / 2}
    have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), ∀ S ∈ 𝒮, ∀ ε ∈ Ioo (0 : ℝ) 1,
        P (bad δ ε S) ≤ ENNReal.ofReal η := by
      refine (eventually_all_finset 𝒮).2 fun S hS => ?_
      obtain ⟨a, s, hs, rfl⟩ := hsq S hS
      obtain ⟨δ, hδ, hb⟩ := sq_modulus h28 hγ hγ2 hs P h hh (half_pos hζ) hη
      filter_upwards [Ioo_mem_nhdsGT hδ] with δ' hδ' ε hε
      refine le_trans (measure_mono fun ω hω => ?_) (hb ε hε)
      simp only [bad, mem_ofPred_eq] at hω ⊢
      exact fun h' => hω fun z hz w hw hzw => h' z hz w hw (hzw.trans hδ'.2.le)
    obtain ⟨δ0, hδ0, hsep⟩ := exists_sep_finset 𝒮 hsq
    obtain ⟨δ, hδS, hδpos⟩ := (hev.and (Ioo_mem_nhdsGT hδ0)).exists
    refine ⟨δ, hδpos.1, ?_⟩
    rintro μ ⟨ε, hε, rfl⟩
    have hbadm : MeasurableSet {d : C(K × K, ℝ) | ¬ ∀ z w : K, dist z w ≤ δ → d (z, w) ≤ ζ} := by
      have e : {d : C(K × K, ℝ) | ¬ ∀ z w : K, dist z w ≤ δ → d (z, w) ≤ ζ} =
          ⋃ z : K, ⋃ w : K, ⋃ (_ : dist z w ≤ δ), {d | ζ < d (z, w)} := by
        ext d; simp only [mem_ofPred_eq, mem_iUnion, not_forall, not_le, exists_prop]
      rw [e]
      exact (isOpen_iUnion fun z => isOpen_iUnion fun w => isOpen_iUnion fun _ =>
        isOpen_lt continuous_const (continuous_eval_const _)).measurableSet
    have hm : AEMeasurable (fun ω => lfppSqC ξ ε (h ω) K) P :=
      aemeasurable_lfppSqC_union hh.1 ((hh.ae_tendstoLocallyUniformly_heatMollify ε
        hε.1.ne').mono fun ω hω => hω.2) 𝒮 hsq hWc.isPreconnected
    rw [Measure.map_apply_of_aemeasurable hm hbadm]
    calc _ ≤ P (⋃ S ∈ 𝒮, bad δ ε S) := by
          refine measure_mono_ae ?_
          filter_upwards [hh.ae_tendstoLocallyUniformly_heatMollify ε hε.1.ne'] with ω hω hbad
          by_contra hgood
          have hg : ∀ S ∈ 𝒮, ω ∉ bad δ ε S := fun S hS hb => hgood (mem_biUnion hS hb)
          apply hbad
          intro z w hzw
          rw [hval ε _ hω.2]
          obtain ⟨S, hS, hzS⟩ := mem_iUnion₂.1 z.2
          obtain ⟨T, hT, hwT⟩ := mem_iUnion₂.1 w.2
          have hd : ‖(w : ℂ) - z‖ ≤ δ := by
            rw [← dist_eq_norm, dist_comm, ← Subtype.dist_eq]; exact hzw
          have hST := hsep S hS T hT z hzS w hwT (hd.trans_lt hδpos.2)
          have gS := not_not.1 (hg S hS)
          have gT := not_not.1 (hg T hT)
          obtain ⟨a, s, hs, rfl⟩ := hsq S hS
          obtain ⟨b, t, ht, rfl⟩ := hsq T hT
          obtain ⟨u, ⟨huS, huT⟩, hu1, hu2⟩ := exists_mem_inter_closedSq_near hzS hwT hST
          have g1 := gS z hzS u huS (hu1.trans hd)
          have g2 := gT u huT w hwT (hu2.trans hd)
          obtain ⟨B1, -, hB1⟩ := exists_lfppDOn_le_mul_norm (ξ := ξ) hω.2 (convex_closedSq a s)
            (closedSq_subset_closedBall a hs.le)
          obtain ⟨B2, -, hB2⟩ := exists_lfppDOn_le_mul_norm (ξ := ξ) hω.2 (convex_closedSq b t)
            (closedSq_subset_closedBall b ht.le)
          have f1 := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hB1 z hzS u huS)
          have f2 := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hB2 u huT w hwT)
          have hK : lfppDOn ξ (heatMollify ε (h ω)) K z w ≤
              lfppDOn ξ (heatMollify ε (h ω)) (closedSq a s) z u +
                lfppDOn ξ (heatMollify ε (h ω)) (closedSq b t) u w :=
            (lfppDOn_triangle _ u _).trans (add_le_add
              (lfppDOn_anti_set (subset_biUnion_of_mem (u := fun S : Set ℂ => S) hS) _ _)
              (lfppDOn_anti_set (subset_biUnion_of_mem (u := fun S : Set ℂ => S) hT) _ _))
          have hK' := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨f1, f2⟩) hK
          rw [ENNReal.toReal_add f1 f2] at hK'
          have h𝔞 := inv_nonneg.2 (aEpsDF_nonneg_sq ξ ε)
          calc (aEpsDF ξ ε)⁻¹ * (lfppDOn ξ (heatMollify ε (h ω)) K z w).toReal
              ≤ (aEpsDF ξ ε)⁻¹ * ((lfppDOn ξ (heatMollify ε (h ω)) (closedSq a s) z u).toReal +
                (lfppDOn ξ (heatMollify ε (h ω)) (closedSq b t) u w).toReal) :=
                mul_le_mul_of_nonneg_left hK' h𝔞
            _ ≤ ζ / 2 + ζ / 2 := by rw [mul_add]; exact add_le_add g1 g2
            _ = ζ := by ring
      _ ≤ ∑ S ∈ 𝒮, P (bad δ ε S) := measure_biUnion_finset_le _ _
      _ ≤ ∑ S ∈ 𝒮, ENNReal.ofReal η := Finset.sum_le_sum fun S hS => hδS S hS ε hε
      _ ≤ ENNReal.ofReal ζ := by
          rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          refine ENNReal.ofReal_le_ofReal ?_
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          nlinarith


end LQGMetric.DFGPS
