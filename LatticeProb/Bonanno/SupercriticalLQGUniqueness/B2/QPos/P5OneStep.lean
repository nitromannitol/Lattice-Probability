/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.QPos.P5OneStep at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.QPos.P5OneStepDet

 













set_option autoImplicit false
noncomputable section

open Finset MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.QPos.P5

open P4

theorem compl_le_ofReal {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {E : Set Ω} (hE : MeasurableSet E) {p : ℝ} (hp : p ≤ 1) (h : ENNReal.ofReal (1 - p) ≤ μ E) :
    μ Eᶜ ≤ ENNReal.ofReal p := by
  rw [prob_compl_eq_one_sub hE]
  calc 1 - μ E ≤ 1 - ENNReal.ofReal (1 - p) := tsub_le_tsub_left h 1
    _ = ENNReal.ofReal p := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith)]
      congr 1; ring

 
theorem distBad_prob (n : ℕ) (z : ℤ × ℤ) (K : ℕ) (hK : 2 ∣ K) (hK0 : 0 < K) (ξ R q : ℝ)
    (hq0 : 0 ≤ q)
    (hpred : ∀ m, n - K + 1 ≤ m → m ≤ n - (K + 1) / 2 →
      ENNReal.ofReal q ≤ boxDGFF m (distEvent m ξ R)) :
    boxDGFF n (distBad n z K ξ R) ≤
      (Nat.choose (K / 2) (K / 8) : ℝ≥0∞) * (ENNReal.ofReal (1 - q)) ^ (K / 8) := by
  classical
  unfold distBad
  split_ifs with hz
  swap
  · simp
  set W := scaleWindow K
  set B : ∀ k : ℕ, Set (EuclideanSpace ℝ (DGFFSite (n - k))) := fun k => (distEvent (n - k) ξ R)ᶜ
  have hind := nested_iIndepSet n z W hz B (fun k _ => (distEvent_measurable _ ξ R).compl)
    (fun k _ => (distEvent_annDet _ ξ R).compl)
  have := independent_many_failures_bound (boxDGFF n) (scaleEvent n z W hz B) hind W (K / 8)
    (ENNReal.ofReal (1 - q)) ?_
  · rw [scaleWindow_card K hK hK0] at this
    exact this
  intro k hk
  unfold scaleEvent
  rw [dif_pos hk]
  have hpre : tresCLM (hz k hk) ⁻¹' B k = (tresCLM (hz k hk) ⁻¹' distEvent (n - k) ξ R)ᶜ := rfl
  rw [hpre]
  apply compl_le_ofReal ((tresCLM (hz k hk)).continuous.measurable (distEvent_measurable _ ξ R))
    (by linarith)
  rw [tres_prob (hz k hk) (distEvent_measurable _ ξ R), show 1 - (1 - q) = q by ring]
  have hkb := window_le hk
  have hk4 := (hz k hk).1
  exact hpred (n - k) (by omega) (by omega)

theorem goodCentres_card_le (n K : ℕ) : (goodCentres n K).card ≤ 25 * 4 ^ K :=
  (Finset.card_filter_le _ _).trans (dgffGridCenters_card_le n K)

 
theorem goodEvent_compl_le (c : ℝ) (hc : 0 < c)
    (hcir : ∀ m : ℕ, 4 ≤ m → ∀ u : ℝ, 0 < u →
      ENNReal.ofReal (1 - Real.exp (-c * u ^ 2)) ≤ boxDGFF m (highCircuit m u))
    (C₂ : ℝ)
    (hosc : ∀ (n : ℕ) (z : ℤ × ℤ) (W : Finset ℕ) (K : ℕ),
      W.Nonempty → W.card ≤ K → (∀ k ∈ W, GoodScale n z k) →
      ∀ A : ℕ → Finset (DGFFSite n), (∀ k ∈ W, (A k).Nonempty) →
      (∀ k ∈ W, ∀ c ∈ A k, inReg n z k c) →
      boxDGFF n {h | (1 / 8 : ℝ) * K / 4 < ((W.filter fun k => C₂ < osc n z k (A k) h).card : ℝ)} ≤
        ENNReal.ofReal ((1 / 8 : ℝ) ^ K))
    (K n : ℕ) (hK32 : 32 ∣ K) (hK : 32 ≤ K) (hn : K + 3 ≤ n) (ξ R q A u : ℝ)
    (hq0 : 0 ≤ q) (hA : 0 < A) (hu : 0 < u)
    (hpred : ∀ m, n - K + 1 ≤ m → m ≤ n - (K + 1) / 2 →
      ENNReal.ofReal q ≤ boxDGFF m (distEvent m ξ R)) :
    boxDGFF n (goodEvent n K ξ R A (A + 1 + u + C₂))ᶜ ≤
      ENNReal.ofReal (Real.exp (-c * A ^ 2)) +
        ((25 * 4 ^ K : ℕ) : ℝ≥0∞) *
          (((Nat.choose (K / 2) (K / 32) : ℝ≥0∞)) *
              (ENNReal.ofReal (Real.exp (-c * u ^ 2))) ^ (K / 32) +
            ENNReal.ofReal ((1 / 8 : ℝ) ^ K) +
            (Nat.choose (K / 2) (K / 8) : ℝ≥0∞) * (ENNReal.ofReal (1 - q)) ^ (K / 8)) := by
  classical
  set G := goodCentres n K
  set b35 := ((Nat.choose (K / 2) (K / 32) : ℝ≥0∞)) *
      (ENNReal.ofReal (Real.exp (-c * u ^ 2))) ^ (K / 32) + ENNReal.ofReal ((1 / 8 : ℝ) ^ K)
  set bd := (Nat.choose (K / 2) (K / 8) : ℝ≥0∞) * (ENNReal.ofReal (1 - q)) ^ (K / 8)
  have hsub : (goodEvent n K ξ R A (A + 1 + u + C₂))ᶜ ⊆ (highCircuit n A)ᶜ ∪
      (⋃ z ∈ G, bad35 n z K A (A + 1 + u + C₂)) ∪ (⋃ z ∈ G, distBad n z K ξ R) := by
    intro h hh
    unfold goodEvent at hh
    simp only [Set.mem_compl_iff, Set.mem_inter_iff, Set.mem_iInter, not_and_or, not_forall,
      not_not, exists_prop] at hh
    simp only [Set.mem_union, Set.mem_compl_iff, Set.mem_iUnion, exists_prop, G]
    exact hh
  have hhigh : boxDGFF n (highCircuit n A)ᶜ ≤ ENNReal.ofReal (Real.exp (-c * A ^ 2)) := by
    apply compl_le_ofReal (highCircuit_measurable n A)
    · rw [Real.exp_le_one_iff]; nlinarith
    · exact hcir n (by omega) A hA
  have hbad : boxDGFF n (⋃ z ∈ G, bad35 n z K A (A + 1 + u + C₂)) ≤
      ((25 * 4 ^ K : ℕ) : ℝ≥0∞) * b35 := by
    refine (measure_biUnion_finset_le _ _).trans ?_
    calc ∑ z ∈ G, boxDGFF n (bad35 n z K A (A + 1 + u + C₂)) ≤ ∑ _z ∈ G, b35 := by
          apply Finset.sum_le_sum
          intro z hz
          exact bad_scales_prob c hc hcir C₂ hosc K n hK32 hK hn z
            (Finset.mem_filter.mp hz).2 A u hA hu
      _ = (G.card : ℝ≥0∞) * b35 := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((25 * 4 ^ K : ℕ) : ℝ≥0∞) * b35 := by
          gcongr; exact_mod_cast goodCentres_card_le n K
  have hdist : boxDGFF n (⋃ z ∈ G, distBad n z K ξ R) ≤ ((25 * 4 ^ K : ℕ) : ℝ≥0∞) * bd := by
    refine (measure_biUnion_finset_le _ _).trans ?_
    calc ∑ z ∈ G, boxDGFF n (distBad n z K ξ R) ≤ ∑ _z ∈ G, bd := by
          apply Finset.sum_le_sum
          intro z _
          exact distBad_prob n z K (by omega) (by omega) ξ R q hq0 hpred
      _ = (G.card : ℝ≥0∞) * bd := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((25 * 4 ^ K : ℕ) : ℝ≥0∞) * bd := by
          gcongr; exact_mod_cast goodCentres_card_le n K
  calc boxDGFF n (goodEvent n K ξ R A (A + 1 + u + C₂))ᶜ
      ≤ boxDGFF n ((highCircuit n A)ᶜ ∪ (⋃ z ∈ G, bad35 n z K A (A + 1 + u + C₂)) ∪
          (⋃ z ∈ G, distBad n z K ξ R)) := measure_mono hsub
    _ ≤ boxDGFF n (highCircuit n A)ᶜ + boxDGFF n (⋃ z ∈ G, bad35 n z K A (A + 1 + u + C₂)) +
          boxDGFF n (⋃ z ∈ G, distBad n z K ξ R) :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ ENNReal.ofReal (Real.exp (-c * A ^ 2)) + ((25 * 4 ^ K : ℕ) : ℝ≥0∞) * b35 +
          ((25 * 4 ^ K : ℕ) : ℝ≥0∞) * bd := by gcongr
    _ = _ := by rw [add_assoc, ← mul_add]

 
theorem one_step (c : ℝ) (hc : 0 < c)
    (hcir : ∀ m : ℕ, 4 ≤ m → ∀ u : ℝ, 0 < u →
      ENNReal.ofReal (1 - Real.exp (-c * u ^ 2)) ≤ boxDGFF m (highCircuit m u))
    (C₂ : ℝ)
    (hosc : ∀ (n : ℕ) (z : ℤ × ℤ) (W : Finset ℕ) (K : ℕ),
      W.Nonempty → W.card ≤ K → (∀ k ∈ W, GoodScale n z k) →
      ∀ A : ℕ → Finset (DGFFSite n), (∀ k ∈ W, (A k).Nonempty) →
      (∀ k ∈ W, ∀ c ∈ A k, inReg n z k c) →
      boxDGFF n {h | (1 / 8 : ℝ) * K / 4 < ((W.filter fun k => C₂ < osc n z k (A k) h).card : ℝ)} ≤
        ENNReal.ofReal ((1 / 8 : ℝ) ^ K))
    (K n : ℕ) (hK32 : 32 ∣ K) (hK : 32 ≤ K) (hn : K + 3 ≤ n) (ξ R q A u : ℝ) (hξ : 0 < ξ)
    (hR : 0 < R) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hA : 0 < A) (hu : 0 < u)
    (hbudget : ENNReal.ofReal (Real.exp (-c * A ^ 2)) +
        ((25 * 4 ^ K : ℕ) : ℝ≥0∞) *
          (((Nat.choose (K / 2) (K / 32) : ℝ≥0∞)) *
              (ENNReal.ofReal (Real.exp (-c * u ^ 2))) ^ (K / 32) +
            ENNReal.ofReal ((1 / 8 : ℝ) ^ K) +
            (Nat.choose (K / 2) (K / 8) : ℝ≥0∞) * (ENNReal.ofReal (1 - q)) ^ (K / 8)) ≤
        ENNReal.ofReal (1 - q))
    (hpred : ∀ m, n - K + 1 ≤ m → m ≤ n - (K + 1) / 2 →
      ENNReal.ofReal q ≤ boxDGFF m (distEvent m ξ R)) :
    ENNReal.ofReal q ≤
      boxDGFF n (distEvent n ξ ((K / 4 : ℝ) * Real.exp (-ξ * (A + 1 + u + C₂)) * R)) := by
  set G := goodEvent n K ξ R A (A + 1 + u + C₂)
  have hc' := (goodEvent_compl_le c hc hcir C₂ hosc K n hK32 hK hn ξ R q A u hq0 hA hu
    hpred).trans hbudget
  have hcov : 1 ≤ boxDGFF n G + boxDGFF n Gᶜ := by
    rw [← measure_univ (μ := boxDGFF n), ← Set.union_compl_self G]
    exact measure_union_le _ _
  have hG : ENNReal.ofReal q ≤ boxDGFF n G := by
    have h1 : 1 - boxDGFF n Gᶜ ≤ boxDGFF n G := tsub_le_iff_right.mpr hcov
    have h2 : ENNReal.ofReal q = 1 - ENNReal.ofReal (1 - q) := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith)]
      congr 1; ring
    rw [h2]
    exact (tsub_le_tsub_left hc' 1).trans h1
  exact hG.trans (measure_mono (goodEvent_sub n K hK32 hK hn ξ R A _ hξ hR))

end SupercriticalLQGUniqueness.B2.QPos.P5
