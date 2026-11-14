/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module SupercriticalLQGUniqueness.B2.Polylog.P5Iterate at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.B2.Polylog.P7Net
import LatticeProb.Bonanno.SupercriticalLQGUniqueness.Uniqueness.Toolkit.AnnulusIteration.Bridge

 














set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology Metric Asymptotics
open scoped ENNReal
open LQGMetric (DistC)

namespace SupercriticalLQGUniqueness.B2.Polylog

 
def geoRad (ρ₀ t : ℝ) : ℝ := ρ₀ * (10 : ℝ) ^ (-t)

lemma geoRad_pos {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) (t : ℝ) : 0 < geoRad ρ₀ t :=
  mul_pos hρ₀ (Real.rpow_pos_of_pos (by norm_num) _)

lemma geoRad_succ_div_le {ρ₀ : ℝ} (hρ₀ : 0 < ρ₀) {s t : ℝ} (hst : s + 1 ≤ t) :
    geoRad ρ₀ t / geoRad ρ₀ s ≤ 1 / 10 := by
  unfold geoRad
  rw [mul_div_mul_left _ _ hρ₀.ne', ← Real.rpow_sub (by norm_num)]
  calc (10 : ℝ) ^ (-t - -s) ≤ (10 : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    _ = 1 / 10 := by rw [Real.rpow_neg_one]; norm_num

 






theorem annulus_iteration_finset (a : ℝ) (ha : 0 < a) :
    ∃ p c : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), LQGMetric.IsWholePlaneGFF h P →
        ∀ (z : ℂ) (ρ₀ : ℝ), 0 < ρ₀ → ∀ (S : Finset ℕ), S.Nonempty → ∀ (E : ℕ → Set Ω),
          (∀ i ∈ S, LQGMetric.Blueprint.AEEventIn P
            (LQGMetric.Blueprint.fieldSigma
              (fun ω => LQGMetric.addConst (h ω) (-LQGMetric.circleAvg (h ω) (geoRad ρ₀ i) z))
              (LQGMetric.Blueprint.annulus z (1 / 10 * geoRad ρ₀ i) (9 / 10 * geoRad ρ₀ i)))
            (E i)) →
          (∀ i ∈ S, ENNReal.ofReal p ≤ P (E i)) →
          P {ω | ∀ i ∈ S, ω ∉ E i} ≤ ENNReal.ofReal (c * Real.exp (-a * S.card)) := by
  obtain ⟨p, c, hp0, hp1, hc0, hmain⟩ :=
    Uniqueness.Toolkit.AnnulusIteration.annulus_iteration_ae_translated_open (1 / 10) (9 / 10)
      (by norm_num) (by norm_num) (by norm_num) a ha (1 / 2) (by norm_num) (by norm_num)
  refine ⟨p, c, hp0, hp1, hc0, ?_⟩
  intro Ω _ P _ h hh z ρ₀ hρ₀ S hS E hloc hprob
  classical
  set K := S.card with hKdef
  have hK : 0 < K := Finset.card_pos.2 hS
  let e : Fin K ↪o ℕ := S.orderEmbOfFin rfl
  let g : ℕ → ℕ := fun j => if hj : j < K then e ⟨j, hj⟩ else e ⟨K - 1, by omega⟩ + 1 + j
  have hg : StrictMono g := by
    refine strictMono_nat_of_lt_succ fun n => ?_
    by_cases h1 : n + 1 < K
    · have h0 : n < K := by omega
      simp only [g, h0, h1, ↓reduceDIte]
      exact e.strictMono (Fin.mk_lt_mk.2 (Nat.lt_succ_self n))
    · have h1' : ¬ n + 1 < K := h1
      simp only [g, h1', ↓reduceDIte]
      by_cases h0 : n < K
      · simp only [h0, ↓reduceDIte]
        have hn : n = K - 1 := by omega
        subst hn
        omega
      · simp only [h0, ↓reduceDIte]
        omega
  have hgS : ∀ j, j < K → g j ∈ S := by
    intro j hj
    simp only [g, hj, ↓reduceDIte]
    exact Finset.orderEmbOfFin_mem S rfl _
  let t : ℕ → ℝ := fun k => if k = 0 then -1 else ((g (k - 1) : ℕ) : ℝ)
  have ht : ∀ k, t k + 1 ≤ t (k + 1) := by
    intro k
    have hk1 : t (k + 1) = ((g k : ℕ) : ℝ) := by simp [t]
    rw [hk1]
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp [t]
    · have hk0 : k ≠ 0 := hk.ne'
      have : t k = ((g (k - 1) : ℕ) : ℝ) := by simp [t, hk0]
      rw [this]
      have hlt : g (k - 1) < g k := hg (by omega)
      exact_mod_cast hlt
  let r : ℕ → ℝ := fun k => geoRad ρ₀ (t k)
  let E' : ℕ → Set Ω := fun k => if k ≠ 0 ∧ k - 1 < K then E (g (k - 1)) else univ
  have hr : ∀ k, 0 < r k := fun k => geoRad_pos hρ₀ _
  have hratio : ∀ k, r (k + 1) / r k ≤ 1 / 10 := fun k => geoRad_succ_div_le hρ₀ (ht k)
  have hanti : Antitone r := by
    refine antitone_nat_of_succ_le fun k => ?_
    have h1 := hratio k
    rw [div_le_iff₀ (hr k)] at h1
    linarith [hr k]
  have hE'loc : ∀ k, LQGMetric.Blueprint.AEEventIn P
      (LQGMetric.Blueprint.fieldSigma
        (fun ω => LQGMetric.addConst (h ω) (-LQGMetric.circleAvg (h ω) (r k) z))
        (LQGMetric.Blueprint.annulus z (1 / 10 * r k) (9 / 10 * r k))) (E' k) := by
    intro k
    by_cases hk : k ≠ 0 ∧ k - 1 < K
    · have hrk : r k = geoRad ρ₀ ((g (k - 1) : ℕ) : ℝ) := by simp [r, t, hk.1]
      have hE : E' k = E (g (k - 1)) := by simp [E', hk.1, hk.2]
      rw [hE, hrk]
      exact hloc _ (hgS _ hk.2)
    · simp only [E', hk, ↓reduceIte]
      exact ⟨univ, MeasurableSet.univ, EventuallyEq.rfl⟩
  have hE'prob : ∀ k, ENNReal.ofReal p ≤ P (E' k) := by
    intro k
    by_cases hk : k ≠ 0 ∧ k - 1 < K
    · have hE : E' k = E (g (k - 1)) := by simp [E', hk.1, hk.2]
      rw [hE]
      exact hprob _ (hgS _ hk.2)
    · simp only [E', hk, ↓reduceIte, measure_univ]
      exact ENNReal.ofReal_le_one.2 hp1.le
  have hLM := hmain P h hh z r E' hr hanti hratio hE'loc hE'prob K
  refine le_trans (measure_mono ?_) hLM
  intro ω hω
  simp only [mem_ofPred_eq] at hω ⊢
  have hzero : LQGMetric.Blueprint.countOcc E' K ω = 0 := by
    unfold LQGMetric.Blueprint.countOcc
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro k hk hmem
    rw [Finset.mem_Icc] at hk
    have hk' : k ≠ 0 ∧ k - 1 < K := ⟨by omega, by omega⟩
    have hE : E' k = E (g (k - 1)) := by simp [E', hk'.1, hk'.2]
    rw [hE] at hmem
    exact hω _ (hgS _ hk'.2) hmem
  rw [hzero]
  have : (0 : ℝ) < K := by exact_mod_cast hK
  push_cast
  linarith

 

 
def plRadPt (ζ : ℝ) (ε : Set.Ioi (0 : ℝ)) (i : ℕ) : Set.Ioi (0 : ℝ) :=
  ⟨(10 : ℝ) ^ (-((i : ℝ) + 2)) * (ε : ℝ) ^ (1 - ζ),
    Set.mem_Ioi.mpr (mul_pos (Real.rpow_pos_of_pos (by norm_num) _)
      (Real.rpow_pos_of_pos (Set.mem_Ioi.mp ε.2) _))⟩

lemma plRadiusSet_eq (ζ : ℝ) (ε : Set.Ioi (0 : ℝ)) :
    plRadiusSet ζ ε = (Finset.range (plRadiusCount ζ ε)).image (plRadPt ζ ε) := rfl

lemma plRadPt_injective (ζ : ℝ) (ε : Set.Ioi (0 : ℝ)) : Function.Injective (plRadPt ζ ε) :=
  plRadiusSet_injective ζ ε

 
lemma plRadiusCount_ge {ζ ε : ℝ} (hζ : 0 ≤ ζ) (hε : ε ∈ Ioo (0 : ℝ) 1) :
    ζ / 2 * Real.logb 10 ε⁻¹ - 11 ≤ (plRadiusCount ζ ε : ℝ) := by
  have hx : 0 ≤ ζ / 2 * Real.logb 10 ε⁻¹ :=
    mul_nonneg (by linarith) (Real.logb_nonneg (by norm_num)
      (one_le_inv_iff₀.2 ⟨hε.1, hε.2.le⟩))
  have hfl := Nat.lt_floor_add_one (ζ / 2 * Real.logb 10 ε⁻¹)
  unfold plRadiusCount
  rcases le_or_gt 10 ⌊ζ / 2 * Real.logb 10 ε⁻¹⌋₊ with h10 | h10
  · rw [Nat.cast_sub h10]
    push_cast
    linarith
  · have hsub : ⌊ζ / 2 * Real.logb 10 ε⁻¹⌋₊ - 10 = 0 := by omega
    rw [hsub]
    have : (⌊ζ / 2 * Real.logb 10 ε⁻¹⌋₊ : ℝ) ≤ 9 := by exact_mod_cast (by omega : _ ≤ 9)
    push_cast
    linarith

 

lemma le_plRadPt {ζ ε : ℝ} (hζ : 0 < ζ) (hε : ε ∈ Ioo (0 : ℝ) 1) {i : ℕ}
    (hi : i < plRadiusCount ζ ε) :
    ε ^ (1 - ζ / 2) ≤ (plRadPt ζ ⟨ε, hε.1⟩ i : ℝ) := by
  have hN : (plRadiusCount ζ ε : ℝ) ≤ ζ / 2 * Real.logb 10 ε⁻¹ - 10 := by
    have hpos : 0 < ⌊ζ / 2 * Real.logb 10 ε⁻¹⌋₊ - 10 := lt_of_le_of_lt (Nat.zero_le i) hi
    have hx0 : 0 ≤ ζ / 2 * Real.logb 10 ε⁻¹ :=
      mul_nonneg (by linarith) (Real.logb_nonneg (by norm_num)
        (one_le_inv_iff₀.2 ⟨hε.1, hε.2.le⟩))
    have hfl := Nat.floor_le hx0
    show ((⌊ζ / 2 * Real.logb 10 ε⁻¹⌋₊ - 10 : ℕ) : ℝ) ≤ _
    rw [Nat.cast_sub (by omega)]
    push_cast
    linarith
  have hi' : (i : ℝ) + 2 ≤ ζ / 2 * Real.logb 10 ε⁻¹ := by
    have : (i : ℝ) + 1 ≤ plRadiusCount ζ ε := by exact_mod_cast hi
    linarith
  have h10x : (10 : ℝ) ^ (-(ζ / 2 * Real.logb 10 ε⁻¹)) = ε ^ (ζ / 2) := by
    rw [Real.rpow_def_of_pos (by norm_num), Real.rpow_def_of_pos hε.1]
    congr 1
    have hl : Real.log 10 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 10)).ne'
    simp only [Real.logb, Real.log_inv]
    field_simp
  show ε ^ (1 - ζ / 2) ≤ (10 : ℝ) ^ (-((i : ℝ) + 2)) * ε ^ (1 - ζ)
  calc ε ^ (1 - ζ / 2) = ε ^ (ζ / 2) * ε ^ (1 - ζ) := by
        rw [← Real.rpow_add hε.1]; ring_nf
    _ = (10 : ℝ) ^ (-(ζ / 2 * Real.logb 10 ε⁻¹)) * ε ^ (1 - ζ) := by rw [h10x]
    _ ≤ (10 : ℝ) ^ (-((i : ℝ) + 2)) * ε ^ (1 - ζ) :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))
          (Real.rpow_nonneg hε.1.le _)

 

lemma exists_two_plRad_lt {q s : ℝ} (hs : 0 < s) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → 2 * plRad q ε < ε ^ (1 - s) := by
  have hO := (isLittleO_log_rpow_rpow_atTop q hs).bound (show (0 : ℝ) < 1 / 4 by norm_num)
  obtain ⟨X, hX⟩ := eventually_atTop.1 hO
  refine ⟨1 / max X 1, by positivity, fun ε hε hεX => ?_⟩
  have hx : max X 1 < ε⁻¹ := by
    rw [lt_inv_comm₀ (by positivity) hε]
    simpa using hεX
  have hx1 : 1 < ε⁻¹ := lt_of_le_of_lt (le_max_right _ _) hx
  have hb := hX ε⁻¹ (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hx))
  have hlog : 0 < Real.log ε⁻¹ := Real.log_pos hx1
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog.le _),
    Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)] at hb
  have hpow : 0 < ε⁻¹ ^ s := Real.rpow_pos_of_pos (by positivity) _
  have hkey : 2 * Real.log ε⁻¹ ^ q < ε⁻¹ ^ s := by linarith
  unfold plRad
  calc 2 * (ε * Real.log ε⁻¹ ^ q) = ε * (2 * Real.log ε⁻¹ ^ q) := by ring
    _ < ε * ε⁻¹ ^ s := mul_lt_mul_of_pos_left hkey hε
    _ = ε ^ (1 - s) := by
        rw [sub_eq_add_neg, Real.rpow_add hε, Real.rpow_one, Real.rpow_neg hε.le,
          Real.inv_rpow hε.le]

end SupercriticalLQGUniqueness.B2.Polylog
