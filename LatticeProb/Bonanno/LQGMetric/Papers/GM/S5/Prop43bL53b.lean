/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Prop43bL53b at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Prop43bL53
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Tubes57Meas

/-!
# Towards GM Lemma 5.3: `𝔈_r` is a.s. a function of internal metrics and the stopped geodesic
(task P2-M2N2)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
Lemma 5.3 and its proof, l. 2775–2789.
* `lastExitTime_*`, `stopLastExit_*` : basic facts on the last exit time `T` and the stopped path
  `u ↦ η(uT)` (D89a): if `T < 1` then `η(T) ∉ K`, a path meeting `K` has `T > 0`;
* `frkDistIn_stop_iff` : (5.4) (internal form) only sees the stopped path (every time at which
  the geodesic is in `B_{3r/2}(z)` is `< T`; time rescaling `s ↦ s/T`);
* `ae_mem_constCore_frkE_iff_stop` : a.s. `h ∈ constCore 𝔈_r` iff the internal form of (5.4)
  holds for the stopped path `stopLastExit (sel 𝕫 𝕨 h) (B_{4r}(z))` and the internal metrics of
  `D_h`, `D̃_h` in `B_{4r}(z)`, and (5.5) holds. What is left of Lemma 5.3 is the measurability of
  this right-hand side w.r.t. `σ(h|_{B_{4r}}) ∨ σ(stopped path)` (locality, Axiom II).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

lemma lastExit_bdd (η : C(unitInterval, ℂ)) (K : Set ℂ) :
    BddAbove {s : ℝ | ∃ u : unitInterval, (u : ℝ) = s ∧ η u ∈ K} :=
  ⟨1, fun _ ⟨u, hu, _⟩ => hu ▸ u.2.2⟩

lemma lastExitTime_nonneg (η : C(unitInterval, ℂ)) (K : Set ℂ) : 0 ≤ lastExitTime η K :=
  Real.sSup_nonneg (fun _ ⟨u, hu, _⟩ => hu ▸ u.2.1)

lemma lastExitTime_le_one (η : C(unitInterval, ℂ)) (K : Set ℂ) : lastExitTime η K ≤ 1 :=
  Real.sSup_le (fun _ ⟨u, hu, _⟩ => hu ▸ u.2.2) zero_le_one

lemma le_lastExitTime_of_mem {η : C(unitInterval, ℂ)} {K : Set ℂ} {s : unitInterval}
    (hs : η s ∈ K) : (s : ℝ) ≤ lastExitTime η K :=
  le_csSup (lastExit_bdd η K) ⟨s, rfl, hs⟩

lemma stopLastExit_apply (η : C(unitInterval, ℂ)) (K : Set ℂ) (u : unitInterval) :
    stopLastExit η K u = η (Set.projIcc 0 1 zero_le_one ((u : ℝ) * lastExitTime η K)) := rfl

/-- if the last exit time is `1`, the stopped path is the path -/
lemma stopLastExit_of_lastExitTime_eq_one {η : C(unitInterval, ℂ)} {K : Set ℂ}
    (hT : lastExitTime η K = 1) : stopLastExit η K = η := by
  funext u
  rw [stopLastExit_apply, hT, mul_one, Set.projIcc_val]

/-- for `K` open, if the last exit time `T` is `< 1` then `η(T) ∉ K` -/
lemma apply_lastExitTime_not_mem {η : C(unitInterval, ℂ)} {K : Set ℂ} (hK : IsOpen K)
    (hT1 : lastExitTime η K < 1) :
    η (Set.projIcc 0 1 zero_le_one (lastExitTime η K)) ∉ K := by
  intro hTK
  set T := lastExitTime η K with hT
  set T' : unitInterval := Set.projIcc 0 1 zero_le_one T with hT'
  have hT0 : 0 ≤ T := lastExitTime_nonneg η K
  have hT'v : (T' : ℝ) = T := by rw [hT', Set.projIcc_of_mem _ ⟨hT0, hT1.le⟩]
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1
    (η.continuous.continuousAt.preimage_mem_nhds (hK.mem_nhds hTK))
  have hv0 : 0 ≤ min (T + ε / 2) 1 := le_min (by linarith) zero_le_one
  have hv1 : min (T + ε / 2) 1 ≤ 1 := min_le_right _ _
  have hTv : T < min (T + ε / 2) 1 := lt_min (by linarith) hT1
  let u : unitInterval := ⟨min (T + ε / 2) 1, hv0, hv1⟩
  have hu : η u ∈ K := by
    refine hball ?_
    rw [Metric.mem_ball, Subtype.dist_eq, hT'v, Real.dist_eq, abs_lt]
    have : min (T + ε / 2) 1 ≤ T + ε / 2 := min_le_left _ _
    show -ε < min (T + ε / 2) 1 - T ∧ min (T + ε / 2) 1 - T < ε
    constructor <;> linarith
  have huS : (u : ℝ) ≤ T := le_lastExitTime_of_mem hu
  have : (u : ℝ) = min (T + ε / 2) 1 := rfl
  linarith

/-- for `K` open, a path meeting `K` has a positive last exit time -/
lemma lastExitTime_pos_of_mem {η : C(unitInterval, ℂ)} {K : Set ℂ} (hK : IsOpen K)
    {s : unitInterval} (hs : η s ∈ K) : 0 < lastExitTime η K := by
  rcases (lastExitTime_nonneg η K).lt_or_eq with h | h
  · exact h
  exfalso
  have hs0 : (s : ℝ) = 0 := le_antisymm (h ▸ le_lastExitTime_of_mem hs) s.2.1
  refine apply_lastExitTime_not_mem hK (by rw [← h]; exact zero_lt_one) ?_
  have e : Set.projIcc 0 1 zero_le_one (0 : ℝ) = s := by
    apply Subtype.ext
    rw [Set.projIcc_of_mem _ ⟨le_rfl, zero_le_one⟩]
    exact hs0.symm
  rw [← h, e]
  exact hs

/-- (5.4) in internal form sees only the geodesic stopped at its last exit from `B_{4r}(z)`
(time rescaling `s ↦ s/T`; D89a) -/
lemma frkDistIn_stop_iff (d d' : ContMetric) {cs Cs c₂ b₀ r : ℝ} (hr : 0 < r) (z : ℂ)
    (Q : C(unitInterval, ℂ)) :
    frkDistIn d d' cs Cs c₂ b₀ r z (stopLastExit Q (ball z (4 * r))) ↔
      frkDistIn d d' cs Cs c₂ b₀ r z Q := by
  have hsub : ball z (3 / 2 * r) ⊆ ball z (4 * r) := ball_subset_ball (by linarith)
  set T := lastExitTime Q (ball z (4 * r)) with hT
  have hT0 : 0 ≤ T := lastExitTime_nonneg _ _
  by_cases hT1 : T = 1
  · rw [stopLastExit_of_lastExitTime_eq_one hT1]
  have hTlt : T < 1 := lt_of_le_of_ne (lastExitTime_le_one _ _) hT1
  have hnot := apply_lastExitTime_not_mem (η := Q) isOpen_ball hTlt
  constructor
  · rintro ⟨s, t, h0, hst, h1, hs, ht, rest⟩
    have hs' : Q (Set.projIcc 0 1 zero_le_one ((s : ℝ) * T)) ∈ ball z (3 / 2 * r) := hs
    have ht' : Q (Set.projIcc 0 1 zero_le_one ((t : ℝ) * T)) ∈ ball z (3 / 2 * r) := ht
    have hTpos : 0 < T := lastExitTime_pos_of_mem isOpen_ball (hsub hs')
    have h0' : (0 : ℝ) < s := by simpa using Subtype.coe_lt_coe.2 h0
    have hst' : (s : ℝ) < t := Subtype.coe_lt_coe.2 hst
    have hsv : ((Set.projIcc 0 1 zero_le_one ((s : ℝ) * T) : unitInterval) : ℝ) = s * T := by
      rw [Set.projIcc_of_mem _ ⟨mul_nonneg s.2.1 hT0, mul_le_one₀ s.2.2 hT0 hTlt.le⟩]
    have htv : ((Set.projIcc 0 1 zero_le_one ((t : ℝ) * T) : unitInterval) : ℝ) = t * T := by
      rw [Set.projIcc_of_mem _ ⟨mul_nonneg t.2.1 hT0, mul_le_one₀ t.2.2 hT0 hTlt.le⟩]
    refine ⟨Set.projIcc 0 1 zero_le_one ((s : ℝ) * T), Set.projIcc 0 1 zero_le_one ((t : ℝ) * T),
      ?_, ?_, ?_, hs', ht', rest⟩
    · refine Subtype.coe_lt_coe.1 ?_
      rw [hsv]; exact mul_pos h0' hTpos
    · refine Subtype.coe_lt_coe.1 ?_
      rw [hsv, htv]; exact mul_lt_mul_of_pos_right hst' hTpos
    · refine Subtype.coe_lt_coe.1 ?_
      rw [htv]
      exact lt_of_le_of_lt (mul_le_of_le_one_left hT0 t.2.2) hTlt
  · rintro ⟨s, t, h0, hst, h1, hs, ht, rest⟩
    have hsT : (s : ℝ) ≤ T := le_lastExitTime_of_mem (hsub hs)
    have htT : (t : ℝ) ≤ T := le_lastExitTime_of_mem (hsub ht)
    have htT' : (t : ℝ) < T := by
      refine lt_of_le_of_ne htT fun h => hnot ?_
      show Q (Set.projIcc 0 1 zero_le_one T) ∈ ball z (4 * r)
      rw [← h, Set.projIcc_val]
      exact hsub ht
    have h0' : (0 : ℝ) < s := by simpa using Subtype.coe_lt_coe.2 h0
    have hst' : (s : ℝ) < t := Subtype.coe_lt_coe.2 hst
    have hTpos : 0 < T := h0'.trans_le hsT
    let s' : unitInterval := ⟨(s : ℝ) / T, div_nonneg s.2.1 hT0, by
      rw [div_le_one hTpos]; exact hsT⟩
    let t' : unitInterval := ⟨(t : ℝ) / T, div_nonneg t.2.1 hT0, by
      rw [div_le_one hTpos]; exact htT⟩
    have es : stopLastExit Q (ball z (4 * r)) s' = Q s := by
      rw [stopLastExit_apply]
      show Q (Set.projIcc 0 1 zero_le_one ((s : ℝ) / T * T)) = Q s
      rw [div_mul_cancel₀ _ hTpos.ne', Set.projIcc_val]
    have et : stopLastExit Q (ball z (4 * r)) t' = Q t := by
      rw [stopLastExit_apply]
      show Q (Set.projIcc 0 1 zero_le_one ((t : ℝ) / T * T)) = Q t
      rw [div_mul_cancel₀ _ hTpos.ne', Set.projIcc_val]
    refine ⟨s', t', ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact Subtype.coe_lt_coe.1 (show ((0 : unitInterval) : ℝ) < (s' : ℝ) from div_pos h0' hTpos)
    · exact Subtype.coe_lt_coe.1 (div_lt_div_of_pos_right hst' hTpos)
    · exact Subtype.coe_lt_coe.1
        (show (t' : ℝ) < ((1 : unitInterval) : ℝ) from (div_lt_one hTpos).2 htT')
    · rw [es]; exact hs
    · rw [et]; exact ht
    · rw [es, et]; exact rest

/-- **GM Lemma 5.3, reduction**: a.s. `h ∈ constCore 𝔈_r^{𝕫,𝕨}(z)` iff (5.4) holds in internal form
(metrics internal to `B_{4r}(z)`) for the geodesic stopped at its last exit from `B_{4r}(z)`, and
(5.5) holds -/
theorem ae_mem_constCore_frkE_iff_stop {γ : ℝ} {D D' : DistC → ContMetric} {c₀ c₀' : ℝ → ℝ}
    (hD : IsWeakLQGMetric γ D c₀) (hD' : IsWeakLQGMetric γ D' c₀')
    {sel : ℂ → ℂ → DistC → C(unitInterval, ℂ)}
    (hsel : ∀ (a b : ℂ) (g : DistC) (c : ℝ), sel a b (addConst g c) = sel a b g)
    {cs Cs c₂ b₀ Λ r : ℝ} (hcs : 0 < cs) (hcC : cs ≤ Cs) (hc₂ : 0 ≤ c₂) (hr : 0 < r)
    (hRat : RatiosAre D D' cs Cs) (G : Set TestC) (z a b : ℂ)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {h : Ω → DistC}
    (hh : IsWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, h ω ∈ constCore (frkE D D' sel cs Cs c₂ b₀ Λ r G z a b) ↔
      frkDistIn (D (h ω)) (D' (h ω)) cs Cs c₂ b₀ r z
          (stopLastExit (sel a b (h ω)) (ball z (4 * r))) ∧
        ∀ φ ∈ G, Real.exp (-dirInner (h ω) φ + gradEnergy φ / 2) ≤ Λ := by
  have hP := Tight.isGFFPlusCont_of_wp hh
  filter_upwards [ae_mem_constCore_frkE_iff hD hD' hsel cs Cs c₂ b₀ Λ r G z a b hh,
    hD.length P h hP, hD'.length P h hP, hRat P h hh] with ω h1 hL hL' hR
  rw [h1, frkDistIn_stop_iff _ _ hr]
  show frkDist D D' cs Cs c₂ b₀ r z (h ω) (sel a b (h ω)) ∧ _ ↔ _
  rw [frkDist_iff_frkDistIn hL hL' hcs hcC hc₂ (ratio_of_ratios hcs hcC hR.1 hR.2)]

end LQGMetric.GM
