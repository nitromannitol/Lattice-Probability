/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS3.Lemma37 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.Lemma31

/-!
# GMS [18] Lemma 3.7, deterministic form

Source: GMS [18] Lemma 3.7.

Let `{P_t}_{t ∈ [a, b]}` be subsets of `D` with `dist(P_s, P_t) ≥ C⁻¹ |s − t|` (stated as
`|s − t| ≤ C |u − v|` for `u ∈ P_s`, `v ∈ P_t`). For every `φ : V → ℝ`:

* `lemma37` (**[18] Lemma 3.7**, (3.18) with (3.19) as the hypothesis `∑_{x ∈ V(D)} diam(H_x)² deg(x) ≤ K`):
  `∫_a^b ∑_{{x,y} ∈ E(G(P_t))} |φ(x) − φ(y)| dt ≤ 2C √K √Energy(φ; G(D))`.
  The `t`-integral is a lower Lebesgue integral, so no measurability of `t ↦ P_t` is needed (the usual proof asks
  for Hausdorff continuity or explicit families to make `t ↦ 1{x, y ∈ V(P_t)}` measurable; here the set of
  `t` at which an edge belongs to `G(V(P_t))` is covered by an interval of length `2C diam(H_x)`, which
  costs the factor `2` against [18]'s `C`). The bound (3.19) itself is `cellSum_one_le` with Proposition
  2.10 for `(D, 1)` (Lemma 3.1 with `f = 1`).
* `exists_le_of_setLIntegral_le` ([18], "the average of any function is bounded below by its
  minimum"): if `∫_a^b F ≤ B` and `B < c (b − a)`, some `t ∈ [a, b]` has `F t ≤ c`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal Classical

namespace MatedCRTHarmonic.GMS3

open LFMultigraph Harmonic

variable {V E : Type*} {G : LFMultigraph V E} {o : V} (H : CellularEmbedding G o)

/-- The interval of times at which an edge of `G(V(D))` can belong to `G(V(P_t))`. -/
def edgeTimes (P : ℝ → Set ℂ) (a b C : ℝ) (e : E) : Set ℝ :=
  if h : ∃ t ∈ Icc a b, e ∈ edgesIn G (vFin H (P t)) then
    Icc (h.choose - C * cellDiam H (G.src e)) (h.choose + C * cellDiam H (G.src e))
  else ∅

theorem mem_edgeTimes {D : Set ℂ} (hDb : Bornology.IsBounded D) {P : ℝ → Set ℂ} {a b C : ℝ}
    (hPD : ∀ t ∈ Icc a b, P t ⊆ D)
    (hsep : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ u ∈ P s, ∀ v ∈ P t, |s - t| ≤ C * dist u v)
    (hC : 0 ≤ C) {e : E} {t : ℝ} (ht : t ∈ Icc a b) (he : e ∈ edgesIn G (vFin H (P t))) :
    t ∈ edgeTimes H P a b C e := by
  have hex : ∃ t ∈ Icc a b, e ∈ edgesIn G (vFin H (P t)) := ⟨t, ht, he⟩
  unfold edgeTimes
  rw [dite_eq_left hex]
  obtain ⟨ht₀, he₀⟩ := hex.choose_spec
  set t₀ := hex.choose
  have hb : ∀ s ∈ Icc a b, Bornology.IsBounded (P s) := fun s hs => hDb.subset (hPD s hs)
  obtain ⟨u, hux, hu⟩ := (mem_vFin H (hb t₀ ht₀)).mp ((mem_edgesIn G).mp he₀).1
  obtain ⟨v, hvx, hv⟩ := (mem_vFin H (hb t ht)).mp ((mem_edgesIn G).mp he).1
  have h1 := hsep t ht t₀ ht₀ v hv u hu
  have h2 : C * dist v u ≤ C * cellDiam H (G.src e) :=
    mul_le_mul_of_nonneg_left (dist_le_cellDiam H hvx hux) hC
  have h3 := (abs_le.mp (h1.trans h2))
  constructor <;> linarith [h3.1, h3.2]

theorem volume_edgeTimes_le (P : ℝ → Set ℂ) (a b C : ℝ) (e : E) :
    volume (edgeTimes H P a b C e) ≤ ENNReal.ofReal (2 * C * cellDiam H (G.src e)) := by
  unfold edgeTimes
  split_ifs with h
  · rw [Real.volume_Icc]
    exact ENNReal.ofReal_le_ofReal (by ring_nf; exact le_rfl)
  · simp

theorem measurableSet_edgeTimes (P : ℝ → Set ℂ) (a b C : ℝ) (e : E) :
    MeasurableSet (edgeTimes H P a b C e) := by
  unfold edgeTimes
  split_ifs
  · exact measurableSet_Icc
  · exact MeasurableSet.empty

/-- **[18] Lemma 3.7**, deterministic form: on the event (3.19) `∑_{x ∈ V(D)} diam(H_x)² deg(x) ≤ K`,
for every family `{P_t}_{t ∈ [a, b]}` of subsets of `D` with `dist(P_s, P_t) ≥ C⁻¹|s − t|` and every
`φ : V → ℝ`, `∫_a^b ∑_{E(G(P_t))} |φ(x) − φ(y)| dt ≤ 2C √K √Energy(φ; G(D))`. -/
theorem lemma37 {D : Set ℂ} (hDb : Bornology.IsBounded D) (P : ℝ → Set ℂ) {a b C K : ℝ}
    (hC : 0 ≤ C) (hPD : ∀ t ∈ Icc a b, P t ⊆ D)
    (hsep : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, ∀ u ∈ P s, ∀ v ∈ P t, |s - t| ≤ C * dist u v)
    (hK : ∑ x ∈ vFin H D, cellDiam H x ^ 2 * G.deg x ≤ K) (φ : V → ℝ) :
    ∫⁻ t in Icc a b, ENNReal.ofReal (tv G (vFin H (P t)) φ) ≤
      ENNReal.ofReal (2 * C * Real.sqrt K * Real.sqrt (energy G (vFin H D) φ)) := by
  set S := edgesIn G (vFin H D)
  set c : E → ℝ := fun e => |φ (G.src e) - φ (G.tgt e)|
  -- pointwise domination of the integrand
  have hpt : ∀ t ∈ Icc a b, ENNReal.ofReal (tv G (vFin H (P t)) φ) ≤
      ∑ e ∈ S, ENNReal.ofReal (c e) * (edgeTimes H P a b C e).indicator 1 t := by
    intro t ht
    have hsub : edgesIn G (vFin H (P t)) ⊆ S :=
      edgesIn_mono G (vFin_mono H hDb (hPD t ht))
    unfold tv
    rw [ENNReal.ofReal_sum_of_nonneg fun e _ => abs_nonneg _]
    calc ∑ e ∈ edgesIn G (vFin H (P t)), ENNReal.ofReal (c e)
        ≤ ∑ e ∈ edgesIn G (vFin H (P t)), ENNReal.ofReal (c e) *
            (edgeTimes H P a b C e).indicator 1 t := by
          refine Finset.sum_le_sum fun e he => ?_
          rw [Set.indicator_of_mem (mem_edgeTimes H hDb hPD hsep hC ht he), Pi.one_apply, mul_one]
      _ ≤ ∑ e ∈ S, ENNReal.ofReal (c e) * (edgeTimes H P a b C e).indicator 1 t :=
          Finset.sum_le_sum_of_subset hsub
  have hdeg : ∑ e ∈ S, cellDiam H (G.src e) ^ 2 ≤ ∑ x ∈ vFin H D, cellDiam H x ^ 2 * G.deg x := by
    have h := sum_edgesIn_add_le G (vFin H D) (φ := fun x => cellDiam H x ^ 2)
      fun x _ => sq_nonneg _
    calc ∑ e ∈ S, cellDiam H (G.src e) ^ 2
        ≤ ∑ e ∈ S, (cellDiam H (G.src e) ^ 2 + cellDiam H (G.tgt e) ^ 2) :=
          Finset.sum_le_sum fun e _ => le_add_of_nonneg_right (sq_nonneg _)
      _ ≤ ∑ x ∈ vFin H D, (G.deg x : ℝ) * cellDiam H x ^ 2 := h
      _ = ∑ x ∈ vFin H D, cellDiam H x ^ 2 * G.deg x :=
          Finset.sum_congr rfl fun x _ => mul_comm _ _
  have hCS : ∑ e ∈ S, c e * cellDiam H (G.src e) ≤
      Real.sqrt (energy G (vFin H D) φ) * Real.sqrt K := by
    refine (Real.sum_mul_le_sqrt_mul_sqrt S c fun e => cellDiam H (G.src e)).trans ?_
    gcongr
    · unfold energy
      exact le_of_eq (Finset.sum_congr rfl fun e _ => by simp only [c, sq_abs])
    · exact hdeg.trans hK
  calc ∫⁻ t in Icc a b, ENNReal.ofReal (tv G (vFin H (P t)) φ)
      ≤ ∫⁻ t in Icc a b, ∑ e ∈ S, ENNReal.ofReal (c e) * (edgeTimes H P a b C e).indicator 1 t :=
        setLIntegral_mono' measurableSet_Icc hpt
    _ ≤ ∫⁻ t, ∑ e ∈ S, ENNReal.ofReal (c e) * (edgeTimes H P a b C e).indicator 1 t :=
        setLIntegral_le_lintegral _ _
    _ = ∑ e ∈ S, ENNReal.ofReal (c e) * volume (edgeTimes H P a b C e) := by
        rw [lintegral_finsetSum _ fun e _ =>
          ((measurable_one (α := ℝ≥0∞) (β := ℝ)).indicator
            (measurableSet_edgeTimes H P a b C e)).const_mul _]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [lintegral_const_mul _ ((measurable_one (α := ℝ≥0∞) (β := ℝ)).indicator
            (measurableSet_edgeTimes H P a b C e)),
          lintegral_indicator_one (measurableSet_edgeTimes H P a b C e)]
    _ ≤ ∑ e ∈ S, ENNReal.ofReal (c e) * ENNReal.ofReal (2 * C * cellDiam H (G.src e)) :=
        Finset.sum_le_sum fun e _ => mul_le_mul' le_rfl (volume_edgeTimes_le H P a b C e)
    _ = ENNReal.ofReal (2 * C * ∑ e ∈ S, c e * cellDiam H (G.src e)) := by
        rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun e _ => by
          have := cellDiam_nonneg H (G.src e); have := abs_nonneg (φ (G.src e) - φ (G.tgt e))
          positivity]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [← ENNReal.ofReal_mul (abs_nonneg _)]
        congr 1
        ring
    _ ≤ ENNReal.ofReal (2 * C * Real.sqrt K * Real.sqrt (energy G (vFin H D) φ)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc 2 * C * ∑ e ∈ S, c e * cellDiam H (G.src e)
            ≤ 2 * C * (Real.sqrt (energy G (vFin H D) φ) * Real.sqrt K) := by gcongr
          _ = 2 * C * Real.sqrt K * Real.sqrt (energy G (vFin H D) φ) := by ring

/-- **The minimum is at most the average**. -/
theorem exists_le_of_setLIntegral_le {a b B c : ℝ} (hab : a < b) {F : ℝ → ℝ}
    (hint : ∫⁻ t in Icc a b, ENNReal.ofReal (F t) ≤ ENNReal.ofReal B) (hB : 0 ≤ B)
    (hc : B < c * (b - a)) : ∃ t ∈ Icc a b, F t ≤ c := by
  by_contra hne
  push Not at hne
  have hlow : ENNReal.ofReal (c * (b - a)) ≤ ∫⁻ t in Icc a b, ENNReal.ofReal (F t) := by
    calc ENNReal.ofReal (c * (b - a)) = ∫⁻ _ in Icc a b, ENNReal.ofReal c := by
          rw [setLIntegral_const, Real.volume_Icc, ← ENNReal.ofReal_mul]
          have : 0 < c * (b - a) := hB.trans_lt hc
          have hba : 0 < b - a := by linarith
          exact (pos_of_mul_pos_left this hba.le).le
      _ ≤ ∫⁻ t in Icc a b, ENNReal.ofReal (F t) :=
          setLIntegral_mono' measurableSet_Icc fun t ht => ENNReal.ofReal_le_ofReal (hne t ht).le
  have := hlow.trans hint
  rw [ENNReal.ofReal_le_ofReal_iff hB] at this
  linarith

end MatedCRTHarmonic.GMS3
