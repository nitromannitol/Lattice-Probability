import Mathlib
import LatticeProb.Prob.UpcrossLevel
import LatticeProb.Prob.UpcrossStrongMarkov

/-!
# The first up-crossing piece under conditioning to stay above `-δ`

Let `μ` be the law of Brownian motion with drift `mu > 0` on `C(ℝ≥0, ℝ)`, and let
`staySet δ` be the event that the path stays strictly above `-δ` for all times.  The event
`staySet δ` is the intersection of the event that the path hits `c` before `-δ` with the event that
the increments after the first hit of `c` stay above `-(δ + c)`; by the strong Markov property
at the first hit of `c`, the second event is independent of the path stopped at that hit.
Combined with the renewal equation at the level `-δ`, this gives, for every `δ > 0`,
`μ(staySet δ) · ∫ f(piece_c) dμ = ∫_{staySet δ} f(piece_c) dμ`:
conditioning on `staySet δ` does not change the law of the first up-crossing piece.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace LatticeProb

section Stay

/-- The path stays strictly above `-δ` for all times. -/
def staySet (δ : ℝ) : Set C(ℝ≥0, ℝ) := {z | ∀ t : ℝ≥0, -δ < z t}

lemma mem_staySet_iff {δ : ℝ} {z : C(ℝ≥0, ℝ)} :
    z ∈ staySet δ ↔ -δ < z 0 ∧ hitFrom (-δ) 0 (z : ℝ≥0 → ℝ) = ⊤ := by
  constructor
  · intro h
    refine ⟨h 0, ?_⟩
    by_contra hne
    obtain ⟨s, -, -, hs, -⟩ := exists_hitFrom_eq z.continuous hne
    exact (h s).ne' hs
  · rintro ⟨h0, htop⟩ t
    by_contra hle
    rw [not_lt] at hle
    obtain ⟨s, hs, hzs⟩ : ∃ s ∈ Set.Icc (0 : ℝ≥0) t, z s = -δ :=
      intermediate_value_Icc' zero_le z.continuous.continuousOn ⟨hle, h0.le⟩
    have : hitFrom (-δ) 0 (z : ℝ≥0 → ℝ) ≤ s := hitFrom_le zero_le hzs
    rw [htop] at this
    exact absurd (top_le_iff.1 this) (by simp)

lemma measurableSet_staySet (δ : ℝ) : MeasurableSet (staySet δ) := by
  have : staySet δ = {z : C(ℝ≥0, ℝ) | -δ < z 0} ∩
      {z : C(ℝ≥0, ℝ) | hitFrom (-δ) 0 (z : ℝ≥0 → ℝ) = ⊤} := by
    ext z; exact mem_staySet_iff
  rw [this]
  exact (measurableSet_lt measurable_const (continuous_eval_const 0).measurable).inter
    ((measurable_hitFrom (r := fun _ => 0) measurable_const (-δ)) (measurableSet_singleton ⊤))

/-- **Splitting at the first hit of `c`.**  A path from `0` which hits `c` stays above `-δ`
if and only if it hits `c` before `-δ` and its increments after the first hit of `c` stay above
`-(δ + c)`. -/
lemma mem_staySet_iff_split {δ c : ℝ} (hδ : 0 < δ) {w : C(ℝ≥0, ℝ)} (hw0 : w 0 = 0)
    (hτ : hitFrom c 0 (w : ℝ≥0 → ℝ) ≠ ⊤) :
    w ∈ staySet δ ↔ w ∈ levelSuccess δ c ∧
      shiftPath (hitFrom c 0 (w : ℝ≥0 → ℝ)).toNNReal w ∈ staySet (δ + c) := by
  obtain ⟨T, hT, -, hwT, -⟩ := exists_hitFrom_eq w.continuous hτ
  rw [hT, ENNReal.toNNReal_coe]
  constructor
  · intro h
    refine ⟨?_, fun s => ?_⟩
    · have htop : hitFrom (-δ) 0 (w : ℝ≥0 → ℝ) = ⊤ := (mem_staySet_iff.1 h).2
      show hitFrom c 0 (w : ℝ≥0 → ℝ) < hitFrom (-δ) 0 (w : ℝ≥0 → ℝ)
      rw [htop]; exact lt_top_iff_ne_top.2 hτ
    · have := h (T + s)
      simp only [shiftPath_apply, hwT]
      linarith
  · rintro ⟨hS, hsh⟩ t
    have hS' : hitFrom c 0 (w : ℝ≥0 → ℝ) < hitFrom (-δ) 0 (w : ℝ≥0 → ℝ) := hS
    rcases le_total t T with htT | hTt
    · by_contra hle
      rw [not_lt] at hle
      obtain ⟨s, hs, hzs⟩ : ∃ s ∈ Set.Icc (0 : ℝ≥0) t, w s = -δ :=
        intermediate_value_Icc' zero_le w.continuous.continuousOn
          ⟨hle, by rw [hw0]; linarith⟩
      have h1 : hitFrom (-δ) 0 (w : ℝ≥0 → ℝ) ≤ s := hitFrom_le zero_le hzs
      have h2 : (s : ℝ≥0∞) ≤ T := by exact_mod_cast hs.2.trans htT
      rw [hT] at hS'
      exact absurd (h1.trans h2) (not_le.2 hS')
    · have := hsh (t - T)
      simp only [shiftPath_apply, hwT, add_tsub_cancel_of_le hTt] at this
      linarith

end Stay

section Law

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- **Independence of the tail after the first hit of `c`.**  For Brownian motion with drift
`mu > 0`, `δ > 0`, `c > 0`, and a measurable functional `F` of the path stopped at its first hit of
`c`: `∫_{staySet δ} F(w^{τ_c}) dμ = μ(staySet (δ + c)) · ∫_{levelSuccess δ c} F(w^{τ_c}) dμ`. -/
theorem lintegral_stay_stopAt_driftLaw [IsProbabilityMeasure P] (hB : IsBrownianReal B P)
    (hm : ∀ t, Measurable (B t)) (hcont : ∀ ω, Continuous fun t => B t ω) {mu : ℝ} (hmu : 0 < mu)
    {δ c : ℝ} (hδ : 0 < δ) (hc : 0 < c) {F : C(ℝ≥0, ℝ) → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ w in staySet δ, F (stopAt (hitFrom c 0 (w : ℝ≥0 → ℝ)) w) ∂(driftLaw P B hcont mu) =
      driftLaw P B hcont mu (staySet (δ + c)) *
        ∫⁻ w in levelSuccess δ c, F (stopAt (hitFrom c 0 (w : ℝ≥0 → ℝ)) w)
          ∂(driftLaw P B hcont mu) := by
  set μ := driftLaw P B hcont mu with hμ
  have hτm : Measurable fun w : C(ℝ≥0, ℝ) => hitFrom c 0 (w : ℝ≥0 → ℝ) :=
    measurable_hitFrom (r := fun _ => 0) measurable_const c
  have hτ : IsStopFun fun w : C(ℝ≥0, ℝ) => hitFrom c 0 (w : ℝ≥0 → ℝ) := isStopFun_hitFrom_zero c
  have hBs : IsStopFun fun w : C(ℝ≥0, ℝ) => hitFrom (-δ) 0 (w : ℝ≥0 → ℝ) :=
    isStopFun_hitFrom_zero (-δ)
  have hae : ∀ᵐ w : C(ℝ≥0, ℝ) ∂μ, w 0 = 0 ∧ hitFrom c 0 (w : ℝ≥0 → ℝ) ≠ ⊤ :=
    ae_start_hitFrom_driftLaw hB hm hcont hmu hc.le
  have hS : MeasurableSet (levelSuccess δ c) := measurableSet_levelSuccess δ c
  have hSt : MeasurableSet (staySet (δ + c)) := measurableSet_staySet (δ + c)
  have hΦ : Measurable fun p : C(ℝ≥0, ℝ) × C(ℝ≥0, ℝ) =>
      (levelSuccess δ c).indicator F p.1 * (staySet (δ + c)).indicator (fun _ => (1 : ℝ≥0∞)) p.2 :=
    ((hF.indicator hS).comp measurable_fst).mul
      ((measurable_const.indicator hSt).comp measurable_snd)
  have hSM := lintegral_stopAt_shift_driftLaw hB hm hcont mu hτm hτ hΦ
  have hres : μ.restrict {w : C(ℝ≥0, ℝ) | hitFrom c 0 (w : ℝ≥0 → ℝ) < ⊤} = μ :=
    Measure.restrict_eq_self_of_ae_mem (by
      filter_upwards [hae] with w hw using lt_top_iff_ne_top.2 hw.2)
  rw [hres] at hSM
  -- the stopped path decides success
  have hstopS : ∀ w : C(ℝ≥0, ℝ), hitFrom c 0 (w : ℝ≥0 → ℝ) ≠ ⊤ →
      (stopAt (hitFrom c 0 (w : ℝ≥0 → ℝ)) w ∈ levelSuccess δ c ↔ w ∈ levelSuccess δ c) := by
    intro w hw
    obtain ⟨t, ht⟩ : ∃ t : ℝ≥0, (t : ℝ≥0∞) = hitFrom c 0 (w : ℝ≥0 → ℝ) :=
      ⟨_, ENNReal.coe_toNNReal hw⟩
    rw [← ht]
    exact hBs.stopAt_lt_iff_of_min_le hτ w t (by rw [ht]; exact min_le_right _ _)
  have hL : ∫⁻ w, (levelSuccess δ c).indicator F (stopAt (hitFrom c 0 (w : ℝ≥0 → ℝ)) w) *
        (staySet (δ + c)).indicator (fun _ => (1 : ℝ≥0∞))
          (shiftPath (hitFrom c 0 (w : ℝ≥0 → ℝ)).toNNReal w) ∂μ =
      ∫⁻ w in staySet δ, F (stopAt (hitFrom c 0 (w : ℝ≥0 → ℝ)) w) ∂μ := by
    rw [← lintegral_indicator (measurableSet_staySet δ)]
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with w ⟨hw0, hwt⟩
    have hiff := mem_staySet_iff_split hδ hw0 hwt
    by_cases hw : w ∈ staySet δ
    · obtain ⟨h1, h2⟩ := hiff.1 hw
      simp [Set.indicator_of_mem hw, Set.indicator_of_mem ((hstopS w hwt).2 h1), h2]
    · rw [Set.indicator_of_notMem hw]
      by_cases h1 : w ∈ levelSuccess δ c
      · have h2 : shiftPath (hitFrom c 0 (w : ℝ≥0 → ℝ)).toNNReal w ∉ staySet (δ + c) :=
          fun h2 => hw (hiff.2 ⟨h1, h2⟩)
        simp [Set.indicator_of_notMem h2]
      · simp [Set.indicator_of_notMem (fun h => h1 ((hstopS w hwt).1 h))]
  have hR : ∫⁻ w, ∫⁻ v, (levelSuccess δ c).indicator F (stopAt (hitFrom c 0 (w : ℝ≥0 → ℝ)) w) *
        (staySet (δ + c)).indicator (fun _ => (1 : ℝ≥0∞)) v ∂μ ∂μ =
      μ (staySet (δ + c)) * ∫⁻ w in levelSuccess δ c,
        F (stopAt (hitFrom c 0 (w : ℝ≥0 → ℝ)) w) ∂μ := by
    have hin : ∀ w : C(ℝ≥0, ℝ), ∫⁻ v, (levelSuccess δ c).indicator F
        (stopAt (hitFrom c 0 (w : ℝ≥0 → ℝ)) w) *
        (staySet (δ + c)).indicator (fun _ => (1 : ℝ≥0∞)) v ∂μ =
        (levelSuccess δ c).indicator F (stopAt (hitFrom c 0 (w : ℝ≥0 → ℝ)) w) *
          μ (staySet (δ + c)) := fun w => by
      rw [lintegral_const_mul _ (measurable_const.indicator hSt), lintegral_indicator hSt]
      simp
    simp_rw [hin]
    have hfin : μ (staySet (δ + c)) ≠ ⊤ := measure_ne_top _ _
    rw [lintegral_mul_const' _ _ hfin, mul_comm]
    congr 1
    calc ∫⁻ w, (levelSuccess δ c).indicator F (stopAt (hitFrom c 0 (w : ℝ≥0 → ℝ)) w) ∂μ
        = ∫⁻ w, (levelSuccess δ c).indicator
            (fun w : C(ℝ≥0, ℝ) => F (stopAt (hitFrom c 0 (w : ℝ≥0 → ℝ)) w)) w ∂μ := by
          refine lintegral_congr_ae ?_
          filter_upwards [hae] with w ⟨_, hwt⟩
          by_cases h1 : w ∈ levelSuccess δ c
          · rw [Set.indicator_of_mem h1, Set.indicator_of_mem ((hstopS w hwt).2 h1)]
          · rw [Set.indicator_of_notMem h1,
              Set.indicator_of_notMem (fun h => h1 ((hstopS w hwt).1 h))]
      _ = ∫⁻ w in levelSuccess δ c, F (stopAt (hitFrom c 0 (w : ℝ≥0 → ℝ)) w) ∂μ :=
          lintegral_indicator hS _
  exact hL.symm.trans (hSM.trans hR)

/-- **Conditioning on staying above `-δ` does not change the law of the first up-crossing piece.**
For Brownian motion with drift `mu > 0`, `δ > 0`, `c > 0` and `f ≤ 1` a functional of the first
up-crossing piece to `c`:
`μ(staySet δ) · ∫ f(piece_c) dμ = ∫_{staySet δ} f(piece_c) dμ`. -/
theorem driftLaw_mul_lintegral_piece_eq_setLIntegral_stay [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (hm : ∀ t, Measurable (B t))
    (hcont : ∀ ω, Continuous fun t => B t ω) {mu : ℝ} (hmu : 0 < mu) {δ c : ℝ} (hδ : 0 < δ)
    (hc : 0 < c) {f : (ℝ≥0 → ℝ) → ℝ≥0∞}
    (hf : Measurable fun w : C(ℝ≥0, ℝ) => f (firstUpcrossPiece c (w : ℝ≥0 → ℝ)))
    (hf1 : ∀ p, f p ≤ 1) :
    driftLaw P B hcont mu (staySet δ) *
        ∫⁻ w : C(ℝ≥0, ℝ), f (firstUpcrossPiece c (w : ℝ≥0 → ℝ)) ∂(driftLaw P B hcont mu)
      = ∫⁻ w in staySet δ, f (firstUpcrossPiece c (w : ℝ≥0 → ℝ)) ∂(driftLaw P B hcont mu) := by
  set μ := driftLaw P B hcont mu with hμ
  have hae : ∀ᵐ w : C(ℝ≥0, ℝ) ∂μ, w 0 = 0 ∧ hitFrom c 0 (w : ℝ≥0 → ℝ) ≠ ⊤ :=
    ae_start_hitFrom_driftLaw hB hm hcont hmu hc.le
  have hS : MeasurableSet (levelSuccess δ c) := measurableSet_levelSuccess δ c
  have hSt : MeasurableSet (staySet δ) := measurableSet_staySet δ
  -- the piece only depends on the path stopped at its first hit of `c`
  have hpiece : ∀ᵐ w : C(ℝ≥0, ℝ) ∂μ, firstUpcrossPiece c (w : ℝ≥0 → ℝ) =
      firstUpcrossPiece c (stopAt (hitFrom c 0 (w : ℝ≥0 → ℝ)) w : ℝ≥0 → ℝ) := by
    filter_upwards [hae] with w ⟨hw0, hwt⟩
    have hD : upcrossEnd₁ c (w : ℝ≥0 → ℝ) = ((hitFrom c 0 (w : ℝ≥0 → ℝ)).toNNReal : ℝ≥0) := by
      rw [upcrossEnd₁_of_zero_start hw0, ENNReal.coe_toNNReal hwt]
    have := firstUpcrossPiece_stopAt c w hD
    rw [ENNReal.coe_toNNReal hwt] at this
    exact this.symm
  have hmain := lintegral_stay_stopAt_driftLaw hB hm hcont hmu hδ hc
    (F := fun w : C(ℝ≥0, ℝ) => f (firstUpcrossPiece c (w : ℝ≥0 → ℝ))) hf
  have hone := lintegral_stay_stopAt_driftLaw hB hm hcont hmu hδ hc
    (F := fun _ : C(ℝ≥0, ℝ) => (1 : ℝ≥0∞)) measurable_const
  simp only [setLIntegral_const, one_mul] at hone
  have h6e := driftLaw_mul_lintegral_piece_eq_setLIntegral_level hB hm hcont hmu hδ hc hf hf1
  have e1 : ∫⁻ w in staySet δ, f (firstUpcrossPiece c (w : ℝ≥0 → ℝ)) ∂μ =
      ∫⁻ w in staySet δ, f (firstUpcrossPiece c
        (stopAt (hitFrom c 0 (w : ℝ≥0 → ℝ)) w : ℝ≥0 → ℝ)) ∂μ :=
    setLIntegral_congr_fun_ae hSt (by filter_upwards [hpiece] with w hw _ using by rw [hw])
  have e2 : ∫⁻ w in levelSuccess δ c, f (firstUpcrossPiece c
        (stopAt (hitFrom c 0 (w : ℝ≥0 → ℝ)) w : ℝ≥0 → ℝ)) ∂μ =
      ∫⁻ w in levelSuccess δ c, f (firstUpcrossPiece c (w : ℝ≥0 → ℝ)) ∂μ :=
    setLIntegral_congr_fun_ae hS (by filter_upwards [hpiece] with w hw _ using by rw [hw])
  calc μ (staySet δ) * ∫⁻ w, f (firstUpcrossPiece c (w : ℝ≥0 → ℝ)) ∂μ
      = (μ (staySet (δ + c)) * μ (levelSuccess δ c)) *
          ∫⁻ w, f (firstUpcrossPiece c (w : ℝ≥0 → ℝ)) ∂μ := by rw [hone]
    _ = μ (staySet (δ + c)) * (μ (levelSuccess δ c) *
          ∫⁻ w, f (firstUpcrossPiece c (w : ℝ≥0 → ℝ)) ∂μ) := mul_assoc _ _ _
    _ = μ (staySet (δ + c)) * ∫⁻ w in levelSuccess δ c,
          f (firstUpcrossPiece c (w : ℝ≥0 → ℝ)) ∂μ := by rw [h6e]
    _ = μ (staySet (δ + c)) * ∫⁻ w in levelSuccess δ c, f (firstUpcrossPiece c
          (stopAt (hitFrom c 0 (w : ℝ≥0 → ℝ)) w : ℝ≥0 → ℝ)) ∂μ := by rw [e2]
    _ = ∫⁻ w in staySet δ, f (firstUpcrossPiece c
          (stopAt (hitFrom c 0 (w : ℝ≥0 → ℝ)) w : ℝ≥0 → ℝ)) ∂μ := hmain.symm
    _ = _ := e1.symm

end Law

end LatticeProb
