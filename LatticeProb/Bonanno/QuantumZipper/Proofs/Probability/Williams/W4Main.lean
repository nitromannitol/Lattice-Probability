/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Probability.Williams.W4Main at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.W4Pos

/-!
# W4 (part 2): the time-integrated law of `Ŷ`, given the last zero

Node W4 of `blueprint/EXT_PP_BLUEPRINT.md` (§A.1), in the form conditional on the almost sure
existence of a last zero of `Y = dpath σ μ b` after which `Y > 0` (`hgood`; this transience input
is proved in `W4Trans.lean`).

The route is the blueprint's: put `m = L + s − r`, so that `{s > r} = {Y > 0 on [m, ∞)}`
(`lintegral_postLast_eq_pathwise`); the simple Markov property at `m` (`markov_fixed`) turns the
integrand into `Φ(Y_m)`; `∫ dm E Φ(Y_m) = ∫ Φ d occ` (`lintegral_occ_eq`) and `occ = C · Leb` on
`(0, ∞)` (`occ_eq`, `occDens_nonneg_const`); the Markov property at `r` splits
`Φ(x) = E[1{x + Y > 0 on [0, r]} Ĥ(x + Y_r)]`; and the Lebesgue duality W2
(`lintegral_reversal`, `T = r`) turns `∫ dx Φ(x)` into `∫ dy Ĥ(y) P(y + X > 0 on [0, r])`.

Sources: D. Williams, *Path decomposition and continuity of local time for one-dimensional
diffusions I*, Proc. LMS 28 (1974); Rogers–Pitman, *Markov functions*, Ann. Probab. 9 (1981);
Revuz–Yor, *Continuous Martingales and Brownian Motion*, VII §4. The bookkeeping (Tonelli, the
measurable surrogates of `W4Pos.lean`) is own.
-/

set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper.Williams

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {b : ℝ≥0 → Ω → ℝ} {σ μ : ℝ}

/-- Indicator of the (surrogate of the) event `∀ t, 0 < w t`. -/
def posInd (w : ℝ≥0 → ℝ) : ℝ≥0∞ := posAllSet.indicator 1 w

theorem measurable_posInd : Measurable posInd :=
  measurable_const.indicator measurableSet_posAllSet

theorem posInd_of_pos {w : ℝ≥0 → ℝ} (hw : Continuous w) (h : ∀ t, 0 < w t) : posInd w = 1 := by
  rw [posInd, Set.indicator_of_mem ((mem_posAllSet_iff hw).2 h)]; rfl

theorem posInd_of_not {w : ℝ≥0 → ℝ} (hw : Continuous w) (h : ¬ ∀ t, 0 < w t) : posInd w = 0 :=
  Set.indicator_of_notMem (fun hm => h ((mem_posAllSet_iff hw).1 hm)) _

theorem posInd_of_nonpos {w : ℝ≥0 → ℝ} (hw : Continuous w) (h0 : w 0 ≤ 0) : posInd w = 0 :=
  posInd_of_not hw fun h => absurd (h 0) (not_lt.2 h0)

/-- Splitting positivity at a time `r`. -/
theorem posInd_split {w : ℝ≥0 → ℝ} (hw : Continuous w) (r : ℝ≥0) :
    posInd w = posInd (fun t => w (min t r)) * posInd (fun u => w (r + u)) := by
  have h1 : Continuous fun t : ℝ≥0 => w (min t r) := hw.comp (continuous_id.min continuous_const)
  have h2 : Continuous fun u : ℝ≥0 => w (r + u) := hw.comp (continuous_const.add continuous_id)
  by_cases hA : ∀ t, 0 < w t
  · rw [posInd_of_pos hw hA, posInd_of_pos h1 (fun t => hA _), posInd_of_pos h2 (fun u => hA _),
      one_mul]
  · rw [posInd_of_not hw hA]
    by_cases hB : ∀ t, 0 < w (min t r)
    · have hC : ¬ ∀ u, 0 < w (r + u) := by
        intro hC; apply hA; intro t
        rcases le_total t r with htr | hrt
        · simpa [min_eq_left htr] using hB t
        · have := hC (t - r); rwa [add_tsub_cancel_of_le hrt] at this
      rw [posInd_of_not h2 hC, mul_zero]
    · rw [posInd_of_not h1 hB, zero_mul]

theorem dpath_zero (hb : GoodBM b P) (σ μ : ℝ) (ω : Ω) : dpath σ μ b ω 0 = 0 := by
  simp [dpath, hb.zero ω]

/-- **Pathwise change of variables.** For a continuous path started at `0` with a last zero `L`
after which it is positive, `∫_{s>r} F(Ŷ(s+·)) ds = ∫_{m>0} 1{w > 0 on [m,∞)} F(w(m+r+·)) dm`. -/
theorem lintegral_postLast_eq_pathwise {w : ℝ≥0 → ℝ} (hw : Continuous w) (hw0 : w 0 = 0)
    (hbdd : BddAbove {t | w t = 0}) (hpos : ∀ t, lastPass w 0 < t → 0 < w t)
    (F : (ℝ≥0 → ℝ) → ℝ≥0∞) (r : ℝ≥0) :
    ∫⁻ s in Set.Ioi (r : ℝ), F (fun u => postLast w 0 (s.toNNReal + u)) =
      ∫⁻ m in Set.Ioi (0 : ℝ), posInd (fun t => w (m.toNNReal + t))
        * F (fun u => w (m.toNNReal + (r + u))) := by
  set L := lastPass w 0 with hL
  have hLmem : w L = 0 :=
    IsClosed.csSup_mem (isClosed_eq hw continuous_const) ⟨0, hw0⟩ hbdd
  set G : ℝ → ℝ≥0∞ := fun m => F (fun u => w (m.toNNReal + (r + u))) with hG
  have hind : ∀ m : ℝ, (Set.Ioi (0 : ℝ)).indicator
      (fun m => posInd (fun t => w (m.toNNReal + t)) * G m) m = (Set.Ioi (L : ℝ)).indicator G m := by
    intro m
    have hc : Continuous fun t : ℝ≥0 => w (m.toNNReal + t) :=
      hw.comp (continuous_const.add continuous_id)
    by_cases hLm : (L : ℝ) < m
    · have hm : (0 : ℝ) < m := lt_of_le_of_lt L.2 hLm
      rw [Set.indicator_of_mem (Set.mem_Ioi.2 hm), Set.indicator_of_mem (Set.mem_Ioi.2 hLm)]
      rw [posInd_of_pos hc (fun t => hpos _ ?_), one_mul]
      have : (L : ℝ) < ((m.toNNReal + t : ℝ≥0) : ℝ) := by
        rw [NNReal.coe_add, Real.coe_toNNReal _ hm.le]; linarith [NNReal.coe_nonneg t]
      exact_mod_cast this
    · rw [Set.indicator_of_notMem (by simpa using hLm) G]
      by_cases hm : (0 : ℝ) < m
      · rw [Set.indicator_of_mem (Set.mem_Ioi.2 hm)]
        refine (mul_eq_zero_of_left (posInd_of_not hc fun h => ?_) _)
        have hle : m.toNNReal ≤ L := by
          rw [Real.toNNReal_le_iff_le_coe]; exact not_lt.1 hLm
        have := h (L - m.toNNReal)
        rw [add_tsub_cancel_of_le hle, hLmem] at this
        exact lt_irrefl _ this
      · exact Set.indicator_of_notMem hm _
  have hR : ∫⁻ m in Set.Ioi (0 : ℝ), posInd (fun t => w (m.toNNReal + t)) * G m
      = ∫⁻ m in Set.Ioi (L : ℝ), G m := by
    rw [← lintegral_indicator measurableSet_Ioi, lintegral_congr hind,
      lintegral_indicator measurableSet_Ioi]
  rw [hR, lintegral_Ioi_add _ (r : ℝ), lintegral_Ioi_add G (L : ℝ)]
  refine setLIntegral_congr_fun measurableSet_Ioi ?_
  intro u hu
  have hu' : (0 : ℝ) < u := hu
  simp only [hG, postLast, sub_zero]
  congr 1
  funext v
  congr 1
  apply NNReal.eq
  simp only [NNReal.coe_add, Real.coe_toNNReal _ (by positivity : (0 : ℝ) ≤ (r : ℝ) + u),
    Real.coe_toNNReal _ (by positivity : (0 : ℝ) ≤ (L : ℝ) + u)]
  ring

/-- `∫ Φ d occ = ∫_{m>0} E Φ(Y_m) dm`. -/
theorem lintegral_occ_eq (hb : GoodBM b P) (σ μ : ℝ) {Φ : ℝ → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ x, Φ x ∂(occ σ μ) = ∫⁻ m in Set.Ioi (0 : ℝ), ∫⁻ ω, Φ (dpath σ μ b ω m.toNNReal) ∂P := by
  rw [occ, Measure.lintegral_bind (measurable_occKernel σ μ).aemeasurable hΦ.aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioi ?_
  intro m hm
  have h := (hasLaw_dpath hb σ μ hm).lintegral_comp hΦ.aemeasurable
  exact h.symm

/-- Measurability of `(x, ω) ↦ (u ↦ x + Y_ω(c u))`. -/
theorem measurable_addPath (hb : GoodBM b P) (σ μ : ℝ) (c : ℝ≥0 → ℝ≥0) :
    Measurable fun p : ℝ × Ω => fun u => p.1 + dpath σ μ b p.2 (c u) :=
  measurable_pi_iff.2 fun u => measurable_fst.add ((measurable_dpath hb σ μ (c u)).comp measurable_snd)

end QuantumZipper.Williams
