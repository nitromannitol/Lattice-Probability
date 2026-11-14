import Mathlib
import LatticeProb.Prob.CrossingTimesClock3

/-!
# The inverse crossing clock and the recovery of a time-changed path

If `X = f ∘ τ` for an increasing homeomorphism `τ` of `[0, ∞)`, and the crossing clock of `f` is
the identity, then the crossing clock of `X` is `τ` (the crossing count is invariant under
reparametrisation).  Hence the inverse clock of `X` is `τ⁻¹`, and reading `X` in the time scale of
its own clock returns `f`.  The same holds after a shift of `X` by `a = τ⁻¹ t`, which is a
reparametrisation of the shift of `f` by `t`.

* `clockInv c t = inf {u : t ≤ c u}` and `clockPath m f t = f (clockInv (crossClock m f) t)`;
* `crossClock_comp`, `crossClock_comp_of_clock_id`: the clock of `f ∘ τ`;
* `clockInv_comp`, `clockPath_comp`: recovery of `τ⁻¹` and of `f`;
* `clockInv_shift`: for `τ a = t`, `A (t + s) = a + A_{θ_a X} (s)` and the clock-read path of the
  shifted path is the shift of the clock-read path.
-/

open Filter Topology
open scoped NNReal ENNReal

noncomputable section

namespace LatticeProb

variable {E : Type*} [PseudoMetricSpace E]

/-- **Inverse of a clock.**  `clockInv c t = inf {u : t ≤ c u}` in `ℝ≥0∞` (`⊤` if the set is
empty). -/
def clockInv (c : ℝ≥0 → ℝ≥0∞) (t : ℝ≥0) : ℝ≥0∞ :=
  ⨅ (u : ℝ≥0) (_ : (t : ℝ≥0∞) ≤ c u), (u : ℝ≥0∞)

/-- **The path read in the time scale of its crossing clock**: `t ↦ f (A_t)` where
`A_t = clockInv (crossClock m f) t`. -/
def clockPath (m : ℝ≥0∞) (f : ℝ≥0 → E) (t : ℝ≥0) : E :=
  f (clockInv (crossClock m f) t).toNNReal

theorem clockInv_coe_eq {τ : ℝ≥0 → ℝ≥0} (hτm : StrictMono τ) {σ t : ℝ≥0} (h : τ σ = t) :
    clockInv (fun u => (τ u : ℝ≥0∞)) t = σ := by
  refine le_antisymm (iInf₂_le_of_le σ (by show (t : ℝ≥0∞) ≤ (τ σ : ℝ≥0∞); rw [h]) le_rfl) (le_iInf₂ fun u hu => ?_)
  have h1 : τ σ ≤ τ u := by
    rw [h]
    have hu' : (t : ℝ≥0∞) ≤ (τ u : ℝ≥0∞) := hu
    exact_mod_cast hu'
  exact_mod_cast hτm.le_iff_le.1 h1

/-- A continuous unbounded `τ` with `τ 0 = 0` takes every value. -/
theorem exists_eq_of_unbounded {τ : ℝ≥0 → ℝ≥0} (hτc : Continuous τ) (hτ0 : τ 0 = 0)
    (hτu : Tendsto τ atTop atTop) (t : ℝ≥0) : ∃ σ, τ σ = t := by
  obtain ⟨u, hu⟩ := (hτu.eventually_ge_atTop t).exists
  have h := intermediate_value_Icc (by positivity : (0 : ℝ≥0) ≤ u) hτc.continuousOn
  have ht : t ∈ Set.Icc (τ 0) (τ u) := ⟨by rw [hτ0]; positivity, hu⟩
  obtain ⟨σ, -, hσ⟩ := h ht
  exact ⟨σ, hσ⟩

/-- The crossing clock of a reparametrised path. -/
theorem crossClock_comp {τ : ℝ≥0 → ℝ≥0} (hτc : Continuous τ) (hτm : StrictMono τ)
    (hτ0 : τ 0 = 0) (m : ℝ≥0∞) (f : ℝ≥0 → E) (u : ℝ≥0) :
    crossClock m (f ∘ τ) u = crossClock m f (τ u) := by
  unfold crossClock
  simp only [crossCount_comp hτc hτm hτ0]

/-- If the clock of `f` is the identity, the clock of `f ∘ τ` is `τ`. -/
theorem crossClock_comp_of_clock_id {τ : ℝ≥0 → ℝ≥0} (hτc : Continuous τ) (hτm : StrictMono τ)
    (hτ0 : τ 0 = 0) {m : ℝ≥0∞} {f : ℝ≥0 → E} (hf : ∀ u, crossClock m f u = u) :
    crossClock m (f ∘ τ) = fun u => (τ u : ℝ≥0∞) := by
  funext u
  rw [crossClock_comp hτc hτm hτ0, hf]

/-- The inverse clock of `f ∘ τ` is `τ⁻¹`. -/
theorem clockInv_comp {τ : ℝ≥0 → ℝ≥0} (hτc : Continuous τ) (hτm : StrictMono τ)
    (hτ0 : τ 0 = 0) {m : ℝ≥0∞} {f : ℝ≥0 → E} (hf : ∀ u, crossClock m f u = u) {σ t : ℝ≥0}
    (h : τ σ = t) : clockInv (crossClock m (f ∘ τ)) t = σ := by
  rw [crossClock_comp_of_clock_id hτc hτm hτ0 hf]
  exact clockInv_coe_eq hτm h

/-- Reading `f ∘ τ` in the time scale of its own clock returns `f`. -/
theorem clockPath_comp {τ : ℝ≥0 → ℝ≥0} (hτc : Continuous τ) (hτm : StrictMono τ)
    (hτ0 : τ 0 = 0) {m : ℝ≥0∞} {f : ℝ≥0 → E} (hf : ∀ u, crossClock m f u = u) {σ t : ℝ≥0}
    (h : τ σ = t) : clockPath m (f ∘ τ) t = f t := by
  unfold clockPath
  rw [clockInv_comp hτc hτm hτ0 hf h, ENNReal.toNNReal_coe, Function.comp_apply, h]

/-- The time change seen from the time `a`: `v ↦ τ (a + v) - τ a`. -/
def shiftTime (τ : ℝ≥0 → ℝ≥0) (a v : ℝ≥0) : ℝ≥0 := τ (a + v) - τ a

theorem shiftTime_zero (τ : ℝ≥0 → ℝ≥0) (a : ℝ≥0) : shiftTime τ a 0 = 0 := by
  simp [shiftTime]

theorem continuous_shiftTime {τ : ℝ≥0 → ℝ≥0} (hτc : Continuous τ) (a : ℝ≥0) :
    Continuous (shiftTime τ a) :=
  (hτc.comp (continuous_const.add continuous_id)).sub continuous_const

theorem strictMono_shiftTime {τ : ℝ≥0 → ℝ≥0} (hτm : StrictMono τ) (a : ℝ≥0) :
    StrictMono (shiftTime τ a) := fun _ _ hvw =>
  tsub_lt_tsub_right_of_le (hτm.monotone le_self_add) (hτm (add_lt_add_right hvw a))

theorem add_shiftTime {τ : ℝ≥0 → ℝ≥0} (hτm : StrictMono τ) (a v : ℝ≥0) :
    τ a + shiftTime τ a v = τ (a + v) :=
  add_tsub_cancel_of_le (hτm.monotone le_self_add)

/-- **Shift identity at the inverse clock.**  Let `X = f ∘ τ`, with `τ` an increasing
homeomorphism of `[0, ∞)`, and let `τ a = t`.  If the clocks of `f` and of its shift by `t` are the
identity, then the inverse clock of `X` satisfies `A (t + s) = a + A_{θ_a X} (s)`, and the
clock-read path of the shift of `X` by `a` is the shift of the clock-read path of `X`. -/
theorem clockInv_shift {τ : ℝ≥0 → ℝ≥0} (hτc : Continuous τ) (hτm : StrictMono τ)
    (hτ0 : τ 0 = 0) (hτu : Tendsto τ atTop atTop) {m : ℝ≥0∞} {f : ℝ≥0 → E}
    (hf : ∀ u, crossClock m f u = u) {a : ℝ≥0}
    (ht : ∀ u, crossClock m (fun w => f (τ a + w)) u = u) (s : ℝ≥0) :
    clockInv (crossClock m (f ∘ τ)) (τ a + s) =
        (a : ℝ≥0∞) + clockInv (crossClock m (fun v => (f ∘ τ) (a + v))) s ∧
      clockPath m (fun v => (f ∘ τ) (a + v)) s = clockPath m (f ∘ τ) (τ a + s) := by
  have hc' := continuous_shiftTime hτc a
  have hm' := strictMono_shiftTime hτm a
  have h0' := shiftTime_zero τ a
  have hX' : (fun v => (f ∘ τ) (a + v)) = (fun w => f (τ a + w)) ∘ shiftTime τ a := by
    funext v
    simp only [Function.comp_apply, add_shiftTime hτm]
  have hclock' : crossClock m (fun v => (f ∘ τ) (a + v)) = fun u => (shiftTime τ a u : ℝ≥0∞) := by
    rw [hX']
    exact crossClock_comp_of_clock_id hc' hm' h0' ht
  obtain ⟨σ, hσ⟩ := exists_eq_of_unbounded hτc hτ0 hτu (τ a + s)
  have haσ : a ≤ σ := hτm.le_iff_le.1 (by rw [hσ]; exact le_self_add)
  obtain ⟨v, hv⟩ : ∃ v, a + v = σ := ⟨σ - a, add_tsub_cancel_of_le haσ⟩
  have hτ'v : shiftTime τ a v = s := by
    have h1 := add_shiftTime hτm a v
    rw [hv, hσ] at h1
    exact add_left_cancel h1
  have hinv : clockInv (fun u => (shiftTime τ a u : ℝ≥0∞)) s = v := clockInv_coe_eq hm' hτ'v
  constructor
  · rw [clockInv_comp hτc hτm hτ0 hf hσ, hclock', hinv, ← hv]
    simp
  · rw [clockPath_comp hτc hτm hτ0 hf hσ]
    unfold clockPath
    rw [hclock', hinv, ENNReal.toNNReal_coe]
    show f (τ (a + v)) = f (τ a + s)
    rw [hv, hσ]

end LatticeProb
