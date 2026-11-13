/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Loewner.CoreArc3d at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.CoreArc3c

/-!
# CORE_ARC, part 3d: continuity of a surjective monotone reparametrisation; tip convergence

Plan nodes "τ continuous" and "Tip convergence" of `blueprint/CORE_ARC_PLAN.md`.

## Main results

* `continuousOn_Icc_of_monotoneOn_of_surj`: a function monotone on `[0,T]` with `τ 0 = 0`,
  `τ T = 1` and `[0,1] ⊆ τ '' [0,T]` is continuous on `[0,T]`.
  Proof: extend by `x` below `0` and `1 + (x - T)` above `T`; the extension is monotone and
  surjective, hence continuous (`Monotone.continuous_of_surjective`).
* `tendsto_fwdMap_arc_tip`: if `K_r = γ(0, τ r]` for `r ∈ [0,T]`, with `τ` strictly increasing
  and `γ` injective on `[0,1]`, then `f_r (γ w) → 0` as `w ↓ τ r`, for `r ∈ (0,T)`.
  Proof: for `w ∈ (τ r, τ (r+η)]`, `γ w ∈ K_{r+η} \ K_r`, so local growth (T6,
  `norm_fwdMap_le_of_mem_diff`) gives `‖f_r (γ w)‖ ≤ 4 (osc_{[r,r+η]} A + √η)`.

## Sources

Route of `blueprint/CORE_ARC_PLAN.md` (the project's own; no published proof of this direction in
this form was found, see `handoff/CORE-2.md`). Own elementary proofs.
-/

noncomputable section

open Set Filter Topology Metric

namespace QuantumZipper

namespace CoreArc

variable {A : ℝ → ℝ}

/-- A monotone map of `[0,T]` onto `[0,1]` (with `τ 0 = 0`, `τ T = 1`) is continuous. -/
theorem continuousOn_Icc_of_monotoneOn_of_surj {τ : ℝ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hmono : MonotoneOn τ (Icc 0 T)) (h0 : τ 0 = 0) (h1 : τ T = 1)
    (himg : Icc (0 : ℝ) 1 ⊆ τ '' Icc 0 T) : ContinuousOn τ (Icc 0 T) := by
  classical
  have hτ : ∀ x, 0 ≤ x → x ≤ T → 0 ≤ τ x ∧ τ x ≤ 1 := fun x hx0 hxT =>
    ⟨h0 ▸ hmono ⟨le_rfl, hT⟩ ⟨hx0, hxT⟩ hx0, h1 ▸ hmono ⟨hx0, hxT⟩ ⟨hT, le_rfl⟩ hxT⟩
  set φ : ℝ → ℝ := fun x => if x < 0 then x else if x ≤ T then τ x else 1 + (x - T) with hφ
  have hφm : Monotone φ := by
    intro x y hxy
    simp only [hφ]
    split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 <;>
      first
      | linarith
      | exact hmono ⟨by linarith, by assumption⟩ ⟨by linarith, by assumption⟩ hxy
      | linarith [(hτ x (by linarith) (by assumption)).2]
      | linarith [(hτ y (by linarith) (by assumption)).1]
  have hsurj : Function.Surjective φ := by
    intro y
    rcases lt_or_ge y 0 with hy | hy
    · exact ⟨y, by simp [hφ, hy]⟩
    rcases le_or_gt y 1 with hy1 | hy1
    · obtain ⟨x, hx, rfl⟩ := himg ⟨hy, hy1⟩
      exact ⟨x, by simp [hφ, not_lt.2 hx.1, hx.2]⟩
    · refine ⟨T + (y - 1), ?_⟩
      have ha : ¬ T + (y - 1) < 0 := by linarith
      have hb : ¬ T + (y - 1) ≤ T := by linarith
      simp only [hφ, ha, hb, ↓reduceIte]
      ring
  refine (hφm.continuous_of_surjective hsurj).continuousOn.congr fun x hx => ?_
  simp [hφ, not_lt.2 hx.1, hx.2]

/-- **Tip convergence.** If the hulls are the initial subarcs `γ(0, τ r]`, with `τ` strictly
increasing, then the forward map sends the tip to the driving point: `f_r (γ w) → 0` as
`w ↓ τ r`. -/
theorem tendsto_fwdMap_arc_tip (hA : Continuous A) {T : ℝ} {γ : ℝ → ℂ}
    (hγi : InjOn γ (Icc 0 1)) {τ : ℝ → ℝ} (hτ : StrictMonoOn τ (Icc 0 T))
    (hτ1 : ∀ r ∈ Icc (0 : ℝ) T, τ r ∈ Icc (0 : ℝ) 1)
    (hK : ∀ r ∈ Icc (0 : ℝ) T, fwdHull A r = γ '' Ioc 0 (τ r)) {r : ℝ} (hr : r ∈ Ioo 0 T) :
    Tendsto (fun w => fwdMap A r (γ w)) (𝓝[>] (τ r)) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hAδ⟩ := Metric.continuousAt_iff.1 (hA.continuousAt (x := r)) (ε / 16)
    (by positivity)
  set η := min (min (δ / 2) (T - r)) ((ε / 8) ^ 2 / 2) with hη
  have hTr : 0 < T - r := by linarith [hr.2]
  have hη0 : 0 < η := by positivity
  have hηδ : η ≤ δ / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hηT : η ≤ T - r := (min_le_left _ _).trans (min_le_right _ _)
  have hηe : η ≤ (ε / 8) ^ 2 / 2 := min_le_right _ _
  have hrI : r ∈ Icc (0 : ℝ) T := ⟨hr.1.le, hr.2.le⟩
  have hrηI : r + η ∈ Icc (0 : ℝ) T := ⟨by linarith [hr.1], by linarith⟩
  have hlt : τ r < τ (r + η) := hτ hrI hrηI (by linarith)
  filter_upwards [Ioc_mem_nhdsGT hlt] with w hw
  have hτr0 := (hτ1 r hrI).1
  have hw1 : w ≤ 1 := hw.2.trans (hτ1 _ hrηI).2
  have hz : γ w ∈ fwdHull A (r + η) := by
    rw [hK _ hrηI]
    exact ⟨w, ⟨by linarith [hw.1], hw.2⟩, rfl⟩
  have hzr : γ w ∉ fwdHull A r := by
    rw [hK _ hrI]
    rintro ⟨v, hv, hvw⟩
    have := hγi ⟨hv.1.le, hv.2.trans (hτ1 r hrI).2⟩ ⟨by linarith [hw.1], hw1⟩ hvw
    linarith [hv.2, hw.1]
  have hM : ∀ t ∈ Icc (0 : ℝ) η, |A (r + t) - A r| ≤ ε / 8 := by
    intro t ht
    have h1 := hAδ (x := r + t) (by
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith [ht.1, ht.2])
    rw [Real.dist_eq] at h1
    linarith
  have hb := norm_fwdMap_le_of_mem_diff hA hr.1.le hη0.le hM hz hzr
  have hsq : Real.sqrt η < ε / 8 :=
    (Real.sqrt_lt' (by positivity)).2 (by nlinarith)
  rw [dist_zero_right]
  linarith

end CoreArc

end QuantumZipper
