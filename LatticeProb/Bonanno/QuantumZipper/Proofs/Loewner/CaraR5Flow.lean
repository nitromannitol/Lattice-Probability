/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Loewner.CaraR5Flow at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Loewner.CaraR1

/-!
# EXT-CA node R5 (real-flow part): the flow at the ends of the swallowed interval

Blueprint `blueprint/EXT_CA_BLUEPRINT.md` §3.R, node R5 (step 3). If `b > W 0` has finite
hitting time `τ` and every `x > b` survives up to time `τ`, then `u^x_τ → 0` as `x ↓ b`; and
symmetrically at a left end `a < W 0`.

Source: Lawler, *Conformally Invariant Processes in the Plane* (2005), §4.1, p. 80 (the real
Loewner flow and the swallowing times). The argument follows the blueprint (R1/R5): compare
`u^x_τ ≤ u^x_s + (W s - W τ)` for `s < τ` close to `τ` (`realRevMap_le_add`), and use continuity
of `x ↦ u^x_s` at `b` together with `u^b_s → 0` as `s ↑ τ` (`tendsto_realRevMap_hitTime`).
The left end is obtained by the reflection `W ↦ -W`.
-/

open Set Filter
open scoped Topology ENNReal

namespace QuantumZipper

namespace CaraR

open RealLine

variable {W : ℝ → ℝ}

/-- **R5 (right end).** For `b > W 0` with hitting time `τ`, if every `x > b` survives to time
`τ`, then `u^x_τ → 0` as `x ↓ b`. -/
theorem tendsto_realRevMap_right_end (hW : Continuous W) {b τ : ℝ} (hb : W 0 < b)
    (hτ : realHitTime W b = ENNReal.ofReal τ) (hright : ∀ x, b < x → x ∉ swallowedSet W τ) :
    Tendsto (fun x => realRevMap W τ x) (𝓝[>] b) (𝓝 0) := by
  have hτpos : 0 < τ := by
    have := realHitTime_pos hW hb.ne'
    rw [hτ] at this
    exact ENNReal.ofReal_pos.1 this
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- choose `s < τ` with `u^b_s < ε/3` and `|W s - W τ| < ε/3`
  have h1 : ∀ᶠ s in 𝓝[<] τ, realRevMap W s b < ε / 3 :=
    (tendsto_realRevMap_hitTime hW hb hτ).eventually (gt_mem_nhds (by linarith))
  have h2 : ∀ᶠ s in 𝓝[<] τ, |W s - W τ| < ε / 3 := by
    have := (hW.tendsto τ).eventually (Metric.ball_mem_nhds (W τ) (by linarith : 0 < ε / 3))
    exact nhdsWithin_le_nhds (this.mono fun s hs => by rwa [← Real.dist_eq])
  have h3 : ∀ᶠ s in 𝓝[<] τ, 0 < s := nhdsWithin_le_nhds (lt_mem_nhds hτpos)
  have h4 : ∀ᶠ s in 𝓝[<] τ, s < τ := self_mem_nhdsWithin
  obtain ⟨s, hs1, hs2, hs3, hs4⟩ := (h1.and (h2.and (h3.and h4))).exists
  have hbS : b ∉ swallowedSet W s := by
    rw [← ofReal_lt_realHitTime_iff hW hs3.le, hτ]
    exact (ENNReal.ofReal_lt_ofReal_iff hτpos).2 hs4
  have hc := continuousAt_realRevMap hW hs3.le hbS
  have h5 : ∀ᶠ x in 𝓝 b, realRevMap W s x < realRevMap W s b + ε / 3 :=
    hc.eventually (gt_mem_nhds (by linarith))
  filter_upwards [nhdsWithin_le_nhds h5, self_mem_nhdsWithin] with x hx5 hxb
  have hxb' : b < x := hxb
  have hxS := hright x hxb'
  obtain ⟨u, hu⟩ := not_mem_swallowedSet_iff.1 hxS
  have hpos : 0 < realRevMap W τ x := by
    rw [realRevMap_eq hW hu hτpos.le le_rfl]
    exact pos_of_isRealRevSol hu hτpos.le (by linarith) τ ⟨hτpos.le, le_rfl⟩
  have hle := realRevMap_le_add hW ⟨hs3.le, hs4.le⟩ (by linarith) hxS
  rw [Real.dist_eq, sub_zero, abs_of_pos hpos]
  have := (abs_lt.1 hs2).2
  linarith

/-- **R5 (left end).** For `a < W 0` with hitting time `τ`, if every `x < a` survives to time
`τ`, then `u^x_τ → 0` as `x ↑ a`. Obtained from the right end by the reflection `W ↦ -W`. -/
theorem tendsto_realRevMap_left_end (hW : Continuous W) {a τ : ℝ} (ha : a < W 0)
    (hτ : realHitTime W a = ENNReal.ofReal τ) (hleft : ∀ x, x < a → x ∉ swallowedSet W τ) :
    Tendsto (fun x => realRevMap W τ x) (𝓝[<] a) (𝓝 0) := by
  have ha' : (-W) 0 < -a := by simp only [Pi.neg_apply]; linarith
  have hτ' : realHitTime (-W) (-a) = ENNReal.ofReal τ := by rw [realHitTime_neg, hτ]
  have hright : ∀ x, -a < x → x ∉ swallowedSet (-W) τ := by
    intro x hx
    rw [mem_swallowedSet_neg_iff]
    exact hleft (-x) (by linarith)
  have hR := tendsto_realRevMap_right_end hW.neg ha' hτ' hright
  have hneg : Tendsto (fun x : ℝ => -x) (𝓝[<] a) (𝓝[>] (-a)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((continuous_neg.tendsto a).mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact neg_lt_neg (show x < a from hx)
  have hlim := (hR.comp hneg).neg
  rw [neg_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hxS : ∃ u, IsRealRevSol W (- -x) τ u := by
    rw [neg_neg]; exact not_mem_swallowedSet_iff.1 (hleft x hx)
  have hτ0 : 0 ≤ τ := by
    have := realHitTime_pos hW ha.ne
    rw [hτ] at this
    exact (ENNReal.ofReal_pos.1 this).le
  simp only [Function.comp]
  rw [realRevMap_neg hW hτ0 hxS, neg_neg, neg_neg]

end CaraR

end QuantumZipper
