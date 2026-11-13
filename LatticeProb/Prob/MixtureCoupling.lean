import Mathlib

/-!
# Maximal couplings on a countable set and couplings of mixtures

* `LatticeProb.exists_coupling_countable`: two probability vectors `p, q` on a countable set `V`
  have a coupling `π` on `V × V` whose off-diagonal mass is at most `1 - ∑ min (p v) (q v)`.
* `LatticeProb.one_sub_tsum_min_le`: if `∑_{v ∈ S} p v ≤ ∑_{v ∈ S} q v + a` for every `S`, then
  `1 - ∑ min (p v) (q v) ≤ a`; so a total variation bound `a` bounds the off-diagonal mass.
* `LatticeProb.exists_coupling_mixture`: let `μ = ∑ p v • α v` and `ν = ∑ q v • β v` be mixtures of
  probability measures indexed by the countable set `V`.  If for each `v` with `p v ≠ 0` and
  `q v ≠ 0` there is a coupling `c v` of `α v` and `β v` carried by a measurable event `E`, then
  there is a coupling of `μ` and `ν` that gives `Eᶜ` mass at most `1 - ∑ min (p v) (q v)`.

The last statement is the abstract form of coupling two Markov chains started from different
points: after the chains first reach a set, with laws `p` and `q` for the position of arrival, the
positions are coupled maximally, and the continuations from equal positions are coupled to agree.
-/

open MeasureTheory

open scoped ENNReal

namespace LatticeProb

section Discrete

variable {V : Type*}

lemma tsum_ite_eq_left [DecidableEq V] (v : V) (c : ℝ≥0∞) :
    ∑' v', (if v = v' then c else 0) = c := by
  rw [tsum_eq_single v (fun b hb => by simp [Ne.symm hb])]
  simp

lemma tsum_ite_eq_right [DecidableEq V] (v' : V) (c : V → ℝ≥0∞) :
    ∑' v, (if v = v' then c v else 0) = c v' := by
  rw [tsum_eq_single v' (fun b hb => by simp [hb])]
  simp

/-- **Maximal coupling on a countable set.**  Two probability vectors `p, q` on a countable set
have a coupling `π` on `V × V` with marginals `p` and `q` whose off-diagonal mass is at most
`1 - ∑ min (p v) (q v)`. -/
theorem exists_coupling_countable [Countable V] [DecidableEq V] (p q : V → ℝ≥0∞)
    (hp : ∑' v, p v = 1) (hq : ∑' v, q v = 1) :
    ∃ π : V × V → ℝ≥0∞, (∀ v, ∑' v', π (v, v') = p v) ∧ (∀ v', ∑' v, π (v, v') = q v') ∧
      ∑' w : V × V, (if w.1 = w.2 then 0 else π w) ≤ 1 - ∑' v, min (p v) (q v) := by
  classical
  set m : V → ℝ≥0∞ := fun v => min (p v) (q v) with hm
  set δ : ℝ≥0∞ := 1 - ∑' v, m v with hδ
  have hmp : ∀ v, m v ≤ p v := fun v => min_le_left _ _
  have hmq : ∀ v, m v ≤ q v := fun v => min_le_right _ _
  have hs : ∑' v, m v ≤ 1 := hp ▸ ENNReal.tsum_le_tsum hmp
  have hsne : ∑' v, m v ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hs
  have hpsum : ∑' v, (p v - m v) = δ := by
    have h1 : ∑' v, p v = ∑' v, m v + ∑' v, (p v - m v) := by
      rw [← ENNReal.tsum_add]
      exact tsum_congr fun v => (add_tsub_cancel_of_le (hmp v)).symm
    rw [hp] at h1
    exact (ENNReal.sub_eq_of_eq_add_rev hsne h1).symm
  have hqsum : ∑' v, (q v - m v) = δ := by
    have h1 : ∑' v, q v = ∑' v, m v + ∑' v, (q v - m v) := by
      rw [← ENNReal.tsum_add]
      exact tsum_congr fun v => (add_tsub_cancel_of_le (hmq v)).symm
    rw [hq] at h1
    exact (ENNReal.sub_eq_of_eq_add_rev hsne h1).symm
  have hδtop : δ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hp'le : ∀ v, p v - m v ≤ δ := fun v => by
    rw [← hpsum]; exact ENNReal.le_tsum (f := fun v => p v - m v) v
  have hq'le : ∀ v, q v - m v ≤ δ := fun v => by
    rw [← hqsum]; exact ENNReal.le_tsum (f := fun v => q v - m v) v
  -- the sum of the cross term over one coordinate
  have hrowsum : ∀ v, ∑' v', (p v - m v) * (q v' - m v') * δ⁻¹ = p v - m v := by
    intro v
    by_cases h0 : δ = 0
    · have : p v - m v = 0 := le_antisymm ((hp'le v).trans h0.le) bot_le
      simp [this]
    · rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, hqsum, mul_assoc,
        ENNReal.mul_inv_cancel h0 hδtop, mul_one]
  have hcolsum : ∀ v', ∑' v, (p v - m v) * (q v' - m v') * δ⁻¹ = q v' - m v' := by
    intro v'
    by_cases h0 : δ = 0
    · have : q v' - m v' = 0 := le_antisymm ((hq'le v').trans h0.le) bot_le
      simp [this]
    · rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right, hpsum, mul_right_comm,
        ENNReal.mul_inv_cancel h0 hδtop, one_mul]
  refine ⟨fun w => (if w.1 = w.2 then m w.1 else 0) + (p w.1 - m w.1) * (q w.2 - m w.2) * δ⁻¹,
    ?_, ?_, ?_⟩
  · intro v
    simp only
    rw [ENNReal.tsum_add, tsum_ite_eq_left, hrowsum, add_tsub_cancel_of_le (hmp v)]
  · intro v'
    simp only
    rw [ENNReal.tsum_add, tsum_ite_eq_right, hcolsum, add_tsub_cancel_of_le (hmq v')]
  · calc ∑' w : V × V, (if w.1 = w.2 then 0 else
            (if w.1 = w.2 then m w.1 else 0) + (p w.1 - m w.1) * (q w.2 - m w.2) * δ⁻¹)
        ≤ ∑' w : V × V, (p w.1 - m w.1) * (q w.2 - m w.2) * δ⁻¹ := by
          refine ENNReal.tsum_le_tsum fun w => ?_
          by_cases h : w.1 = w.2
          · simp [h]
          · simp [h]
      _ = δ := by
          rw [ENNReal.tsum_prod (f := fun v v' => (p v - m v) * (q v' - m v') * δ⁻¹)]
          rw [tsum_congr hrowsum, hpsum]

/-- If `∑_{v ∈ S} p v ≤ ∑_{v ∈ S} q v + a` for every `S` and `p` has total mass `1`, then
`1 - ∑ min (p v) (q v) ≤ a`: the total variation bound controls the off-diagonal mass of a
maximal coupling. -/
theorem one_sub_tsum_min_le (p q : V → ℝ≥0∞) (hp : ∑' v, p v = 1) {a : ℝ≥0∞}
    (h : ∀ S : Set V, ∑' v, S.indicator p v ≤ ∑' v, S.indicator q v + a) :
    1 - ∑' v, min (p v) (q v) ≤ a := by
  set S : Set V := {v | q v < p v} with hS
  have hmin : ∀ v, min (p v) (q v) = S.indicator q v + Sᶜ.indicator p v := by
    intro v
    by_cases hv : v ∈ S
    · have hv' : q v < p v := hv
      simp [Set.indicator_of_mem hv, Set.indicator_of_notMem (Set.notMem_compl_iff.2 hv),
        min_eq_right hv'.le]
    · have hv' : p v ≤ q v := not_lt.1 hv
      simp [Set.indicator_of_notMem hv, Set.indicator_of_mem (Set.mem_compl hv),
        min_eq_left hv']
  rw [tsub_le_iff_right]
  have h1 : ∑' v, p v = ∑' v, S.indicator p v + ∑' v, Sᶜ.indicator p v := by
    rw [← ENNReal.tsum_add]
    exact tsum_congr fun v => (congrFun (Set.indicator_self_add_compl S p) v).symm
  have h2 : ∑' v, min (p v) (q v) = ∑' v, S.indicator q v + ∑' v, Sᶜ.indicator p v := by
    rw [← ENNReal.tsum_add]
    exact tsum_congr hmin
  calc 1 = ∑' v, S.indicator p v + ∑' v, Sᶜ.indicator p v := hp ▸ h1
    _ ≤ (∑' v, S.indicator q v + a) + ∑' v, Sᶜ.indicator p v := by gcongr; exact h S
    _ = a + ∑' v, min (p v) (q v) := by rw [h2]; ring

end Discrete

section Mixture

variable {V Ω₁ Ω₂ : Type*} [Countable V] [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]

/-- **Coupling of mixtures.**  Let `μ = ∑ p v • α v` and `ν = ∑ q v • β v` be mixtures of
probability measures indexed by a countable set `V`, `p` and `q` probability vectors.  Suppose that
for each `v` with `p v ≠ 0` and `q v ≠ 0`, `c v` is a coupling of `α v` and `β v` carried by the
measurable event `E`.  Then
there is a coupling `ρ` of `μ` and `ν` such that `ρ Eᶜ ≤ 1 - ∑ min (p v) (q v)`. -/
theorem exists_coupling_mixture (p q : V → ℝ≥0∞) (hp : ∑' v, p v = 1) (hq : ∑' v, q v = 1)
    (α : V → Measure Ω₁) (β : V → Measure Ω₂) [∀ v, IsProbabilityMeasure (α v)]
    [∀ v, IsProbabilityMeasure (β v)] (c : V → Measure (Ω₁ × Ω₂))
    (hc₁ : ∀ v, (c v).map Prod.fst = α v) (hc₂ : ∀ v, (c v).map Prod.snd = β v)
    {E : Set (Ω₁ × Ω₂)} (hE : MeasurableSet E) (hcE : ∀ v, p v ≠ 0 → q v ≠ 0 → c v Eᶜ = 0) :
    ∃ ρ : Measure (Ω₁ × Ω₂), ρ.map Prod.fst = Measure.sum (fun v => p v • α v) ∧
      ρ.map Prod.snd = Measure.sum (fun v => q v • β v) ∧
      ρ Eᶜ ≤ 1 - ∑' v, min (p v) (q v) := by
  classical
  obtain ⟨π, hrow, hcol, hoff⟩ := exists_coupling_countable p q hp hq
  let c' : V × V → Measure (Ω₁ × Ω₂) := fun w =>
    if w.1 = w.2 then c w.1 else (α w.1).prod (β w.2)
  have hc'pos : ∀ w : V × V, w.1 = w.2 → c' w = c w.1 := fun w h => by simp [c', h]
  have hc'neg : ∀ w : V × V, ¬ w.1 = w.2 → c' w = (α w.1).prod (β w.2) := fun w h => by
    simp [c', h]
  have hc'1 : ∀ w S, MeasurableSet S → c' w (Prod.fst ⁻¹' S) = α w.1 S := by
    intro w S hS
    by_cases h : w.1 = w.2
    · rw [hc'pos w h, ← Measure.map_apply measurable_fst hS, hc₁]
    · rw [hc'neg w h, ← Set.prod_univ, Measure.prod_prod]
      simp
  have hc'2 : ∀ w S, MeasurableSet S → c' w (Prod.snd ⁻¹' S) = β w.2 S := by
    intro w S hS
    by_cases h : w.1 = w.2
    · rw [hc'pos w h, ← Measure.map_apply measurable_snd hS, hc₂, h]
    · rw [hc'neg w h, ← Set.univ_prod, Measure.prod_prod]
      simp
  refine ⟨Measure.sum (fun w => π w • c' w), ?_, ?_, ?_⟩
  · ext S hS
    rw [Measure.map_apply measurable_fst hS, Measure.sum_apply _ (measurable_fst hS),
      Measure.sum_apply _ hS]
    simp only [Measure.smul_apply, smul_eq_mul]
    calc ∑' w : V × V, π w * c' w (Prod.fst ⁻¹' S) = ∑' w : V × V, π w * α w.1 S :=
          tsum_congr fun w => by rw [hc'1 w S hS]
      _ = ∑' v, ∑' v', π (v, v') * α v S :=
          ENNReal.tsum_prod (f := fun v v' => π (v, v') * α v S)
      _ = ∑' v, p v * α v S := tsum_congr fun v => by rw [ENNReal.tsum_mul_right, hrow]
  · ext S hS
    rw [Measure.map_apply measurable_snd hS, Measure.sum_apply _ (measurable_snd hS),
      Measure.sum_apply _ hS]
    simp only [Measure.smul_apply, smul_eq_mul]
    calc ∑' w : V × V, π w * c' w (Prod.snd ⁻¹' S) = ∑' w : V × V, π w * β w.2 S :=
          tsum_congr fun w => by rw [hc'2 w S hS]
      _ = ∑' v, ∑' v', π (v, v') * β v' S :=
          ENNReal.tsum_prod (f := fun v v' => π (v, v') * β v' S)
      _ = ∑' v', ∑' v, π (v, v') * β v' S := ENNReal.tsum_comm
      _ = ∑' v', q v' * β v' S := tsum_congr fun v' => by rw [ENNReal.tsum_mul_right, hcol]
  · rw [Measure.sum_apply _ hE.compl]
    simp only [Measure.smul_apply, smul_eq_mul]
    refine le_trans (ENNReal.tsum_le_tsum fun w => ?_) hoff
    by_cases h : w.1 = w.2
    · have hpw : π w ≤ p w.1 := by
        rw [← hrow w.1]; exact ENNReal.le_tsum (f := fun v' => π (w.1, v')) w.2
      have hqw : π w ≤ q w.2 := by
        rw [← hcol w.2]; exact ENNReal.le_tsum (f := fun v => π (v, w.2)) w.1
      rw [hc'pos w h]
      by_cases hz : π w = 0
      · simp [hz]
      · have hp0 : p w.1 ≠ 0 := by
          intro h0
          apply hz
          rw [h0] at hpw
          exact nonpos_iff_eq_zero.1 hpw
        have hq0 : q w.2 ≠ 0 := by
          intro h0
          apply hz
          rw [h0] at hqw
          exact nonpos_iff_eq_zero.1 hqw
        rw [hcE w.1 hp0 (by rw [h]; exact hq0)]
        simp [h]
    · rw [hc'neg w h]
      simp only [h, ↓reduceIte]
      calc π w * ((α w.1).prod (β w.2)) Eᶜ ≤ π w * 1 := by gcongr; exact prob_le_one
        _ = π w := mul_one _

end Mixture

end LatticeProb
