/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.ChainUnion at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.ChainUnionAux

/-!
# Node `U49` (`Draft.ChainUnionBound`): the chain union bound of Section 4.3

We prove `Draft.ChainUnionBound` with `κ = π² / 8` from `Draft.SegCombLaw`.

For a fixed chain record `ρ` of length `l` (bins `kᵢ`):

* the supremum over the product of the configuration families of `Σ cfgVal` is approximated
  from below by maxima over finite product families taken from countable dense sequences
  (`exists_dense_seq_config`, using continuity of `cfgVal (h ε · ω)` in the vertices), and the
  outer measure is continuous from below (`chain_bound_family`);
* for a finite product family, the maximum is a finite maximum of affine functions of a
  Gaussian vector (`SegCombLaw` applied to `pcomb`), its mean is `Σ E max ≤ Σ m(kᵢ)` and each
  variance is `≤ Σ v(kᵢ)`; the Maurey–Pisier bound `MaxConc` and Chernoff give
  `P(S > β) ≤ exp(-t β + t Σ m + κ t² Σ v)` (`chain_bound_finite`);
* the union bound over chain records, with the counting hypotheses (`sum_chain_le`,
  `sum_ite_le_tsum`), gives `exp(-t B l) Z(t)^l = e^{-l}`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Real
open scoped RealInnerProductSpace Classical

namespace LQGDimension

open Blueprint.Draft ChainUnion

/-- **Node `U49`**: the chain union bound, with `κ = π² / 8`, from the segment law `P1`. -/
theorem chainUnionBound_of (hP1 : SegCombLaw) : ChainUnionBound := by
  refine ⟨π ^ 2 / 8, by positivity, ?_⟩
  intro Ω _ P h hG ε hε δ hδ RS N m v hNroot hNnext hpos hmean hvar t ht hsum l
  letI : Fintype RS.Rec := RS.fintype
  set Z := chainZ N m v (π ^ 2 / 8) t with hZdef
  set β : ℝ := (Real.log Z + 1) / t * l with hβ
  -- the case `l = 0`: the event is empty
  rcases Nat.eq_zero_or_pos l with hl0 | hl
  · subst hl0
    refine le_trans (measure_mono (t := ∅) ?_) (by simp)
    rintro ω ⟨r, c, -, -, hlt⟩
    simp [hβ] at hlt
  set a : ℕ → ℝ := fun k => Real.exp (t * m k + π ^ 2 / 8 * t ^ 2 * v k) with ha
  have ha0 : ∀ k, 0 ≤ a k := fun k => (Real.exp_pos _).le
  have hN0 : ∀ k, 0 ≤ N k := fun k => le_trans (Nat.cast_nonneg _) (hNroot k)
  have hZ : Z = ∑' k, N k * a k := rfl
  have hZ0 : 0 ≤ Z := by
    rw [hZ]
    exact tsum_nonneg fun k => mul_nonneg (hN0 k) (ha0 k)
  -- chain records as tuples
  let chainF : (Fin l → RS.Rec) → Prop := fun ρ =>
    ∃ r : ℕ → RS.Rec, RS.IsChain r l ∧ ∀ i : Fin l, r i = ρ i
  let T : Finset (Fin l → RS.Rec) := Finset.univ.filter chainF
  let E : (Fin l → RS.Rec) → Set Ω := fun ρ =>
    {ω | ∃ c : Fin l → Config, (∀ i, c i ∈ RS.family (ρ i)) ∧
      β < ∑ i, cfgVal (fun z => h ε z ω) δ (RS.bin (ρ i)) (c i)}
  -- step 1: the event is covered by the chain events
  have hcover : {ω | ∃ (r : ℕ → RS.Rec) (c : ℕ → Config), RS.IsChain r l ∧
      (∀ i < l, c i ∈ RS.family (r i)) ∧
      (Real.log (chainZ N m v (π ^ 2 / 8) t) + 1) / t * l <
        ∑ i ∈ Finset.range l, cfgVal (fun z => h ε z ω) δ (RS.bin (r i)) (c i)} ⊆
      ⋃ ρ ∈ T, E ρ := by
    rintro ω ⟨r, c, hr, hc, hlt⟩
    refine mem_iUnion₂.2 ⟨fun i => r i, ?_, fun i => c i, fun i => hc i i.2, ?_⟩
    · simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨r, hr, fun i => rfl⟩
    · rw [Finset.sum_range] at hlt
      exact hlt
  -- step 2: the bound for one chain record
  have hchain : ∀ ρ ∈ T, P (E ρ) ≤ ENNReal.ofReal (Real.exp (-t * β +
      t * ∑ i, m (RS.bin (ρ i)) + π ^ 2 / 8 * t ^ 2 * ∑ i, v (RS.bin (ρ i)))) := by
    intro ρ hρ
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hρ
    obtain ⟨r, hr, hrρ⟩ := hρ
    refine chain_bound_family hP1 hG hε δ (fun i => RS.bin (ρ i)) (fun i => RS.family (ρ i))
      (fun i => hpos (ρ i)) (fun i => m (RS.bin (ρ i))) (∑ i, v (RS.bin (ρ i)))
      (fun i F hF hsub => hmean (ρ i) F hF hsub) ?_ β t ht.le
    intro c hc
    let c' : ℕ → Config := fun i => if hi : i < l then c ⟨i, hi⟩ else c ⟨0, hl⟩
    have hc' : ∀ i < l, c' i ∈ RS.family (r i) := by
      intro i hi
      have e1 : c' i = c ⟨i, hi⟩ := dif_pos hi
      rw [e1, hrρ ⟨i, hi⟩]
      exact hc ⟨i, hi⟩
    have := hvar l r c' hr hc'
    simp only [Finset.sum_range] at this
    have e2 : ∀ i : Fin l, c' i = c i := fun i => dif_pos i.2
    simp only [e2, hrρ] at this
    exact this
  -- step 3: the chain events are bounded by the weights `exp(-tβ) Π a(kᵢ)`
  have hexp : ∀ ρ : Fin l → RS.Rec, Real.exp (-t * β +
      t * ∑ i, m (RS.bin (ρ i)) + π ^ 2 / 8 * t ^ 2 * ∑ i, v (RS.bin (ρ i))) =
      Real.exp (-t * β) * ∏ i, a (RS.bin (ρ i)) := by
    intro ρ
    have e3 : ∏ i, a (RS.bin (ρ i)) = Real.exp (∑ i, (t * m (RS.bin (ρ i)) +
        π ^ 2 / 8 * t ^ 2 * v (RS.bin (ρ i)))) :=
      (Real.exp_sum Finset.univ fun i => t * m (RS.bin (ρ i)) +
        π ^ 2 / 8 * t ^ 2 * v (RS.bin (ρ i))).symm
    rw [e3, ← Real.exp_add]
    congr 1
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    ring
  -- step 4: counting
  have hcount : ∑ ρ ∈ T, ∏ i, a (RS.bin (ρ i)) ≤ Z ^ l := by
    rw [show T = Finset.univ.filter chainF from rfl, Finset.sum_filter]
    refine le_trans (Finset.sum_le_sum fun ρ _ => ?_) (sum_chain_le RS.next
      (fun x => a (RS.bin x)) (fun x => ha0 _) Z hZ0
      (fun x => sum_ite_le_tsum (RS.next x) RS.bin N a ha0 (hNnext x) hsum) l RS.isRoot
      (sum_ite_le_tsum RS.isRoot RS.bin N a ha0 hNroot hsum))
    by_cases hρ : chainF ρ
    · have hQ : IsChainQ RS.next RS.isRoot ρ := by
        obtain ⟨r, hr, hrρ⟩ := hρ
        refine ⟨fun h0 => ?_, fun i hi => ?_⟩
        · rw [← hrρ ⟨0, h0⟩]
          exact hr.1 h0
        · rw [← hrρ ⟨i, by omega⟩, ← hrρ ⟨i + 1, hi⟩]
          exact hr.2 i hi
      rw [if_pos hQ]
      exact le_of_eq (if_pos hρ)
    · rw [if_neg hρ]
      split_ifs
      · exact Finset.prod_nonneg fun i _ => ha0 _
      · exact le_rfl
  -- step 5: `exp(-tβ) Z^l ≤ e^{-l}`
  have hfinal : Real.exp (-t * β) * Z ^ l ≤ Real.exp (-(l : ℝ)) := by
    rcases hZ0.eq_or_lt with hZe | hZpos
    · rw [← hZe, zero_pow hl.ne', mul_zero]
      exact (Real.exp_pos _).le
    · have hZl : Z ^ l = Real.exp (l * Real.log Z) := by
        rw [Real.exp_nat_mul, Real.exp_log hZpos]
      rw [hZl, ← Real.exp_add]
      refine le_of_eq (congrArg Real.exp ?_)
      have htne : t ≠ 0 := ht.ne'
      have e4 : t * ((Real.log Z + 1) / t * l) = (Real.log Z + 1) * l := by
        rw [div_mul_eq_mul_div, mul_div_assoc', mul_div_cancel_left₀ _ htne]
      rw [hβ]
      linear_combination -e4
  -- assembly
  calc P _ ≤ P (⋃ ρ ∈ T, E ρ) := measure_mono hcover
    _ ≤ ∑ ρ ∈ T, P (E ρ) := measure_biUnion_finset_le T E
    _ ≤ ∑ ρ ∈ T, ENNReal.ofReal (Real.exp (-t * β) * ∏ i, a (RS.bin (ρ i))) := by
        refine Finset.sum_le_sum fun ρ hρ => ?_
        rw [← hexp ρ]
        exact hchain ρ hρ
    _ = ENNReal.ofReal (∑ ρ ∈ T, Real.exp (-t * β) * ∏ i, a (RS.bin (ρ i))) :=
        (ENNReal.ofReal_sum_of_nonneg fun ρ _ =>
          mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg fun i _ => ha0 _)).symm
    _ ≤ ENNReal.ofReal (Real.exp (-(l : ℝ))) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Finset.mul_sum]
        exact le_trans (mul_le_mul_of_nonneg_left hcount (Real.exp_pos _).le) hfinal

end LQGDimension
