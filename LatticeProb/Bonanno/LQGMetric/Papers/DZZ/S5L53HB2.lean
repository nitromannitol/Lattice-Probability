/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53HB2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53W2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53Z3
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L1

/-!
# The `hbadB` assembly: conditioning on the chain, union over the cells, numerics

Ding–Zeitouni–Zhang, arXiv:1807.00422 (`LBM_LGDarXiv.tex`, DZZ l.), proof of Lemma 5.3:
DZZ bound the probability that the chain `𝒞` of `𝓔*` (l. 2363–2378) is not desirable
conditionally on `𝓕*` (l. 2504–2522): the event `𝓔₄` is removed first (l. 2440–2443; here
`E = l53E4 ∩ cellSizeEvent`, DEC-131-IF W-4, with P-131R's `l53_E4_prob` and L3.1
`dzz_lemma31`); on each fibre `{𝒞 = c₀}` (`measurableSet_l53Chain_eq`, S5L53L5) the cells
`𝖢_i`, `2 ≤ i ≤ d − 1`, are desirable with conditional probability `≥ 1 − β` each (node 3,
l. 2510–2514); a union bound over the `d ≤ e^{T₁}` cells (l. 2513–2514) and the sum over the
disjoint fibres follow (`measure_iUnion_inter_le_cond`, S5L53W2); `u`, `v` (node 4,
l. 2516–2522) enter through an unconditional bound (U's `l53_uv_bound`, DEC-131-IF W-3).

* **`l53BadB_le_split'`** (DEC-131-IF G-W1, exact statement);
* **`l53_hbadB_of_parts`**: `L53HbadB P W γ αs` (S5L53W1) from the node-4 bound (`≤ e^{-L^{0.22}}/2`),
  the node-3 conditional per-cell bound `β k l` and `e^{T₁} β ≤ e^{-L^{0.22}}/4`, with
  `P(Eᶜ) ≤ e^{-L^{0.22}}/4` proved here;
* **`l53HbadBAll_of_parts`**: `L53HbadBAll` (the input of W's `dzzLem53ExpAll_of_hbadB`) from the
  same parts for every white noise, `γ ∈ (0, 2)`, `α* > 0`.

Own elementary bookkeeping (on top of P2-DZZ53W's S5L53W2).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter ProbabilityTheory
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open DyBox WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **G-W1** (DEC-131-IF §3): `l53BadB_le_split` (S5L53W2) with one unconditional bound for the
`u`- and `v`-clauses of the selected chain (node 4 is unconditional). -/
theorem l53BadB_le_split' {P : Measure Ω} [IsProbabilityMeasure P] {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) (γ αs : ℝ) (ν : Ω → Measure ℂ) (u v : ℂ) (k l : ℕ) (R : Set ℂ)
    (T₁ T T' : ℝ) (E : Set Ω) (b εuv β : ℝ≥0∞) (hE : P Eᶜ ≤ b)
    (huv : P (E ∩ {ω | ¬ (l53UClause (ν ω) u ((2 : ℝ)⁻¹ ^ (k + l)) T
        (l53Chain γ W αs ((2 : ℝ)⁻¹ ^ k) u v R T₁ ω) ∧
      l53VClause (ν ω) v ((2 : ℝ)⁻¹ ^ (k + l)) T (l53Chain γ W αs ((2 : ℝ)⁻¹ ^ k) u v R T₁ ω))}) ≤ εuv)
    (hcell : ∀ c₀ : List DyBox, (c₀.length : ℝ) ≤ Real.exp T₁ → ∀ i, 2 ≤ i → i ≤ c₀.length - 1 →
      P[E ∩ {ω | ¬ L53DesClause (μH[1] : Measure ℂ) (ν ω) ((2 : ℝ)⁻¹ ^ (k + l)) T'
        (l53Iface c₀ (i - 1)) (l53Iface c₀ i)} |
        {ω | l53Chain γ W αs ((2 : ℝ)⁻¹ ^ k) u v R T₁ ω = c₀}] ≤ β) :
    P (l53BadB γ W αs ν u v k l R T₁ T T') ≤ b + (εuv + ENNReal.ofReal (Real.exp T₁) * β) := by
  classical
  set D := l53D1EventB γ W αs ((2 : ℝ)⁻¹ ^ k) u v R T₁
  set A : List DyBox → Set Ω := fun c₀ => {ω | l53Chain γ W αs ((2 : ℝ)⁻¹ ^ k) u v R T₁ ω = c₀}
  set B : List DyBox → Set Ω := fun c₀ => D ∩ {ω | (c₀.length : ℝ) ≤ Real.exp T₁ ∧
    (ω ∉ E ∨ ¬ l53CellsClause (ν ω) ((2 : ℝ)⁻¹ ^ (k + l)) T' c₀)}
  have hA : ∀ c₀, MeasurableSet (A c₀) := fun c₀ =>
    cellSigma_le hW γ _ _ (measurableSet_l53Chain_eq γ αs _ u v R T₁ c₀)
  have hdis : Pairwise (Function.onFun Disjoint A) := fun c c' hcc' =>
    Set.disjoint_left.2 fun ω h1 h2 => hcc' (h1.symm.trans h2)
  have hsub : l53BadB γ W αs ν u v k l R T₁ T T' ⊆
      (E ∩ {ω | ¬ (l53UClause (ν ω) u ((2 : ℝ)⁻¹ ^ (k + l)) T
        (l53Chain γ W αs ((2 : ℝ)⁻¹ ^ k) u v R T₁ ω) ∧
        l53VClause (ν ω) v ((2 : ℝ)⁻¹ ^ (k + l)) T
          (l53Chain γ W αs ((2 : ℝ)⁻¹ ^ k) u v R T₁ ω))}) ∪ ⋃ c₀, A c₀ ∩ B c₀ := by
    rintro ω ⟨hD, hnd⟩
    have hlen := (l53Chain_spec hD.2).2.2
    by_cases hE : ω ∈ E
    · by_cases huv : l53UClause (ν ω) u ((2 : ℝ)⁻¹ ^ (k + l)) T
          (l53Chain γ W αs ((2 : ℝ)⁻¹ ^ k) u v R T₁ ω) ∧
          l53VClause (ν ω) v ((2 : ℝ)⁻¹ ^ (k + l)) T
            (l53Chain γ W αs ((2 : ℝ)⁻¹ ^ k) u v R T₁ ω)
      · exact Or.inr (mem_iUnion.2 ⟨_, rfl, hD, hlen, Or.inr fun hc =>
        hnd ((l53ChainDesirable_iff _ _ _ _ _ _ _).2 ⟨huv.1, huv.2, hc⟩)⟩)
      · exact Or.inl ⟨hE, huv⟩
    · exact Or.inr (mem_iUnion.2 ⟨_, rfl, hD, hlen, Or.inl hE⟩)
  have hcond : ∀ c₀, P[E ∩ B c₀ | A c₀] ≤ ENNReal.ofReal (Real.exp T₁) * β := by
    intro c₀
    by_cases hlen : (c₀.length : ℝ) ≤ Real.exp T₁
    · have hXs : E ∩ B c₀ ⊆ ⋃ i ∈ Finset.Icc 2 (c₀.length - 1),
          E ∩ {ω | ¬ L53DesClause (μH[1] : Measure ℂ) (ν ω) ((2 : ℝ)⁻¹ ^ (k + l)) T'
            (l53Iface c₀ (i - 1)) (l53Iface c₀ i)} := by
        rintro ω ⟨hE, -, -, hc⟩
        rcases hc with hc | hc
        · exact absurd hE hc
        rw [l53CellsClause_iff] at hc
        simp only [not_forall] at hc
        obtain ⟨i, hi, hQ⟩ := hc
        exact mem_biUnion hi ⟨hE, hQ⟩
      calc P[E ∩ B c₀ | A c₀] ≤ ∑ i ∈ Finset.Icc 2 (c₀.length - 1), P[E ∩
            {ω | ¬ L53DesClause (μH[1] : Measure ℂ) (ν ω) ((2 : ℝ)⁻¹ ^ (k + l)) T'
              (l53Iface c₀ (i - 1)) (l53Iface c₀ i)} | A c₀] :=
            (measure_mono hXs).trans (measure_biUnion_finset_le _ _)
        _ ≤ ∑ _i ∈ Finset.Icc 2 (c₀.length - 1), β := Finset.sum_le_sum fun i hi =>
            hcell c₀ hlen i (Finset.mem_Icc.1 hi).1 (Finset.mem_Icc.1 hi).2
        _ = ((Finset.Icc 2 (c₀.length - 1)).card : ℝ≥0∞) * β := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ENNReal.ofReal (Real.exp T₁) * β := by
            gcongr
            rw [Nat.card_Icc]
            calc ((c₀.length - 1 + 1 - 2 : ℕ) : ℝ≥0∞) ≤ (c₀.length : ℝ≥0∞) := by
                  exact_mod_cast (by omega : c₀.length - 1 + 1 - 2 ≤ c₀.length)
              _ = ENNReal.ofReal (c₀.length : ℝ) := (ENNReal.ofReal_natCast _).symm
              _ ≤ ENNReal.ofReal (Real.exp T₁) := ENNReal.ofReal_le_ofReal hlen
    · have h0 : E ∩ B c₀ = ∅ := eq_empty_iff_forall_notMem.2 fun ω h => hlen h.2.2.1
      rw [h0, measure_empty]
      exact zero_le
  calc P (l53BadB γ W αs ν u v k l R T₁ T T')
      ≤ εuv + (P Eᶜ + ENNReal.ofReal (Real.exp T₁) * β) :=
        (measure_mono hsub).trans ((measure_union_le _ _).trans
          (add_le_add huv (measure_iUnion_inter_le_cond P A B hA hdis E _ hcond)))
    _ ≤ εuv + (b + ENNReal.ofReal (Real.exp T₁) * β) := by gcongr
    _ = b + (εuv + ENNReal.ofReal (Real.exp T₁) * β) := by ring

/-- `e^{-a L^q} ≤ e^{-L^{0.22}}/8` for large `L` (`a > 0`, `q > 0.22`). -/
lemma l53_ev_exp_small {a q : ℝ} (ha : 0 < a) (hq : 0.22 < q) : ∀ᶠ L : ℝ in atTop,
    Real.exp (-(a * L ^ q)) ≤ Real.exp (-L ^ (0.22 : ℝ)) / 8 := by
  filter_upwards [l53_ev_mul_rpow_le (2 / a) hq,
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 0.22)).eventually
      (eventually_ge_atTop (Real.log 8))] with L h1 h2
  have h3 : 2 * L ^ (0.22 : ℝ) ≤ a * L ^ q := by
    have := mul_le_mul_of_nonneg_left h1 ha.le
    rwa [← mul_assoc, mul_div_cancel₀ _ ha.ne'] at this
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 8)]
  calc Real.exp (-(a * L ^ q)) * 8 = Real.exp (-(a * L ^ q) + Real.log 8) := by
        rw [Real.exp_add, Real.exp_log (by norm_num)]
    _ ≤ Real.exp (-L ^ (0.22 : ℝ)) := Real.exp_le_exp.2 (by linarith)

/-- **`P(𝓔₄ᶜ ∪ (cell sizes)ᶜ) ≤ e^{-L^{0.22}}/4`** for large `k` (P-131R `l53_E4_prob`, L3.1
`dzz_lemma31`). -/
theorem l53_E_prob {P : Measure Ω} {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) : ∃ k₀ : ℕ, ∀ k ≥ k₀,
      P (l53E4 hW γ ((2 : ℝ)⁻¹ ^ k) ∩ cellSizeEvent γ W ((2 : ℝ)⁻¹ ^ k))ᶜ ≤
        ENNReal.ofReal (Real.exp (-((k : ℝ) * Real.log 2) ^ (0.22 : ℝ)) / 4) := by
  have := hW.isProbabilityMeasure
  obtain ⟨δ₁, hδ₁, hE4⟩ := l53_E4_prob hW hγ hγ2
  obtain ⟨c, hc, δ₂, hδ₂, hcs⟩ := dzz_lemma31 hW hγ hγ2
  obtain ⟨k₁, hk₁⟩ := exists_pow_lt_of_lt_one (lt_min hδ₁ hδ₂) (by norm_num : (2 : ℝ)⁻¹ < 1)
  obtain ⟨k₂, h₂⟩ := eventually_atTop.1 (l53_tendsto_kL.eventually
    ((l53_ev_exp_small one_pos (by norm_num : (0.22 : ℝ) < 0.23)).and
      (l53_ev_exp_small hc (by norm_num : (0.22 : ℝ) < 1))))
  refine ⟨max k₁ k₂, fun k hk => ?_⟩
  have hk1 : k₁ ≤ k := by omega
  have hk2 : k₂ ≤ k := by omega
  have hδ : (2 : ℝ)⁻¹ ^ k < min δ₁ δ₂ :=
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) hk1).trans_lt hk₁
  have hδ0 : (0 : ℝ) < (2 : ℝ)⁻¹ ^ k := by positivity
  obtain ⟨e1, e2⟩ := h₂ k hk2
  set e := Real.exp (-((k : ℝ) * Real.log 2) ^ (0.22 : ℝ))
  have he : 0 ≤ e := (Real.exp_pos _).le
  have hA : P (l53E4 hW γ ((2 : ℝ)⁻¹ ^ k))ᶜ ≤ ENNReal.ofReal (e / 8) := by
    refine (hE4 _ ⟨hδ0, hδ.trans_le (min_le_left _ _)⟩).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [log_inv_two_inv_pow]
    simpa only [one_mul] using e1
  have hB : P (cellSizeEvent γ W ((2 : ℝ)⁻¹ ^ k))ᶜ ≤ ENNReal.ofReal (e / 8) := by
    refine (hcs _ ⟨hδ0, hδ.trans_le (min_le_right _ _)⟩).trans (ENNReal.ofReal_le_ofReal ?_)
    have hlog : Real.log ((2 : ℝ)⁻¹ ^ k) = -((k : ℝ) * Real.log 2) := by
      rw [← log_inv_two_inv_pow, Real.log_inv, neg_neg]
    rw [Real.rpow_def_of_pos hδ0, hlog]
    simpa only [Real.rpow_one, neg_mul, mul_comm c] using e2
  rw [compl_inter]
  calc _ ≤ _ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (e / 8) + ENNReal.ofReal (e / 8) := add_le_add hA hB
    _ = ENNReal.ofReal (e / 4) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring

/-- **The parts of `hbadB` at one pair and one `(k, l)`** (DEC-131-IF §4.1), with
`E = l53E4 ∩ cellSizeEvent` (W-4), box region `R = cthickening (2δ^{C_Mc}) (cthickening (8δ^{C_Mc})
(l53Region u v))`, `T₁ = EX_k + L^{0.97}`, `T = EX_l + L^{0.98}`, `T' = EX_l + 2L^{0.98}`:
* node 4 (P-131U, `l53_uv_bound` with `Adm ω c := c = l53Chain … ω`): the `u`/`v` clauses of the
  selected chain fail on `E` with probability `≤ e^{-L^{0.22}}/2`;
* node 3 (G-J3 with F's G-F3): on each fibre `{𝒞 = c₀}` with `d ≤ e^{T₁}`, each interior cell
  fails on `E` with conditional probability `≤ β`, and `e^{T₁} β ≤ e^{-L^{0.22}}/4`. -/
def L53HbadBParts {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) (γ αs : ℝ) (u v : ℂ) (k l : ℕ) : Prop :=
  P (l53E4 hW γ ((2 : ℝ)⁻¹ ^ k) ∩ cellSizeEvent γ W ((2 : ℝ)⁻¹ ^ k) ∩
      {ω | ¬ (l53UClause (dzzWall (tildeBox u v) (dzzMuIn γ W ω)) u ((2 : ℝ)⁻¹ ^ (k + l))
          (l53EX P γ W u v l + ((k : ℝ) * Real.log 2) ^ (0.98 : ℝ))
          (l53Chain γ W αs ((2 : ℝ)⁻¹ ^ k) u v
            (Metric.cthickening (2 * ((2 : ℝ)⁻¹ ^ k) ^ dzzCMc γ)
              (Metric.cthickening (8 * ((2 : ℝ)⁻¹ ^ k) ^ dzzCMc γ) (l53Region u v)))
            (l53EX P γ W u v k + ((k : ℝ) * Real.log 2) ^ (0.97 : ℝ)) ω) ∧
        l53VClause (dzzWall (tildeBox u v) (dzzMuIn γ W ω)) v ((2 : ℝ)⁻¹ ^ (k + l))
          (l53EX P γ W u v l + ((k : ℝ) * Real.log 2) ^ (0.98 : ℝ))
          (l53Chain γ W αs ((2 : ℝ)⁻¹ ^ k) u v
            (Metric.cthickening (2 * ((2 : ℝ)⁻¹ ^ k) ^ dzzCMc γ)
              (Metric.cthickening (8 * ((2 : ℝ)⁻¹ ^ k) ^ dzzCMc γ) (l53Region u v)))
            (l53EX P γ W u v k + ((k : ℝ) * Real.log 2) ^ (0.97 : ℝ)) ω))}) ≤
    ENNReal.ofReal (Real.exp (-((k : ℝ) * Real.log 2) ^ (0.22 : ℝ)) / 2) ∧
  ∃ β : ℝ≥0∞,
    (∀ c₀ : List DyBox,
      (c₀.length : ℝ) ≤ Real.exp (l53EX P γ W u v k + ((k : ℝ) * Real.log 2) ^ (0.97 : ℝ)) →
      ∀ i, 2 ≤ i → i ≤ c₀.length - 1 →
      P[l53E4 hW γ ((2 : ℝ)⁻¹ ^ k) ∩ cellSizeEvent γ W ((2 : ℝ)⁻¹ ^ k) ∩
          {ω | ¬ L53DesClause (μH[1] : Measure ℂ) (dzzWall (tildeBox u v) (dzzMuIn γ W ω))
            ((2 : ℝ)⁻¹ ^ (k + l)) (l53EX P γ W u v l + 2 * ((k : ℝ) * Real.log 2) ^ (0.98 : ℝ))
            (l53Iface c₀ (i - 1)) (l53Iface c₀ i)} |
        {ω | l53Chain γ W αs ((2 : ℝ)⁻¹ ^ k) u v
          (Metric.cthickening (2 * ((2 : ℝ)⁻¹ ^ k) ^ dzzCMc γ)
            (Metric.cthickening (8 * ((2 : ℝ)⁻¹ ^ k) ^ dzzCMc γ) (l53Region u v)))
          (l53EX P γ W u v k + ((k : ℝ) * Real.log 2) ^ (0.97 : ℝ)) ω = c₀}] ≤ β) ∧
    ENNReal.ofReal (Real.exp (l53EX P γ W u v k + ((k : ℝ) * Real.log 2) ^ (0.97 : ℝ))) * β ≤
      ENNReal.ofReal (Real.exp (-((k : ℝ) * Real.log 2) ^ (0.22 : ℝ)) / 4)

/-- **`l53_hbadB_of_parts`** (P-131W, first half): the `hbadB` bound `L53HbadB` (S5L53W1) at `α*`
from the parts of node 4 and node 3 for large `k` (`P(Eᶜ)` is `l53_E_prob`). -/
theorem l53_hbadB_of_parts {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (αs : ℝ)
    (h : ∀ u ∈ dzzVbar, ∀ v ∈ dzzVbar, u ≠ v → ∃ k₀ : ℕ, ∀ k l : ℕ, k₀ ≤ k → 1 ≤ l → l ≤ k →
      L53HbadBParts hW γ αs u v k l) :
    L53HbadB P W γ αs := by
  have := hW.isProbabilityMeasure
  intro u hu v hv huv
  obtain ⟨k₁, h₁⟩ := h u hu v hv huv
  obtain ⟨k₂, h₂⟩ := l53_E_prob hW hγ hγ2
  refine ⟨max k₁ k₂, fun k l hk hl hlk => ?_⟩
  obtain ⟨hU, β, hcell, hβ⟩ := h₁ k l (le_of_max_le_left hk) hl hlk
  set e := Real.exp (-((k : ℝ) * Real.log 2) ^ (0.22 : ℝ))
  have he : 0 ≤ e := (Real.exp_pos _).le
  refine (l53BadB_le_split' hW γ αs _ u v k l _ _ _ _ _ _ _ β (h₂ k (le_of_max_le_right hk))
    hU hcell).trans ?_
  calc ENNReal.ofReal (e / 4) + (ENNReal.ofReal (e / 2) +
        ENNReal.ofReal (Real.exp (l53EX P γ W u v k + ((k : ℝ) * Real.log 2) ^ (0.97 : ℝ))) * β)
      ≤ ENNReal.ofReal (e / 4) + (ENNReal.ofReal (e / 2) + ENNReal.ofReal (e / 4)) := by gcongr
    _ = ENNReal.ofReal e := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; ring

/-- **`L53HbadBAll` from the parts** for every white noise, `γ ∈ (0, 2)` and `α* > 0`; with
`dzzLem53ExpAll_of_hbadB` (S5L53W1, refinement by `l53RefineB_of_pos`) this closes the DZZ leaf. -/
theorem l53HbadBAll_of_parts
    (h : ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (W : WNSpace → Ω → ℝ)
      (hW : IsWhiteNoise P W) (γ : ℝ), 0 < γ → γ < 2 → ∀ αs : ℝ, 0 < αs →
      ∀ u ∈ dzzVbar, ∀ v ∈ dzzVbar, u ≠ v → ∃ k₀ : ℕ, ∀ k l : ℕ, k₀ ≤ k → 1 ≤ l → l ≤ k →
        L53HbadBParts hW γ αs u v k l) :
    L53HbadBAll := fun P W hW γ hγ hγ2 αs hαs =>
  l53_hbadB_of_parts hW hγ hγ2 αs (h P W hW γ hγ hγ2 αs hαs)

end DZZ
end LQGMetric
