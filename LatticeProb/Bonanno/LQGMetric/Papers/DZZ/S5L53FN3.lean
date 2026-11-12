/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53FN3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53HB2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53GA2

/-!
# DZZ Lemma 5.3 part 1, final assembly 3: the numerics conjunct and the combination
(P2-DZZ53FIN)

Ding–Zeitouni–Zhang, arXiv:1807.00422 (`LBM_LGDarXiv.tex`), proof of Lemma 5.3, l. 2523–2548
(the union bound over the at most `e^{T₁}` interior cells of the chain, `T₁ = E X_k + L^{0.97}`).

* `L53Node4At`, `L53CellAt`: the two parts of `L53HbadBParts` (S5L53HB2), verbatim
  (`l53HbadBParts_iff` is `Iff.rfl`).
* **`l53fn_numerics`**: the numerics conjunct `e^{T₁} β ≤ e^{-L^{0.22}}/4` for every
  `β ≤ e^{-L^q}` (`q > 1`) and large `k`, from G-W2 `l53EX_le_mul_L` (S5L53GA2: `E X_k ≤ C L`).
  (The per-cell bound of node 3, `K 2^{-L²} + (4e(L²+2)/j)^j` with `j ≍ ε*² K`, AUDIT-N §3 and
  N11, is `≤ e^{-L^{1.5}}` for large `L`.)
* **`l53HbadBParts_holds`**, **`l53HbadBAll_holds`**: the combination, from the node-4 part
  (`L53Node4PartAll`) and the node-3 part with a super-exponential `β` (`L53Node3PartAll`).

Own elementary bookkeeping.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

/-- **Node 4 at `(k, l)`**: the first conjunct of `L53HbadBParts` (S5L53HB2), verbatim. -/
def L53Node4At {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
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
    ENNReal.ofReal (Real.exp (-((k : ℝ) * Real.log 2) ^ (0.22 : ℝ)) / 2)

/-- **Node 3 at `(k, l)` with per-cell bound `β`**: the cell clause of the second conjunct of
`L53HbadBParts` (S5L53HB2), verbatim. -/
def L53CellAt {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) (γ αs : ℝ) (u v : ℂ) (k l : ℕ) (β : ℝ≥0∞) : Prop :=
  ∀ c₀ : List DyBox,
      (c₀.length : ℝ) ≤ Real.exp (l53EX P γ W u v k + ((k : ℝ) * Real.log 2) ^ (0.97 : ℝ)) →
      ∀ i, 2 ≤ i → i ≤ c₀.length - 1 →
      P[l53E4 hW γ ((2 : ℝ)⁻¹ ^ k) ∩ cellSizeEvent γ W ((2 : ℝ)⁻¹ ^ k) ∩
          {ω | ¬ L53DesClause (μH[1] : Measure ℂ) (dzzWall (tildeBox u v) (dzzMuIn γ W ω))
            ((2 : ℝ)⁻¹ ^ (k + l)) (l53EX P γ W u v l + 2 * ((k : ℝ) * Real.log 2) ^ (0.98 : ℝ))
            (l53Iface c₀ (i - 1)) (l53Iface c₀ i)} |
        {ω | l53Chain γ W αs ((2 : ℝ)⁻¹ ^ k) u v
          (Metric.cthickening (2 * ((2 : ℝ)⁻¹ ^ k) ^ dzzCMc γ)
            (Metric.cthickening (8 * ((2 : ℝ)⁻¹ ^ k) ^ dzzCMc γ) (l53Region u v)))
          (l53EX P γ W u v k + ((k : ℝ) * Real.log 2) ^ (0.97 : ℝ)) ω = c₀}] ≤ β

lemma l53HbadBParts_iff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) (γ αs : ℝ) (u v : ℂ) (k l : ℕ) :
    L53HbadBParts hW γ αs u v k l ↔ L53Node4At hW γ αs u v k l ∧ ∃ β : ℝ≥0∞,
      L53CellAt hW γ αs u v k l β ∧
      ENNReal.ofReal (Real.exp (l53EX P γ W u v k + ((k : ℝ) * Real.log 2) ^ (0.97 : ℝ))) * β ≤
        ENNReal.ofReal (Real.exp (-((k : ℝ) * Real.log 2) ^ (0.22 : ℝ)) / 4) :=
  Iff.rfl

/-- `e^{X + L^{0.97}} e^{-L^q} ≤ e^{-L^{0.22}}/4` for `X ≤ C L`, `q > 1`, large `L`. -/
lemma l53fn_exp_small (C : ℝ) {q : ℝ} (hq : 1 < q) : ∀ᶠ L : ℝ in atTop, ∀ X : ℝ, X ≤ C * L →
    Real.exp (X + L ^ (0.97 : ℝ)) * Real.exp (-L ^ q) ≤ Real.exp (-L ^ (0.22 : ℝ)) / 4 := by
  have ht := tendsto_rpow_atTop (show (0 : ℝ) < q - 1 by linarith)
  filter_upwards [ht.eventually_ge_atTop (|C| + 4), eventually_ge_atTop (1 : ℝ)] with L hLq hL1 X hX
  have hL0 : 0 < L := by linarith
  have h97 : L ^ (0.97 : ℝ) ≤ L := by
    simpa using Real.rpow_le_rpow_of_exponent_le hL1 (show (0.97 : ℝ) ≤ 1 by norm_num)
  have h22 : L ^ (0.22 : ℝ) ≤ L := by
    simpa using Real.rpow_le_rpow_of_exponent_le hL1 (show (0.22 : ℝ) ≤ 1 by norm_num)
  have hLqe : L ^ q = L * L ^ (q - 1) := by
    rw [← Real.rpow_one_add' hL0.le (by linarith)]
    · norm_num
  have hC : C * L ≤ |C| * L := mul_le_mul_of_nonneg_right (le_abs_self C) hL0.le
  have hlog4 : Real.log 4 ≤ 2 := by
    have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    have e : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    linarith
  have key : X + L ^ (0.97 : ℝ) + -L ^ q ≤ -L ^ (0.22 : ℝ) - Real.log 4 := by
    have : (|C| + 4) * L ≤ L * L ^ (q - 1) := by nlinarith
    nlinarith
  rw [← Real.exp_add]
  calc Real.exp (X + L ^ (0.97 : ℝ) + -L ^ q) ≤ Real.exp (-L ^ (0.22 : ℝ) - Real.log 4) :=
        Real.exp_le_exp.2 key
    _ = Real.exp (-L ^ (0.22 : ℝ)) / 4 := by
        rw [Real.exp_sub, Real.exp_log (by norm_num)]

/-- **The numerics conjunct** (DZZ l. 2523–2548): for large `k`, every `β ≤ e^{-L^q}` (`q > 1`)
satisfies `e^{T₁} β ≤ e^{-L^{0.22}}/4`, `T₁ = E X_k + L^{0.97}` (G-W2, S5L53GA2). -/
theorem l53fn_numerics {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {u v : ℂ} (hu : u ∈ dzzVbar)
    (hv : v ∈ dzzVbar) (huv : u ≠ v) {q : ℝ} (hq : 1 < q) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ β : ℝ≥0∞,
      β ≤ ENNReal.ofReal (Real.exp (-((k : ℝ) * Real.log 2) ^ q)) →
      ENNReal.ofReal (Real.exp (l53EX P γ W u v k + ((k : ℝ) * Real.log 2) ^ (0.97 : ℝ))) * β ≤
        ENNReal.ofReal (Real.exp (-((k : ℝ) * Real.log 2) ^ (0.22 : ℝ)) / 4) := by
  obtain ⟨C, hC⟩ := l53EX_le_mul_L hW hγ hγ2 hu hv huv
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.1 (l53fn_exp_small C hq)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨k₁, hk₁⟩ := eventually_atTop.1 hC
  refine ⟨max k₁ ⌈L₀ / Real.log 2⌉₊, fun k hk β hβ => ?_⟩
  have hkL : L₀ ≤ (k : ℝ) * Real.log 2 := by
    rw [← div_le_iff₀ hl2]
    exact (Nat.le_ceil _).trans (by exact_mod_cast le_of_max_le_right hk)
  have h := hL₀ _ hkL _ (hk₁ k (le_of_max_le_left hk))
  calc ENNReal.ofReal (Real.exp (l53EX P γ W u v k + ((k : ℝ) * Real.log 2) ^ (0.97 : ℝ))) * β
      ≤ ENNReal.ofReal (Real.exp (l53EX P γ W u v k + ((k : ℝ) * Real.log 2) ^ (0.97 : ℝ))) *
          ENNReal.ofReal (Real.exp (-((k : ℝ) * Real.log 2) ^ q)) := by gcongr
    _ = ENNReal.ofReal (Real.exp (l53EX P γ W u v k + ((k : ℝ) * Real.log 2) ^ (0.97 : ℝ)) *
          Real.exp (-((k : ℝ) * Real.log 2) ^ q)) :=
        (ENNReal.ofReal_mul (Real.exp_pos _).le).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal h

/-- **The node-4 part for every white noise** (P2-DZZ53N4F's `l53_node4_part`, in flight), in the
exact form of the first conjunct of `L53HbadBParts`. -/
def L53Node4PartAll : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (W : WNSpace → Ω → ℝ)
    (hW : IsWhiteNoise P W) (γ : ℝ), 0 < γ → γ < 2 → ∀ αs : ℝ, 0 < αs →
    ∀ u ∈ dzzVbar, ∀ v ∈ dzzVbar, u ≠ v → ∃ k₀ : ℕ, ∀ k l : ℕ, k₀ ≤ k → 1 ≤ l → l ≤ k →
      L53Node4At hW γ αs u v k l

/-- **The node-3 part for every white noise** (P2-DZZ53N3F's `l53_node3_part`, in flight): the
cell clause of `L53HbadBParts` with a per-cell bound `β ≤ e^{-L^q}`, some `q > 1`. -/
def L53Node3PartAll : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (W : WNSpace → Ω → ℝ)
    (hW : IsWhiteNoise P W) (γ : ℝ), 0 < γ → γ < 2 → ∀ αs : ℝ, 0 < αs →
    ∀ u ∈ dzzVbar, ∀ v ∈ dzzVbar, u ≠ v → ∃ q : ℝ, 1 < q ∧ ∃ k₀ : ℕ, ∀ k l : ℕ, k₀ ≤ k →
      1 ≤ l → l ≤ k → ∃ β : ℝ≥0∞,
        β ≤ ENNReal.ofReal (Real.exp (-((k : ℝ) * Real.log 2) ^ q)) ∧ L53CellAt hW γ αs u v k l β

/-- **`L53HbadBParts` for every white noise** from the node-4 and node-3 parts and the numerics
`l53fn_numerics`. -/
theorem l53HbadBParts_holds (h4 : L53Node4PartAll) (h3 : L53Node3PartAll) :
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (W : WNSpace → Ω → ℝ)
      (hW : IsWhiteNoise P W) (γ : ℝ), 0 < γ → γ < 2 → ∀ αs : ℝ, 0 < αs →
      ∀ u ∈ dzzVbar, ∀ v ∈ dzzVbar, u ≠ v → ∃ k₀ : ℕ, ∀ k l : ℕ, k₀ ≤ k → 1 ≤ l → l ≤ k →
        L53HbadBParts hW γ αs u v k l := by
  intro Ω _ P W hW γ hγ hγ2 αs hαs u hu v hv huv
  obtain ⟨k₄, hk₄⟩ := h4 P W hW γ hγ hγ2 αs hαs u hu v hv huv
  obtain ⟨q, hq, k₃, hk₃⟩ := h3 P W hW γ hγ hγ2 αs hαs u hu v hv huv
  obtain ⟨kn, hkn⟩ := l53fn_numerics hW hγ hγ2 hu hv huv hq
  refine ⟨max (max k₄ k₃) kn, fun k l hk hl hlk => ?_⟩
  have hk4 : k₄ ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hk
  have hk3 : k₃ ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hk
  have hkn' : kn ≤ k := le_trans (le_max_right _ _) hk
  obtain ⟨β, hβ, hcell⟩ := hk₃ k l hk3 hl hlk
  exact (l53HbadBParts_iff hW γ αs u v k l).2
    ⟨hk₄ k l hk4 hl hlk, β, hcell, hkn k hkn' β hβ⟩

/-- **`L53HbadBAll`** (the DZZ L5.3 part-1 leaf, S5L53W1) from the node-4 and node-3 parts. -/
theorem l53HbadBAll_holds (h4 : L53Node4PartAll) (h3 : L53Node3PartAll) : L53HbadBAll :=
  l53HbadBAll_of_parts (l53HbadBParts_holds h4 h3)

end DZZ
end LQGMetric
