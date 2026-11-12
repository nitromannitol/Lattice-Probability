/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53F1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53E3
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12Defs
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12Good
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32K1

/-!
# DZZ Lemma 5.3, part 1, node 1: the cell chain of `𝒟₁` (P2-DZZ53F)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`, proof of Lemma 5.3
(`lem-existence-exponent`), l. 2361–2391.

* `l53W u v i = u + (i/9)(v − u)` (l. 2361; DZZ write `u + (i/9)|u − v|`, a typo for the point
  at fraction `i/9` of the segment `[u, v]`), `l53Box u v i = 𝕍̃_{w_{i−1}, w_i}` and
  `l53Region u v = ⋃_{i=1}^9 𝕍̃_{w_{i−1}, w_i}`.
* `L53CellChain`: the deterministic content of `𝓔*_{δ,α*,u,v}` ∩ `𝒟₁` (Def. `def-Estar`,
  l. 2363–2378, and (Eq.calD1)): a good sequence (Definition 3.11) of cells of the global
  partition `𝒱_δ` (D117 §3: the tilde partition is `𝒱_δ` restricted to the cells meeting the wall)
  meeting `l53Region u v`, joining `u` to `v`, with `d ≤ e^T`.
* `l53D1Event`: that chain exists, and all cells have side in `[δ^{C_mc}, δ^{C_Mc}]`
  (`cellSizeEvent`, contained in DZZ's `𝓔_{δ,α}`, which is part of (eq-def-E-delta-alpha*-u-v)).
* **`l53_concat_chain`**: good cell sequences joining `p_{i}` to `p_{i+1}` (`i < n`) concatenate
  into one joining `p_0` to `p_n` of length `≤ Σ dᵢ` (DZZ l. 2376: "following the discussions after
  (eq-E2)"; with the global partition the cells at the junction `p_i` coincide, so no surgery is
  needed). Own elementary proof.
* **`dzzLem53Event_of_desirable97`**, **`dzzLem53Exp_dzzMuIn_of_desirable97`**: the corrected
  form of `dzzLem53Exp_dzzMuIn_of_desirable` (S5L53E3) with `𝒟₁` at `E X_k + L^{0.97}` instead of
  `E X_k + L^{0.95}` (see "Source errors": DZZ's errors in (Eq.calD1) add up to more than
  `L^{0.95}`, since P3.17 (eq-concentration-2) alone costs `L^{0.95}`). `L^{0.97} + 4L^{0.98} ≤
  5 L^{0.98}` for large `L`, so the conclusion is unchanged.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

/-! ### The nine boxes -/

/-- `w_i = u + (i/9)(v − u)` (DZZ l. 2361). -/
def l53W (u v : ℂ) (i : ℕ) : ℂ := u + ((i : ℂ) / 9) * (v - u)

/-- `𝕍̃_{w_{i−1}, w_i}`. -/
def l53Box (u v : ℂ) (i : ℕ) : Set ℂ := tildeBox (l53W u v (i - 1)) (l53W u v i)

/-- `⋃_{i=1}^9 𝕍̃_{w_{i−1}, w_i}`. -/
def l53Region (u v : ℂ) : Set ℂ := ⋃ i ∈ Finset.Icc 1 9, l53Box u v i

lemma l53W_zero (u v : ℂ) : l53W u v 0 = u := by simp [l53W]

lemma l53W_nine (u v : ℂ) : l53W u v 9 = v := by
  simp only [l53W]; push_cast; ring

lemma l53Box_subset_region {u v : ℂ} {i : ℕ} (h1 : 1 ≤ i) (h9 : i ≤ 9) :
    l53Box u v i ⊆ l53Region u v := fun _ hz =>
  mem_iUnion₂.2 ⟨i, Finset.mem_Icc.2 ⟨h1, h9⟩, hz⟩

/-! ### Cell chains -/

/-- **The cell chain of `𝓔* ∩ 𝒟₁`** (l. 2363–2391): a good sequence of cells of `𝒱_δ` meeting `R`
joining `u` to `v`, of length `d ≤ e^T`. -/
def L53CellChain (m : DyBox → ℝ) (δ ε : ℝ) (u v : ℂ) (R : Set ℂ) (T : ℝ) (l : List DyBox) :
    Prop :=
  JoinsCells m δ u v l ∧ IsGoodSeq ε l ∧ (∀ c ∈ l, c ∈ cellsMeeting R) ∧
    (l.length : ℝ) ≤ Real.exp T

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### Concatenation -/

variable {m : DyBox → ℝ} {δ ε : ℝ}

/-- The cell of `𝒱_δ` containing a point is unique. -/
lemma isCell_eq_of_mem {c c' : DyBox} {w : ℂ} (hc : IsCell m δ c) (hc' : IsCell m δ c')
    (hw : c.Mem w) (hw' : c'.Mem w) : c = c' :=
  isCell_eq_of_anc m δ (d := boxAt (max c.n c'.n) w) hc hc'
    (by rw [anc_boxAt (le_max_left _ _), hw.2]) (by rw [anc_boxAt (le_max_right _ _), hw'.2])

/-- Two good cell sequences `u → w`, `w → v` concatenate (the cell containing `w` is shared). -/
lemma l53_concat_two {u w v : ℂ} {l₁ l₂ : List DyBox} (h₁ : JoinsCells m δ u w l₁)
    (h₂ : JoinsCells m δ w v l₂) (g₁ : IsGoodSeq ε l₁) (g₂ : IsGoodSeq ε l₂) :
    JoinsCells m δ u v (l₁ ++ l₂.tail) ∧ IsGoodSeq ε (l₁ ++ l₂.tail) ∧
      (l₁ ++ l₂.tail).length ≤ l₁.length + l₂.length ∧ ∀ c ∈ l₁ ++ l₂.tail, c ∈ l₁ ∨ c ∈ l₂ := by
  obtain ⟨hl₁, hc₁, hu₁, hw₁⟩ := h₁
  obtain ⟨hl₂, hc₂, hw₂, hv₂⟩ := h₂
  obtain ⟨c, t, rfl⟩ : ∃ c t, l₂ = c :: t := List.exists_cons_of_ne_nil hl₂
  have hlast : l₁.getLast hl₁ = c :=
    isCell_eq_of_mem (hc₁ _ (List.getLast_mem hl₁)) (hc₂ c List.mem_cons_self) hw₁ hw₂
  simp only [List.tail_cons]
  refine ⟨⟨by simp [hl₁], fun x hx => ?_, ?_, ?_⟩, ?_, by simp, fun x hx => ?_⟩
  · rcases List.mem_append.1 hx with h | h
    · exact hc₁ x h
    · exact hc₂ x (List.mem_cons_of_mem _ h)
  · rw [List.head_append_of_ne_nil hl₁]; exact hu₁
  · rcases eq_or_ne t [] with ht | ht
    · subst ht; simp only [List.append_nil]; rw [hlast]; simpa using hv₂
    · rw [List.getLast_append_of_ne_nil _ ht]
      rwa [List.getLast_cons ht] at hv₂
  · refine List.IsChain.append g₁ g₂.tail fun x hx y hy => ?_
    rw [List.getLast?_eq_some_getLast hl₁, Option.mem_some_iff, hlast] at hx
    subst hx
    obtain ⟨y', t', rfl⟩ : ∃ y' t', t = y' :: t' := by
      cases t with
      | nil => simp at hy
      | cons a b => exact ⟨a, b, rfl⟩
    simp only [List.head?_cons, Option.mem_some_iff] at hy
    subst hy
    exact (List.isChain_cons_cons.1 g₂).1
  · rcases List.mem_append.1 hx with h | h
    · exact Or.inl h
    · exact Or.inr (List.mem_cons_of_mem _ h)

/-- **Concatenation of `n` good cell sequences** `p_i → p_{i+1}` into one `p_0 → p_n` with
`d ≤ Σ dᵢ`, all cells among the given ones. -/
theorem l53_concat_chain (p : ℕ → ℂ) (L : ℕ → List DyBox) (S : Set DyBox) :
    ∀ n : ℕ, 1 ≤ n → (∀ i < n, JoinsCells m δ (p i) (p (i + 1)) (L i) ∧ IsGoodSeq ε (L i) ∧
      ∀ c ∈ L i, c ∈ S) →
    ∃ l : List DyBox, JoinsCells m δ (p 0) (p n) l ∧ IsGoodSeq ε l ∧ (∀ c ∈ l, c ∈ S) ∧
      l.length ≤ ∑ i ∈ Finset.range n, (L i).length
  | 0, h, _ => absurd h (by norm_num)
  | 1, _, hL => ⟨L 0, (hL 0 one_pos).1, (hL 0 one_pos).2.1, (hL 0 one_pos).2.2, by simp⟩
  | n + 2, _, hL => by
    obtain ⟨l, hj, hg, hS, hlen⟩ := l53_concat_chain p L S (n + 1) (by omega)
      (fun i hi => hL i (by omega))
    obtain ⟨j₂, g₂, S₂⟩ := hL (n + 1) (by omega)
    obtain ⟨hj', hg', hlen', hmem⟩ := l53_concat_two hj j₂ hg g₂
    refine ⟨_, hj', hg', fun c hc => ?_, ?_⟩
    · rcases hmem c hc with h | h
      · exact hS c h
      · exact S₂ c h
    · rw [Finset.sum_range_succ]; omega

/-! ### The corrected form of `hdes` -/

/-- **DZZ L5.3 part 1 from the desirability event with `𝒟₁` at `E X_k + L^{0.97}`**
(corrected (Eq.calD1), see the module docstring; copy of `dzzLem53Event_of_desirable` and
`dzzLem53Event_of_chain`, S5L53E1–E2). -/
theorem dzzLem53Event_of_desirable97 {P : Measure Ω} {ν : Ω → Measure ℂ} {u v : ℂ}
    (h : ∃ k₀ : ℕ, ∀ k l : ℕ, k₀ ≤ k → 1 ≤ l → l ≤ k →
      P (l53DesirableEvent ν u v ((2 : ℝ)⁻¹ ^ (k + l))
        ((∫ ω', logMinLGD (ν ω') ((2 : ℝ)⁻¹ ^ k) {u} {v} ∂P) + ((k : ℝ) * Real.log 2) ^ (0.97 : ℝ))
        ((∫ ω', logMinLGD (ν ω') ((2 : ℝ)⁻¹ ^ l) {u} {v} ∂P) + ((k : ℝ) * Real.log 2) ^ (0.98 : ℝ))
        ((∫ ω', logMinLGD (ν ω') ((2 : ℝ)⁻¹ ^ l) {u} {v} ∂P) +
          2 * ((k : ℝ) * Real.log 2) ^ (0.98 : ℝ)))ᶜ ≤
        ENNReal.ofReal (2 * Real.exp (-((k : ℝ) * Real.log 2) ^ (0.22 : ℝ)))) :
    DZZLem53Event P ν u v := by
  obtain ⟨k₀, hk₀⟩ := h
  refine ⟨max k₀ 2, fun k l hk hl hlk => ?_⟩
  set L : ℝ := (k : ℝ) * Real.log 2 with hL
  have hL1 : 1 ≤ L := by
    have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast le_of_max_le_right hk
    have : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    nlinarith
  have hL0 : 0 ≤ L := by linarith
  have h98 : 0 ≤ L ^ (0.98 : ℝ) := Real.rpow_nonneg hL0 _
  refine le_trans (measure_mono ?_) (hk₀ k l (le_of_max_le_left hk) hl hlk)
  intro ω hω hmem
  simp only [mem_ofPred_eq] at hω
  have hmem' := l53DesirableEvent_subset (T₂ := (∫ ω', logMinLGD (ν ω') ((2 : ℝ)⁻¹ ^ l) {u} {v} ∂P) +
    4 * L ^ (0.98 : ℝ)) (by linarith) (by linarith) hmem
  have hEk : 0 ≤ ∫ ω', logMinLGD (ν ω') ((2 : ℝ)⁻¹ ^ k) {u} {v} ∂P :=
    integral_nonneg fun ω' => logMinLGD_nonneg _ _ _ _
  have hEl : 0 ≤ ∫ ω', logMinLGD (ν ω') ((2 : ℝ)⁻¹ ^ l) {u} {v} ∂P :=
    integral_nonneg fun ω' => logMinLGD_nonneg _ _ _ _
  have h97 : L ^ (0.97 : ℝ) ≤ L ^ (0.98 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hp : 0 ≤ L ^ (0.97 : ℝ) := Real.rpow_nonneg hL0 _
  have hb := logMinLGD_le_of_mem_l53ChainEvent (by linarith) hmem'
  linarith

/-- **DZZ Lemma 5.3 at `μIn` from the corrected desirability bound** (`𝒟₁` at `L^{0.97}`;
copy of `dzzLem53Exp_dzzMuIn_of_desirable`, S5L53E3). -/
theorem dzzLem53Exp_dzzMuIn_of_desirable97 {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hdes : ∀ u ∈ dzzVbar, ∀ v ∈ dzzVbar, u ≠ v → ∃ k₀ : ℕ, ∀ k l : ℕ, k₀ ≤ k → 1 ≤ l → l ≤ k →
      P (l53DesirableEvent (fun ω => dzzWall (tildeBox u v) (dzzMuIn γ W ω)) u v
        ((2 : ℝ)⁻¹ ^ (k + l))
        ((∫ ω', logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω')) ((2 : ℝ)⁻¹ ^ k) {u} {v} ∂P) +
          ((k : ℝ) * Real.log 2) ^ (0.97 : ℝ))
        ((∫ ω', logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω')) ((2 : ℝ)⁻¹ ^ l) {u} {v} ∂P) +
          ((k : ℝ) * Real.log 2) ^ (0.98 : ℝ))
        ((∫ ω', logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω')) ((2 : ℝ)⁻¹ ^ l) {u} {v} ∂P) +
          2 * ((k : ℝ) * Real.log 2) ^ (0.98 : ℝ)))ᶜ ≤
        ENNReal.ofReal (2 * Real.exp (-((k : ℝ) * Real.log 2) ^ (0.22 : ℝ)))) :
    ∃ χ, DZZLem53Exp P (dzzMuIn γ W) χ :=
  dzzLem53Exp_dzzMuIn_of_event_only hW hγ hγ2
    (fun u hu v hv huv => dzzLem53Event_of_desirable97 (hdes u hu v hv huv))

end DZZ
end LQGMetric
