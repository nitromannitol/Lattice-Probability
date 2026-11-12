/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53P2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53P1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53L5

/-!
# DZZ Lemma 5.3, part 1: the adapter in the form of DEC-131 §2 (P2-DZZ53P, packet P-131B)

DEC-131 §2/§5, P-131B, on the interface of P-131A (S5L53L5: `L53Q`, `l53Chain`, `l53D1EventB`,
`l53Chain_spec`, `l53Chain_ne_nil`). Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`
l. 2363–2391 (`𝓔*` and `𝒟₁` on the chain `𝒞` of Lemma 3.13 boxes), l. 2504–2522 (desirability).

* `l53BadB` (DEC-131 §2 verbatim): `𝓔* ∩ 𝒟₁` on the box chain, and the selected chain
  `l53Chain` is not desirable.
* `l53_mem_desirable_chain`, **`l53_hdes_of_D1B`** (copy of `l53_hdes_of_D1R`, S5L53I5).
* `L53RefineB`: the refinement `𝒟₁(cells) ∩ {u, v good} ⊆ 𝒟₁(boxes)` (DEC-131 §2
  `l53D1EventR_subset_l53D1EventB`, P-131A, being proved by P2-DZZ53LR) is a **hypothesis** here, in
  the form `l313_assemble` + `l313_len_asym` give: box region `cthickening (2 δ^{C_Mc}) R`, threshold
  `T + (log δ⁻¹)^{0.6}`. (With the *same* region `R` for boxes, as written in DEC-131 §2, the
  inclusion is not what the construction gives: the clause `b ∈ cellsMeeting R` of `L53Q` is for the
  box, and a box in a cell meeting `R` is only within `√2 s_𝖢 ≤ 2 δ^{C_Mc}` of `R`.)
* **`dzzLem53Exp_dzzMuIn_of_hd_hbadB`**: `∃ α* > 0`, `HighProb 𝓔_{δ,α*}` and
  `L53RefineB α* → hbadB α* → DZZ Lemma 5.3 at μIn` (`hd` by `l53_hd_holds`, `hreg` by
  `l53_hregN`, good points by `dzz_lemma312_proved`, via `l53_D1_probG`, S5L53P1).

Own elementary proofs (copies of the cited declarations).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open DyBox WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The bad event of nodes 2–4 on the box chain** (DEC-131 §2; replaces `l53BadR`, S5L53I5). -/
def l53BadB (γ : ℝ) (W : WNSpace → Ω → ℝ) (αs : ℝ) (ν : Ω → Measure ℂ) (u v : ℂ) (k l : ℕ)
    (R : Set ℂ) (T₁ T T' : ℝ) : Set Ω :=
  l53D1EventB γ W αs ((2 : ℝ)⁻¹ ^ k) u v R T₁ ∩
    {ω | ¬ L53ChainDesirable (ν ω) u v ((2 : ℝ)⁻¹ ^ (k + l)) T T'
      (l53Chain γ W αs ((2 : ℝ)⁻¹ ^ k) u v R T₁ ω)}

/-- **The refinement of the cell chain into Lemma 3.13 boxes** (DEC-131 §2
`l53D1EventR_subset_l53D1EventB`, P-131A): for small `δ`, on `{u, v good}` a cell chain of `𝒟₁`
(region `R`, `d ≤ e^T`) yields a box chain (region `cthickening (2 δ^{C_Mc}) R`,
`d ≤ e^{T + (log δ⁻¹)^{0.6}}`). -/
def L53RefineB (γ : ℝ) (W : WNSpace → Ω → ℝ) (αs : ℝ) : Prop :=
  ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀, ∀ (u v : ℂ) (R : Set ℂ) (T : ℝ),
    l53D1EventR γ W αs δ u v R T ∩ l53GoodUV γ W αs δ u v ⊆
      l53D1EventB γ W αs δ u v (Metric.cthickening (2 * δ ^ dzzCMc γ) R)
        (T + Real.log δ⁻¹ ^ (0.6 : ℝ))

omit [MeasurableSpace Ω] in
lemma l53D1EventB_mono {γ αs δ T T' : ℝ} {W : WNSpace → Ω → ℝ} {u v : ℂ} {R : Set ℂ}
    (hT : T ≤ T') : l53D1EventB γ W αs δ u v R T ⊆ l53D1EventB γ W αs δ u v R T' := by
  rintro ω ⟨hs, hne⟩
  obtain ⟨h1, h2, h3⟩ := l53Chain_spec hne
  exact ⟨hs, l53Chain_ne_nil ⟨h1, h2, h3.trans (Real.exp_le_exp.2 hT)⟩⟩

/-- The boxes of an `L313Q` chain are at level `n_𝖢 + 2 n_{ε*}` (from `s_B = s_𝖢 ε*²`). -/
lemma l53Q_level {m : DyBox → ℝ} {δ : ℝ} {N : ℕ} {u v : ℂ} {c : List DyBox}
    (h : L313Q ((2 : ℝ)⁻¹ ^ N) u v (fun b => IsCell m δ b) c) :
    ∀ b ∈ c, ∃ C : DyBox, IsCell m δ C ∧ b.closedBox ⊆ C.closedBox ∧ b.n = C.n + 2 * N := by
  intro b hb
  obtain ⟨C, hC, hbC, hside⟩ := h.2.1 b hb
  refine ⟨C, hC, hbC, ?_⟩
  have e : (2 : ℝ)⁻¹ ^ b.n = (2 : ℝ)⁻¹ ^ (C.n + 2 * N) := by
    have : b.side = C.side * ((2 : ℝ)⁻¹ ^ N) ^ 2 := hside
    unfold DyBox.side at this
    rw [this, ← pow_mul, ← pow_add, mul_comm N 2]
  exact pow_right_injective₀ (by norm_num : (0 : ℝ) < 2⁻¹) (by norm_num) e

omit [MeasurableSpace Ω] in
/-- **A desirable selected chain lies in `l53DesirableEvent`** (copy of `l53_mem_desirableB`,
S5L53L2). -/
theorem l53_mem_desirable_chain {γ αs δ₀ δ T₁ T T' : ℝ} {W : WNSpace → Ω → ℝ}
    {ν : Ω → Measure ℂ} {u v : ℂ} {R : Set ℂ} {ω : Ω}
    (hD : ω ∈ l53D1EventB γ W αs δ₀ u v R T₁)
    (hdes : L53ChainDesirable (ν ω) u v δ T T' (l53Chain γ W αs δ₀ u v R T₁ ω))
    (hsep : 2 * δ₀ ^ dzzCMc γ < ‖u - v‖) :
    ω ∈ l53DesirableEvent ν u v δ T₁ T T' := by
  obtain ⟨hsize, hne⟩ := hD
  have hQ := l53Chain_spec hne
  have hsafe := l53Q_level hQ.1
  exact ⟨_, l53_two_le_length_box hsize hQ.1.1.1 hsafe hsep, hQ.2.2, l53Iface _,
    fun _ hi1 hi => l53Iface_pos_box hsafe hQ.1.1.2 hi1 hi, hdes.1, hdes.2.1, hdes.2.2⟩

/-- **`hdes` for one pair from `𝒟₁` on the box chain and `l53BadB`** (copy of `l53_hdes_of_D1R`,
S5L53I5). -/
theorem l53_hdes_of_D1B {P : Measure Ω} {γ αs : ℝ} {W : WNSpace → Ω → ℝ} {ν : Ω → Measure ℂ}
    {u v : ℂ} (huv : u ≠ v) {EX : ℕ → ℝ} {R : ℕ → Set ℂ}
    (hD1 : ∃ k₀ : ℕ, ∀ k ≥ k₀,
      P (l53D1EventB γ W αs ((2 : ℝ)⁻¹ ^ k) u v (R k)
        (EX k + ((k : ℝ) * Real.log 2) ^ (0.97 : ℝ)))ᶜ ≤
        ENNReal.ofReal (Real.exp (-((k : ℝ) * Real.log 2) ^ (0.22 : ℝ))))
    (hbad : ∃ k₀ : ℕ, ∀ k l : ℕ, k₀ ≤ k → 1 ≤ l → l ≤ k →
      P (l53BadB γ W αs ν u v k l (R k) (EX k + ((k : ℝ) * Real.log 2) ^ (0.97 : ℝ))
        (EX l + ((k : ℝ) * Real.log 2) ^ (0.98 : ℝ))
        (EX l + 2 * ((k : ℝ) * Real.log 2) ^ (0.98 : ℝ))) ≤
        ENNReal.ofReal (Real.exp (-((k : ℝ) * Real.log 2) ^ (0.22 : ℝ)))) :
    ∃ k₀ : ℕ, ∀ k l : ℕ, k₀ ≤ k → 1 ≤ l → l ≤ k →
      P (l53DesirableEvent ν u v ((2 : ℝ)⁻¹ ^ (k + l))
        (EX k + ((k : ℝ) * Real.log 2) ^ (0.97 : ℝ))
        (EX l + ((k : ℝ) * Real.log 2) ^ (0.98 : ℝ))
        (EX l + 2 * ((k : ℝ) * Real.log 2) ^ (0.98 : ℝ)))ᶜ ≤
        ENNReal.ofReal (2 * Real.exp (-((k : ℝ) * Real.log 2) ^ (0.22 : ℝ))) := by
  obtain ⟨k₁, h₁⟩ := hD1
  obtain ⟨k₂, h₂⟩ := hbad
  obtain ⟨k₃, h₃⟩ := l53_ev_sep (dzzCMc γ) (dzzCMc_pos γ) (norm_pos_iff.2 (sub_ne_zero.2 huv))
  refine ⟨max (max k₁ k₂) k₃, fun k l hk hl hlk => ?_⟩
  have hk1 : k₁ ≤ k := by omega
  have hk2 : k₂ ≤ k := by omega
  have hk3 : k₃ ≤ k := by omega
  have hsub : (l53DesirableEvent ν u v ((2 : ℝ)⁻¹ ^ (k + l))
        (EX k + ((k : ℝ) * Real.log 2) ^ (0.97 : ℝ))
        (EX l + ((k : ℝ) * Real.log 2) ^ (0.98 : ℝ))
        (EX l + 2 * ((k : ℝ) * Real.log 2) ^ (0.98 : ℝ)))ᶜ ⊆
      (l53D1EventB γ W αs ((2 : ℝ)⁻¹ ^ k) u v (R k)
        (EX k + ((k : ℝ) * Real.log 2) ^ (0.97 : ℝ)))ᶜ ∪
        l53BadB γ W αs ν u v k l (R k) (EX k + ((k : ℝ) * Real.log 2) ^ (0.97 : ℝ))
          (EX l + ((k : ℝ) * Real.log 2) ^ (0.98 : ℝ))
          (EX l + 2 * ((k : ℝ) * Real.log 2) ^ (0.98 : ℝ)) := by
    intro ω hω
    by_contra hcon
    simp only [mem_union, mem_compl_iff, not_or, not_not] at hcon
    obtain ⟨hD, hB⟩ := hcon
    have hdes : L53ChainDesirable (ν ω) u v ((2 : ℝ)⁻¹ ^ (k + l))
        (EX l + ((k : ℝ) * Real.log 2) ^ (0.98 : ℝ))
        (EX l + 2 * ((k : ℝ) * Real.log 2) ^ (0.98 : ℝ))
        (l53Chain γ W αs ((2 : ℝ)⁻¹ ^ k) u v (R k)
          (EX k + ((k : ℝ) * Real.log 2) ^ (0.97 : ℝ)) ω) := by
      by_contra hn
      exact hB ⟨hD, hn⟩
    exact hω (l53_mem_desirable_chain hD hdes (h₃ k hk3))
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  refine (add_le_add (h₁ k hk1) (h₂ k l hk2 hl hlk)).trans (le_of_eq ?_)
  rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
  ring_nf

lemma l53_ev_965_6 : ∀ᶠ L : ℝ in atTop, L ^ (0.965 : ℝ) + L ^ (0.6 : ℝ) ≤ L ^ (0.97 : ℝ) := by
  filter_upwards [l53_ev_mul_rpow_le 2 (by norm_num : (0.965 : ℝ) < 0.97),
    eventually_ge_atTop 1] with L h hL1
  have : L ^ (0.6 : ℝ) ≤ L ^ (0.965 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  linarith

/-- **`𝒟₁` on the box chain** from `𝒟₁ ∩ {u, v good}` on cells (`l53_D1_probG`, S5L53P1) and the
refinement `L53RefineB`. -/
theorem l53_D1B_prob {P : Measure Ω} {γ αs : ℝ} {W : WNSpace → Ω → ℝ} {u v : ℂ} {EX : ℕ → ℝ}
    {R : ℕ → Set ℂ} (href : L53RefineB γ W αs)
    (hD1 : ∃ k₀ : ℕ, ∀ k ≥ k₀,
      P (l53D1EventR γ W αs ((2 : ℝ)⁻¹ ^ k) u v (R k)
          (EX k + ((k : ℝ) * Real.log 2) ^ (0.965 : ℝ)) ∩
        l53GoodUV γ W αs ((2 : ℝ)⁻¹ ^ k) u v)ᶜ ≤
        ENNReal.ofReal (Real.exp (-((k : ℝ) * Real.log 2) ^ (0.22 : ℝ)))) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀,
      P (l53D1EventB γ W αs ((2 : ℝ)⁻¹ ^ k) u v
        (Metric.cthickening (2 * ((2 : ℝ)⁻¹ ^ k) ^ dzzCMc γ) (R k))
        (EX k + ((k : ℝ) * Real.log 2) ^ (0.97 : ℝ)))ᶜ ≤
        ENNReal.ofReal (Real.exp (-((k : ℝ) * Real.log 2) ^ (0.22 : ℝ))) := by
  obtain ⟨δ₀, hδ₀, href⟩ := href
  obtain ⟨k₁, h₁⟩ := hD1
  obtain ⟨k₂, hk₂⟩ := exists_pow_lt_of_lt_one hδ₀ (by norm_num : (2 : ℝ)⁻¹ < 1)
  obtain ⟨k₃, h₃⟩ := eventually_atTop.1 (l53_tendsto_kL.eventually l53_ev_965_6)
  refine ⟨max (max k₁ k₂) k₃, fun k hk => ?_⟩
  have hk1 : k₁ ≤ k := by omega
  have hk2 : k₂ ≤ k := by omega
  have hk3 : k₃ ≤ k := by omega
  have hδ : (2 : ℝ)⁻¹ ^ k ∈ Ioo (0 : ℝ) δ₀ :=
    ⟨by positivity, (pow_le_pow_of_le_one (by norm_num) (by norm_num) hk2).trans_lt hk₂⟩
  refine le_trans (measure_mono (compl_subset_compl.2 ?_)) (h₁ k hk1)
  refine (href _ hδ u v (R k) _).trans (l53D1EventB_mono ?_)
  rw [log_inv_two_inv_pow]
  linarith [h₃ k hk3]

/-- **DZZ Lemma 5.3 at `μIn` from the refinement and `hbadB`** (DEC-131 §2, P-131B): there is
`α* > 0` (the larger of the `α*` of `l53_hregN` and of `dzz_lemma312_proved`) such that the
refinement `L53RefineB` and the bound on `l53BadB` (box region
`cthickening (2 δ^{C_Mc}) (cthickening (8 δ^{C_Mc}) (l53Region u v))`, box threshold
`E X_k + L^{0.97}`) give DZZ Lemma 5.3. `hd` is `l53_hd_holds`. -/
theorem dzzLem53Exp_dzzMuIn_of_hd_hbadB {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ αs : ℝ, 0 < αs ∧ HighProb P (fun δ => eventEDeltaAlpha γ W αs δ) ∧
      (L53RefineB γ W αs →
      (∀ u ∈ dzzVbar, ∀ v ∈ dzzVbar, u ≠ v → ∃ k₀ : ℕ, ∀ k l : ℕ, k₀ ≤ k → 1 ≤ l → l ≤ k →
        P (l53BadB γ W αs (fun ω => dzzWall (tildeBox u v) (dzzMuIn γ W ω)) u v k l
          (Metric.cthickening (2 * ((2 : ℝ)⁻¹ ^ k) ^ dzzCMc γ)
            (Metric.cthickening (8 * ((2 : ℝ)⁻¹ ^ k) ^ dzzCMc γ) (l53Region u v)))
          ((∫ ω', logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω')) ((2 : ℝ)⁻¹ ^ k) {u} {v} ∂P) +
            ((k : ℝ) * Real.log 2) ^ (0.97 : ℝ))
          ((∫ ω', logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω')) ((2 : ℝ)⁻¹ ^ l) {u} {v} ∂P) +
            ((k : ℝ) * Real.log 2) ^ (0.98 : ℝ))
          ((∫ ω', logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω')) ((2 : ℝ)⁻¹ ^ l) {u} {v} ∂P) +
            2 * ((k : ℝ) * Real.log 2) ^ (0.98 : ℝ))) ≤
          ENNReal.ofReal (Real.exp (-((k : ℝ) * Real.log 2) ^ (0.22 : ℝ)))) →
      ∃ χ, DZZLem53Exp P (dzzMuIn γ W) χ) := by
  obtain ⟨αr, hαr, -, hreg⟩ := l53_hregN hW hγ hγ2
  obtain ⟨αg, hαg, -, δ₀, hδ₀, hg⟩ := dzz_lemma312_proved hW hγ hγ2
  have hα : 0 < max αr αg := lt_max_of_lt_left hαr
  refine ⟨max αr αg, hα, dzz_lemma34_of_pos hW hγ hγ2 hα, fun href hbad => ?_⟩
  obtain ⟨k₀, hk₀⟩ := exists_pow_lt_of_lt_one hδ₀ (by norm_num : (2 : ℝ)⁻¹ < 1)
  have hgood : ∀ u ∈ dzzVbar, ∀ v ∈ dzzVbar, ∃ k₀ : ℕ, ∀ k ≥ k₀,
      P (eventRegular γ W αg ((2 : ℝ)⁻¹ ^ k) u v)ᶜ ≤
        ENNReal.ofReal (Real.exp (-((k : ℝ) * Real.log 2) ^ (1 / 4 : ℝ))) := by
    intro u hu v hv
    refine ⟨k₀, fun k hk => ?_⟩
    have hδ : (2 : ℝ)⁻¹ ^ k ∈ Ioo (0 : ℝ) δ₀ :=
      ⟨by positivity, (pow_le_pow_of_le_one (by norm_num) (by norm_num) hk).trans_lt hk₀⟩
    have huV : u ∈ dzzV := by simpa [l53W_zero] using l53I_w_mem_dzzV hu hv (i := 0) (by norm_num)
    have hvV : v ∈ dzzV := by simpa [l53W_nine] using l53I_w_mem_dzzV hu hv (i := 9) le_rfl
    have := hg _ hδ u huV v hvV
    rwa [log_inv_two_inv_pow] at this
  exact dzzLem53Exp_dzzMuIn_of_desirable97 hW hγ hγ2 fun u hu v hv huv =>
    l53_hdes_of_D1B
      (R := fun k => Metric.cthickening (2 * ((2 : ℝ)⁻¹ ^ k) ^ dzzCMc γ)
        (Metric.cthickening (8 * ((2 : ℝ)⁻¹ ^ k) ^ dzzCMc γ) (l53Region u v)))
      (EX := fun k =>
        ∫ ω', logMinLGD (dzzWall (tildeBox u v) (dzzMuIn γ W ω')) ((2 : ℝ)⁻¹ ^ k) {u} {v} ∂P) huv
      (l53_D1B_prob (R := fun k => Metric.cthickening (8 * ((2 : ℝ)⁻¹ ^ k) ^ dzzCMc γ)
          (l53Region u v)) href
        (l53_D1_probG (le_max_left _ _) (le_max_right _ _) (hreg u hu v hv) (hgood u hu v hv)
          (l53_hd_holds hW hγ hγ2 u hu v hv huv)))
      (hbad u hu v hv huv)

end DZZ
end LQGMetric
