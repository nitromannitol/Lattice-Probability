/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53P1 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53L2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53H5
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L12X15

/-!
# DZZ Lemma 5.3, part 1: the adapter for the box-chain bad event (P2-DZZ53P, packet P-131B)

DEC-131 §2/§5, packet P-131B. Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`
l. 2363–2391 (`𝓔*`, (Eq.calD1)): the chain `𝒞` of `𝓔*` consists of Lemma 3.13 boxes, which exist
only when `u` and `v` are *good points* (Lemma 3.13 needs `u, v` good, l. 1314–1316). Hence the
event `𝒟₁` of the adapter is the cell event `l53D1EventR` (S5L53I5) **intersected with
`{u, v good}`** (`l53GoodUV`), and the bad event of nodes 2–4 is A's `l53BadBox` (S5L53L2) on the same
intersection.

* `epsStarN_mono`, `epsStar_anti`, `isGoodSeq_mono`, `isGoodPoint_mono`: monotonicity in `α*`
  (larger `α*` = smaller `ε*` = weaker), used to take one `α*` for the walled L3.12 with margin
  (`l53_hregN`) and the global L3.12 (`dzz_lemma312_proved`, good points of `u`, `v`).
* `l53_D1_probG`: copy of `l53_D1_probR` (S5L53I5) with the good points of `u`, `v` added and the
  cell threshold `E X_k + L^{0.965}` (room `L^{0.97} − L^{0.965}` for the `2 log 4 · n_{ε*}` of the
  Lemma 3.13 refinement, which lengthens the chain by the factor `4^{2 n_{ε*}}`).
* `l53_hdes_of_D1G`: copy of `l53_hdes_of_D1Box` (S5L53L2) with the good-point event.
* **`dzzLem53Exp_dzzMuIn_of_hbadBG`**: there is `α* > 0` such that the bound on
  `l53BadBox ∩ l53GoodUV` gives DZZ Lemma 5.3 at `μIn` (`hd` by `l53_hd_holds`, `hreg` by
  `l53_hregN`, good points by `dzz_lemma312_proved`). This is the good-point version of P2-DZZ53L's
  `dzzLem53Exp_dzzMuIn_of_hd_hbadBox` (S5L53L3). That version's `hbadBox` has no good-point event, and
  its `α*` is that of `l53_hregN` alone. So the wiring cannot remove `{u or v bad}` from `l53BadBox`
  (the box chain needs good `u`, `v`, Lemma 3.13). The adapter in the DEC-131 §2 form is in S5L53P2.

Own elementary proofs (copies of the cited Lean declarations).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open DyBox WhiteNoise

/-! ### Monotonicity in `α*` -/

lemma epsStarThr_anti {αs αs' δ : ℝ} (h : αs ≤ αs') (hδ : 1 ≤ Real.log δ⁻¹) :
    epsStarThr αs' δ ≤ epsStarThr αs δ := by
  unfold epsStarThr
  refine Real.exp_le_exp.2 (neg_le_neg ?_)
  have h1 : 0 ≤ Real.sqrt (Real.log δ⁻¹) * Real.log (Real.log δ⁻¹) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg hδ)
  simpa [mul_assoc] using mul_le_mul_of_nonneg_right h h1

lemma epsStarN_mono {αs αs' δ : ℝ} (h : αs ≤ αs') (hδ : 1 ≤ Real.log δ⁻¹) :
    epsStarN αs δ ≤ epsStarN αs' δ := by
  classical
  unfold epsStarN
  exact Nat.find_mono fun n hn => hn.trans (epsStarThr_anti h hδ)

lemma epsStar_anti {αs αs' δ : ℝ} (h : αs ≤ αs') (hδ : 1 ≤ Real.log δ⁻¹) :
    epsStar αs' δ ≤ epsStar αs δ :=
  pow_le_pow_of_le_one (by norm_num) (by norm_num) (epsStarN_mono h hδ)

lemma epsStar_pos' (αs δ : ℝ) : 0 < epsStar αs δ := by unfold epsStar; positivity

lemma isGoodSeq_mono {ε ε' : ℝ} (h0 : 0 < ε') (h : ε' ≤ ε) {l : List DyBox}
    (hl : IsGoodSeq ε l) : IsGoodSeq ε' l :=
  List.IsChain.imp (fun b _ hb => ⟨hb.1,
    (mul_le_mul_of_nonneg_right h (side_pos' b).le).trans hb.2.1,
    hb.2.2.trans (div_le_div_of_nonneg_left (side_pos' b).le h0 h)⟩) hl

lemma isGoodPoint_mono {m : DyBox → ℝ} {δ ε ε' : ℝ} (h : ε' ≤ ε) {x : ℂ}
    (hx : IsGoodPoint m δ ε x) : IsGoodPoint m δ ε' x := fun C hC hxC w hw hwV =>
  (mul_le_mul_of_nonneg_right h (side_pos' C).le).trans (hx C hC hxC w hw hwV)

lemma one_le_log_two_inv_pow {k : ℕ} (hk : 2 ≤ k) : 1 ≤ Real.log ((2 : ℝ)⁻¹ ^ k)⁻¹ := by
  rw [log_inv_two_inv_pow]
  have : (1 / 2 : ℝ) ≤ Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **`u` and `v` are good points** (Definition 3.11, l. 1284–1285) at `ε*_δ`: the hypothesis of
Lemma 3.13 under which the box chain `𝒞` of `𝓔*` exists. -/
def l53GoodUV (γ : ℝ) (W : WNSpace → Ω → ℝ) (αs δ : ℝ) (u v : ℂ) : Set Ω :=
  {ω | IsGoodPoint (approxLQG γ W ω) δ (epsStar αs δ) u ∧
    IsGoodPoint (approxLQG γ W ω) δ (epsStar αs δ) v}

/-! ### `𝒟₁ ∩ {u, v good}` -/

lemma l53_ev_D1G : ∀ᶠ L : ℝ in atTop,
    Real.log 9 + L ^ (0.96 : ℝ) + L ^ (0.6 : ℝ) ≤ L ^ (0.965 : ℝ) ∧
      19 * Real.exp (-L ^ (1 / 4 : ℝ)) ≤ Real.exp (-L ^ (0.22 : ℝ)) := by
  filter_upwards [l53_ev_mul_rpow_le (Real.log 9) (p := 0) (by norm_num : (0 : ℝ) < 0.96),
    l53_ev_mul_rpow_le 3 (by norm_num : (0.96 : ℝ) < 0.965),
    l53_ev_mul_rpow_le (Real.log 19) (p := 0) (by norm_num : (0 : ℝ) < 0.22),
    l53_ev_mul_rpow_le 2 (by norm_num : (0.22 : ℝ) < 1 / 4),
    eventually_ge_atTop 1] with L h1 h2 h3 h4 hL1
  simp only [Real.rpow_zero, mul_one] at h1 h3
  refine ⟨?_, ?_⟩
  · have : L ^ (0.6 : ℝ) ≤ L ^ (0.96 : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    linarith
  · rw [show (19 : ℝ) = Real.exp (Real.log 19) by rw [Real.exp_log (by norm_num)],
      ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)

/-- **`𝒟₁ ∩ {u, v good}`** (copy of `l53_D1_probR`, S5L53I5, with the global L3.12 for the good
points and the cell threshold `L^{0.965}`): `hreg` at `α_r ≤ α*`, L3.12 at `α_g ≤ α*`. -/
theorem l53_D1_probG {P : Measure Ω} {γ αs αr αg : ℝ} {W : WNSpace → Ω → ℝ} {u v : ℂ}
    {EX : ℕ → ℝ} (hαr : αr ≤ αs) (hαg : αg ≤ αs)
    (hreg : ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ i < 9,
      P (eventRegularNear (tildeBox (l53W u v i) (l53W u v (i + 1)))
        (8 * ((2 : ℝ)⁻¹ ^ k) ^ dzzCMc γ) γ W αr ((2 : ℝ)⁻¹ ^ k)
        (l53W u v i) (l53W u v (i + 1)))ᶜ ≤
        ENNReal.ofReal (Real.exp (-((k : ℝ) * Real.log 2) ^ (1 / 4 : ℝ))))
    (hgood : ∃ k₀ : ℕ, ∀ k ≥ k₀, P (eventRegular γ W αg ((2 : ℝ)⁻¹ ^ k) u v)ᶜ ≤
        ENNReal.ofReal (Real.exp (-((k : ℝ) * Real.log 2) ^ (1 / 4 : ℝ))))
    (hd : ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ i < 9,
      P (l53DiEvent γ W ((2 : ℝ)⁻¹ ^ k) u v i (EX k + ((k : ℝ) * Real.log 2) ^ (0.96 : ℝ)))ᶜ ≤
        ENNReal.ofReal (Real.exp (-((k : ℝ) * Real.log 2) ^ (1 / 4 : ℝ)))) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀,
      P (l53D1EventR γ W αs ((2 : ℝ)⁻¹ ^ k) u v
          (Metric.cthickening (8 * ((2 : ℝ)⁻¹ ^ k) ^ dzzCMc γ) (l53Region u v))
          (EX k + ((k : ℝ) * Real.log 2) ^ (0.965 : ℝ)) ∩
        l53GoodUV γ W αs ((2 : ℝ)⁻¹ ^ k) u v)ᶜ ≤
        ENNReal.ofReal (Real.exp (-((k : ℝ) * Real.log 2) ^ (0.22 : ℝ))) := by
  obtain ⟨k₁, h₁⟩ := hreg
  obtain ⟨k₂, h₂⟩ := hd
  obtain ⟨k₄, h₄⟩ := hgood
  obtain ⟨k₃, h₃⟩ := eventually_atTop.1 (l53_tendsto_kL.eventually l53_ev_D1G)
  refine ⟨max (max (max k₁ k₂) k₃) (max k₄ 2), fun k hk => ?_⟩
  have hk1 : k₁ ≤ k := by omega
  have hk2 : k₂ ≤ k := by omega
  have hk3 : k₃ ≤ k := by omega
  have hk4 : k₄ ≤ k := by omega
  have hk5 : 2 ≤ k := by omega
  obtain ⟨hA, hB⟩ := h₃ k hk3
  set δ : ℝ := (2 : ℝ)⁻¹ ^ k with hδ
  set L : ℝ := (k : ℝ) * Real.log 2 with hL
  have hlog1 : 1 ≤ Real.log δ⁻¹ := one_le_log_two_inv_pow hk5
  have hεr : epsStar αs δ ≤ epsStar αr δ := epsStar_anti hαr hlog1
  have hεg : epsStar αs δ ≤ epsStar αg δ := epsStar_anti hαg hlog1
  set G : ℕ → Set Ω := fun i =>
    eventRegularNear (tildeBox (l53W u v i) (l53W u v (i + 1))) (8 * δ ^ dzzCMc γ) γ W αr δ
      (l53W u v i)
      (l53W u v (i + 1)) ∩ l53DiEvent γ W δ u v i (EX k + L ^ (0.96 : ℝ)) with hG
  have hsub : (⋂ i ∈ Finset.range 9, G i) ∩ eventRegular γ W αg δ u v ⊆
      l53D1EventR γ W αs δ u v (Metric.cthickening (8 * δ ^ dzzCMc γ) (l53Region u v))
        (EX k + L ^ (0.965 : ℝ)) ∩ l53GoodUV γ W αs δ u v := by
    rintro ω ⟨hω, hreg⟩
    refine ⟨?_, isGoodPoint_mono hεg hreg.2.1, isGoodPoint_mono hεg hreg.2.2.1⟩
    simp only [mem_iInter, Finset.mem_range] at hω
    refine ⟨(hω 0 (by norm_num)).1.1.1, ?_⟩
    have hlog : Real.log δ⁻¹ = L := log_inv_two_inv_pow k
    have hex : ∀ i < 9, ∃ l : List DyBox,
        JoinsCells (approxLQG γ W ω) δ (l53W u v i) (l53W u v (i + 1)) l ∧
        IsGoodSeq (epsStar αr δ) l ∧
        (∀ c ∈ l, c ∈ cellsMeeting (Metric.cthickening (8 * δ ^ dzzCMc γ)
          (tildeBox (l53W u v i) (l53W u v (i + 1))))) ∧
        ((l.length : ℕ∞) : ℝ≥0∞) ≤ ((approxLGDIn (tildeBox (l53W u v i) (l53W u v (i + 1))) γ W δ
          (l53W u v i) (l53W u v (i + 1)) ω : ℕ∞) : ℝ≥0∞) *
          ENNReal.ofReal (Real.exp (Real.log δ⁻¹ ^ (0.6 : ℝ))) := by
      intro i hi
      exact (hω i hi).1.2 (hω i hi).2.1
    choose! Lc hLc using hex
    have hreg' : ∀ K ⊆ l53Region u v, cellsMeeting (Metric.cthickening (8 * δ ^ dzzCMc γ) K) ⊆
        cellsMeeting (Metric.cthickening (8 * δ ^ dzzCMc γ) (l53Region u v)) := fun K hK =>
      cellsMeeting_mono (Metric.cthickening_subset_of_subset _ hK)
    have hcomp : ∀ i < 9, JoinsCells (approxLQG γ W ω) δ (l53W u v i) (l53W u v (i + 1)) (Lc i) ∧
        IsGoodSeq (epsStar αs δ) (Lc i) ∧
        ∀ c ∈ Lc i, c ∈ cellsMeeting (Metric.cthickening (8 * δ ^ dzzCMc γ) (l53Region u v)) := by
      intro i hi
      obtain ⟨a1, a2, a3, -⟩ := hLc i hi
      exact ⟨a1, isGoodSeq_mono (epsStar_pos' _ _) hεr a2,
        fun c hc => hreg' _ (tildeBox_w_subset_region u v hi) (a3 c hc)⟩
    obtain ⟨l, hj, hg, hS, hlen⟩ := l53_concat_chain (m := approxLQG γ W ω) (δ := δ)
      (ε := epsStar αs δ) (l53W u v) Lc _ 9 (by norm_num) hcomp
    rw [l53W_zero, l53W_nine] at hj
    refine ⟨l, hj, hg, hS, ?_⟩
    have hEi : ∀ i < 9, ((Lc i).length : ℝ) ≤
        Real.exp (EX k + L ^ (0.96 : ℝ) + L ^ (0.6 : ℝ)) := by
      intro i hi
      obtain ⟨hfin, hle⟩ := (hω i hi).2
      have h1 := length_le_of_eventRegularIn hfin (hLc i hi).2.2.2
      rw [hlog] at h1
      refine h1.trans ?_
      rw [Real.exp_add (EX k + _)]
      exact mul_le_mul_of_nonneg_right (natCast_le_exp_of_log_le hle) (Real.exp_pos _).le
    have hsum : (l.length : ℝ) ≤ 9 * Real.exp (EX k + L ^ (0.96 : ℝ) + L ^ (0.6 : ℝ)) := by
      have h1 : (l.length : ℝ) ≤ ∑ i ∈ Finset.range 9, ((Lc i).length : ℝ) := by
        exact_mod_cast hlen
      refine h1.trans ?_
      have := Finset.sum_le_sum (s := Finset.range 9) fun i hi => hEi i (Finset.mem_range.1 hi)
      simpa using this
    refine hsum.trans ?_
    rw [show (9 : ℝ) = Real.exp (Real.log 9) by rw [Real.exp_log (by norm_num)], ← Real.exp_add]
    exact Real.exp_le_exp.2 (by linarith)
  refine (measure_mono (compl_subset_compl.2 hsub)).trans ?_
  rw [compl_inter, compl_iInter₂]
  refine (measure_union_le _ _).trans ?_
  refine (add_le_add (measure_biUnion_finset_le _ _) (h₄ k hk4)).trans ?_
  have hterm : ∀ i ∈ Finset.range 9, P (G i)ᶜ ≤
      ENNReal.ofReal (2 * Real.exp (-L ^ (1 / 4 : ℝ))) := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    rw [hG, compl_inter]
    refine (measure_union_le _ _).trans ?_
    rw [two_mul, ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
    exact add_le_add (h₁ k hk1 i hi') (h₂ k hk2 i hi')
  refine (add_le_add (Finset.sum_le_sum hterm) le_rfl).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  push_cast
  linarith

end DZZ
end LQGMetric
