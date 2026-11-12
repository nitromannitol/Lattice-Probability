/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3P32W15 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3P32W14

/-!
# D97, packet P-3: (eq-cell-LQG-compare) from the per-box estimate (Eq.LD-lowerbound-approx-LGD)

DZZ (arXiv:1807.00422, `LBM_LGDarXiv.tex` l. 1183–1189): "We will show that for a fixed box `B`
and a fixed square `S ∈ 𝒮_B`, (Eq.LD-lowerbound-approx-LGD)
`P(Ẽ_{δ,α}, Ẽ_{δ',α}, M_{γ,s}(B) > δ'², M_γ(S) ≤ δ²) ≤ e^{−(2 C_Mc log δ⁻¹)²}`. Assuming this, one
can check (eq-cell-LQG-compare), noting that the event there is not empty only for
`s ≥ (δ')^{C_Mc}`."

* `L32CellCompareBox P γ W ν`: (Eq.LD-lowerbound-approx-LGD) for a high-probability event `G`
  (DZZ: `G = Ẽ_{δ,α} ∩ Ẽ_{δ',α}`), boxes of side `≥ δ'^{C_mc}` and squares `S ⊆ 𝕍`;
* **`highProb_cellCompare'`**: union bound over the `≤ 4 δ^{−2C_mc}` boxes of side `≥ δ'^{C_mc}` and
  the `4096²` squares of each `𝒮_B`;
* **`l32BallCover_of_cellCompareBox`**: `L32BallCover` at `dzzWall dzzV ν` from
  (Eq.LD-lowerbound-approx-LGD).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

variable {Ω : Type*} [MeasurableSpace Ω]

/-- DZZ (Eq.LD-lowerbound-approx-LGD) (l. 1183–1185), with `M_{γ,s}(B) ≥ δ'²`, for boxes of side
`≥ δ'^{C_mc}` and squares of `𝒮_B` inside `𝕍`; `G` plays the role of `Ẽ_{δ,α} ∩ Ẽ_{δ',α}`. -/
def L32CellCompareBox (P : Measure Ω) (γ : ℝ) (W : WNSpace → Ω → ℝ) (ν : Ω → Measure ℂ) :
    Prop :=
  ∃ G : ℝ → Set Ω, HighProb P G ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
    ∀ (B : DyBox) (a b : ℕ), a < 4096 → b < 4096 → p32Up δ ^ dzzCmc γ ≤ B.side →
      sqSB B a b ⊆ dzzV →
        P (G δ ∩ {ω | p32Up δ ^ 2 ≤ approxLQG γ W ω B ∧
          ν ω (sqSB B a b) ≤ ENNReal.ofReal (δ ^ 2)}) ≤
          ENNReal.ofReal (Real.exp (-(2 * dzzCMc γ * Real.log δ⁻¹) ^ 2))

/-- the dyadic boxes of level `≤ N` -/
def boxesLE (N : ℕ) : Finset DyBox :=
  (Finset.range (N + 1)).biUnion fun n => (finite_level n).toFinset

lemma card_level_le (n : ℕ) : (finite_level n).toFinset.card ≤ 4 ^ n := by
  have h : ((Finset.range (2 ^ n)) ×ˢ (Finset.range (2 ^ n))).card = 4 ^ n := by
    rw [Finset.card_product, Finset.card_range, ← mul_pow]; norm_num
  rw [← h]
  refine Finset.card_le_card_of_injOn (fun B : DyBox => (B.j, B.k)) ?_ ?_
  · intro B hB
    rw [Set.Finite.coe_toFinset] at hB
    have hn : B.n = n := hB
    simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio]
    exact ⟨hn ▸ B.hj, hn ▸ B.hk⟩
  · intro B hB B' hB' h
    rw [Set.Finite.coe_toFinset] at hB hB'
    simp only [Prod.mk.injEq] at h
    exact DyBox.ext ((show B.n = n from hB).trans (show B'.n = n from hB').symm) h.1 h.2

lemma sum_four_pow_le (k : ℕ) : ∑ n ∈ Finset.range k, (4 : ℕ) ^ n ≤ 4 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, pow_succ]; omega

lemma card_boxesLE (N : ℕ) : (boxesLE N).card ≤ 4 ^ (N + 1) :=
  Finset.card_biUnion_le.trans ((Finset.sum_le_sum fun n _ => card_level_le n).trans
    (sum_four_pow_le _))

lemma mem_boxesLE {B : DyBox} {N : ℕ} (h : B.n ≤ N) : B ∈ boxesLE N :=
  Finset.mem_biUnion.2 ⟨B.n, Finset.mem_range.2 (by omega),
    (Set.Finite.mem_toFinset _).2 rfl⟩

/-- Boxes of side `≥ x` have level `≤ log₂ ⌊1/x⌋`. -/
lemma level_le_of_side {B : DyBox} {x : ℝ} (hx : 0 < x) (h : x ≤ B.side) :
    B.n ≤ Nat.log 2 ⌊1 / x⌋₊ := by
  have h1 : (2 : ℝ) ^ B.n ≤ 1 / x := by
    rw [le_div_iff₀ hx]
    have : B.side * 2 ^ B.n = 1 := by
      unfold DyBox.side; rw [← mul_pow, inv_mul_cancel₀ (by norm_num), one_pow]
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) B.n]
  have h2 : 2 ^ B.n ≤ ⌊1 / x⌋₊ := Nat.le_floor (by exact_mod_cast h1)
  exact Nat.le_log_of_pow_le (by norm_num) h2

/-- Arithmetic of the union bound (own elementary bookkeeping). -/
lemma unionBound_asym {C D K : ℝ} (hC : 0 < C) (hD : 0 ≤ D) (hK : 0 ≤ K) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      Real.exp (K + D * Real.log δ⁻¹ - 4 * C ^ 2 * Real.log δ⁻¹ ^ 2) ≤ δ := by
  set L₀ : ℝ := 1 + (K + D + 1) / (4 * C ^ 2)
  refine ⟨Real.exp (-L₀), Real.exp_pos _, fun δ ⟨hδ0, hδ⟩ => ?_⟩
  set L := Real.log δ⁻¹
  have hL : L₀ < L := by
    have := Real.log_lt_log hδ0 hδ
    rw [Real.log_exp] at this
    simp only [L, Real.log_inv]; linarith
  have hq : 0 ≤ (K + D + 1) / (4 * C ^ 2) := by positivity
  have hL1 : 1 ≤ L := by simp only [L₀] at hL; linarith
  have hkey : K + D + 1 ≤ 4 * C ^ 2 * (L - 1) := by
    have : (K + D + 1) / (4 * C ^ 2) < L - 1 := by simp only [L₀] at hL; linarith
    rw [div_lt_iff₀ (by positivity)] at this; linarith
  rw [← Real.exp_log hδ0]
  refine Real.exp_le_exp.2 ?_
  have hlog : Real.log δ = -L := by simp only [L, Real.log_inv]; ring
  rw [hlog]
  have h1 : (K + D + 1) * L ≤ 4 * C ^ 2 * (L - 1) * L := mul_le_mul_of_nonneg_right hkey (by linarith)
  have h2 : K ≤ K * L := le_mul_of_one_le_right hK hL1
  have h3 : 0 ≤ 4 * C ^ 2 * L := by positivity
  nlinarith

/-- **(eq-cell-LQG-compare) w.h.p. from (Eq.LD-lowerbound-approx-LGD)** (DZZ l. 1185–1186):
union bound over the boxes of side `≥ δ'^{C_mc}` and the squares of their `𝒮_B`. -/
theorem highProb_cellCompare' {P : Measure Ω} {W : WNSpace → Ω → ℝ} (hW : IsWhiteNoise P W)
    {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ν : Ω → Measure ℂ}
    (hbox : L32CellCompareBox P γ W ν) : HighProb P (cellCompareEvent' γ W ν) := by
  classical
  have := hW.isProbabilityMeasure
  obtain ⟨G, ⟨cG, hcG, δG, hδG, hGp⟩, δ₁, hδ₁, hb⟩ := hbox
  set C := dzzCMc γ with hCdef
  set Cm := dzzCmc γ with hCmdef
  have hC : 0 < C := dzzCMc_pos γ
  have hCm : 0 < Cm := hC.trans_le (dzzCMc_le_dzzCmc hγ hγ2)
  set K0 : ℝ := Real.log (4 * 4096 * 4096) with hK0
  have hK0p : 0 ≤ K0 := Real.log_nonneg (by norm_num)
  obtain ⟨δu, hδu, hu⟩ := unionBound_asym (C := C) (D := 2 * Cm) hC (by positivity) hK0p
  obtain ⟨δa, hδa, hasym⟩ := p32_asym (a := 1) (b := 0) one_pos
  set c := min cG 1 with hcdef
  have hc : 0 < c := lt_min hcG one_pos
  refine ⟨c / 2, by positivity, min (min δG δ₁) (min (min δu δa) (min (1 / 4) ((1 / 2) ^ (2 / c)))),
    lt_min (lt_min hδG hδ₁) (lt_min (lt_min hδu hδa) (lt_min (by norm_num)
      (Real.rpow_pos_of_pos (by norm_num) _))), fun δ hδ => ?_⟩
  obtain ⟨hδ0, hδ⟩ := hδ
  have hδG' : δ < δG := hδ.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hδ1' : δ < δ₁ := hδ.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hδu' : δ < δu := hδ.trans_le ((min_le_right _ _).trans ((min_le_left _ _).trans
    (min_le_left _ _)))
  have hδa' : δ < δa := hδ.trans_le ((min_le_right _ _).trans ((min_le_left _ _).trans
    (min_le_right _ _)))
  have hδq : δ < 1 / 4 := hδ.trans_le ((min_le_right _ _).trans ((min_le_right _ _).trans
    (min_le_left _ _)))
  have hδc : δ < (1 / 2) ^ (2 / c) := hδ.trans_le ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _)))
  have hδ1 : δ < 1 := by linarith
  -- `δ ≤ δ' ≤ 1`
  have hp0 := p32Up_pos hδ0
  have hpδ : δ ≤ p32Up δ := by
    have hL : 0 ≤ Real.log δ⁻¹ := by
      rw [Real.log_inv]; have := Real.log_neg hδ0 hδ1; linarith
    unfold p32Up
    exact le_mul_of_one_le_right hδ0.le (Real.one_le_exp (Real.rpow_nonneg hL _))
  have hp1 : p32Up δ ≤ 1 := by
    have hs := p32Up_le_sqrt hδ0 (hasym δ ⟨hδ0, hδa'⟩).1
    exact hs.trans (Real.rpow_le_one hδ0.le hδ1.le (by norm_num))
  set x := p32Up δ ^ Cm with hxdef
  have hx0 : 0 < x := Real.rpow_pos_of_pos hp0 _
  have hx1 : x ≤ 1 := Real.rpow_le_one hp0.le hp1 hCm.le
  have hxδ : δ ^ Cm ≤ x := Real.rpow_le_rpow hδ0.le hpδ hCm.le
  set N := Nat.log 2 ⌊1 / x⌋₊ with hN
  set F := boxesLE N with hF
  set e : ℝ := Real.exp (-(2 * C * Real.log δ⁻¹) ^ 2) with he
  set bad : DyBox → Fin 4096 → Fin 4096 → Set Ω := fun B a b =>
    if x ≤ B.side ∧ sqSB B a b ⊆ dzzV then G δ ∩ {ω | p32Up δ ^ 2 ≤ approxLQG γ W ω B ∧
      ν ω (sqSB B a b) ≤ ENNReal.ofReal (δ ^ 2)} else ∅ with hbad
  have hsub : (cellCompareEvent' γ W ν δ)ᶜ ⊆
      (G δ)ᶜ ∪ ⋃ B ∈ F, ⋃ a : Fin 4096, ⋃ b : Fin 4096, bad B a b := by
    intro ω hω
    by_cases hg : ω ∈ G δ
    · right
      simp only [cellCompareEvent', mem_compl_iff, mem_ofPred_eq, not_forall, not_lt] at hω
      obtain ⟨B, a, b, ha, hb', hs, hm, hS, hν⟩ := hω
      refine mem_iUnion₂.2 ⟨B, mem_boxesLE (level_le_of_side hx0 hs),
        mem_iUnion.2 ⟨⟨a, ha⟩, mem_iUnion.2 ⟨⟨b, hb'⟩, ?_⟩⟩⟩
      simp only [hbad]
      rw [ite_eq_left_iff.2 (fun h => absurd ⟨hs, hS⟩ h)]
      exact ⟨hg, hm, hν⟩
    · exact Or.inl hg
  have hbad_le : ∀ B a b, P (bad B a b) ≤ ENNReal.ofReal e := by
    intro B a b
    simp only [hbad]
    split_ifs with h
    · exact hb δ ⟨hδ0, hδ1'⟩ B a b a.2 b.2 h.1 h.2
    · simp
  have hU : P (⋃ B ∈ F, ⋃ a : Fin 4096, ⋃ b : Fin 4096, bad B a b) ≤
      ENNReal.ofReal (F.card * (4096 * (4096 * e))) := by
    refine (measure_biUnion_finset_le _ _).trans ?_
    refine (Finset.sum_le_sum fun B _ => (measure_iUnion_fintype_le _ _).trans
      (Finset.sum_le_sum fun a _ => (measure_iUnion_fintype_le _ _).trans
        (Finset.sum_le_sum fun b _ => hbad_le B a b))).trans (le_of_eq ?_)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num),
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat]
  -- the count
  have hfl : ⌊1 / x⌋₊ ≠ 0 := by
    refine Nat.pos_iff_ne_zero.1 (Nat.floor_pos.2 ?_)
    rw [le_div_iff₀ hx0]; linarith
  have h2N : ((2 ^ N : ℕ) : ℝ) ≤ 1 / x :=
    (Nat.cast_le.2 (Nat.pow_log_le_self 2 hfl)).trans (Nat.floor_le (by positivity))
  have hcard : (F.card : ℝ) ≤ 4 * (1 / x) ^ 2 := by
    have h1 : (F.card : ℝ) ≤ ((4 ^ (N + 1) : ℕ) : ℝ) := Nat.cast_le.2 (card_boxesLE N)
    have h2 : ((4 ^ (N + 1) : ℕ) : ℝ) = 4 * ((2 ^ N : ℕ) : ℝ) ^ 2 := by
      push_cast; rw [pow_succ, show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul]; ring_nf
    rw [h2] at h1
    refine h1.trans (by gcongr)
  have hxinv : 1 / x ≤ Real.exp (Cm * Real.log δ⁻¹) := by
    rw [div_le_iff₀ hx0]
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hxδ (Real.exp_pos _).le)
    rw [Real.rpow_def_of_pos hδ0, ← Real.exp_add, Real.log_inv]
    ring_nf; rw [Real.exp_zero]
  have hreal : (F.card : ℝ) * (4096 * (4096 * e)) ≤ δ := by
    refine le_trans ?_ (hu δ ⟨hδ0, hδu'⟩)
    have he0 : 0 ≤ e := (Real.exp_pos _).le
    calc (F.card : ℝ) * (4096 * (4096 * e)) ≤ 4 * (1 / x) ^ 2 * (4096 * (4096 * e)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ ≤ 4 * Real.exp (Cm * Real.log δ⁻¹) ^ 2 * (4096 * (4096 * e)) := by
          gcongr
      _ = Real.exp (K0 + 2 * Cm * Real.log δ⁻¹ - 4 * C ^ 2 * Real.log δ⁻¹ ^ 2) := by
          have e1 : Real.exp (Cm * Real.log δ⁻¹) ^ 2 = Real.exp (2 * Cm * Real.log δ⁻¹) := by
            rw [← Real.exp_nat_mul]; ring_nf
          rw [e1, he, show K0 + 2 * Cm * Real.log δ⁻¹ - 4 * C ^ 2 * Real.log δ⁻¹ ^ 2 =
              K0 + 2 * Cm * Real.log δ⁻¹ + -(2 * C * Real.log δ⁻¹) ^ 2 by ring,
            Real.exp_add, Real.exp_add, hK0, Real.exp_log (by norm_num)]
          ring
  calc P (cellCompareEvent' γ W ν δ)ᶜ
      ≤ P ((G δ)ᶜ ∪ ⋃ B ∈ F, ⋃ a : Fin 4096, ⋃ b : Fin 4096, bad B a b) := measure_mono hsub
    _ ≤ ENNReal.ofReal (δ ^ cG) + ENNReal.ofReal δ :=
        (measure_union_le _ _).trans (add_le_add (hGp δ ⟨hδ0, hδG'⟩)
          (hU.trans (ENNReal.ofReal_le_ofReal hreal)))
    _ = ENNReal.ofReal (δ ^ cG + δ) := (ENNReal.ofReal_add (by positivity) hδ0.le).symm
    _ ≤ ENNReal.ofReal (δ ^ (c / 2)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hm1 : δ ^ cG ≤ δ ^ c := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le (min_le_left _ _)
        have hm2 : δ ≤ δ ^ c := by
          have := Real.rpow_le_rpow_of_exponent_ge hδ0 hδ1.le (min_le_right cG 1)
          rwa [Real.rpow_one] at this
        have hhalf : δ ^ (c / 2) ≤ 1 / 2 := by
          have := Real.rpow_le_rpow hδ0.le hδc.le (by positivity : 0 ≤ c / 2)
          rwa [← Real.rpow_mul (by positivity), show 2 / c * (c / 2) = 1 by field_simp,
            Real.rpow_one] at this
        have hsplit : δ ^ c = δ ^ (c / 2) * δ ^ (c / 2) := by
          rw [← Real.rpow_add hδ0]; ring_nf
        have h0 : 0 ≤ δ ^ (c / 2) := by positivity
        nlinarith

/-- **P-3 from (Eq.LD-lowerbound-approx-LGD)**: DZZ l. 1160–1189 for the internal measure. -/
theorem l32BallCover_of_cellCompareBox {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {ν : Ω → Measure ℂ}
    (hbox : L32CellCompareBox P γ W ν) : L32BallCover P γ W (fun ω => dzzWall dzzV (ν ω)) :=
  l32BallCover_of_cellCompare' hW hγ hγ2 (highProb_cellCompare' hW hγ hγ2 hbox)

/-- **P-3 at `μIn = dzzMuIn γ W`** from (Eq.LD-lowerbound-approx-LGD) for `M^W`. -/
theorem l32BallCover_dzzMuIn_of_box {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hbox : L32CellCompareBox P γ W (wickQArea γ W)) : L32BallCover P γ W (dzzMuIn γ W) :=
  l32BallCover_of_cellCompareBox hW hγ hγ2 hbox

end DZZ
end LQGMetric
