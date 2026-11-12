/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S3L4FineHP at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S3L4Fine

/-!
# DZZ Lemma 3.4 at finer centres: high probability (P2-DZZ3B, WP-113)

`nbrFineEvent` (the η-part of `𝓔_{δ,α}` with `y` any dyadic centre of level `≥ m + j`, see
`S3L4Fine`) holds with high probability for every `α > 0`: `nbrFineGen_compl_le`, Lemma 2.6
(`dzz_lemma26_eta`) and the asymptotics `l34_eventually`. `eventEFine` is
`cellSizeEvent ∩ nbrFineEvent`, and `dzz_lemma34_fine` is DZZ Lemma 3.4 for it.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise SupTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}

/-- The η-part of `𝓔_{δ,α}` at all dyadic centres of level `≥ m + j`. -/
def nbrFineEvent (W : WNSpace → Ω → ℝ) (Cmc α δ : ℝ) : Set Ω :=
  nbrFineGen W (δ ^ (-Cmc)) ((α * Real.log δ⁻¹) ^ 2)
    (α * Real.sqrt (Real.log δ⁻¹) * Real.log (Real.log δ⁻¹))

/-- `𝓔_{δ,α}` with the η-part at all finer dyadic centres (what DZZ Lemma 3.7 uses). -/
def eventEFine (γ : ℝ) (W : WNSpace → Ω → ℝ) (α δ : ℝ) : Set Ω :=
  cellSizeEvent γ W δ ∩ nbrFineEvent W (dzzCmc γ) α δ

set_option maxHeartbeats 600000 in
theorem nbrFineEvent_highProb (hW : IsWhiteNoise P W) {Cmc α : ℝ} (hCmc : 0 ≤ Cmc)
    (hα : 0 < α) : HighProb P (fun δ => nbrFineEvent W Cmc α δ) := by
  have := hW.isProbabilityMeasure
  obtain ⟨C, hC0, hC⟩ := dzz_lemma26_eta
  choose Ys hYc _ hYae using fun n : ℕ =>
    exists_continuous_etaInf hW (δ := (2 : ℝ)⁻¹ ^ n) (by positivity)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.1 ((l34_eventually (K := 18 * (5 * Cmc + 2))
    (D := 1076 * 9 + 1) hα (by linarith) (by norm_num)).and
    ((l34_eventually (K := 9 * Real.log 2 ^ 2 * C * (5 * Cmc + 3)) (D := 1) hα (by positivity)
      (by norm_num)).and (eventually_ge_atTop (Real.log C))))
  refine ⟨1 / 2, by norm_num, Real.exp (-max L₀ 8), Real.exp_pos _, fun δ hδ => ?_⟩
  obtain ⟨hδ0, hδ1⟩ := hδ
  set L := Real.log δ⁻¹ with hLdef
  have hLgt : max L₀ 8 < L := by
    rw [hLdef, Real.log_inv, lt_neg]
    exact (Real.log_lt_iff_lt_exp hδ0).2 hδ1
  obtain ⟨⟨hL1, hY, hpoly, hlog⟩, ⟨-, -, -, hlog'⟩, hLC⟩ := hL₀ L (le_max_left _ _ |>.trans hLgt.le)
  have hL2 : 8 ≤ L := (le_max_right _ _).trans hLgt.le
  have hδL : δ = Real.exp (-L) := by
    rw [hLdef, Real.log_inv, neg_neg, Real.exp_log hδ0]
  have hδ1' : δ < 1 := by rw [hδL, ← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
  have hX : δ ^ (-Cmc) = Real.exp (Cmc * L) := by
    rw [Real.rpow_def_of_pos hδ0, hLdef, Real.log_inv]; ring_nf
  have hX1 : 1 ≤ δ ^ (-Cmc) := by rw [hX]; exact Real.one_le_exp (by positivity)
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  set T := α * Real.sqrt L * Real.log L with hTdef
  have hT : 0 ≤ T := by positivity
  set Y := (α * L) ^ 2 with hYdef
  have hlogY : 0 ≤ Real.log Y := Real.log_nonneg hY
  have hfine := nbrFineGen_compl_le (P := P) hW hX1 hY hT Ys hYae hC0.le
    (fun n u hu => by
      have h := hC hW ((2 : ℝ)⁻¹ ^ n) (by positivity) (Ys n) (hYc n) (hYae n) u hu 1 le_rfl
        (T / (3 * Real.log 2)) (by positivity)
      simpa using h)
  have h9 := nbrEventGen_compl_le (P := P) hW (K := 9) (by norm_num) hX1 hY
    (by positivity : 0 ≤ 2 * T / 3)
  rw [hX] at hfine h9
  set E := Real.exp (Cmc * L)
  have hE1 : 1 ≤ E := Real.one_le_exp (by positivity)
  have hT2 : T ^ 2 = α ^ 2 * Real.log L ^ 2 * L := by
    rw [hTdef, mul_pow, mul_pow, Real.sq_sqrt (by linarith)]; ring
  have hE5 : ∀ k : ℝ, E ^ 5 * Real.exp (-((5 * Cmc + k) * L)) = Real.exp (-(k * L)) := by
    intro k; rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; push_cast; ring
  have hY0 : 0 ≤ Y := by positivity
  -- first term
  set V := 1076 * 9 + 1 + Real.log Y
  have hV : 0 < V := by simp only [V]; linarith
  have hG1 : Real.exp (-(2 * T / 3 / 2) ^ 2 / (2 * V)) ≤ Real.exp (-((5 * Cmc + 2) * L)) := by
    refine Real.exp_le_exp.2 ?_
    have e : (2 * T / 3 / 2) ^ 2 = T ^ 2 / 9 := by ring
    rw [e, hT2, neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_right hlog (by linarith : (0 : ℝ) ≤ L)
    nlinarith
  have hterm1 : (E + 1) * (Y + 1) * (2 * (E ^ 4 * Y ^ 2) *
      (2 * Real.exp (-(2 * T / 3 / 2) ^ 2 / (2 * V)))) ≤ δ := by
    calc (E + 1) * (Y + 1) * (2 * (E ^ 4 * Y ^ 2) *
          (2 * Real.exp (-(2 * T / 3 / 2) ^ 2 / (2 * V))))
        ≤ (E + E) * (Y + 1) * (2 * (E ^ 4 * Y ^ 2) * (2 * Real.exp (-((5 * Cmc + 2) * L)))) := by
          gcongr
      _ = (8 * (Y + 1) * Y ^ 2) * (E ^ 5 * Real.exp (-((5 * Cmc + 2) * L))) := by ring
      _ ≤ Real.exp L * (E ^ 5 * Real.exp (-((5 * Cmc + 2) * L))) := by gcongr
      _ = δ := by rw [hE5, ← Real.exp_add, hδL]; congr 1; ring
  -- second term
  have hG2 : C * Real.exp (-(T / (3 * Real.log 2)) ^ 2 / C) ≤
      C * Real.exp (-((5 * Cmc + 3) * L)) := by
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC0.le
    have e : (T / (3 * Real.log 2)) ^ 2 = T ^ 2 / (9 * Real.log 2 ^ 2) := by
      rw [div_pow]; ring
    rw [e, hT2, neg_div, neg_le_neg_iff, div_div, le_div_iff₀ (by positivity)]
    have h1 : 9 * Real.log 2 ^ 2 * C * (5 * Cmc + 3) ≤ α ^ 2 * Real.log L ^ 2 := by
      have : 0 ≤ 9 * Real.log 2 ^ 2 * C * (5 * Cmc + 3) := by positivity
      calc 9 * Real.log 2 ^ 2 * C * (5 * Cmc + 3) = 9 * Real.log 2 ^ 2 * C * (5 * Cmc + 3) * 1 :=
            (mul_one _).symm
        _ ≤ 9 * Real.log 2 ^ 2 * C * (5 * Cmc + 3) * (1 + Real.log Y) :=
            mul_le_mul_of_nonneg_left (by linarith) this
        _ ≤ α ^ 2 * Real.log L ^ 2 := hlog'
    have := mul_le_mul_of_nonneg_right h1 (by linarith : (0 : ℝ) ≤ L)
    calc _ = 9 * Real.log 2 ^ 2 * C * (5 * Cmc + 3) * L := by ring
      _ ≤ _ := this
  have hCe : C ≤ Real.exp L := by
    rw [← Real.exp_log hC0]; exact Real.exp_le_exp.2 hLC
  have hterm2 : (E * Y + 1) * ((E * Y) ^ 2 * (C * Real.exp (-(T / (3 * Real.log 2)) ^ 2 / C)))
      ≤ 2 * δ := by
    have hEY : 1 ≤ E * Y := by nlinarith
    calc (E * Y + 1) * ((E * Y) ^ 2 * (C * Real.exp (-(T / (3 * Real.log 2)) ^ 2 / C)))
        ≤ (E * Y + E * Y) * ((E * Y) ^ 2 * (C * Real.exp (-((5 * Cmc + 3) * L)))) := by
          gcongr
      _ = 2 * (E ^ 3 * Y ^ 3) * C * Real.exp (-((5 * Cmc + 3) * L)) := by ring
      _ ≤ 2 * (E ^ 5 * (8 * (Y + 1) * Y ^ 2)) * C * Real.exp (-((5 * Cmc + 3) * L)) := by
          have h1 : E ^ 3 ≤ E ^ 5 := pow_le_pow_right₀ hE1 (by norm_num)
          have h2 : Y ^ 3 ≤ 8 * (Y + 1) * Y ^ 2 := by
            have h3 : Y ≤ 8 * (Y + 1) := by linarith
            calc Y ^ 3 = Y * Y ^ 2 := by ring
              _ ≤ 8 * (Y + 1) * Y ^ 2 := mul_le_mul_of_nonneg_right h3 (sq_nonneg Y)
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (by positivity) (by positivity))
              (by norm_num)) hC0.le) (Real.exp_pos _).le
      _ ≤ 2 * (E ^ 5 * (8 * (Y + 1) * Y ^ 2)) * Real.exp L *
            Real.exp (-((5 * Cmc + 3) * L)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hCe (by positivity))
            (Real.exp_pos _).le
      _ = 2 * (8 * (Y + 1) * Y ^ 2) * Real.exp L * (E ^ 5 * Real.exp (-((5 * Cmc + 3) * L))) := by
          ring
      _ ≤ 2 * Real.exp L * Real.exp L * Real.exp (-(3 * L)) := by
          rw [hE5]; gcongr
      _ = 2 * δ := by
          rw [hδL, mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]; congr 2; ring
  have hδ9 : δ ≤ 1 / 9 := by
    have h := Real.add_one_le_exp L
    rw [hδL, Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
    norm_num; linarith
  have htot : P.real (nbrFineEvent W Cmc α δ)ᶜ ≤ 3 * δ := by
    unfold nbrFineEvent
    rw [hX]
    refine hfine.trans ?_
    linarith [h9.trans hterm1]
  rw [← ofReal_measureReal (measure_ne_top _ _)]
  refine ENNReal.ofReal_le_ofReal (htot.trans ?_)
  rw [← Real.sqrt_eq_rpow]
  have hs0 := Real.sqrt_nonneg δ
  have hs3 : Real.sqrt δ ≤ 1 / 3 := by
    have h := Real.sqrt_le_sqrt hδ9
    rwa [show (1 : ℝ) / 9 = (1 / 3) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at h
  calc 3 * δ = 3 * (Real.sqrt δ * Real.sqrt δ) := by rw [Real.mul_self_sqrt hδ0.le]
    _ ≤ 3 * (1 / 3 * Real.sqrt δ) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs3 hs0) (by norm_num)
    _ = Real.sqrt δ := by ring

/-- **DZZ Lemma 3.4** with the η-part at all finer dyadic centres, for every `α > 0`. -/
theorem dzz_lemma34_fine (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {α : ℝ}
    (hα : 0 < α) : HighProb P (fun δ => eventEFine γ W α δ) :=
  have := hW.isProbabilityMeasure
  (dzz_lemma31 hW hγ hγ2).inter (nbrFineEvent_highProb hW (dzzCmc_nonneg hγ hγ2) hα)

end DZZ
end LQGMetric
