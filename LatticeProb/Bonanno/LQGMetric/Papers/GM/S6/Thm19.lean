/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S6.Thm19 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.AttainedFinal
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.Deterministic
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.DeterministicRatio
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.DefsLemmas
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.Bilip
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S2.SpatialIndep
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.Subseq
import LatticeProb.Bonanno.LQGMetric.Metric.WeylScaling

/-!
# GM §6: S6.2, S6.3 and the proof of Theorem 1.9 from Proposition 6.1 (task P2-M2O, WP-M2o)

GM = Gwynne–Miller, arXiv:1905.00383v3, `literature/src/1905.00383/uniqueness-final.tex`,
proof of Theorem 1.9, l. 3651–3676.

* `gm_S6_23` (GM.S6.2–S6.3, l. 3653–3655): if `c_* = C_*` then a.s. `D̃_h = C_* D_h` for a
  whole-plane GFF (definition (1.21) of `c_*`, `C_*`, with GM Prop 2.2 for finiteness), and then
  for a whole-plane GFF plus a continuous function by Weyl scaling (Axiom III).
* `gm_ratios_eq` (l. 3659–3675): `c_* = C_*`, by contradiction from Props 3.2, 3.3, 6.1 and the
  pigeonhole GM.S6.1 (`gm_S6_1`, with `μ = 3/8 > ν/2 = 1/4`).
* `gm_T1_9`: GM Theorem 1.9 (`Blueprint.GMWeakUniqueness`) from L3.1, P3.2, P3.3, P6.1, S6.2–3.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- **GM.S6.2–S6.3** (l. 3653–3655): `c_* = C_*` gives `D̃_h = C_* D_h` a.s. for a whole-plane GFF
(by (1.21)), hence for a whole-plane GFF plus a continuous function (Axiom III, Weyl scaling). -/
theorem gm_S6_23 (h22 : P2_2) : S6_23 := by
  intro γ D D' c Cs hp hr Ω _ P _ h hh
  obtain ⟨-, f, -, hg⟩ := hh
  set h₀ : Ω → DistC := fun ω => h ω - ofCont (f ω) with hh₀def
  obtain ⟨K, hK, hb⟩ := h22 hp
  have hh₀ : IsGFFPlusCont h₀ P := isGFFPlusCont_of_isWholePlaneGFF hg
  filter_upwards [hr P h₀ hg, hb P h₀ hg, hp.2.2.1.weyl P h₀ hh₀, hp.2.2.2.weyl P h₀ hh₀]
    with ω hr' hb' hw hw'
  have hB : BiLip (D (h₀ ω)) (D' (h₀ ω)) K := hb'
  obtain ⟨hl, -, -⟩ := ratio_bounds_of_bilip (D := D) (D' := D') hb'
  have hCs : 0 < Cs := by rw [hr'.1] at hl; exact lt_of_lt_of_le (inv_pos.2 hK) hl
  -- step 1: `D̃_{h₀} = C_* D_{h₀}` (GM (1.21))
  have h1 : ∀ u v : ℂ, (D' (h₀ ω)).1 (u, v) = Cs * (D (h₀ ω)).1 (u, v) := by
    intro u v
    by_cases huv : u = v
    · subst huv; rw [(D' (h₀ ω)).2.self_eq_zero, (D (h₀ ω)).2.self_eq_zero, mul_zero]
    have hpos := dist_pos_of_ne (D (h₀ ω)) huv
    let p : {p : ℂ × ℂ // p.1 ≠ p.2} := ⟨(u, v), huv⟩
    have a1 : (D' (h₀ ω)).1 p.1 / (D (h₀ ω)).1 p.1 ≤ Cs := by
      rw [← hr'.2]
      exact le_ciSup (f := fun p : {p : ℂ × ℂ // p.1 ≠ p.2} =>
        (D' (h₀ ω)).1 p.1 / (D (h₀ ω)).1 p.1) (bddAbove_ratio hB) p
    have a2 : Cs ≤ (D' (h₀ ω)).1 p.1 / (D (h₀ ω)).1 p.1 := by
      rw [← hr'.1]
      exact ciInf_le (f := fun p : {p : ℂ × ℂ // p.1 ≠ p.2} =>
        (D' (h₀ ω)).1 p.1 / (D (h₀ ω)).1 p.1) (bddBelow_ratio hB) p
    have := le_antisymm a1 a2
    exact (div_eq_iff hpos.ne').1 this
  have hsm : D' (h₀ ω) = (D (h₀ ω)).smul Cs hCs := by
    apply Subtype.ext; ext x
    simp only [ContMetric.smul, ContinuousMap.smul_apply, smul_eq_mul]
    exact h1 x.1 x.2
  have hadd : addFun (h₀ ω) (f ω) = h ω := by simp only [hh₀def, addFun, sub_add_cancel]
  -- step 2: Weyl scaling
  intro u v
  have e1 := hw' (f ω) u v
  have e2 := hw (f ω) u v
  rw [hadd] at e1 e2
  rw [hsm, weylScale_smul, e2, ← ENNReal.ofReal_mul hCs.le] at e1
  exact ((ENNReal.ofReal_eq_ofReal_iff (ContMetric.nonneg _ _ _)
    (mul_nonneg hCs.le (ContMetric.nonneg _ _ _))).1 e1.symm)

/-- **GM, proof of Theorem 1.9** (l. 3659–3675): `c_* = C_*`. Otherwise Prop 6.1 gives `c''`,
Prop 3.3 (with `c''`) many scales with `P[G̲_r(c'', β̲)] ≥ p̲`, Prop 6.1 (with `β = β̲ ∧ p̲`,
`η = p̄/2`) a `δ` with `P[Ḡ_r(C_* − δ, β̄)] ≤ p̄/2` at those scales, and Prop 3.2 (with
`C' = C_* − δ`) many scales with `P[Ḡ_r(C_* − δ, β̄)] ≥ p̄`; GM.S6.1 (`μ = 3/8 > ν/2`) makes the
two sets of scales intersect. -/
theorem gm_ratios_eq (h32 : P3_2) (h33 : P3_3) (h61 : P6_1) {γ : ℝ} {D D' : DistC → ContMetric}
    {c : ℝ → ℝ} {cs Cs : ℝ} (hp : PairSetting γ D D' c) (hr : RatiosAre D D' cs Cs)
    (hcs : 0 < cs) (hle : cs ≤ Cs) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsWholePlaneGFF h P) : cs = Cs := by
  by_contra hne
  have hlt : cs < Cs := lt_of_le_of_ne hle hne
  have hμ : (0 : ℝ) < 3 / 8 := by norm_num
  have hμν : (3 / 8 : ℝ) < 1 / 2 := by norm_num
  have hν : (1 / 2 : ℝ) < 1 := by norm_num
  obtain ⟨βb, pb, hβb, hpb, H32⟩ := h32 hp hr hμ hμν hν
  obtain ⟨βl, pl, hβl, hpl, H33⟩ := h33 hp hr hμ hμν hν
  obtain ⟨c'', hc'', H61⟩ := h61 hp hr hlt
  obtain ⟨ε₁, hε₁, H33'⟩ := H33 c'' hc''
  have hβ : min βl pl ∈ Ioo (0 : ℝ) 1 := ⟨lt_min hβl.1 hpl.1, min_lt_of_left_lt hβl.2⟩
  obtain ⟨δ₀, hδ₀, H61'⟩ := H61 _ hβ βb hβb (pb / 2) (half_pos hpb.1)
  have hCs : 0 < Cs := hcs.trans hlt
  set δ := min (δ₀ / 2) (Cs / 2) with hδ
  have hδpos : 0 < δ := lt_min (half_pos hδ₀) (half_pos hCs)
  have hδ1 : δ < δ₀ := (min_le_left _ _).trans_lt (half_lt_self hδ₀)
  have hδ2 : δ < Cs := (min_le_right _ _).trans_lt (half_lt_self hCs)
  obtain ⟨ε₀, hε₀, H32'⟩ := H32 (Cs - δ) ⟨by linarith, by linarith⟩
  obtain ⟨ε₂, hε₂, Hpig⟩ := gm_S6_1 (μ := 3 / 8) (ν := 1 / 2) (by norm_num) (by norm_num)
  set ε := min (min ε₀ ε₁) ε₂ / 2 with hε
  have hm : 0 < min (min ε₀ ε₁) ε₂ := lt_min (lt_min hε₀ hε₁) hε₂
  have hεpos : 0 < ε := half_pos hm
  have hεm : ε < min (min ε₀ ε₁) ε₂ := half_lt_self hm
  have hεa : ε < ε₀ := hεm.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hεb : ε < ε₁ := hεm.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hεc : ε < ε₂ := hεm.trans_le (min_le_right _ _)
  have A := H32' P h hh ε ⟨hεpos, hεa⟩
  have B := H33' P h hh ε ⟨hεpos, hεb⟩
  obtain ⟨k, -, -, hk1, hk2⟩ := Hpig ε ⟨hεpos, hεc⟩ _ _ A B
  have hR : (0 : ℝ) < (8 : ℝ)⁻¹ ^ k := by positivity
  have hG : ENNReal.ofReal (min βl pl) ≤ P (h ⁻¹' GLow D D' ((8 : ℝ)⁻¹ ^ k) c'' (min βl pl)) :=
    calc ENNReal.ofReal (min βl pl) ≤ ENNReal.ofReal pl :=
          ENNReal.ofReal_le_ofReal (min_le_right _ _)
      _ ≤ P (h ⁻¹' GLow D D' ((8 : ℝ)⁻¹ ^ k) c'' βl) := hk2
      _ ≤ _ := measure_mono (preimage_mono (GLow_anti_beta D D' hR.le c'' (min_le_left _ _)))
  have C := H61' _ hR P h hh hG δ ⟨hδpos, hδ1⟩
  have := hk1.trans C
  rw [ENNReal.ofReal_le_ofReal_iff (half_pos hpb.1).le] at this
  linarith [hpb.1]

/-- **GM Theorem 1.9** (l. 3651–3676) from GM Lemma 3.1, Props 3.2, 3.3, 6.1 and GM.S6.2–S6.3. -/
theorem gm_T1_9 (h31 : L3_1) (h32 : P3_2) (h33 : P3_3) (h61 : P6_1) (h623 : S6_23) :
    GMWeakUniqueness := by
  intro γ hγ hγ2 D D' c hD hD'
  have hp : PairSetting γ D' D c := ⟨hγ, hγ2, hD', hD⟩
  obtain ⟨cs, Cs, hcs, hle, hr⟩ := h31 hp
  refine ⟨Cs, hcs.trans_le hle, ?_⟩
  intro Ω _ P _ h hh
  obtain ⟨f, -, hg⟩ := hh.2
  have heq : cs = Cs := gm_ratios_eq h32 h33 h61 hp hr hcs hle P _ hg
  subst heq
  exact h623 hp hr P h hh

end LQGMetric.GM
