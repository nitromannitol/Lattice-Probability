/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DDDF.S6Thm12Sq2C at commit fdb5cad; only the module paths of local imports are changed.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DDDF.S6Thm12Sq2B
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P29SqA
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8FinAsm
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffFarA
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GenTrans
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GenRatio
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_8GffRed
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L2_13

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemmas 2.13, 2.14 with DDDF Theorem 1 (2) on the square (task P2-DDDF6f)

Copy of `Papers/DFGPS/P29SqC.lean` with `Blueprint.DDDFThm1_2` replaced by `DDDF.DDDFThm1_2Sq` (DDDF Theorem 1 (2)
for `D = (−1,2)²` only; DFGPS T:877–881 applies Theorem 1 (2) only to that domain, and `zb_step'`
reads only its tightness there). Same names in the namespace `LQGMetric.DFGPS.Q12`; proofs
verbatim. Wiring only.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric TopologicalSpace
open scoped ENNReal NNReal

namespace LQGMetric.DFGPS.Q12

open Blueprint LFPP HeatSq WhiteNoise DDDF

/-- **`𝔞_ε ≍ λ_ε`** (DFGPS T:888–891) for `λ` built from one white noise on `stdP`. -/
theorem aEpsDF_lambda_white' (h11 : DDDFThm1_1) (h12 : DDDFThm1_2Sq) (h29 : DDDFProp29Sq)
    (hLM : LMLem2_1) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ W : WNSpace → (ℕ → ℝ) → ℝ, IsWhiteNoise LQGDimension.ExistAsm.stdP W ∧
      ∃ C > 0, ∃ εb > 0, ∀ ε, 0 < ε → ε < εb →
        0 < lambdaDelta (xiGamma γ) W LQGDimension.ExistAsm.stdP ε ∧
        C⁻¹ * lambdaDelta (xiGamma γ) W LQGDimension.ExistAsm.stdP ε ≤ aEpsDF (xiGamma γ) ε ∧
        aEpsDF (xiGamma γ) ε ≤ C * lambdaDelta (xiGamma γ) W LQGDimension.ExistAsm.stdP ε := by
  obtain ⟨W, hW⟩ := exists_isWhiteNoise
  have := hW.isProbabilityMeasure
  obtain ⟨Ω, _, P, g, hP, hg⟩ := GFFExist.exists_wholePlaneGFF
  have hVb : Bornology.IsBounded ((sqOpens (-1) 3 : Opens ℂ) : Set ℂ) := isBounded_sqOpen (-1) 3
  have hVd : Disjoint ((sqOpens (-1) 3 : Opens ℂ) : Set ℂ) (sphere (0 : ℂ) 4) :=
    disjoint_sqOpen_sphere
  obtain ⟨hgw, hgn⟩ := isNormalizedAt_recenter hg one_pos (0 : ℂ)
  set g' : Ω → DistC := fun ω => addConst (g ω) (-circleAvg (g ω) 1 0)
  have hg' : IsNormalizedWPGFF g' P := ⟨hgw, hgn⟩
  obtain ⟨hh', hz', Xh', hsum', hharm', -, hX', hlink'⟩ :=
    markov_zb_coupling hLM P g' hgw (by norm_num : (0 : ℝ) < 4) 0 (sqOpens (-1) 3) hVb hVd
  obtain ⟨Y', hY', hT', hpos'⟩ := zb_step' h11 h12 h29 hγ hγ2 _ W hW P Xh' hX'
  exact ⟨W, hW, aEps_lambda_bounds hg' hsum' hharm' hX' hlink' hY' hT' hpos'⟩

/-- **The ratio bounds for `𝔞_ε`** (DFGPS T:1096–1097, DDDF (1.3) and (6.99)). -/
theorem aEpsDF_ratio_bounds' (h11 : DDDFThm1_1) (h12 : DDDFThm1_2Sq) (h29 : DDDFProp29Sq)
    (hLM : LMLem2_1) (h13 : DDDFEq1_3) (h699 : DDDFEq6_99) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) :
    ∃ Λ : ℝ, 1 < Λ ∧ ∀ δ ∈ Ioo (0 : ℝ) 1, ∃ η₀ > 0, ∀ η, 0 < η → η < η₀ →
      0 < aEpsDF (xiGamma γ) η ∧ 0 < aEpsDF (xiGamma γ) (δ * η) ∧
      Λ⁻¹ * δ ^ Λ ≤ aEpsDF (xiGamma γ) (δ * η) / aEpsDF (xiGamma γ) η ∧
      aEpsDF (xiGamma γ) (δ * η) / aEpsDF (xiGamma γ) η ≤ Λ * δ ^ (-Λ) := by
  obtain ⟨W, hW, hab⟩ := aEpsDF_lambda_white' h11 h12 h29 hLM hγ hγ2
  exact L214.ratio_bounds hab (h13 γ hγ hγ2 _ W hW) (h699 γ hγ hγ2 _ W hW)

/-- **DFGPS Lemma 2.14** in the form D78 (`Lem2_14`): `𝔠_r := liminf_n r 𝔞_{εn/r}/𝔞_{εn}` is a
positive cluster point of the ratios, with the Λ-bounds (T:1096–1097, DDDF (1.3), (6.99)). -/
theorem lem2_14' (h11 : DDDFThm1_1) (h12 : DDDFThm1_2Sq) (h29 : DDDFProp29Sq)
    (hLM : LMLem2_1) (h13 : DDDFEq1_3) (h699 : DDDFEq6_99) : Lem2_14 := by
  intro γ hγ hγ2 εn hε hεt
  obtain ⟨Λ, hΛ, hr⟩ := aEpsDF_ratio_bounds' h11 h12 h29 hLM h13 h699 hγ hγ2
  obtain ⟨h1, hrel⟩ := L214.ratio_rel hΛ hr hε hεt
  have hΛ1 : (0 : ℝ) < Λ + 1 := by linarith
  obtain ⟨hc, hb⟩ := L214.liminf_scaling
    (x := fun r n => r * aEpsDF (xiGamma γ) (εn n / r) / aEpsDF (xiGamma γ) (εn n))
    (A := fun δ => (Λ + 1)⁻¹ * δ ^ (Λ + 1)) (B := fun δ => (Λ + 1) * δ ^ (-(Λ + 1)))
    (fun δ hδ => mul_pos (inv_pos.2 hΛ1) (Real.rpow_pos_of_pos hδ.1 _))
    (fun δ hδ => mul_pos hΛ1 (Real.rpow_pos_of_pos hδ.1 _)) hrel h1
  exact ⟨_, Λ + 1, by linarith, hc, hb⟩

open L213 in
/-- **DFGPS Lemma 2.13** (`lem-lfpp-coord`, T:1060–1071, proof T:1101–1119), node `Lem2_13`
(DEC-78), from the Blueprint inputs of `lem2_14'` and `lem2_8_proved'`. -/
theorem lem2_13' (h11 : DDDFThm1_1) (h12 : DDDFThm1_2Sq) (h29 : DDDFProp29Sq) (hLM : LMLem2_1)
    (h13 : DDDFEq1_3) (h699 : DDDFEq6_99) : Lem2_13 := by
  intro γ hγ hγ2 εn hε hεt
  obtain ⟨c, Λ, hΛ, hc, hb⟩ := lem2_14' h11 h12 h29 hLM h13 h699 γ hγ hγ2 εn hε hεt
  have h25 := (lem2_5 (lem2_8_proved' h11 h12 h29 hLM h699)).1
  refine ⟨c, Λ, hΛ, hc, hb, ?_⟩
  intro Ω _ P _ h Dh hh hDh hconv X
  set ξ := xiGamma γ
  have hgff := isGFFPlusBddCont_of_normalizedWP hh
  obtain ⟨hS0, hlim0⟩ := h25 γ hγ hγ2 P h hgff
  -- the laws of `𝔞_δ⁻¹ D^δ_h`, `δ < 1/(m+1)`, and their limit points `T` as `δ → 0`
  set S : ℕ → Set (ProbabilityMeasure C(ℂ × ℂ, ℝ)) := fun m =>
    {ν | ∃ ε ∈ Ioo (0 : ℝ) (1 / ((m : ℝ) + 1)), (ν : Measure _) = P.map fun ω => lfppC ξ ε (h ω)}
  set T := ⋂ m, closure (S m)
  have hTc : IsClosed T := isClosed_iInter fun _ => isClosed_closure
  -- step 2: every `law(X r)` is in `T`
  have hXT : ∀ r, 0 < r → lawPM P (X r) ∈ T := by
    intro r hr
    obtain ⟨φs, hφs, hl⟩ := (hc r hr).2.tendsto_subseq
    have key := tendsto_law_scaled (P := P) (γ := γ) εn hε hεt Dh hh hDh hconv hr
      (hc r hr).1.ne' φs hφs hl
    have hεr : Tendsto (fun k => εn (φs k) / r) atTop (𝓝 0) := by
      simpa using (hεt.comp hφs.tendsto_atTop).div_const r
    refine mem_iInter.2 fun m => mem_closure_of_tendsto key ?_
    filter_upwards [hεr.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / ((m : ℝ) + 1)))]
      with k hk
    exact ⟨_, ⟨div_pos (hε _) hr, hk⟩, rfl⟩
  -- step 1: points of `T` are carried by continuous metrics
  have hTm : ∀ μ ∈ T, ∀ᵐ d ∂(μ : Measure C(ℂ × ℂ, ℝ)), IsContinuousMetric d := by
    intro μ hμ
    obtain ⟨U, hU⟩ := (𝓝 μ).exists_antitone_basis
    have hex : ∀ j, ∃ ν, ν ∈ U j ∧ ν ∈ S j := fun j =>
      mem_closure_iff_nhds.1 (mem_iInter.1 hμ j) _ (hU.mem j)
    choose ν hνU hνS using hex
    choose ε hε01 hεν using hνS
    have hνt : Tendsto ν atTop (𝓝 μ) := hU.tendsto hνU
    have hεt0 : Tendsto ε atTop (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        tendsto_one_div_add_atTop_nhds_zero_nat (fun j => (hε01 j).1.le) (fun j => (hε01 j).2.le)
    have hε1 : ∀ j, ε j ∈ Ioo (0 : ℝ) 1 := fun j => ⟨(hε01 j).1, (hε01 j).2.trans_le (by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])⟩
    filter_upwards [hlim0 ε ν μ (fun j => ⟨hε1 j, hεν j⟩) hεt0 hνt] with d hd
    exact hd.1
  -- step 3: assembly (T:1118)
  set L := {ν : ProbabilityMeasure C(ℂ × ℂ, ℝ) |
    ∃ r : ℝ, 0 < r ∧ (ν : Measure C(ℂ × ℂ, ℝ)) = P.map (X r)}
  have hLT : L ⊆ T := by
    rintro ν ⟨r, hr, hν⟩
    have : ν = lawPM P (X r) := Subtype.ext hν
    rw [this]; exact hXT r hr
  have hclL : closure L ⊆ T := closure_minimal hLT hTc
  refine ⟨?_, fun μ hμ => hTm μ (hclL hμ)⟩
  have hS0t : IsTightMeasureSet {((μ : ProbabilityMeasure C(ℂ × ℂ, ℝ)) : Measure _) | μ ∈ S 0} :=
    hS0.subset (by
      rintro _ ⟨μ, ⟨ε, hε', hμ⟩, rfl⟩
      exact ⟨ε, by simpa using hε', hμ⟩)
  have hK := isCompact_closure_of_isTightMeasureSet hS0t
  have hcl : IsCompact (closure L) :=
    hK.of_isClosed_subset isClosed_closure ((hclL.trans (iInter_subset _ 0)).trans subset_rfl)
  refine (isTight_of_isCompact_closure hcl).subset ?_
  rintro _ ⟨r, hr, rfl⟩
  exact ⟨lawPM P (X r), ⟨r, hr, rfl⟩, rfl⟩

end LQGMetric.DFGPS.Q12
