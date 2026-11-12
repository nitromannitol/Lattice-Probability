/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.P3_1 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.P3_1Arith
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_2Node
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L3_4
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.Nodes
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T1_5
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S1.FieldAux

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Proposition 3.1 from Lemma 3.2 (task P2-DFA3, package DF-A3)

Dubédat–Falconet–Gwynne–Pfeffer–Sun, *Weak LQG metrics and Liouville first passage percolation*
(arXiv:1905.00380, `lqg-metric-estimates-final.tex`, "T"), Proposition 3.1
(`prop-two-set-dist`, T:1414–1420), proof T:1522–1568, followed step by step:

* bounded `U` (T:1525, T:1566): `P31.exists_bounded_conn` gives a bounded connected open
  `U₀ ⊆ U ⊇ K₁ ∪ K₂`; the lower bound is proved in `𝕣U` directly and the upper bound in `𝕣U₀`,
  then transferred to `𝕣U` by monotonicity of internal distances;
* `ν = 1`, `M` large, `F^ε_𝕣` from Lemma 3.2 (the node `Lem3_2`), (3.10) from Lemma 3.4
  (`lem3_4`, with `q` large; the paper takes `q = 2√2√(4+M)`, i.e. `M = q²/8 − 4`, which is
  what we do: `q = s`, `M = s²/8 − 4`);
* Step 1 `P31.lower_det`, Step 2 `P31.upper_det` with Lemma 3.5 (`lem3_5`), Step 3
  `P31.step3_arith` with `ε = A^{-β}`.
The paper's `ε = A^{-b/√M}` and "`M` can be made arbitrarily large" become an explicit choice of
`s` in terms of the target exponent `p`: `s = 32pξ + 2p(2Λ+6) + 16`.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace LQGMetric.DFGPS
open Blueprint P31

/-- the exponent choice: `M = s²/8 − 4` beats `2p(2Λ + ξs + 6)` -/
lemma exponent_choice {p ξ Λ : ℝ} (hp : 0 < p) (hξ : 0 < ξ) (hΛ : 1 < Λ) :
    let s := 32 * p * ξ + 2 * p * (2 * Λ + 6) + 16
    1 ≤ s ^ 2 / 8 - 4 ∧ p ≤ 1 / (2 * (2 * Λ + ξ * s + 6)) * (s ^ 2 / 8 - 4) := by
  intro s
  have hs16 : 16 ≤ s := by have : 0 ≤ 32 * p * ξ + 2 * p * (2 * Λ + 6) := by positivity
                           linarith
  have hs1 : 32 * p * ξ ≤ s := by have : 0 ≤ 2 * p * (2 * Λ + 6) := by positivity
                                  linarith
  have key : 2 * p * (2 * Λ + ξ * s + 6) ≤ s ^ 2 / 8 - 4 := by
    have h1 : 2 * p * ξ * s ≤ s ^ 2 / 16 := by nlinarith
    have h2 : 2 * p * (2 * Λ + 6) + 4 ≤ s ^ 2 / 16 := by nlinarith
    nlinarith
  refine ⟨by nlinarith, ?_⟩
  have hpos : 0 < 2 * (2 * Λ + ξ * s + 6) := by positivity
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hpos]
  linarith

/-- **DFGPS Proposition 3.1** (`prop-two-set-dist`, T:1414–1420), from DFGPS Lemma 3.2. -/
theorem prop3_1_of_lem3_2 (h32 : Lem3_2) : Prop3_1 := by
  intro γ hγ0 hγ2 D c hD U K₁ K₂ hU hUc hK₁ hK₂ hK₁c hK₂c h₁U h₂U hdisj hK₁n hK₂n Ω _ P _ h hh p hp
  set ξ := xiGamma γ with hξ_def
  have hξ : 0 < ξ := GM.xiGamma_pos hγ0
  obtain ⟨hcpos, ⟨Λ, hΛ, hc⟩, -⟩ := hD.tightness
  obtain ⟨U₀, R₀, hR₀, hU₀o, hU₀c, hU₀b, h₁U₀, h₂U₀, hU₀U⟩ :=
    exists_bounded_conn hU hUc hK₁ hK₁c hK₂ hK₂c h₁U h₂U
  obtain ⟨d, hd, hdK⟩ := exists_sep hK₁ hK₂ hdisj
  obtain ⟨hM1, hpM⟩ := exponent_choice hp hξ hΛ
  set s := 32 * p * ξ + 2 * p * (2 * Λ + 6) + 16 with hs_def
  set m := s ^ 2 / 8 - 4 with hm_def
  have hs : 0 < s := by positivity
  obtain ⟨C, hC, K, ε₀, hε₀, H32⟩ := h32 γ hγ0 hγ2 D c hD 1 m one_pos (by linarith)
  obtain ⟨ε₁, hε₁, H35⟩ := lem3_5 hU₀o hU₀c hK₁ hK₁c (Set.not_subsingleton_iff.1 hK₁n) hK₂
    hK₂c (Set.not_subsingleton_iff.1 hK₂n) h₁U₀ h₂U₀ (M := m) (by linarith)
  obtain ⟨C4, H34⟩ := lem3_4 hh.1 (ν := 1) (q := s) (R := R₀ + 1) zero_le_one hs (by linarith)
  set ε₂ := min (min ε₀ ε₁) (min 1 (min R₀⁻¹ (d / 3))) with hε₂_def
  have hε₂ : 0 < ε₂ := by positivity
  set a := 2 * Λ + ξ * s with ha_def
  have ha : 0 ≤ a := by positivity
  set β := 1 / (2 * (a + 6)) with hβ_def
  have hβ : 0 < β := by positivity
  set Bc := 2 * (8 * (R₀ + 1) + 1) ^ 2 + 1 with hBc_def
  have hBc : 1 ≤ Bc := by have : 0 ≤ 2 * (8 * (R₀ + 1) + 1) ^ 2 := by positivity
                          linarith
  refine ⟨|C4| + |K|, max (max 1 (ε₂ ^ (-(1 / β)))) ((Bc * C * Λ) ^ 2), fun A hA 𝕣 h𝕣 => ?_⟩
  have hA1 : 1 < A := lt_of_le_of_lt (le_max_left _ _ |>.trans (le_max_left _ _)) hA
  have hA0 : 0 < A := by linarith
  obtain ⟨hεpos, -, hlowA, hupA⟩ :=
    step3_arith ha hBc hC hΛ ((le_max_right _ _).trans hA.le)
  set ε := A ^ (-β) with hε_def
  have hεlt : ε < ε₂ := by
    have h1 : ε₂ ^ (-(1 / β)) < A := lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hA
    have h2 := Real.rpow_lt_rpow_of_neg (Real.rpow_pos_of_pos hε₂ _) h1 (by linarith : -β < 0)
    rwa [← Real.rpow_mul hε₂.le, show -(1 / β) * -β = 1 by field_simp, Real.rpow_one] at h2
  have hε0' : ε < ε₀ := hεlt.trans_le ((min_le_left _ _).trans (min_le_left _ _))
  have hε1' : ε < ε₁ := hεlt.trans_le ((min_le_left _ _).trans (min_le_right _ _))
  have hε1 : ε < 1 := hεlt.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hεR : ε ≤ R₀⁻¹ :=
    hεlt.le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hεd : 3 * ε ≤ d := by
    have : ε ≤ d / 3 :=
      hεlt.le.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    linarith
  -- the two bad events
  set S : Set ℝ := {r | ∃ k : ℕ, r = ((2 : ℝ) ^ k)⁻¹ * 𝕣} ∩ Icc (ε ^ ((1 : ℝ) + 1) * 𝕣) (ε * 𝕣)
  have hSc : S.Countable :=
    (countable_range fun k : ℕ => ((2 : ℝ) ^ k)⁻¹ * 𝕣).mono fun r hr => by
      obtain ⟨⟨k, rfl⟩, -⟩ := hr; exact ⟨k, rfl⟩
  have H34' := H34 𝕣 h𝕣 ε ⟨hεpos, hε1⟩ S hSc inter_subset_right
  have H32' := H32 P h hh.1 𝕣 h𝕣 ε ⟨hεpos, hε0'⟩
  set E34 := {ω | ∃ w ∈ ball (0 : ℂ) ((R₀ + 1) * 𝕣) ∩ gridPts (ε ^ ((1 : ℝ) + 1) * 𝕣 / 4),
    ∃ r ∈ S, s * Real.log ε⁻¹ < |circleAvg (h ω) r w - circleAvg (h ω) 𝕣 0|}
  set E32 := {ω | ¬ GoodCover (fun w r => h ω ∈ annEvent ξ D c C r w) 1 m ε 𝕣}
  have hexp : s ^ 2 / (2 * (1 + Real.sqrt 1) ^ 2) - 2 - 2 * 1 = m := by
    rw [Real.sqrt_one, hm_def]; ring
  rw [hexp] at H34'
  -- the event holds off `E34 ∪ E32`
  have hsub : {ω | ENNReal.ofReal (A⁻¹ * scaleFac ξ c (h ω) 𝕣 0) ≤
        setDistIn (D (h ω)) (scaleSet 𝕣 0 K₁) (scaleSet 𝕣 0 K₂) (scaleSet 𝕣 0 U) ∧
      setDistIn (D (h ω)) (scaleSet 𝕣 0 K₁) (scaleSet 𝕣 0 K₂) (scaleSet 𝕣 0 U) ≤
        ENNReal.ofReal (A * scaleFac ξ c (h ω) 𝕣 0)}ᶜ ⊆ E34 ∪ E32 := by
    intro ω hω
    by_contra hcon
    simp only [mem_union, not_or] at hcon
    obtain ⟨h34, h32⟩ := hcon
    have hcov : GoodCover (fun w r => h ω ∈ annEvent ξ D c C r w) 1 m ε 𝕣 := by
      by_contra hh'; exact h32 hh'
    have htail : TailOK (h ω) s ε 𝕣 (R₀ + 1) := by
      intro w hw hwg k hk1 hk2
      by_contra hlt
      push Not at hlt
      refine h34 ⟨w, ⟨mem_ball_zero_iff.2 hw, by rwa [rpow_one_add_one]⟩, _,
        ⟨⟨k, rfl⟩, ?_, ?_⟩, hlt⟩
      · rw [rpow_one_add_one]; exact mul_le_mul_of_nonneg_right hk1 h𝕣.le
      · exact mul_le_mul_of_nonneg_right hk2 h𝕣.le
    have hF : 0 ≤ scaleFac ξ c (h ω) 𝕣 0 :=
      (mul_pos (hcpos 𝕣 h𝕣) (Real.exp_pos _)).le
    apply hω
    refine ⟨?_, ?_⟩
    · refine le_trans ?_ (lower_det hξ hΛ hc hcpos hεpos hε1 h𝕣 hC hM1 hR₀ hεR hεd
        (h₁U₀.trans hU₀b) hdK hcov htail)
      refine ENNReal.ofReal_le_ofReal ?_
      have := mul_le_mul_of_nonneg_right hlowA hF
      linarith [show C⁻¹ * (Λ⁻¹ * ε ^ a * scaleFac ξ c (h ω) 𝕣 0) =
        C⁻¹ * (Λ⁻¹ * ε ^ a) * scaleFac ξ c (h ω) 𝕣 0 by ring]
    · have hmono : setDistIn (D (h ω)) (scaleSet 𝕣 0 K₁) (scaleSet 𝕣 0 K₂) (scaleSet 𝕣 0 U) ≤
          setDistIn (D (h ω)) (scaleSet 𝕣 0 K₁) (scaleSet 𝕣 0 K₂) (scaleSet 𝕣 0 U₀) :=
        iInf₂_mono fun x _ => iInf₂_mono fun y _ =>
          MetricGeometry.internalEDist_anti (Set.image_mono (Set.image_mono hU₀U)) _ _
      refine hmono.trans ((upper_det hξ hΛ hc hcpos hεpos hε1 h𝕣 hC hR₀ hU₀b
        (H35 ε ⟨hεpos, hε1'⟩ 𝕣 h𝕣 _ hcov) htail).trans (ENNReal.ofReal_le_ofReal ?_))
      have := mul_le_mul_of_nonneg_right hupA hF
      have e : Bc / ε ^ 6 * (C * (Λ * ε ^ (-(2 * Λ + ξ * s)) * scaleFac ξ c (h ω) 𝕣 0)) =
          Bc / ε ^ 6 * (C * (Λ * ε ^ (-a))) * scaleFac ξ c (h ω) 𝕣 0 := by ring
      rw [e]; exact this
  -- probability
  refine (measure_mono hsub).trans ((measure_union_le _ _).trans ?_)
  have hεm : ε ^ m ≤ A ^ (-p) := by
    rw [hε_def, ← Real.rpow_mul hA0.le]
    exact Real.rpow_le_rpow_of_exponent_le hA1.le (by nlinarith)
  have hεm0 : 0 ≤ ε ^ m := (Real.rpow_pos_of_pos hεpos _).le
  calc P E34 + P E32 ≤ ENNReal.ofReal (C4 * ε ^ m) + ENNReal.ofReal (K * ε ^ m) :=
        add_le_add H34' H32'
    _ ≤ ENNReal.ofReal (|C4| * ε ^ m) + ENNReal.ofReal (|K| * ε ^ m) := by
        gcongr <;> exact le_abs_self _
    _ = ENNReal.ofReal ((|C4| + |K|) * ε ^ m) := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_mul]
    _ ≤ ENNReal.ofReal ((|C4| + |K|) * A ^ (-p)) :=
        ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hεm (by positivity))

/-- DFGPS Theorem 1.5 (`Blueprint.DFGPSScaling`) from DFGPS Lemmas 3.2 and 3.6. -/
theorem dfgpsScaling_of_lem3_2 (h32 : Lem3_2) (h36 : Lem3_6) : Blueprint.DFGPSScaling :=
  dfgpsScaling_of_nodes (prop3_1_of_lem3_2 h32) h36

end LQGMetric.DFGPS
