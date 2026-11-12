/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.L36Lower at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.L36Graph
import LatticeProb.Bonanno.LQGMetric.Papers.DG.XiQBound
import LatticeProb.Bonanno.LQGMetric.Field.CircleAvgBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# DFGPS Lemma 3.6, lower bound for `𝕣 = 1`

DFGPS Lemma 3.6 (arXiv:1905.00380, T:1628–1650): w.p. → 1 as `δ → 0`,
`D̃^δ_h(∂_L 𝕊, ∂_R 𝕊; 𝕊) ≥ δ^{−ξQ+ζ} e^{ξ h_1(0)}`. Proof (DFGPS T:1646–1649 and node S11 of
`blueprint/DFGPS.md`): every left–right graph path gives a continuum path from `K = [0,1/4]×[0,1]` to
`∂U`, `U = (−1,1/2)×(−1,2)` (`L36Graph.dgSetDist_le_graphPath`), of LFPP length
`≤ √2 δ e^{ξ osc} Σ e^{ξ h_δ}`; DG Theorem 1.5 (second half of (1.5b), `Blueprint.DGThm1_5KU`)
gives `D^δ(K, ∂U) ≥ δ^{1 − ξQ + ζ/4}` and the oscillation bound (LQGDimension
`Osc37.osc_tendsto`, the circle-average continuity estimate used in DG's proof of Prop 3.16 via
DG Lemma 3.7) gives `osc ≤ (ζ/(4ξ)) log δ⁻¹`, both w.p. → 1. We compare the whole-plane field
directly (no white-noise intermediary; the field-level comparison of DG Lemma 3.7 is only needed
for this continuity estimate, which LQGDimension proves for the whole-plane circle averages).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace LQGMetric.DFGPS.L36

open Blueprint

/-- the bottom row `⟨kε, ε⟩`, `k = 1, …, M`, is a graph path from a leftmost to a rightmost
vertex of `𝕊 ∩ εℤ²` -/
theorem exists_graphPath {ε : ℝ} (hε : 0 < ε) (hε4 : ε ≤ 1/4) :
    ∃ L : List ℂ, IsGraphPath ε (rS 1) L ∧ (∃ x ∈ L.head?, x ∈ leftVerts ε 1) ∧
      ∃ y ∈ L.getLast?, y ∈ rightVerts ε 1 := by
  set c : ℤ := ⌈1 / ε⌉ with hc
  have hc1 : 1 / ε ≤ (c:ℝ) := Int.le_ceil _
  have hc2 : (c:ℝ) < 1 / ε + 1 := Int.ceil_lt_add_one _
  have hεinv : 4 ≤ 1 / ε := by rw [le_div_iff₀ hε]; linarith
  have hc4 : (2:ℝ) ≤ c := by linarith
  set M : ℕ := (c - 1).toNat with hM
  have hMc : (M:ℤ) = c - 1 := Int.toNat_of_nonneg (by
    have : (2:ℤ) ≤ c := by exact_mod_cast hc4
    omega)
  have hMR : (M:ℝ) = (c:ℝ) - 1 := by exact_mod_cast hMc
  have hM1 : 1 ≤ M := by
    have : (2:ℤ) ≤ c := by exact_mod_cast hc4
    omega
  have hMε : (M:ℝ) * ε < 1 := by
    rw [hMR]
    have : ((c:ℝ) - 1) < 1 / ε := by linarith
    calc ((c:ℝ) - 1) * ε < (1 / ε) * ε := mul_lt_mul_of_pos_right this hε
      _ = 1 := by field_simp
  set f : ℕ → ℂ := fun k => ⟨((k:ℤ) + 1 : ℤ) * ε, ((1:ℤ):ℝ) * ε⟩ with hf
  set L := (List.range M).map f with hL
  have hlen : L.length = M := by simp [hL]
  have hget : ∀ i (hi : i < L.length), L[i] = f i := fun i hi => by simp [hL]
  have hfS : ∀ k < M, f k ∈ rS 1 ∧ f k ∈ gridPts ε := fun k hk => by
    refine ⟨mem_rS_one.2 ⟨?_, ?_, ?_, ?_⟩, ⟨(k:ℤ) + 1, 1, rfl⟩⟩
    · simp only [hf]; push_cast; positivity
    · simp only [hf]; push_cast
      have : ((k:ℝ) + 1) ≤ M := by exact_mod_cast hk
      nlinarith
    · simp [hf, hε]
    · simp [hf]; linarith
  refine ⟨L, ⟨?_, ?_, ?_⟩, ⟨f 0, ?_, ?_⟩, ⟨f (M-1), ?_, ?_⟩⟩
  · rw [← List.length_pos_iff, hlen]; omega
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    exact hfS k (List.mem_range.1 hk)
  · rw [List.isChain_iff_getElem]
    intro i hi
    rw [hget, hget]
    left
    have : f i - f (i+1) = ((-ε : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hf] <;> ring
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_pos hε]
  · rw [List.head?_eq_getElem?, Option.mem_def, List.getElem?_eq_some_iff]
    exact ⟨by omega, hget 0 (by omega)⟩
  · refine ⟨hfS 0 (by omega), fun y ⟨hyS, a, b, hy⟩ => ?_⟩
    rw [hy] at hyS ⊢
    have h0 := (mem_rS_one.1 hyS).1
    simp only at h0 ⊢
    have ha : (0:ℝ) < a := pos_of_mul_pos_left h0 hε.le
    have ha1 : (1:ℝ) ≤ a := by exact_mod_cast (show (1:ℤ) ≤ a by exact_mod_cast ha)
    simp [hf]; nlinarith
  · rw [List.getLast?_eq_getElem?, Option.mem_def, List.getElem?_eq_some_iff]
    refine ⟨by omega, ?_⟩
    simp [hL]
  · refine ⟨hfS (M-1) (by omega), fun y ⟨hyS, a, b, hy⟩ => ?_⟩
    rw [hy] at hyS ⊢
    have h1 := (mem_rS_one.1 hyS).2.1
    simp only at h1 ⊢
    have ha : (a:ℝ) < c := by
      have : (a:ℝ) < 1 / ε := by rw [lt_div_iff₀ hε]; linarith
      linarith
    have ha' : a ≤ c - 1 := by
      have : a < c := by exact_mod_cast ha
      omega
    have : (a:ℝ) ≤ M := by rw [hMR]; exact_mod_cast ha'
    have hM1' : ((M - 1 : ℕ) : ℝ) + 1 = M := by
      rw [Nat.cast_sub hM1]; push_cast; ring
    simp only [hf]; push_cast
    rw [hM1']
    nlinarith

/-- `graphLFPP` only sees the field on the vertices `U ∩ εℤ²` -/
lemma graphLFPP_congr {ξ ε : ℝ} {φ ψ : ℂ → ℝ} {A B U : Set ℂ}
    (hφψ : ∀ x ∈ U, x ∈ gridPts ε → φ x = ψ x) :
    graphLFPP ξ ε φ A B U = graphLFPP ξ ε ψ A B U := by
  unfold graphLFPP
  refine iInf_congr fun L => congrArg List.sum (List.map_congr_left fun x hx => ?_)
  have := L.2.1.2.1 x hx
  rw [hφψ x this.1 this.2]

/-- **Deterministic lower bound.** If `D^ε(K, ∂U) ≥ A` then
`D̃^ε(∂_L 𝕊, ∂_R 𝕊; 𝕊) ≥ A / (√2 ε e^{ξ osc_{8ε} φ})`. -/
theorem graphLFPP_ge {ε : ℝ} (hε : 0 < ε) (hε4 : ε ≤ 1/4) (φ : ℂ → ℝ) (hφ : Continuous φ)
    (ξ : ℝ) (hξ : 0 ≤ ξ) (A : ℝ) (hA : ENNReal.ofReal A ≤ dgSetDist ξ φ K36 U36) :
    A / (Real.sqrt 2 * ε * Real.exp (ξ * LQGDimension.Blueprint.Draft.osc φ (8 * ε))) ≤
      graphLFPP ξ ε φ (leftVerts ε 1) (rightVerts ε 1) (rS 1) := by
  obtain ⟨L₀, hL₀, h0, h1⟩ := exists_graphPath hε hε4
  haveI : Nonempty {L : List ℂ // IsGraphPath ε (rS 1) L ∧ (∃ x ∈ L.head?, x ∈ leftVerts ε 1) ∧
      ∃ y ∈ L.getLast?, y ∈ rightVerts ε 1} := ⟨⟨L₀, hL₀, h0, h1⟩⟩
  have hc : 0 < Real.sqrt 2 * ε * Real.exp (ξ * LQGDimension.Blueprint.Draft.osc φ (8 * ε)) := by
    have : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    positivity
  refine le_ciInf fun L => ?_
  have hb := hA.trans (dgSetDist_le_graphPath hε hε4 φ hφ ξ hξ L.1 L.2.1 L.2.2.1 L.2.2.2)
  have hs : 0 ≤ (L.1.map fun x => Real.exp (ξ * φ x)).sum :=
    List.sum_nonneg fun y hy => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.1 hy
      exact (Real.exp_pos _).le
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at hb
  rw [div_le_iff₀ hc]
  linarith

lemma dgLambda_eq {γ : ℝ} (hγ : 0 < γ) : DG.dgLambda γ = 1 - xiGamma γ * Q γ := by
  have hd := DG.dGamma_pos γ
  unfold DG.dgLambda xiGamma Q
  field_simp
  ring

/-- **DFGPS Lemma 3.6, lower bound, `𝕣 = 1`.** -/
theorem lem3_6_lower_one (hKU : DGThm1_5KU) {γ : ℝ} (hγ0 : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWPGFF h P) {ζ : ℝ} (hζ : 0 < ζ) {η : ℝ} (hη : 0 < η) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ ∈ Ioo (0 : ℝ) δ₀,
      P {ω | ¬ δ ^ (-xiGamma γ * Q γ + ζ) * Real.exp (xiGamma γ * circleAvg (h ω) 1 0) ≤
        graphLFPP (xiGamma γ) δ (fun x => circleAvg (h ω) δ x) (leftVerts δ 1) (rightVerts δ 1)
          (rS 1)} ≤ ENNReal.ofReal η := by
  obtain ⟨H, hH, -, hHae⟩ := CircleAvg.exists_isGFFCircleAverage_normalized hh
  set ξ := xiGamma γ with hξdef
  have hξ : 0 < ξ := DG.xiGamma_pos hγ0
  set κ := ζ / (4 * ξ) with hκ
  have hκ0 : 0 < κ := by positivity
  have hT1 := hKU γ hγ0 hγ2 P H hH U36 K36 isOpen_U36 isBounded_U36 isCompact_K36 K36_nonempty
    K36_subset_U36 (ζ/4) (by positivity)
  have hT2 := LQGDimension.Osc37.osc_tendsto hH hκ0
  have hη2 : (0 : ℝ≥0∞) < ENNReal.ofReal (η/2) := ENNReal.ofReal_pos.2 (by positivity)
  have hT3 : Tendsto (fun δ : ℝ => δ ^ (ζ/2)) (𝓝[>] 0) (𝓝 0) := by
    have := Real.continuousAt_rpow_const 0 (ζ/2) (Or.inr (by positivity))
    rw [ContinuousAt, Real.zero_rpow (by positivity)] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hev := ((hT1.eventually (gt_mem_nhds hη2)).and (hT2.eventually (gt_mem_nhds hη2))).and
    ((hT3.eventually (gt_mem_nhds (show (0:ℝ) < 1/2 by norm_num))).and
      (Ioo_mem_nhdsGT (show (0:ℝ) < 1/4 by norm_num)))
  obtain ⟨δ₀, hδ₀, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  refine ⟨δ₀, hδ₀, fun δ hδ => ?_⟩
  obtain ⟨⟨hA, hB⟩, hpow, hδ14⟩ := hsub hδ
  have hδ0 : 0 < δ := hδ.1
  have hδ4 : δ ≤ 1/4 := hδ14.2.le
  -- the null set where `H` and the circle averages of `h` differ on the grid
  set N := {ω | ¬ (circleAvg (h ω) 1 0 = 0 ∧ ∀ ab : ℤ × ℤ,
    H δ ⟨ab.1 * δ, ab.2 * δ⟩ ω = circleAvg (h ω) δ ⟨ab.1 * δ, ab.2 * δ⟩)} with hN
  have hN0 : P N = 0 := by
    have hall : ∀ᵐ ω ∂P, ∀ ab : ℤ × ℤ,
        H δ ⟨ab.1 * δ, ab.2 * δ⟩ ω = circleAvg (h ω) δ ⟨ab.1 * δ, ab.2 * δ⟩ :=
      ae_all_iff.2 fun ab => hHae δ hδ0 _
    have := hh.2.and hall
    rwa [ae_iff] at this
  set A := {ω | ¬ (ENNReal.ofReal (δ ^ (DG.dgLambda γ + ζ/4)) ≤
      dgSetDist ξ (fun x => H δ x ω) K36 U36 ∧
    dgSetDist ξ (fun x => H δ x ω) K36 U36 ≤ ENNReal.ofReal (δ ^ (DG.dgLambda γ - ζ/4)))}
  set B := {ω | κ * Real.log (1 / δ) <
    LQGDimension.Blueprint.Draft.osc (fun z => H δ z ω) (8 * δ)}
  have hsubE : {ω | ¬ δ ^ (-ξ * Q γ + ζ) * Real.exp (ξ * circleAvg (h ω) 1 0) ≤
      graphLFPP ξ δ (fun x => circleAvg (h ω) δ x) (leftVerts δ 1) (rightVerts δ 1) (rS 1)} ⊆
      A ∪ B ∪ N := by
    intro ω hω
    by_contra hc
    simp only [mem_union, not_or] at hc
    obtain ⟨⟨hAω, hBω⟩, hNω⟩ := hc
    simp only [A, mem_setOf_eq, not_not] at hAω
    simp only [B, mem_setOf_eq, not_lt] at hBω
    simp only [hN, mem_setOf_eq, not_not] at hNω
    apply hω
    rw [hNω.1, mul_zero, Real.exp_zero, mul_one]
    have hcongr : graphLFPP ξ δ (fun x => circleAvg (h ω) δ x) (leftVerts δ 1) (rightVerts δ 1)
        (rS 1) = graphLFPP ξ δ (fun x => H δ x ω) (leftVerts δ 1) (rightVerts δ 1) (rS 1) :=
      graphLFPP_congr fun x _ ⟨a, b, hx⟩ => by rw [hx]; exact (hNω.2 (a, b)).symm
    rw [hcongr]
    refine le_trans ?_ (graphLFPP_ge hδ0 hδ4 _ (hH.continuous δ hδ0 ω) ξ hξ.le _ hAω.1)
    set O := LQGDimension.Blueprint.Draft.osc (fun z => H δ z ω) (8 * δ)
    have hO : Real.exp (ξ * O) ≤ δ ^ (-(ζ/4)) := by
      rw [Real.rpow_def_of_pos hδ0]
      apply Real.exp_le_exp.2
      have : ξ * O ≤ ξ * (κ * Real.log (1 / δ)) := mul_le_mul_of_nonneg_left hBω hξ.le
      have e : ξ * (κ * Real.log (1 / δ)) = Real.log δ * (-(ζ/4)) := by
        rw [hκ, one_div, Real.log_inv]; field_simp
      linarith
    have hs2 : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
    have hs2' : Real.sqrt 2 ≤ 2 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    have hden : 0 < Real.sqrt 2 * δ * Real.exp (ξ * O) := by positivity
    rw [le_div_iff₀ hden]
    have e : δ ^ (-ξ * Q γ + ζ) * δ * δ ^ (-(ζ/4)) = δ ^ (ζ/2) * δ ^ (DG.dgLambda γ + ζ/4) := by
      calc δ ^ (-ξ * Q γ + ζ) * δ * δ ^ (-(ζ/4))
          = δ ^ (-ξ * Q γ + ζ) * δ ^ (1:ℝ) * δ ^ (-(ζ/4)) := by rw [Real.rpow_one]
        _ = δ ^ (-ξ * Q γ + ζ + 1 + -(ζ/4)) := by rw [← Real.rpow_add hδ0, ← Real.rpow_add hδ0]
        _ = δ ^ (ζ/2 + (DG.dgLambda γ + ζ/4)) := by congr 1; rw [dgLambda_eq hγ0]; ring
        _ = _ := Real.rpow_add hδ0 _ _
    have hpos1 : 0 < δ ^ (-ξ * Q γ + ζ) := Real.rpow_pos_of_pos hδ0 _
    have hpos2 : 0 < δ ^ (DG.dgLambda γ + ζ/4) := Real.rpow_pos_of_pos hδ0 _
    calc δ ^ (-ξ * Q γ + ζ) * (Real.sqrt 2 * δ * Real.exp (ξ * O))
        ≤ δ ^ (-ξ * Q γ + ζ) * (Real.sqrt 2 * δ * δ ^ (-(ζ/4))) := by gcongr
      _ = Real.sqrt 2 * (δ ^ (ζ/2) * δ ^ (DG.dgLambda γ + ζ/4)) := by rw [← e]; ring
      _ ≤ 2 * (1/2 * δ ^ (DG.dgLambda γ + ζ/4)) := by gcongr
      _ = δ ^ (DG.dgLambda γ + ζ/4) := by ring
  calc P _ ≤ P (A ∪ B ∪ N) := measure_mono hsubE
    _ ≤ P A + P B + P N := (measure_union_le _ _).trans (by gcongr; exact measure_union_le _ _)
    _ ≤ ENNReal.ofReal (η/2) + ENNReal.ofReal (η/2) + 0 := by
        rw [hN0]; exact add_le_add (add_le_add hA.le hB.le) le_rfl
    _ = ENNReal.ofReal η := by
        rw [add_zero, ← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf

end LQGMetric.DFGPS.L36
