/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DFGPS.T1_5CentreDet at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T1_5CentreGeom
import LatticeProb.Bonanno.LQGMetric.Papers.DFGPS.T1_5Chain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
DFGPS (arXiv:1905.00380, "T"), proof of Theorem 1.5:
* Step 2 (T:1677–1691, (eqn-lfpp-lower)): if every grid vertex `z ∈ (𝕣𝕊) ∩ (sℤ²)` (`s = δ𝕣`) has
  short crossings of its two rectangles (cost `≤ K e^{ξ φ(z)}`), then the `D`-distance between
  the sides `{0} × [-𝕣, 2𝕣]` and `{𝕣} × [-𝕣, 2𝕣]` inside `(-2𝕣, 3𝕣)²` is at most
  `4K·M` whenever `M` exceeds the discretized LFPP distance `D̃^s(∂_L, ∂_R; 𝕣𝕊)`
  (`step2_det`);
* Step 3 (T:1693–1720, (eqn-lfpp-upper)): if every annulus around a grid vertex costs at least
  `K' e^{ξ φ(z)}` to cross, then `K'·D̃^s(∂_L, ∂_R; 𝕣𝕊)` is at most the `D`-distance between the
  sides `{0} × [3𝕣/8, 5𝕣/8]` and `{5𝕣/4} × [3𝕣/8, 5𝕣/8]` inside `(-𝕣/8, 11𝕣/8) × (𝕣/4, 3𝕣/4)`
  (`step3_det`).
These combine `setDistIn_le_of_graphPath` (T1_5Chain) and `exists_graphPath_le_len` (T1_5Disc)
with the box descriptions of T1_5CentreGeom. Boxes instead of the paper's `𝕣∂_L𝕊`, `𝕣∂_R𝕊`: see
the proposed DEVIATIONS entry in the report (the paper's sets are compared to these through
Axiom V / Prop 3.1 in the same way).
-/

noncomputable section

open Set Metric Complex
open scoped ENNReal ComplexOrder

namespace LQGMetric.DFGPS
open Blueprint MetricGeometry

/-- the sets of the horizontal / vertical rectangle crossings and of the two boxes -/
abbrev rectHK₁ : Set ℂ := Icc (-5 / 2) (-5 / 2) ×ℂ Icc (-1 / 4) (1 / 4)
abbrev rectHK₂ : Set ℂ := Icc (5 / 2) (5 / 2) ×ℂ Icc (-1 / 4) (1 / 4)
abbrev rectHU : Set ℂ := Ioo (-3) 3 ×ℂ Ioo (-1 / 2) (1 / 2)
abbrev rectVK₁ : Set ℂ := Icc (-1 / 4) (1 / 4) ×ℂ Icc (-5 / 2) (-5 / 2)
abbrev rectVK₂ : Set ℂ := Icc (-1 / 4) (1 / 4) ×ℂ Icc (5 / 2) (5 / 2)
abbrev rectVU : Set ℂ := Ioo (-1 / 2) (1 / 2) ×ℂ Ioo (-3) 3
abbrev box2K₁ : Set ℂ := Icc 0 0 ×ℂ Icc (-1) 2
abbrev box2K₂ : Set ℂ := Icc 1 1 ×ℂ Icc (-1) 2
abbrev box2U : Set ℂ := Ioo (-2) 3 ×ℂ Ioo (-2) 3
abbrev box3K₁ : Set ℂ := Icc 0 0 ×ℂ Icc (3 / 8) (5 / 8)
abbrev box3K₂ : Set ℂ := Icc (5 / 4) (5 / 4) ×ℂ Icc (3 / 8) (5 / 8)
abbrev box3U : Set ℂ := Ioo (-1 / 8) (11 / 8) ×ℂ Ioo (1 / 4) (3 / 4)

/-- the cost of a graph path -/
lemma graphLFPP_le_cost {ξ s 𝕣 : ℝ} {φ : ℂ → ℝ} {L : List ℂ} (hL : IsGraphPath s (rS 𝕣) L)
    (hhead : ∃ x ∈ L.head?, x ∈ leftVerts s 𝕣) (hlast : ∃ y ∈ L.getLast?, y ∈ rightVerts s 𝕣) :
    graphLFPP ξ s φ (leftVerts s 𝕣) (rightVerts s 𝕣) (rS 𝕣) ≤
      (L.map fun x => Real.exp (ξ * φ x)).sum :=
  ciInf_le ⟨0, by
    rintro _ ⟨L', rfl⟩
    exact List.sum_nonneg fun x hx => by
      obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
      exact (Real.exp_pos _).le⟩ (⟨L, hL, hhead, hlast⟩ :
      {L : List ℂ // IsGraphPath s (rS 𝕣) L ∧ (∃ x ∈ L.head?, x ∈ leftVerts s 𝕣) ∧
        ∃ y ∈ L.getLast?, y ∈ rightVerts s 𝕣})

/-- **Step 2** (deterministic) -/
theorem step2_det (D : ContMetric) {s 𝕣 : ℝ} (hs : 0 < s) (hs𝕣 : 8 * s ≤ 𝕣) {ξ K : ℝ}
    (hK : 0 < K) (φ : ℂ → ℝ)
    (hH : ∀ z ∈ rS 𝕣 ∩ gridPts s, setDistIn D (scaleSet s z rectHK₁) (scaleSet s z rectHK₂)
      (scaleSet s z rectHU) ≤ ENNReal.ofReal (K * Real.exp (ξ * φ z)))
    (hV : ∀ z ∈ rS 𝕣 ∩ gridPts s, setDistIn D (scaleSet s z rectVK₁) (scaleSet s z rectVK₂)
      (scaleSet s z rectVU) ≤ ENNReal.ofReal (K * Real.exp (ξ * φ z)))
    (hpos : 0 < graphLFPP ξ s φ (leftVerts s 𝕣) (rightVerts s 𝕣) (rS 𝕣)) {M : ℝ}
    (hM : graphLFPP ξ s φ (leftVerts s 𝕣) (rightVerts s 𝕣) (rS 𝕣) < M) :
    setDistIn D (scaleSet 𝕣 0 box2K₁) (scaleSet 𝕣 0 box2K₂) (scaleSet 𝕣 0 box2U) ≤
      ENNReal.ofReal (4 * K * M) := by
  have h𝕣 : 0 < 𝕣 := by linarith
  set Y := scaleSet 𝕣 0 box2U with hY
  set b : ℂ → ℝ := fun z => 2 * (K * Real.exp (ξ * φ z)) with hb
  have hbpos : ∀ z, 0 < K * Real.exp (ξ * φ z) := fun z => mul_pos hK (Real.exp_pos _)
  -- the crossings
  have hHex : ∀ z, ∃ P : ℝ → ℂ, z ∈ rS 𝕣 ∩ gridPts s → HCross D s Y z P (b z) := by
    intro z
    by_cases hz : z ∈ rS 𝕣 ∩ gridPts s
    · have hlt : setDistIn D (scaleSet s z rectHK₁) (scaleSet s z rectHK₂) (scaleSet s z rectHU) <
          ENNReal.ofReal (b z) :=
        (hH z hz).trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith [hbpos z])).2
          (by simp only [hb]; linarith [hbpos z]))
      obtain ⟨P, hPc, hP0, hP1, hPm, hlen⟩ := exists_path_of_setDistIn_lt D hlt
      have hzS := (mem_rS_iff h𝕣).1 hz.1
      rw [mem_scaleSet_Icc hs] at hP0 hP1
      refine ⟨P, fun _ => ⟨hPc, by linarith [hP0.1.1, hP0.1.2], by linarith [hP1.1.1, hP1.1.2],
        fun t ht => ?_, fun t ht => ?_, hlen.le⟩⟩
      · have := (mem_scaleSet_Ioo hs _ _ _ _ _ _).1 (hPm ht)
        rw [abs_le]; constructor <;> linarith [this.2.1, this.2.2]
      · have := (mem_scaleSet_Ioo hs _ _ _ _ _ _).1 (hPm ht)
        rw [hY, mem_scaleSet_Ioo h𝕣]
        simp only [zero_re, zero_im]
        refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith [this.1.1, this.1.2, this.2.1, this.2.2]
    · exact ⟨fun _ => 0, fun h => absurd h hz⟩
  have hVex : ∀ z, ∃ P : ℝ → ℂ, z ∈ rS 𝕣 ∩ gridPts s → VCross D s Y z P (b z) := by
    intro z
    by_cases hz : z ∈ rS 𝕣 ∩ gridPts s
    · have hlt : setDistIn D (scaleSet s z rectVK₁) (scaleSet s z rectVK₂) (scaleSet s z rectVU) <
          ENNReal.ofReal (b z) :=
        (hV z hz).trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by linarith [hbpos z])).2
          (by simp only [hb]; linarith [hbpos z]))
      obtain ⟨P, hPc, hP0, hP1, hPm, hlen⟩ := exists_path_of_setDistIn_lt D hlt
      have hzS := (mem_rS_iff h𝕣).1 hz.1
      rw [mem_scaleSet_Icc hs] at hP0 hP1
      refine ⟨P, fun _ => ⟨hPc, by linarith [hP0.2.1, hP0.2.2], by linarith [hP1.2.1, hP1.2.2],
        fun t ht => ?_, fun t ht => ?_, hlen.le⟩⟩
      · have := (mem_scaleSet_Ioo hs _ _ _ _ _ _).1 (hPm ht)
        rw [abs_le]; constructor <;> linarith [this.1.1, this.1.2]
      · have := (mem_scaleSet_Ioo hs _ _ _ _ _ _).1 (hPm ht)
        rw [hY, mem_scaleSet_Ioo h𝕣]
        simp only [zero_re, zero_im]
        refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> nlinarith [this.1.1, this.1.2, this.2.1, this.2.2]
    · exact ⟨fun _ => 0, fun h => absurd h hz⟩
  choose H hHc using hHex
  choose V hVc using hVex
  -- a near-optimal graph path
  have hne : Nonempty {L : List ℂ // IsGraphPath s (rS 𝕣) L ∧
      (∃ x ∈ L.head?, x ∈ leftVerts s 𝕣) ∧ ∃ y ∈ L.getLast?, y ∈ rightVerts s 𝕣} := by
    by_contra hcon
    rw [not_nonempty_iff] at hcon
    have h0 : graphLFPP ξ s φ (leftVerts s 𝕣) (rightVerts s 𝕣) (rS 𝕣) = 0 := by
      unfold graphLFPP; exact Real.iInf_of_isEmpty _
    linarith
  obtain ⟨⟨L, hL, hhead, hlast⟩, hLM⟩ := exists_lt_of_ciInf_lt hM
  have key := setDistIn_le_of_graphPath D b H V hs (by linarith)
    (fun z => by simp only [hb]; linarith [hbpos z]) (fun z hz => hHc z hz) (fun z hz => hVc z hz)
    (K₁ := scaleSet 𝕣 0 box2K₁) (K₂ := scaleSet 𝕣 0 box2K₂) ?_ ?_ hL hhead hlast
  · refine key.trans (ENNReal.ofReal_le_ofReal ?_)
    have e : (L.map fun x => 2 * b x) = L.map fun x => (4 * K) * Real.exp (ξ * φ x) := by
      refine List.map_congr_left fun x _ => ?_
      simp only [hb]; ring
    rw [e, List.sum_map_mul_left]
    exact mul_le_mul_of_nonneg_left hLM.le (by linarith)
  · intro w hw ⟨y, hy, hwy⟩
    have hyS := (mem_rS_iff h𝕣).1 hy
    rw [abs_le] at hwy
    rw [mem_scaleSet_Icc h𝕣]
    simp only [zero_re, zero_im]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith
  · intro w hw ⟨y, hy, hwy⟩
    have hyS := (mem_rS_iff h𝕣).1 hy
    rw [abs_le] at hwy
    rw [mem_scaleSet_Icc h𝕣]
    simp only [zero_re, zero_im]
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith

/-- **Step 3** (deterministic) -/
theorem step3_det (D : ContMetric) {s 𝕣 : ℝ} (hs : 0 < s) (hs𝕣 : 8 * s ≤ 𝕣) {ξ K' : ℝ}
    (hK' : 0 < K') (φ : ℂ → ℝ)
    (hann : ∀ z ∈ rS 𝕣 ∩ gridPts s, ENNReal.ofReal (K' * Real.exp (ξ * φ z)) ≤
      setDistIn D (closedBall z (3 / 4 * s)) (sphere z (3 / 2 * s)) (ball z (2 * s)))
    {X : ℝ} (hX : setDistIn D (scaleSet 𝕣 0 box3K₁) (scaleSet 𝕣 0 box3K₂) (scaleSet 𝕣 0 box3U) <
      ENNReal.ofReal X) :
    K' * graphLFPP ξ s φ (leftVerts s 𝕣) (rightVerts s 𝕣) (rS 𝕣) ≤ X := by
  have h𝕣 : 0 < 𝕣 := by linarith
  obtain ⟨P, hPc, hP0, hP1, hPm, hlen⟩ := exists_path_of_setDistIn_lt D hX
  rw [mem_scaleSet_Icc h𝕣] at hP0 hP1
  simp only [zero_re, zero_im] at hP0 hP1
  obtain ⟨ta, tb, hta, htab, htb, hfa, hfb, hmid⟩ := RectCross.exists_sub_crossing
    (f := fun t => (P t).re) zero_le_one (continuous_re.comp_continuousOn hPc)
    (z := s) (w := 𝕣 + 2 * s) (by linarith) (by linarith [hP0.1.2]) (by linarith [hP1.1.1])
  have hsub : Icc ta tb ⊆ Icc 0 1 := Icc_subset_Icc hta htb
  obtain ⟨L, hL, hhead, hlast, hLlen⟩ := exists_graphPath_le_len D hs (by linarith)
    (fun z => K' * Real.exp (ξ * φ z)) hann htab (hPc.mono hsub) (fun t ht => (hmid t ht).1)
    (fun t ht => by
      have := (mem_scaleSet_Ioo h𝕣 _ _ _ _ _ _).1 (hPm (hsub ht))
      simp only [zero_re, zero_im] at this
      constructor <;> linarith [this.2.1, this.2.2])
    hfa hfb.ge
  have hlen' : D.len P ta tb ≤ D.len P 0 1 := curveLength_mono _ hta htb
  have hsum : ENNReal.ofReal (L.map fun z => K' * Real.exp (ξ * φ z)).sum < ENNReal.ofReal X :=
    (hLlen.trans hlen').trans_lt hlen
  rw [List.sum_map_mul_left] at hsum
  have h2 := (ENNReal.ofReal_lt_ofReal_iff'.1 hsum).1
  exact (mul_le_mul_of_nonneg_left (graphLFPP_le_cost hL hhead hlast) hK'.le).trans h2.le

end LQGMetric.DFGPS
