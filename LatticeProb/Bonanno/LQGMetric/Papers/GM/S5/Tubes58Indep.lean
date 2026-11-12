/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Tubes58Indep at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Tubes57Sq
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S3.Deterministic01

/-!
# GM Lemma 5.8, step 1 inputs: spatial independence at scale `R` and locality of `F_{ρr}(z)`
(task P2-M2L3)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, proof of
Lemma 5.8, Step 1 (l. 3066–3077): "By Lemmas 5.6 and 5.7, … each of the events `F_{ρr}(z)` … is
determined by `(h − h_{4ρr}(z))|_{B_{3ρr}(z)}` … Lemma 2.7 (applied with the whole-plane GFF
`h(·/(3ρr))` in place of `h`) implies …".

* `gm_L2_7_scaled`: GM Lemma 2.7 (`L2_7`, unit scale) at scale `R`: centres `R`-separated by
  `2(1+s)R`, events determined by `h|_{B_R(z)}` modulo any measurable additive constant. Proof: apply
  `L2_7` to `h(R ·)` (the same scaling as `measure_eq_one_of_L2_7`, GM l. 1204).
* `aeEventIn_tubeEvent_addConst`: `F_r(z)` (square tube `V ⊆ B_{3r}(z)`) is a.s. determined by
  `(h + a)|_{B_{3r}(z)}` for every measurable random constant `a` (GM Lemma 5.7 and Axiom III, as in
  GM l. 3001–3004), the form needed by `gm_L2_7_scaled` with `R = 3ρr`, `s = 1/3`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint LocalEvent

/-- **GM Lemma 2.7 at scale `R`** (from `L2_7` applied to `h(R ·)`) -/
theorem gm_L2_7_scaled (hL : L2_7) {s p q : ℝ} (hs : 0 < s) (hp : 0 < p) (hp1 : p < 1)
    (hq : 0 < q) (hq1 : q < 1) : ∃ n₀ : ℕ,
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC),
    IsWholePlaneGFF h P → ∀ R : ℝ, 0 < R → ∀ Z : Finset ℂ, n₀ ≤ Z.card →
    (∀ z ∈ Z, ∀ w ∈ Z, z ≠ w → 2 * (1 + s) * R ≤ ‖z - w‖) → ∀ E : ℂ → Set Ω,
    (∀ z ∈ Z, ∀ a : Ω → ℝ, Measurable a →
      AEEventIn P (fieldSigma (fun ω => addConst (h ω) (a ω)) (ballO z R)) (E z)) →
    (∀ z ∈ Z, ENNReal.ofReal p ≤ P (E z)) → ENNReal.ofReal q ≤ P (⋃ z ∈ Z, E z) := by
  obtain ⟨n₀, hn₀⟩ := hL hs hp hp1 hq hq1
  refine ⟨n₀, fun P _ h hh R hR Z hZ hsep E hdet hprob => ?_⟩
  set h' : _ → DistC := fun ω => affineComp R 0 (h ω) with hh'def
  have hh' : IsWholePlaneGFF h' P := hh.affineComp hR 0
  have hRi : (R⁻¹ : ℝ) ≠ 0 := inv_ne_zero hR.ne'
  have hRw : ∀ z : ℂ, R • ((R⁻¹ : ℝ) • z) = z := fun z => by
    rw [smul_smul, mul_inv_cancel₀ hR.ne', one_smul]
  set Z' := Z.image (fun z : ℂ => (R⁻¹ : ℝ) • z) with hZ'
  have hinj : Function.Injective (fun z : ℂ => (R⁻¹ : ℝ) • z) := fun a b hab => by
    have := congrArg (fun x : ℂ => R • x) hab
    simpa only [hRw] using this
  have hcard : Z'.card = Z.card := Finset.card_image_of_injective _ hinj
  have hU := hn₀ P h' hh' Z' (hcard ▸ hZ) ?_ (fun w => E (R • w)) ?_ ?_
  · refine hU.trans (measure_mono fun ω hω => ?_)
    simp only [mem_iUnion] at hω ⊢
    obtain ⟨w, hw, hωw⟩ := hω
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hw
    exact ⟨z, hz, by rwa [hRw] at hωw⟩
  · intro w₁ hw₁ w₂ hw₂ hne
    obtain ⟨z₁, hz₁, rfl⟩ := Finset.mem_image.1 hw₁
    obtain ⟨z₂, hz₂, rfl⟩ := Finset.mem_image.1 hw₂
    have hz : z₁ ≠ z₂ := fun he => hne (by rw [he])
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hR.le), ← div_eq_inv_mul,
      le_div_iff₀ hR]
    exact hsep z₁ hz₁ z₂ hz₂ hz
  · intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hw
    have hc : Measurable fun ω => -circleAvg (h' ω) (1 + s) ((R⁻¹ : ℝ) • z) :=
      ((measurable_circleAvg_left _ _).comp hh'.measurable).neg
    obtain ⟨F, hF, hEF⟩ := hdet z hz _ hc
    refine ⟨F, ?_, by simp only [hRw]; exact hEF⟩
    have hle := fieldSigma_le_affineComp (z := 0) (U := ballO z R)
      (V := ballO ((R⁻¹ : ℝ) • z) 1) hR (fun y => by
        have := mem_ballO_iff_scale hR ((R⁻¹ : ℝ) • z) y
        rwa [hRw] at this)
      (fun ω => addConst (h ω) (-circleAvg (h' ω) (1 + s) ((R⁻¹ : ℝ) • z)))
    simp only [affineComp_addConst hR] at hle
    exact hle _ hF
  · intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.1 hw
    simp only [hRw]
    exact hprob z hz

/-- **`F_r(z)` is a.s. determined by `(h + a)|_{B_{3r}(z)}`** for every measurable random constant
`a` (GM Lemma 5.7 for square tubes, with Axiom III) -/
theorem aeEventIn_tubeEvent_addConst (h38 : DFGPSLem3_8) {γ : ℝ}
    {D D' : DistC → ContMetric} {c : ℝ → ℝ} {cs Cs : ℝ} (hPS : PairSetting γ D D' c)
    (hRat : RatiosAre D D' cs Cs) (hcs : 0 < cs) (hCs : cs ≤ Cs) (c₁ η b ε r : ℝ) (z : ℂ)
    (V : Set ℂ) (s : ℝ) (X : Set ℂ) (hr : 0 < r) (hV : IsSquareTube V s X)
    (hVB : V ⊆ ball z (3 * r)) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsWholePlaneGFF h P) (a : Ω → ℝ)
    (ha : Measurable a) :
    AEEventIn P (fieldSigma (fun ω => addConst (h ω) (a ω)) (ballO z (3 * r)))
      (h ⁻¹' tubeEvent D D' cs Cs c₁ η b ε r z V) := by
  obtain ⟨-, -, hD, hD'⟩ := id hPS
  have hX : IsWholePlaneGFF (fun ω => addConst (h ω) (a ω)) P := hh.addConst ha
  obtain ⟨F, hF, hEF⟩ :=
    gm_L5_7locSq h38 hPS hRat hcs hCs c₁ η b ε r z V s X hr hV hVB P _ hX
  refine ⟨F, hF, EventuallyEq.trans ?_ hEF⟩
  have hgp := Tight.isGFFPlusCont_of_wp hh
  filter_upwards [hD.ae_dist_addConst hgp, hD'.ae_dist_addConst hgp] with ω h1 h2
  exact propext (mem_tubeEvent_of_scale (Real.exp_pos _) (h1 (a ω)) (h2 (a ω))).symm

end LQGMetric.GM
