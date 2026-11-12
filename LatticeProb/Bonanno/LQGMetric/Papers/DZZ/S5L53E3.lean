/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53E3 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53E2
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53B11A

/-!
# DZZ Lemma 5.3, part 1: the counting step of (eq-z-open) and the μIn wrapper (P2-DZZ53E)

Ding–Zeitouni–Zhang, arXiv:1807.00422, `LBM_LGDarXiv.tex`.

* **`l53_far_count`** (l. 2495–2502): if every pair `(z, z')` of `∂𝖡` is *far*
  (`log D̃(z,z') ≥ E log D̃_{δ̃}(u,v) + (log δ⁻¹)^{0.97}`) with probability `≤ p`, then
  `a b · P(𝓛₁{z : 𝓛₁(Λ_{z,far}) ≥ a} ≥ b) ≤ p 𝓛₁(∂𝖡)²` (DZZ: `p = O(K⁻⁴)`, `a = b = K⁻¹ 𝓛₁(∂𝖡)`,
  giving `O(K⁻²)`). DZZ only say "therefore"; the proof is Tonelli plus Markov twice.
  The far relation is any jointly measurable random relation.
* **`l53_open_of_not_bad`** (l. 2502, "this implies that (eq-z-open) holds"): off that bad event,
  every `Λ ⊆ ∂𝖡` with `𝓛₁(Λ) ≥ b` contains a point `z` whose non-far set
  `Λ' = {z' : (z,z') not far}` has `𝓛₁(∂𝖡) ≤ 𝓛₁(Λ') + a`, i.e. `𝖡` is open.
* **`dzzLem53Exp_dzzMuIn_of_desirable`**: DZZ Lemma 5.3 at `μIn` from the desirability bound
  (the hypothesis of `dzzLem53Event_of_desirable`) for every pair `u ≠ v` of `𝕍̄`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal MeasureTheory

namespace LQGMetric
namespace DZZ

open WhiteNoise

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **The counting step of (eq-z-open)** (DZZ l. 2495–2502): Tonelli and Markov. `S` is the random
far relation `{((ω, z), z') | (z, z') far at ω}`. -/
theorem l53_far_count {X : Type*} [MeasurableSpace X] (P : Measure Ω) [SFinite P]
    (ν : Measure X) [SFinite ν] {S : Set ((Ω × X) × X)} (hS : MeasurableSet S) {p : ℝ≥0∞}
    (hp : ∀ z z', P {ω | ((ω, z), z') ∈ S} ≤ p) (a b : ℝ≥0∞) :
    a * b * P {ω | b ≤ ν {z | a ≤ ν {z' | ((ω, z), z') ∈ S}}} ≤ p * ν univ ^ 2 := by
  set f : (Ω × X) × X → ℝ≥0∞ := S.indicator 1 with hf
  have hfm : Measurable f := measurable_one.indicator hS
  -- `h (ω, z) = 𝓛₁(Λ_{z,far})`
  set h : Ω × X → ℝ≥0∞ := fun q => ∫⁻ z', f (q, z') ∂ν with hh
  have hhm : Measurable h := hfm.lintegral_prod_right'
  have hh_eq : ∀ q, h q = ν {z' | (q, z') ∈ S} := by
    intro q
    have hsl : MeasurableSet {z' | (q, z') ∈ S} := measurable_prodMk_left hS
    rw [hh, ← lintegral_indicator_one hsl]
    rfl
  set G : Ω → ℝ≥0∞ := fun ω => ∫⁻ z, h (ω, z) ∂ν with hG
  have hGm : Measurable G := hhm.lintegral_prod_right'
  -- the bad event is inside `{a b ≤ G}`
  have hsub : {ω | b ≤ ν {z | a ≤ ν {z' | ((ω, z), z') ∈ S}}} ⊆ {ω | a * b ≤ G ω} := by
    intro ω hω
    simp only [mem_ofPred_eq] at hω ⊢
    have hmz : Measurable fun z => h (ω, z) := hhm.comp measurable_prodMk_left
    have := mul_meas_ge_le_lintegral (μ := ν) hmz a
    have hset : {z | a ≤ h (ω, z)} = {z | a ≤ ν {z' | ((ω, z), z') ∈ S}} := by
      ext z; simp only [mem_ofPred_eq, hh_eq]
    rw [hset] at this
    exact (by gcongr : a * b ≤ a * _).trans this
  -- `E G ≤ p ν(X)²`
  have hEG : ∫⁻ ω, G ω ∂P ≤ p * ν univ ^ 2 := by
    have h1 : ∫⁻ ω, G ω ∂P = ∫⁻ z, ∫⁻ ω, h (ω, z) ∂P ∂ν :=
      lintegral_lintegral_swap (f := fun ω z => h (ω, z)) hhm.aemeasurable
    have h2 : ∀ z, ∫⁻ ω, h (ω, z) ∂P ≤ p * ν univ := by
      intro z
      have hm2 : Measurable fun q : Ω × X => f ((q.1, z), q.2) :=
        hfm.comp (Measurable.prodMk (Measurable.prodMk measurable_fst measurable_const)
          measurable_snd)
      have hsw : ∫⁻ ω, h (ω, z) ∂P = ∫⁻ z', ∫⁻ ω, f ((ω, z), z') ∂P ∂ν :=
        lintegral_lintegral_swap (f := fun ω z' => f ((ω, z), z')) hm2.aemeasurable
      rw [hsw]
      have h3 : ∀ z', ∫⁻ ω, f ((ω, z), z') ∂P ≤ p := by
        intro z'
        have hsl : MeasurableSet {ω | ((ω, z), z') ∈ S} :=
          (Measurable.prodMk (Measurable.prodMk measurable_id measurable_const)
            measurable_const) hS
        have : ∫⁻ ω, f ((ω, z), z') ∂P = P {ω | ((ω, z), z') ∈ S} := by
          rw [← lintegral_indicator_one hsl]; rfl
        rw [this]; exact hp z z'
      calc ∫⁻ z', ∫⁻ ω, f ((ω, z), z') ∂P ∂ν ≤ ∫⁻ _z', p ∂ν := lintegral_mono h3
        _ = p * ν univ := lintegral_const p
    rw [h1]
    calc ∫⁻ z, ∫⁻ ω, h (ω, z) ∂P ∂ν ≤ ∫⁻ _z, p * ν univ ∂ν := lintegral_mono h2
      _ = p * ν univ ^ 2 := by rw [lintegral_const, mul_assoc, sq]
  calc a * b * P {ω | b ≤ ν {z | a ≤ ν {z' | ((ω, z), z') ∈ S}}}
      ≤ a * b * P {ω | a * b ≤ G ω} := by gcongr
    _ ≤ ∫⁻ ω, G ω ∂P := mul_meas_ge_le_lintegral hGm _
    _ ≤ p * ν univ ^ 2 := hEG

end DZZ
end LQGMetric
