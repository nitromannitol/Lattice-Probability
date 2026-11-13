/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS3.Lemma31 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS3.Cells

/-!
# GMS [18] Lemma 3.1, deterministic form with the corrected boundary term

Source: GMS [18] Lemma 3.1 ([18]), with the following boundary correction: the step
`∑_{x ∈ V(∂D)} diam(H_x)² ≤ area(B_{ε^q}(∂D))` of [18] (3.4) is false in general (squared diameter is not
bounded by area); the boundary cells are instead bounded by `∫ g u^ε` for a smoothed indicator `g` of a
neighbourhood of `∂D`, to which Proposition 2.10 applies.

The probabilistic inputs are hypotheses, never proved here:
* `CellDiamBound H ρ δ` is the event of [18] **Lemma 2.7** (every cell meeting `B_ρ(0)` has diameter
  `≤ δ = ε^q`);
* `Prop210Bound H D f A η` is the conclusion of [18] **Proposition 2.10** for one pair `(D, f)`
  (`∫_D f u^ε ≤ A ∫_D f + η`, `η = ε^α`), stated with lower Lebesgue integrals (`f ≥ 0`, `u^ε ≥ 0`).

Main results (for any reference points `p x ∈ H_x`; [18] (3.1) takes `p x = η(x)` for interior vertices
and a maximizer of `f` on `H_x ∩ ∂D` for boundary vertices, so `f^ε(x) = f(p x)`):
* `cellSum_le_lintegral` (the deterministic core of Lemma 3.1, no probabilistic input):
  `∑_{x ∈ V(D)} f(p x) diam(H_x)² deg(x) ≤ ∫_D f u + Lδ ∫_D u + M ∫_Ω g u`, where `f` is `L`-Lipschitz
  (one-sided) on `D`, `δ` bounds the diameters of the cells of `V(D)`, `M` bounds `f` at the reference
  points, and `g ≥ 1` on every boundary cell, which lies in `Ω`;
* `lemma31` (**[18] Lemma 3.1**, corrected): the same with the three Proposition 2.10 inputs
  `(D, f)`, `(D, 1)`, `(Ω, g)`;
* `cellSum_one_le` / `lemma31_one`: the case `f = 1`, the bound (3.19) used by Lemma 3.7.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal Classical

namespace MatedCRTHarmonic.GMS3

open LFMultigraph Harmonic

variable {V E : Type*} {G : LFMultigraph V E} {o : V} (H : CellularEmbedding G o)

/-- The event of **[18] Lemma 2.7**: every cell meeting `B_ρ(0)` has diameter at most `δ` (`δ = ε^q`). -/
def CellDiamBound (ρ δ : ℝ) : Prop :=
  ∀ x, (H.cell x ∩ ball (0 : ℂ) ρ).Nonempty → cellDiam H x ≤ δ

/-- The conclusion of **[18] Proposition 2.10** for one pair `(D, f)`: `∫_D f u^ε ≤ A ∫_D f + η`
(`η = ε^α`), with lower Lebesgue integrals. -/
def Prop210Bound (D : Set ℂ) (f : ℂ → ℝ) (A η : ℝ) : Prop :=
  (∫⁻ z in D, ENNReal.ofReal (f z) * uDens H z) ≤
    ENNReal.ofReal A * (∫⁻ z in D, ENNReal.ofReal (f z)) + ENNReal.ofReal η

/-- The interior vertices of `V(D)` (cells not meeting `∂D`) and the boundary vertices. -/
theorem sum_vFin_split (D : Set ℂ) (F : V → ℝ≥0∞) :
    ∑ x ∈ vFin H D, F x = ∑ x ∈ (vFin H D).filter (fun x => (H.cell x ∩ frontier D).Nonempty), F x +
      ∑ x ∈ (vFin H D).filter (fun x => ¬ (H.cell x ∩ frontier D).Nonempty), F x :=
  (Finset.sum_filter_add_sum_filter_not _ _ _).symm

/-- **Deterministic core of [18] Lemma 3.1** (with the boundary correction). -/
theorem cellSum_le_lintegral {D : Set ℂ} (hDo : IsOpen D) (hDb : Bornology.IsBounded D)
    (p : V → ℂ) (hp : ∀ x, p x ∈ H.cell x) {f : ℂ → ℝ} {L M δ : ℝ}
    (hLip : ∀ z ∈ D, ∀ w ∈ D, f z ≤ f w + L * dist z w) (hL : 0 ≤ L)
    (hδ : ∀ x ∈ vFin H D, cellDiam H x ≤ δ) (hM : ∀ x ∈ vFin H D, f (p x) ≤ M)
    {Ω : Set ℂ} {g : ℂ → ℝ}
    (hbd : ∀ x ∈ vFin H D, (H.cell x ∩ frontier D).Nonempty →
      H.cell x ⊆ Ω ∧ ∀ z ∈ H.cell x, 1 ≤ g z) :
    ∑ x ∈ vFin H D, ENNReal.ofReal (f (p x) * (cellDiam H x ^ 2 * G.deg x)) ≤
      (∫⁻ z in D, ENNReal.ofReal (f z) * uDens H z) +
        ENNReal.ofReal (L * δ) * (∫⁻ z in D, uDens H z) +
        ENNReal.ofReal M * (∫⁻ z in Ω, ENNReal.ofReal (g z) * uDens H z) := by
  set B := (vFin H D).filter (fun x => (H.cell x ∩ frontier D).Nonempty) with hB
  set I := (vFin H D).filter (fun x => ¬ (H.cell x ∩ frontier D).Nonempty) with hI
  have hc (x : V) : ENNReal.ofReal (f (p x) * (cellDiam H x ^ 2 * G.deg x)) ≤
      ENNReal.ofReal (f (p x)) * ∫⁻ z in H.cell x, uDens H z := by
    rw [setLIntegral_cell_uDens]
    by_cases hf : 0 ≤ f (p x)
    · rw [ENNReal.ofReal_mul hf]
    · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hf)
        (by positivity))]
      exact bot_le
  rw [sum_vFin_split H D]
  -- interior cells
  have hint : ∑ x ∈ I, ENNReal.ofReal (f (p x) * (cellDiam H x ^ 2 * G.deg x)) ≤
      (∫⁻ z in D, ENNReal.ofReal (f z) * uDens H z) +
        ENNReal.ofReal (L * δ) * (∫⁻ z in D, uDens H z) := by
    have hsub (x : V) (hx : x ∈ I) : H.cell x ⊆ D := by
      rw [hI, Finset.mem_filter] at hx
      refine cell_subset_of_inter_frontier_eq_empty H hDo ((mem_vFin H hDb).mp hx.1) ?_
      exact Set.not_nonempty_iff_eq_empty.mp hx.2
    calc ∑ x ∈ I, ENNReal.ofReal (f (p x) * (cellDiam H x ^ 2 * G.deg x))
        ≤ ∑ x ∈ I, ∫⁻ z in H.cell x, (ENNReal.ofReal (f z) * uDens H z +
            ENNReal.ofReal (L * δ) * uDens H z) := by
          refine Finset.sum_le_sum fun x hx => (hc x).trans ?_
          rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          refine setLIntegral_mono' (measurableSet_cell H x) fun z hz => ?_
          rw [← add_mul]
          gcongr ?_ * _
          have hxD : x ∈ vFin H D := (Finset.mem_filter.mp hx).1
          have h1 : f (p x) ≤ f z + L * δ := by
            refine (hLip _ (hsub x hx (hp x)) _ (hsub x hx hz)).trans ?_
            gcongr
            exact (dist_le_cellDiam H (hp x) hz).trans (hδ x hxD)
          exact (ENNReal.ofReal_le_ofReal h1).trans ENNReal.ofReal_add_le
      _ = ∫⁻ z in ⋃ x ∈ I, H.cell x, (ENNReal.ofReal (f z) * uDens H z +
            ENNReal.ofReal (L * δ) * uDens H z) := (setLIntegral_biUnion_cell H I _).symm
      _ ≤ ∫⁻ z in D, (ENNReal.ofReal (f z) * uDens H z + ENNReal.ofReal (L * δ) * uDens H z) :=
          lintegral_mono_set (Set.iUnion₂_subset fun x hx => hsub x hx)
      _ = (∫⁻ z in D, ENNReal.ofReal (f z) * uDens H z) +
            ENNReal.ofReal (L * δ) * (∫⁻ z in D, uDens H z) := by
          rw [lintegral_add_right _ ((measurable_uDens H).const_mul _),
            lintegral_const_mul _ (measurable_uDens H)]
  -- boundary cells
  have hbdry : ∑ x ∈ B, ENNReal.ofReal (f (p x) * (cellDiam H x ^ 2 * G.deg x)) ≤
      ENNReal.ofReal M * ∫⁻ z in Ω, ENNReal.ofReal (g z) * uDens H z := by
    calc ∑ x ∈ B, ENNReal.ofReal (f (p x) * (cellDiam H x ^ 2 * G.deg x))
        ≤ ∑ x ∈ B, ENNReal.ofReal M * ∫⁻ z in H.cell x, uDens H z := by
          refine Finset.sum_le_sum fun x hx => (hc x).trans ?_
          gcongr
          exact hM x (Finset.mem_filter.mp hx).1
      _ = ENNReal.ofReal M * ∫⁻ z in ⋃ x ∈ B, H.cell x, uDens H z := by
          rw [setLIntegral_biUnion_cell H B, Finset.mul_sum]
      _ ≤ ENNReal.ofReal M * ∫⁻ z in ⋃ x ∈ B, H.cell x, ENNReal.ofReal (g z) * uDens H z := by
          refine mul_le_mul' le_rfl ?_
          refine setLIntegral_mono' (Finset.measurableSet_biUnion _ fun x _ =>
            measurableSet_cell H x) fun z hz => ?_
          obtain ⟨x, hx, hzx⟩ := Set.mem_iUnion₂.mp hz
          have hx' := Finset.mem_filter.mp hx
          have hg1 := (hbd x hx'.1 hx'.2).2 z hzx
          calc uDens H z = 1 * uDens H z := (one_mul _).symm
            _ ≤ ENNReal.ofReal (g z) * uDens H z := by
                gcongr
                rw [← ENNReal.ofReal_one]
                exact ENNReal.ofReal_le_ofReal hg1
      _ ≤ ENNReal.ofReal M * ∫⁻ z in Ω, ENNReal.ofReal (g z) * uDens H z := by
          refine mul_le_mul' le_rfl ?_
          refine lintegral_mono_set (Set.iUnion₂_subset fun x hx => ?_)
          have hx' := Finset.mem_filter.mp hx
          exact (hbd x hx'.1 hx'.2).1
  calc ∑ x ∈ B, ENNReal.ofReal (f (p x) * (cellDiam H x ^ 2 * G.deg x)) +
        ∑ x ∈ I, ENNReal.ofReal (f (p x) * (cellDiam H x ^ 2 * G.deg x))
      ≤ ENNReal.ofReal M * (∫⁻ z in Ω, ENNReal.ofReal (g z) * uDens H z) +
          ((∫⁻ z in D, ENNReal.ofReal (f z) * uDens H z) +
            ENNReal.ofReal (L * δ) * (∫⁻ z in D, uDens H z)) := add_le_add hbdry hint
    _ = _ := by ring

/-- **[18] Lemma 3.1** (corrected boundary term), deterministic form: on the event where
The conclusions of Proposition 2.10 hold for `(D, f)`, `(D, 1)` and `(Ω, g)`,
`∑_{x ∈ V(D)} f^ε(x) diam(H_x)² deg(x) ≤ A ∫_D f + η + Lδ (A area(D) + η) + M (A ∫_Ω g + η)`. -/
theorem lemma31 {D : Set ℂ} (hDo : IsOpen D) (hDb : Bornology.IsBounded D)
    (p : V → ℂ) (hp : ∀ x, p x ∈ H.cell x) {f : ℂ → ℝ} {L M δ : ℝ}
    (hLip : ∀ z ∈ D, ∀ w ∈ D, f z ≤ f w + L * dist z w) (hL : 0 ≤ L)
    (hδ : ∀ x ∈ vFin H D, cellDiam H x ≤ δ) (hM : ∀ x ∈ vFin H D, f (p x) ≤ M)
    {Ω : Set ℂ} {g : ℂ → ℝ}
    (hbd : ∀ x ∈ vFin H D, (H.cell x ∩ frontier D).Nonempty →
      H.cell x ⊆ Ω ∧ ∀ z ∈ H.cell x, 1 ≤ g z)
    {A η : ℝ} (hf : Prop210Bound H D f A η) (h1 : Prop210Bound H D (fun _ => 1) A η)
    (hg : Prop210Bound H Ω g A η) :
    ∑ x ∈ vFin H D, ENNReal.ofReal (f (p x) * (cellDiam H x ^ 2 * G.deg x)) ≤
      (ENNReal.ofReal A * (∫⁻ z in D, ENNReal.ofReal (f z)) + ENNReal.ofReal η) +
        ENNReal.ofReal (L * δ) * (ENNReal.ofReal A * volume D + ENNReal.ofReal η) +
        ENNReal.ofReal M * (ENNReal.ofReal A * (∫⁻ z in Ω, ENNReal.ofReal (g z)) +
          ENNReal.ofReal η) := by
  refine (cellSum_le_lintegral H hDo hDb p hp hLip hL hδ hM hbd).trans ?_
  have h1' : (∫⁻ z in D, uDens H z) ≤ ENNReal.ofReal A * volume D + ENNReal.ofReal η := by
    have := h1
    unfold Prop210Bound at this
    simpa only [ENNReal.ofReal_one, one_mul, setLIntegral_const, Measure.restrict_apply_univ]
      using this
  gcongr
  · exact hf
  · exact hg

/-- The case `f = 1` of the deterministic core: `∑_{x ∈ V(D)} diam(H_x)² deg(x) ≤ ∫_D u + ∫_Ω g u`. -/
theorem cellSum_one_le {D : Set ℂ} (hDo : IsOpen D) (hDb : Bornology.IsBounded D)
    {Ω : Set ℂ} {g : ℂ → ℝ}
    (hbd : ∀ x ∈ vFin H D, (H.cell x ∩ frontier D).Nonempty →
      H.cell x ⊆ Ω ∧ ∀ z ∈ H.cell x, 1 ≤ g z) :
    ∑ x ∈ vFin H D, ENNReal.ofReal (cellDiam H x ^ 2 * G.deg x) ≤
      (∫⁻ z in D, uDens H z) + ∫⁻ z in Ω, ENNReal.ofReal (g z) * uDens H z := by
  have hp : ∀ x, Classical.choose (cell_nonempty H x) ∈ H.cell x :=
    fun x => Classical.choose_spec (cell_nonempty H x)
  have h := cellSum_le_lintegral H hDo hDb (fun x => Classical.choose (cell_nonempty H x)) hp
    (f := fun _ => 1) (L := 0) (M := 1) (δ := ∑ x ∈ vFin H D, cellDiam H x) (by intros; simp)
    le_rfl (fun x hx => Finset.single_le_sum (fun y _ => cellDiam_nonneg H y) hx)
    (fun _ _ => le_rfl) hbd
  simpa only [one_mul, ENNReal.ofReal_one, zero_mul, ENNReal.ofReal_zero, add_zero] using h

end MatedCRTHarmonic.GMS3
