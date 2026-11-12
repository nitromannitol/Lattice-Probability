/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Gaussian.SupTailField at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.LQGMetric.Gaussian.SupTailBorell
import Mathlib.Topology.Bases
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Suprema of continuous Gaussian fields on compact index spaces (F.GTAIL)

For a centered Gaussian process `X : T → Ω → ℝ` with continuous sample paths on a compact
separable space `T`:

* `iSup_eq_iSup_denseSeq`: the supremum over `T` is the supremum along a dense sequence;
* `integrable_iSup_of_continuous`: uniform bounds `E max_{i ≤ n} X (t i) ≤ C` over all finite
  families give `sup_T X` integrable with `E sup_T X ≤ C`;
* `borellTIS_iSup_continuous`: **Borell–TIS** `P(sup_T X - E sup_T X ≥ u) ≤ exp (-u²/(2σ²))`,
  `σ² ≥ sup_T Var X`;
* `tail_iSup_le` / `tail_iSup_abs_le`: **uniform `E sup` + bounded variance ⇒ Gaussian tail**:
  if `E sup_T X ≤ M` then `P(sup_T X ≥ M + u) ≤ exp (-u²/(2σ²))`, and if moreover
  `E sup_T (-X) ≤ M` then `P(sup_T |X| ≥ M + u) ≤ 2 exp (-u²/(2σ²))`.

Source: Adler–Taylor, *Random Fields and Geometry*, Thm 2.1.1 (p. 50) and the separability
reduction in its proof (p. 57); the tail forms are the "immediate consequence" of (2.1.5) on p. 50.
The reduction from `T` to a dense sequence uses only continuity of the paths.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter Topology TopologicalSpace

namespace LQGMetric

namespace SupTail

/-- For a continuous bounded function, the supremum equals the supremum along a dense
sequence. -/
lemma iSup_eq_iSup_denseSeq {T : Type*} [TopologicalSpace T] {f : T → ℝ} (hf : Continuous f)
    {u : ℕ → T} (hu : DenseRange u) (hb : BddAbove (range f)) :
    ⨆ t, f t = ⨆ k, f (u k) := by
  have : Nonempty T := ⟨u 0⟩
  have hbu : BddAbove (range fun k => f (u k)) := hb.mono (range_comp_subset_range u f)
  refine le_antisymm (ciSup_le fun t => ?_) (ciSup_le fun k => le_ciSup hb _)
  have hcl : f t ∈ closure (range fun k => f (u k)) := by
    have h1 : f t ∈ f '' closure (range u) := ⟨t, hu.closure_eq ▸ mem_univ t, rfl⟩
    have h2 := image_closure_subset_closure_image (s := range u) hf h1
    rwa [← range_comp] at h2
  exact closure_minimal (by rintro _ ⟨k, rfl⟩; exact le_ciSup hbu k) isClosed_Iic hcl

variable {Ω T : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [TopologicalSpace T] [CompactSpace T] [SeparableSpace T] [Nonempty T]
  {X : T → Ω → ℝ}

omit [MeasurableSpace Ω] [SeparableSpace T] [Nonempty T] in
lemma bddAbove_range_of_continuous (hc : ∀ ω, Continuous fun t => X t ω) (ω : Ω) :
    BddAbove (range fun t => X t ω) :=
  (isCompact_range (hc ω)).bddAbove

omit [MeasurableSpace Ω] [SeparableSpace T] [Nonempty T] in
/-- The supremum of a continuous field along a dense sequence. -/
lemma iSup_eq_iSup_seq (hc : ∀ ω, Continuous fun t => X t ω) {u : ℕ → T} (hu : DenseRange u)
    (ω : Ω) : ⨆ t, X t ω = ⨆ k, X (u k) ω :=
  iSup_eq_iSup_denseSeq (hc ω) hu (bddAbove_range_of_continuous hc ω)

/-- **`E sup` of a continuous Gaussian field from uniform bounds on finite maxima.** -/
theorem integrable_iSup_of_continuous (hX : IsGaussianProcess X P)
    (hc : ∀ ω, Continuous fun t => X t ω) {C : ℝ}
    (hfin : ∀ (n : ℕ) (t : Fin (n + 1) → T), ∫ ω, (⨆ i, X (t i) ω) ∂P ≤ C) :
    Integrable (fun ω => ⨆ t, X t ω) P ∧ ∫ ω, (⨆ t, X t ω) ∂P ≤ C := by
  obtain ⟨u, hu⟩ := exists_dense_seq T
  have hb : ∀ ω, BddAbove (range fun k => X (u k) ω) := fun ω =>
    (bddAbove_range_of_continuous hc ω).mono (by rintro _ ⟨k, rfl⟩; exact ⟨u k, rfl⟩)
  have h := integrable_iSup_of_seqMax (u := u) hX hb (C := C) fun n => hfin n (fun i => u i)
  simp_rw [iSup_eq_iSup_seq hc hu]
  exact h

/-- **Borell–TIS inequality for a continuous centered Gaussian field on a compact separable
space** (Adler–Taylor, Thm 2.1.1): if `sup_T X` is integrable and `Var X t ≤ σ²` for all `t`,
then for `u ≥ 0`, `P(sup_T X - E sup_T X ≥ u) ≤ exp (-u² / (2σ²))`. -/
theorem borellTIS_iSup_continuous (hX : IsGaussianProcess X P) (h0 : ∀ t, ∫ ω, X t ω ∂P = 0)
    (hc : ∀ ω, Continuous fun t => X t ω) (hint : Integrable (fun ω => ⨆ t, X t ω) P)
    {σ : ℝ} (hvar : ∀ t, Var[X t; P] ≤ σ ^ 2) {u : ℝ} (hu : 0 ≤ u) :
    P.real {ω | u ≤ (⨆ t, X t ω) - ∫ ω', (⨆ t, X t ω') ∂P} ≤ exp (-u ^ 2 / (2 * σ ^ 2)) := by
  obtain ⟨v, hv⟩ := exists_dense_seq T
  have hb : ∀ ω, BddAbove (range fun k => X (v k) ω) := fun ω =>
    (bddAbove_range_of_continuous hc ω).mono (by rintro _ ⟨k, rfl⟩; exact ⟨v k, rfl⟩)
  have hC : ∀ n, ∫ ω, seqMax X v n ω ∂P ≤ ∫ ω, (⨆ t, X t ω) ∂P := fun n =>
    integral_mono (integrable_seqMax hX n) hint fun ω =>
      (seqMax_le_iSup (hb ω) n).trans (iSup_eq_iSup_seq hc hv ω).ge
  have h := borellTIS_iSup_seq hX h0 hb hC (fun k => hvar (v k)) hu
  simp_rw [iSup_eq_iSup_seq hc hv]
  exact h

/-- **Uniform `E sup` and bounded variance give a Gaussian tail**: if `E sup_T X ≤ M` and
`Var X t ≤ σ²`, then `P(sup_T X ≥ M + u) ≤ exp (-u² / (2σ²))` for `u ≥ 0`. -/
theorem tail_iSup_le (hX : IsGaussianProcess X P) (h0 : ∀ t, ∫ ω, X t ω ∂P = 0)
    (hc : ∀ ω, Continuous fun t => X t ω) (hint : Integrable (fun ω => ⨆ t, X t ω) P)
    {M : ℝ} (hM : ∫ ω, (⨆ t, X t ω) ∂P ≤ M) {σ : ℝ} (hvar : ∀ t, Var[X t; P] ≤ σ ^ 2)
    {u : ℝ} (hu : 0 ≤ u) :
    P.real {ω | M + u ≤ ⨆ t, X t ω} ≤ exp (-u ^ 2 / (2 * σ ^ 2)) := by
  have hP := hX.isProbabilityMeasure
  refine (measureReal_mono (fun ω (hω : M + u ≤ ⨆ t, X t ω) => (by linarith :
    u ≤ (⨆ t, X t ω) - ∫ ω', (⨆ t, X t ω') ∂P))).trans
    (borellTIS_iSup_continuous hX h0 hc hint hvar hu)

omit [TopologicalSpace T] [CompactSpace T] [SeparableSpace T] [Nonempty T] in
/-- The negative of a centered Gaussian process is a centered Gaussian process. -/
lemma isGaussianProcess_neg (hX : IsGaussianProcess X P) :
    IsGaussianProcess (fun t ω => -X t ω) P := by
  have h := hX.smul (fun _ => (-1 : ℝ))
  have e : (fun t ω => (-1 : ℝ) • X t ω) = fun t ω => -X t ω := by
    funext t ω; simp
  rwa [e] at h

/-- **Two-sided form**: if `E sup_T X ≤ M`, `E sup_T (-X) ≤ M` and `Var X t ≤ σ²`, then
`P(sup_T |X| ≥ M + u) ≤ 2 exp (-u² / (2σ²))` for `u ≥ 0`. -/
theorem tail_iSup_abs_le (hX : IsGaussianProcess X P) (h0 : ∀ t, ∫ ω, X t ω ∂P = 0)
    (hc : ∀ ω, Continuous fun t => X t ω) (hint : Integrable (fun ω => ⨆ t, X t ω) P)
    (hint' : Integrable (fun ω => ⨆ t, -X t ω) P) {M : ℝ}
    (hM : ∫ ω, (⨆ t, X t ω) ∂P ≤ M) (hM' : ∫ ω, (⨆ t, -X t ω) ∂P ≤ M) {σ : ℝ}
    (hvar : ∀ t, Var[X t; P] ≤ σ ^ 2) {u : ℝ} (hu : 0 ≤ u) :
    P.real {ω | M + u ≤ ⨆ t, |X t ω|} ≤ 2 * exp (-u ^ 2 / (2 * σ ^ 2)) := by
  have hP := hX.isProbabilityMeasure
  have h1 := tail_iSup_le hX h0 hc hint hM hvar hu
  have h2 := tail_iSup_le (X := fun t ω => -X t ω) (isGaussianProcess_neg hX)
    (fun t => by simp [integral_neg, h0]) (fun ω => (hc ω).neg) hint' hM'
    (fun t => by rw [variance_fun_neg]; exact hvar t) hu
  have hsub : {ω | M + u ≤ ⨆ t, |X t ω|} ⊆
      {ω | M + u ≤ ⨆ t, X t ω} ∪ {ω | M + u ≤ ⨆ t, -X t ω} := by
    intro ω hω
    by_contra hn
    simp only [mem_union, mem_ofPred_eq, not_or, not_le] at hn
    have hle : ⨆ t, |X t ω| ≤ max (⨆ t, X t ω) (⨆ t, -X t ω) :=
      ciSup_le fun t => by
        rw [abs_eq_max_neg]
        exact max_le_max (le_ciSup (bddAbove_range_of_continuous hc ω) t)
          (le_ciSup (bddAbove_range_of_continuous (X := fun t ω => -X t ω)
            (fun ω => (hc ω).neg) ω) t)
    have := lt_of_le_of_lt hle (max_lt hn.1 hn.2)
    exact absurd hω (not_le.2 this)
  calc P.real {ω | M + u ≤ ⨆ t, |X t ω|}
      ≤ P.real {ω | M + u ≤ ⨆ t, X t ω} + P.real {ω | M + u ≤ ⨆ t, -X t ω} :=
        (measureReal_mono hsub).trans (measureReal_union_le _ _)
    _ ≤ 2 * exp (-u ^ 2 / (2 * σ ^ 2)) := by linarith

/-- **Gaussian tail with a prefactor** (the form of DDDF (2.16)): if `E sup_T X ≤ M`,
`E sup_T (-X) ≤ M` and `Var X t ≤ σ²`, then for every `x ≥ 0`,
`P(sup_T |X| ≥ x) ≤ 2 exp (M² / (2σ²)) · exp (-x² / (2 · (2σ²)))`. Own elementary step from
`tail_iSup_abs_le`: `(x - M)² ≥ x²/2 - M²`. -/
theorem tail_iSup_abs_le_gaussian (hX : IsGaussianProcess X P) (h0 : ∀ t, ∫ ω, X t ω ∂P = 0)
    (hc : ∀ ω, Continuous fun t => X t ω) (hint : Integrable (fun ω => ⨆ t, X t ω) P)
    (hint' : Integrable (fun ω => ⨆ t, -X t ω) P) {M : ℝ}
    (hM : ∫ ω, (⨆ t, X t ω) ∂P ≤ M) (hM' : ∫ ω, (⨆ t, -X t ω) ∂P ≤ M) {σ : ℝ}
    (hvar : ∀ t, Var[X t; P] ≤ σ ^ 2) {x : ℝ} (hx : 0 ≤ x) :
    P.real {ω | x ≤ ⨆ t, |X t ω|} ≤
      2 * exp (M ^ 2 / (2 * σ ^ 2)) * exp (-x ^ 2 / (2 * (2 * σ ^ 2))) := by
  have hP := hX.isProbabilityMeasure
  have hM0 : 0 ≤ M := by
    obtain ⟨t₀⟩ := (inferInstance : Nonempty T)
    refine le_trans ?_ hM
    rw [← h0 t₀]
    exact integral_mono (hX.hasGaussianLaw_eval t₀).integrable hint fun ω =>
      le_ciSup (bddAbove_range_of_continuous hc ω) t₀
  rw [mul_assoc, ← exp_add]
  rcases le_or_gt M x with hMx | hxM
  · have h := tail_iSup_abs_le hX h0 hc hint hint' hM hM' hvar (sub_nonneg.2 hMx)
    rw [add_sub_cancel] at h
    refine h.trans (mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) (by norm_num))
    have e : M ^ 2 / (2 * σ ^ 2) + -x ^ 2 / (2 * (2 * σ ^ 2)) =
        (M ^ 2 - x ^ 2 / 2) / (2 * σ ^ 2) := by ring
    rw [e, neg_div]
    rw [← neg_div]
    exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (x - 2 * M)]) (by positivity)
  · refine measureReal_le_one.trans ?_
    have h1 : 1 ≤ exp (M ^ 2 / (2 * σ ^ 2) + -x ^ 2 / (2 * (2 * σ ^ 2))) := by
      refine one_le_exp ?_
      have e : M ^ 2 / (2 * σ ^ 2) + -x ^ 2 / (2 * (2 * σ ^ 2)) =
          (M ^ 2 - x ^ 2 / 2) / (2 * σ ^ 2) := by ring
      rw [e]
      exact div_nonneg (by nlinarith) (by positivity)
    linarith

end SupTail

end LQGMetric
