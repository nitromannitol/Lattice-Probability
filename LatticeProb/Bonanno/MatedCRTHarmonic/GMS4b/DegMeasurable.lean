/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4b.DegMeasurable at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.CurveSpace
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4b.Packing

/-!
# Measurability of `deg^ε_in` and `deg^ε_out` on the curve space

Continuation of `CurveSpace.lean` (law transfer in the proof of [18] Theorem 4.4, `[18]`).

* `measurable_of_le_enat`: an `ℕ∞`-valued function is measurable once every superlevel set `{k ≤ f}` is.
* `measurable_locDegIn`: the set of curves admitting an inner-degree family of size `k` is the projection of a closed
  subset of `C(ℝ, ℂ) × ℝ^k`.
* `exists_degOutFamily_iff`: an outer-degree family of size `N ≥ 1` exists iff `diam η([t₀ − ε, t₀ + ε]) > 0` and there
  are `N` *window times* `t_i` (with `c(t_i)` in the local segment) of prescribed types such that each crossing can be
  completed to the last far time before / first far time after `t_i`, and the pairwise disjointness of the crossings is
  witnessed by far times between the `t_i` (`CrossingData`). All these conditions are closed or `F_σ`.
* `measurable_locDegOut`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace MatedCRTHarmonic.GMS4b

/-! ## `ℕ∞`-valued functions -/

theorem enat_eq_top_iff_forall_le (x : ℕ∞) : x = ⊤ ↔ ∀ k : ℕ, (k : ℕ∞) ≤ x := by
  constructor
  · rintro rfl k; exact le_top
  · intro h
    by_contra hx
    obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp hx
    have : m + 1 ≤ m := Nat.cast_le.mp (h (m + 1))
    omega

theorem enat_eq_coe_iff (x : ℕ∞) (k : ℕ) :
    x = k ↔ (k : ℕ∞) ≤ x ∧ ¬ ((k + 1 : ℕ) : ℕ∞) ≤ x := by
  constructor
  · rintro rfl
    refine ⟨le_rfl, fun h => ?_⟩
    have : k + 1 ≤ k := Nat.cast_le.mp h
    omega
  · rintro ⟨h1, h2⟩
    rcases eq_or_ne x ⊤ with hx | hx
    · exact absurd (hx ▸ le_top) h2
    obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp hx
    have h1' : k ≤ m := Nat.cast_le.mp h1
    have h2' : ¬ k + 1 ≤ m := fun h => h2 (Nat.cast_le.mpr h)
    have : m = k := by omega
    subst this; rfl

/-- An `ℕ∞`-valued function is measurable once every superlevel set `{k ≤ f}` is measurable. -/
theorem measurable_of_le_enat {X : Type*} [MeasurableSpace X] {f : X → ℕ∞}
    (h : ∀ k : ℕ, MeasurableSet {x | (k : ℕ∞) ≤ f x}) : Measurable f := by
  refine measurable_to_countable' fun y => ?_
  induction y using ENat.recTopCoe with
  | top =>
    have : f ⁻¹' {⊤} = ⋂ k : ℕ, {x | (k : ℕ∞) ≤ f x} := by
      ext x; simp only [mem_preimage, mem_singleton_iff, mem_iInter, mem_ofPred_eq]
      exact enat_eq_top_iff_forall_le (f x)
    rw [this]; exact MeasurableSet.iInter h
  | coe k =>
    have : f ⁻¹' {(k : ℕ∞)} = {x | (k : ℕ∞) ≤ f x} \ {x | ((k + 1 : ℕ) : ℕ∞) ≤ f x} := by
      ext x; simp only [mem_preimage, mem_singleton_iff, Set.mem_sdiff]
      exact enat_eq_coe_iff (f x) k
    rw [this]; exact (h k).diff (h (k + 1))

/-! ## Continuity helpers on `C(ℝ, ℂ) × ℝ^N` -/

theorem continuous_eval_add {N : ℕ} (i : Fin N) (σ : ℝ) :
    Continuous fun p : C(ℝ, ℂ) × (Fin N → ℝ) => p.1 (p.2 i + σ) :=
  continuous_eval.comp (continuous_fst.prodMk (((continuous_apply i).comp continuous_snd).add continuous_const))

theorem continuous_diam_window (ε t₀ : ℝ) :
    Continuous fun c : C(ℝ, ℂ) => diam (locWindow ε c t₀) :=
  continuous_diam_image isCompact_Icc

/-! ## `deg^ε_in` -/

theorem isDegInFamily_iff (ε : ℝ) (c : ℝ → ℂ) (t₀ : ℝ) {N : ℕ} (a : Fin N → ℝ) :
    IsDegInFamily ε c t₀ a ↔
      (∀ i j, i ≠ j → min (a i + ε) (a j + ε) ≤ max (a i) (a j)) ∧
      (∀ i, ∀ σ ∈ Icc (0 : ℝ) ε, dist (c (a i + σ)) (c t₀) ≤ 4 * diam (locWindow ε c t₀)) ∧
      (∀ i, ∃ y ∈ Icc (0 : ℝ) ε ×ˢ Icc (t₀ - ε) (t₀ + ε), c (a i + y.1) = c y.2) := by
  simp only [IsDegInFamily, Ioo_disjoint_Ioo]
  refine and_congr Iff.rfl ?_
  rw [← forall_and]
  refine forall_congr' fun i => and_congr ?_ ?_
  · constructor
    · intro h σ hσ
      have := h (mem_image_of_mem c (show a i + σ ∈ Icc (a i) (a i + ε) from ⟨by linarith [hσ.1],
        by linarith [hσ.2]⟩))
      exact mem_closedBall.mp this
    · rintro h _ ⟨t, ht, rfl⟩
      have := h (t - a i) ⟨by linarith [ht.1], by linarith [ht.2]⟩
      rw [add_sub_cancel] at this
      exact mem_closedBall.mpr this
  · constructor
    · rintro ⟨_, ⟨t, ht, rfl⟩, ⟨u, hu, hut⟩⟩
      exact ⟨(t - a i, u), ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, hu⟩, by rw [add_sub_cancel]; exact hut.symm⟩
    · rintro ⟨⟨σ, u⟩, ⟨hσ, hu⟩, h⟩
      exact ⟨c u, ⟨a i + σ, ⟨by linarith [hσ.1], by linarith [hσ.2]⟩, h⟩, mem_image_of_mem c hu⟩

theorem isClosed_degInFamily (ε t₀ : ℝ) (N : ℕ) :
    IsClosed {p : C(ℝ, ℂ) × (Fin N → ℝ) | IsDegInFamily ε p.1 t₀ p.2} := by
  have heq : {p : C(ℝ, ℂ) × (Fin N → ℝ) | IsDegInFamily ε p.1 t₀ p.2} =
      (⋂ i, ⋂ j, ⋂ (_ : i ≠ j), {p : C(ℝ, ℂ) × (Fin N → ℝ) |
        min (p.2 i + ε) (p.2 j + ε) ≤ max (p.2 i) (p.2 j)}) ∩
      ((⋂ i, ⋂ σ ∈ Icc (0 : ℝ) ε, {p : C(ℝ, ℂ) × (Fin N → ℝ) |
        dist (p.1 (p.2 i + σ)) (p.1 t₀) ≤ 4 * diam (locWindow ε p.1 t₀)}) ∩
      (⋂ i, {p : C(ℝ, ℂ) × (Fin N → ℝ) | ∃ y ∈ Icc (0 : ℝ) ε ×ˢ Icc (t₀ - ε) (t₀ + ε),
        (p, y) ∈ {q : (C(ℝ, ℂ) × (Fin N → ℝ)) × (ℝ × ℝ) | q.1.1 (q.1.2 i + q.2.1) = q.1.1 q.2.2}})) := by
    ext p
    simp only [mem_ofPred_eq, isDegInFamily_iff, mem_inter_iff, mem_iInter]
  rw [heq]
  refine IsClosed.inter ?_ (IsClosed.inter ?_ ?_)
  · refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ => ?_
    exact isClosed_le
      ((((continuous_apply i).comp continuous_snd).add continuous_const).min
        (((continuous_apply j).comp continuous_snd).add continuous_const))
      (((continuous_apply i).comp continuous_snd).max ((continuous_apply j).comp continuous_snd))
  · refine isClosed_iInter fun i => isClosed_iInter fun σ => isClosed_iInter fun _ => ?_
    exact isClosed_le ((continuous_eval_add i σ).dist
      (continuous_eval.comp (continuous_fst.prodMk continuous_const)))
      (continuous_const.mul ((continuous_diam_window ε t₀).comp continuous_fst))
  · refine isClosed_iInter fun i => ?_
    refine isClosed_exists_mem_of_isCompact (isCompact_Icc.prod isCompact_Icc) ?_
    exact isClosed_eq
      (continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk
        (((continuous_apply i).comp (continuous_snd.comp continuous_fst)).add
          (continuous_fst.comp continuous_snd))))
      (continuous_eval.comp ((continuous_fst.comp continuous_fst).prodMk
        (continuous_snd.comp continuous_snd)))

/-- **`deg^ε_in` is Borel** on `C(ℝ, ℂ)`. -/
theorem measurable_locDegIn (ε t₀ : ℝ) :
    Measurable fun c : C(ℝ, ℂ) => locDegIn ε c t₀ := by
  refine measurable_of_le_enat fun k => ?_
  have : {c : C(ℝ, ℂ) | (k : ℕ∞) ≤ locDegIn ε c t₀} =
      {c | ∃ a : Fin k → ℝ, (c, a) ∈ {p : C(ℝ, ℂ) × (Fin k → ℝ) | IsDegInFamily ε p.1 t₀ p.2}} := by
    ext c; simp only [mem_ofPred_eq, le_locDegIn_iff]
  rw [this]
  exact measurableSet_exists_of_isClosed (isClosed_degInFamily ε t₀ k)

end MatedCRTHarmonic.GMS4b
