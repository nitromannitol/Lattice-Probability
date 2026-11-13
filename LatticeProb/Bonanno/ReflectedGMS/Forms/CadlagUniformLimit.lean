/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.CadlagUniformLimit at commit fdb5cad; only the module paths of local imports are changed. -/
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.Order.Cadlag

/-!
# Locally uniform limits of real càdlàg paths

A locally uniform limit of càdlàg paths is càdlàg.  We then construct such a
limit from eventually geometric bounds on successive differences on every
natural time horizon.
-/

set_option autoImplicit false

open Filter Metric Set Topology
open scoped NNReal

namespace ReflectedGMS

/-- Uniform convergence on every bounded natural time horizon preserves the
càdlàg property for real paths on `ℝ≥0`. -/
theorem isCadlag_of_tendstoUniformlyOn_Icc_nat
    (fseq : ℕ → ℝ≥0 → ℝ) (f : ℝ≥0 → ℝ)
    (hcad : ∀ n, IsCadlag (fseq n))
    (hconv : ∀ T : ℕ,
      TendstoUniformlyOn fseq f atTop (Icc 0 (T : ℝ≥0))) :
    IsCadlag f := by
  constructor
  · intro t
    obtain ⟨T : ℕ, htT : (t : ℝ) < T⟩ := exists_nat_gt (t : ℝ)
    have htT' : t < (T : ℝ≥0) := by exact_mod_cast htT
    have hIcc : Icc (0 : ℝ≥0) (T : ℝ≥0) ∈ 𝓝[>] t := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htT')] with s hs
      exact ⟨bot_le, hs.le⟩
    have hlocal : TendstoUniformlyOnFilter fseq f atTop (𝓝[>] t) :=
      (hconv T).tendstoUniformlyOnFilter.mono_right (le_principal_iff.mpr hIcc)
    exact hlocal.tendsto_of_eventually_tendsto
      (Eventually.of_forall fun n => (hcad n).isRightContinuous t)
      ((hconv T).tendsto_at ⟨bot_le, htT'.le⟩)
  · intro t
    by_cases ht : t = 0
    · subst t
      exact ⟨f 0, by simp⟩
    obtain ⟨T : ℕ, htT : (t : ℝ) < T⟩ := exists_nat_gt (t : ℝ)
    have htT' : t < (T : ℝ≥0) := by exact_mod_cast htT
    have hIcc : Icc (0 : ℝ≥0) (T : ℝ≥0) ∈ 𝓝[<] t := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htT')] with s hs
      exact ⟨bot_le, hs.le⟩
    let lseq : ℕ → ℝ := fun n => (fseq n).leftLim t
    have hlt (n : ℕ) : Tendsto (fseq n) (𝓝[<] t) (𝓝 (lseq n)) :=
      (hcad n).tendsto_nhdsLT_leftLim t
    letI : NeBot (𝓝[<] t) := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.mpr ht⟩
    have hlcauchy : CauchySeq lseq := by
      rw [Metric.cauchySeq_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := Metric.uniformCauchySeqOn_iff.mp
        (hconv T).uniformCauchySeqOn (ε / 2) (half_pos hε)
      refine ⟨N, fun m hm n hn => ?_⟩
      have hdist : Tendsto (fun s => dist (fseq m s) (fseq n s)) (𝓝[<] t)
          (𝓝 (dist (lseq m) (lseq n))) := (hlt m).dist (hlt n)
      have hbound : ∀ᶠ s in 𝓝[<] t,
          dist (fseq m s) (fseq n s) ≤ ε / 2 := by
        filter_upwards [hIcc] with s hs
        exact (hN m hm n hn s hs).le
      exact lt_of_le_of_lt (le_of_tendsto hdist hbound) (half_lt_self hε)
    obtain ⟨l, hl⟩ := cauchySeq_tendsto_of_complete hlcauchy
    refine ⟨l, ?_⟩
    have hlocal : TendstoUniformlyOnFilter fseq f atTop (𝓝[<] t) :=
      (hconv T).tendstoUniformlyOnFilter.mono_right (le_principal_iff.mpr hIcc)
    exact hlocal.tendsto_of_eventually_tendsto
      (Eventually.of_forall hlt) hl

/-- The pointwise telescoping-series limit of a sequence of paths. -/
noncomputable def cadlagUniformLimit (fseq : ℕ → ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  fseq 0 t + ∑' n : ℕ, (fseq (n + 1) t - fseq n t)

/-- Eventually geometric successive-difference bounds give locally uniform
convergence to `cadlagUniformLimit`. -/
theorem tendstoUniformlyOn_cadlagUniformLimit
    (fseq : ℕ → ℝ≥0 → ℝ)
    (hgeom : ∀ T : ℕ, ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ≥0) (T : ℝ≥0),
      ‖fseq (n + 1) t - fseq n t‖ ≤ (1 / 2 : ℝ) ^ n)
    (T : ℕ) :
    TendstoUniformlyOn fseq (cadlagUniformLimit fseq) atTop
      (Icc 0 (T : ℝ≥0)) := by
  have hs := tendstoUniformlyOn_tsum_nat_eventually
    (f := fun n t => fseq (n + 1) t - fseq n t)
    (u := fun n => (1 / 2 : ℝ) ^ n) summable_geometric_two (hgeom T)
  rw [Metric.tendstoUniformlyOn_iff] at hs ⊢
  intro ε hε
  filter_upwards [hs ε hε] with N hN
  intro t ht
  rw [Finset.eq_sum_range_sub (fun n => fseq n t) N]
  simpa only [cadlagUniformLimit, dist_add_left] using hN t ht

/-- Càdlàg real paths whose successive differences are eventually bounded by
`(1/2)^n`, uniformly on every natural horizon, have a càdlàg locally uniform
limit. -/
theorem exists_cadlag_tendstoUniformlyOn_Icc_nat_of_geometric
    (fseq : ℕ → ℝ≥0 → ℝ)
    (hcad : ∀ n, IsCadlag (fseq n))
    (hgeom : ∀ T : ℕ, ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ≥0) (T : ℝ≥0),
      ‖fseq (n + 1) t - fseq n t‖ ≤ (1 / 2 : ℝ) ^ n) :
    ∃ f : ℝ≥0 → ℝ, IsCadlag f ∧
      ∀ T : ℕ, TendstoUniformlyOn fseq f atTop (Icc 0 (T : ℝ≥0)) := by
  refine ⟨cadlagUniformLimit fseq, ?_, tendstoUniformlyOn_cadlagUniformLimit fseq hgeom⟩
  exact isCadlag_of_tendstoUniformlyOn_Icc_nat fseq (cadlagUniformLimit fseq) hcad
    (tendstoUniformlyOn_cadlagUniformLimit fseq hgeom)

end ReflectedGMS
