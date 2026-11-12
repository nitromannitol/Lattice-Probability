/-
Copyright (c) 2026. All rights reserved.
-/
import Mathlib

/-!
# The local uniform metric on continuous paths

For a metric space `E` the space `C(ℝ≥0, E)` of continuous paths carries the compact-open
topology (topology of uniform convergence on compact sets).  Put
`pathSupDist T X Y = sup_{t ∈ [0,T]} dist (X t) (Y t)` and
`dUnif X Y = ∫_0^∞ min (exp (-T)) (pathSupDist T X Y) dT`.

* `LatticeProb.dUnif_le_one`: `0 ≤ dUnif X Y ≤ 1`.
* `LatticeProb.dUnif_self`, `dUnif_comm`, `dUnif_triangle`, `eq_of_dUnif_eq_zero`: `dUnif` is a
  metric.
* `LatticeProb.isOpen_iff_dUnif`, `tendsto_nhds_iff_dUnif`: it induces the compact-open topology.
* `LatticeProb.dUnifMetricSpace`: the resulting `MetricSpace C(ℝ≥0, E)`, whose underlying
  topology is the compact-open topology (by `rfl`).

Completeness and separability are not needed here.
-/

open Filter Topology Set MeasureTheory Metric

open scoped NNReal

noncomputable section

namespace LatticeProb

variable {E : Type*} [MetricSpace E]

/-- `sup_{t ∈ [0,T]} dist (X t) (Y t)` for continuous paths `X, Y : ℝ≥0 → E`. -/
def pathSupDist (T : ℝ≥0) (X Y : C(ℝ≥0, E)) : ℝ :=
  ⨆ t : Set.Icc (0 : ℝ≥0) T, dist (X t) (Y t)

lemma bddAbove_pathDist (T : ℝ≥0) (X Y : C(ℝ≥0, E)) :
    BddAbove (Set.range fun t : Set.Icc (0 : ℝ≥0) T => dist (X t) (Y t)) := by
  have hc : Continuous fun t : ℝ≥0 => dist (X t) (Y t) := X.continuous.dist Y.continuous
  have := ((isCompact_Icc (a := (0 : ℝ≥0)) (b := T)).image hc).bddAbove
  rwa [Set.image_eq_range] at this

lemma dist_le_pathSupDist {T t : ℝ≥0} (X Y : C(ℝ≥0, E)) (ht : t ≤ T) :
    dist (X t) (Y t) ≤ pathSupDist T X Y :=
  le_ciSup (f := fun t : Set.Icc (0 : ℝ≥0) T => dist (X t) (Y t)) (bddAbove_pathDist T X Y)
    ⟨t, ⟨zero_le, ht⟩⟩

lemma pathSupDist_le {T : ℝ≥0} {X Y : C(ℝ≥0, E)} {c : ℝ}
    (h : ∀ t ≤ T, dist (X t) (Y t) ≤ c) : pathSupDist T X Y ≤ c := by
  have : Nonempty (Set.Icc (0 : ℝ≥0) T) := ⟨⟨0, le_rfl, zero_le⟩⟩
  exact ciSup_le fun t => h t t.2.2

lemma pathSupDist_nonneg {T : ℝ≥0} (X Y : C(ℝ≥0, E)) : 0 ≤ pathSupDist T X Y :=
  (dist_nonneg).trans (dist_le_pathSupDist X Y (zero_le))

lemma pathSupDist_mono {S T : ℝ≥0} (h : S ≤ T) (X Y : C(ℝ≥0, E)) :
    pathSupDist S X Y ≤ pathSupDist T X Y :=
  pathSupDist_le fun _ ht => dist_le_pathSupDist X Y (ht.trans h)

lemma pathSupDist_comm (T : ℝ≥0) (X Y : C(ℝ≥0, E)) : pathSupDist T X Y = pathSupDist T Y X := by
  unfold pathSupDist
  simp_rw [dist_comm (X _)]

lemma pathSupDist_self (T : ℝ≥0) (X : C(ℝ≥0, E)) : pathSupDist T X X = 0 :=
  le_antisymm (pathSupDist_le fun t _ => by simp) (pathSupDist_nonneg X X)

lemma pathSupDist_triangle (T : ℝ≥0) (X Y Z : C(ℝ≥0, E)) :
    pathSupDist T X Z ≤ pathSupDist T X Y + pathSupDist T Y Z :=
  pathSupDist_le fun _ ht => (dist_triangle _ _ _).trans
    (add_le_add (dist_le_pathSupDist X Y ht) (dist_le_pathSupDist Y Z ht))

/-- The integrand `min (exp (-T)) (sup_{t ∈ [0,T]} dist (X t) (Y t))` of the local uniform metric. -/
def dUnifIntegrand (X Y : C(ℝ≥0, E)) (T : ℝ) : ℝ :=
  min (Real.exp (-T)) (pathSupDist T.toNNReal X Y)

lemma dUnifIntegrand_nonneg {X Y : C(ℝ≥0, E)} {T : ℝ} : 0 ≤ dUnifIntegrand X Y T :=
  le_min (Real.exp_pos _).le (pathSupDist_nonneg X Y)

lemma dUnifIntegrand_le_exp {X Y : C(ℝ≥0, E)} {T : ℝ} :
    dUnifIntegrand X Y T ≤ Real.exp (-T) := min_le_left _ _

lemma measurable_dUnifIntegrand (X Y : C(ℝ≥0, E)) : Measurable (dUnifIntegrand X Y) := by
  have hm : Monotone fun T : ℝ => pathSupDist T.toNNReal X Y :=
    fun a b h => pathSupDist_mono (Real.toNNReal_le_toNNReal h) X Y
  exact (Real.measurable_exp.comp measurable_neg).min hm.measurable

lemma integrableOn_dUnifIntegrand (X Y : C(ℝ≥0, E)) :
    IntegrableOn (dUnifIntegrand X Y) (Ioi 0) :=
  Integrable.mono' (integrableOn_exp_neg_Ioi 0) (measurable_dUnifIntegrand X Y).aestronglyMeasurable
    (ae_of_all _ fun _ => by
      rw [Real.norm_of_nonneg dUnifIntegrand_nonneg]; exact dUnifIntegrand_le_exp)

/-- The local uniform metric on continuous paths,
`dUnif X Y = ∫_0^∞ min (exp (-T)) (sup_{t ∈ [0,T]} dist (X t) (Y t)) dT`. -/
def dUnif (X Y : C(ℝ≥0, E)) : ℝ := ∫ T in Ioi (0 : ℝ), dUnifIntegrand X Y T

lemma dUnif_nonneg (X Y : C(ℝ≥0, E)) : 0 ≤ dUnif X Y :=
  integral_nonneg fun _ => dUnifIntegrand_nonneg

lemma dUnif_le_one (X Y : C(ℝ≥0, E)) : dUnif X Y ≤ 1 := by
  calc dUnif X Y ≤ ∫ T in Ioi (0 : ℝ), Real.exp (-T) :=
        setIntegral_mono_on (integrableOn_dUnifIntegrand X Y) (integrableOn_exp_neg_Ioi 0)
          measurableSet_Ioi fun _ _ => dUnifIntegrand_le_exp
    _ = 1 := integral_exp_neg_Ioi_zero

lemma dUnif_self (X : C(ℝ≥0, E)) : dUnif X X = 0 := by
  unfold dUnif dUnifIntegrand
  simp_rw [pathSupDist_self, min_eq_right (Real.exp_pos _).le]
  simp

lemma dUnif_comm (X Y : C(ℝ≥0, E)) : dUnif X Y = dUnif Y X := by
  unfold dUnif dUnifIntegrand
  simp_rw [pathSupDist_comm _ X Y]

lemma min_triangle_aux {e a b c : ℝ} (he : 0 ≤ e) (ha : 0 ≤ a) (hb : 0 ≤ b) (h : c ≤ a + b) :
    min e c ≤ min e a + min e b := by
  rcases le_total e a with h1 | h1
  · calc min e c ≤ e := min_le_left _ _
      _ = min e a := (min_eq_left h1).symm
      _ ≤ min e a + min e b := le_add_of_nonneg_right (le_min he hb)
  rcases le_total e b with h2 | h2
  · calc min e c ≤ e := min_le_left _ _
      _ = min e b := (min_eq_left h2).symm
      _ ≤ min e a + min e b := le_add_of_nonneg_left (le_min he ha)
  · rw [min_eq_right h1, min_eq_right h2]
    exact (min_le_right _ _).trans h

lemma dUnif_triangle (X Y Z : C(ℝ≥0, E)) : dUnif X Z ≤ dUnif X Y + dUnif Y Z := by
  unfold dUnif
  rw [← integral_add (integrableOn_dUnifIntegrand X Y) (integrableOn_dUnifIntegrand Y Z)]
  refine setIntegral_mono_on (integrableOn_dUnifIntegrand X Z)
    ((integrableOn_dUnifIntegrand X Y).add (integrableOn_dUnifIntegrand Y Z))
    measurableSet_Ioi fun T _ => ?_
  exact min_triangle_aux (Real.exp_pos _).le (pathSupDist_nonneg X Y) (pathSupDist_nonneg Y Z)
    (pathSupDist_triangle _ X Y Z)

theorem eq_of_dUnif_eq_zero {X Y : C(ℝ≥0, E)} (h : dUnif X Y = 0) : X = Y := by
  have h0 := (integral_eq_zero_iff_of_nonneg (fun _ => dUnifIntegrand_nonneg)
    (integrableOn_dUnifIntegrand X Y)).1 h
  ext t
  have ht : (0 : ℝ) ≤ t := t.2
  have hle : (volume.restrict (Ioi (t : ℝ))) ≤ volume.restrict (Ioi (0 : ℝ)) :=
    Measure.restrict_mono (Ioi_subset_Ioi ht) le_rfl
  have : (ae (volume.restrict (Ioi (t : ℝ)))).NeBot := ae_restrict_neBot.2 (by simp)
  obtain ⟨T, hT, hTt⟩ := ((h0.filter_mono (ae_mono hle)).and
    (ae_restrict_mem measurableSet_Ioi)).exists
  have hT' : dUnifIntegrand X Y T = 0 := hT
  have hs : pathSupDist T.toNNReal X Y ≤ 0 := by
    by_contra hc
    have hc := not_le.1 hc
    have : 0 < dUnifIntegrand X Y T := lt_min (Real.exp_pos _) hc
    linarith
  have h1 : dist (X t) (Y t) ≤ 0 :=
    (dist_le_pathSupDist X Y ((Real.le_toNNReal_iff_coe_le (by linarith [mem_Ioi.1 hTt])).2
      (mem_Ioi.1 hTt).le)).trans hs
  exact dist_le_zero.1 h1

/-- If `dUnif X Y` is small, the paths are uniformly close on `[0, T0]`. -/
lemma pathSupDist_lt_of_dUnif_lt {X Y : C(ℝ≥0, E)} (T0 : ℝ≥0) {δ : ℝ}
    (h : dUnif X Y < min (Real.exp (-((T0 : ℝ) + 1))) δ) : pathSupDist T0 X Y < δ := by
  by_contra hcon
  have hcon := not_lt.1 hcon
  have hlow : ∀ T ∈ Ioc (T0 : ℝ) ((T0 : ℝ) + 1),
      min (Real.exp (-((T0 : ℝ) + 1))) δ ≤ dUnifIntegrand X Y T := by
    intro T hT
    refine le_min ((min_le_left _ _).trans (Real.exp_le_exp.2 (by linarith [hT.2]))) ?_
    exact (min_le_right _ _).trans (hcon.trans (pathSupDist_mono
      ((Real.le_toNNReal_iff_coe_le (by linarith [hT.1, T0.2])).2 hT.1.le) X Y))
  have hsub : Ioc (T0 : ℝ) ((T0 : ℝ) + 1) ⊆ Ioi (0 : ℝ) :=
    Ioc_subset_Ioi_self.trans (Ioi_subset_Ioi T0.2)
  have h2 := setIntegral_ge_of_const_le (μ := volume) measurableSet_Ioc (by simp) hlow
    ((integrableOn_dUnifIntegrand X Y).mono_set hsub)
  have h3 : ∫ T in Ioc (T0 : ℝ) ((T0 : ℝ) + 1), dUnifIntegrand X Y T ≤ dUnif X Y :=
    setIntegral_mono_set (integrableOn_dUnifIntegrand X Y)
      (ae_of_all _ fun _ => dUnifIntegrand_nonneg) hsub.eventuallyLE
  have hv : volume.real (Ioc (T0 : ℝ) ((T0 : ℝ) + 1)) = 1 := by simp [Measure.real]
  rw [hv, one_smul] at h2
  linarith

/-- If the paths are `δ`-close on `[0, T0]`, then `dUnif X Y ≤ T0 δ + exp (-T0)`. -/
lemma dUnif_le_of_forall_dist_le {X Y : C(ℝ≥0, E)} (T0 : ℝ≥0) {δ : ℝ}
    (h : ∀ t ≤ T0, dist (X t) (Y t) ≤ δ) : dUnif X Y ≤ T0 * δ + Real.exp (-(T0 : ℝ)) := by
  have hI := integrableOn_dUnifIntegrand X Y
  have hI1 : IntegrableOn (dUnifIntegrand X Y) (Ioc 0 (T0 : ℝ)) := hI.mono_set Ioc_subset_Ioi_self
  have hI2 : IntegrableOn (dUnifIntegrand X Y) (Ioi (T0 : ℝ)) := hI.mono_set (Ioi_subset_Ioi T0.2)
  have hsplit : Ioc (0 : ℝ) T0 ∪ Ioi (T0 : ℝ) = Ioi 0 := Ioc_union_Ioi_eq_Ioi T0.2
  have b1 : ∫ T in Ioc (0 : ℝ) T0, dUnifIntegrand X Y T ≤ ∫ _ in Ioc (0 : ℝ) T0, δ :=
    setIntegral_mono_on hI1 (integrableOn_const (by simp)) measurableSet_Ioc fun T hT =>
      (min_le_right _ _).trans (pathSupDist_le fun t ht =>
        h t (ht.trans (Real.toNNReal_le_iff_le_coe.2 hT.2)))
  have b2 : ∫ T in Ioi (T0 : ℝ), dUnifIntegrand X Y T ≤ ∫ T in Ioi (T0 : ℝ), Real.exp (-T) :=
    setIntegral_mono_on hI2 (integrableOn_exp_neg_Ioi _) measurableSet_Ioi fun _ _ =>
      dUnifIntegrand_le_exp
  have e1 : ∫ _ in Ioc (0 : ℝ) T0, δ = T0 * δ := by simp [Measure.real]
  unfold dUnif
  rw [← hsplit, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hI1 hI2]
  rw [integral_exp_neg_Ioi] at b2
  linarith

/-- Neighbourhoods in the compact-open topology are described by `dUnif`-balls. -/
theorem mem_nhds_iff_dUnif (X : C(ℝ≥0, E)) (s : Set C(ℝ≥0, E)) :
    s ∈ 𝓝 X ↔ ∃ ε > 0, ∀ Y, dUnif X Y < ε → Y ∈ s := by
  rw [mem_nhds_uniformity_iff_right, ContinuousMap.hasBasis_compactConvergenceUniformity.mem_iff]
  constructor
  · rintro ⟨⟨K, V⟩, ⟨hK, hV⟩, hsub⟩
    obtain ⟨δ, hδ, hδV⟩ := Metric.mem_uniformity_dist.1 hV
    obtain ⟨T0, hT0⟩ := hK.bddAbove
    refine ⟨min (Real.exp (-((T0 : ℝ) + 1))) δ, lt_min (Real.exp_pos _) hδ, fun Y hY => ?_⟩
    have hlt := pathSupDist_lt_of_dUnif_lt T0 hY
    have := @hsub (X, Y) (fun t ht => hδV
      (lt_of_le_of_lt (dist_le_pathSupDist X Y (hT0 ht)) hlt))
    exact this rfl
  · rintro ⟨ε, hε, hball⟩
    obtain ⟨n, hn⟩ := exists_nat_gt (-Real.log (ε / 2))
    have hexp : Real.exp (-(n : ℝ)) < ε / 2 := by
      calc Real.exp (-(n : ℝ)) < Real.exp (Real.log (ε / 2)) :=
            Real.exp_lt_exp.2 (by linarith)
        _ = ε / 2 := Real.exp_log (by positivity)
    have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    set δ : ℝ := ε / (2 * ((n : ℝ) + 1)) with hδ
    have hδpos : 0 < δ := by positivity
    refine ⟨⟨Set.Icc 0 (n : ℝ≥0), {p | dist p.1 p.2 < δ}⟩,
      ⟨isCompact_Icc, Metric.dist_mem_uniformity hδpos⟩, ?_⟩
    rintro ⟨X', Y⟩ hXY rfl
    refine hball Y ?_
    have hle := dUnif_le_of_forall_dist_le (X := X') (Y := Y) (n : ℝ≥0) (δ := δ)
      fun t ht => (hXY t ⟨zero_le, ht⟩).le
    have hnd : (n : ℝ) * δ ≤ ε / 2 := by
      rw [hδ, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    simp only [NNReal.coe_natCast] at hle
    linarith

theorem isOpen_iff_dUnif (s : Set C(ℝ≥0, E)) :
    IsOpen s ↔ ∀ X ∈ s, ∃ ε > 0, ∀ Y, dUnif X Y < ε → Y ∈ s := by
  rw [isOpen_iff_mem_nhds]
  exact forall₂_congr fun X _ => mem_nhds_iff_dUnif X s

/-- Convergence in the compact-open topology (local uniform convergence of paths) is
convergence in `dUnif`. -/
theorem tendsto_nhds_iff_dUnif {ι : Type*} {l : Filter ι} {F : ι → C(ℝ≥0, E)} {X : C(ℝ≥0, E)} :
    Tendsto F l (𝓝 X) ↔ ∀ ε > 0, ∀ᶠ i in l, dUnif X (F i) < ε := by
  constructor
  · intro h ε hε
    exact h ((mem_nhds_iff_dUnif X {Y | dUnif X Y < ε}).2 ⟨ε, hε, fun _ hY => hY⟩)
  · intro h
    rw [tendsto_def]
    intro s hs
    obtain ⟨ε, hε, hball⟩ := (mem_nhds_iff_dUnif X s).1 hs
    exact (h ε hε).mono fun i hi => hball _ hi

/-- `dUnif` is a metric on `C(ℝ≥0, E)`; its topology is the compact-open topology. -/
@[instance_reducible]
def dUnifMetricSpace : MetricSpace C(ℝ≥0, E) :=
  { PseudoMetricSpace.ofDistTopology dUnif dUnif_self dUnif_comm dUnif_triangle
      isOpen_iff_dUnif with
    eq_of_dist_eq_zero := fun h => eq_of_dUnif_eq_zero h }

theorem dUnifMetricSpace_dist (X Y : C(ℝ≥0, E)) :
    @dist _ (dUnifMetricSpace (E := E)).toDist X Y = dUnif X Y := rfl

theorem dUnifMetricSpace_topology :
    (dUnifMetricSpace (E := E)).toUniformSpace.toTopologicalSpace =
      (ContinuousMap.compactOpen : TopologicalSpace C(ℝ≥0, E)) := rfl

end LatticeProb
