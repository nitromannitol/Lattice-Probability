/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.MoTInput.CurveGeometry at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted.
   Imports of copied modules that this file does not need are replaced by their own imports. -/
import Mathlib
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTPath2
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.MatedCRTField
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.IsMatingOfTreesCoupling
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.CellAdjacency
import LatticeProb.Bonanno.MatedCRTHarmonic.MoTInput.CurveAdapters
import LatticeProb.Bonanno.MatedCRTHarmonic.Frozen.CellularEmbedding
import LatticeProb.Bonanno.MatedCRTHarmonic.GMSLemma27.Bookkeeping
import LatticeProb.Bonanno.MatedCRTHarmonic.CellFamily.Interfaces
import LatticeProb.Bonanno.MatedCRTHarmonic.MatedCRT.LocalFiniteness

/-!
# Euclidean geometry forced by the area parametrization

The Lebesgue clock of `ηL`, together with the increasing order-isomorphism in `areaParam`,
determines Euclidean volumes of every curve interval. These lemmas give null overlaps of distinct
integer-time cells without assuming a cell-configuration theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric
open scoped Topology NNReal ENNReal

namespace MatedCRTHarmonic.MoTInput

open MatedCRTHarmonic.MatedCRT

private theorem image_reparam_Icc {φ : ℝ ≃o ℝ} {ηL η : C(ℝ, ℂ)}
    (hη : ∀ t, η t = ηL (φ t)) (a b : ℝ) :
    η '' Icc a b = ηL '' Icc (φ a) (φ b) := by
  rw [show (η : ℝ → ℂ) = (ηL : ℝ → ℂ) ∘ φ from funext hη, Set.image_comp, φ.image_Icc]

/-- The Euclidean volume of a segment of the area-parametrized curve is its Lebesgue-time length
after applying the increasing time change. -/
theorem volume_curve_interval_reparam {φ : ℝ ≃o ℝ} {ηL η : C(ℝ, ℂ)}
    (hη : ∀ t, η t = ηL (φ t))
    (hvol : ∀ s t : ℝ, s ≤ t → volume (ηL '' Icc s t) = ENNReal.ofReal (t - s))
    {a b : ℝ} (hab : a ≤ b) :
    volume (η '' Icc a b) = ENNReal.ofReal (φ b - φ a) := by
  rw [image_reparam_Icc hη]
  exact hvol (φ a) (φ b) (φ.monotone hab)

private theorem interval_image_union {f : ℝ → ℂ} {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b) :
    f '' Icc a c ∪ f '' Icc c b = f '' Icc a b := by
  rw [← Set.image_union]
  congr 1
  ext t
  simp only [mem_union, mem_Icc]
  constructor
  · rintro (⟨ha, hc⟩ | ⟨hc, hb⟩)
    · exact ⟨ha, hc.trans hcb⟩
    · exact ⟨hac.trans hc, hb⟩
  · rintro ⟨ha, hb⟩
    rcases le_total t c with htc | hct
    · exact Or.inl ⟨ha, htc⟩
    · exact Or.inr ⟨hct, hb⟩

private theorem volume_inter_separated_cell_zero
    {φ : ℝ ≃o ℝ} {ηL η : C(ℝ, ℂ)}
    (hη : ∀ t, η t = ηL (φ t))
    (hvol : ∀ s t : ℝ, s ≤ t → volume (ηL '' Icc s t) = ENNReal.ofReal (t - s))
    {x y : ℤ} (hxy : x < y) :
    volume ((η '' Icc ((x : ℝ) - 1) x) ∩ (η '' Icc ((y : ℝ) - 1) y)) = 0 := by
  let A : Set ℂ := η '' Icc ((x : ℝ) - 1) ((y : ℝ) - 1)
  let B : Set ℂ := η '' Icc ((y : ℝ) - 1) y
  have hxyR : (x : ℝ) ≤ (y : ℝ) - 1 := by
    exact_mod_cast (show x ≤ y - 1 by omega)
  have hAvol : volume A = ENNReal.ofReal (φ ((y : ℝ) - 1) - φ ((x : ℝ) - 1)) := by
    dsimp [A]
    exact volume_curve_interval_reparam hη hvol (by linarith)
  have hBvol : volume B = ENNReal.ofReal (φ y - φ ((y : ℝ) - 1)) := by
    dsimp [B]
    exact volume_curve_interval_reparam hη hvol (by linarith)
  have hUnion : A ∪ B = η '' Icc ((x : ℝ) - 1) y := by
    dsimp [A, B]
    exact interval_image_union (f := η) (by linarith) (by linarith)
  have hUnionVol : volume (A ∪ B) = volume A + volume B := by
    rw [hUnion, volume_curve_interval_reparam hη hvol (by linarith), hAvol, hBvol]
    have hp₁ : 0 ≤ φ ((y : ℝ) - 1) - φ ((x : ℝ) - 1) :=
      sub_nonneg.mpr (φ.monotone (by linarith))
    have hp₂ : 0 ≤ φ y - φ ((y : ℝ) - 1) :=
      sub_nonneg.mpr (φ.monotone (by linarith))
    rw [← ENNReal.ofReal_add hp₁ hp₂]
    congr 1
    ring
  have hBmeas : MeasurableSet B := (isCompact_Icc.image η.continuous).measurableSet
  have hformula := MeasureTheory.measure_union_add_inter (μ := volume) A hBmeas
  have hfinite : volume A + volume B ≠ ⊤ := by
    rw [hAvol, hBvol]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  have hcancel : volume A + volume B + volume (A ∩ B) = volume A + volume B + 0 := by
    calc
      volume A + volume B + volume (A ∩ B) = volume (A ∪ B) + volume (A ∩ B) := by rw [hUnionVol]
      _ = volume A + volume B := hformula
      _ = volume A + volume B + 0 := by simp
  have hcancel' : volume (A ∩ B) + (volume A + volume B) = 0 + (volume A + volume B) := by
    calc
      volume (A ∩ B) + (volume A + volume B) = volume A + volume B + volume (A ∩ B) := by ac_rfl
      _ = volume A + volume B + 0 := hcancel
      _ = 0 + (volume A + volume B) := by ac_rfl
  have hAB : volume (A ∩ B) = 0 := (ENNReal.add_left_inj hfinite).mp hcancel'
  have hsub : (η '' Icc ((x : ℝ) - 1) x) ∩ (η '' Icc ((y : ℝ) - 1) y) ⊆ A ∩ B := by
    rintro z ⟨⟨t, ht, hzt⟩, ⟨u, hu, hzu⟩⟩
    refine ⟨⟨t, ⟨ht.1, le_trans ht.2 hxyR⟩, hzt⟩, ⟨u, hu, hzu⟩⟩
  exact le_antisymm ((measure_mono hsub).trans_eq hAB) bot_le

/-- Distinct unit-time cells of the area-parametrized whole-plane curve have Lebesgue-null
intersection. -/
theorem volume_inter_unit_cells_zero
    {φ : ℝ ≃o ℝ} {ηL η : C(ℝ, ℂ)}
    (hη : ∀ t, η t = ηL (φ t))
    (hvol : ∀ s t : ℝ, s ≤ t → volume (ηL '' Icc s t) = ENNReal.ofReal (t - s))
    {x y : ℤ} (hxy : x ≠ y) :
    volume ((η '' Icc ((x : ℝ) - 1) x) ∩ (η '' Icc ((y : ℝ) - 1) y)) = 0 := by
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · exact volume_inter_separated_cell_zero hη hvol hlt
  · rw [inter_comm]
    exact volume_inter_separated_cell_zero hη hvol hgt

/-- Intervals with ordered disjoint time interiors have curve images whose intersection has
Lebesgue measure zero, by additivity of the area clock. -/
private theorem volume_inter_ordered_curve_intervals_zero
    {φ : ℝ ≃o ℝ} {ηL η : C(ℝ, ℂ)}
    (hη : ∀ t, η t = ηL (φ t))
    (hvol : ∀ s t : ℝ, s ≤ t → volume (ηL '' Icc s t) = ENNReal.ofReal (t - s))
    {a b c d : ℝ} (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    volume ((η '' Icc a b) ∩ (η '' Icc c d)) = 0 := by
  let A : Set ℂ := η '' Icc a c
  let B : Set ℂ := η '' Icc c d
  have hac : a ≤ c := hab.trans hbc
  have hAvol : volume A = ENNReal.ofReal (φ c - φ a) := by
    dsimp [A]
    exact volume_curve_interval_reparam hη hvol hac
  have hBvol : volume B = ENNReal.ofReal (φ d - φ c) := by
    dsimp [B]
    exact volume_curve_interval_reparam hη hvol hcd
  have hUnion : A ∪ B = η '' Icc a d := by
    dsimp [A, B]
    exact interval_image_union (f := η) hac hcd
  have hUnionVol : volume (A ∪ B) = volume A + volume B := by
    rw [hUnion, volume_curve_interval_reparam hη hvol (hac.trans hcd), hAvol, hBvol]
    have hp₁ : 0 ≤ φ c - φ a := sub_nonneg.mpr (φ.monotone hac)
    have hp₂ : 0 ≤ φ d - φ c := sub_nonneg.mpr (φ.monotone hcd)
    rw [← ENNReal.ofReal_add hp₁ hp₂]
    congr 1
    ring
  have hBmeas : MeasurableSet B := (isCompact_Icc.image η.continuous).measurableSet
  have hformula := MeasureTheory.measure_union_add_inter (μ := volume) A hBmeas
  have hfinite : volume A + volume B ≠ ⊤ := by
    rw [hAvol, hBvol]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  have hcancel : volume (A ∩ B) = 0 := by
    apply (ENNReal.add_left_inj hfinite).mp
    calc
      volume (A ∩ B) + (volume A + volume B) = volume A + volume B + volume (A ∩ B) := by ac_rfl
      _ = volume (A ∪ B) + volume (A ∩ B) := by rw [hUnionVol]
      _ = volume A + volume B := hformula
      _ = 0 + (volume A + volume B) := by simp
  have hsub : (η '' Icc a b) ∩ (η '' Icc c d) ⊆ A ∩ B := by
    rintro z ⟨⟨t, ht, hzt⟩, ⟨u, hu, hzu⟩⟩
    exact ⟨⟨t, ⟨ht.1, ht.2.trans hbc⟩, hzt⟩, ⟨u, hu, hzu⟩⟩
  exact le_antisymm ((measure_mono hsub).trans_eq hcancel) bot_le

/-- Distinct curve cells at any positive time mesh have null intersections. -/
theorem volume_inter_mesh_cells_zero
    {φ : ℝ ≃o ℝ} {ηL η : C(ℝ, ℂ)} {ε : ℝ} (hε : 0 < ε)
    (hη : ∀ t, η t = ηL (φ t))
    (hvol : ∀ s t : ℝ, s ≤ t → volume (ηL '' Icc s t) = ENNReal.ofReal (t - s))
    {x y : ℤ} (hxy : x ≠ y) :
    volume ((η '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ∩
      (η '' Icc (ε * ((y : ℝ) - 1)) (ε * y))) = 0 := by
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · have hxyR : ε * (x : ℝ) ≤ ε * ((y : ℝ) - 1) := by
      have : (x : ℝ) ≤ (y : ℝ) - 1 := by exact_mod_cast (show x ≤ y - 1 by omega)
      exact mul_le_mul_of_nonneg_left this hε.le
    exact volume_inter_ordered_curve_intervals_zero hη hvol
      (by nlinarith [hε.le]) hxyR (by nlinarith [hε.le])
  · rw [inter_comm]
    have hyxR : ε * (y : ℝ) ≤ ε * ((x : ℝ) - 1) := by
      have : (y : ℝ) ≤ (x : ℝ) - 1 := by exact_mod_cast (show y ≤ x - 1 by omega)
      exact mul_le_mul_of_nonneg_left this hε.le
    exact volume_inter_ordered_curve_intervals_zero hη hvol
      (by nlinarith [hε.le]) hyxR (by nlinarith [hε.le])

/-- A proper continuous Peanosphere curve has a locally finite family of bounded-time cells. -/
theorem locallyFinite_unit_curve_cells {η : C(ℝ, ℂ)}
    (htrans : Tendsto η (Filter.cocompact ℝ) (Filter.cocompact ℂ)) :
    LocallyFinite (fun x : ℤ => (η : ℝ → ℂ) '' Icc ((x : ℝ) - 1) x) := by
  intro z
  let K : Set ℂ := closedBall z 1
  have hK : IsCompact K := isCompact_closedBall z 1
  have hpre : (η : ℝ → ℂ) ⁻¹' Kᶜ ∈ Filter.cocompact ℝ :=
    htrans (hK.compl_mem_cocompact)
  obtain ⟨T, hTcompact, hTpre⟩ := (Filter.mem_cocompact.mp hpre)
  obtain ⟨R, hTR⟩ := hTcompact.isBounded.subset_ball (0 : ℝ)
  let R' : ℝ := max R 1
  have hR' : 0 < R' := lt_of_lt_of_le zero_lt_one (le_max_right R 1)
  have hTR' : T ⊆ ball (0 : ℝ) R' := hTR.trans (ball_subset_ball (le_max_left R 1))
  obtain ⟨N, hN⟩ := exists_nat_gt (R' + 1)
  let n : ℤ := N
  have hfinite : {x : ℤ | ((η '' Icc ((x : ℝ) - 1) x) ∩ ball z 1).Nonempty}.Finite := by
    apply (Set.finite_Icc (-(n)) n).subset
    intro x hx
    obtain ⟨w, ⟨⟨t, ht, rfl⟩, hw⟩⟩ := hx
    have hwK : η t ∈ K := (ball_subset_closedBall) hw
    have htT : t ∈ T := by
      by_contra htT
      have htTc : t ∈ Tᶜ := htT
      have hnotK : η t ∈ Kᶜ := hTpre htTc
      exact hnotK hwK
    have htR : t ∈ ball (0 : ℝ) R' := hTR' htT
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at htR
    have htR' : -R' < t ∧ t < R' := abs_lt.mp htR
    have hxlo : -(N : ℝ) ≤ (x : ℝ) := by
      have htx : t ≤ (x : ℝ) := ht.2
      linarith
    have hxhi : (x : ℝ) ≤ N := by
      have htx : (x : ℝ) - 1 ≤ t := ht.1
      linarith
    exact ⟨by exact_mod_cast hxlo, by exact_mod_cast hxhi⟩
  exact ⟨ball z 1, Metric.ball_mem_nhds z one_pos, hfinite⟩

private theorem ae_exists_segmentBallEvent
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    {R : ℝ} (hR : 0 < R) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    ∀ᵐ ω ∂P, ∃ n : ℕ,
      SegmentsContainBalls (ηL ω) R r (1 / ((n : ℝ) + 2)) := by
  letI : IsProbabilityMeasure P := D.isProbabilityMeasure
  obtain ⟨C, hC⟩ := D.segmentsContainBalls R hR r hr 1
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2)
  let bad : Set Ω := {ω | ∀ n, ¬ SegmentsContainBalls (ηL ω) R r (ε n)}
  have hseq : Tendsto ε atTop (𝓝 0) := by
    have hden : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
      Filter.tendsto_atTop_mono (fun n => show (n : ℝ) ≤ (n : ℝ) + 2 by norm_num)
        tendsto_natCast_atTop_atTop
    have hinv : Tendsto (fun n : ℕ => ((n : ℝ) + 2)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hden
    simpa [ε, one_div] using hinv
  have hbound : ∀ n, P bad ≤ ENNReal.ofReal (max C 0 * ε n) := by
    intro n
    have hεpos : 0 < ε n := by dsimp [ε]; positivity
    have hεlt : ε n < 1 := by
      dsimp [ε]
      have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      have hden : 2 ≤ (n : ℝ) + 2 := by linarith
      have hden' : 1 < (n : ℝ) + 2 := by linarith
      simpa using (one_div_lt_one_div_of_lt (a := (1 : ℝ)) zero_lt_one hden')
    have hsubset : bad ⊆ {ω | ¬ SegmentsContainBalls (ηL ω) R r (ε n)} := by
      intro ω hω
      exact hω n
    have hprob := measure_mono (μ := P) hsubset
    have hsource := hC (ε n) ⟨hεpos, hεlt⟩
    have hcoef : C * ε n ≤ max C 0 * ε n :=
      mul_le_mul_of_nonneg_right (le_max_left C 0) hεpos.le
    exact hprob.trans (hsource.trans (ENNReal.ofReal_le_ofReal (by simpa [pow_one] using hcoef)))
  have hreal : ∀ n, (P bad).toReal ≤ max C 0 * ε n := by
    intro n
    have hnonneg : 0 ≤ max C 0 * ε n := mul_nonneg (le_max_right C 0) (le_of_lt (by dsimp [ε]; positivity))
    exact ENNReal.toReal_le_of_le_ofReal hnonneg (hbound n)
  have hlim : Tendsto (fun n : ℕ => max C 0 * ε n) atTop (𝓝 0) := by
    simpa [mul_zero] using (tendsto_const_nhds (x := max C 0)).mul hseq
  have hbadReal : (P bad).toReal = 0 := by
    apply le_antisymm
    · exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hreal
    · exact ENNReal.toReal_nonneg
  have hbadFinite : P bad < ⊤ := by
    have hle : P bad ≤ 1 := by
      calc
        P bad ≤ P Set.univ := measure_mono (μ := P) (subset_univ bad)
        _ = 1 := by simp
    exact lt_of_le_of_lt hle ENNReal.one_lt_top
  have hbadZero : P bad = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff (P bad)).mp hbadReal with hzero | htop
    · exact hzero
    · exact (hbadFinite.ne htop).elim
  rw [ae_iff]
  simpa [bad, ε, one_div, not_exists] using hbadZero

private theorem diam_pos_of_volume_pos {S : Set ℂ} (hS : Bornology.IsBounded S)
    (hSne : S.Nonempty) (hvol : 0 < volume S) : 0 < Metric.diam S := by
  have hnotSub : ¬ S.Subsingleton := by
    intro hsub
    obtain ⟨z, hz⟩ := hSne
    have hsubset : S ⊆ ({z} : Set ℂ) := by
      intro w hw
      simp only [Set.mem_singleton_iff]
      exact hsub hw hz
    have hzero : volume S = 0 := by
      apply le_antisymm
      · calc
          volume S ≤ volume ({z} : Set ℂ) := measure_mono (μ := volume) hsubset
          _ = 0 := by simp
      · exact bot_le
    rw [hzero] at hvol
    exact (lt_irrefl 0) hvol
  obtain ⟨z, hz, w, hw, hzw⟩ := Set.not_subsingleton_iff.mp hnotSub
  exact (dist_pos.mpr hzw).trans_le (Metric.dist_le_diam_of_mem hS hz hw)

/-- Positive Lebesgue-time length and the SLE segment-ball estimate imply that every unit-time
cell has nonempty Euclidean interior almost surely. -/
theorem ae_curve_cells_have_interior
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ x : ℤ, (interior (η ω '' Icc ((x : ℝ) - 1) x)).Nonempty := by
  have hgood : ∀ᵐ ω ∂P, ∀ R : ℕ, ∃ n : ℕ,
      SegmentsContainBalls (ηL ω) ((R : ℝ) + 1) (1 / 2) (1 / ((n : ℝ) + 2)) := by
    refine ae_all_iff.2 fun R => ?_
    exact ae_exists_segmentBallEvent D (by positivity) (by norm_num)
  filter_upwards [D.areaParam, D.spaceFilling, hgood] with ω harea hspace hgood
  rcases harea with ⟨⟨φ, _, hη⟩, _⟩
  rcases hspace with ⟨_, _, _, hvol⟩
  intro x
  have hηLcompact : IsCompact (ηL ω '' Icc (φ ((x : ℝ) - 1)) (φ x)) :=
    isCompact_Icc.image (ηL ω).continuous
  obtain ⟨Rreal, hRball⟩ := hηLcompact.isBounded.subset_ball (0 : ℂ)
  let R : ℕ := ⌈Rreal⌉₊ + 1
  have hRball' : ηL ω '' Icc (φ ((x : ℝ) - 1)) (φ x) ⊆ ball 0 ((R : ℝ) + 1) := by
    exact hRball.trans (Metric.ball_subset_ball (by dsimp [R]; push_cast; linarith [Nat.le_ceil Rreal]))
  obtain ⟨n, hsegEvent⟩ := hgood R
  let δ : ℝ := 1 / ((n : ℝ) + 2)
  have hδpos : 0 < δ := by dsimp [δ]; positivity
  have hdiam : 0 < Metric.diam (ηL ω '' Icc (φ ((x : ℝ) - 1)) (φ x)) := by
    apply diam_pos_of_volume_pos hηLcompact.isBounded (by
      exact ⟨(ηL ω) (φ ((x : ℝ) - 1)), φ ((x : ℝ) - 1), ⟨le_rfl, φ.monotone (by linarith)⟩, rfl⟩) ?_
    rw [hvol _ _ (φ.monotone (by linarith))]
    apply ENNReal.ofReal_pos.mpr
    exact sub_pos.mpr (φ.strictMono (by linarith))
  have hp : 0 < 1 - (1 / 2 : ℝ) := by norm_num
  have hpow := GMSLemma27.tendsto_rpow_nhdsGT_zero hp
  have hsmall : ∀ᶠ d : ℝ in 𝓝[>] (0 : ℝ), d ^ (1 - (1 / 2 : ℝ)) < Metric.diam (ηL ω '' Icc (φ ((x : ℝ) - 1)) (φ x)) :=
    hpow.mono_right nhdsWithin_le_nhds |>.eventually (gt_mem_nhds hdiam)
  have hδexist : ∃ d : ℝ, 0 < d ∧ d < δ ∧
      d ^ (1 - (1 / 2 : ℝ)) ≤ Metric.diam (ηL ω '' Icc (φ ((x : ℝ) - 1)) (φ x)) := by
    have hmem : ∀ᶠ d : ℝ in 𝓝[>] (0 : ℝ), 0 < d ∧ d < δ ∧
        d ^ (1 - (1 / 2 : ℝ)) ≤ Metric.diam (ηL ω '' Icc (φ ((x : ℝ) - 1)) (φ x)) := by
      filter_upwards [hsmall, self_mem_nhdsWithin, Ioo_mem_nhdsGT hδpos] with d hd hdp hdu
      exact ⟨hdp, hdu.2, le_of_lt hd⟩
    exact hmem.exists
  obtain ⟨d, hdp, hdδ, hddiam⟩ := hδexist
  have hdEvent : d ∈ Ioc (0 : ℝ) δ := ⟨hdp, le_of_lt hdδ⟩
  have hparamL : ηL ω '' Icc (φ ((x : ℝ) - 1)) (φ x) ⊆ ball 0 ((R : ℝ) + 1) := hRball'
  obtain ⟨w, hwball⟩ := hsegEvent d hdEvent (φ ((x : ℝ) - 1)) (φ x)
    (φ.strictMono (by linarith)) hparamL hddiam
  have himage : η ω '' Icc ((x : ℝ) - 1) x =
      ηL ω '' Icc (φ ((x : ℝ) - 1)) (φ x) := image_reparam_Icc hη _ _
  refine ⟨w, ?_⟩
  apply (mem_interior_iff_mem_nhds).2
  apply Filter.mem_of_superset (Metric.ball_mem_nhds w hdp)
  rw [himage]
  exact hwball

/-- Every positive-length time interval of the bundle curve has nonempty interior almost surely. -/
theorem ae_curve_intervals_have_interior
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ a b : ℝ, a < b → (interior (η ω '' Icc a b)).Nonempty := by
  have hgood : ∀ᵐ ω ∂P, ∀ R : ℕ, ∃ n : ℕ,
      SegmentsContainBalls (ηL ω) ((R : ℝ) + 1) (1 / 2) (1 / ((n : ℝ) + 2)) := by
    refine ae_all_iff.2 fun R => ?_
    exact ae_exists_segmentBallEvent D (by positivity) (by norm_num)
  filter_upwards [D.areaParam, D.spaceFilling, hgood] with ω harea hspace hgood
  rcases harea with ⟨⟨φ, _, hη⟩, _⟩
  rcases hspace with ⟨_, _, _, hvol⟩
  intro a b hab
  have hηLcompact : IsCompact (ηL ω '' Icc (φ a) (φ b)) :=
    isCompact_Icc.image (ηL ω).continuous
  obtain ⟨Rreal, hRball⟩ := hηLcompact.isBounded.subset_ball (0 : ℂ)
  let R : ℕ := ⌈Rreal⌉₊ + 1
  have hRball' : ηL ω '' Icc (φ a) (φ b) ⊆ ball 0 ((R : ℝ) + 1) :=
    hRball.trans (Metric.ball_subset_ball (by dsimp [R]; push_cast; linarith [Nat.le_ceil Rreal]))
  obtain ⟨n, hsegEvent⟩ := hgood R
  let δ : ℝ := 1 / ((n : ℝ) + 2)
  have hδpos : 0 < δ := by dsimp [δ]; positivity
  have hdiam : 0 < Metric.diam (ηL ω '' Icc (φ a) (φ b)) := by
    apply diam_pos_of_volume_pos hηLcompact.isBounded (by
      exact ⟨(ηL ω) (φ a), φ a, ⟨le_rfl, φ.monotone (le_of_lt hab)⟩, rfl⟩) ?_
    rw [hvol _ _ (φ.monotone (le_of_lt hab))]
    exact ENNReal.ofReal_pos.mpr (sub_pos.mpr (φ.strictMono hab))
  have hp : 0 < 1 - (1 / 2 : ℝ) := by norm_num
  have hpow := GMSLemma27.tendsto_rpow_nhdsGT_zero hp
  have hsmall : ∀ᶠ d : ℝ in 𝓝[>] (0 : ℝ),
      d ^ (1 - (1 / 2 : ℝ)) < Metric.diam (ηL ω '' Icc (φ a) (φ b)) :=
    hpow.mono_right nhdsWithin_le_nhds |>.eventually (gt_mem_nhds hdiam)
  have hδexist : ∃ d : ℝ, 0 < d ∧ d < δ ∧
      d ^ (1 - (1 / 2 : ℝ)) ≤ Metric.diam (ηL ω '' Icc (φ a) (φ b)) := by
    have hmem : ∀ᶠ d : ℝ in 𝓝[>] (0 : ℝ), 0 < d ∧ d < δ ∧
        d ^ (1 - (1 / 2 : ℝ)) ≤ Metric.diam (ηL ω '' Icc (φ a) (φ b)) := by
      filter_upwards [hsmall, self_mem_nhdsWithin, Ioo_mem_nhdsGT hδpos] with d hd hdp hdu
      exact ⟨hdp, hdu.2, le_of_lt hd⟩
    exact hmem.exists
  obtain ⟨d, hdp, hdδ, hddiam⟩ := hδexist
  obtain ⟨w, hwball⟩ := hsegEvent d ⟨hdp, le_of_lt hdδ⟩ (φ a) (φ b)
    (φ.strictMono hab) hRball' hddiam
  have himage : η ω '' Icc a b = ηL ω '' Icc (φ a) (φ b) := image_reparam_Icc hη _ _
  refine ⟨w, ?_⟩
  apply (mem_interior_iff_mem_nhds).2
  apply Filter.mem_of_superset (Metric.ball_mem_nhds w hdp)
  rw [himage]
  exact hwball

/-- Surjectivity makes the closed unit-time cells cover the plane. -/
theorem curve_cells_cover {η : C(ℝ, ℂ)} (hsurj : Function.Surjective η) :
    (⋃ x : ℤ, η '' Icc ((x : ℝ) - 1) x) = Set.univ := by
  ext z
  constructor
  · intro _
    exact Set.mem_univ z
  · intro _
    obtain ⟨t, rfl⟩ := hsurj z
    let x : ℤ := Int.floor t + 1
    have htlo : (Int.floor t : ℝ) ≤ t := Int.floor_le t
    have hthi : t ≤ (Int.floor t : ℝ) + 1 := le_of_lt (Int.lt_floor_add_one t)
    have hcast : ((Int.floor t + 1 : ℤ) : ℝ) = (Int.floor t : ℝ) + 1 := by
      push_cast
      ring
    have hcast' : ((Int.floor t + 1 : ℤ) : ℝ) - 1 = (Int.floor t : ℝ) := by
      rw [hcast]
      ring
    have ht : t ∈ Icc ((x : ℝ) - 1) x := by
      dsimp [x]
      rw [hcast']
      rw [hcast]
      exact ⟨htlo, hthi⟩
    exact Set.mem_iUnion.mpr ⟨x, ⟨t, ht, rfl⟩⟩

/-- Package the deterministic curve-cell facts as a cellular embedding once the quantitative
segment-ball input supplies nonempty interiors. -/
def cellularEmbeddingOfCurve {ω : Path2} {ηL η : C(ℝ, ℂ)}
    (hlocal : IsLocallyFinite 1 ω) (P : RouteM.Peanosphere ω η)
    (hside : RouteM.SideStrict 1 ω) (hη0 : η 0 = 0)
    {φ : ℝ ≃o ℝ} (hη : ∀ t, η t = ηL (φ t))
    (hvol : ∀ s t : ℝ, s ≤ t → volume (ηL '' Icc s t) = ENNReal.ofReal (t - s))
    (hinterior : ∀ x : ℤ, (interior (η '' Icc ((x : ℝ) - 1) x)).Nonempty)
    (hnull : ∀ x y : ℤ, x ≠ y →
      volume ((η '' Icc ((x : ℝ) - 1) x) ∩ (η '' Icc ((y : ℝ) - 1) y)) = 0) :
    CellularEmbedding (MatedCRT.graph 1 ω hlocal) 0 where
  cell x := η '' Icc ((x : ℝ) - 1) x
  isCompact_cell x := isCompact_Icc.image η.continuous
  isConnected_cell x :=
    (isConnected_Icc (by linarith : ((x : ℝ) - 1) ≤ x)).image
      (η : ℝ → ℂ) η.continuous.continuousOn
  interior_cell_nonempty := hinterior
  locallyFinite_cell := locallyFinite_unit_curve_cells (η := η) P.transient
  iUnion_cell := curve_cells_cover P.surj
  volume_inter_cell := hnull
  inter_of_adj := by
    intro x y hadj
    simpa only [one_mul] using cell_intersects_of_matedCRT_adj one_pos P hside hadj
  zero_mem_root := by
    rw [← hη0]
    refine ⟨0, ?_, rfl⟩
    constructor <;> simp

/-- A proper curve has locally finite cell images at every positive time mesh. -/
theorem locallyFinite_curve_cellsAt {η : C(ℝ, ℂ)} {ε : ℝ} (hε : 0 < ε)
    (htrans : Tendsto η (Filter.cocompact ℝ) (Filter.cocompact ℂ)) :
    LocallyFinite (fun x : ℤ => (η : ℝ → ℂ) '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) := by
  intro z
  let K : Set ℂ := closedBall z 1
  have hK : IsCompact K := isCompact_closedBall z 1
  have hpre : (η : ℝ → ℂ) ⁻¹' Kᶜ ∈ Filter.cocompact ℝ := htrans (hK.compl_mem_cocompact)
  obtain ⟨T, hTcompact, hTpre⟩ := Filter.mem_cocompact.mp hpre
  obtain ⟨R, hTR⟩ := hTcompact.isBounded.subset_ball (0 : ℝ)
  let R' : ℝ := max R 1
  have hR' : 0 < R' := lt_of_lt_of_le zero_lt_one (le_max_right R 1)
  have hTR' : T ⊆ ball (0 : ℝ) R' := hTR.trans (ball_subset_ball (le_max_left R 1))
  obtain ⟨N, hN⟩ := exists_nat_gt (R' / ε + 2)
  let n : ℤ := N
  have hfinite : {x : ℤ | ((η '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ∩ ball z 1).Nonempty}.Finite := by
    apply (Set.finite_Icc (-(n)) n).subset
    intro x hx
    obtain ⟨w, ⟨⟨t, ht, rfl⟩, hw⟩⟩ := hx
    have htT : t ∈ T := by
      by_contra htT
      have hnotK : η t ∈ Kᶜ := hTpre htT
      exact hnotK (ball_subset_closedBall hw)
    have htR : t ∈ ball (0 : ℝ) R' := hTR' htT
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at htR
    have htR' : -R' < t ∧ t < R' := abs_lt.mp htR
    have hlo : -(N : ℝ) ≤ (x : ℝ) := by
      have hdiv : t / ε ≤ (x : ℝ) := (div_le_iff₀ hε).2 (by simpa [mul_comm] using ht.2)
      have hNpos : 0 < (N : ℝ) := by linarith [hN, div_nonneg (le_of_lt hR') hε.le]
      have hquot : -(R' / ε) < t / ε := by
        simpa [neg_div] using (div_lt_div_of_pos_right htR'.1 hε)
      have hbound : -(N : ℝ) < -(R' / ε) := by linarith [hN]
      exact le_of_lt (hbound.trans (hquot.trans_le hdiv))
    have hhi : (x : ℝ) ≤ N := by
      have hdiv : (x : ℝ) - 1 ≤ t / ε := (le_div_iff₀ hε).2 (by simpa [mul_comm] using ht.1)
      have hquot : t / ε < R' / ε := (div_lt_div_of_pos_right htR'.2 hε)
      have hN' : R' / ε + 1 < (N : ℝ) := by push_cast at hN ⊢; linarith
      linarith
    exact ⟨by exact_mod_cast hlo, by exact_mod_cast hhi⟩
  exact ⟨ball z 1, Metric.ball_mem_nhds z one_pos, hfinite⟩

/-- The curve cells at any positive time mesh cover the plane. -/
theorem curve_cellsAt_cover {η : C(ℝ, ℂ)} {ε : ℝ} (hε : 0 < ε)
    (hsurj : Function.Surjective η) :
    (⋃ x : ℤ, η '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) = Set.univ := by
  ext z
  constructor
  · intro _
    exact Set.mem_univ z
  · intro _
    obtain ⟨t, rfl⟩ := hsurj z
    let q : ℝ := t / ε
    let x : ℤ := Int.floor q + 1
    have hqlo : (Int.floor q : ℝ) ≤ q := Int.floor_le q
    have hqhi : q ≤ (Int.floor q : ℝ) + 1 := le_of_lt (Int.lt_floor_add_one q)
    have hx : (x : ℝ) = (Int.floor q : ℝ) + 1 := by simp [x]
    have hxl : (x : ℝ) - 1 = (Int.floor q : ℝ) := by rw [hx]; ring
    have ht : t ∈ Icc (ε * ((x : ℝ) - 1)) (ε * x) := by
      rw [hxl, hx]
      constructor
      · dsimp [q] at hqlo
        simpa [mul_comm] using (le_div_iff₀ hε).mp hqlo
      · dsimp [q] at hqhi
        simpa [mul_comm] using (div_le_iff₀ hε).mp hqhi
    exact Set.mem_iUnion.mpr ⟨x, ⟨t, ht, rfl⟩⟩

/-- Unit-mesh local finiteness plus a Peanosphere curve and its geometric estimates gives the
cellular embedding at any positive mesh. -/
def cellularEmbeddingOfCurveAt {ω : Path2} {η : C(ℝ, ℂ)} {ε : ℝ} (hε : 0 < ε)
    (hlocal : IsLocallyFinite ε ω) (P : RouteM.Peanosphere ω η)
    (hside : RouteM.SideStrict ε ω) (hη0 : η 0 = 0)
    (hinterior : ∀ x : ℤ,
      (interior (η '' Icc (ε * ((x : ℝ) - 1)) (ε * x))).Nonempty)
    (hnull : ∀ x y : ℤ, x ≠ y →
      volume ((η '' Icc (ε * ((x : ℝ) - 1)) (ε * x)) ∩
        (η '' Icc (ε * ((y : ℝ) - 1)) (ε * y))) = 0) :
    CellularEmbedding (MatedCRT.graph ε ω hlocal) 0 where
  cell x := η '' Icc (ε * ((x : ℝ) - 1)) (ε * x)
  isCompact_cell x := isCompact_Icc.image η.continuous
  isConnected_cell x :=
    (isConnected_Icc (by nlinarith : ε * ((x : ℝ) - 1) ≤ ε * x)).image
      (η : ℝ → ℂ) η.continuous.continuousOn
  interior_cell_nonempty := hinterior
  locallyFinite_cell := locallyFinite_curve_cellsAt hε P.transient
  iUnion_cell := curve_cellsAt_cover hε P.surj
  volume_inter_cell := hnull
  inter_of_adj := by
    intro x y hadj
    exact cell_intersects_of_matedCRT_adj hε P hside hadj
  zero_mem_root := by
    rw [← hη0]
    refine ⟨0, ?_, rfl⟩
    constructor
    · simp only [Int.cast_zero, zero_sub, Int.cast_one, mul_neg]
      nlinarith [hε.le]
    · simp

/-- The bundle's segment-ball estimate gives interior for every cell in every dyadic mesh. -/
theorem ae_mesh_cells_have_interior
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ k (x : ℤ), (interior (η ω '' Icc
      (CellFamily.mesh k * ((x : ℝ) - 1)) (CellFamily.mesh k * x))).Nonempty := by
  have hinterval := ae_curve_intervals_have_interior D
  refine ae_all_iff.2 fun k => ae_all_iff.2 fun x => ?_
  filter_upwards [hinterval] with ω hω
  have hε : 0 < CellFamily.mesh k := by dsimp [CellFamily.mesh]; positivity
  exact hω _ _ (by nlinarith [hε])

/-- Pairwise curve-cell intersections remain null at every dyadic mesh. -/
theorem ae_mesh_cells_have_null_intersections
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ k (x y : ℤ), x ≠ y → volume
      ((η ω '' Icc (CellFamily.mesh k * ((x : ℝ) - 1)) (CellFamily.mesh k * x)) ∩
        (η ω '' Icc (CellFamily.mesh k * ((y : ℝ) - 1)) (CellFamily.mesh k * y))) = 0 := by
  refine ae_all_iff.2 fun k => ae_all_iff.2 fun x => ae_all_iff.2 fun y => ?_
  filter_upwards [D.areaParam, D.spaceFilling] with ω harea hspace
  rcases harea with ⟨⟨φ, _, hη⟩, _⟩
  rcases hspace with ⟨_, _, _, hvol⟩
  intro hxy
  have hε : 0 < CellFamily.mesh k := by dsimp [CellFamily.mesh]; positivity
  exact volume_inter_mesh_cells_zero hε hη hvol hxy

/-- On a common full-measure event, the SLE cells form cellular embeddings of the full
dyadic-mesh mated-CRT multigraphs. -/
theorem ae_meshCellularEmbeddings
    {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
    {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    ∀ᵐ ω ∂P, ∀ k, ∃ h : IsLocallyFinite (CellFamily.mesh k) (bm ω),
      ∃ H : CellularEmbedding (MatedCRT.graph (CellFamily.mesh k) (bm ω) h) 0,
        H.cell = fun x : ℤ => η ω '' Icc
          (CellFamily.mesh k * ((x : ℝ) - 1)) (CellFamily.mesh k * x) := by
  have hlocal : ∀ᵐ ω ∂P, ∀ k, IsLocallyFinite (CellFamily.mesh k) (bm ω) := by
    refine ae_all_iff.2 fun k => ?_
    have hε : 0 < CellFamily.mesh k := by dsimp [CellFamily.mesh]; positivity
    have hmap := MatedCRTHarmonic.ae_isLocallyFinite_holds γ (P.map bm)
      D.boundaryLawBM (CellFamily.mesh k) hε
    exact ae_of_ae_map D.measurable_curves.2.2.2.aemeasurable hmap
  filter_upwards [hlocal, ae_peanosphere D, ae_sideStrict_allMeshes D,
      ae_mesh_cells_have_interior D, ae_mesh_cells_have_null_intersections D,
      D.areaParam, D.spaceFilling] with ω hlocal hP hside hinterior hnull harea hspace
  rcases harea with ⟨⟨φ, hφ0, hη⟩, _⟩
  rcases hspace with ⟨_, _, hηL0, _⟩
  have hη0 : η ω 0 = 0 := by rw [hη, hφ0, hηL0]
  intro k
  have hε : 0 < CellFamily.mesh k := by dsimp [CellFamily.mesh]; positivity
  let H := cellularEmbeddingOfCurveAt hε (hlocal k) hP (hside k) hη0
    (fun x => hinterior k x) (fun x y hxy => hnull k x y hxy)
  exact ⟨hlocal k, H, rfl⟩

end MatedCRTHarmonic.MoTInput
