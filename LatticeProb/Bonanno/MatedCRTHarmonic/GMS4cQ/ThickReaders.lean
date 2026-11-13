/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.GMS4cQ.ThickReaders at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4c.BundleAreaReader
import LatticeProb.Bonanno.MatedCRTHarmonic.GMS4.Prop48CanonicalCompletion

/-!
# Thickened-field GMC readers for every open set (target (b))

Source: the proof of [18] Lemma 4.3 : "`μ_h` is determined by
`h|_V`". the `GMS4c.exists_borel_bundle_localAreaReader` gives, for a **bounded** open `V`, one Borel map
from the measurable zero-cone field version on the `δ`-thickening of `V` to the restricted GMC area `μ_h|_V`.

Here:
* `exists_zeroCone_areaReader_of_bounded`: the bounded case for the **raw** zero-cone field
  `coneField X₀ (coneRadial γ 0 B₀ B₀')` (the measurable version agrees with it almost surely);
* `l43qAreaReader`: for an arbitrary open `V`, the restricted area is the countable sum of the readers of the
  bounded pieces `V ∩ B_{n+1}(0)`, each restricted to the disjointed annulus `B_{n+1}(0) \ B_n(0)`;
* `thickGMCReaders D hγ : GMS4.Canonical.ThickGMCReaders D` — the H2, exactly as stated.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped NNReal ENNReal

namespace MatedCRTHarmonic.GMS4cQ

open LQGMetric MatedCRTHarmonic.MatedCRT MatedCRTHarmonic.MoTPort.IG.GFFAbsCont

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → Path2}

/-- The raw zero-cone field of the coupling. -/
abbrev l43qZeroField (B₀ B₀' : ℝ≥0 → Ω → ℝ) (X₀ : Ω → Field) (γ : ℝ) (ω : Ω) : DistC :=
  coneField (X₀ ω) (coneRadial γ 0 (fun t => B₀ t ω) (fun t => B₀' t ω))

/-- A translation moving a bounded set into the upper half-plane. -/
theorem exists_translate_upper {V : Set ℂ} (hVb : Bornology.IsBounded V) :
    ∃ J : ℂ ≃ₜ ℂ, Bornology.IsBounded (J '' V) ∧ J '' V ⊆ QuantumZipper.H ∧
      (J '' V)ᶜ.Nonempty := by
  obtain ⟨R, hR⟩ := hVb.subset_ball (0 : ℂ)
  set c : ℂ := ((|R| + 1 : ℝ) : ℂ) * Complex.I
  refine ⟨Homeomorph.addRight c, ?_, ?_, ?_⟩
  · refine (isBounded_ball (x := c) (r := R)).subset ?_
    rintro _ ⟨w, hw, rfl⟩
    have hw' := hR hw
    rw [mem_ball, dist_zero_right] at hw'
    rw [mem_ball, dist_eq_norm]
    change ‖w + c - c‖ < R
    rwa [add_sub_cancel_right]
  · rintro _ ⟨w, hw, rfl⟩
    have hw' := hR hw
    rw [mem_ball, dist_zero_right] at hw'
    have him : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
    change 0 < (w + c).im
    simp only [c, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.ofReal_im, Complex.I_re, mul_one, mul_zero, add_zero]
    have := neg_abs_le w.im
    have := le_abs_self R
    linarith
  · refine ⟨c + ((|R| + 1 : ℝ) : ℂ) * 2, ?_⟩
    rintro ⟨w, hw, hwe⟩
    have hw' := hR hw
    rw [mem_ball, dist_zero_right] at hw'
    change w + c = c + ((|R| + 1 : ℝ) : ℂ) * 2 at hwe
    have hw2 : w = ((|R| + 1 : ℝ) : ℂ) * 2 := by linear_combination hwe
    rw [hw2, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)] at hw'
    norm_num at hw'
    have := le_abs_self R
    have := abs_nonneg R
    linarith

/-- **Bounded case.** One Borel map from the thickened raw zero-cone field to its restricted GMC area. -/
theorem exists_zeroCone_areaReader_of_bounded
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2)
    (V : TopologicalSpace.Opens ℂ) (hVb : Bornology.IsBounded (V : Set ℂ))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ F : DistOn (GMS4c.thickOpen V δ) → Measure ℂ, Measurable F ∧
      ∀ᵐ ω ∂P, F (restrictTo (GMS4c.thickOpen V δ) (l43qZeroField B₀ B₀' X₀ γ ω)) =
        (CellScaling.lqgArea γ (l43qZeroField B₀ B₀' X₀ γ ω)).restrict V := by
  obtain ⟨J, hJb, hJH, hJc⟩ := exists_translate_upper hVb
  have hVc : (V : Set ℂ)ᶜ.Nonempty := by
    obtain ⟨w, hw⟩ := hJc
    refine ⟨J.symm w, fun hv => hw ⟨J.symm w, hv, J.apply_symm_apply w⟩⟩
  obtain ⟨F, hF, -, h0⟩ :=
    GMS4c.exists_borel_bundle_localAreaReader D hγ V hVb hVc hδ J hJb hJH hJc
  refine ⟨F, hF, ?_⟩
  filter_upwards [h0, GMS4b.l46tZeroConeFieldVersion_ae_eq_raw D hγ] with ω h1 h2
  have h2' : l43qZeroField B₀ B₀' X₀ γ ω = GMS4b.l46tZeroConeFieldVersion D ω := h2
  exact (congrArg (fun T => F (restrictTo (GMS4c.thickOpen V δ) T)) h2').trans h1

/-- The bounded pieces `V ∩ B_{n+1}(0)`. -/
def l43qPiece (V : TopologicalSpace.Opens ℂ) (n : ℕ) : TopologicalSpace.Opens ℂ :=
  V ⊓ ⟨ball (0 : ℂ) ((n : ℝ) + 1), isOpen_ball⟩

theorem l43qPiece_bounded (V : TopologicalSpace.Opens ℂ) (n : ℕ) :
    Bornology.IsBounded (l43qPiece V n : Set ℂ) :=
  isBounded_ball.subset inter_subset_right

theorem l43qPiece_le (V : TopologicalSpace.Opens ℂ) (n : ℕ) : l43qPiece V n ≤ V :=
  inf_le_left

theorem thickOpen_mono {V V' : TopologicalSpace.Opens ℂ} (h : V ≤ V') (δ : ℝ) :
    GMS4c.thickOpen V δ ≤ GMS4c.thickOpen V' δ := by
  have h' : (V : Set ℂ) ⊆ (V' : Set ℂ) := SetLike.coe_subset_coe.mpr h
  exact SetLike.coe_subset_coe.mp (thickening_subset_of_subset δ h')

/-- The disjointed annuli `B_{n+1}(0) \ ⋃_{m<n} B_{m+1}(0)`. -/
def l43qAnnulus (n : ℕ) : Set ℂ := disjointed (fun m : ℕ => ball (0 : ℂ) ((m : ℝ) + 1)) n

theorem measurableSet_l43qAnnulus (n : ℕ) : MeasurableSet (l43qAnnulus n) :=
  MeasurableSet.disjointed (fun _ => measurableSet_ball) n

theorem iUnion_l43qAnnulus : (⋃ n, l43qAnnulus n) = univ := by
  show (⋃ n, disjointed (fun m : ℕ => ball (0 : ℂ) ((m : ℝ) + 1)) n) = univ
  rw [iUnion_disjointed]
  refine eq_univ_of_forall fun w => mem_iUnion.2 ?_
  obtain ⟨n, hn⟩ := exists_nat_gt ‖w‖
  exact ⟨n, by rw [mem_ball, dist_zero_right]; linarith⟩

/-- The restricted measure is the sum of its restrictions to the pieces, cut by the annuli. -/
theorem sum_restrict_piece_annulus (μ : Measure ℂ) (V : TopologicalSpace.Opens ℂ) :
    Measure.sum (fun n => (μ.restrict (l43qPiece V n)).restrict (l43qAnnulus n)) =
      μ.restrict V := by
  have hpiece : ∀ n, (μ.restrict (l43qPiece V n)).restrict (l43qAnnulus n) =
      μ.restrict (l43qAnnulus n ∩ V) := by
    intro n
    rw [Measure.restrict_restrict (measurableSet_l43qAnnulus n)]
    congr 1
    ext w
    simp only [l43qPiece, TopologicalSpace.Opens.coe_inf, TopologicalSpace.Opens.coe_mk,
      mem_inter_iff]
    constructor
    · rintro ⟨h1, h2, -⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2, disjointed_subset _ n h1⟩
  simp_rw [hpiece]
  rw [← Measure.restrict_iUnion]
  · rw [← iUnion_inter, iUnion_l43qAnnulus, univ_inter]
  · exact (disjoint_disjointed _).mono fun i j h =>
      h.mono inter_subset_left inter_subset_left
  · exact fun n => (measurableSet_l43qAnnulus n).inter V.isOpen.measurableSet

/-- The bounded-piece readers, chosen once. -/
def l43qPieceReader
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (V : TopologicalSpace.Opens ℂ) {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    DistOn (GMS4c.thickOpen (l43qPiece V n) δ) → Measure ℂ :=
  Classical.choose
    (exists_zeroCone_areaReader_of_bounded D hγ (l43qPiece V n) (l43qPiece_bounded V n) hδ)

theorem l43qPieceReader_spec
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (V : TopologicalSpace.Opens ℂ) {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    Measurable (l43qPieceReader D hγ V hδ n) ∧
      ∀ᵐ ω ∂P, l43qPieceReader D hγ V hδ n
          (restrictTo (GMS4c.thickOpen (l43qPiece V n) δ) (l43qZeroField B₀ B₀' X₀ γ ω)) =
        (CellScaling.lqgArea γ (l43qZeroField B₀ B₀' X₀ γ ω)).restrict (l43qPiece V n) :=
  Classical.choose_spec
    (exists_zeroCone_areaReader_of_bounded D hγ (l43qPiece V n) (l43qPiece_bounded V n) hδ)

/-- **The area reader for an arbitrary open set.** -/
def l43qAreaReader
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (V : TopologicalSpace.Opens ℂ) {δ : ℝ} (hδ : 0 < δ)
    (T : DistOn (GMS4c.thickOpen V δ)) : Measure ℂ :=
  Measure.sum fun n => (l43qPieceReader D hγ V hδ n
    (resOn (GMS4c.thickOpen (l43qPiece V n) δ) (GMS4c.thickOpen V δ) T)).restrict (l43qAnnulus n)

theorem measurable_l43qAreaReader
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (V : TopologicalSpace.Opens ℂ) {δ : ℝ} (hδ : 0 < δ) :
    Measurable (l43qAreaReader D hγ V hδ) := by
  refine Measure.measurable_of_measurable_coe _ fun s hs => ?_
  simp only [l43qAreaReader, Measure.sum_apply _ hs]
  refine Measurable.tsum fun n => ?_
  simp only [Measure.restrict_apply hs]
  exact (Measure.measurable_coe (hs.inter (measurableSet_l43qAnnulus n))).comp
    ((l43qPieceReader_spec D hγ V hδ n).1.comp (measurable_resOn _ _))

theorem ae_l43qAreaReader
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) (V : TopologicalSpace.Opens ℂ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᵐ ω ∂P, l43qAreaReader D hγ V hδ
        (restrictTo (GMS4c.thickOpen V δ) (l43qZeroField B₀ B₀' X₀ γ ω)) =
      (CellScaling.lqgArea γ (l43qZeroField B₀ B₀' X₀ γ ω)).restrict V := by
  have hall := ae_all_iff.2 fun n => (l43qPieceReader_spec D hγ V hδ n).2
  filter_upwards [hall] with ω hω
  unfold l43qAreaReader
  have hres : ∀ n, resOn (GMS4c.thickOpen (l43qPiece V n) δ) (GMS4c.thickOpen V δ)
      (restrictTo (GMS4c.thickOpen V δ) (l43qZeroField B₀ B₀' X₀ γ ω)) =
      restrictTo (GMS4c.thickOpen (l43qPiece V n) δ) (l43qZeroField B₀ B₀' X₀ γ ω) :=
    fun n => resOn_restrictTo (thickOpen_mono (l43qPiece_le V n) δ) _
  simp_rw [hres, hω]
  exact sum_restrict_piece_annulus _ V

/-- **the H2** `GMS4.Canonical.ThickGMCReaders D`: a Borel thickened-field GMC reader for every open set
and every thickening radius. -/
def thickGMCReaders
    (D : IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hγ : γ ∈ Ioo (0 : ℝ) 2) : GMS4.Canonical.ThickGMCReaders D :=
  fun V _δ hδ =>
    { reconstruct := l43qAreaReader D hγ V hδ
      measurable_reconstruct := measurable_l43qAreaReader D hγ V hδ
      ae_reconstruct := ae_l43qAreaReader D hγ V hδ }

end MatedCRTHarmonic.GMS4cQ
