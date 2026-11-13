/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.GMS.CodeMeasurableLocal at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.GMS.CodingDef
import Mathlib.Util.AssertNoSorry

/-!
# Local analysis of GMS's metric `d^CC`

This file supplies the three local facts about `CellConfig.dCC` on which the measurability of the
labelled coding rests.

* **Extraction** (`CellConfig.exists_admissible_of_dCC_lt`).  If `d^CC(H,H')` is small then, at
  some radius `r ≥ R`, there is an admissible homeomorphism of small distortion.  The proof needs no
  measurability of the integrand of `d^CC`: were the integrand at least `c` on all of `[R, R+1]`,
  the lower Lebesgue integral would be at least `c`.
* **Interior transfer** (`CellConfig.ball_subset_mapCell`, `CellConfig.transfer`).  If
  `B_δ(q) ⊆ K ∈ H`, `f` is admissible at radius `r` and moves points by at most `η < δ`, then
  `B_{δ−η}(q) ⊆ f(K)`.  Proof: otherwise an open set `U` near `q` misses `f(K)`; every cell of `H'`
  meeting `U` is `f(L)` for a cell `L ≠ K` of `H`, and `f⁻¹(U) ⊆ ⋃ (L ∩ K)`, a finite union of
  Lebesgue-null sets — impossible for a nonempty open set.  No fixed-point theorem is used.
* **Openness** (`isOpen_commonInteriorSet`).  The configurations having a cell that contains two
  prescribed points in its interior form a `d^CC`-open set.

Only the defining clauses of `IsCellConfiguration` are used.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal NNReal

namespace ReflectedGMS.GMS

namespace CellConfig

/-! ### Images of cells -/

theorem coe_mapCell_eq_image (f : Plane ≃ₜ Plane) (K : Cell) :
    (mapCell f K : Set Plane) = f '' (K : Set Plane) :=
  TopologicalSpace.NonemptyCompacts.coe_map _ _

theorem mapCell_symm_mapCell (f : Plane ≃ₜ Plane) (K : Cell) :
    mapCell f.symm (mapCell f K) = K :=
  TopologicalSpace.NonemptyCompacts.ext (by simp [coe_mapCell_eq_image, image_image])

theorem mapCell_mapCell_symm (f : Plane ≃ₜ Plane) (K : Cell) :
    mapCell f (mapCell f.symm K) = K :=
  TopologicalSpace.NonemptyCompacts.ext (by simp [coe_mapCell_eq_image, image_image])

theorem mapCell_refl (K : Cell) : mapCell (Homeomorph.refl Plane) K = K :=
  TopologicalSpace.NonemptyCompacts.ext (by simp [coe_mapCell_eq_image])

/-! ### `d^CC(H,H) = 0` -/

theorem admissibleAt_refl (H : CellConfig) (r : ℝ) :
    AdmissibleAt H H r (Homeomorph.refl Plane) := by
  refine ⟨fun K hK => ?_, fun K hK => ?_, fun K _ K' _ h => ?_, fun K _ K' _ h => ?_⟩
  · rwa [mapCell_refl]
  · rwa [Homeomorph.refl_symm, mapCell_refl]
  · rwa [mapCell_refl, mapCell_refl]
  · rwa [Homeomorph.refl_symm, mapCell_refl, mapCell_refl]

theorem distortion_refl (H : CellConfig) (r : ℝ) :
    distortion H H r (Homeomorph.refl Plane) = 0 := by
  simp [distortion, mapCell_refl]

theorem dCC_self (H : CellConfig) : dCC H H = 0 := by
  have h : ∀ r : ℝ, min (ENNReal.ofReal (Real.exp (-r)))
      (⨅ (f : Plane ≃ₜ Plane) (_ : AdmissibleAt H H r f), distortion H H r f) ≤ 0 := fun r =>
    (min_le_right _ _).trans ((iInf₂_le (Homeomorph.refl Plane) (admissibleAt_refl H r)).trans
      (distortion_refl H r).le)
  refine nonpos_iff_eq_zero.1 ?_
  calc dCC H H ≤ ∫⁻ _ in Ioi (0 : ℝ), (0 : ℝ≥0∞) := lintegral_mono h
    _ = 0 := lintegral_zero

/-! ### Extraction of an admissible homeomorphism -/

/-- **Extraction, first form.**  If `d^CC(H,H') < c`, then on every unit interval `[R, R+1]` with
`R > 0` the integrand of `d^CC` drops below `c` somewhere.  No measurability of the integrand is
needed: the lower Lebesgue integral dominates `c · 1_{[R,R+1]}`. -/
theorem exists_mem_Icc_integrand_lt {H H' : CellConfig} {R : ℝ} (hR : 0 < R) {c : ℝ≥0∞}
    (hc : dCC H H' < c) :
    ∃ r ∈ Icc R (R + 1), min (ENNReal.ofReal (Real.exp (-r)))
      (⨅ (f : Plane ≃ₜ Plane) (_ : AdmissibleAt H H' r f), distortion H H' r f) < c := by
  by_contra hcon
  push_neg at hcon
  have hlt : c < c := calc
    c = ∫⁻ _ in Icc R (R + 1), c := by
        rw [setLIntegral_const, Real.volume_Icc, add_sub_cancel_left, ENNReal.ofReal_one,
          mul_one]
    _ ≤ ∫⁻ r in Icc R (R + 1), min (ENNReal.ofReal (Real.exp (-r)))
          (⨅ (f : Plane ≃ₜ Plane) (_ : AdmissibleAt H H' r f), distortion H H' r f) :=
        lintegral_mono_ae ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall hcon))
    _ ≤ ∫⁻ r in Ioi (0 : ℝ), min (ENNReal.ofReal (Real.exp (-r)))
          (⨅ (f : Plane ≃ₜ Plane) (_ : AdmissibleAt H H' r f), distortion H H' r f) :=
        lintegral_mono_set fun x hx => lt_of_lt_of_le hR hx.1
    _ = dCC H H' := rfl
    _ < c := hc
  exact lt_irrefl c hlt

/-- **Extraction.**  For every `R > 0` and `η > 0` there is `ε > 0` such that `d^CC(H,H') < ε`
yields, at some radius `r ≥ R`, an admissible homeomorphism of distortion `< η`. -/
theorem exists_admissible_of_dCC_lt {R η : ℝ} (hR : 0 < R) (hη : 0 < η) :
    ∃ ε : ℝ≥0∞, 0 < ε ∧ ∀ H H' : CellConfig, dCC H H' < ε →
      ∃ r, R ≤ r ∧ ∃ f : Plane ≃ₜ Plane, AdmissibleAt H H' r f ∧
        distortion H H' r f < ENNReal.ofReal η := by
  refine ⟨min (ENNReal.ofReal (Real.exp (-(R + 1)))) (ENNReal.ofReal η),
    lt_min (ENNReal.ofReal_pos.2 (Real.exp_pos _)) (ENNReal.ofReal_pos.2 hη), fun H H' hc => ?_⟩
  obtain ⟨r, hr, hlt⟩ := exists_mem_Icc_integrand_lt hR hc
  have hexp : min (ENNReal.ofReal (Real.exp (-(R + 1)))) (ENNReal.ofReal η) ≤
      ENNReal.ofReal (Real.exp (-r)) :=
    (min_le_left _ _).trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith [hr.2])))
  have hinf := (min_lt_iff.1 hlt).resolve_left (not_lt.2 hexp)
  obtain ⟨f, hf⟩ := iInf_lt_iff.1 hinf
  obtain ⟨hadm, hlt'⟩ := iInf_lt_iff.1 hf
  exact ⟨r, hr.1, f, hadm, hlt'.trans_le (min_le_right _ _)⟩

/-- Small distortion bounds the displacement of every point. -/
theorem dist_lt_of_distortion_lt {H H' : CellConfig} {r η : ℝ} {f : Plane ≃ₜ Plane}
    (h : distortion H H' r f < ENNReal.ofReal η) (z : Plane) : dist z (f z) < η :=
  edist_lt_ofReal.1 (lt_of_le_of_lt ((le_iSup (fun z : Plane => edist z (f z)) z).trans
    le_self_add) h)

/-- Small distortion bounds the change of the conductance of every adjacent pair of `H(B_r(0))`. -/
theorem abs_sub_lt_of_distortion_lt {H H' : CellConfig} {r η : ℝ} (hη : 0 < η)
    {f : Plane ≃ₜ Plane} (h : distortion H H' r f < ENNReal.ofReal η) {K K' : Cell}
    (hK : K ∈ H.restrict (ball 0 r)) (hK' : K' ∈ H.restrict (ball 0 r)) (hadj : H.Adj K K') :
    |H.c K K' - H'.c (mapCell f K) (mapCell f K')| < η := by
  have hle : ENNReal.ofReal |H.c K K' - H'.c (mapCell f K) (mapCell f K')| ≤
      distortion H H' r f := by
    refine le_trans ?_ le_add_self
    exact le_iSup₂_of_le K hK (le_iSup₂_of_le K' hK' (le_iSup_of_le hadj le_rfl))
  exact (ENNReal.ofReal_lt_ofReal_iff hη).1 (hle.trans_lt h)

/-! ### Interior transfer -/

/-- Two cells of a cell configuration sharing an interior point coincide. -/
theorem eq_of_interior_mem {H : CellConfig} (hH : H.IsCellConfiguration) {K K' : Cell}
    (hK : K ∈ H.cells) (hK' : K' ∈ H.cells) {p : Plane} (hp : p ∈ interior (K : Set Plane))
    (hp' : p ∈ interior (K' : Set Plane)) : K = K' := by
  by_contra hne
  have hpos : 0 < volume (interior (K : Set Plane) ∩ interior (K' : Set Plane)) :=
    (isOpen_interior.inter isOpen_interior).measure_pos volume ⟨p, hp, hp'⟩
  exact hpos.ne' (measure_mono_null (inter_subset_inter interior_subset interior_subset)
    (hH.volume_inter K hK K' hK' hne))

/-- **The geometric lemma.**  If `B_δ(q) ⊆ K ∈ H`, `f` is admissible at radius `r`, moves every
point by at most `η`, and `B_{δ−η}(q) ⊆ B_r(0)`, then `B_{δ−η}(q) ⊆ f(K)`. -/
theorem ball_subset_mapCell {H H' : CellConfig} (hH : H.IsCellConfiguration)
    (hH' : H'.IsCellConfiguration) {r η δ : ℝ} {f : Plane ≃ₜ Plane} (hf : AdmissibleAt H H' r f)
    (hfη : ∀ z, dist z (f z) ≤ η) {K : Cell} (hK : K ∈ H.cells) {q : Plane}
    (hqK : ball q δ ⊆ (K : Set Plane)) (hqr : ball q (δ - η) ⊆ ball (0 : Plane) r) :
    ball q (δ - η) ⊆ (mapCell f K : Set Plane) := by
  intro p hp
  by_contra hpK
  have hcl : IsClosed (mapCell f K : Set Plane) := (mapCell f K).isCompact.isClosed
  obtain ⟨W, hW, hWfin⟩ := hH'.locallyFinite p
  obtain ⟨U, hUsub, hUo, hpU⟩ := _root_.mem_nhds_iff.1
    (inter_mem hW (inter_mem (isOpen_ball.mem_nhds hp) (hcl.isOpen_compl.mem_nhds hpK)))
  have hUball : U ⊆ ball (0 : Plane) r := fun x hx => hqr (hUsub hx).2.1
  -- the cells of `H'` meeting `U` pull back to cells of `H` other than `K`
  have hpull : ∀ L' ∈ H'.restrict U, mapCell f.symm L' ∈ H.cells ∧ mapCell f.symm L' ≠ K := by
    intro L' hL'
    have hL'r : L' ∈ H'.restrict (ball (0 : Plane) r) :=
      ⟨hL'.1, hL'.2.mono (inter_subset_inter_right _ hUball)⟩
    refine ⟨(hf.2.1 L' hL'r).1, fun heq => ?_⟩
    obtain ⟨x, hxL', hxU⟩ := hL'.2
    have hxK : x ∈ (mapCell f K : Set Plane) := by
      rw [← heq, mapCell_mapCell_symm]
      exact hxL'
    exact (hUsub hxU).2.2 hxK
  have hsub : f ⁻¹' U ⊆ ⋃ L' ∈ H'.restrict U, ((mapCell f.symm L' : Set Plane) ∩ K) := by
    intro y hy
    have hmem : f y ∈ ⋃ L ∈ H'.cells, (L : Set Plane) := by
      rw [hH'.iUnion_eq_univ]
      exact mem_univ _
    obtain ⟨L', hL'c, hyL'⟩ := mem_iUnion₂.1 hmem
    have hL'U : L' ∈ H'.restrict U := ⟨hL'c, f y, hyL', hy⟩
    refine mem_iUnion₂.2 ⟨L', hL'U, ?_, ?_⟩
    · rw [coe_mapCell_eq_image]
      exact ⟨f y, hyL', f.symm_apply_apply y⟩
    · apply hqK
      rw [mem_ball]
      have h1 : dist (f y) q < δ - η := (hUsub hy).2.1
      have h2 : dist y (f y) ≤ η := hfη y
      calc dist y q ≤ dist y (f y) + dist (f y) q := dist_triangle _ _ _
        _ < η + (δ - η) := add_lt_add_of_le_of_lt h2 h1
        _ = δ := by ring
  have hfin : (H'.restrict U).Finite :=
    hWfin.subset fun L' hL' =>
      ⟨hL'.1, hL'.2.mono (inter_subset_inter_right _ fun x hx => (hUsub hx).1)⟩
  have hnull : volume (⋃ L' ∈ H'.restrict U, ((mapCell f.symm L' : Set Plane) ∩ K)) = 0 :=
    (measure_biUnion_null_iff hfin.countable).2 fun L' hL' =>
      hH.volume_inter _ (hpull L' hL').1 K hK (hpull L' hL').2
  have hpos : 0 < volume (f ⁻¹' U) :=
    (hUo.preimage f.continuous).measure_pos volume ⟨f.symm p, by simpa using hpU⟩
  exact hpos.ne' (measure_mono_null hsub hnull)

/-- **Interior transfer.**  If `B_δ(p) ⊆ K ∈ H`, `‖p‖ + δ ≤ r` and `f` is admissible at radius `r`
and moves every point by less than `η ≤ δ/2`, then `K ∈ H(B_r(0))`, `f(K)` is a cell of `H'`, and
`p` lies in the interior of `f(K)`. -/
theorem transfer {H H' : CellConfig} (hH : H.IsCellConfiguration) (hH' : H'.IsCellConfiguration)
    {r η δ : ℝ} {f : Plane ≃ₜ Plane} (hf : AdmissibleAt H H' r f) (hfη : ∀ z, dist z (f z) < η)
    (hηδ : η ≤ δ / 2) {K : Cell} (hK : K ∈ H.cells) {p : Plane}
    (hpK : ball p δ ⊆ (K : Set Plane)) (hpr : ‖p‖ + δ ≤ r) :
    K ∈ H.restrict (ball (0 : Plane) r) ∧ mapCell f K ∈ H'.cells ∧
      p ∈ interior (mapCell f K : Set Plane) := by
  have hη : 0 < η := lt_of_le_of_lt dist_nonneg (hfη 0)
  have hδ : 0 < δ := by linarith
  have hKr : K ∈ H.restrict (ball (0 : Plane) r) :=
    ⟨hK, p, hpK (mem_ball_self hδ), mem_ball_zero_iff.2 (by linarith)⟩
  refine ⟨hKr, (hf.1 K hKr).1, ?_⟩
  have hsub : ball p (δ - η) ⊆ (mapCell f K : Set Plane) := by
    refine ball_subset_mapCell hH hH' hf (fun z => (hfη z).le) hK hpK ?_
    intro x hx
    rw [mem_ball] at hx
    rw [mem_ball_zero_iff]
    have htri := dist_triangle x p 0
    rw [dist_zero_right, dist_zero_right] at htri
    linarith
  exact mem_interior.2 ⟨ball p (δ - η), hsub, isOpen_ball, mem_ball_self (by linarith)⟩

end CellConfig

/-! ### Open sets of the `d^CC` topology -/

/-- A set containing a `d^CC`-ball around each of its points is open. -/
theorem isOpen_of_forall_dCC {U : Set GMSSpace}
    (h : ∀ H ∈ U, ∃ ε : ℝ≥0∞, 0 < ε ∧ ∀ H' : GMSSpace, CellConfig.dCC H.1 H'.1 < ε → H' ∈ U) :
    IsOpen U := by
  refine isOpen_iff_forall_mem_open.2 fun H hH => ?_
  obtain ⟨ε, hε, hU⟩ := h H hH
  refine ⟨{H' | CellConfig.dCC H.1 H'.1 < ε}, fun H' hH' => hU H' hH', ?_, ?_⟩
  · exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨H, ε, hε, rfl⟩
  · show CellConfig.dCC H.1 H.1 < ε
    rw [CellConfig.dCC_self]
    exact hε

/-- The configurations having a cell that contains both `p₁` and `p₂` in its interior. -/
def commonInteriorSet (p₁ p₂ : Plane) : Set GMSSpace :=
  {H | ∃ K ∈ H.1.cells, p₁ ∈ interior (K : Set Plane) ∧ p₂ ∈ interior (K : Set Plane)}

/-- The configurations having a cell that contains `p` in its interior. -/
def interiorSet (p : Plane) : Set GMSSpace :=
  {H | ∃ K ∈ H.1.cells, p ∈ interior (K : Set Plane)}

theorem mem_interiorSet {p : Plane} {H : GMSSpace} :
    H ∈ interiorSet p ↔ ∃ K ∈ H.1.cells, p ∈ interior (K : Set Plane) :=
  Iff.rfl

theorem isOpen_commonInteriorSet (p₁ p₂ : Plane) : IsOpen (commonInteriorSet p₁ p₂) := by
  refine isOpen_of_forall_dCC fun H hH => ?_
  obtain ⟨K, hK, h₁, h₂⟩ := hH
  obtain ⟨δ₁, hδ₁, hb₁⟩ := Metric.isOpen_iff.1 isOpen_interior p₁ h₁
  obtain ⟨δ₂, hδ₂, hb₂⟩ := Metric.isOpen_iff.1 isOpen_interior p₂ h₂
  have hn₁ := norm_nonneg p₁
  have hn₂ := norm_nonneg p₂
  have hδ : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  obtain ⟨ε, hε, hspec⟩ := CellConfig.exists_admissible_of_dCC_lt
    (R := ‖p₁‖ + ‖p₂‖ + min δ₁ δ₂ + 1) (η := min δ₁ δ₂ / 2) (by linarith) (half_pos hδ)
  refine ⟨ε, hε, fun H' hH' => ?_⟩
  obtain ⟨r, hRr, f, hf, hdist⟩ := hspec H.1 H'.1 hH'
  have hfη := CellConfig.dist_lt_of_distortion_lt hdist
  obtain ⟨-, hc, hi₁⟩ := CellConfig.transfer H.2 H'.2 hf hfη (δ := min δ₁ δ₂) le_rfl hK
    ((ball_subset_ball (min_le_left _ _)).trans (hb₁.trans interior_subset)) (by linarith)
  obtain ⟨-, -, hi₂⟩ := CellConfig.transfer H.2 H'.2 hf hfη (δ := min δ₁ δ₂) le_rfl hK
    ((ball_subset_ball (min_le_right _ _)).trans (hb₂.trans interior_subset)) (by linarith)
  exact ⟨_, hc, hi₁, hi₂⟩

theorem interiorSet_eq_commonInteriorSet (p : Plane) :
    interiorSet p = commonInteriorSet p p := by
  ext H
  simp only [interiorSet, commonInteriorSet, and_self]

theorem isOpen_interiorSet (p : Plane) : IsOpen (interiorSet p) := by
  rw [interiorSet_eq_commonInteriorSet]
  exact isOpen_commonInteriorSet p p

end ReflectedGMS.GMS

assert_no_sorry ReflectedGMS.GMS.CellConfig.dCC_self
assert_no_sorry ReflectedGMS.GMS.CellConfig.exists_admissible_of_dCC_lt
assert_no_sorry ReflectedGMS.GMS.CellConfig.ball_subset_mapCell
assert_no_sorry ReflectedGMS.GMS.CellConfig.transfer
assert_no_sorry ReflectedGMS.GMS.isOpen_commonInteriorSet
assert_no_sorry ReflectedGMS.GMS.isOpen_interiorSet

#print axioms ReflectedGMS.GMS.CellConfig.exists_admissible_of_dCC_lt
#print axioms ReflectedGMS.GMS.CellConfig.ball_subset_mapCell
#print axioms ReflectedGMS.GMS.isOpen_commonInteriorSet
