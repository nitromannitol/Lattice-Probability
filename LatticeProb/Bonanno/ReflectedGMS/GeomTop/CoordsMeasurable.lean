/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.GeomTop.CoordsMeasurable at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.GeomTop.Statement
import LatticeProb.Bonanno.ReflectedGMS.GMS.CodeMeasurable
import LatticeProb.Bonanno.ReflectedGMS.MeasureTheory.HausdorffPlane
import Mathlib.Util.AssertNoSorry

/-!
# The auxiliary rational-label coordinates are `B_sing`-measurable (Proposition 2.7)

`GeomTop.measurable_coords`: the coding `coords : SingSpace → Code.RawCode` of the
geometric-topology revision is measurable from `B_sing = B(τ_sing)` to the product σ-algebra of
`Code.RawCode` (manuscript Proposition 2.7, `work/geomtop/manuscript-text.txt:492-519`).

The route is the one of the GMS analogue (`GMS/CodeMeasurable.lean`), with the local analysis of
`d^CC` replaced by that of `d_sing`:

* **Extraction** (`CoordsMeasurable.exists_matching_of_dSing_lt`).  If on a radius interval
  `[a,b]` the finite restriction of `H` to the test windows of the tuple `q(j)` has at most `N + 1`
  cells, then every `H'` with `d_sing(H,H')` small admits, at some radius `r ∈ [a,b]`, a whole-cell
  matching of `H(U_{q(j),r})` onto `H'(U_{q(j),r})` of small distortion.  As in the manuscript's
  Lemma 2.3, no measurability of the integrand of `d_sing` is needed: a lower Lebesgue integral
  bounds a constant from below on `[a,b]`.
* **Regular windows** (`CoordsMeasurable.exists_window`).  Every cell `K` has a rational point in
  its interior outside the singular-set witness, around which `H` is locally finite (manuscript
  line 294: each cell has an interior point outside `S(H)`).  A window made of small disks around
  such points of finitely many cells has a finite restriction containing those cells, for every
  radius in an interval.  This is how a rational point `q` that is itself an accumulation point is
  handled (manuscript lines 510-512): the matching is obtained from a *different*, regular interior
  point of the same whole cell.
* **Interior transfer** (`CoordsMeasurable.ball_subset_mapCell_of_dist_lt`).  A matching moves every
  point by less than `η`, and so does its inverse; hence `B_{δ-η}(q) ⊆ f(B_δ(q))`.  Nothing about
  the configurations is used, and no fixed-point theorem.
* Continuity of the cell containing a point in its interior (Hausdorff metric) and of the
  conductance between two such cells, on the open sets where they exist; the label events are finite
  Boolean combinations of these open sets.
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology Metric
open scoped ENNReal NNReal

namespace ReflectedGMS.GeomTop

open GMS

namespace CoordsMeasurable

/-! ### The distance vanishes on the diagonal -/

theorem matchesWhole_refl (F : CellConfig) : MatchesWhole F F (Homeomorph.refl Plane) := by
  refine ⟨fun K hK => ?_, fun K hK => ?_, fun K _ K' _ => ?_⟩
  · rwa [CellConfig.mapCell_refl]
  · rwa [Homeomorph.refl_symm, CellConfig.mapCell_refl]
  · rw [CellConfig.mapCell_refl, CellConfig.mapCell_refl]

theorem wholeDistortion_refl (F : CellConfig) :
    wholeDistortion F F (Homeomorph.refl Plane) = 0 := by
  simp [wholeDistortion, CellConfig.mapCell_refl]

theorem restrictionDist_self (o : Option CellConfig) : restrictionDist o o = 0 := by
  cases o with
  | none => rfl
  | some F =>
    refine nonpos_iff_eq_zero.1 ?_
    exact (min_le_right _ _).trans ((iInf₂_le (Homeomorph.refl Plane) (matchesWhole_refl F)).trans
      (wholeDistortion_refl F).le)

theorem dSing_self (H : CellConfig) : dSing H H = 0 := by
  simp [dSing, restrictionDist_self]

/-- A set containing a `d_sing`-ball around each of its points is `τ_sing`-open. -/
theorem isOpen_of_forall_dSing {U : Set SingSpace}
    (h : ∀ H ∈ U, ∃ ε : ℝ≥0∞, 0 < ε ∧ ∀ H' : SingSpace, dSing H.1 H'.1 < ε → H' ∈ U) :
    IsOpen U := by
  refine isOpen_iff_forall_mem_open.2 fun H hH => ?_
  obtain ⟨ε, hε, hU⟩ := h H hH
  refine ⟨{H' | dSing H.1 H'.1 < ε}, fun H' hH' => hU H' hH', ?_, ?_⟩
  · exact TopologicalSpace.isOpen_generateFrom_of_mem ⟨H, ε, hε, rfl⟩
  · show dSing H.1 H.1 < ε
    rw [dSing_self]
    exact hε

/-! ### Extraction of a whole-cell matching -/

/-- The integrand of the `(j, N)` term of `d_sing`. -/
noncomputable def integrand (H H' : CellConfig) (j N : ℕ) (r : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (-r)) *
    restrictionDist (CellConfigOps.capped H (N + 1) (window (ratTuple j) r))
      (CellConfigOps.capped H' (N + 1) (window (ratTuple j) r))

theorem term_le_dSing (H H' : CellConfig) (j N : ℕ) :
    (2 : ℝ≥0∞)⁻¹ ^ ((j + 1) + (N + 1)) * ∫⁻ r in Ioi (0 : ℝ), integrand H H' j N r ≤
      dSing H H' := by
  calc (2 : ℝ≥0∞)⁻¹ ^ ((j + 1) + (N + 1)) * ∫⁻ r in Ioi (0 : ℝ), integrand H H' j N r
      ≤ ∑' N' : ℕ, (2 : ℝ≥0∞)⁻¹ ^ ((j + 1) + (N' + 1)) *
          ∫⁻ r in Ioi (0 : ℝ), integrand H H' j N' r :=
        ENNReal.le_tsum (f := fun N' : ℕ => (2 : ℝ≥0∞)⁻¹ ^ ((j + 1) + (N' + 1)) *
          ∫⁻ r in Ioi (0 : ℝ), integrand H H' j N' r) N
    _ ≤ ∑' (j' : ℕ) (N' : ℕ), (2 : ℝ≥0∞)⁻¹ ^ ((j' + 1) + (N' + 1)) *
          ∫⁻ r in Ioi (0 : ℝ), integrand H H' j' N' r :=
        ENNReal.le_tsum (f := fun j' : ℕ => ∑' N' : ℕ, (2 : ℝ≥0∞)⁻¹ ^ ((j' + 1) + (N' + 1)) *
          ∫⁻ r in Ioi (0 : ℝ), integrand H H' j' N' r) j
    _ = dSing H H' := rfl

/-- **Extraction, first form.**  If `d_sing(H,H')` is below `2^{-j-N-2} · c · (b - a)`, the
`(j,N)` integrand drops below `c` somewhere on `[a,b]`.  No measurability of the integrand is
needed: the lower Lebesgue integral dominates `c · 1_{[a,b]}`. -/
theorem exists_mem_Icc_integrand_lt {H H' : CellConfig} {j N : ℕ} {a b : ℝ} (ha : 0 < a)
    (hab : a < b) {c : ℝ≥0∞}
    (hc : dSing H H' < (2 : ℝ≥0∞)⁻¹ ^ ((j + 1) + (N + 1)) * (c * ENNReal.ofReal (b - a))) :
    ∃ r ∈ Icc a b, integrand H H' j N r < c := by
  by_contra hcon
  push_neg at hcon
  have hle : c * ENNReal.ofReal (b - a) ≤ ∫⁻ r in Ioi (0 : ℝ), integrand H H' j N r := calc
    c * ENNReal.ofReal (b - a) = ∫⁻ _ in Icc a b, c := by
        rw [setLIntegral_const, Real.volume_Icc]
    _ ≤ ∫⁻ r in Icc a b, integrand H H' j N r :=
        lintegral_mono_ae ((ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall hcon))
    _ ≤ ∫⁻ r in Ioi (0 : ℝ), integrand H H' j N r :=
        lintegral_mono_set fun x hx => lt_of_lt_of_le ha hx.1
  have hle' : (2 : ℝ≥0∞)⁻¹ ^ ((j + 1) + (N + 1)) * (c * ENNReal.ofReal (b - a)) ≤ dSing H H' :=
    le_trans (by gcongr) (term_le_dSing H H' j N)
  exact lt_irrefl _ (hc.trans_le hle')

/-- **Extraction.**  Suppose that for every radius `r ∈ [a,b]` the restriction of `H` to the window
`U_{q(j),r}` has at most `N + 1` cells.  Then for every `η > 0` there is `ε > 0` such that
`d_sing(H,H') < ε` yields, at some `r ∈ [a,b]`, a whole-cell matching of `H(U_{q(j),r})` onto
`H'(U_{q(j),r})` of distortion `< η`. -/
theorem exists_matching_of_dSing_lt {H : CellConfig} {j N : ℕ} {a b : ℝ} (ha : 0 < a)
    (hab : a < b)
    (hfin : ∀ r ∈ Icc a b, (H.restrict (window (ratTuple j) r)).encard ≤ ((N + 1 : ℕ) : ℕ∞))
    {η : ℝ} (hη : 0 < η) :
    ∃ ε : ℝ≥0∞, 0 < ε ∧ ∀ H' : CellConfig, dSing H H' < ε →
      ∃ r ∈ Icc a b, ∃ f : Plane ≃ₜ Plane,
        MatchesWhole (CellConfigOps.restrictConfig H (window (ratTuple j) r))
          (CellConfigOps.restrictConfig H' (window (ratTuple j) r)) f ∧
        wholeDistortion (CellConfigOps.restrictConfig H (window (ratTuple j) r))
          (CellConfigOps.restrictConfig H' (window (ratTuple j) r)) f < ENNReal.ofReal η := by
  have hη₁ : 0 < min η 1 := lt_min hη one_pos
  have h2 : (2 : ℝ≥0∞)⁻¹ ^ ((j + 1) + (N + 1)) ≠ 0 := by simp
  have hc0 : ENNReal.ofReal (Real.exp (-b)) * ENNReal.ofReal (min η 1) ≠ 0 :=
    (ENNReal.mul_pos (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne'
      (ENNReal.ofReal_pos.2 hη₁).ne').ne'
  have hba : ENNReal.ofReal (b - a) ≠ 0 := (ENNReal.ofReal_pos.2 (sub_pos.2 hab)).ne'
  refine ⟨(2 : ℝ≥0∞)⁻¹ ^ ((j + 1) + (N + 1)) *
      ((ENNReal.ofReal (Real.exp (-b)) * ENNReal.ofReal (min η 1)) * ENNReal.ofReal (b - a)),
    ENNReal.mul_pos h2 (ENNReal.mul_pos hc0 hba).ne', fun H' hH' => ?_⟩
  obtain ⟨r, hr, hlt⟩ := exists_mem_Icc_integrand_lt ha hab hH'
  refine ⟨r, hr, ?_⟩
  have hδ : restrictionDist (CellConfigOps.capped H (N + 1) (window (ratTuple j) r))
      (CellConfigOps.capped H' (N + 1) (window (ratTuple j) r)) < ENNReal.ofReal (min η 1) := by
    by_contra hge
    push_neg at hge
    have hexp : ENNReal.ofReal (Real.exp (-b)) ≤ ENNReal.ofReal (Real.exp (-r)) :=
      ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith [hr.2]))
    exact (not_le.2 hlt) (mul_le_mul' hexp hge)
  have hcapH : CellConfigOps.capped H (N + 1) (window (ratTuple j) r) =
      some (CellConfigOps.restrictConfig H (window (ratTuple j) r)) := by
    unfold CellConfigOps.capped
    rw [if_pos (hfin r hr)]
  have hle1 : ENNReal.ofReal (min η 1) ≤ 1 := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (min_le_right _ _)
  rw [hcapH] at hδ
  cases hcap : CellConfigOps.capped H' (N + 1) (window (ratTuple j) r) with
  | none =>
    rw [hcap] at hδ
    exact absurd (hδ.trans_le hle1) (lt_irrefl 1)
  | some F' =>
    have hF' : F' = CellConfigOps.restrictConfig H' (window (ratTuple j) r) := by
      unfold CellConfigOps.capped at hcap
      split_ifs at hcap
      exact (Option.some.inj hcap).symm
    rw [hcap, hF'] at hδ
    have hinf := (min_lt_iff.1 hδ).resolve_left (not_lt.2 hle1)
    obtain ⟨f, hf⟩ := iInf_lt_iff.1 hinf
    obtain ⟨hm, hlt'⟩ := iInf_lt_iff.1 hf
    exact ⟨f, hm, hlt'.trans_le (ENNReal.ofReal_le_ofReal (min_le_left _ _))⟩

/-! ### Consequences of a matching of small distortion -/

/-- Small distortion bounds the displacement of every point. -/
theorem dist_lt_of_wholeDistortion_lt {F F' : CellConfig} {f : Plane ≃ₜ Plane} {η : ℝ}
    (h : wholeDistortion F F' f < ENNReal.ofReal η) (z : Plane) : dist (f z) z < η :=
  edist_lt_ofReal.1 (lt_of_le_of_lt ((le_iSup (fun z : Plane => edist (f z) z) z).trans
    le_self_add) h)

/-- Small distortion bounds the change of the conductance of every adjacent pair of `F`. -/
theorem abs_sub_lt_of_wholeDistortion_lt {F F' : CellConfig} {f : Plane ≃ₜ Plane} {η : ℝ}
    (hη : 0 < η) (h : wholeDistortion F F' f < ENNReal.ofReal η) {K K' : Cell}
    (hK : K ∈ F.cells) (hK' : K' ∈ F.cells) (hadj : F.Adj K K') :
    |F.c K K' - F'.c (CellConfig.mapCell f K) (CellConfig.mapCell f K')| < η := by
  have hle : ENNReal.ofReal |F.c K K' - F'.c (CellConfig.mapCell f K) (CellConfig.mapCell f K')| ≤
      wholeDistortion F F' f := by
    refine le_trans ?_ le_add_self
    exact le_iSup₂_of_le K hK (le_iSup₂_of_le K' hK' (le_iSup_of_le hadj le_rfl))
  exact (ENNReal.ofReal_lt_ofReal_iff hη).1 (hle.trans_lt h)

/-- **Interior transfer.**  A plane homeomorphism moving every point by less than `η` maps
`B_δ(q)` onto a superset of `B_{δ-η}(q)` (its inverse moves points by less than `η` too). -/
theorem ball_subset_mapCell_of_dist_lt {f : Plane ≃ₜ Plane} {η δ : ℝ}
    (hf : ∀ z, dist (f z) z < η) {K : Cell} {q : Plane} (hq : ball q δ ⊆ (K : Set Plane)) :
    ball q (δ - η) ⊆ (CellConfig.mapCell f K : Set Plane) := by
  intro y hy
  rw [CellConfig.coe_mapCell_eq_image]
  refine ⟨f.symm y, hq ?_, f.apply_symm_apply y⟩
  rw [mem_ball] at hy ⊢
  have h1 : dist y (f.symm y) < η := by
    have := hf (f.symm y)
    rwa [f.apply_symm_apply] at this
  calc dist (f.symm y) q ≤ dist (f.symm y) y + dist y q := dist_triangle _ _ _
    _ < η + (δ - η) := add_lt_add (by rwa [dist_comm]) hy
    _ = δ := by ring

theorem mem_interior_mapCell_of_dist_lt {f : Plane ≃ₜ Plane} {η δ : ℝ}
    (hf : ∀ z, dist (f z) z < η) {K : Cell} {q : Plane} (hq : ball q δ ⊆ (K : Set Plane))
    (hηδ : η < δ) : q ∈ interior (CellConfig.mapCell f K : Set Plane) :=
  mem_interior.2 ⟨ball q (δ - η), ball_subset_mapCell_of_dist_lt hf hq, isOpen_ball,
    mem_ball_self (by linarith)⟩

/-- A homeomorphism moving points by less than `η` moves every cell by at most `η` in the
Hausdorff metric. -/
theorem dist_mapCell_le {f : Plane ≃ₜ Plane} {η : ℝ} (hη : 0 ≤ η) (hf : ∀ z, dist (f z) z < η)
    (K : Cell) : dist (CellConfig.mapCell f K) K ≤ η := by
  rw [TopologicalSpace.NonemptyCompacts.dist_eq, CellConfig.coe_mapCell_eq_image]
  refine hausdorffDist_le_of_mem_dist hη ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨y, hy, (hf y).le⟩
  · intro y hy
    exact ⟨f y, mem_image_of_mem f hy, by rw [dist_comm]; exact (hf y).le⟩

theorem restrictConfig_c_of_mem {H : CellConfig} {W : Set Plane} {K K' : Cell}
    (hK : K ∈ H.restrict W) (hK' : K' ∈ H.restrict W) :
    (CellConfigOps.restrictConfig H W).c K K' = H.c K K' :=
  if_pos ⟨hK, hK'⟩

/-! ### Regular windows -/

/-- Every cell of an environment in `C_sing` contains a rational point around which the
configuration is locally finite. -/
theorem exists_ratPoint_mem_restrict_finite (H : SingSpace) {K : Cell} (hK : K ∈ H.1.cells) :
    ∃ (p : ℚ × ℚ) (ρ : ℝ), 0 < ρ ∧ ratPoint p ∈ (K : Set Plane) ∧
      (H.1.restrict (ball (ratPoint p) ρ)).Finite := by
  obtain ⟨w⟩ := H.2.witness
  have hvol : volume w.sing = 0 := volume_eq_zero_of_hausdorffMeasure_one w.hausdorff_sing
  obtain ⟨z, hzK, hzs⟩ : ∃ z ∈ interior (K : Set Plane), z ∉ w.sing := by
    by_contra hcon
    push_neg at hcon
    have hpos : 0 < volume (interior (K : Set Plane)) :=
      isOpen_interior.measure_pos volume (H.2.interior_nonempty K hK)
    exact hpos.ne' (measure_mono_null hcon hvol)
  obtain ⟨U, hU, hUfin⟩ := w.locallyFinite z hzs
  obtain ⟨n, hn⟩ := Code.exists_rationalPoint_mem (isOpen_interior.inter isOpen_interior)
    ⟨z, hzK, mem_interior_iff_mem_nhds.2 hU⟩
  obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.1 (isOpen_interior : IsOpen (interior U)) _ hn.2
  refine ⟨Code.rationalPair n, ρ, hρ, interior_subset hn.1, hUfin.subset ?_⟩
  rintro L ⟨hL, x, hxL, hx⟩
  exact ⟨hL, x, hxL, interior_subset (hball hx)⟩

theorem window_pair (p₁ p₂ : ℚ × ℚ) (r : ℝ) :
    window ⟨[p₁, p₂], List.cons_ne_nil _ _⟩ r = ball (ratPoint p₁) r ∪ ball (ratPoint p₂) r := by
  ext x
  simp [window]

/-- **Regular windows.**  For two cells `K₁, K₂` of an environment in `C_sing` there are a tuple
`q(j)`, a bound `N` and radii `0 < a < b` such that for every `r ∈ [a,b]` both cells meet the window
`U_{q(j),r}` and its restriction has at most `N + 1` cells. -/
theorem exists_window (H : SingSpace) {K₁ K₂ : Cell} (h₁ : K₁ ∈ H.1.cells)
    (h₂ : K₂ ∈ H.1.cells) :
    ∃ (j N : ℕ) (a b : ℝ), 0 < a ∧ a < b ∧ ∀ r ∈ Icc a b,
      K₁ ∈ H.1.restrict (window (ratTuple j) r) ∧ K₂ ∈ H.1.restrict (window (ratTuple j) r) ∧
      (H.1.restrict (window (ratTuple j) r)).encard ≤ ((N + 1 : ℕ) : ℕ∞) := by
  obtain ⟨p₁, ρ₁, hρ₁, hp₁, hfin₁⟩ := exists_ratPoint_mem_restrict_finite H h₁
  obtain ⟨p₂, ρ₂, hρ₂, hp₂, hfin₂⟩ := exists_ratPoint_mem_restrict_finite H h₂
  obtain ⟨j, hj⟩ : ∃ j, ratTuple j = ⟨[p₁, p₂], List.cons_ne_nil _ _⟩ :=
    ⟨_, Denumerable.ofNat_encode _⟩
  have hS : (H.1.restrict (ball (ratPoint p₁) ρ₁) ∪ H.1.restrict (ball (ratPoint p₂) ρ₂)).Finite :=
    hfin₁.union hfin₂
  have hρ : 0 < min ρ₁ ρ₂ := lt_min hρ₁ hρ₂
  refine ⟨j, (H.1.restrict (ball (ratPoint p₁) ρ₁) ∪ H.1.restrict (ball (ratPoint p₂) ρ₂)).ncard,
    min ρ₁ ρ₂ / 2, min ρ₁ ρ₂, half_pos hρ, half_lt_self hρ, fun r hr => ?_⟩
  have hr0 : 0 < r := lt_of_lt_of_le (half_pos hρ) hr.1
  rw [hj, window_pair]
  refine ⟨⟨h₁, ratPoint p₁, hp₁, Or.inl (mem_ball_self hr0)⟩,
    ⟨h₂, ratPoint p₂, hp₂, Or.inr (mem_ball_self hr0)⟩, ?_⟩
  have hsub : H.1.restrict (ball (ratPoint p₁) r ∪ ball (ratPoint p₂) r) ⊆
      H.1.restrict (ball (ratPoint p₁) ρ₁) ∪ H.1.restrict (ball (ratPoint p₂) ρ₂) := by
    rintro L ⟨hL, x, hxL, hx | hx⟩
    · exact Or.inl ⟨hL, x, hxL, ball_subset_ball (le_trans hr.2 (min_le_left _ _)) hx⟩
    · exact Or.inr ⟨hL, x, hxL, ball_subset_ball (le_trans hr.2 (min_le_right _ _)) hx⟩
  calc _ ≤ (H.1.restrict (ball (ratPoint p₁) ρ₁) ∪ H.1.restrict (ball (ratPoint p₂) ρ₂)).encard :=
        encard_le_encard hsub
    _ = ((H.1.restrict (ball (ratPoint p₁) ρ₁) ∪
          H.1.restrict (ball (ratPoint p₂) ρ₂)).ncard : ℕ∞) := hS.cast_ncard_eq.symm
    _ ≤ _ := by exact_mod_cast Nat.le_succ _

/-- **The local matching property** (manuscript Lemma 2.3, for two whole cells).  Near an
environment `H ∈ C_sing`, every environment admits a whole-cell matching, of distortion `< η`, of
finite restrictions containing two prescribed cells of `H`. -/
theorem exists_matching_near (H : SingSpace) {K₁ K₂ : Cell} (h₁ : K₁ ∈ H.1.cells)
    (h₂ : K₂ ∈ H.1.cells) {η : ℝ} (hη : 0 < η) :
    ∃ ε : ℝ≥0∞, 0 < ε ∧ ∀ H' : SingSpace, dSing H.1 H'.1 < ε →
      ∃ (W : Set Plane) (f : Plane ≃ₜ Plane), K₁ ∈ H.1.restrict W ∧ K₂ ∈ H.1.restrict W ∧
        MatchesWhole (CellConfigOps.restrictConfig H.1 W) (CellConfigOps.restrictConfig H'.1 W) f ∧
        wholeDistortion (CellConfigOps.restrictConfig H.1 W)
          (CellConfigOps.restrictConfig H'.1 W) f < ENNReal.ofReal η := by
  obtain ⟨j, N, a, b, ha, hab, hwin⟩ := exists_window H h₁ h₂
  obtain ⟨ε, hε, hspec⟩ :=
    exists_matching_of_dSing_lt ha hab (fun r hr => (hwin r hr).2.2) hη
  refine ⟨ε, hε, fun H' hH' => ?_⟩
  obtain ⟨r, hr, f, hm, hd⟩ := hspec H'.1 hH'
  exact ⟨_, f, (hwin r hr).1, (hwin r hr).2.1, hm, hd⟩

/-! ### The cell containing a point in its interior -/

/-- Two cells of an environment in `C_sing` sharing an interior point coincide. -/
theorem eq_of_interior_mem {H : CellConfig} (hH : IsSingConfiguration H) {K K' : Cell}
    (hK : K ∈ H.cells) (hK' : K' ∈ H.cells) {p : Plane} (hp : p ∈ interior (K : Set Plane))
    (hp' : p ∈ interior (K' : Set Plane)) : K = K' := by
  by_contra hne
  have hpos : 0 < volume (interior (K : Set Plane) ∩ interior (K' : Set Plane)) :=
    (isOpen_interior.inter isOpen_interior).measure_pos volume ⟨p, hp, hp'⟩
  exact hpos.ne' (measure_mono_null (inter_subset_inter interior_subset interior_subset)
    (hH.volume_inter K hK K' hK' hne))

/-- The environments having a cell that contains both `p₁` and `p₂` in its interior. -/
def commonInteriorSet (p₁ p₂ : Plane) : Set SingSpace :=
  {H | ∃ K ∈ H.1.cells, p₁ ∈ interior (K : Set Plane) ∧ p₂ ∈ interior (K : Set Plane)}

/-- The environments having a cell that contains `p` in its interior (the manuscript's `O_q`). -/
def interiorSet (p : Plane) : Set SingSpace :=
  {H | ∃ K ∈ H.1.cells, p ∈ interior (K : Set Plane)}

theorem isOpen_commonInteriorSet (p₁ p₂ : Plane) : IsOpen (commonInteriorSet p₁ p₂) := by
  refine isOpen_of_forall_dSing fun H hH => ?_
  obtain ⟨K, hK, h₁, h₂⟩ := hH
  obtain ⟨δ₁, hδ₁, hb₁⟩ := Metric.isOpen_iff.1 isOpen_interior p₁ h₁
  obtain ⟨δ₂, hδ₂, hb₂⟩ := Metric.isOpen_iff.1 isOpen_interior p₂ h₂
  have hδ : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  obtain ⟨ε, hε, hspec⟩ := exists_matching_near H hK hK (half_pos hδ)
  refine ⟨ε, hε, fun H' hH' => ?_⟩
  obtain ⟨W, f, hKW, -, hm, hd⟩ := hspec H' hH'
  have hfη := dist_lt_of_wholeDistortion_lt hd
  exact ⟨_, (hm.1 K hKW).1,
    mem_interior_mapCell_of_dist_lt hfη
      ((ball_subset_ball (min_le_left _ _)).trans (hb₁.trans interior_subset))
      (half_lt_self hδ),
    mem_interior_mapCell_of_dist_lt hfη
      ((ball_subset_ball (min_le_right _ _)).trans (hb₂.trans interior_subset))
      (half_lt_self hδ)⟩

theorem interiorSet_eq_commonInteriorSet (p : Plane) :
    interiorSet p = commonInteriorSet p p := by
  ext H
  simp only [interiorSet, commonInteriorSet, and_self]

/-- **`O_q` is open** (first sentence of the proof of Proposition 2.7). -/
theorem isOpen_interiorSet (p : Plane) : IsOpen (interiorSet p) := by
  rw [interiorSet_eq_commonInteriorSet]
  exact isOpen_commonInteriorSet p p

/-- The reference cell `{0}`, used as the value off `interiorSet p`. -/
noncomputable def refCell : Cell := {(0 : Plane)}

/-- The cell containing `p` in its interior (unique when it exists), `refCell` otherwise. -/
noncomputable def interiorCell (p : Plane) (H : SingSpace) : Cell :=
  open Classical in
  if h : ∃ K ∈ H.1.cells, p ∈ interior (K : Set Plane) then h.choose else refCell

theorem interiorCell_spec {p : Plane} {H : SingSpace} (hH : H ∈ interiorSet p) :
    interiorCell p H ∈ H.1.cells ∧ p ∈ interior (interiorCell p H : Set Plane) := by
  have h : ∃ K ∈ H.1.cells, p ∈ interior (K : Set Plane) := hH
  unfold interiorCell
  rw [dif_pos h]
  exact h.choose_spec

theorem interiorCell_eq {p : Plane} {H : SingSpace} {K : Cell} (hK : K ∈ H.1.cells)
    (hp : p ∈ interior (K : Set Plane)) : interiorCell p H = K := by
  obtain ⟨h1, h2⟩ := interiorCell_spec (p := p) (H := H) ⟨K, hK, hp⟩
  exact eq_of_interior_mem H.2 h1 hK h2 hp

theorem interiorCell_of_notMem {p : Plane} {H : SingSpace} (hH : H ∉ interiorSet p) :
    interiorCell p H = refCell := by
  have h : ¬ ∃ K ∈ H.1.cells, p ∈ interior (K : Set Plane) := hH
  unfold interiorCell
  rw [dif_neg h]

/-- **Continuity of the interior cell** on `O_p`, for the Hausdorff metric (even when `p` is an
accumulation point: the matching comes from a regular interior point of the same cell). -/
theorem isOpen_interiorSet_inter_preimage (p : Plane) {V : Set Cell} (hV : IsOpen V) :
    IsOpen (interiorSet p ∩ interiorCell p ⁻¹' V) := by
  refine isOpen_of_forall_dSing fun H hH => ?_
  obtain ⟨hHp, hHV⟩ := hH
  obtain ⟨hKc, hKi⟩ := interiorCell_spec hHp
  obtain ⟨ρ, hρ, hρV⟩ := Metric.isOpen_iff.1 hV _ hHV
  obtain ⟨δ, hδ, hb⟩ := Metric.isOpen_iff.1 isOpen_interior p hKi
  have hη : 0 < min (δ / 2) (ρ / 2) := lt_min (half_pos hδ) (half_pos hρ)
  obtain ⟨ε, hε, hspec⟩ := exists_matching_near H hKc hKc hη
  refine ⟨ε, hε, fun H' hH' => ?_⟩
  obtain ⟨W, f, hKW, -, hm, hd⟩ := hspec H' hH'
  have hfη := dist_lt_of_wholeDistortion_lt hd
  have hc : CellConfig.mapCell f (interiorCell p H) ∈ H'.1.cells := (hm.1 _ hKW).1
  have hi : p ∈ interior (CellConfig.mapCell f (interiorCell p H) : Set Plane) :=
    mem_interior_mapCell_of_dist_lt hfη (hb.trans interior_subset)
      ((min_le_left _ _).trans_lt (half_lt_self hδ))
  refine ⟨⟨_, hc, hi⟩, ?_⟩
  show interiorCell p H' ∈ V
  rw [interiorCell_eq hc hi]
  refine hρV ?_
  rw [mem_ball]
  calc _ ≤ min (δ / 2) (ρ / 2) := dist_mapCell_le hη.le hfη _
    _ ≤ ρ / 2 := min_le_right _ _
    _ < ρ := half_lt_self hρ

/-- A map which is continuous on an open set `A` (in the sense that `A ∩ g⁻¹ V` is open for open
`V`) and constant off `A` is Borel measurable. -/
theorem measurable_of_isOpen_inter_preimage {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] {A : Set X}
    (hA : IsOpen A) {g : X → Y} {y₀ : Y} (hg : ∀ V : Set Y, IsOpen V → IsOpen (A ∩ g ⁻¹' V))
    (hoff : ∀ x ∉ A, g x = y₀) : Measurable g := by
  refine measurable_of_isOpen fun V hV => ?_
  rw [← inter_union_compl (g ⁻¹' V) A]
  refine MeasurableSet.union ?_ ?_
  · rw [inter_comm]
    exact (hg V hV).measurableSet
  · by_cases hy : y₀ ∈ V
    · convert hA.measurableSet.compl using 1
      ext x
      simp only [mem_inter_iff, mem_preimage, mem_compl_iff]
      exact ⟨fun h => h.2, fun h => ⟨by rw [hoff x h]; exact hy, h⟩⟩
    · convert MeasurableSet.empty using 1
      ext x
      simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false,
        not_and]
      intro hx hxA
      exact hy (by rw [← hoff x hxA]; exact hx)

theorem measurable_interiorCell (p : Plane) : Measurable (interiorCell p) :=
  measurable_of_isOpen_inter_preimage (isOpen_interiorSet p)
    (fun _ hV => isOpen_interiorSet_inter_preimage p hV) (fun _ hH => interiorCell_of_notMem hH)

/-! ### The conductance between two interior cells -/

/-- The conductance between the cells containing `p₁` and `p₂` in their interiors (`0` when one of
them does not exist). -/
noncomputable def pairCond (p₁ p₂ : Plane) (H : SingSpace) : ℝ :=
  open Classical in
  if H ∈ interiorSet p₁ ∩ interiorSet p₂ then H.1.c (interiorCell p₁ H) (interiorCell p₂ H)
  else 0

/-- **Continuity of the conductance** on `O_{p₁} ∩ O_{p₂}`. -/
theorem isOpen_inter_preimage_pairCond (p₁ p₂ : Plane) {V : Set ℝ} (hV : IsOpen V) :
    IsOpen ((interiorSet p₁ ∩ interiorSet p₂) ∩ pairCond p₁ p₂ ⁻¹' V) := by
  refine isOpen_of_forall_dSing fun H hH => ?_
  obtain ⟨⟨hH₁, hH₂⟩, hHV⟩ := hH
  obtain ⟨hK₁c, hK₁i⟩ := interiorCell_spec hH₁
  obtain ⟨hK₂c, hK₂i⟩ := interiorCell_spec hH₂
  have hval : pairCond p₁ p₂ H = H.1.c (interiorCell p₁ H) (interiorCell p₂ H) := by
    unfold pairCond
    rw [if_pos ⟨hH₁, hH₂⟩]
  obtain ⟨ρ, hρ, hρV⟩ := Metric.isOpen_iff.1 hV _ hHV
  obtain ⟨δ₁, hδ₁, hb₁⟩ := Metric.isOpen_iff.1 isOpen_interior p₁ hK₁i
  obtain ⟨δ₂, hδ₂, hb₂⟩ := Metric.isOpen_iff.1 isOpen_interior p₂ hK₂i
  have hδ : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  have hη : 0 < min (min δ₁ δ₂ / 2) ρ := lt_min (half_pos hδ) hρ
  obtain ⟨ε, hε, hspec⟩ := exists_matching_near H hK₁c hK₂c hη
  refine ⟨ε, hε, fun H' hH' => ?_⟩
  obtain ⟨W, f, hK₁W, hK₂W, hm, hd⟩ := hspec H' hH'
  have hfη := dist_lt_of_wholeDistortion_lt hd
  have hηδ : min (min δ₁ δ₂ / 2) ρ < min δ₁ δ₂ :=
    (min_le_left _ _).trans_lt (half_lt_self hδ)
  have hc₁ : CellConfig.mapCell f (interiorCell p₁ H) ∈ H'.1.restrict W := hm.1 _ hK₁W
  have hc₂ : CellConfig.mapCell f (interiorCell p₂ H) ∈ H'.1.restrict W := hm.1 _ hK₂W
  have hi₁ : p₁ ∈ interior (CellConfig.mapCell f (interiorCell p₁ H) : Set Plane) :=
    mem_interior_mapCell_of_dist_lt hfη
      ((ball_subset_ball (min_le_left _ _)).trans (hb₁.trans interior_subset)) hηδ
  have hi₂ : p₂ ∈ interior (CellConfig.mapCell f (interiorCell p₂ H) : Set Plane) :=
    mem_interior_mapCell_of_dist_lt hfη
      ((ball_subset_ball (min_le_right _ _)).trans (hb₂.trans interior_subset)) hηδ
  have hH'₁ : H' ∈ interiorSet p₁ := ⟨_, hc₁.1, hi₁⟩
  have hH'₂ : H' ∈ interiorSet p₂ := ⟨_, hc₂.1, hi₂⟩
  have hval' : pairCond p₁ p₂ H' = H'.1.c (CellConfig.mapCell f (interiorCell p₁ H))
      (CellConfig.mapCell f (interiorCell p₂ H)) := by
    unfold pairCond
    rw [if_pos ⟨hH'₁, hH'₂⟩, interiorCell_eq hc₁.1 hi₁, interiorCell_eq hc₂.1 hi₂]
  refine ⟨⟨hH'₁, hH'₂⟩, ?_⟩
  show pairCond p₁ p₂ H' ∈ V
  apply hρV
  rw [mem_ball, hval', hval, Real.dist_eq]
  have hcF : (CellConfigOps.restrictConfig H.1 W).c (interiorCell p₁ H) (interiorCell p₂ H) =
      H.1.c (interiorCell p₁ H) (interiorCell p₂ H) := restrictConfig_c_of_mem hK₁W hK₂W
  have hcF' : (CellConfigOps.restrictConfig H'.1 W).c (CellConfig.mapCell f (interiorCell p₁ H))
      (CellConfig.mapCell f (interiorCell p₂ H)) =
      H'.1.c (CellConfig.mapCell f (interiorCell p₁ H))
        (CellConfig.mapCell f (interiorCell p₂ H)) := restrictConfig_c_of_mem hc₁ hc₂
  by_cases hadj : H.1.Adj (interiorCell p₁ H) (interiorCell p₂ H)
  · have hadjF : (CellConfigOps.restrictConfig H.1 W).Adj (interiorCell p₁ H)
        (interiorCell p₂ H) := by
      show 0 < (CellConfigOps.restrictConfig H.1 W).c _ _
      rw [hcF]
      exact hadj
    have h := abs_sub_lt_of_wholeDistortion_lt hη hd hK₁W hK₂W hadjF
    rw [hcF, hcF'] at h
    rw [abs_sub_comm]
    exact h.trans_le (min_le_right _ _)
  · have h0 : H.1.c (interiorCell p₁ H) (interiorCell p₂ H) = 0 :=
      le_antisymm (not_lt.1 hadj) (H.2.c_nonneg _ _)
    have h0' : H'.1.c (CellConfig.mapCell f (interiorCell p₁ H))
        (CellConfig.mapCell f (interiorCell p₂ H)) = 0 := by
      refine le_antisymm (not_lt.1 ?_) (H'.2.c_nonneg _ _)
      intro hadj'
      apply hadj
      have hF'adj : (CellConfigOps.restrictConfig H'.1 W).Adj
          (CellConfig.mapCell f (interiorCell p₁ H)) (CellConfig.mapCell f (interiorCell p₂ H)) := by
        show 0 < (CellConfigOps.restrictConfig H'.1 W).c _ _
        rw [hcF']
        exact hadj'
      have hFadj := (hm.2.2 _ hK₁W _ hK₂W).2 hF'adj
      show 0 < H.1.c _ _
      rw [← hcF]
      exact hFadj
    rw [h0, h0', sub_zero, abs_zero]
    exact hρ

theorem measurable_pairCond (p₁ p₂ : Plane) : Measurable (pairCond p₁ p₂) := by
  refine measurable_of_isOpen_inter_preimage
    ((isOpen_interiorSet p₁).inter (isOpen_interiorSet p₂))
    (fun _ hV => isOpen_inter_preimage_pairCond p₁ p₂ hV) (y₀ := 0) fun H hH => ?_
  unfold pairCond
  rw [if_neg hH]

/-! ### The label events -/

/-- The environments having a cell whose least rational interior label is `n`. -/
def labelSet (n : ℕ) : Set SingSpace := {H | ∃ K ∈ H.1.cells, Code.LeastInteriorLabel K n}

theorem labelSet_subset (n : ℕ) : labelSet n ⊆ interiorSet (Code.rationalPoint n) :=
  fun _ ⟨K, hK, hn, _⟩ => ⟨K, hK, hn⟩

theorem labelSet_eq (n : ℕ) :
    labelSet n = interiorSet (Code.rationalPoint n) ∩
      ⋂ m : Fin n, (commonInteriorSet (Code.rationalPoint n) (Code.rationalPoint m))ᶜ := by
  ext H
  simp only [mem_inter_iff, mem_iInter, mem_compl_iff]
  constructor
  · rintro ⟨K, hK, hn, hlt⟩
    refine ⟨⟨K, hK, hn⟩, fun m hm => ?_⟩
    obtain ⟨K', hK', hn', hm'⟩ := hm
    have hKK' : K' = K := eq_of_interior_mem H.2 hK' hK hn' hn
    rw [hKK'] at hm'
    exact hlt m m.2 hm'
  · rintro ⟨⟨K, hK, hn⟩, hnot⟩
    exact ⟨K, hK, hn, fun m hm hmK => hnot ⟨m, hm⟩ ⟨K, hK, hn, hmK⟩⟩

theorem measurableSet_labelSet (n : ℕ) : MeasurableSet (labelSet n) := by
  rw [labelSet_eq]
  exact (isOpen_interiorSet _).measurableSet.inter
    (MeasurableSet.iInter fun _ => (isOpen_commonInteriorSet _ _).measurableSet.compl)

/-! ### The coordinates of the code -/

open Classical in
theorem slot_eq (H : SingSpace) (n : ℕ) :
    H.1.slot n =
      if H ∈ labelSet n then some (interiorCell (Code.rationalPoint n) H) else none := by
  unfold CellConfig.slot
  by_cases h : ∃ K ∈ H.1.cells, Code.LeastInteriorLabel K n
  · have hH : H ∈ labelSet n := h
    rw [dif_pos h, if_pos hH]
    exact congrArg some (interiorCell_eq h.choose_spec.1 h.choose_spec.2.1).symm
  · have hH : H ∉ labelSet n := h
    rw [dif_neg h, if_neg hH]

open Classical in
theorem codeCond_eq (H : SingSpace) (n m : ℕ) :
    H.1.codeCond n m =
      if H ∈ labelSet n ∧ H ∈ labelSet m then
        pairCond (Code.rationalPoint n) (Code.rationalPoint m) H
      else 0 := by
  unfold CellConfig.codeCond
  rw [slot_eq H n, slot_eq H m]
  by_cases h₁ : H ∈ labelSet n <;> by_cases h₂ : H ∈ labelSet m
  · rw [if_pos h₁, if_pos h₂, if_pos ⟨h₁, h₂⟩]
    unfold pairCond
    rw [if_pos ⟨labelSet_subset n h₁, labelSet_subset m h₂⟩]
  · rw [if_pos h₁, if_neg h₂, if_neg fun h => h₂ h.2]
  · rw [if_neg h₁, if_pos h₂, if_neg fun h => h₁ h.1]
  · rw [if_neg h₁, if_neg h₂, if_neg fun h => h₁ h.1]

theorem measurable_slot (n : ℕ) : Measurable fun H : SingSpace => H.1.slot n := by
  classical
  have h : (fun H : SingSpace => H.1.slot n) = fun H =>
      if H ∈ labelSet n then some (interiorCell (Code.rationalPoint n) H) else none :=
    funext fun H => slot_eq H n
  rw [h]
  exact Measurable.ite (measurableSet_labelSet n)
    (CanonicalSimilarity.measurable_someCell.comp (measurable_interiorCell _)) measurable_const

theorem measurable_codeCond (n m : ℕ) : Measurable fun H : SingSpace => H.1.codeCond n m := by
  classical
  have h : (fun H : SingSpace => H.1.codeCond n m) = fun H =>
      if H ∈ labelSet n ∧ H ∈ labelSet m then
        pairCond (Code.rationalPoint n) (Code.rationalPoint m) H
      else 0 :=
    funext fun H => codeCond_eq H n m
  rw [h]
  exact Measurable.ite ((measurableSet_labelSet n).inter (measurableSet_labelSet m))
    (measurable_pairCond _ _) measurable_const

end CoordsMeasurable

/-- **Manuscript Proposition 2.7** (measurability part): the auxiliary rational-label coordinates
`coords : SingSpace → Code.RawCode` are measurable from `B_sing = B(τ_sing)` to the product
σ-algebra of `Code.RawCode`. -/
theorem measurable_coords : Measurable coords := by
  show Measurable fun H : SingSpace => ((fun n => H.1.slot n), fun n m => H.1.codeCond n m)
  exact (Measurable.of_eval fun n => CoordsMeasurable.measurable_slot n).prodMk
    (Measurable.of_eval fun n => Measurable.of_eval fun m => CoordsMeasurable.measurable_codeCond n m)

end ReflectedGMS.GeomTop

assert_no_sorry ReflectedGMS.GeomTop.CoordsMeasurable.dSing_self
assert_no_sorry ReflectedGMS.GeomTop.CoordsMeasurable.exists_matching_of_dSing_lt
assert_no_sorry ReflectedGMS.GeomTop.CoordsMeasurable.exists_window
assert_no_sorry ReflectedGMS.GeomTop.CoordsMeasurable.exists_matching_near
assert_no_sorry ReflectedGMS.GeomTop.CoordsMeasurable.isOpen_interiorSet
assert_no_sorry ReflectedGMS.GeomTop.CoordsMeasurable.measurable_interiorCell
assert_no_sorry ReflectedGMS.GeomTop.CoordsMeasurable.measurable_pairCond
assert_no_sorry ReflectedGMS.GeomTop.CoordsMeasurable.measurableSet_labelSet
assert_no_sorry ReflectedGMS.GeomTop.CoordsMeasurable.measurable_slot
assert_no_sorry ReflectedGMS.GeomTop.CoordsMeasurable.measurable_codeCond
assert_no_sorry ReflectedGMS.GeomTop.measurable_coords

#print axioms ReflectedGMS.GeomTop.CoordsMeasurable.exists_matching_near
#print axioms ReflectedGMS.GeomTop.CoordsMeasurable.isOpen_interiorSet
#print axioms ReflectedGMS.GeomTop.CoordsMeasurable.measurable_slot
#print axioms ReflectedGMS.GeomTop.CoordsMeasurable.measurable_codeCond
#print axioms ReflectedGMS.GeomTop.measurable_coords
