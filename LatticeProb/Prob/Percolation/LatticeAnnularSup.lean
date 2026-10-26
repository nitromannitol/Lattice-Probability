import LatticeProb.Prob.Percolation.LatticeClusterBall
import Mathlib.Order.LiminfLimsup
import Mathlib.Topology.Instances.ENNReal.Lemmas

namespace LatticeProb.Percolation

noncomputable section

variable {d : ℕ} {ω : Configuration d}

/-- The supremum of the absolute values on the literal Euclidean annulus. -/
def componentAnnularSup (C : OpenComponent ω) (u : C → ℝ) (R : ℝ) : ENNReal :=
  ⨆ (x : C) (_ : R / 2 ≤ dist (latticeEuclideanEmbedding x.val)
      (latticeEuclideanEmbedding 0) ∧
    dist (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding 0) < R),
    ENNReal.ofReal |u x|

/-- Every value on the annulus is bounded by its extended supremum. -/
theorem le_componentAnnularSup (C : OpenComponent ω) (u : C → ℝ) (R : ℝ)
    (x : C) (hx : R / 2 ≤ dist (latticeEuclideanEmbedding x.val)
      (latticeEuclideanEmbedding 0) ∧
    dist (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding 0) < R) :
    ENNReal.ofReal |u x| ≤ componentAnnularSup C u R :=
  le_iSup_of_le x (le_iSup_of_le hx le_rfl)

/-- Upper bounds for the annular supremum are exactly the pointwise upper bounds. -/
theorem componentAnnularSup_le_iff (C : OpenComponent ω) (u : C → ℝ) (R : ℝ)
    (a : ENNReal) : componentAnnularSup C u R ≤ a ↔
    ∀ x : C, R / 2 ≤ dist (latticeEuclideanEmbedding x.val)
      (latticeEuclideanEmbedding 0) →
      dist (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding 0) < R →
      ENNReal.ofReal |u x| ≤ a := by
  simp only [componentAnnularSup, iSup_le_iff, and_imp]

/-- The annulus is finite because it is contained in the outer Euclidean ball. -/
theorem finite_componentAnnulus (C : OpenComponent ω) (R : ℝ) :
    {x : C | R / 2 ≤ dist (latticeEuclideanEmbedding x.val)
      (latticeEuclideanEmbedding 0) ∧
    dist (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding 0) < R}.Finite :=
  (finite_componentEuclideanBall C 0 R).subset (fun _ hx => hx.2)

/-- Empty annuli have supremum zero in the complete order. -/
theorem componentAnnularSup_eq_zero_of_empty (C : OpenComponent ω) (u : C → ℝ)
    (R : ℝ) (h : ¬ ∃ x : C, R / 2 ≤ dist (latticeEuclideanEmbedding x.val)
      (latticeEuclideanEmbedding 0) ∧
    dist (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding 0) < R) :
    componentAnnularSup C u R = 0 := by
  apply le_antisymm
  · apply (componentAnnularSup_le_iff C u R 0).2
    intro x hx hy
    exact False.elim (h ⟨x, hx, hy⟩)
  · exact bot_le

/-- A nonempty annulus has a unique real maximum, which is its real least upper bound
and represents the extended supremum. -/
theorem existsUnique_componentAnnularMax (C : OpenComponent ω) (u : C → ℝ) (R : ℝ)
    (h : ∃ x : C, R / 2 ≤ dist (latticeEuclideanEmbedding x.val)
      (latticeEuclideanEmbedding 0) ∧
    dist (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding 0) < R) :
    ∃! m : ℝ, (∃ x : C, (R / 2 ≤ dist (latticeEuclideanEmbedding x.val)
      (latticeEuclideanEmbedding 0) ∧
    dist (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding 0) < R) ∧ m = |u x|) ∧
      (∀ x : C, R / 2 ≤ dist (latticeEuclideanEmbedding x.val)
      (latticeEuclideanEmbedding 0) →
      dist (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding 0) < R → |u x| ≤ m) ∧
      componentAnnularSup C u R = ENNReal.ofReal m := by
  classical
  let s := (finite_componentAnnulus C R).toFinset
  have hs : s.Nonempty := by
    obtain ⟨x, hx⟩ := h
    exact ⟨x, (Set.Finite.mem_toFinset _).2 hx⟩
  obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image s (fun x => |u x|) hs
  have hx' := (Set.Finite.mem_toFinset _).1 hx
  have hb : ∀ y : C, R / 2 ≤ dist (latticeEuclideanEmbedding y.val)
      (latticeEuclideanEmbedding 0) →
      dist (latticeEuclideanEmbedding y.val) (latticeEuclideanEmbedding 0) < R →
      |u y| ≤ |u x| := by
    intro y hy hz
    exact hmax y ((Set.Finite.mem_toFinset _).2 ⟨hy, hz⟩)
  have heq : componentAnnularSup C u R = ENNReal.ofReal |u x| := by
    apply le_antisymm
    · apply (componentAnnularSup_le_iff C u R _).2
      intro y hy hz
      exact ENNReal.ofReal_le_ofReal (hb y hy hz)
    · exact le_componentAnnularSup C u R x hx'
  refine ⟨|u x|, ⟨⟨x, hx', rfl⟩, hb, heq⟩, ?_⟩
  intro m hm
  obtain ⟨⟨y, hy, rfl⟩, hm, _⟩ := hm
  exact le_antisymm (hb y hy.1 hy.2) (hm x hx'.1 hx'.2)

/-- At nonnegative radius, scaling the exact real maximum gives the scaled supremum. -/
theorem scaled_componentAnnularSup_eq_ofReal_max (C : OpenComponent ω) (u : C → ℝ)
    (R : ℝ) (hR : 0 ≤ R)
    (h : ∃ x : C, R / 2 ≤ dist (latticeEuclideanEmbedding x.val)
      (latticeEuclideanEmbedding 0) ∧
    dist (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding 0) < R) :
    ∃ m : ℝ, (∃ x : C, (R / 2 ≤ dist (latticeEuclideanEmbedding x.val)
      (latticeEuclideanEmbedding 0) ∧
    dist (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding 0) < R) ∧ m = |u x|) ∧
      (∀ x : C, R / 2 ≤ dist (latticeEuclideanEmbedding x.val)
      (latticeEuclideanEmbedding 0) →
      dist (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding 0) < R → |u x| ≤ m) ∧
      ENNReal.ofReal R * componentAnnularSup C u R = ENNReal.ofReal (R * m) := by
  obtain ⟨m, ⟨hm, hb, heq⟩, _⟩ := existsUnique_componentAnnularMax C u R h
  refine ⟨m, hm, hb, ?_⟩
  rw [heq, ENNReal.ofReal_mul hR]

private theorem dist_embedding_add_unit (x : Vertex d) (i : Fin d) :
    dist (latticeEuclideanEmbedding (x + unit i)) (latticeEuclideanEmbedding x) = 1 := by
  rw [dist_eq_norm]
  have heq : latticeEuclideanEmbedding (x + unit i) - latticeEuclideanEmbedding x =
      PiLp.single 2 i (1 : ℝ) := by
    ext j
    change ((x j + unit i j : ℤ) : ℝ) - (x j : ℝ) = (Pi.single i (1 : ℝ) : Fin d → ℝ) j
    by_cases h : j = i <;> simp [unit, h]
  rw [heq, PiLp.norm_single]
  norm_num

theorem dist_embedding_adj {x y : Vertex d}
    (h : (openGraph ω).Adj x y) :
    dist (latticeEuclideanEmbedding x) (latticeEuclideanEmbedding y) = 1 := by
  obtain ⟨i, hi | hi⟩ := openGraph_le ω h
  · rw [hi, dist_comm]
    exact dist_embedding_add_unit x i
  · rw [hi]
    exact dist_embedding_add_unit y i

private theorem walk_crosses_radius (C : OpenComponent ω) (t : ℝ)
    {a b : C} (p : (componentGraph C).Walk a b)
    (ha : dist (latticeEuclideanEmbedding a.val) (latticeEuclideanEmbedding 0) < t)
    (hb : t ≤ dist (latticeEuclideanEmbedding b.val) (latticeEuclideanEmbedding 0)) :
    ∃ x : C, t ≤ dist (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding 0) ∧
      dist (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding 0) < t + 1 := by
  induction p with
  | nil => exact False.elim ((not_le_of_gt ha) hb)
  | @cons a z b haz p ih =>
    by_cases hz : dist (latticeEuclideanEmbedding z.val) (latticeEuclideanEmbedding 0) < t
    · exact ih hz hb
    · refine ⟨z, le_of_not_gt hz, ?_⟩
      have he : dist (latticeEuclideanEmbedding z.val) (latticeEuclideanEmbedding a.val) = 1 := by
        rw [dist_comm]
        exact dist_embedding_adj haz
      have ht := dist_triangle (latticeEuclideanEmbedding z.val)
        (latticeEuclideanEmbedding a.val) (latticeEuclideanEmbedding 0)
      rw [he] at ht
      linarith

/-- Every sufficiently large real annulus of an infinite actual component is nonempty. -/
theorem eventually_nonempty_componentAnnulus (C : OpenComponent ω) (hC : C.supp.Infinite) :
    ∃ T : ℝ, ∀ R : ℝ, T ≤ R →
      ∃ x : C, R / 2 ≤ dist (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding 0) ∧
        dist (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding 0) < R := by
  let a : C := ⟨C.out, C.out_eq⟩
  let r := dist (latticeEuclideanEmbedding a.val) (latticeEuclideanEmbedding 0)
  refine ⟨2 * r + 3, ?_⟩
  intro R hR
  have ha : dist (latticeEuclideanEmbedding a.val) (latticeEuclideanEmbedding 0) < R / 2 := by
    dsimp [r] at hR
    linarith
  have hout : ∃ y : Vertex d, y ∈ C.supp ∧
      R ≤ dist (latticeEuclideanEmbedding y) (latticeEuclideanEmbedding 0) := by
    by_contra! hn
    apply hC
    apply (finite_latticeEuclideanBall 0 R).subset
    intro y hy
    exact hn y hy
  obtain ⟨y, hy, hyR⟩ := hout
  let b : C := ⟨y, hy⟩
  obtain ⟨p⟩ := C.connected_toSimpleGraph a b
  obtain ⟨x, hx, hx'⟩ := walk_crosses_radius C (R / 2) p ha (by
    dsimp [b]
    have hr0 : 0 ≤ R := by
      dsimp [r] at hR
      have := dist_nonneg (x := latticeEuclideanEmbedding a.val)
        (y := latticeEuclideanEmbedding 0)
      linarith
    linarith)
  refine ⟨x, hx, ?_⟩
  have hr : 2 < R := by
    have : 0 ≤ r := dist_nonneg
    linarith
  linarith

/-- The extended scaled annular limsup appearing in the decay condition. -/
def annularDecayZero (C : OpenComponent ω) (u : C → ℝ) : Prop :=
  Filter.limsup (fun R : ℝ => ENNReal.ofReal R * componentAnnularSup C u R)
    Filter.atTop = 0

/-- The scaled supremum is the supremum of the scaled terms. -/
theorem scaled_componentAnnularSup_le_iff (C : OpenComponent ω) (u : C → ℝ)
    (R : ℝ) (a : ENNReal) :
    ENNReal.ofReal R * componentAnnularSup C u R ≤ a ↔
    ∀ x : C, R / 2 ≤ dist (latticeEuclideanEmbedding x.val)
      (latticeEuclideanEmbedding 0) →
      dist (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding 0) < R →
      ENNReal.ofReal R * ENNReal.ofReal |u x| ≤ a := by
  simp only [componentAnnularSup, ENNReal.mul_iSup, iSup_le_iff, and_imp]

/-- Any eventual real maximum representation gives the same scaled limsup. -/
theorem annularDecayZero_iff_realMax_limsup (C : OpenComponent ω) (u : C → ℝ)
    (m : ℝ → ℝ)
    (hm : ∀ᶠ R : ℝ in Filter.atTop,
      (∃ x : C, (R / 2 ≤ dist (latticeEuclideanEmbedding x.val)
        (latticeEuclideanEmbedding 0) ∧
        dist (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding 0) < R) ∧
        m R = |u x|) ∧
      ∀ x : C, R / 2 ≤ dist (latticeEuclideanEmbedding x.val)
        (latticeEuclideanEmbedding 0) →
        dist (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding 0) < R →
        |u x| ≤ m R) :
    annularDecayZero C u ↔
      Filter.limsup (fun R : ℝ => ENNReal.ofReal (R * m R)) Filter.atTop = 0 := by
  have he : ∀ᶠ R : ℝ in Filter.atTop,
      ENNReal.ofReal R * componentAnnularSup C u R = ENNReal.ofReal (R * m R) := by
    filter_upwards [hm, Filter.eventually_ge_atTop (0 : ℝ)] with R hmax hR
    obtain ⟨⟨x, hx, hxm⟩, hb⟩ := hmax
    have hs : componentAnnularSup C u R = ENNReal.ofReal (m R) := by
      apply le_antisymm
      · apply (componentAnnularSup_le_iff C u R _).2
        intro y hy hz
        exact ENNReal.ofReal_le_ofReal (hb y hy hz)
      · rw [hxm]
        exact le_componentAnnularSup C u R x hx
    rw [hs, ENNReal.ofReal_mul hR]
  unfold annularDecayZero
  rw [Filter.limsup_congr he]

/-- The literal limsup vanishes exactly for the full positive epsilon tail. -/
theorem annularDecayZero_iff_tail (C : OpenComponent ω) (u : C → ℝ) :
    annularDecayZero C u ↔
      ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧ ∀ R : ℝ, T ≤ R →
        ∀ x : C, R / 2 ≤ dist (latticeEuclideanEmbedding x.val)
          (latticeEuclideanEmbedding 0) →
        dist (latticeEuclideanEmbedding x.val) (latticeEuclideanEmbedding 0) < R →
        R * |u x| < ε := by
  constructor
  · intro h ε hε
    have he : ∀ᶠ R : ℝ in Filter.atTop,
        ENNReal.ofReal R * componentAnnularSup C u R < ENNReal.ofReal ε := by
      apply Filter.eventually_lt_of_limsup_lt (hu := ⟨⊤, Filter.Eventually.of_forall (fun _ => le_top)⟩)
      rw [show Filter.limsup (fun R : ℝ => ENNReal.ofReal R *
        componentAnnularSup C u R) Filter.atTop = 0 from h]
      exact ENNReal.ofReal_pos.mpr hε
    obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp he
    refine ⟨max T 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
    intro R hR x hx hy
    have hRp : 0 ≤ R := le_of_lt (lt_of_lt_of_le zero_lt_one
      ((le_max_right T 1).trans hR))
    have hl : ENNReal.ofReal R * ENNReal.ofReal |u x| ≤
        ENNReal.ofReal R * componentAnnularSup C u R := by
      simpa only [mul_comm] using mul_le_mul_left
        (le_componentAnnularSup C u R x ⟨hx, hy⟩) (ENNReal.ofReal R)
    have ht := hl.trans_lt (hT R ((le_max_left T 1).trans hR))
    rw [← ENNReal.ofReal_mul hRp] at ht
    exact (ENNReal.ofReal_lt_ofReal_iff hε).mp ht
  · intro h
    apply le_antisymm
    · apply ENNReal.le_of_forall_pos_le_add
      intro ε hε _
      simp only [zero_add]
      have hεr : 0 < (ε : ℝ) := hε
      obtain ⟨T, hT, ht⟩ := h (ε : ℝ) hεr
      apply Filter.limsup_le_of_le (hf := Filter.isCoboundedUnder_le_of_eventually_le
        Filter.atTop (Filter.Eventually.of_forall (fun _ => bot_le)))
      apply Filter.eventually_atTop.mpr
      refine ⟨T, ?_⟩
      intro R hR
      apply (scaled_componentAnnularSup_le_iff C u R ε).2
      intro x hx hy
      have hp : 0 ≤ R := le_of_lt (hT.trans_le hR)
      rw [← ENNReal.ofReal_mul hp]
      have hb := (ht R hR x hx hy).le
      simpa only [ENNReal.ofReal_coe_nnreal] using ENNReal.ofReal_le_ofReal hb
    · exact bot_le

end
end LatticeProb.Percolation
