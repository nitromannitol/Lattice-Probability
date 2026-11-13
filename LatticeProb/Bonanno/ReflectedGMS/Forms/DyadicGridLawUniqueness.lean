/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.DyadicGridLawUniqueness at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.DyadicGridLaw
import Mathlib.MeasureTheory.PiSystem
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-! Uniqueness of the uniform random dyadic grid law.

`DyadicApproximation.UniformGridLaw ν` prescribes the law of every finite cylinder
`DyadicApproximation.gridCylinder k n`, i.e. of the phase, the relative origin at one
level `k`, and `n` successive parent digits from that level. The measurable structure
on `DyadicApproximation.Grid` is the comap of the full coordinate code
`(phase, origin, digit)`, which carries origins at *all* integer levels, so the
prescribed cylinders do not literally exhaust the coordinates.

The reconstruction here closes that gap: by `Grid.compatible`, the relative origin at
level `k + m` and the digits at levels `k + m, …` are explicit measurable functions of
the level-`k` relative origin and of the digits at levels `k, …, k + m + n' - 1`
(`gridCylinder_reindex`). Hence the cylinder preimages form a π-system, and the
level-`k` cylinder alone already recovers `phase`, `origin k` and `digit k`, so that
π-system generates the whole grid σ-algebra. Two probability measures with the same
cylinder laws therefore agree (`eq_of_uniformGridLaw`). No invariance, independence
of coordinates, or second law is assumed. -/

set_option autoImplicit false

open MeasureTheory Set

namespace ReflectedGMS.DyadicGridLawUniqueness

open ReflectedGMS.DyadicApproximation

/-- The value space read by `DyadicApproximation.gridCylinder _ n`. -/
abbrev Cyl (n : ℕ) : Type := ℝ × ((Fin 2 → ℝ) × (Fin n → Fin 2 → Fin 2))

/-! ### Coordinate reconstruction from a deeper cylinder -/

/-- Side lengths at two levels differ by the integer power of their level difference. -/
theorem side_eq_rpow_mul (D : Grid) (a b : ℤ) :
    side D a = (2 : ℝ) ^ ((a : ℝ) - (b : ℝ)) * side D b := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  simp only [side, ← Real.rpow_add h2]
  congr 1
  ring

theorem side_add_nat (D : Grid) (k : ℤ) (m : ℕ) :
    side D (k + (m : ℤ)) = (2 : ℝ) ^ ((m : ℝ)) * side D k := by
  have hexp : ((k + (m : ℤ) : ℤ) : ℝ) - (k : ℝ) = ((m : ℕ) : ℝ) := by push_cast; ring
  rw [side_eq_rpow_mul D (k + (m : ℤ)) k, hexp]

/-- One step of `Grid.compatible`, solved for the finer origin. -/
theorem origin_succ (D : Grid) (k : ℤ) (i : Fin 2) :
    D.origin (k + 1) i = D.origin k i - side D k * ((D.digit k i).val : ℝ) := by
  have hc := D.compatible k i
  simp only [side]
  linarith [hc]

/-- The origin `m` levels up is the level-`k` origin corrected by the `m` intervening
digits. This is the exact content of `Grid.compatible` used below. -/
theorem origin_add_nat (D : Grid) (k : ℤ) (m : ℕ) (i : Fin 2) :
    D.origin (k + (m : ℤ)) i
      = D.origin k i -
          ∑ j : Fin m, side D (k + ((j : ℕ) : ℤ)) * ((D.digit (k + ((j : ℕ) : ℤ)) i).val : ℝ) := by
  induction m with
  | zero => simp
  | succ m ih =>
      have hcast : ((m + 1 : ℕ) : ℤ) = (m : ℤ) + 1 := by push_cast; ring
      have hstep : D.origin (k + ((m : ℤ) + 1)) i
          = D.origin (k + (m : ℤ)) i -
            side D (k + (m : ℤ)) * ((D.digit (k + (m : ℤ)) i).val : ℝ) := by
        rw [← add_assoc]
        exact origin_succ D (k + (m : ℤ)) i
      rw [hcast, hstep, ih, Fin.sum_univ_castSucc]
      simp only [Fin.coe_castSucc, Fin.val_last]
      ring

/-- The relative origin recorded by `gridCylinder` at level `k + m`, expressed through the
level-`k` relative origin and the intervening digits. The phase cancels. -/
theorem relOrigin_add_nat (D : Grid) (k : ℤ) (m : ℕ) (i : Fin 2) :
    -D.origin (k + (m : ℤ)) i / side D (k + (m : ℤ))
      = (2 : ℝ) ^ (-(m : ℝ)) *
          ((-D.origin k i / side D k) +
            ∑ j : Fin m, (2 : ℝ) ^ (((j : ℕ) : ℝ)) *
              ((D.digit (k + ((j : ℕ) : ℤ)) i).val : ℝ)) := by
  have hs : side D k ≠ 0 := (side_pos D k).ne'
  have hm : ((2 : ℝ) ^ ((m : ℝ))) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
  have hsum :
      ∑ j : Fin m, side D (k + ((j : ℕ) : ℤ)) * ((D.digit (k + ((j : ℕ) : ℤ)) i).val : ℝ)
        = side D k * ∑ j : Fin m, (2 : ℝ) ^ (((j : ℕ) : ℝ)) *
            ((D.digit (k + ((j : ℕ) : ℤ)) i).val : ℝ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [side_add_nat D k (j : ℕ)]
    ring
  rw [origin_add_nat D k m i, hsum, side_add_nat D k m,
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  first
    | (field_simp; ring)
    | field_simp

/-! ### The reindexing map between cylinder spaces -/

/-- The explicit measurable reconstruction of the level `k + m`, depth `n'` cylinder data
from the level `k`, depth `n` data. -/
noncomputable def reindex (m n' n : ℕ) (h : m + n' ≤ n) (p : Cyl n) : Cyl n' :=
  (p.1,
    (fun i => (2 : ℝ) ^ (-(m : ℝ)) *
        (p.2.1 i +
          ∑ j : Fin m, (2 : ℝ) ^ (((j : ℕ) : ℝ)) *
            ((p.2.2 (Fin.castLE (le_trans (Nat.le_add_right m n') h) j) i).val : ℝ)),
      fun j i => p.2.2 (Fin.castLE h (Fin.natAdd m j)) i))

theorem measurable_digitSum (n m : ℕ) (e : Fin m → Fin n) (i : Fin 2) :
    Measurable fun c : Fin n → Fin 2 → Fin 2 =>
      ∑ j : Fin m, (2 : ℝ) ^ (((j : ℕ) : ℝ)) * ((c (e j) i).val : ℝ) :=
  measurable_of_countable _

theorem measurable_digitShift (n n' : ℕ) (e : Fin n' → Fin n) :
    Measurable fun c : Fin n → Fin 2 → Fin 2 => fun j i => c (e j) i :=
  measurable_of_countable _

theorem measurable_reindex (m n' n : ℕ) (h : m + n' ≤ n) : Measurable (reindex m n' n h) := by
  refine measurable_fst.prodMk (Measurable.prodMk ?_ ?_)
  · refine Measurable.of_eval fun i => ?_
    exact measurable_const.mul
      (((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)).add
        ((measurable_digitSum n m (Fin.castLE (le_trans (Nat.le_add_right m n') h)) i).comp
          (measurable_snd.comp measurable_snd)))
  · exact (measurable_digitShift n n' (fun j => Fin.castLE h (Fin.natAdd m j))).comp
      (measurable_snd.comp measurable_snd)

/-- First milestone: every finite family of grid coordinates read at level `k + m` is a
measurable function of the deeper level-`k` cylinder. -/
theorem gridCylinder_reindex (k : ℤ) (m n' n : ℕ) (h : m + n' ≤ n) (D : Grid) :
    gridCylinder (k + (m : ℤ)) n' D = reindex m n' n h (gridCylinder k n D) := by
  simp only [gridCylinder, reindex, Prod.mk.injEq, true_and, Fin.coe_castLE, Fin.coe_natAdd]
  constructor
  · funext i
    exact relOrigin_add_nat D k m i
  · funext j i
    have hidx : (k + (m : ℤ)) + ((j : ℕ) : ℤ) = k + (((m + (j : ℕ) : ℕ)) : ℤ) := by
      push_cast; ring
    rw [hidx]

/-! ### The cylinder π-system -/

/-- Preimages of measurable sets under the prescribed cylinders. -/
def gridCylinderSets : Set (Set Grid) :=
  {s | ∃ (k : ℤ) (n : ℕ) (t : Set (Cyl n)), MeasurableSet t ∧ s = gridCylinder k n ⁻¹' t}

theorem isPiSystem_gridCylinderSets : IsPiSystem gridCylinderSets := by
  rintro s ⟨k₁, n₁, t₁, ht₁, rfl⟩ s' ⟨k₂, n₂, t₂, ht₂, rfl⟩ -
  obtain ⟨k, hk₁, hk₂⟩ : ∃ k : ℤ, k ≤ k₁ ∧ k ≤ k₂ :=
    ⟨min k₁ k₂, min_le_left _ _, min_le_right _ _⟩
  obtain ⟨m₁, hm₁⟩ : ∃ m : ℕ, k₁ = k + (m : ℤ) := ⟨(k₁ - k).toNat, by omega⟩
  obtain ⟨m₂, hm₂⟩ : ∃ m : ℕ, k₂ = k + (m : ℤ) := ⟨(k₂ - k).toNat, by omega⟩
  obtain ⟨n, hn₁, hn₂⟩ : ∃ n : ℕ, m₁ + n₁ ≤ n ∧ m₂ + n₂ ≤ n :=
    ⟨max (m₁ + n₁) (m₂ + n₂), le_max_left _ _, le_max_right _ _⟩
  have e₁ : gridCylinder k₁ n₁ = reindex m₁ n₁ n hn₁ ∘ gridCylinder k n := by
    funext D
    rw [hm₁]
    exact gridCylinder_reindex k m₁ n₁ n hn₁ D
  have e₂ : gridCylinder k₂ n₂ = reindex m₂ n₂ n hn₂ ∘ gridCylinder k n := by
    funext D
    rw [hm₂]
    exact gridCylinder_reindex k m₂ n₂ n hn₂ D
  refine ⟨k, n, reindex m₁ n₁ n hn₁ ⁻¹' t₁ ∩ reindex m₂ n₂ n hn₂ ⁻¹' t₂,
    (measurable_reindex m₁ n₁ n hn₁ ht₁).inter (measurable_reindex m₂ n₂ n hn₂ ht₂), ?_⟩
  rw [e₁, e₂, Set.preimage_comp, Set.preimage_comp, ← Set.preimage_inter]

/-! ### The cylinders generate the grid σ-algebra -/

theorem measurableSet_gridCylinder_preimage (k : ℤ) (n : ℕ) {t : Set (Cyl n)}
    (ht : MeasurableSet t) :
    MeasurableSet[MeasurableSpace.generateFrom gridCylinderSets] (gridCylinder k n ⁻¹' t) :=
  MeasurableSpace.measurableSet_generateFrom ⟨k, n, t, ht, rfl⟩

theorem measurable_gridCylinder_generateFrom (k : ℤ) (n : ℕ) :
    @Measurable Grid _ (MeasurableSpace.generateFrom gridCylinderSets) _ (gridCylinder k n) :=
  fun _ ht => measurableSet_gridCylinder_preimage k n ht

theorem origin_eq_neg_rel_mul_side (D : Grid) (k : ℤ) (i : Fin 2) :
    D.origin k i = -((-D.origin k i / side D k) * side D k) := by
  have hs : side D k ≠ 0 := (side_pos D k).ne'
  rw [div_mul_cancel₀ _ hs, neg_neg]

theorem generateFrom_gridCylinderSets :
    (inferInstance : MeasurableSpace Grid) = MeasurableSpace.generateFrom gridCylinderSets := by
  refine le_antisymm ?_ ?_
  · letI G : MeasurableSpace Grid := MeasurableSpace.generateFrom gridCylinderSets
    have hcyl : ∀ (k : ℤ) (n : ℕ), Measurable (gridCylinder k n) :=
      fun k n => measurable_gridCylinder_generateFrom k n
    have hphase : Measurable (fun D : Grid => D.phase) :=
      measurable_fst.comp (hcyl 0 0)
    have hdig : ∀ (k : ℤ) (i : Fin 2), Measurable (fun D : Grid => D.digit k i) := by
      intro k i
      have hfun : (fun D : Grid => D.digit k i)
          = fun D : Grid => (gridCylinder k 1 D).2.2 ⟨0, Nat.zero_lt_one⟩ i := by
        funext D
        first
          | simp [gridCylinder]
          | (show D.digit k i = D.digit (k + ((0 : ℕ) : ℤ)) i; norm_num)
      rw [hfun]
      exact (measurable_pi_apply i).comp
        ((measurable_pi_apply (⟨0, Nat.zero_lt_one⟩ : Fin 1)).comp
          (measurable_snd.comp (measurable_snd.comp (hcyl k 1))))
    have horig : ∀ (k : ℤ) (i : Fin 2), Measurable (fun D : Grid => D.origin k i) := by
      intro k i
      have hu : Measurable (fun D : Grid => -D.origin k i / side D k) :=
        (measurable_pi_apply i).comp
          (measurable_fst.comp (measurable_snd.comp (hcyl k 0)))
      have hside : Measurable (fun D : Grid => side D k) :=
        (ReflectedGMS.DyadicGridLaw.measurable_two_rpow (k : ℝ)).comp hphase
      have hrw : (fun D : Grid => D.origin k i)
          = fun D : Grid => -((-D.origin k i / side D k) * side D k) :=
        funext fun D => origin_eq_neg_rel_mul_side D k i
      rw [hrw]
      exact (hu.mul hside).neg
    have horigin : Measurable (fun D : Grid => D.origin) :=
      Measurable.of_eval fun k => Measurable.of_eval fun i => horig k i
    have hdigit : Measurable (fun D : Grid => D.digit) :=
      Measurable.of_eval fun k => Measurable.of_eval fun i => hdig k i
    have hcode : Measurable (fun D : Grid => (D.phase, D.origin, D.digit)) :=
      hphase.prodMk (horigin.prodMk hdigit)
    exact hcode.comap_le
  · refine MeasurableSpace.generateFrom_le ?_
    rintro s ⟨k, n, t, ht, rfl⟩
    exact ReflectedGMS.DyadicGridLaw.measurable_gridCylinder k n ht

/-! ### Uniqueness -/

/-- Any two measures satisfying the uniform dyadic grid specification coincide. -/
theorem eq_of_uniformGridLaw {ν₁ ν₂ : Measure Grid}
    (h₁ : UniformGridLaw ν₁) (h₂ : UniformGridLaw ν₂) : ν₁ = ν₂ := by
  have hp₁ : IsProbabilityMeasure ν₁ := h₁.1
  have hp₂ : IsProbabilityMeasure ν₂ := h₂.1
  refine MeasureTheory.ext_of_generate_finite gridCylinderSets generateFrom_gridCylinderSets
    isPiSystem_gridCylinderSets ?_ ?_
  · rintro s ⟨k, n, t, ht, rfl⟩
    rw [← Measure.map_apply (ReflectedGMS.DyadicGridLaw.measurable_gridCylinder k n) ht,
      ← Measure.map_apply (ReflectedGMS.DyadicGridLaw.measurable_gridCylinder k n) ht,
      h₁.2 k n, h₂.2 k n]
  · rw [measure_univ, measure_univ]

end ReflectedGMS.DyadicGridLawUniqueness
