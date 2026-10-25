import LatticeProb.Site

/-!
# Antisymmetric pairing on the integer lattice

Finite collections of absolutely summable rows admit summation by parts against
finitely supported tests. Delta tests give minus twice the divergence, and unit
edge fields provide concrete finitely supported examples.
-/

namespace LatticeProb.AntisymmetricPairing

open Classical

noncomputable section

variable {d : ℕ}

/-- Reversing the endpoints of a directed lattice displacement is an involution. -/
def displacementReverse (d : ℕ) : Site d × Site d ≃ Site d × Site d where
  toFun p := (p.1 + p.2, -p.2)
  invFun p := (p.1 + p.2, -p.2)
  left_inv _ := Prod.ext (add_neg_cancel_right _ _) (neg_neg _)
  right_inv _ := Prod.ext (add_neg_cancel_right _ _) (neg_neg _)

/-- Antisymmetry forces the diagonal contribution, omitted in the source divergence, to vanish. -/
theorem antisymmetric_diagonal_eq_zero (g : Site d → Site d → ℝ)
    (hanti : ∀ x y, g x y = -g y x) (x : Site d) : g x x = 0 := by
  have h := hanti x x
  linarith

/-- Including the zero displacement leaves the source divergence unchanged. -/
theorem antisymmetric_tsum_nonzero (g : Site d → Site d → ℝ)
    (hanti : ∀ x y, g x y = -g y x) (x : Site d) :
    (∑' z : {z : Site d // z ≠ 0}, g (x + z) x) = ∑' z, g (x + z) x := by
  apply tsum_subtype_eq_of_support_subset (f := fun z => g (x + z) x)
    (s := {z : Site d | z ≠ 0})
  intro z hz
  change z ≠ 0
  intro hzero
  apply hz
  change g (x + z) x = 0
  rw [hzero, add_zero, antisymmetric_diagonal_eq_zero g hanti]

/-- Absolute convergence of the source row excluding zero is equivalent to convergence
of the full row, since antisymmetry kills the diagonal. -/
theorem antisymmetric_summable_nonzero_iff (g : Site d → Site d → ℝ)
    (hanti : ∀ x y, g x y = -g y x) (x : Site d) :
    Summable (fun z : {z : Site d // z ≠ 0} => g (x + z) x) ↔
      Summable (fun z => g (x + z) x) := by
  apply Subtype.val_injective.summable_iff
    (f := fun z : Site d => g (x + z) x)
    (g := (Subtype.val : {z : Site d // z ≠ 0} → Site d))
  intro z hz
  have hzero : z = 0 := by
    by_contra hne
    exact hz ⟨⟨z, hne⟩, rfl⟩
  rw [hzero, add_zero, antisymmetric_diagonal_eq_zero g hanti]

/-- A finite collection of absolutely summable rows gives an absolutely summable array. -/
theorem summable_finite_rows {α β : Type*} {f : α × β → ℝ}
    {s : Set α} (hs : s.Finite) (hf : ∀ x ∈ s, Summable (fun y => f (x, y)))
    (hz : ∀ x ∉ s, ∀ y, f (x, y) = 0) : Summable f := by
  apply Summable.of_norm
  refine (summable_prod_of_nonneg (fun q => norm_nonneg (f q))).mpr ⟨?_, ?_⟩
  · intro x
    by_cases hx : x ∈ s
    · exact (hf x hx).norm
    · simpa only [hz x hx, norm_zero] using
        (summable_zero : Summable (fun _ : β => (0 : ℝ)))
  · apply summable_of_hasFiniteSupport
    apply hs.subset
    intro x hx
    by_contra hxs
    apply hx
    simp only [hz x hxs, norm_zero, tsum_zero]

/-- Antisymmetry and local row summability suffice for pairing summability and summation
by parts against every finite test. This generic identity includes the factor two. -/
theorem antisymmetric_pairing_eq (g : Site d → Site d → ℝ)
    (hanti : ∀ x y, g x y = -g y x) {w : Site d → ℝ}
    (hw : Function.HasFiniteSupport w)
    (hrow : ∀ x ∈ Function.support w, Summable (fun z => g (x + z) x)) :
    Summable (fun q : Site d × Site d =>
      g (q.1 + q.2) q.1 * (w (q.1 + q.2) - w q.1)) ∧
      (∑' q : Site d × Site d,
        g (q.1 + q.2) q.1 * (w (q.1 + q.2) - w q.1)) =
        -2 * ∑' x, (∑' z, g (x + z) x) * w x := by
  let f : Site d × Site d → ℝ := fun q => g (q.1 + q.2) q.1 * w q.1
  have hf : Summable f := summable_finite_rows hw
    (fun x hx => (hrow x hx).mul_right (w x))
    (fun x hx z => by dsimp [f]; rw [not_ne_iff.mp hx, mul_zero])
  have hr : Summable (fun q => f (displacementReverse d q)) :=
    (displacementReverse d).summable_iff.mpr hf
  have he (q : Site d × Site d) :
      g (q.1 + q.2) q.1 * (w (q.1 + q.2) - w q.1) =
        -f (displacementReverse d q) - f q := by
    dsimp [f, displacementReverse]
    rw [add_neg_cancel_right, hanti q.1 (q.1 + q.2)]
    ring
  have hfrow : (∑' q, f q) = ∑' x, (∑' z, g (x + z) x) * w x := by
    rw [hf.tsum_prod]
    exact tsum_congr (fun x => tsum_mul_right (f := fun z => g (x + z) x) (a := w x))
  refine ⟨(hr.neg.sub hf).congr (fun q => (he q).symm), ?_⟩
  simp_rw [he]
  rw [hr.neg.tsum_sub hf, tsum_neg, (displacementReverse d).tsum_eq f, hfrow]
  ring

/-- The unit delta test at an integer lattice site. -/
def deltaTest (x : Site d) (y : Site d) : ℝ := if y = x then 1 else 0

/-- A delta test has support exactly its distinguished singleton. -/
theorem support_deltaTest (x : Site d) : Function.support (deltaTest x) = {x} := by
  ext y
  simp only [Function.mem_support, deltaTest, Set.mem_singleton_iff]
  split_ifs <;> simp_all only [ne_eq, one_ne_zero, not_false_eq_true, not_true_eq_false]

/-- Delta tests are finitely supported. -/
theorem hasFiniteSupport_deltaTest (x : Site d) :
    Function.HasFiniteSupport (deltaTest x) := by
  change (Function.support (deltaTest x)).Finite
  rw [support_deltaTest]
  exact Set.finite_singleton x

/-- Pairing with a unit delta gives minus twice the absolutely convergent divergence row. -/
theorem antisymmetric_pairing_deltaTest (g : Site d → Site d → ℝ)
    (hanti : ∀ x y, g x y = -g y x) (x : Site d)
    (hrow : Summable (fun z => g (x + z) x)) :
    Summable (fun q : Site d × Site d =>
      g (q.1 + q.2) q.1 * (deltaTest x (q.1 + q.2) - deltaTest x q.1)) ∧
      (∑' q : Site d × Site d,
        g (q.1 + q.2) q.1 * (deltaTest x (q.1 + q.2) - deltaTest x q.1)) =
        -2 * ∑' z, g (x + z) x := by
  have h := antisymmetric_pairing_eq g hanti (hasFiniteSupport_deltaTest x) (by
    intro y hy
    rw [support_deltaTest, Set.mem_singleton_iff] at hy
    exact hy ▸ hrow)
  refine ⟨h.1, h.2.trans ?_⟩
  congr 1
  rw [tsum_eq_single x (fun y hy => by rw [deltaTest, if_neg hy, mul_zero])]
  rw [deltaTest, if_pos rfl, mul_one]

/-- Translation of a delta test shifts its distinguished site by the opposite amount. -/
theorem deltaTest_add (a x z : Site d) : deltaTest a (x + z) = deltaTest (a - x) z := by
  have he : x + z = a ↔ z = a - x := by
    constructor
    · intro h
      rw [← h]
      abel
    · intro h
      rw [h]
      abel
  simp only [deltaTest, he]

/-- A unit delta has total mass one. -/
theorem tsum_deltaTest (x : Site d) : (∑' y, deltaTest x y) = 1 := by
  rw [tsum_eq_single x (f := deltaTest x) (fun y hy => if_neg hy)]
  exact if_pos rfl

/-- The antisymmetric unit edge oriented from `a` to `b`. -/
def singleEdgeField (a b x y : Site d) : ℝ :=
  deltaTest b x * deltaTest a y - deltaTest a x * deltaTest b y

/-- The unit edge field obeys the literal source antisymmetry convention. -/
theorem singleEdgeField_antisymmetric (a b x y : Site d) :
    singleEdgeField a b x y = -singleEdgeField a b y x := by
  dsimp only [singleEdgeField]
  ring

/-- The unit edge field is supported on its two orientations. -/
theorem hasFiniteSupport_singleEdgeField (a b : Site d) :
    Function.HasFiniteSupport (fun q : Site d × Site d => singleEdgeField a b q.1 q.2) := by
  apply (Set.toFinite ({(b, a), (a, b)} : Set (Site d × Site d))).subset
  rintro ⟨x, y⟩ hxy
  by_contra h
  apply hxy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
  simp only [singleEdgeField, deltaTest]
  split_ifs <;> simp_all only [mul_one, mul_zero, sub_self,
    zero_sub, not_true_eq_false, and_self, true_or, or_true]

/-- Every row of a unit edge field is absolutely summable, with divergence equal to
one at its initial site and minus one at its terminal site. -/
theorem singleEdgeField_row (a b x : Site d) :
    Summable (fun z => singleEdgeField a b (x + z) x) ∧
      (∑' z, singleEdgeField a b (x + z) x) = deltaTest a x - deltaTest b x := by
  have ha : Summable (deltaTest (a - x)) :=
    summable_of_hasFiniteSupport (hasFiniteSupport_deltaTest (a - x))
  have hb : Summable (deltaTest (b - x)) :=
    summable_of_hasFiniteSupport (hasFiniteSupport_deltaTest (b - x))
  simp only [singleEdgeField, deltaTest_add]
  refine ⟨(hb.mul_right _).sub (ha.mul_right _), ?_⟩
  rw [(hb.mul_right _).tsum_sub (ha.mul_right _), tsum_mul_right, tsum_mul_right,
    tsum_deltaTest, tsum_deltaTest, one_mul, one_mul]

/-- A nontrivial unit edge is not solenoidal, and its delta pairing is exactly minus two. -/
theorem singleEdgeField_not_solenoidal {a b : Site d} (hab : a ≠ b) :
    (∑' z, singleEdgeField a b (a + z) a) = 1 ∧
      (∑' q : Site d × Site d,
        singleEdgeField a b (q.1 + q.2) q.1 *
          (deltaTest a (q.1 + q.2) - deltaTest a q.1)) = -2 := by
  have hrow : (∑' z, singleEdgeField a b (a + z) a) = 1 := by
    rw [(singleEdgeField_row a b a).2]
    simp [deltaTest, hab]
  refine ⟨hrow, ?_⟩
  rw [(antisymmetric_pairing_deltaTest (singleEdgeField a b)
    (singleEdgeField_antisymmetric a b) a (singleEdgeField_row a b a).1).2, hrow, mul_one]

end

end LatticeProb.AntisymmetricPairing
