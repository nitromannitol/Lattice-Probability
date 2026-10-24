import LatticeProb.Walk.SRW
import LatticeProb.Walk.SRWOneDim
import LatticeProb.Walk.BinomialLower

/-!
# Coordinate formulas for the simple random walk

The one-dimensional kernel is the binomial probability at every reachable site and vanishes
at all other sites. Coordinate averaging operators give the decomposition by coordinate times.
-/

namespace LatticeProb

open Finset

/-- Every one-dimensional site is determined by its zeroth coordinate. -/
private theorem site_one_eq (x : Site 1) : x = ![x 0] := by
  funext i
  fin_cases i
  rfl

/-- The binomial kernel at a reachable site, with displacement computed in the integers. -/
theorem srwHeat_one_eq_choose (n j : ℕ) (x : Site 1) (hj : j ≤ n)
    (hx : x 0 = 2 * (j : ℤ) - n) :
    srwHeat 1 n x = (Nat.choose n j : ℝ) / 2 ^ n := by
  have hsite : x = ![(j : ℤ) - ((n - j : ℕ) : ℤ)] := by
    rw [site_one_eq x]
    congr 1
    rw [hx, Nat.cast_sub hj]
    ring
  rw [hsite]
  exact srwHeat_one_binom n j (n - j) (by omega)

/-- The kernel vanishes when no admissible binomial index represents the displacement. -/
theorem srwHeat_one_eq_zero_of_not_exists (n : ℕ) (x : Site 1)
    (hx : ¬ ∃ j : ℕ, j ≤ n ∧ x 0 = 2 * (j : ℤ) - n) :
    srwHeat 1 n x = 0 := by
  induction n generalizing x with
  | zero =>
      rw [srwHeat_zero, if_neg]
      intro h
      apply hx
      exact ⟨0, le_rfl, by simp [h]⟩
  | succ n ih =>
      rw [site_one_eq x, srwHeat_one_succ]
      have hminus : ¬ ∃ j : ℕ, j ≤ n ∧
          (![x 0 - 1] : Site 1) 0 = 2 * (j : ℤ) - n := by
        rintro ⟨j, hj, he⟩
        apply hx
        refine ⟨j + 1, by omega, ?_⟩
        simp only [Matrix.cons_val_zero] at he
        push_cast
        omega
      have hplus : ¬ ∃ j : ℕ, j ≤ n ∧
          (![x 0 + 1] : Site 1) 0 = 2 * (j : ℤ) - n := by
        rintro ⟨j, hj, he⟩
        apply hx
        refine ⟨j, by omega, ?_⟩
        simp only [Matrix.cons_val_zero] at he
        push_cast
        omega
      rw [ih _ hminus, ih _ hplus]
      norm_num


/-- Averaging in one integer coordinate. -/
private noncomputable def integerAverage : Module.End ℝ (ℤ → ℝ) where
  toFun f a := (f (a - 1) + f (a + 1)) / 2
  map_add' f g := by funext a; dsimp; ring
  map_smul' c f := by funext a; dsimp; ring

/-- Averaging only the selected coordinate of a lattice function. -/
private noncomputable def coordinateAverage {d : ℕ} (i : Fin d) :
    Module.End ℝ (Site d → ℝ) where
  toFun f x := (f (Function.update x i (x i - 1)) +
    f (Function.update x i (x i + 1))) / 2
  map_add' f g := by funext x; dsimp; ring
  map_smul' c f := by funext x; dsimp; ring

/-- A product of functions, one for each coordinate. -/
private noncomputable def coordinateProduct {d : ℕ} (f : Fin d → ℤ → ℝ) :
    Site d → ℝ := fun x => ∏ i, f i (x i)

/-- Distinct coordinate averaging operators commute. -/
private theorem coordinateAverage_commute {d : ℕ} (i j : Fin d) :
    Commute (coordinateAverage i) (coordinateAverage j) := by
  by_cases h : i = j
  · subst j; rfl
  ext f x
  simp only [Module.End.mul_apply, coordinateAverage, LinearMap.coe_mk,
    AddHom.coe_mk, Function.update_of_ne h, Function.update_of_ne (Ne.symm h)]
  simp only [Function.update_comm h]
  ring

/-- A product separates an updated coordinate from all the unchanged coordinates. -/
private theorem coordinateProduct_update {d : ℕ} (f : Fin d → ℤ → ℝ)
    (x : Site d) (i : Fin d) (a : ℤ) :
    coordinateProduct f (Function.update x i a) =
      f i a * ∏ j ∈ univ.erase i, f j (x j) := by
  classical
  rw [coordinateProduct, ← Finset.mul_prod_erase _ _ (mem_univ i)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (mem_erase.mp hj).1]

/-- Coordinate averaging acts on just one factor of a product. -/
private theorem coordinateAverage_product {d : ℕ} (i : Fin d)
    (f : Fin d → ℤ → ℝ) :
    coordinateAverage i (coordinateProduct f) =
      coordinateProduct (Function.update f i (integerAverage (f i))) := by
  classical
  funext x
  change (coordinateProduct f (Function.update x i (x i - 1)) +
    coordinateProduct f (Function.update x i (x i + 1))) / 2 = _
  rw [coordinateProduct_update, coordinateProduct_update]
  rw [coordinateProduct, ← Finset.mul_prod_erase _ _ (mem_univ i)]
  simp only [Function.update_self]
  have he : (∏ j ∈ univ.erase i,
      Function.update f i (integerAverage (f i)) j (x j)) =
      ∏ j ∈ univ.erase i, f j (x j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (mem_erase.mp hj).1]
  rw [he]
  change _ = ((f i (x i - 1) + f i (x i + 1)) / 2) * _
  ring

/-- Repeated coordinate averaging acts by the corresponding one-dimensional power. -/
private theorem coordinateAverage_pow_product {d : ℕ} (i : Fin d) (n : ℕ)
    (f : Fin d → ℤ → ℝ) :
    (coordinateAverage i ^ n) (coordinateProduct f) =
      coordinateProduct (Function.update f i ((integerAverage ^ n) (f i))) := by
  induction n with
  | zero => simp only [pow_zero, Module.End.one_apply, Function.update_eq_self]
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih, coordinateAverage_product]
      simp only [Function.update_self, Function.update_idem, pow_succ', Module.End.mul_apply]

/-- A product of coordinate powers acts independently on every selected factor. -/
private theorem coordinateAverage_noncommProd {d : ℕ} (s : Finset (Fin d))
    (m : Fin d → ℕ) (f : Fin d → ℤ → ℝ)
    (hc : (s : Set (Fin d)).Pairwise
      (fun i j => Commute (coordinateAverage i ^ m i) (coordinateAverage j ^ m j))) :
    (s.noncommProd (fun i => coordinateAverage i ^ m i) hc) (coordinateProduct f) =
      coordinateProduct (fun i => if i ∈ s then (integerAverage ^ m i) (f i) else f i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp only [Finset.noncommProd_empty, Module.End.one_apply,
      Finset.notMem_empty, ↓reduceIte]
  | cons a s ha ih =>
      rw [Finset.noncommProd_cons, Module.End.mul_apply, ih,
        coordinateAverage_pow_product]
      congr 1
      funext i
      by_cases hi : i = a
      · subst i
        simp only [Function.update_self, ha, ↓reduceIte, mem_cons, true_or]
      · simp only [Function.update_of_ne hi, mem_cons, hi, false_or]

/-- The integer averaging powers started at the origin are the one-dimensional kernel. -/
private theorem integerAverage_pow_origin (n : ℕ) :
    (integerAverage ^ n) (fun a : ℤ => if a = 0 then 1 else 0) =
      fun a => srwHeat 1 n ![a] := by
  induction n with
  | zero =>
      funext a
      simp only [pow_zero, Module.End.one_apply, srwHeat_zero]
      congr 1
      apply propext
      constructor
      · intro h; subst a; ext i; fin_cases i; rfl
      · intro h; exact congrFun h 0
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      funext a
      exact (srwHeat_one_succ n a).symm


/-- The origin indicator factors over the coordinates. -/
private theorem coordinateProduct_origin (d : ℕ) :
    coordinateProduct (fun (_ : Fin d) (a : ℤ) => if a = 0 then 1 else 0) =
      fun x : Site d => if x = 0 then 1 else 0 := by
  classical
  funext x
  by_cases hx : x = 0
  · simp [coordinateProduct, hx]
  · rw [if_neg hx]
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      apply hx
      funext i
      simpa using not_exists.mp h i
    exact Finset.prod_eq_zero (mem_univ i) (if_neg hi)

/-- Summing the coordinate averages and dividing by the dimension gives the walk operator. -/
private theorem coordinateAverage_sum {d : ℕ} (f : Site d → ℝ) (x : Site d) :
    ((1 / (d : ℝ)) • ∑ i : Fin d, coordinateAverage i) f x = walkOp f x := by
  classical
  have hm (i : Fin d) : Function.update x i (x i - 1) = x - unit i := by
    funext j
    by_cases h : j = i <;> simp [h, unit]
  have hp (i : Fin d) : Function.update x i (x i + 1) = x + unit i := by
    funext j
    by_cases h : j = i <;> simp [h, unit]
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_apply, coordinateAverage, LinearMap.coe_mk, AddHom.coe_mk, hm, hp]
  rw [walkOp, nbrSum, ← Finset.sum_div]
  have he : (∑ i : Fin d, (f (x - unit i) + f (x + unit i))) =
      ∑ i : Fin d, (f (x + unit i) + f (x - unit i)) := by
    apply Finset.sum_congr rfl
    intro i _
    exact add_comm _ _
  rw [he]
  ring

/-- Powers of the normalized sum of coordinate averages give the actual SRW kernel. -/
private theorem coordinateAverage_sum_pow_origin (d n : ℕ) :
    (((1 / (d : ℝ)) • ∑ i : Fin d, coordinateAverage i) ^ n)
        (coordinateProduct (fun (_ : Fin d) (a : ℤ) => if a = 0 then 1 else 0)) =
      srwHeat d n := by
  rw [coordinateProduct_origin]
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', Module.End.mul_apply, ih]
      funext x
      exact coordinateAverage_sum _ _

/-- The composition index set imposes exactly the prescribed total time. -/
theorem mem_srw_compositions {d n : ℕ} {m : Fin d → ℕ} :
    m ∈ Finset.piAntidiag (univ : Finset (Fin d)) n ↔ ∑ i, m i = n := by
  simp only [Finset.mem_piAntidiag, mem_univ, implies_true, and_true]

/-- The simple walk is the multinomial mixture of its one-dimensional coordinate kernels.
The compositions are indexed by `Finset.piAntidiag univ n`. -/
theorem srwHeat_eq_multinomial (d n : ℕ) (x : Site d) :
    srwHeat d n x =
      ∑ m ∈ Finset.piAntidiag (univ : Finset (Fin d)) n,
        (Nat.multinomial univ m : ℝ) * (1 / (d : ℝ)) ^ n *
          ∏ i : Fin d, srwHeat 1 (m i) (fun _ => x i) := by
  classical
  have hc : (↑(univ : Finset (Fin d)) : Set (Fin d)).Pairwise
      (fun i j => Commute (coordinateAverage i) (coordinateAverage j)) := by
    intro i _ j _ _
    exact coordinateAverage_commute i j
  rw [← congrFun (coordinateAverage_sum_pow_origin d n) x, smul_pow,
    Finset.sum_pow_eq_sum_piAntidiag_of_commute univ coordinateAverage hc n]
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.sum_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [Module.End.mul_apply, coordinateAverage_noncommProd]
  simp only [mem_univ, ↓reduceIte]
  simp only [integerAverage_pow_origin]
  have hsite (a : ℤ) : (![a] : Site 1) = fun _ => a := by
    funext i
    fin_cases i
    rfl
  simp only [Module.End.natCast_apply, Pi.smul_apply, nsmul_eq_mul]
  dsimp only [coordinateProduct]
  simp only [hsite]
  ring

end LatticeProb
