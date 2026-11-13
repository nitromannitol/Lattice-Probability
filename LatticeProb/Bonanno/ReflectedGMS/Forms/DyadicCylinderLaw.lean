/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Forms.DyadicCylinderLaw at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Forms.DyadicFiniteBitLaw

/-! The arbitrary integer level cylinder law of the constructed dyadic grid.

`DyadicGridLaw.map_gridCylinder_gridMeasure` reduces `DyadicApproximation.UniformGridLaw`
for `DyadicGridLaw.gridMeasure` to the law of the five uniform source coordinates,
and `DyadicFiniteBitLaw.map_shiftBits_unitMeasure` gives the exact joint law of the
remainder and finitely many binary digits of one uniform coordinate.  The remaining
mathematical point is that a grid cylinder at an arbitrary integer level `k` reads
those digits in a way that straddles `0`: at levels `k ≤ m < 0` the parent digit is a
binary digit of the level zero coordinate `u`, at levels `m ≥ 0` it is a digit of the
second coordinate `w`, and the relative origin `rel` at level `k` is either a shifted
remainder of `u` (when `k < 0`) or the dyadic gluing of `u` with the `w` digits below
level `k` (when `k ≥ 0`).

The ingredients proved here are

* the exact binary expansion identity `fract_pow_expansion`, which inverts the finite
  bit map through the digit reversal `Fin.rev` and yields `map_glueDigits`: gluing a
  uniform remainder with independent fair digits returns an exactly uniform real;
* a small toolkit for uniform laws on finite types, so every regrouping of digit
  tuples (splitting, reversal, assembly across the sign change) is a single bijective
  reindexing rather than a new probabilistic argument;
* the resulting mixed sign law `map_coordCylinder` of one planar coordinate, valid at
  every integer level and for every number of digits.

The endpoints are the exact half-open ones of the source statement and no level range
is excluded. -/

set_option autoImplicit false

open MeasureTheory Set

open scoped ENNReal

namespace ReflectedGMS.DyadicCylinderLaw

open ReflectedGMS.DyadicApproximation ReflectedGMS.DyadicGridLaw ReflectedGMS.DyadicDigitLaw
  ReflectedGMS.DyadicFiniteBitLaw

/-! ### Uniform laws on finite types -/

/-- A bijection transports a uniform law on a finite type to the uniform law. -/
theorem map_uniformOfFintype_of_bijective {α β : Type*} [Fintype α] [Nonempty α] [Fintype β]
    [Nonempty β] [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] (F : α → β) (hF : Function.Bijective F) :
    Measure.map F (PMF.uniformOfFintype α).toMeasure = (PMF.uniformOfFintype β).toMeasure := by
  have hmeas : Measurable F := measurable_of_countable F
  refine Measure.ext_of_singleton fun b => ?_
  obtain ⟨a₀, ha₀⟩ := hF.surjective b
  have hpre : F ⁻¹' {b} = {a₀} := by
    ext a
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · intro h
      exact hF.injective (by rw [h, ha₀])
    · intro h
      rw [h, ha₀]
  rw [Measure.map_apply hmeas (measurableSet_singleton b), hpre,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply, Fintype.card_of_bijective hF]

/-- The product of two uniform laws on finite types is the uniform law on the product. -/
theorem toMeasure_uniformOfFintype_prod {α β : Type*} [Fintype α] [Nonempty α] [Fintype β]
    [Nonempty β] [MeasurableSpace α] [MeasurableSpace β] [MeasurableSingletonClass α]
    [MeasurableSingletonClass β] :
    (PMF.uniformOfFintype α).toMeasure.prod (PMF.uniformOfFintype β).toMeasure
      = (PMF.uniformOfFintype (α × β)).toMeasure := by
  refine Measure.ext_of_singleton fun p => ?_
  have hcard0 : (Fintype.card α : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero (α := α)
  have hcardtop : (Fintype.card α : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hL : ((PMF.uniformOfFintype α).toMeasure.prod (PMF.uniformOfFintype β).toMeasure) {p}
      = (Fintype.card α : ℝ≥0∞)⁻¹ * (Fintype.card β : ℝ≥0∞)⁻¹ := by
    have hs : ({p.1} : Set α) ×ˢ ({p.2} : Set β) = {p} := by
      rw [Set.singleton_prod_singleton]
    rw [← hs, Measure.prod_prod, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
      PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply]
  have hR : ((PMF.uniformOfFintype (α × β)).toMeasure) {p}
      = (Fintype.card α : ℝ≥0∞)⁻¹ * (Fintype.card β : ℝ≥0∞)⁻¹ := by
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
      PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul,
      ENNReal.mul_inv (Or.inl hcard0) (Or.inl hcardtop)]
  rw [hL, hR]

/-- Independent uniform laws in each of finitely many slots form the uniform law on the
function type. -/
theorem pi_uniformOfFintype {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] :
    (Measure.pi fun _ : ι => (PMF.uniformOfFintype α).toMeasure)
      = (PMF.uniformOfFintype (ι → α)).toMeasure := by
  refine Measure.ext_of_singleton fun f => ?_
  have hslot : ∀ i : ι,
      (PMF.uniformOfFintype α).toMeasure {f i} = (Fintype.card α : ℝ≥0∞)⁻¹ := by
    intro i
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), PMF.uniformOfFintype_apply]
  have hcard : (Fintype.card (ι → α) : ℝ≥0∞)
      = (Fintype.card α : ℝ≥0∞) ^ (Fintype.card ι) := by
    rw [Fintype.card_fun]
    push_cast
    ring
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton f), PMF.uniformOfFintype_apply,
    Measure.pi_singleton, Finset.prod_congr rfl fun i _ => hslot i, Finset.prod_const, hcard,
    ENNReal.inv_pow, Finset.card_univ]

/-! ### Regrouping digit tuples -/

/-- Reindexing finitely many fair digits along a bijection. -/
theorem map_comp_digitMeasure {n m : ℕ} (σ : Fin n → Fin m) (hσ : Function.Bijective σ) :
    Measure.map (fun d : Fin m → Fin 2 => d ∘ σ) (digitMeasure m) = digitMeasure n := by
  obtain ⟨g, hgl, hgr⟩ := Function.bijective_iff_has_inverse.1 hσ
  have hbij : Function.Bijective (fun d : Fin m → Fin 2 => d ∘ σ) := by
    refine Function.bijective_iff_has_inverse.2 ⟨fun c => c ∘ g, fun d => ?_, fun c => ?_⟩
    · funext i
      simp only [Function.comp_apply, hgr i]
    · funext j
      simp only [Function.comp_apply, hgl j]
  rw [digitMeasure_eq_uniformOfFintype, digitMeasure_eq_uniformOfFintype,
    map_uniformOfFintype_of_bijective _ hbij]

/-- Reversing the order of finitely many fair digits. -/
theorem map_rev_digitMeasure (n : ℕ) :
    Measure.map (fun d : Fin n → Fin 2 => d ∘ Fin.rev) (digitMeasure n) = digitMeasure n :=
  map_comp_digitMeasure Fin.rev Fin.rev_bijective

/-- Splitting `a + n` fair digits into the first `a` and the last `n`. -/
theorem map_split_digitMeasure (a n : ℕ) :
    Measure.map (fun d : Fin (a + n) → Fin 2 => (d ∘ Fin.castAdd n, d ∘ Fin.natAdd a))
        (digitMeasure (a + n))
      = (digitMeasure a).prod (digitMeasure n) := by
  have hbij : Function.Bijective
      (fun d : Fin (a + n) → Fin 2 => (d ∘ Fin.castAdd n, d ∘ Fin.natAdd a)) := by
    refine Function.bijective_iff_has_inverse.2
      ⟨fun p => Fin.append p.1 p.2, fun d => ?_, fun p => ?_⟩
    · funext j
      induction j using Fin.addCases with
      | left i => simp
      | right i => simp
    · have h1 : (Fin.append p.1 p.2) ∘ Fin.castAdd n = p.1 := by
        funext i
        simp
      have h2 : (Fin.append p.1 p.2) ∘ Fin.natAdd a = p.2 := by
        funext i
        simp
      simp only [h1, h2]
  rw [digitMeasure_eq_uniformOfFintype, digitMeasure_eq_uniformOfFintype,
    digitMeasure_eq_uniformOfFintype, toMeasure_uniformOfFintype_prod,
    map_uniformOfFintype_of_bijective _ hbij]

/-- Assembling `n` fair digits out of two independent blocks along a bijective index
map.  This is the regrouping used at a level range straddling `0`. -/
theorem map_assemble_digitMeasure {t q n : ℕ} (σ : Fin n → Fin t ⊕ Fin q)
    (hσ : Function.Bijective σ) :
    Measure.map (fun p : (Fin t → Fin 2) × (Fin q → Fin 2) =>
        fun j : Fin n => Sum.elim p.1 p.2 (σ j))
      ((digitMeasure t).prod (digitMeasure q)) = digitMeasure n := by
  obtain ⟨g, hgl, hgr⟩ := Function.bijective_iff_has_inverse.1 hσ
  have hbij : Function.Bijective (fun p : (Fin t → Fin 2) × (Fin q → Fin 2) =>
      fun j : Fin n => Sum.elim p.1 p.2 (σ j)) := by
    refine Function.bijective_iff_has_inverse.2
      ⟨fun c => (fun i => c (g (Sum.inl i)), fun i => c (g (Sum.inr i))),
        fun p => ?_, fun c => ?_⟩
    · have h1 : (fun i : Fin t => Sum.elim p.1 p.2 (σ (g (Sum.inl i)))) = p.1 := by
        funext i
        rw [hgr]
        rfl
      have h2 : (fun i : Fin q => Sum.elim p.1 p.2 (σ (g (Sum.inr i)))) = p.2 := by
        funext i
        rw [hgr]
        rfl
      simp only [h1, h2]
    · funext j
      show Sum.elim (fun i => c (g (Sum.inl i))) (fun i => c (g (Sum.inr i))) (σ j) = c j
      have key : ∀ x : Fin t ⊕ Fin q,
          Sum.elim (fun i => c (g (Sum.inl i))) (fun i => c (g (Sum.inr i))) x = c (g x) := by
        rintro (i | i) <;> rfl
      rw [key, hgl j]
  rw [digitMeasure_eq_uniformOfFintype, digitMeasure_eq_uniformOfFintype,
    digitMeasure_eq_uniformOfFintype, toMeasure_uniformOfFintype_prod,
    map_uniformOfFintype_of_bijective _ hbij]

/-! ### The exact binary expansion identity -/

theorem bitFin_val (x : ℝ) : ((bitFin x).val : ℝ) = (bitInt x : ℝ) := by
  have h0 := bitInt_nonneg x
  have h2 := bitInt_lt_two x
  have h : bitInt x = 0 ∨ bitInt x = 1 := by omega
  rcases h with h | h <;> simp [bitFin, intToFin2, h]

/-- **Exact finite binary expansion.**  The first `a` binary digits, read with the digit
at index `a - 1 - j` in the slot of weight `2 ^ j`, reconstruct a real number from the
remainder after `a` shifts. -/
theorem fract_pow_expansion (a : ℕ) : ∀ y : ℝ,
    (2 : ℝ) ^ a * Int.fract y
      = Int.fract ((2 : ℝ) ^ a * y)
        + ∑ j ∈ Finset.range a, (2 : ℝ) ^ j * (bitInt ((2 : ℝ) ^ (a - 1 - j) * y) : ℝ) := by
  induction a with
  | zero =>
    intro y
    simp
  | succ a ih =>
    intro y
    have hsum : ∑ j ∈ Finset.range a, (2 : ℝ) ^ j * (bitInt ((2 : ℝ) ^ (a - 1 - j) * (2 * y)) : ℝ)
        = ∑ j ∈ Finset.range a, (2 : ℝ) ^ j * (bitInt ((2 : ℝ) ^ (a + 1 - 1 - j) * y) : ℝ) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : j < a := Finset.mem_range.1 hj
      have he : a + 1 - 1 - j = (a - 1 - j) + 1 := by omega
      have hx : (2 : ℝ) ^ (a - 1 - j) * (2 * y) = (2 : ℝ) ^ (a + 1 - 1 - j) * y := by
        rw [he, pow_succ]
        ring
      rw [hx]
    have hlast : (2 : ℝ) ^ a * (bitInt ((2 : ℝ) ^ (a + 1 - 1 - a) * y) : ℝ)
        = (2 : ℝ) ^ a * (bitInt y : ℝ) := by
      have h0 : a + 1 - 1 - a = 0 := by omega
      rw [h0, pow_zero, one_mul]
    have hps : (2 : ℝ) ^ (a + 1) = 2 ^ a * 2 := pow_succ 2 a
    have hpow : (2 : ℝ) ^ a * (2 * y) = (2 : ℝ) ^ (a + 1) * y := by ring
    have ihy := ih (2 * y)
    rw [hpow, hps] at ihy
    rw [Finset.sum_range_succ, hlast, ← hsum, fract_eq_half y, hps]
    linarith [ihy]

/-! ### Gluing a uniform remainder with independent fair digits -/

/-- The integer represented by finitely many digits, the digit in slot `j` carrying the
weight `2 ^ j` exactly as in `DyadicGridLaw.futureNum`. -/
noncomputable def digitValue {a : ℕ} (d : Fin a → Fin 2) : ℝ :=
  ∑ j : Fin a, (2 : ℝ) ^ (j : ℕ) * ((d j).val : ℝ)

/-- The dyadic gluing of a remainder with finitely many digits. -/
noncomputable def glueDigits (a : ℕ) (p : ℝ × (Fin a → Fin 2)) : ℝ :=
  ((2 : ℝ) ^ a)⁻¹ * (p.1 + digitValue p.2)

theorem measurable_digitValue (a : ℕ) : Measurable (digitValue (a := a)) :=
  measurable_of_countable _

theorem measurable_glueDigits (a : ℕ) : Measurable (glueDigits a) :=
  measurable_const.mul (measurable_fst.add ((measurable_digitValue a).comp measurable_snd))

theorem ae_mem_Ico_unitMeasure : ∀ᵐ x ∂unitMeasure, x ∈ Set.Ico (0 : ℝ) 1 := by
  rw [unitMeasure]
  exact ae_restrict_mem measurableSet_Ico

/-- Gluing inverts the finite bit map, once the digits are reversed. -/
theorem glueDigits_shiftBits_rev (a : ℕ) {y : ℝ} (hy : y ∈ Set.Ico (0 : ℝ) 1) :
    glueDigits a ((shiftBits a y).1, (shiftBits a y).2 ∘ Fin.rev) = y := by
  have hval : digitValue ((shiftBits a y).2 ∘ Fin.rev)
      = ∑ j ∈ Finset.range a, (2 : ℝ) ^ j * (bitInt ((2 : ℝ) ^ (a - 1 - j) * y) : ℝ) := by
    have h1 : ∀ j : Fin a, (2 : ℝ) ^ (j : ℕ) * (((((shiftBits a y).2 ∘ Fin.rev)) j).val : ℝ)
        = (fun l : ℕ => (2 : ℝ) ^ l * (bitInt ((2 : ℝ) ^ (a - 1 - l) * y) : ℝ)) (j : ℕ) := by
      intro j
      have hrev : ((Fin.rev j : Fin a) : ℕ) = a - 1 - (j : ℕ) := by
        rw [Fin.val_rev]
        omega
      simp only [Function.comp_apply, shiftBits_snd, bitsUpTo, hrev, bitFin_val]
    rw [digitValue, Finset.sum_congr rfl fun j _ => h1 j]
    exact Fin.sum_univ_eq_sum_range
      (fun l : ℕ => (2 : ℝ) ^ l * (bitInt ((2 : ℝ) ^ (a - 1 - l) * y) : ℝ)) a
  have hfy : Int.fract y = y := Int.fract_eq_self.2 ⟨hy.1, hy.2⟩
  have hexp := fract_pow_expansion a y
  rw [hfy] at hexp
  have h2 : ((2 : ℝ) ^ a) ≠ 0 := by positivity
  rw [glueDigits, hval, shiftBits_fst, ← hexp]
  field_simp

/-- **Exact gluing law.**  A uniform remainder glued with independent fair digits is
again exactly uniform on the half-open unit interval. -/
theorem map_glueDigits (a : ℕ) :
    Measure.map (glueDigits a) (unitMeasure.prod (digitMeasure a)) = unitMeasure := by
  have := isProbabilityMeasure_unitMeasure
  have hrevmeas : Measurable (fun d : Fin a → Fin 2 => d ∘ Fin.rev) := measurable_of_countable _
  have hpairmeas : Measurable (Prod.map (id : ℝ → ℝ) (fun d : Fin a → Fin 2 => d ∘ Fin.rev)) :=
    measurable_id.prodMap hrevmeas
  have hrev : Measure.map (Prod.map (id : ℝ → ℝ) (fun d : Fin a → Fin 2 => d ∘ Fin.rev))
      (unitMeasure.prod (digitMeasure a)) = unitMeasure.prod (digitMeasure a) := by
    rw [← Measure.map_prod_map unitMeasure (digitMeasure a) measurable_id hrevmeas,
      Measure.map_id, map_rev_digitMeasure a]
  calc Measure.map (glueDigits a) (unitMeasure.prod (digitMeasure a))
      = Measure.map (glueDigits a)
          (Measure.map (Prod.map (id : ℝ → ℝ) (fun d : Fin a → Fin 2 => d ∘ Fin.rev))
            (unitMeasure.prod (digitMeasure a))) := by rw [hrev]
    _ = Measure.map (glueDigits a ∘
          (Prod.map (id : ℝ → ℝ) (fun d : Fin a → Fin 2 => d ∘ Fin.rev)))
          (unitMeasure.prod (digitMeasure a)) := by
          rw [Measure.map_map (measurable_glueDigits a) hpairmeas]
    _ = Measure.map (glueDigits a ∘
          (Prod.map (id : ℝ → ℝ) (fun d : Fin a → Fin 2 => d ∘ Fin.rev)))
          (Measure.map (shiftBits a) unitMeasure) := by rw [map_shiftBits_unitMeasure a]
    _ = Measure.map ((glueDigits a ∘
          (Prod.map (id : ℝ → ℝ) (fun d : Fin a → Fin 2 => d ∘ Fin.rev))) ∘ shiftBits a)
          unitMeasure := by
          rw [Measure.map_map ((measurable_glueDigits a).comp hpairmeas) (measurable_shiftBits a)]
    _ = Measure.map id unitMeasure := by
          refine Measure.map_congr ?_
          filter_upwards [ae_mem_Ico_unitMeasure] with y hy
          exact glueDigits_shiftBits_rev a hy
    _ = unitMeasure := Measure.map_id

/-! ### The cylinder data of one planar coordinate -/

/-- The parent digit of a single planar coordinate: the `i`-th component of
`DyadicGridLaw.digitInt`, which depends only on the `i`-th source coordinates. -/
noncomputable def coordDigitInt (x y : ℝ) (k : ℤ) : ℤ :=
  if k < 0 then bitInt ((2 : ℝ) ^ (-(k + 1)) * Int.fract x)
  else bitInt ((2 : ℝ) ^ k * Int.fract y)

noncomputable def coordDigitFin (x y : ℝ) (k : ℤ) : Fin 2 := intToFin2 (coordDigitInt x y k)

/-- The integer accumulated from the digits below level `k`, in one coordinate. -/
noncomputable def coordFutureNum (x y : ℝ) (k : ℤ) : ℝ :=
  ∑ j ∈ Finset.range k.toNat, (2 : ℝ) ^ j * (coordDigitInt x y (j : ℤ) : ℝ)

/-- The relative origin at level `k`, in one coordinate. -/
noncomputable def coordRel (x y : ℝ) (k : ℤ) : ℝ :=
  Int.fract ((2 : ℝ) ^ (-k) * (Int.fract x + coordFutureNum x y k))

/-- The data read by `DyadicApproximation.gridCylinder` in one planar coordinate: the
relative origin at level `k` and the parent digits at the levels `k, …, k + n - 1`. -/
noncomputable def coordCylinder (k : ℤ) (n : ℕ) (p : ℝ × ℝ) : ℝ × (Fin n → Fin 2) :=
  (coordRel p.1 p.2 k, fun j : Fin n => coordDigitFin p.1 p.2 (k + (j.val : ℤ)))

theorem coordRel_of_nonneg {k : ℤ} (hk : 0 ≤ k) (x y : ℝ) :
    coordRel x y k = (2 : ℝ) ^ (-k) * (Int.fract x + coordFutureNum x y k) :=
  rel_of_nonneg (fun _ => x) (fun _ => y) hk 0

theorem measurable_coordDigitInt (k : ℤ) :
    Measurable fun p : ℝ × ℝ => coordDigitInt p.1 p.2 k := by
  by_cases hk : k < 0
  · simp only [coordDigitInt, if_pos hk]
    exact measurable_bitInt.comp (measurable_const.mul (measurable_fract.comp measurable_fst))
  · simp only [coordDigitInt, if_neg hk]
    exact measurable_bitInt.comp (measurable_const.mul (measurable_fract.comp measurable_snd))

theorem measurable_coordDigitFin (k : ℤ) :
    Measurable fun p : ℝ × ℝ => coordDigitFin p.1 p.2 k :=
  (measurable_of_countable intToFin2).comp (measurable_coordDigitInt k)

theorem measurable_coordFutureNum (k : ℤ) :
    Measurable fun p : ℝ × ℝ => coordFutureNum p.1 p.2 k := by
  simp only [coordFutureNum]
  exact Finset.measurable_sum _ fun j _ => measurable_const.mul
    ((measurable_of_countable fun m : ℤ => (m : ℝ)).comp (measurable_coordDigitInt (j : ℤ)))

theorem measurable_coordRel (k : ℤ) : Measurable fun p : ℝ × ℝ => coordRel p.1 p.2 k := by
  simp only [coordRel]
  exact measurable_fract.comp (measurable_const.mul
    ((measurable_fract.comp measurable_fst).add (measurable_coordFutureNum k)))

theorem measurable_coordCylinder (k : ℤ) (n : ℕ) : Measurable (coordCylinder k n) :=
  (measurable_coordRel k).prodMk
    (Measurable.of_eval fun j => measurable_coordDigitFin (k + (j.val : ℤ)))

theorem ae_mem_Ico_prod_unitMeasure :
    ∀ᵐ p ∂(unitMeasure.prod unitMeasure),
      p.1 ∈ Set.Ico (0 : ℝ) 1 ∧ p.2 ∈ Set.Ico (0 : ℝ) 1 := by
  have h : unitMeasure.prod unitMeasure
      = (volume.prod volume).restrict (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1) := by
    rw [unitMeasure, Measure.prod_restrict]
  rw [h]
  filter_upwards [ae_restrict_mem (measurableSet_Ico.prod measurableSet_Ico)] with p hp
  exact ⟨hp.1, hp.2⟩

/-! ### Invariance of the digits under taking the fractional part -/

theorem fract_pow_mul_fract (a : ℕ) (z : ℝ) :
    Int.fract ((2 : ℝ) ^ a * Int.fract z) = Int.fract ((2 : ℝ) ^ a * z) := by
  have h : (2 : ℝ) ^ a * Int.fract z
      = (2 : ℝ) ^ a * z + ((-(2 ^ a * ⌊z⌋) : ℤ) : ℝ) := by
    rw [fract_eq_add_intCast z]
    push_cast
    ring
  rw [h, Int.fract_add_intCast]

theorem bitInt_pow_mul_fract (a : ℕ) (z : ℝ) :
    bitInt ((2 : ℝ) ^ a * Int.fract z) = bitInt ((2 : ℝ) ^ a * z) := by
  have h : (2 : ℝ) ^ a * Int.fract z
      = (2 : ℝ) ^ a * z + ((-(2 ^ a * ⌊z⌋) : ℤ) : ℝ) := by
    rw [fract_eq_add_intCast z]
    push_cast
    ring
  rw [h, bitInt_add_intCast]

theorem bitFin_pow_mul_fract (a : ℕ) (z : ℝ) :
    bitFin ((2 : ℝ) ^ a * Int.fract z) = bitFin ((2 : ℝ) ^ a * z) := by
  rw [bitFin, bitFin, bitInt_pow_mul_fract]

theorem coordDigitFin_of_nonneg {k : ℤ} (hk : 0 ≤ k) (x y : ℝ) :
    coordDigitFin x y k = bitFin ((2 : ℝ) ^ k.toNat * Int.fract y) := by
  have hk' : ¬ k < 0 := by omega
  have hp : (2 : ℝ) ^ k = (2 : ℝ) ^ k.toNat := by
    rw [← zpow_natCast (2 : ℝ) k.toNat, Int.toNat_of_nonneg hk]
  simp only [coordDigitFin, coordDigitInt, if_neg hk', hp, bitFin]

theorem coordDigitFin_of_neg {k : ℤ} (hk : k < 0) (x y : ℝ) :
    coordDigitFin x y k = bitFin ((2 : ℝ) ^ (-(k + 1)).toNat * Int.fract x) := by
  have hnn : (0 : ℤ) ≤ -(k + 1) := by omega
  have hp : (2 : ℝ) ^ (-(k + 1)) = (2 : ℝ) ^ (-(k + 1)).toNat := by
    rw [← zpow_natCast (2 : ℝ) (-(k + 1)).toNat, Int.toNat_of_nonneg hnn]
  simp only [coordDigitFin, coordDigitInt, if_pos hk, hp, bitFin]

/-! ### Nonnegative levels: gluing the digits below the level -/

/-- The cylinder data at a nonnegative level, read off the finite bit data of the
second coordinate: the digits below the level are glued to the first coordinate, the
digits from the level on are the cylinder digits. -/
noncomputable def glueCombine (a n : ℕ) (p : ℝ × (Fin (a + n) → Fin 2)) :
    ℝ × (Fin n → Fin 2) :=
  (glueDigits a (p.1, p.2 ∘ Fin.castAdd n), p.2 ∘ Fin.natAdd a)

/-- The same with the discarded remainder of the second coordinate still present. -/
noncomputable def glueSplit (a n : ℕ) (p : ℝ × (ℝ × (Fin (a + n) → Fin 2))) :
    ℝ × (Fin n → Fin 2) :=
  glueCombine a n (p.1, p.2.2)

theorem measurable_glueCombine (a n : ℕ) : Measurable (glueCombine a n) :=
  ((measurable_glueDigits a).comp (measurable_fst.prodMk
    ((measurable_of_countable fun d : Fin (a + n) → Fin 2 => d ∘ Fin.castAdd n).comp
      measurable_snd))).prodMk
    ((measurable_of_countable fun d : Fin (a + n) → Fin 2 => d ∘ Fin.natAdd a).comp measurable_snd)

theorem measurable_glueSplit (a n : ℕ) : Measurable (glueSplit a n) :=
  (measurable_glueCombine a n).comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))

theorem coordCylinder_eq_glueSplit {k : ℤ} (hk : 0 ≤ k) (n : ℕ) {x y : ℝ}
    (hx : x ∈ Set.Ico (0 : ℝ) 1) (hy : y ∈ Set.Ico (0 : ℝ) 1) :
    coordCylinder k n (x, y) = glueSplit k.toNat n (x, shiftBits (k.toNat + n) y) := by
  have hfx : Int.fract x = x := Int.fract_eq_self.2 ⟨hx.1, hx.2⟩
  have hfy : Int.fract y = y := Int.fract_eq_self.2 ⟨hy.1, hy.2⟩
  have hcoef : (2 : ℝ) ^ (-k) = ((2 : ℝ) ^ k.toNat)⁻¹ := by
    rw [zpow_neg, ← zpow_natCast (2 : ℝ) k.toNat, Int.toNat_of_nonneg hk]
  have h1 : coordRel x y k
      = glueDigits k.toNat (x, (shiftBits (k.toNat + n) y).2 ∘ Fin.castAdd n) := by
    have hterm : ∀ j : Fin k.toNat,
        (2 : ℝ) ^ (j : ℕ) * (((((shiftBits (k.toNat + n) y).2 ∘ Fin.castAdd n)) j).val : ℝ)
          = (fun l : ℕ => (2 : ℝ) ^ l * (coordDigitInt x y (l : ℤ) : ℝ)) (j : ℕ) := by
      intro j
      have hjnn : ¬ (((j : ℕ) : ℤ) < 0) := by omega
      have hpow : (2 : ℝ) ^ (((j : ℕ) : ℤ)) = (2 : ℝ) ^ (j : ℕ) := zpow_natCast (2 : ℝ) _
      simp only [Function.comp_apply, shiftBits_snd, bitsUpTo, Fin.val_castAdd, bitFin_val,
        coordDigitInt, if_neg hjnn, hpow, hfy]
    have hval : digitValue ((shiftBits (k.toNat + n) y).2 ∘ Fin.castAdd n)
        = coordFutureNum x y k := by
      rw [digitValue, coordFutureNum, Finset.sum_congr rfl fun j _ => hterm j]
      exact Fin.sum_univ_eq_sum_range
        (fun l : ℕ => (2 : ℝ) ^ l * (coordDigitInt x y (l : ℤ) : ℝ)) k.toNat
    simp only [glueDigits, hval, coordRel_of_nonneg hk, hcoef, hfx]
  have h2 : (fun j : Fin n => coordDigitFin x y (k + (j.val : ℤ)))
      = (shiftBits (k.toNat + n) y).2 ∘ Fin.natAdd k.toNat := by
    funext j
    have hkj : 0 ≤ k + (j.val : ℤ) := by omega
    have hnat : (k + (j.val : ℤ)).toNat = k.toNat + (j : ℕ) := by omega
    simp only [Function.comp_apply, shiftBits_snd, bitsUpTo, Fin.val_natAdd,
      coordDigitFin_of_nonneg hkj, hnat, hfy]
  have hpair : coordCylinder k n (x, y)
      = (coordRel x y k, fun j : Fin n => coordDigitFin x y (k + (j.val : ℤ))) := rfl
  rw [hpair, h1, h2]
  rfl

theorem map_glueCombine (a n : ℕ) :
    Measure.map (glueCombine a n) (unitMeasure.prod (digitMeasure (a + n)))
      = unitMeasure.prod (digitMeasure n) := by
  have := isProbabilityMeasure_unitMeasure
  have hsplitmeas : Measurable
      (fun d : Fin (a + n) → Fin 2 => (d ∘ Fin.castAdd n, d ∘ Fin.natAdd a)) :=
    measurable_of_countable _
  have hassocmeas : Measurable
      (⇑(MeasurableEquiv.prodAssoc (α := ℝ) (β := Fin a → Fin 2) (γ := Fin n → Fin 2)).symm) :=
    (MeasurableEquiv.prodAssoc (α := ℝ) (β := Fin a → Fin 2)
      (γ := Fin n → Fin 2)).symm.measurable
  have step1 : Measure.map (Prod.map (id : ℝ → ℝ)
        (fun d : Fin (a + n) → Fin 2 => (d ∘ Fin.castAdd n, d ∘ Fin.natAdd a)))
        (unitMeasure.prod (digitMeasure (a + n)))
      = unitMeasure.prod ((digitMeasure a).prod (digitMeasure n)) := by
    rw [← Measure.map_prod_map unitMeasure (digitMeasure (a + n)) measurable_id hsplitmeas,
      Measure.map_id, map_split_digitMeasure]
  have step2 : Measure.map
        (⇑(MeasurableEquiv.prodAssoc (α := ℝ) (β := Fin a → Fin 2) (γ := Fin n → Fin 2)).symm)
        (unitMeasure.prod ((digitMeasure a).prod (digitMeasure n)))
      = (unitMeasure.prod (digitMeasure a)).prod (digitMeasure n) := by
    have h := Measure.prodAssoc_prod (μ := unitMeasure) (ν := digitMeasure a)
      (τ := digitMeasure n)
    rw [← h, MeasurableEquiv.map_symm_map]
  have step3 : Measure.map
        (Prod.map (glueDigits a) (id : (Fin n → Fin 2) → Fin n → Fin 2))
        ((unitMeasure.prod (digitMeasure a)).prod (digitMeasure n))
      = unitMeasure.prod (digitMeasure n) := by
    rw [← Measure.map_prod_map (unitMeasure.prod (digitMeasure a)) (digitMeasure n)
      (measurable_glueDigits a) measurable_id, Measure.map_id, map_glueDigits]
  have hfun : glueCombine a n
      = (Prod.map (glueDigits a) (id : (Fin n → Fin 2) → Fin n → Fin 2))
        ∘ ((⇑(MeasurableEquiv.prodAssoc (α := ℝ) (β := Fin a → Fin 2)
              (γ := Fin n → Fin 2)).symm)
          ∘ (Prod.map (id : ℝ → ℝ)
              (fun d : Fin (a + n) → Fin 2 => (d ∘ Fin.castAdd n, d ∘ Fin.natAdd a)))) := by
    funext p
    rfl
  calc Measure.map (glueCombine a n) (unitMeasure.prod (digitMeasure (a + n)))
      = Measure.map ((Prod.map (glueDigits a) (id : (Fin n → Fin 2) → Fin n → Fin 2))
          ∘ ((⇑(MeasurableEquiv.prodAssoc (α := ℝ) (β := Fin a → Fin 2)
                (γ := Fin n → Fin 2)).symm)
            ∘ (Prod.map (id : ℝ → ℝ)
                (fun d : Fin (a + n) → Fin 2 => (d ∘ Fin.castAdd n, d ∘ Fin.natAdd a)))))
          (unitMeasure.prod (digitMeasure (a + n))) := by rw [hfun]
    _ = Measure.map (Prod.map (glueDigits a) (id : (Fin n → Fin 2) → Fin n → Fin 2))
          (Measure.map ((⇑(MeasurableEquiv.prodAssoc (α := ℝ) (β := Fin a → Fin 2)
                (γ := Fin n → Fin 2)).symm)
            ∘ (Prod.map (id : ℝ → ℝ)
                (fun d : Fin (a + n) → Fin 2 => (d ∘ Fin.castAdd n, d ∘ Fin.natAdd a))))
            (unitMeasure.prod (digitMeasure (a + n)))) := by
          rw [← Measure.map_map ((measurable_glueDigits a).prodMap measurable_id)
            (hassocmeas.comp (measurable_id.prodMap hsplitmeas))]
    _ = Measure.map (Prod.map (glueDigits a) (id : (Fin n → Fin 2) → Fin n → Fin 2))
          (Measure.map (⇑(MeasurableEquiv.prodAssoc (α := ℝ) (β := Fin a → Fin 2)
              (γ := Fin n → Fin 2)).symm)
            (Measure.map (Prod.map (id : ℝ → ℝ)
                (fun d : Fin (a + n) → Fin 2 => (d ∘ Fin.castAdd n, d ∘ Fin.natAdd a)))
              (unitMeasure.prod (digitMeasure (a + n))))) := by
          rw [← Measure.map_map hassocmeas (measurable_id.prodMap hsplitmeas)]
    _ = unitMeasure.prod (digitMeasure n) := by rw [step1, step2, step3]

theorem map_glueSplit (a n : ℕ) :
    Measure.map (glueSplit a n) (unitMeasure.prod (unitMeasure.prod (digitMeasure (a + n))))
      = unitMeasure.prod (digitMeasure n) := by
  have := isProbabilityMeasure_unitMeasure
  have hdrop : Measure.map (Prod.map (id : ℝ → ℝ)
        (Prod.snd : ℝ × (Fin (a + n) → Fin 2) → (Fin (a + n) → Fin 2)))
        (unitMeasure.prod (unitMeasure.prod (digitMeasure (a + n))))
      = unitMeasure.prod (digitMeasure (a + n)) := by
    rw [← Measure.map_prod_map unitMeasure (unitMeasure.prod (digitMeasure (a + n)))
        measurable_id measurable_snd, Measure.map_id, Measure.map_snd_prod, measure_univ,
      one_smul]
  have hfun : glueSplit a n = glueCombine a n ∘ Prod.map (id : ℝ → ℝ)
      (Prod.snd : ℝ × (Fin (a + n) → Fin 2) → (Fin (a + n) → Fin 2)) := rfl
  rw [hfun, ← Measure.map_map (measurable_glueCombine a n)
      (measurable_id.prodMap measurable_snd), hdrop, map_glueCombine]

theorem map_coordCylinder_of_nonneg {k : ℤ} (hk : 0 ≤ k) (n : ℕ) :
    Measure.map (coordCylinder k n) (unitMeasure.prod unitMeasure)
      = unitMeasure.prod (digitMeasure n) := by
  have := isProbabilityMeasure_unitMeasure
  have hae : Measure.map (coordCylinder k n) (unitMeasure.prod unitMeasure)
      = Measure.map (glueSplit k.toNat n ∘ Prod.map (id : ℝ → ℝ)
          (shiftBits (k.toNat + n))) (unitMeasure.prod unitMeasure) := by
    refine Measure.map_congr ?_
    filter_upwards [ae_mem_Ico_prod_unitMeasure] with z hz
    exact coordCylinder_eq_glueSplit hk n hz.1 hz.2
  rw [hae, ← Measure.map_map (measurable_glueSplit k.toNat n)
      (measurable_id.prodMap (measurable_shiftBits (k.toNat + n))),
    ← Measure.map_prod_map unitMeasure unitMeasure measurable_id
      (measurable_shiftBits (k.toNat + n)),
    Measure.map_id, map_shiftBits_unitMeasure, map_glueSplit]

/-! ### Negative levels: digits of the first coordinate, in reversed order -/

/-- The remainder after `s + t` shifts together with the last `t` of those digits. -/
noncomputable def negCoordMap (s t : ℕ) (x : ℝ) : ℝ × (Fin t → Fin 2) :=
  shiftBits t (shiftBits s x).1

/-- The index map of a level range straddling `0`: the levels below `0` read the
digits of the first coordinate in reversed order, the levels from `0` on read the
digits of the second coordinate in order. -/
def negIndex (t q n : ℕ) (h : t + q = n) (j : Fin n) : Fin t ⊕ Fin q :=
  if hj : (j : ℕ) < t then Sum.inl ⟨t - 1 - (j : ℕ), by omega⟩
  else Sum.inr ⟨(j : ℕ) - t, by have := j.isLt; omega⟩

theorem negIndex_bijective (t q n : ℕ) (h : t + q = n) :
    Function.Bijective (negIndex t q n h) := by
  have hcard : Fintype.card (Fin n) = Fintype.card (Fin t ⊕ Fin q) := by
    simp [h]
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨?_, hcard⟩
  intro j1 j2 hj
  have h1 := j1.isLt
  have h2 := j2.isLt
  by_cases c1 : (j1 : ℕ) < t
  · by_cases c2 : (j2 : ℕ) < t
    · simp only [negIndex, dif_pos c1, dif_pos c2, Sum.inl.injEq, Fin.mk.injEq] at hj
      exact Fin.ext (by omega)
    · simp [negIndex, dif_pos c1, dif_neg c2] at hj
  · by_cases c2 : (j2 : ℕ) < t
    · simp [negIndex, dif_neg c1, dif_pos c2] at hj
    · simp only [negIndex, dif_neg c1, dif_neg c2, Sum.inr.injEq, Fin.mk.injEq] at hj
      exact Fin.ext (by omega)

/-- The cylinder data assembled from the two independent digit blocks. -/
noncomputable def negAssemble (t q n : ℕ) (σ : Fin n → Fin t ⊕ Fin q)
    (p : (ℝ × (Fin t → Fin 2)) × (Fin q → Fin 2)) : ℝ × (Fin n → Fin 2) :=
  (p.1.1, fun j : Fin n => Sum.elim p.1.2 p.2 (σ j))

theorem measurable_negCoordMap (s t : ℕ) : Measurable (negCoordMap s t) :=
  (measurable_shiftBits t).comp (measurable_fst.comp (measurable_shiftBits s))

theorem measurable_negAssemble (t q n : ℕ) (σ : Fin n → Fin t ⊕ Fin q) :
    Measurable (negAssemble t q n σ) :=
  (measurable_fst.comp measurable_fst).prodMk
    ((measurable_of_countable fun pr : (Fin t → Fin 2) × (Fin q → Fin 2) =>
        fun j : Fin n => Sum.elim pr.1 pr.2 (σ j)).comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

theorem map_negCoordMap (s t : ℕ) :
    Measure.map (negCoordMap s t) unitMeasure = unitMeasure.prod (digitMeasure t) := by
  have := isProbabilityMeasure_unitMeasure
  have hdrop : Measure.map (Prod.fst ∘ shiftBits s) unitMeasure = unitMeasure := by
    rw [← Measure.map_map measurable_fst (measurable_shiftBits s), map_shiftBits_unitMeasure,
      Measure.map_fst_prod, measure_univ, one_smul]
  have hfun : negCoordMap s t = shiftBits t ∘ (Prod.fst ∘ shiftBits s) := rfl
  rw [hfun, ← Measure.map_map (measurable_shiftBits t)
      (measurable_fst.comp (measurable_shiftBits s)), hdrop, map_shiftBits_unitMeasure]

theorem map_bitsUpTo_unitMeasure (q : ℕ) :
    Measure.map (bitsUpTo q) unitMeasure = digitMeasure q := by
  have := isProbabilityMeasure_unitMeasure
  have hfun : bitsUpTo q = Prod.snd ∘ shiftBits q := rfl
  rw [hfun, ← Measure.map_map measurable_snd (measurable_shiftBits q),
    map_shiftBits_unitMeasure, Measure.map_snd_prod, measure_univ, one_smul]

theorem map_negAssemble (t q n : ℕ) (σ : Fin n → Fin t ⊕ Fin q)
    (hσ : Function.Bijective σ) :
    Measure.map (negAssemble t q n σ)
        ((unitMeasure.prod (digitMeasure t)).prod (digitMeasure q))
      = unitMeasure.prod (digitMeasure n) := by
  have := isProbabilityMeasure_unitMeasure
  have hassemblemeas : Measurable (fun pr : (Fin t → Fin 2) × (Fin q → Fin 2) =>
      fun j : Fin n => Sum.elim pr.1 pr.2 (σ j)) := measurable_of_countable _
  have hfun : negAssemble t q n σ
      = (Prod.map (id : ℝ → ℝ) (fun pr : (Fin t → Fin 2) × (Fin q → Fin 2) =>
          fun j : Fin n => Sum.elim pr.1 pr.2 (σ j)))
        ∘ (⇑(MeasurableEquiv.prodAssoc (α := ℝ) (β := Fin t → Fin 2)
            (γ := Fin q → Fin 2))) := by
    funext pr
    rfl
  rw [hfun, ← Measure.map_map (measurable_id.prodMap hassemblemeas)
      (MeasurableEquiv.prodAssoc (α := ℝ) (β := Fin t → Fin 2)
        (γ := Fin q → Fin 2)).measurable,
    Measure.prodAssoc_prod,
    ← Measure.map_prod_map unitMeasure ((digitMeasure t).prod (digitMeasure q))
      measurable_id hassemblemeas, Measure.map_id, map_assemble_digitMeasure σ hσ]

theorem coordCylinder_eq_negAssemble {k : ℤ} {n p t s q : ℕ} (hk : k < 0)
    (hp : (p : ℤ) = -k) (ht : t = min n p) (hs : s + t = p) (hq : t + q = n)
    {x y : ℝ} (hx : x ∈ Set.Ico (0 : ℝ) 1) (hy : y ∈ Set.Ico (0 : ℝ) 1) :
    coordCylinder k n (x, y)
      = negAssemble t q n (negIndex t q n hq) (negCoordMap s t x, bitsUpTo q y) := by
  have hfx : Int.fract x = x := Int.fract_eq_self.2 ⟨hx.1, hx.2⟩
  have hfy : Int.fract y = y := Int.fract_eq_self.2 ⟨hy.1, hy.2⟩
  have h1 : coordRel x y k = (negCoordMap s t x).1 := by
    have hzero : coordFutureNum x y k = 0 := by
      have hk0 : k.toNat = 0 := by omega
      simp [coordFutureNum, hk0]
    have hcoef : (2 : ℝ) ^ (-k) = (2 : ℝ) ^ p := by
      rw [← hp, zpow_natCast]
    have htsp : t + s = p := by omega
    have hinner : (2 : ℝ) ^ t * ((2 : ℝ) ^ s * x) = (2 : ℝ) ^ p * x := by
      rw [← mul_assoc, ← pow_add, htsp]
    calc coordRel x y k = Int.fract ((2 : ℝ) ^ p * x) := by
          rw [coordRel, hzero, hcoef, hfx, add_zero]
      _ = Int.fract ((2 : ℝ) ^ t * Int.fract ((2 : ℝ) ^ s * x)) := by
          rw [fract_pow_mul_fract, hinner]
      _ = (negCoordMap s t x).1 := rfl
  have h2 : (fun j : Fin n => coordDigitFin x y (k + (j.val : ℤ)))
      = fun j : Fin n =>
          Sum.elim (negCoordMap s t x).2 (bitsUpTo q y) (negIndex t q n hq j) := by
    funext j
    have hjn : (j : ℕ) < n := j.isLt
    by_cases hj : (j : ℕ) < t
    · have hkj : k + (j.val : ℤ) < 0 := by omega
      have hidx : negIndex t q n hq j = Sum.inl ⟨t - 1 - (j : ℕ), by omega⟩ := by
        simp only [negIndex, dif_pos hj]
      have hexp : (-(k + (j.val : ℤ) + 1)).toNat = (t - 1 - (j : ℕ)) + s := by omega
      have hinner : (2 : ℝ) ^ (t - 1 - (j : ℕ)) * ((2 : ℝ) ^ s * x)
          = (2 : ℝ) ^ ((t - 1 - (j : ℕ)) + s) * x := by
        rw [← mul_assoc, ← pow_add]
      rw [coordDigitFin_of_neg hkj, hfx, hidx]
      simp only [Sum.elim_inl, negCoordMap, shiftBits_snd, bitsUpTo, shiftBits_fst,
        bitFin_pow_mul_fract, hinner, hexp]
    · have htn : t = p := by omega
      have hkj : 0 ≤ k + (j.val : ℤ) := by omega
      have hidx : negIndex t q n hq j
          = Sum.inr ⟨(j : ℕ) - t, by have := j.isLt; omega⟩ := by
        simp only [negIndex, dif_neg hj]
      have hexp : (k + (j.val : ℤ)).toNat = (j : ℕ) - t := by omega
      rw [coordDigitFin_of_nonneg hkj, hfy, hidx]
      simp only [Sum.elim_inr, bitsUpTo, hexp]
  have hpair : coordCylinder k n (x, y)
      = (coordRel x y k, fun j : Fin n => coordDigitFin x y (k + (j.val : ℤ))) := rfl
  rw [hpair, h1, h2]
  rfl

theorem map_coordCylinder_of_neg {k : ℤ} (hk : k < 0) (n : ℕ) :
    Measure.map (coordCylinder k n) (unitMeasure.prod unitMeasure)
      = unitMeasure.prod (digitMeasure n) := by
  have := isProbabilityMeasure_unitMeasure
  set p := (-k).toNat with hpdef
  set t := min n p with htdef
  set s := p - t with hsdef
  set q := n - t with hqdef
  have hp : (p : ℤ) = -k := by
    rw [hpdef]
    exact Int.toNat_of_nonneg (by omega)
  have hs : s + t = p := by omega
  have hq : t + q = n := by omega
  have hbij := negIndex_bijective t q n hq
  have hae : Measure.map (coordCylinder k n) (unitMeasure.prod unitMeasure)
      = Measure.map (negAssemble t q n (negIndex t q n hq)
          ∘ Prod.map (negCoordMap s t) (bitsUpTo q)) (unitMeasure.prod unitMeasure) := by
    refine Measure.map_congr ?_
    filter_upwards [ae_mem_Ico_prod_unitMeasure] with z hz
    exact coordCylinder_eq_negAssemble hk hp htdef hs hq hz.1 hz.2
  rw [hae, ← Measure.map_map (measurable_negAssemble t q n (negIndex t q n hq))
      ((measurable_negCoordMap s t).prodMap (measurable_bitsUpTo q)),
    ← Measure.map_prod_map unitMeasure unitMeasure (measurable_negCoordMap s t)
      (measurable_bitsUpTo q),
    map_negCoordMap, map_bitsUpTo_unitMeasure, map_negAssemble t q n _ hbij]

/-- **The mixed sign cylinder law of one planar coordinate.**  At every integer level
`k`, including a level range straddling `0`, the relative origin is exactly uniform on
`[0, 1)` and exactly independent of the `n` parent digits, which are independent fair
coins. -/
theorem map_coordCylinder (k : ℤ) (n : ℕ) :
    Measure.map (coordCylinder k n) (unitMeasure.prod unitMeasure)
      = unitMeasure.prod (digitMeasure n) := by
  by_cases hk : 0 ≤ k
  · exact map_coordCylinder_of_nonneg hk n
  · exact map_coordCylinder_of_neg (by omega) n

/-! ### The grid cylinder law -/

/-- Regrouping the two independent coordinate cylinders into the grid cylinder shape. -/
noncomputable def planarAssemble (n : ℕ) (g : Fin 2 → ℝ × (Fin n → Fin 2)) :
    (Fin 2 → ℝ) × (Fin n → Fin 2 → Fin 2) :=
  (fun i => (g i).1, fun (j : Fin n) (i : Fin 2) => (g i).2 j)

/-- The cylinder data of both planar coordinates at once. -/
noncomputable def planarCylinder (k : ℤ) (n : ℕ) (uw : (Fin 2 → ℝ) × (Fin 2 → ℝ)) :
    (Fin 2 → ℝ) × (Fin n → Fin 2 → Fin 2) :=
  planarAssemble n fun i => coordCylinder k n (uw.1 i, uw.2 i)

theorem measurable_planarAssemble (n : ℕ) : Measurable (planarAssemble n) :=
  (Measurable.of_eval fun i => measurable_fst.comp (measurable_pi_apply i)).prodMk
    (Measurable.of_eval fun j => Measurable.of_eval fun i =>
      (measurable_pi_apply j).comp (measurable_snd.comp (measurable_pi_apply i)))

theorem measurable_planarCylinder (k : ℤ) (n : ℕ) : Measurable (planarCylinder k n) := by
  have hpair : ∀ i : Fin 2,
      Measurable fun uw : (Fin 2 → ℝ) × (Fin 2 → ℝ) => (uw.1 i, uw.2 i) :=
    fun i => ((measurable_pi_apply i).comp measurable_fst).prodMk
      ((measurable_pi_apply i).comp measurable_snd)
  have hcoord : Measurable fun uw : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
      fun i : Fin 2 => coordCylinder k n (uw.1 i, uw.2 i) :=
    measurable_pi_iff.2 fun i => (measurable_coordCylinder k n).comp (hpair i)
  exact (measurable_planarAssemble n).comp hcoord

theorem map_fract_unitMeasure : Measure.map Int.fract unitMeasure = unitMeasure := by
  have h : Measure.map Int.fract unitMeasure = Measure.map id unitMeasure := by
    refine Measure.map_congr ?_
    filter_upwards [ae_mem_Ico_unitMeasure] with x hx
    exact Int.fract_eq_self.2 ⟨hx.1, hx.2⟩
  rw [h, Measure.map_id]

theorem pi_digitMeasure_eq_uniformOfFintype (n : ℕ) :
    (Measure.pi fun _ : Fin 2 => digitMeasure n)
      = (PMF.uniformOfFintype (Fin 2 → Fin n → Fin 2)).toMeasure := by
  simp only [digitMeasure_eq_uniformOfFintype]
  exact pi_uniformOfFintype

theorem swap_bijective (n : ℕ) :
    Function.Bijective
      (Function.swap : (Fin 2 → Fin n → Fin 2) → (Fin n → Fin 2 → Fin 2)) := by
  refine Function.bijective_iff_has_inverse.2 ⟨Function.swap, fun f => ?_, fun f => ?_⟩
  · funext i j
    rfl
  · funext j i
    rfl

theorem map_swap_uniformOfFintype (n : ℕ) :
    Measure.map (Function.swap : (Fin 2 → Fin n → Fin 2) → (Fin n → Fin 2 → Fin 2))
        (PMF.uniformOfFintype (Fin 2 → Fin n → Fin 2)).toMeasure
      = (PMF.uniformOfFintype (Fin n → Fin 2 → Fin 2)).toMeasure :=
  map_uniformOfFintype_of_bijective _ (swap_bijective n)

theorem map_planarAssemble (n : ℕ) :
    Measure.map (planarAssemble n)
        (Measure.pi fun _ : Fin 2 => unitMeasure.prod (digitMeasure n))
      = (Measure.pi fun _ : Fin 2 => unitMeasure).prod
          (PMF.uniformOfFintype (Fin n → Fin 2 → Fin 2)).toMeasure := by
  have := isProbabilityMeasure_unitMeasure
  have harrow := (measurePreserving_arrowProdEquivProdArrow ℝ (Fin n → Fin 2) (Fin 2)
    (fun _ => unitMeasure) (fun _ => digitMeasure n)).map_eq
  have hswapmeas : Measurable
      (Function.swap : (Fin 2 → Fin n → Fin 2) → (Fin n → Fin 2 → Fin 2)) :=
    measurable_of_countable _
  have hfun : planarAssemble n
      = (Prod.map (id : (Fin 2 → ℝ) → (Fin 2 → ℝ))
          (Function.swap : (Fin 2 → Fin n → Fin 2) → (Fin n → Fin 2 → Fin 2)))
        ∘ (⇑(MeasurableEquiv.arrowProdEquivProdArrow ℝ (Fin n → Fin 2) (Fin 2))) := rfl
  rw [hfun, ← Measure.map_map (measurable_id.prodMap hswapmeas)
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ (Fin n → Fin 2) (Fin 2)).measurable,
    harrow, ← Measure.map_prod_map (Measure.pi fun _ : Fin 2 => unitMeasure)
      (Measure.pi fun _ : Fin 2 => digitMeasure n) measurable_id hswapmeas,
    Measure.map_id, pi_digitMeasure_eq_uniformOfFintype, map_swap_uniformOfFintype]

theorem map_planarCylinder (k : ℤ) (n : ℕ) :
    Measure.map (planarCylinder k n)
        ((Measure.pi fun _ : Fin 2 => unitMeasure).prod
          (Measure.pi fun _ : Fin 2 => unitMeasure))
      = (Measure.pi fun _ : Fin 2 => unitMeasure).prod
          (PMF.uniformOfFintype (Fin n → Fin 2 → Fin 2)).toMeasure := by
  have := isProbabilityMeasure_unitMeasure
  have harrow := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin 2)
    (fun _ => unitMeasure) (fun _ => unitMeasure)).map_eq
  have hcoordmeas : Measurable
      (fun f : Fin 2 → ℝ × ℝ => fun i => coordCylinder k n (f i)) :=
    measurable_pi_iff.2 fun i => (measurable_coordCylinder k n).comp (measurable_pi_apply i)
  have hpi : Measure.map (fun f : Fin 2 → ℝ × ℝ => fun i => coordCylinder k n (f i))
      (Measure.pi fun _ : Fin 2 => unitMeasure.prod unitMeasure)
      = Measure.pi fun _ : Fin 2 => unitMeasure.prod (digitMeasure n) :=
    (measurePreserving_pi (fun _ : Fin 2 => unitMeasure.prod unitMeasure)
      (fun _ : Fin 2 => unitMeasure.prod (digitMeasure n))
      (fun _ => ⟨measurable_coordCylinder k n, map_coordCylinder k n⟩)).map_eq
  have hfun : planarCylinder k n ∘ (⇑(MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin 2)))
      = planarAssemble n ∘ (fun f : Fin 2 → ℝ × ℝ => fun i => coordCylinder k n (f i)) := rfl
  rw [← harrow, Measure.map_map (measurable_planarCylinder k n)
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin 2)).measurable, hfun,
    ← Measure.map_map (measurable_planarAssemble n) hcoordmeas, hpi, map_planarAssemble]

/-- **The uniform dyadic grid law.**  The candidate grid law constructed in
`DyadicGridLaw` satisfies `DyadicApproximation.UniformGridLaw` exactly: at every
integer level the phase and both relative origin coordinates are uniform on the
half-open unit interval and independent of the parent digits, which are independent
fair coins. -/
theorem uniformGridLaw_gridMeasure : UniformGridLaw gridMeasure := by
  have := isProbabilityMeasure_unitMeasure
  refine ⟨isProbabilityMeasure_gridMeasure, fun k n => ?_⟩
  have hfun : (fun ω : Source => (Int.fract ω.1, (fun i => rel ω.2.1 ω.2.2 k i,
      fun (j : Fin n) (i : Fin 2) => digitFin ω.2.1 ω.2.2 (k + (j.val : ℤ)) i)))
      = Prod.map Int.fract (planarCylinder k n) := rfl
  rw [map_gridCylinder_gridMeasure k n, hfun, sourceMeasure,
    ← Measure.map_prod_map unitMeasure ((Measure.pi fun _ : Fin 2 => unitMeasure).prod
      (Measure.pi fun _ : Fin 2 => unitMeasure)) measurable_fract
      (measurable_planarCylinder k n),
    map_fract_unitMeasure, map_planarCylinder]
  rfl

end ReflectedGMS.DyadicCylinderLaw
