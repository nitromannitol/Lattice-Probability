/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.RecordsAux4 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.RecordsAux3

/-!
# Records (node `R44`), auxiliary part 4: the finite record system and the count (4.4)

A record consists of the current location (scale exponent and endpoint cells), the bin, the
large-excess flag, and the location of the followed child.  Valid records satisfy the
geometric constraints of Section 4.2: in the small-excess case the followed child's cell
corners are within `rho` of a straight position `j / M`, `j ≤ 3M`, of the reference segment; in
the large-excess case they are within `12 · 2^σ` of the first reference point, and the bin is
`⌊δ⁻²⌋`.  Scale exponents and cells range over explicit finite boxes (depending on `ε`).

The count of valid records with a given current location and bin `k` is at most
`C M^19 (k+1)^19` (`count_le`), which gives both counting bounds of `RecordSystem.Good`.
-/

noncomputable section

open Real
open scoped Classical

namespace LQGDimension.LFPPRecords

open Blueprint.Draft

/-- Largest bin `⌊δ⁻²⌋`. -/
def kmax (δ : ℝ) : ℕ := ⌊δ ^ (-2 : ℤ)⌋₊

/-- Validity of record data (see the module docstring). -/
def RecValid (n : ℕ) (δ : ℝ) (p : RecData) : Prop :=
  p.1.2.1 ≠ p.1.2.2 ∧
  p.2.2.1 ≤ p.1.1 ∧ p.1.1 ≤ p.2.2.1 + (4 * (n : ℤ) + 2) ∧
  (p.2.1.2 = true → p.2.1.1 = kmax δ ∧
    ‖refX n δ p.2.2 - refX n δ p.1‖ ≤ 12 * (2 : ℝ) ^ p.1.1 ∧
    ‖refY n δ p.2.2 - refX n δ p.1‖ ≤ 12 * (2 : ℝ) ^ p.1.1) ∧
  (p.2.1.2 = false →
    (∃ j ≤ 3 * Mn n, ‖refX n δ p.2.2 - straight n δ p.1 j‖ ≤ rho n δ p.1.1 p.2.1.1) ∧
    (∃ j ≤ 3 * Mn n, ‖refY n δ p.2.2 - straight n δ p.1 j‖ ≤ rho n δ p.1.1 p.2.1.1))

/-- Smallest scale exponent used (chords of length `≥ ε / (2M)`). -/
def sigMin (n : ℕ) (ε : ℝ) : ℤ := Int.log 2 (ε / (2 * (Mn n : ℝ)))

/-- Bound on cell indices (points of norm `≤ 4`). -/
def boxB (n : ℕ) (δ ε : ℝ) : ℤ := ⌈4 / side n δ (sigMin n ε)⌉ + 1

def sqBox (B : ℤ) : Finset (ℤ × ℤ) := Finset.Icc (-B) B ×ˢ Finset.Icc (-B) B

/-- The finite box of locations. -/
def locBox (n : ℕ) (δ ε : ℝ) : Finset Loc :=
  Finset.Icc (sigMin n ε) 0 ×ˢ (sqBox (boxB n δ ε) ×ˢ sqBox (boxB n δ ε))

/-- The finite set of valid records. -/
def recSet (n : ℕ) (δ ε : ℝ) : Finset RecData :=
  (locBox n δ ε ×ˢ ((Finset.range (kmax δ + 1) ×ˢ Finset.univ) ×ˢ locBox n δ ε)).filter
    (RecValid n δ)

/-- The location of the root chord `[0, 1]`. -/
def rootLoc (n : ℕ) (δ : ℝ) : Loc := locOf n δ 0 1

/-- The record system at `M = 16^n`, `δ`, `ε`. -/
def recSys (n : ℕ) (δ ε : ℝ) : RecordSystem where
  Rec := {p // p ∈ recSet n δ ε}
  fintype := inferInstance
  large r := r.1.2.1.2
  bin r := r.1.2.1.1
  sim r := (locAlpha n δ r.1.1, refX n δ r.1.1)
  isRoot r := r.1.1 = rootLoc n δ
  next r r' := r'.1.1 = r.1.2.2 ∧
    ‖locAlpha n δ r'.1.1‖ ≤ 4 / ((16 ^ n : ℕ) : ℝ) * ‖locAlpha n δ r.1.1‖
  family r := cfgMap (locAlpha n δ r.1.1, refX n δ r.1.1) ''
    localFamily (16 ^ n) δ r.1.2.1.2 r.1.2.1.1

theorem recValid_of_mem {n : ℕ} {δ ε : ℝ} {p : RecData} (hp : p ∈ recSet n δ ε) :
    RecValid n δ p := (Finset.mem_filter.mp hp).2

/-! ## Counting -/

/-- Cells at scale `σ'` that may contain a followed child's endpoint. -/
def ballSet (n : ℕ) (δ : ℝ) (l : Loc) (k : ℕ) (σ' : ℤ) : Finset (ℤ × ℤ) :=
  (Finset.range (3 * Mn n + 1)).biUnion
      (fun j => gridBox (side n δ σ') (straight n δ l j) (rho n δ l.1 k)) ∪
    (if k = kmax δ then gridBox (side n δ σ') (refX n δ l) (12 * (2 : ℝ) ^ l.1) else ∅)

/-- Possible (flag, next location) pairs of records with current location `l` and bin `k`. -/
def tgtSet (n : ℕ) (δ : ℝ) (l : Loc) (k : ℕ) : Finset (Bool × Loc) :=
  (Finset.univ : Finset Bool) ×ˢ ((Finset.Icc (l.1 - (4 * (n : ℤ) + 2)) l.1).biUnion
    (fun σ' => ({σ'} : Finset ℤ) ×ˢ (ballSet n δ l k σ' ×ˢ ballSet n δ l k σ')))

theorem mem_tgtSet {n : ℕ} {δ : ℝ} (hδ : 0 < δ) {p : RecData} (hp : RecValid n δ p) :
    (p.2.1.2, p.2.2) ∈ tgtSet n δ p.1 p.2.1.1 := by
  obtain ⟨_, hσ1, hσ2, hL, hS⟩ := hp
  have hs := side_pos hδ n p.2.2.1
  simp only [tgtSet, Finset.mem_product, Finset.mem_univ, true_and, Finset.mem_biUnion,
    Finset.mem_Icc, Finset.mem_singleton]
  refine ⟨p.2.2.1, ⟨by omega, hσ1⟩, rfl, ?_, ?_⟩
  · cases hb : p.2.1.2
    · obtain ⟨⟨j, hj, h⟩, _⟩ := hS hb
      apply Finset.mem_union_left
      rw [Finset.mem_biUnion]
      exact ⟨j, Finset.mem_range.mpr (by omega), mem_gridBox hs h⟩
    · obtain ⟨hk, h, _⟩ := hL hb
      apply Finset.mem_union_right
      simp only [hk, ↓reduceIte]
      exact mem_gridBox hs h
  · cases hb : p.2.1.2
    · obtain ⟨_, ⟨j, hj, h⟩⟩ := hS hb
      apply Finset.mem_union_left
      rw [Finset.mem_biUnion]
      exact ⟨j, Finset.mem_range.mpr (by omega), mem_gridBox hs h⟩
    · obtain ⟨hk, _, h⟩ := hL hb
      apply Finset.mem_union_right
      simp only [hk, ↓reduceIte]
      exact mem_gridBox hs h

theorem inv_le_sqrt_kmax {δ : ℝ} (_hδ : 0 < δ) : 1 / δ ≤ √((kmax δ : ℝ) + 1) := by
  apply Real.le_sqrt_of_sq_le
  have h := Nat.lt_floor_add_one (δ ^ (-2 : ℤ))
  rw [zpow_neg, zpow_ofNat] at h
  rw [div_pow, one_pow, ← inv_eq_one_div]
  exact h.le

theorem card_ballSet_le {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ) (l : Loc) (k : ℕ) {σ' : ℤ}
    (hσ : l.1 ≤ σ' + (4 * (n : ℤ) + 2)) :
    ((ballSet n δ l k σ').card : ℝ) ≤
      250000 * (Mn n : ℝ) * ((Mn n : ℝ) ^ 4 * ((k : ℝ) + 1)) ^ 2 := by
  have hM := Mn_pos n
  have hM16 := Mn_ge_sixteen hn
  set M : ℝ := (Mn n : ℝ) with hMdef
  set X : ℝ := M ^ 4 * ((k : ℝ) + 1) with hX
  have hs := side_pos hδ n σ'
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hX1 : 1 ≤ X := by
    have : (1 : ℝ) ≤ M ^ 4 := one_le_pow₀ (by linarith)
    rw [hX]; nlinarith
  have hsq1 := one_le_sqrt_succ k
  have hsq2 := sqrt_succ_le k
  have hpow : (2 : ℝ) ^ l.1 ≤ 4 * M * (2 : ℝ) ^ σ' := by
    calc (2 : ℝ) ^ l.1 ≤ (2 : ℝ) ^ (σ' + (4 * (n : ℤ) + 2)) :=
          zpow_le_zpow_right₀ (by norm_num) hσ
      _ = 4 * M * (2 : ℝ) ^ σ' := by rw [zpow_add₀ two_ne_zero, two_zpow_eq]; ring
  have h2σ' : (0 : ℝ) < (2 : ℝ) ^ σ' := by positivity
  -- the small-excess part
  have hA : ∀ j, ((gridBox (side n δ σ') (straight n δ l j) (rho n δ l.1 k)).card : ℝ) ≤
      (225 * X) ^ 2 := by
    intro j
    have hρ : 0 ≤ rho n δ l.1 k := by unfold rho; positivity
    refine (card_gridBox_le hs hρ _).trans ?_
    have hr : 2 * rho n δ l.1 k / side n δ σ' ≤ 224 * X := by
      rw [div_le_iff₀ hs]
      have e : 224 * X * side n δ σ' = 224 * M ^ 2 * δ * ((k : ℝ) + 1) * (2 : ℝ) ^ σ' := by
        rw [hX, side_eq, ← hMdef]; field_simp
      rw [e]
      unfold rho
      rw [← hMdef]
      have : 0 ≤ M * δ * √((k : ℝ) + 1) := by positivity
      calc 2 * (28 * M * (2 : ℝ) ^ l.1 * δ * √((k : ℝ) + 1))
          = 56 * (M * δ * √((k : ℝ) + 1)) * (2 : ℝ) ^ l.1 := by ring
        _ ≤ 56 * (M * δ * √((k : ℝ) + 1)) * (4 * M * (2 : ℝ) ^ σ') := by gcongr
        _ = 224 * M ^ 2 * δ * √((k : ℝ) + 1) * (2 : ℝ) ^ σ' := by ring
        _ ≤ 224 * M ^ 2 * δ * ((k : ℝ) + 1) * (2 : ℝ) ^ σ' := by gcongr
    have : 0 ≤ 2 * rho n δ l.1 k / side n δ σ' + 1 := by positivity
    calc (2 * rho n δ l.1 k / side n δ σ' + 1) ^ 2 ≤ (224 * X + X) ^ 2 := by gcongr
      _ = (225 * X) ^ 2 := by ring
  -- the large-excess part
  have hB : (((if k = kmax δ then gridBox (side n δ σ') (refX n δ l) (12 * (2 : ℝ) ^ l.1)
      else ∅) : Finset (ℤ × ℤ)).card : ℝ) ≤ (97 * X) ^ 2 := by
    split_ifs with hk
    · refine (card_gridBox_le hs (by positivity) _).trans ?_
      have hδk := inv_le_sqrt_kmax hδ
      rw [← hk] at hδk
      have h1 : 1 ≤ δ * ((k : ℝ) + 1) := by
        have : 1 / δ ≤ (k : ℝ) + 1 := hδk.trans hsq2
        rw [div_le_iff₀ hδ] at this; linarith
      have hr : 2 * (12 * (2 : ℝ) ^ l.1) / side n δ σ' ≤ 96 * X := by
        rw [div_le_iff₀ hs]
        have e : 96 * X * side n δ σ' = 96 * (M ^ 2 * (δ * ((k : ℝ) + 1))) * (2 : ℝ) ^ σ' := by
          rw [hX, side_eq, ← hMdef]; field_simp
        rw [e]
        have h2 : M ≤ M ^ 2 * (δ * ((k : ℝ) + 1)) := by nlinarith
        calc 2 * (12 * (2 : ℝ) ^ l.1) ≤ 2 * (12 * (4 * M * (2 : ℝ) ^ σ')) := by gcongr
          _ = 96 * M * (2 : ℝ) ^ σ' := by ring
          _ ≤ 96 * (M ^ 2 * (δ * ((k : ℝ) + 1))) * (2 : ℝ) ^ σ' := by gcongr
      have : 0 ≤ 2 * (12 * (2 : ℝ) ^ l.1) / side n δ σ' + 1 := by positivity
      calc (2 * (12 * (2 : ℝ) ^ l.1) / side n δ σ' + 1) ^ 2 ≤ (96 * X + X) ^ 2 := by
            gcongr
        _ = (97 * X) ^ 2 := by ring
    · simp only [Finset.card_empty, Nat.cast_zero]; positivity
  have hAc : (((Finset.range (3 * Mn n + 1)).biUnion
      (fun j => gridBox (side n δ σ') (straight n δ l j) (rho n δ l.1 k))).card : ℝ) ≤
      ((3 * Mn n + 1 : ℕ) : ℝ) * (225 * X) ^ 2 := by
    calc (((Finset.range (3 * Mn n + 1)).biUnion
          (fun j => gridBox (side n δ σ') (straight n δ l j) (rho n δ l.1 k))).card : ℝ)
        ≤ ((∑ j ∈ Finset.range (3 * Mn n + 1),
            (gridBox (side n δ σ') (straight n δ l j) (rho n δ l.1 k)).card : ℕ) : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ = ∑ j ∈ Finset.range (3 * Mn n + 1),
            ((gridBox (side n δ σ') (straight n δ l j) (rho n δ l.1 k)).card : ℝ) := by
          push_cast; rfl
      _ ≤ ∑ _j ∈ Finset.range (3 * Mn n + 1), (225 * X) ^ 2 :=
          Finset.sum_le_sum fun j _ => hA j
      _ = ((3 * Mn n + 1 : ℕ) : ℝ) * (225 * X) ^ 2 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hU : ((ballSet n δ l k σ').card : ℝ) ≤
      (((Finset.range (3 * Mn n + 1)).biUnion
        (fun j => gridBox (side n δ σ') (straight n δ l j) (rho n δ l.1 k))).card : ℝ) +
      (((if k = kmax δ then gridBox (side n δ σ') (refX n δ l) (12 * (2 : ℝ) ^ l.1)
        else ∅) : Finset (ℤ × ℤ)).card : ℝ) := by
    exact_mod_cast Finset.card_union_le _ _
  have hcast : ((3 * Mn n + 1 : ℕ) : ℝ) = 3 * M + 1 := by rw [hMdef]; push_cast; ring
  rw [hcast] at hAc
  have hX2 : 0 ≤ X ^ 2 := sq_nonneg X
  nlinarith

/-- The universal constant of the count (4.4). -/
def Ccount : ℝ := 125000000000

theorem card_tgtSet_le {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 < δ) (l : Loc) (k : ℕ) :
    ((tgtSet n δ l k).card : ℝ) ≤ Ccount * (Mn n : ℝ) ^ 19 * ((k : ℝ) + 1) ^ 19 := by
  have hM := Mn_pos n
  have hM16 := Mn_ge_sixteen hn
  set M : ℝ := (Mn n : ℝ) with hMdef
  set X : ℝ := M ^ 4 * ((k : ℝ) + 1) with hX
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hW : (((Finset.Icc (l.1 - (4 * (n : ℤ) + 2)) l.1).biUnion
      (fun σ' => ({σ'} : Finset ℤ) ×ˢ (ballSet n δ l k σ' ×ˢ ballSet n δ l k σ'))).card : ℝ) ≤
      M * (250000 * M * X ^ 2) ^ 2 := by
    calc (((Finset.Icc (l.1 - (4 * (n : ℤ) + 2)) l.1).biUnion
          (fun σ' => ({σ'} : Finset ℤ) ×ˢ (ballSet n δ l k σ' ×ˢ ballSet n δ l k σ'))).card : ℝ)
        ≤ ((∑ σ' ∈ Finset.Icc (l.1 - (4 * (n : ℤ) + 2)) l.1,
            (({σ'} : Finset ℤ) ×ˢ (ballSet n δ l k σ' ×ˢ ballSet n δ l k σ')).card : ℕ) : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ = ∑ σ' ∈ Finset.Icc (l.1 - (4 * (n : ℤ) + 2)) l.1,
            ((ballSet n δ l k σ').card : ℝ) * ((ballSet n δ l k σ').card : ℝ) := by
          push_cast
          refine Finset.sum_congr rfl fun σ' _ => ?_
          rw [Finset.card_product, Finset.card_product, Finset.card_singleton]
          push_cast; ring
      _ ≤ ∑ _σ' ∈ Finset.Icc (l.1 - (4 * (n : ℤ) + 2)) l.1, (250000 * M * X ^ 2) ^ 2 := by
          apply Finset.sum_le_sum
          intro σ' hσ'
          rw [Finset.mem_Icc] at hσ'
          have h := card_ballSet_le hn hδ l k (σ' := σ') (by omega)
          rw [sq]
          exact mul_le_mul h h (Nat.cast_nonneg _) (by positivity)
      _ = ((4 * n + 3 : ℕ) : ℝ) * (250000 * M * X ^ 2) ^ 2 := by
          rw [Finset.sum_const, Int.card_Icc, nsmul_eq_mul]
          congr 2
          have : l.1 + 1 - (l.1 - (4 * (n : ℤ) + 2)) = ((4 * n + 3 : ℕ) : ℤ) := by push_cast; ring
          rw [this, Int.toNat_natCast]
      _ ≤ M * (250000 * M * X ^ 2) ^ 2 := by
          gcongr
          rw [hMdef]
          exact_mod_cast four_n_add_three_le n hn
  have hT : ((tgtSet n δ l k).card : ℝ) = 2 * (((Finset.Icc (l.1 - (4 * (n : ℤ) + 2)) l.1).biUnion
      (fun σ' => ({σ'} : Finset ℤ) ×ˢ (ballSet n δ l k σ' ×ˢ ballSet n δ l k σ'))).card : ℝ) := by
    rw [tgtSet, Finset.card_product, Finset.card_univ, Fintype.card_bool]
    push_cast; ring
  rw [hT]
  have hk1 : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith
  have hpow : ((k : ℝ) + 1) ^ 4 ≤ ((k : ℝ) + 1) ^ 19 := pow_le_pow_right₀ hk1 (by norm_num)
  have hM19 : 0 ≤ M ^ 19 := by positivity
  calc 2 * (((Finset.Icc (l.1 - (4 * (n : ℤ) + 2)) l.1).biUnion
        (fun σ' => ({σ'} : Finset ℤ) ×ˢ (ballSet n δ l k σ' ×ˢ ballSet n δ l k σ'))).card : ℝ)
      ≤ 2 * (M * (250000 * M * X ^ 2) ^ 2) := by linarith
    _ = Ccount * M ^ 19 * ((k : ℝ) + 1) ^ 4 := by rw [hX, Ccount]; ring
    _ ≤ Ccount * M ^ 19 * ((k : ℝ) + 1) ^ 19 := by
        apply mul_le_mul_of_nonneg_left hpow
        unfold Ccount; positivity

/-- **The count (4.4).**  Records with a given current location and bin `k`. -/
theorem count_le {n : ℕ} (hn : 1 ≤ n) {δ ε : ℝ} (hδ : 0 < δ) (l : Loc) (k : ℕ) :
    (({r : {p // p ∈ recSet n δ ε} | r.1.1 = l ∧ r.1.2.1.1 = k}.ncard : ℕ) : ℝ) ≤
      Ccount * (Mn n : ℝ) ^ 19 * ((k : ℝ) + 1) ^ 19 := by
  refine le_trans ?_ (card_tgtSet_le hn hδ l k)
  have h := Set.ncard_le_ncard_of_injOn (fun r : {p // p ∈ recSet n δ ε} => (r.1.2.1.2, r.1.2.2))
    (s := {r : {p // p ∈ recSet n δ ε} | r.1.1 = l ∧ r.1.2.1.1 = k})
    (t := ((tgtSet n δ l k : Finset (Bool × Loc)) : Set (Bool × Loc))) ?_ ?_
    (Finset.finite_toSet _)
  · rw [Set.ncard_coe_finset] at h
    exact_mod_cast h
  · intro r hr
    have hr' : r.1.1 = l ∧ r.1.2.1.1 = k := hr
    have := mem_tgtSet hδ (recValid_of_mem r.2)
    rw [hr'.1, hr'.2] at this
    exact Finset.mem_coe.mpr this
  · intro r₁ h₁ r₂ h₂ he
    have h₁' : r₁.1.1 = l ∧ r₁.1.2.1.1 = k := h₁
    have h₂' : r₂.1.1 = l ∧ r₂.1.2.1.1 = k := h₂
    simp only [Prod.mk.injEq] at he
    apply Subtype.ext
    exact Prod.ext (h₁'.1.trans h₂'.1.symm)
      (Prod.ext (Prod.ext (h₁'.2.trans h₂'.2.symm) he.1) he.2)

/-! ## The properties `RecordSystem.Good` -/

theorem recSys_good {n : ℕ} (hn : 1 ≤ n) {δ ε : ℝ} (hδ : 0 < δ) :
    (recSys n δ ε).Good (16 ^ n) δ Ccount 19 := by
  have hcount : ∀ (l : Loc) (k : ℕ),
      (({r : {p // p ∈ recSet n δ ε} | r.1.1 = l ∧ r.1.2.1.1 = k}.ncard : ℕ) : ℝ) ≤
        Ccount * ((16 ^ n : ℕ) : ℝ) ^ (19 : ℝ) * ((k : ℝ) + 1) ^ (19 : ℝ) := by
    intro l k
    rw [Real.rpow_ofNat, Real.rpow_ofNat]
    exact count_le hn hδ l k
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r
    have hv : RecValid n δ r.1 := recValid_of_mem r.2
    show locAlpha n δ r.1.1 ≠ 0
    intro h
    apply hv.1
    have h' : gridPt (side n δ r.1.1.1) r.1.1.2.2 = gridPt (side n δ r.1.1.1) r.1.1.2.1 :=
      sub_eq_zero.mp h
    exact (gridPt_injective (side_pos hδ n _).ne' h').symm
  · intro r
    exact subset_rfl
  · intro r hr
    exact ((recValid_of_mem r.2).2.2.2.1 hr).1
  · intro r r' h
    exact h.2
  · intro k
    exact hcount (rootLoc n δ) k
  · intro r k
    have hsub : {r' : (recSys n δ ε).Rec | (recSys n δ ε).next r r' ∧ (recSys n δ ε).bin r' = k} ⊆
        {r' : {p // p ∈ recSet n δ ε} | r'.1.1 = r.1.2.2 ∧ r'.1.2.1.1 = k} :=
      fun r' hr' => ⟨hr'.1.1, hr'.2⟩
    have hfin : ({r' : {p // p ∈ recSet n δ ε} | r'.1.1 = r.1.2.2 ∧ r'.1.2.1.1 = k}).Finite :=
      Set.Finite.subset (Finset.univ : Finset {p // p ∈ recSet n δ ε}).finite_toSet
        (fun x _ => Finset.mem_coe.mpr (Finset.mem_univ x))
    have := Set.ncard_le_ncard hsub hfin
    refine le_trans ?_ (hcount r.1.2.2 k)
    exact_mod_cast this

end LQGDimension.LFPPRecords
