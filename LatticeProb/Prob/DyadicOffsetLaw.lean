import Mathlib

/-!
# Translation invariance of the uniform dyadic offset law

A uniform dyadic system of the line (Gwynne, Miller and Sheffield, *An invariance principle for
ergodic scale-free random environments*, arXiv 1807.07515, Section 2.1 and Remark 2.4) is built from
a uniform point `x ∈ [0, 1)` and independent fair bits `e 0, e 1, …`: the base interval has its left
end at `-x`, and the interval of generation `k + 1` containing the origin is obtained from the one
of generation `k` by doubling it to the left or to the right according to the bit `e k`. The
intervals of generation `k` then form the grid `-o k + 2^k ℤ` with offset

  `o k = x + ∑_{j<k} 2^j e j ∈ [0, 2^k)`,

and the offsets of distinct generations are compatible: `o j ≡ o k (mod 2^j)` for `j ≤ k`.
Translating the system by `c` replaces each offset `o k` by `toIcoMod (2^k) 0 (o k - c)`.

## Main statements

* `LatticeProb.DyadicOffset.map_offsetsL_eval`: the offset `o k` of generation `k` is uniform
  on `[0, 2^k)` (more generally on `[0, L 2^k)` for the system of base length `L`).
* `LatticeProb.DyadicOffset.offsetsL_eq_toIcoMod`: compatibility of the offsets.
* `LatticeProb.DyadicOffset.map_shiftOffsets_offsetLaw`: the law of the offset sequence is
  invariant under every translation (the one-dimensional, fixed-scale part of Lemma 2.1 of the paper
  cited above). The proof compares finite-dimensional marginals, each of which is the image of the
  uniform law of the last offset, and uses the invariance of Lebesgue measure on `ℝ / 2^k ℤ`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace LatticeProb.DyadicOffset

/-- The digit `0` or `1` of a bit. -/
def bit (b : Bool) : ℝ := if b then 1 else 0

@[fun_prop]
theorem measurable_bit : Measurable bit := measurable_of_countable _

theorem bit_nonneg (b : Bool) : 0 ≤ bit b := by cases b <;> simp [bit]

theorem bit_le_one (b : Bool) : bit b ≤ 1 := by cases b <;> simp [bit]

/-- The uniform probability law on `[0, p)`. -/
noncomputable def unifIco (p : ℝ) : Measure ℝ := (ENNReal.ofReal p)⁻¹ • volume.restrict (Ico 0 p)

theorem isProbabilityMeasure_unifIco {p : ℝ} (hp : 0 < p) : IsProbabilityMeasure (unifIco p) := by
  constructor
  rw [unifIco, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Ico, sub_zero, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by simpa using hp) ENNReal.ofReal_ne_top

/-- The law of a fair bit. -/
noncomputable def bitProb : Measure Bool := uniformOn (univ : Set Bool)

instance : IsProbabilityMeasure bitProb := by unfold bitProb; infer_instance

/-- The law of a sequence of independent fair bits. -/
noncomputable def bitLaw : Measure (ℕ → Bool) := Measure.infinitePi (fun _ : ℕ => bitProb)

instance : IsProbabilityMeasure bitLaw := by unfold bitLaw; infer_instance

/-- The offsets of the generations of the dyadic system of base length `L`:
`offsetsL L x e k = x + ∑_{j<k} L 2^j e j`. -/
noncomputable def offsetsL (L x : ℝ) (e : ℕ → Bool) (k : ℕ) : ℝ :=
  x + ∑ j ∈ Finset.range k, L * 2 ^ j * bit (e j)

theorem measurable_offsetsL_eval (L : ℝ) (k : ℕ) :
    Measurable fun q : ℝ × (ℕ → Bool) => offsetsL L q.1 q.2 k := by
  unfold offsetsL
  refine measurable_fst.add (Finset.measurable_sum _ fun j _ => ?_)
  exact measurable_const.mul (measurable_bit.comp ((measurable_pi_apply j).comp measurable_snd))

theorem measurable_offsetsL (L : ℝ) :
    Measurable fun q : ℝ × (ℕ → Bool) => offsetsL L q.1 q.2 :=
  measurable_pi_iff.mpr fun k => measurable_offsetsL_eval L k

/-- One generation is the next generation of the system of twice the base length. -/
theorem offsetsL_succ (L x : ℝ) (e : ℕ → Bool) (k : ℕ) :
    offsetsL L x e (k + 1) = offsetsL (2 * L) (x + L * bit (e 0)) (fun n => e (n + 1)) k := by
  unfold offsetsL
  rw [Finset.sum_range_succ']
  have : ∀ i ∈ Finset.range k, L * 2 ^ (i + 1) * bit (e (i + 1)) =
      2 * L * 2 ^ i * bit (e (i + 1)) := fun i _ => by ring
  rw [Finset.sum_congr rfl this]
  ring

/-- Prepending a bit to a sequence of bits. -/
def consBit (q : Bool × (ℕ → Bool)) : ℕ → Bool
  | 0 => q.1
  | n + 1 => q.2 n

@[fun_prop]
theorem measurable_consBit : Measurable consBit := by
  refine measurable_pi_iff.mpr fun n => ?_
  cases n with
  | zero => exact measurable_fst
  | succ n => exact (measurable_pi_apply n).comp measurable_snd

/-- A sequence of fair bits is its first bit followed by an independent sequence of fair bits. -/
theorem map_consBit : (bitProb.prod bitLaw).map consBit = bitLaw := by
  refine Measure.eq_infinitePi _ fun S t ht => ?_
  classical
  rw [Measure.map_apply measurable_consBit (MeasurableSet.pi S.countable_toSet fun i _ => ht i)]
  set S' : Finset ℕ := S.preimage Nat.succ (Nat.succ_injective.injOn)
  have hpre : consBit ⁻¹' (Set.pi (S : Set ℕ) t) =
      {b : Bool | 0 ∈ S → b ∈ t 0} ×ˢ Set.pi (S' : Set ℕ) (fun n => t (n + 1)) := by
    ext q
    simp only [mem_preimage, Set.mem_pi, Finset.mem_coe, mem_prod, Set.mem_ofPred_eq, S',
      Finset.mem_preimage]
    constructor
    · intro h
      exact ⟨fun h0 => h 0 h0, fun n hn => h (n + 1) hn⟩
    · rintro ⟨h0, h1⟩ i hi
      cases i with
      | zero => exact h0 hi
      | succ n => exact h1 n hi
  rw [hpre, Measure.prod_prod, bitLaw,
    Measure.infinitePi_pi _ (fun n _ => ht (n + 1))]
  have hsplit : ∏ i ∈ S, bitProb (t i) =
      (∏ i ∈ S, if i = 0 then bitProb (t 0) else 1) *
        ∏ i ∈ S, if i = 0 then 1 else bitProb (t i) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases h : i = 0
    · subst h; simp
    · simp [h]
  have hpre' : ∏ n ∈ S', bitProb (t (n + 1)) = ∏ i ∈ S, if i = 0 then 1 else bitProb (t i) := by
    rw [← Finset.prod_preimage Nat.succ S (Nat.succ_injective.injOn)
      (fun i => if i = 0 then 1 else bitProb (t i)) ?_]
    · refine Finset.prod_congr rfl fun n _ => ?_
      simp
    · intro i _ hi
      have : i = 0 := by
        by_contra h
        exact hi ⟨i - 1, by simpa using Nat.succ_pred_eq_of_ne_zero h⟩
      simp [this]
  rw [hsplit, hpre', Finset.prod_ite_eq']
  congr 1
  by_cases h0 : 0 ∈ S
  · simp [h0]
  · have : {b : Bool | 0 ∈ S → b ∈ t 0} = univ := by ext b; simp [h0]
    rw [this, measure_univ]
    simp [h0]

/-- Splitting off the first bit of a sequence of fair bits. -/
theorem map_head_tail :
    bitLaw.map (fun e : ℕ → Bool => (e 0, fun n => e (n + 1))) = bitProb.prod bitLaw := by
  conv_lhs => rw [← map_consBit]
  rw [Measure.map_map (by fun_prop) measurable_consBit]
  have : ((fun e : ℕ → Bool => (e 0, fun n => e (n + 1))) ∘ consBit) = id := by
    funext q; rfl
  rw [this, Measure.map_id]

/-- Lebesgue measure on `[0, p)` translated by `p` is Lebesgue measure on `[p, 2p)`. -/
theorem map_add_restrict_Ico (p : ℝ) :
    (volume.restrict (Ico 0 p)).map (· + p) = volume.restrict (Ico p (p + p)) := by
  have hm : Measurable fun y : ℝ => y + p := measurable_add_const p
  have hpre : Ico 0 p = (fun y : ℝ => y + p) ⁻¹' Ico p (p + p) := by
    ext y
    simp only [mem_preimage, mem_Ico]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  rw [hpre, ← Measure.restrict_map hm measurableSet_Ico,
    (measurePreserving_add_right volume p).map_eq]

/-- Halving: a uniform point of `[0, L)` plus `L` times an independent fair bit is uniform on
`[0, 2L)`. -/
theorem map_addBit (L : ℝ) (hL : 0 < L) :
    ((unifIco L).prod bitProb).map (fun q : ℝ × Bool => q.1 + L * bit q.2) = unifIco (2 * L) := by
  have := isProbabilityMeasure_unifIco hL
  have hbit : bitProb = (2 : ℝ≥0∞)⁻¹ • (Measure.dirac true + Measure.dirac false) := by
    refine Measure.ext_iff_singleton.mpr fun b => ?_
    cases b <;> rw [bitProb, uniformOn_univ] <;> simp
  have hm : Measurable fun q : ℝ × Bool => q.1 + L * bit q.2 :=
    measurable_fst.add (measurable_const.mul (measurable_bit.comp measurable_snd))
  rw [hbit, Measure.prod_smul_right, Measure.prod_add, Measure.map_smul, Measure.map_add _ _ hm,
    Measure.prod_dirac, Measure.prod_dirac, Measure.map_map hm (by fun_prop),
    Measure.map_map hm (by fun_prop)]
  have h1 : ((fun q : ℝ × Bool => q.1 + L * bit q.2) ∘ fun x => (x, true)) = (· + L) := by
    funext x; simp [bit]
  have h0 : ((fun q : ℝ × Bool => q.1 + L * bit q.2) ∘ fun x => (x, false)) = id := by
    funext x; simp [bit]
  rw [h1, h0, Measure.map_id, unifIco, unifIco, Measure.map_smul, map_add_restrict_Ico,
    ← smul_add, smul_smul, add_comm (volume.restrict (Ico L (L + L))),
    ← Measure.restrict_union (Ico_disjoint_Ico_same) measurableSet_Ico,
    Ico_union_Ico_eq_Ico hL.le (by linarith), ← two_mul]
  · congr 1
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.mul_inv (by simp) (by simp)]
    simp
  all_goals fun_prop

/-- **The offset of generation `k` is uniform** on `[0, L 2^k)`. -/
theorem map_offsetsL_eval (k : ℕ) : ∀ (L : ℝ), 0 < L →
    ((unifIco L).prod bitLaw).map (fun q => offsetsL L q.1 q.2 k) = unifIco (L * 2 ^ k) := by
  induction k with
  | zero =>
    intro L hL
    have := isProbabilityMeasure_unifIco hL
    have : (fun q : ℝ × (ℕ → Bool) => offsetsL L q.1 q.2 0) = Prod.fst := by
      funext q; simp [offsetsL]
    rw [this, Measure.map_fst_prod, measure_univ, one_smul, pow_zero, mul_one]
  | succ k ih =>
    intro L hL
    have := isProbabilityMeasure_unifIco hL
    have hcons : (unifIco L).prod bitLaw =
        ((unifIco L).prod (bitProb.prod bitLaw)).map (Prod.map id consBit) := by
      conv_lhs => rw [← map_consBit, ← Measure.map_id (μ := unifIco L)]
      rw [Measure.map_prod_map _ _ measurable_id measurable_consBit]
    have hm : Measurable fun q : ℝ × Bool => q.1 + L * bit q.2 := by fun_prop
    have hΦ : ((unifIco L).prod bitLaw).map
        (fun q : ℝ × (ℕ → Bool) => (q.1 + L * bit (q.2 0), fun n => q.2 (n + 1))) =
        (unifIco (2 * L)).prod bitLaw := by
      rw [hcons, Measure.map_map (by fun_prop) (measurable_id.prodMap measurable_consBit),
        ← Measure.prodAssoc_prod, Measure.map_map (by fun_prop)
          MeasurableEquiv.prodAssoc.measurable]
      have : ((fun q : ℝ × (ℕ → Bool) => (q.1 + L * bit (q.2 0), fun n => q.2 (n + 1))) ∘
          Prod.map id consBit) ∘ MeasurableEquiv.prodAssoc =
          Prod.map (fun q : ℝ × Bool => q.1 + L * bit q.2) id := by
        funext q; rfl
      rw [this, ← Measure.map_prod_map _ _ hm measurable_id, map_addBit L hL, Measure.map_id]
    have hfun : (fun q : ℝ × (ℕ → Bool) => offsetsL L q.1 q.2 (k + 1)) =
        (fun q : ℝ × (ℕ → Bool) => offsetsL (2 * L) q.1 q.2 k) ∘
          (fun q : ℝ × (ℕ → Bool) => (q.1 + L * bit (q.2 0), fun n => q.2 (n + 1))) := by
      funext q; exact offsetsL_succ L q.1 q.2 k
    rw [hfun, ← Measure.map_map (measurable_offsetsL_eval _ k) (by fun_prop), hΦ,
      ih (2 * L) (by linarith), pow_succ]
    congr 1
    ring

theorem offsetsL_mem_Ico {L x : ℝ} (hL : 0 < L) (hx : x ∈ Ico 0 L) (e : ℕ → Bool) (k : ℕ) :
    offsetsL L x e k ∈ Ico 0 (L * 2 ^ k) := by
  have hsum : ∑ j ∈ Finset.range k, L * 2 ^ j * bit (e j) ≤ L * (2 ^ k - 1) := by
    calc ∑ j ∈ Finset.range k, L * 2 ^ j * bit (e j)
        ≤ ∑ j ∈ Finset.range k, L * 2 ^ j := Finset.sum_le_sum fun j _ =>
          mul_le_of_le_one_right (by positivity) (bit_le_one _)
      _ = L * (2 ^ k - 1) := by
          rw [← Finset.mul_sum, geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]; ring
  have hsum0 : 0 ≤ ∑ j ∈ Finset.range k, L * 2 ^ j * bit (e j) :=
    Finset.sum_nonneg fun j _ => mul_nonneg (by positivity) (bit_nonneg _)
  unfold offsetsL
  constructor
  · linarith [hx.1]
  · nlinarith [hx.2]

/-- The offsets of two generations differ by a multiple of the length of the earlier one. -/
theorem exists_offsetsL_sub (L x : ℝ) (e : ℕ → Bool) {j k : ℕ} (hjk : j ≤ k) :
    ∃ n : ℤ, offsetsL L x e k - offsetsL L x e j = n • (L * 2 ^ j) := by
  induction k, hjk using Nat.le_induction with
  | base => exact ⟨0, by simp⟩
  | succ k hjk ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + (2 ^ (k - j) * (if e k then 1 else 0) : ℕ), ?_⟩
    have hk : offsetsL L x e (k + 1) = offsetsL L x e k + L * 2 ^ k * bit (e k) := by
      simp [offsetsL, Finset.sum_range_succ, add_assoc]
    have h2 : (2 : ℝ) ^ k = 2 ^ (k - j) * 2 ^ j := by
      rw [← pow_add, Nat.sub_add_cancel hjk]
    rw [hk, add_sub_right_comm, hn, h2]
    rcases Bool.eq_false_or_eq_true (e k) with h | h <;> simp [h, bit, zsmul_eq_mul]
    ring

/-- **Compatibility of the offsets**: `o j = o k mod L 2^j` for `j ≤ k`. -/
theorem offsetsL_eq_toIcoMod {L x : ℝ} (hL : 0 < L) (hx : x ∈ Ico 0 L) (e : ℕ → Bool) {j k : ℕ}
    (hjk : j ≤ k) (hp : 0 < L * 2 ^ j) :
    offsetsL L x e j = toIcoMod hp 0 (offsetsL L x e k) := by
  obtain ⟨n, hn⟩ := exists_offsetsL_sub L x e hjk
  rw [eq_add_of_sub_eq hn, toIcoMod_zsmul_add, eq_comm, toIcoMod_eq_self]
  simpa using offsetsL_mem_Ico hL hx e j

theorem measurable_toIcoMod {p : ℝ} (hp : 0 < p) : Measurable (toIcoMod hp 0) := by
  have : toIcoMod hp 0 = fun y => Int.fract (y / p) * p := funext fun y => toIcoMod_eq_fract_mul hp y
  rw [this]
  exact (measurable_fract.comp (measurable_id.div_const p)).mul_const p

/-- Translation modulo `p` preserves Lebesgue measure on `[0, p)`. -/
theorem map_toIcoMod_sub_restrict {p : ℝ} (hp : 0 < p) (c : ℝ) :
    (volume.restrict (Ico 0 p)).map (fun y => toIcoMod hp 0 (y - c)) = volume.restrict (Ico 0 p) := by
  have : Fact (0 < p) := ⟨hp⟩
  have h1 : (volume.restrict (Ico 0 p)).map ((↑) : ℝ → AddCircle p) = volume := by
    rw [Measure.restrict_congr_set Ico_ae_eq_Ioc]
    simpa using (AddCircle.measurePreserving_mk p 0).map_eq
  set g : AddCircle p → ℝ := fun z => (AddCircle.equivIco p 0 z : ℝ) with hg_def
  have hg : Measurable g := measurable_subtype_coe.comp (AddCircle.measurableEquivIco p 0).measurable
  have hgmk : ∀ y : ℝ, g (y : AddCircle p) = toIcoMod hp 0 y := fun y => by
    simp [g, toIcoMod_eq_fract_mul]
  have hfun : (fun y => toIcoMod hp 0 (y - c)) =
      g ∘ (fun z : AddCircle p => z - (c : AddCircle p)) ∘ ((↑) : ℝ → AddCircle p) := by
    funext y
    simp only [Function.comp_apply]
    rw [← hgmk, QuotientAddGroup.mk_sub]
  have hsub : Measurable fun z : AddCircle p => z - (c : AddCircle p) := measurable_sub_const _
  rw [hfun, ← Measure.map_map hg (hsub.comp AddCircle.measurable_mk'),
    ← Measure.map_map hsub AddCircle.measurable_mk', h1,
    (measurePreserving_sub_right volume (c : AddCircle p)).map_eq, ← h1,
    Measure.map_map hg AddCircle.measurable_mk']
  have hid : (g ∘ ((↑) : ℝ → AddCircle p)) =ᵐ[volume.restrict (Ico 0 p)] id := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with y hy
    show g (y : AddCircle p) = y
    rw [hgmk]
    exact (toIcoMod_eq_self hp).mpr (by simpa using hy)
  rw [Measure.map_congr hid, Measure.map_id]

theorem map_toIcoMod_sub_unifIco {p : ℝ} (hp : 0 < p) (c : ℝ) :
    (unifIco p).map (fun y => toIcoMod hp 0 (y - c)) = unifIco p := by
  rw [unifIco, Measure.map_smul, map_toIcoMod_sub_restrict hp c]
  exact ((measurable_toIcoMod hp).comp (measurable_sub_const c)).aemeasurable

/-- The law of the offset sequence of a uniform dyadic system of base length `1`. -/
noncomputable def offsetLaw : Measure (ℕ → ℝ) :=
  ((unifIco 1).prod bitLaw).map fun q => offsetsL 1 q.1 q.2

theorem two_pow_pos' (k : ℕ) : (0 : ℝ) < 2 ^ k := by positivity

/-- The offsets of the translated system `D - c`. -/
noncomputable def shiftOffsets (c : ℝ) (o : ℕ → ℝ) (k : ℕ) : ℝ :=
  toIcoMod (two_pow_pos' k) 0 (o k - c)

theorem measurable_shiftOffsets (c : ℝ) : Measurable (shiftOffsets c) :=
  measurable_pi_iff.mpr fun k =>
    (measurable_toIcoMod (two_pow_pos' k)).comp (by fun_prop)

instance : IsProbabilityMeasure offsetLaw := by
  have := isProbabilityMeasure_unifIco (zero_lt_one' ℝ)
  unfold offsetLaw
  constructor
  rw [Measure.map_apply (measurable_offsetsL 1) MeasurableSet.univ]
  simp

/-- Reduction of a point modulo `2^i` for each `i` in a finite set of generations. -/
noncomputable def restrictMod (I : Finset ℕ) (y : ℝ) : I → ℝ := fun i => toIcoMod (two_pow_pos' i) 0 y

theorem measurable_restrictMod (I : Finset ℕ) : Measurable (restrictMod I) :=
  measurable_pi_iff.mpr fun i => measurable_toIcoMod (two_pow_pos' i)

theorem map_offsetsL_one_eval (N : ℕ) :
    ((unifIco 1).prod bitLaw).map (fun q => offsetsL 1 q.1 q.2 N) = unifIco (2 ^ N) := by
  have := map_offsetsL_eval N 1 zero_lt_one
  rwa [one_mul] at this

/-- **Translation invariance of the uniform dyadic offset law.** -/
theorem map_shiftOffsets_offsetLaw (c : ℝ) : offsetLaw.map (shiftOffsets c) = offsetLaw := by
  have := isProbabilityMeasure_unifIco (zero_lt_one' ℝ)
  refine (IsProjectiveLimit.unique (P := fun I : Finset ℕ => offsetLaw.map I.restrict)
    (fun I => ?_) (fun I => rfl))
  obtain ⟨N, hle⟩ : ∃ N : ℕ, ∀ i : I, (i : ℕ) ≤ N :=
    ⟨I.sup id, fun i => Finset.le_sup (f := id) i.2⟩
  have hT : Measurable fun y : ℝ => toIcoMod (two_pow_pos' N) 0 (y - c) :=
    (measurable_toIcoMod (two_pow_pos' N)).comp (measurable_sub_const c)
  have hae : ∀ᵐ q ∂((unifIco 1).prod bitLaw), q.1 ∈ Ico 0 1 := by
    rw [ae_iff]
    have : {q : ℝ × (ℕ → Bool) | ¬q.1 ∈ Ico (0 : ℝ) 1} = (Ico (0 : ℝ) 1)ᶜ ×ˢ univ := by
      ext q; simp
    rw [this, Measure.prod_prod, unifIco, Measure.smul_apply,
      Measure.restrict_apply measurableSet_Ico.compl, compl_inter_self]
    simp
  -- the marginal of the original law
  have hL : offsetLaw.map I.restrict = (unifIco (2 ^ N)).map (restrictMod I) := by
    rw [offsetLaw, Measure.map_map (Finset.measurable_restrict I) (measurable_offsetsL 1),
      ← map_offsetsL_one_eval N, Measure.map_map (measurable_restrictMod I)
        (measurable_offsetsL_eval 1 N)]
    refine Measure.map_congr ?_
    filter_upwards [hae] with q hq
    funext i
    have := offsetsL_eq_toIcoMod zero_lt_one hq q.2 (hle i) (by positivity)
    simpa [restrictMod] using this
  dsimp only
  rw [Measure.map_map (Finset.measurable_restrict I) (measurable_shiftOffsets c), hL, offsetLaw,
    Measure.map_map ((Finset.measurable_restrict I).comp (measurable_shiftOffsets c))
      (measurable_offsetsL 1), ← map_toIcoMod_sub_unifIco (two_pow_pos' N) c,
    ← map_offsetsL_one_eval N, Measure.map_map hT (measurable_offsetsL_eval 1 N),
    Measure.map_map (measurable_restrictMod I) (hT.comp (measurable_offsetsL_eval 1 N))]
  refine Measure.map_congr (Filter.Eventually.of_forall fun q => ?_)
  funext i
  simp only [Function.comp_apply, Finset.restrict, shiftOffsets, restrictMod]
  -- both sides are `o N - c` modulo `2^i`
  obtain ⟨n, hn⟩ := exists_offsetsL_sub 1 q.1 q.2 (hle i)
  rw [one_mul] at hn
  have h2 : (2 : ℝ) ^ N = 2 ^ (N - i) * 2 ^ (i : ℕ) := by
    rw [← pow_add, Nat.sub_add_cancel (hle i)]
  have e1 : offsetsL 1 q.1 q.2 i - c = (offsetsL 1 q.1 q.2 N - c) - n • (2 : ℝ) ^ (i : ℕ) := by
    rw [← hn]; ring
  have e2 : toIcoMod (two_pow_pos' N) 0 (offsetsL 1 q.1 q.2 N - c) =
      (offsetsL 1 q.1 q.2 N - c) -
        (toIcoDiv (two_pow_pos' N) 0 (offsetsL 1 q.1 q.2 N - c) * 2 ^ (N - i) : ℤ) •
          (2 : ℝ) ^ (i : ℕ) := by
    have h := self_sub_toIcoMod (two_pow_pos' N) 0 (offsetsL 1 q.1 q.2 N - c)
    rw [zsmul_eq_mul] at h ⊢
    push_cast
    linear_combination -h - ((toIcoDiv (two_pow_pos' N) 0 (offsetsL 1 q.1 q.2 N - c) : ℤ) : ℝ) * h2
  rw [e1, e2, toIcoMod_sub_zsmul, toIcoMod_sub_zsmul]

end LatticeProb.DyadicOffset
