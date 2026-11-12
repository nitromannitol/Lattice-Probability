/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module QuantumZipper.Proofs.Probability.Williams.W5Main1 at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.QuantumZipper.Proofs.Probability.Williams.W5Rev

/-!
# W5 (part 6): the reversed side, Markov steps

Node W5(i), reversed side, of `blueprint/EXT_PP_BLUEPRINT.md` (§A.1). For `X = dpath σ (-μ) b`,
`c > 0` and `T_c = hitLevel X (-c)`:

* `measurable_hitLevel_dpath`: `ω ↦ hitLevel (dpath σ μ b ω) a` is measurable (for every `ω`,
  with the junk value `0` off the hitting event);
* `lt_hitLevel_iff_pos`: on a path that hits `-c`, `m < T_c ↔ c + X > 0 on [0, m]`;
* `markov_pos_split`: the Markov property at a fixed time `L` for a functional carrying the
  positivity constraint `z + Y > 0 on [0, L + V]`;
* `lintegral_pos_psiRev`: the Markov property applied twice (at `L`, then at `U`), which turns
  `E[g(c + X(L + U - uᵢ)); c + X > 0 on [0, L + U + r]]` into
  `E[Ψ(c + X_L); c + X > 0 on [0, L]]`, with
  `Ψ(z) = E[g(z + X(U - uᵢ)) ψ_r(z + X_U); z + X > 0 on [0, U]]` (`psiRev`).

Sources: the Markov property of drift Brownian motion (Revuz–Yor III (3.7), used through
`markov_fixed`); the decomposition follows the blueprint sketch of W5(i) (Williams 1974; Rogers–
Pitman 1981, Thm 1). The bookkeeping (IVT for the hitting time, measurability of `T_c` through
`zeroSet`) is own elementary work.
-/

set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper.Williams

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {b : ℝ≥0 → Ω → ℝ} {σ μ : ℝ}

/-- The hitting time of a level by drift Brownian motion is measurable (every `ω`; junk value
`0` off the hitting event). Own elementary proof: `{T ≤ m}` is `{hit in [0, m]} ∪ {never hit}`. -/
theorem measurable_hitLevel_dpath (hb : GoodBM b P) (σ μ a : ℝ) :
    Measurable fun ω => hitLevel (dpath σ μ b ω) a := by
  refine measurable_of_Iic fun m => ?_
  have hS : (fun ω => hitLevel (dpath σ μ b ω) a) ⁻¹' Iic m
      = (fun ω => fun t => dpath σ μ b ω (min t m) - a) ⁻¹' zeroSet
        ∪ {ω | ∃ t : ℝ≥0, dpath σ μ b ω t = a}ᶜ := by
    ext ω
    have hw := continuous_dpath hb σ μ ω
    have hc : Continuous fun t => dpath σ μ b ω (min t m) - a :=
      (hw.comp (continuous_id.min continuous_const)).sub continuous_const
    simp only [mem_preimage, mem_Iic, mem_union, mem_compl_iff, mem_setOf_eq]
    rw [mem_zeroSet_iff hc]
    constructor
    · intro h
      by_cases hh : ∃ t, dpath σ μ b ω t = a
      · left
        exact ⟨hitLevel (dpath σ μ b ω) a, by rw [min_eq_left h, hitLevel_mem hw hh, sub_self]⟩
      · exact Or.inr hh
    · rintro (⟨t, ht⟩ | hh)
      · have h1 : hitLevel (dpath σ μ b ω) a ≤ min t m :=
          csInf_le (OrderBot.bddBelow _)
            (show dpath σ μ b ω (min t m) = a from sub_eq_zero.1 ht)
        exact h1.trans (min_le_right _ _)
      · have he : {t | dpath σ μ b ω t = a} = ∅ :=
          eq_empty_iff_forall_notMem.2 fun t ht => hh ⟨t, ht⟩
        simp [hitLevel, he]
  rw [hS]
  exact (measurableSet_zeroSet.preimage (measurable_pi_iff.2 fun t =>
    (measurable_dpath hb σ μ _).sub_const a)).union (measurableSet_exists_dpath_eq hb σ μ a).compl

/-- On a continuous path from `0` that hits `-c < 0`: `m < T_c ↔ c + x > 0 on [0, m]`.
Own elementary proof (intermediate value theorem via `hitLevel_lt_of_neg`). -/
theorem lt_hitLevel_iff_pos {x : ℝ≥0 → ℝ} (hx : Continuous x) (hx0 : x 0 = 0) {c : ℝ}
    (hc : 0 < c) (hh : ∃ t, x t = -c) (m : ℝ≥0) :
    m < hitLevel x (-c) ↔ ∀ t ≤ m, 0 < c + x t := by
  constructor
  · intro hm t ht
    have := hitLevel_lt_of_neg hx hx0 (neg_lt_zero.2 hc) (lt_of_le_of_lt ht hm)
    linarith
  · intro h
    by_contra hle
    push_neg at hle
    have := h _ hle
    rw [hitLevel_mem hx hh] at this
    linarith

open Classical in
/-- `1{w ∈ posSet V} · a` as an `if` (continuous `w`). -/
theorem posSet_indicator_mul {w : ℝ≥0 → ℝ} (hw : Continuous w) (V : ℝ≥0) (a : ℝ≥0∞) :
    (posSet V).indicator 1 w * a = if (∀ t ≤ V, 0 < w t) then a else 0 := by
  by_cases h : ∀ t ≤ V, 0 < w t
  · rw [indicator_of_mem ((mem_posSet_iff hw V).2 h), if_pos h, Pi.one_apply, one_mul]
  · rw [indicator_of_notMem (fun hm => h ((mem_posSet_iff hw V).1 hm)), if_neg h, zero_mul]

open Classical in
/-- **Markov property at `L` with a positivity constraint on `[0, L + V]`.** -/
theorem markov_pos_split (hb : GoodBM b P) (σ μ z : ℝ) (L V : ℝ≥0)
    {A : (ℝ≥0 → ℝ) → ℝ≥0∞} {F : (ℝ≥0 → ℝ) → ℝ≥0∞} (hA : Measurable A) (hF : Measurable F) :
    ∫⁻ ω, {ω | ∀ t ≤ L + V, 0 < z + dpath σ μ b ω t}.indicator
        (fun ω => A (fun t => dpath σ μ b ω (min t L))
          * F (fun v => z + dpath σ μ b ω (L + v))) ω ∂P
      = ∫⁻ ω, {ω | ∀ t ≤ L, 0 < z + dpath σ μ b ω t}.indicator
        (fun ω => A (fun t => dpath σ μ b ω (min t L))
          * ∫⁻ ω', (posSet V).indicator 1 (fun v => z + dpath σ μ b ω L + dpath σ μ b ω' v)
            * F (fun v => z + dpath σ μ b ω L + dpath σ μ b ω' v) ∂P) ω ∂P := by
  set A' : (ℝ≥0 → ℝ) → ℝ≥0∞ := fun p => (posSet L).indicator 1 (fun t => z + p t) * A p
    with hA'def
  set G : ℝ → (ℝ≥0 → ℝ) → ℝ≥0∞ := fun x w =>
    (posSet V).indicator 1 (fun v => z + x + w v) * F (fun v => z + x + w v) with hGdef
  have hA' : Measurable A' :=
    ((measurable_const.indicator (measurableSet_posSet L)).comp
      (measurable_pi_iff.2 fun t => measurable_const.add (measurable_pi_apply t))).mul hA
  have hpm : Measurable fun q : ℝ × (ℝ≥0 → ℝ) => fun v => z + q.1 + q.2 v :=
    measurable_pi_iff.2 fun t =>
      (measurable_const.add measurable_fst).add ((measurable_pi_apply t).comp measurable_snd)
  have hG : Measurable (Function.uncurry G) :=
    ((measurable_const.indicator (measurableSet_posSet V)).comp hpm).mul (hF.comp hpm)
  have hmk := markov_fixed hb σ μ L hA' hG
  have hcY := continuous_dpath hb σ μ
  have hL : ∀ ω, {ω | ∀ t ≤ L + V, 0 < z + dpath σ μ b ω t}.indicator
        (fun ω => A (fun t => dpath σ μ b ω (min t L))
          * F (fun v => z + dpath σ μ b ω (L + v))) ω
      = A' (fun t => dpath σ μ b ω (min t L)) * G (dpath σ μ b ω L)
          (fun u => dpath σ μ b ω (L + u) - dpath σ μ b ω L) := by
    intro ω
    have hs : Continuous fun t => z + dpath σ μ b ω (min t L) :=
      continuous_const.add ((hcY ω).comp (continuous_id.min continuous_const))
    have e : (fun v => z + dpath σ μ b ω L + (dpath σ μ b ω (L + v) - dpath σ μ b ω L))
        = fun v => z + dpath σ μ b ω (L + v) := funext fun v => by ring
    have hf : Continuous fun v => z + dpath σ μ b ω (L + v) :=
      continuous_const.add ((hcY ω).comp (continuous_const.add continuous_id))
    simp only [hA'def, hGdef, e]
    rw [mul_comm ((posSet L).indicator _ _) _, mul_assoc, posSet_indicator_mul hf,
      mul_comm, mul_assoc, posSet_indicator_mul hs]
    simp only [indicator_apply, mem_setOf_eq]
    have hiff : (∀ t ≤ L + V, 0 < z + dpath σ μ b ω t) ↔
        (∀ t ≤ L, 0 < z + dpath σ μ b ω (min t L)) ∧
          ∀ v ≤ V, 0 < z + dpath σ μ b ω (L + v) := by
      constructor
      · intro h
        exact ⟨fun t ht => h _ ((min_le_right t L).trans le_self_add),
          fun v hv => h _ (add_le_add le_rfl hv)⟩
      · rintro ⟨h1, h2⟩ t ht
        rcases le_total t L with htL | htL
        · simpa [min_eq_left htL] using h1 t htL
        · have := h2 (t - L) (tsub_le_iff_left.2 ht)
          rwa [add_tsub_cancel_of_le htL] at this
    by_cases h1 : ∀ t ≤ L, 0 < z + dpath σ μ b ω (min t L)
    · by_cases h2 : ∀ v ≤ V, 0 < z + dpath σ μ b ω (L + v)
      · rw [if_pos (hiff.2 ⟨h1, h2⟩), if_pos h1, if_pos h2, mul_comm]
      · rw [if_neg (fun h => h2 (hiff.1 h).2), if_pos h1, if_neg h2, zero_mul]
    · rw [if_neg (fun h => h1 (hiff.1 h).1), if_neg h1]
  have hR : ∀ ω, A' (fun t => dpath σ μ b ω (min t L))
        * ∫⁻ ω', G (dpath σ μ b ω L) (dpath σ μ b ω') ∂P
      = {ω | ∀ t ≤ L, 0 < z + dpath σ μ b ω t}.indicator
        (fun ω => A (fun t => dpath σ μ b ω (min t L))
          * ∫⁻ ω', (posSet V).indicator 1 (fun v => z + dpath σ μ b ω L + dpath σ μ b ω' v)
            * F (fun v => z + dpath σ μ b ω L + dpath σ μ b ω' v) ∂P) ω := by
    intro ω
    have hs : Continuous fun t => z + dpath σ μ b ω (min t L) :=
      continuous_const.add ((hcY ω).comp (continuous_id.min continuous_const))
    have hiff : (∀ t ≤ L, 0 < z + dpath σ μ b ω (min t L)) ↔ ∀ t ≤ L, 0 < z + dpath σ μ b ω t :=
      ⟨fun h t ht => by simpa [min_eq_left ht] using h t ht,
        fun h t ht => h _ (min_le_right _ _)⟩
    simp only [hA'def, hGdef]
    rw [mul_assoc, posSet_indicator_mul hs]
    simp only [indicator_apply, mem_setOf_eq]
    by_cases h : ∀ t ≤ L, 0 < z + dpath σ μ b ω t
    · rw [if_pos (hiff.2 h), if_pos h]
    · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]
  calc _ = ∫⁻ ω, A' (fun t => dpath σ μ b ω (min t L)) * G (dpath σ μ b ω L)
          (fun u => dpath σ μ b ω (L + u) - dpath σ μ b ω L) ∂P := lintegral_congr hL
    _ = _ := hmk
    _ = _ := lintegral_congr hR

/-- `Ψ(z) = E[g(z + X(U - uᵢ)) ψ_r(z + X_U); z + X > 0 on [0, U]]`, `X = dpath σ (-μ) b`
(the integrand of `lintegral_chi_reversal`). -/
def psiRev (b : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (σ μ : ℝ) {n : ℕ} (u : Fin n → ℝ≥0)
    (U r : ℝ≥0) (g : (Fin n → ℝ) → ℝ≥0∞) (z : ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, {ω | ∀ t ≤ U, 0 < z + dpath σ (-μ) b ω t}.indicator
    (fun ω => g (fun i => z + dpath σ (-μ) b ω (U - u i))
      * psiR b P σ μ r (z + dpath σ (-μ) b ω U)) ω ∂P

open Classical in
/-- Markov property at `U`: `E[g(z + X(U - uᵢ)); z + X > 0 on [0, U + r]] = Ψ(z)`. -/
theorem psiRev_eq_markov (hb : GoodBM b P) (σ μ : ℝ) {n : ℕ} (u : Fin n → ℝ≥0) (U r : ℝ≥0)
    {g : (Fin n → ℝ) → ℝ≥0∞} (hg : Measurable g) (z : ℝ) :
    ∫⁻ ω, {ω | ∀ t ≤ U + r, 0 < z + dpath σ (-μ) b ω t}.indicator
        (fun ω => g (fun i => z + dpath σ (-μ) b ω (U - u i))) ω ∂P
      = psiRev b P σ μ u U r g z := by
  have h := markov_pos_split (P := P) hb σ (-μ) z U r
    (A := fun p => g (fun i => z + p (U - u i))) (F := fun _ => 1)
    (hg.comp (measurable_pi_iff.2 fun i => measurable_const.add (measurable_pi_apply _)))
    measurable_const
  have hmin : ∀ i, min (U - u i) U = U - u i := fun i => min_eq_left tsub_le_self
  simp only [hmin, mul_one] at h
  rw [h, psiRev]
  refine lintegral_congr fun ω => congrFun (Set.indicator_congr fun ω _ => ?_) ω
  rw [psiR_eq hb σ μ r]

open Classical in
/-- **Markov property twice** (at `L`, then at `U`). -/
theorem lintegral_pos_psiRev (hb : GoodBM b P) (σ μ c : ℝ) {n : ℕ} (u : Fin n → ℝ≥0)
    (U r : ℝ≥0) {g : (Fin n → ℝ) → ℝ≥0∞} (hg : Measurable g) (L : ℝ≥0) :
    ∫⁻ ω, {ω | ∀ t ≤ L + (U + r), 0 < c + dpath σ (-μ) b ω t}.indicator
        (fun ω => g (fun i => c + dpath σ (-μ) b ω (L + (U - u i)))) ω ∂P
      = ∫⁻ ω, {ω | ∀ t ≤ L, 0 < c + dpath σ (-μ) b ω t}.indicator
        (fun ω => psiRev b P σ μ u U r g (c + dpath σ (-μ) b ω L)) ω ∂P := by
  have h := markov_pos_split (P := P) hb σ (-μ) c L (U + r)
    (A := fun _ => 1) (F := fun w => g (fun i => w (U - u i))) measurable_const
    (hg.comp (measurable_pi_iff.2 fun i => measurable_pi_apply _))
  simp only [one_mul] at h
  rw [h]
  refine lintegral_congr fun ω => congrFun (Set.indicator_congr fun ω _ => ?_) ω
  rw [← psiRev_eq_markov hb σ μ u U r hg]
  refine lintegral_congr fun ω' => ?_
  rw [posSet_indicator_mul (w := fun v => c + dpath σ (-μ) b ω L + dpath σ (-μ) b ω' v)
    (continuous_const.add (continuous_dpath hb σ (-μ) ω'))]
  simp only [indicator_apply, mem_setOf_eq]

end QuantumZipper.Williams
