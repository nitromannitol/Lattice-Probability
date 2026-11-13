/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module ReflectedGMS.Process.HoldingTimeChange at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.ReflectedGMS.Process.AreaClocks
import LatticeProb.Bonanno.ReflectedWalk.PathProperties

/-!
# Two holding-time families on one chain are a pathwise homeomorphic time change

The constructed reflected process `IndexSet.X Gs Y w E` of (3.26) depends on the
unit holding variables `E` **only through the products** `T_ξ = E_ξ / w(Y_ξ)`:
the index set `Ξ`, the successor `ξ̂` and the visited vertices `Y_ξ` are functions
of `(Gs, Y)` alone.  Consequently two holding families `E₁`, `E₂` on the *same*
chain produce two processes whose holding intervals `[τ_ξ, τ_ξ̂)` tile `[0,∞)` in
the same order, only with different lengths.  The map carrying the second tiling
onto the first is therefore a strictly increasing homeomorphism of `[0,∞)`, and
it conjugates the two processes.

This file constructs that map and proves it, with no probabilistic input beyond
the two instances of the manuscript's (3.16).

## The map

`clock Gs Y w E₁ E₂` is the elapsed `E₁`-time as a function of the elapsed
`E₂`-time,

  `clock t = ∑_{ξ ∈ Ξ} (E₁_ξ / E₂_ξ) · min (T²_ξ) (t - τ²_ξ)`,

i.e. the total `E₁`-length of the parts of the `E₂`-holding intervals lying
below `t`.  It is monotone by construction, it sends `τ²_η` to `τ¹_η`
(`clock_tau`), and on `[τ²_η, τ²_η̂)` it is the affine map onto `[τ¹_η, τ¹_η̂)`
(`clock_of_inInterval`, `clock_mem_interval`).

Two facts make it a homeomorphism.

* **Strict increase** (`clock_strictMono`).  A monotone clock increases strictly
  across `[s,t)` as soon as some holding interval meets `(s,t)` in positive
  length; that is exactly Lemma 3.7 (`PathProperties.volume_notInOpenInterval`),
  which says the times lying in *no open* holding interval are Lebesgue-null.
* **Bijectivity** (`clock_clock`).  The construction is symmetric in `E₁`, `E₂`
  and the two clocks are mutually inverse.  On a holding interval this is the
  cancellation `(E₁/E₂)·(E₂/E₁) = 1`; at a time lying in no holding interval it
  is again Lemma 3.7, for the *other* family.

A strictly monotone bijection of `ℝ≥0` is an order isomorphism, and `ℝ≥0`
carries the order topology, so no separate continuity argument is needed
(`isHomeomorphicTimeChange_X`).

The times lying in no holding interval are handled, not excluded: `X` is `∞`
there, and `clock_notMem` shows the clock carries those times to times where the
other process is also `∞`.  Nothing here assumes that the holding intervals cover
`[0,∞)` — property (i) of Theorem 1.6 is only an almost-sure statement at each
fixed time, and the identity proved here is for *every* time.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped NNReal ENNReal

namespace ReflectedGMS.HoldingTimeChange

open ReflectedWalk ReflectedWalk.IndexSet

universe u

/-! ## Elementary helpers -/

section Helpers

variable {ι : Type*}

/-- Indicators of one set are monotone in the indicated function. -/
theorem indicator_mono {S : Set ι} {f g : ι → ℝ≥0∞} (h : ∀ a, f a ≤ g a) (a : ι) :
    S.indicator f a ≤ S.indicator g a := by
  by_cases ha : a ∈ S
  · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha]
    exact h a
  · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem ha]

/-- A sum with infinitely many terms bounded below by a fixed nonzero value is
infinite. -/
theorem tsum_eq_top_of_infinite_le {f : ι → ℝ≥0∞} {S : Set ι} (hS : S.Infinite)
    {c : ℝ≥0∞} (hc : c ≠ 0) (hf : ∀ i ∈ S, c ≤ f i) : ∑' i, f i = ⊤ := by
  have hinf : Infinite S := Set.Infinite.to_subtype hS
  refine top_unique ?_
  calc (⊤ : ℝ≥0∞) = ∑' _ : S, c := (ENNReal.tsum_const_eq_top_of_ne_zero hc).symm
    _ ≤ ∑' i, f i :=
        ENNReal.summable.tsum_le_tsum_of_inj (fun i : S => (i : ι)) Subtype.val_injective
          (fun _ _ => zero_le) (fun i => hf i.1 i.2) ENNReal.summable

/-- Truncated subtraction of a finite amount strictly below the larger argument
is strictly monotone. -/
theorem tsub_lt_tsub_of_lt {a b c : ℝ≥0∞} (hc : c ≠ ⊤) (hcb : c < b) (hab : a < b) :
    a - c < b - c := by
  rcases le_or_gt a c with h | h
  · rw [tsub_eq_zero_of_le h]
    exact pos_iff_ne_zero.2 fun h0 => absurd (tsub_eq_zero_iff_le.1 h0) (not_le.2 hcb)
  · rw [ENNReal.sub_lt_iff_lt_right hc h.le, tsub_add_cancel_of_le hcb.le]
    exact hab

end Helpers

variable {V : Type u}

/-! ## The deterministic data -/

/-- The deterministic data of one coupled chain: the coupling identity (3.12),
the exhaustion clauses and positivity of the rate. -/
structure ChainData (Gs : ℕ → Set V) (Y : ℕ → ℕ → V) (w : V → ℝ) : Prop where
  consistent : Consistent Gs Y
  monotone : Monotone Gs
  cover : ∀ x, ∃ n, x ∈ Gs n
  ratePos : ∀ x, 0 < w x

/-- The deterministic data of one holding family: positive unit holding times and
the conclusion (3.16) of Lemma 3.5. -/
structure ClockData (Gs : ℕ → Set V) (Y : ℕ → ℕ → V) (w : V → ℝ)
    (E : (ℕ →₀ ℕ) → ℝ) : Prop where
  pos : ∀ a, 0 < E a
  summable : HoldingTimesSummable Gs Y w E

/-! ## The clock -/

/-- The `E₁`-length of the part of the `E₂`-holding interval of `a` lying below
`t`. -/
noncomputable def clockTerm (Gs : ℕ → Set V) (Y : ℕ → ℕ → V) (w : V → ℝ)
    (E₁ E₂ : (ℕ →₀ ℕ) → ℝ) (t : ℝ≥0∞) (a : ℕ →₀ ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (E₁ a / E₂ a) * min (holding Gs Y w E₂ a) (t - tau Gs Y w E₂ a)

/-- **The clock**: the elapsed `E₁`-time at `E₂`-time `t`. -/
noncomputable def clock (Gs : ℕ → Set V) (Y : ℕ → ℕ → V) (w : V → ℝ)
    (E₁ E₂ : (ℕ →₀ ℕ) → ℝ) (t : ℝ≥0∞) : ℝ≥0∞ :=
  ∑' a, (realizedSet Gs Y).indicator (clockTerm Gs Y w E₁ E₂ t) a

/-- The `ℝ≥0`-valued clock. -/
noncomputable def timeChange (Gs : ℕ → Set V) (Y : ℕ → ℕ → V) (w : V → ℝ)
    (E₁ E₂ : (ℕ →₀ ℕ) → ℝ) (t : ℝ≥0) : ℝ≥0 :=
  (clock Gs Y w E₁ E₂ (t : ℝ≥0∞)).toNNReal

variable {Gs : ℕ → Set V} {Y : ℕ → ℕ → V} {w : V → ℝ} {E₁ E₂ : (ℕ →₀ ℕ) → ℝ}

/-! ### Consequences of the deterministic data -/

theorem ClockData.tau_ne_top {E : (ℕ →₀ ℕ) → ℝ} (hd : ClockData Gs Y w E)
    {a : ℕ →₀ ℕ} (ha : Realized Gs Y a) : tau Gs Y w E a ≠ ⊤ :=
  (hd.summable.2 a ha).ne

theorem ChainData.tau_succ (hcd : ChainData Gs Y w) {E : (ℕ →₀ ℕ) → ℝ}
    {η : ℕ →₀ ℕ} (hη : Realized Gs Y η) :
    tau Gs Y w E (succ Gs Y η) = tau Gs Y w E η + holding Gs Y w E η :=
  PathProperties.tau_succ Gs Y w E hcd.consistent hcd.monotone hcd.cover hη

theorem ChainData.realized_succ (hcd : ChainData Gs Y w) {η : ℕ →₀ ℕ}
    (hη : Realized Gs Y η) : Realized Gs Y (succ Gs Y η) :=
  (hcd.consistent.succ_spec Gs Y hcd.monotone hcd.cover hη).1

theorem ChainData.lt_succ (hcd : ChainData Gs Y w) {η : ℕ →₀ ℕ}
    (hη : Realized Gs Y η) : toLex η < toLex (succ Gs Y η) :=
  (hcd.consistent.succ_spec Gs Y hcd.monotone hcd.cover hη).2.1

theorem ChainData.tau_succ_le (hcd : ChainData Gs Y w) {E : (ℕ →₀ ℕ) → ℝ}
    {η η' : ℕ →₀ ℕ} (hη : Realized Gs Y η) (hη' : Realized Gs Y η')
    (hlt : toLex η < toLex η') :
    tau Gs Y w E (succ Gs Y η) ≤ tau Gs Y w E η' :=
  hcd.consistent.tau_succ_le Gs Y w E hcd.monotone hcd.cover hη hη' hlt

/-! ### Lemma 3.7 in the form used here -/

/-- Between two distinct finite times there is a time interior to some holding
interval.  This is Lemma 3.7 (`PathProperties.volume_notInOpenInterval`): the
complement is Lebesgue-null, while a nonempty open interval is not. -/
theorem exists_inOpenInterval_between {E : (ℕ →₀ ℕ) → ℝ} (hcd : ChainData Gs Y w)
    (hd : ClockData Gs Y w E) {s t : ℝ≥0∞} (hst : s < t) (ht : t ≠ ⊤) :
    ∃ ρ : ℝ≥0∞, s < ρ ∧ ρ < t ∧ PathProperties.InOpenInterval Gs Y w E ρ := by
  have hs : s ≠ ⊤ := ne_top_of_lt hst
  have hlt : s.toReal < t.toReal := (ENNReal.toReal_lt_toReal hs ht).2 hst
  have htpos : 0 < t.toReal := lt_of_le_of_lt ENNReal.toReal_nonneg hlt
  by_contra hcon
  push_neg at hcon
  have hsub : Ioo s.toReal t.toReal ⊆
      {r : ℝ | 0 < r ∧ ¬ PathProperties.InOpenInterval Gs Y w E (ENNReal.ofReal r)} := by
    intro r hr
    have hrpos : 0 < r := lt_of_le_of_lt ENNReal.toReal_nonneg hr.1
    refine ⟨hrpos, hcon _ ?_ ?_⟩
    · rw [← ENNReal.ofReal_toReal hs]
      exact (ENNReal.ofReal_lt_ofReal_iff hrpos).2 hr.1
    · rw [← ENNReal.ofReal_toReal ht]
      exact (ENNReal.ofReal_lt_ofReal_iff htpos).2 hr.2
  have hzero : volume (Ioo s.toReal t.toReal) = 0 :=
    measure_mono_null hsub
      (PathProperties.volume_notInOpenInterval Gs Y w E hcd.consistent hcd.monotone
        hcd.cover hd.summable)
  rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at hzero
  exact absurd hzero (not_le.2 (sub_pos.2 hlt))

/-! ### The rescaling factor -/

theorem ofReal_ratio_mul_holding (hcd : ChainData Gs Y w) (hd₁ : ClockData Gs Y w E₁)
    (hd₂ : ClockData Gs Y w E₂) (a : ℕ →₀ ℕ) :
    ENNReal.ofReal (E₁ a / E₂ a) * holding Gs Y w E₂ a = holding Gs Y w E₁ a := by
  have h2 : E₂ a ≠ 0 := (hd₂.pos a).ne'
  have hwa : w (Yxi Gs Y a) ≠ 0 := (hcd.ratePos _).ne'
  have hnn : (0 : ℝ) ≤ E₁ a / E₂ a := (div_pos (hd₁.pos a) (hd₂.pos a)).le
  rw [holding, holding, ← ENNReal.ofReal_mul hnn]
  congr 1
  field_simp

theorem ofReal_ratio_ne_zero (hd₁ : ClockData Gs Y w E₁) (hd₂ : ClockData Gs Y w E₂)
    (a : ℕ →₀ ℕ) : ENNReal.ofReal (E₁ a / E₂ a) ≠ 0 :=
  (ENNReal.ofReal_pos.2 (div_pos (hd₁.pos a) (hd₂.pos a))).ne'

theorem ofReal_ratio_mul_ofReal_ratio (hd₁ : ClockData Gs Y w E₁)
    (hd₂ : ClockData Gs Y w E₂) (a : ℕ →₀ ℕ) :
    ENNReal.ofReal (E₁ a / E₂ a) * ENNReal.ofReal (E₂ a / E₁ a) = 1 := by
  have h1 : E₁ a ≠ 0 := (hd₁.pos a).ne'
  have h2 : E₂ a ≠ 0 := (hd₂.pos a).ne'
  have hnn : (0 : ℝ) ≤ E₁ a / E₂ a := (div_pos (hd₁.pos a) (hd₂.pos a)).le
  have hprod : E₁ a / E₂ a * (E₂ a / E₁ a) = 1 := by field_simp
  rw [← ENNReal.ofReal_mul hnn, hprod, ENNReal.ofReal_one]

/-! ### Evaluation of the clock terms -/

theorem clockTerm_mono {s t : ℝ≥0∞} (hst : s ≤ t) (a : ℕ →₀ ℕ) :
    clockTerm Gs Y w E₁ E₂ s a ≤ clockTerm Gs Y w E₁ E₂ t a :=
  mul_le_mul' le_rfl (min_le_min le_rfl (tsub_le_tsub_right hst _))

theorem clockTerm_eq_zero {t : ℝ≥0∞} {a : ℕ →₀ ℕ} (h : t ≤ tau Gs Y w E₂ a) :
    clockTerm Gs Y w E₁ E₂ t a = 0 := by
  rw [clockTerm, tsub_eq_zero_of_le h, min_eq_right (zero_le), mul_zero]

theorem clockTerm_eq_holding (hcd : ChainData Gs Y w) (hd₁ : ClockData Gs Y w E₁)
    (hd₂ : ClockData Gs Y w E₂) {t : ℝ≥0∞} {a : ℕ →₀ ℕ} (ha : Realized Gs Y a)
    (h : tau Gs Y w E₂ a + holding Gs Y w E₂ a ≤ t) :
    clockTerm Gs Y w E₁ E₂ t a = holding Gs Y w E₁ a := by
  have hle : holding Gs Y w E₂ a ≤ t - tau Gs Y w E₂ a :=
    ENNReal.le_sub_of_add_le_left (hd₂.tau_ne_top ha) h
  rw [clockTerm, min_eq_left hle, ofReal_ratio_mul_holding hcd hd₁ hd₂ a]

theorem clockTerm_eq_of_inInterval (hd₂ : ClockData Gs Y w E₂) {t : ℝ≥0∞}
    {a : ℕ →₀ ℕ} (ha : Realized Gs Y a) (h₁ : tau Gs Y w E₂ a ≤ t)
    (h₂ : t < tau Gs Y w E₂ a + holding Gs Y w E₂ a) :
    clockTerm Gs Y w E₁ E₂ t a
      = ENNReal.ofReal (E₁ a / E₂ a) * (t - tau Gs Y w E₂ a) := by
  have hlt : t - tau Gs Y w E₂ a < holding Gs Y w E₂ a := by
    rw [ENNReal.sub_lt_iff_lt_right (hd₂.tau_ne_top ha) h₁, add_comm]
    exact h₂
  rw [clockTerm, min_eq_right hlt.le]

/-! ### Monotonicity, the value at a clock time, and the affine formula -/

theorem clock_mono {s t : ℝ≥0∞} (hst : s ≤ t) :
    clock Gs Y w E₁ E₂ s ≤ clock Gs Y w E₁ E₂ t := by
  show ∑' a, (realizedSet Gs Y).indicator (clockTerm Gs Y w E₁ E₂ s) a
      ≤ ∑' a, (realizedSet Gs Y).indicator (clockTerm Gs Y w E₁ E₂ t) a
  exact ENNReal.tsum_le_tsum (indicator_mono fun a => clockTerm_mono hst a)

/-- **The clock carries `τ²_η` to `τ¹_η`.** -/
theorem clock_tau (hcd : ChainData Gs Y w) (hd₁ : ClockData Gs Y w E₁)
    (hd₂ : ClockData Gs Y w E₂) {η : ℕ →₀ ℕ} (hη : Realized Gs Y η) :
    clock Gs Y w E₁ E₂ (tau Gs Y w E₂ η) = tau Gs Y w E₁ η := by
  show ∑' a, (realizedSet Gs Y).indicator
        (clockTerm Gs Y w E₁ E₂ (tau Gs Y w E₂ η)) a
      = ∑' a, (below Gs Y η).indicator (holding Gs Y w E₁) a
  refine tsum_congr fun a => ?_
  by_cases hr : Realized Gs Y a
  · rw [Set.indicator_of_mem (show a ∈ realizedSet Gs Y from hr)]
    by_cases hlt : toLex a < toLex η
    · rw [Set.indicator_of_mem (show a ∈ below Gs Y η from ⟨hr, hlt⟩)]
      refine clockTerm_eq_holding hcd hd₁ hd₂ hr ?_
      rw [← hcd.tau_succ (E := E₂) hr]
      exact hcd.tau_succ_le hr hη hlt
    · rw [Set.indicator_of_notMem (show a ∉ below Gs Y η from fun hb => hlt hb.2)]
      exact clockTerm_eq_zero (tau_mono Gs Y w E₂ (not_lt.mp hlt))
  · rw [Set.indicator_of_notMem (show a ∉ realizedSet Gs Y from hr),
      Set.indicator_of_notMem (show a ∉ below Gs Y η from fun hb => hr hb.1)]

/-- **The affine formula on a holding interval.** -/
theorem clock_of_inInterval (hcd : ChainData Gs Y w) (hd₁ : ClockData Gs Y w E₁)
    (hd₂ : ClockData Gs Y w E₂) {η : ℕ →₀ ℕ} {t : ℝ≥0∞}
    (hI : InInterval Gs Y w E₂ η t) :
    clock Gs Y w E₁ E₂ t
      = tau Gs Y w E₁ η + ENNReal.ofReal (E₁ η / E₂ η) * (t - tau Gs Y w E₂ η) := by
  obtain ⟨hη, h1, h2⟩ := hI
  have h2' : t < tau Gs Y w E₂ η + holding Gs Y w E₂ η := by
    rw [← hcd.tau_succ (E := E₂) hη]; exact h2
  have hcl : clock Gs Y w E₁ E₂ t
      = ∑' a, (realizedSet Gs Y).indicator (clockTerm Gs Y w E₁ E₂ t) a := rfl
  have hta : tau Gs Y w E₁ η
      = ∑' a, (below Gs Y η).indicator (holding Gs Y w E₁) a := rfl
  rw [hcl, hta, ENNReal.tsum_eq_add_tsum_ite η,
    Set.indicator_of_mem (show η ∈ realizedSet Gs Y from hη),
    clockTerm_eq_of_inInterval hd₂ hη h1 h2']
  refine Eq.trans (add_comm _ _) ?_
  congr 1
  refine tsum_congr fun a => ?_
  by_cases hae : a = η
  · subst hae
    rw [if_pos rfl,
      Set.indicator_of_notMem (show a ∉ below Gs Y a from fun hb => lt_irrefl _ hb.2)]
  · rw [if_neg hae]
    by_cases hr : Realized Gs Y a
    · rw [Set.indicator_of_mem (show a ∈ realizedSet Gs Y from hr)]
      by_cases hlt : toLex a < toLex η
      · rw [Set.indicator_of_mem (show a ∈ below Gs Y η from ⟨hr, hlt⟩)]
        refine clockTerm_eq_holding hcd hd₁ hd₂ hr ?_
        rw [← hcd.tau_succ (E := E₂) hr]
        exact le_trans (hcd.tau_succ_le hr hη hlt) h1
      · rw [Set.indicator_of_notMem (show a ∉ below Gs Y η from fun hb => hlt hb.2)]
        refine clockTerm_eq_zero (le_trans h2'.le ?_)
        rw [← hcd.tau_succ (E := E₂) hη]
        exact hcd.tau_succ_le hη hr
          (lt_of_le_of_ne (not_lt.mp hlt) fun hc => hae (toLex_inj.mp hc.symm))
    · rw [Set.indicator_of_notMem (show a ∉ realizedSet Gs Y from hr),
        Set.indicator_of_notMem (show a ∉ below Gs Y η from fun hb => hr hb.1)]

/-! ### Finiteness, strict increase and the interval correspondence -/

theorem clock_ne_top (hcd : ChainData Gs Y w) (hd₁ : ClockData Gs Y w E₁)
    (hd₂ : ClockData Gs Y w E₂) {t : ℝ≥0∞} (ht : t ≠ ⊤) :
    clock Gs Y w E₁ E₂ t ≠ ⊤ := by
  obtain ⟨K, hK⟩ := PathProperties.exists_lt_tau_addr_zero Gs Y w E₂ hd₂.summable.1 ht
  have hmono : clock Gs Y w E₁ E₂ t
      ≤ clock Gs Y w E₁ E₂ (tau Gs Y w E₂ (addr Gs Y 0 K)) := clock_mono hK.le
  rw [clock_tau hcd hd₁ hd₂ (realized_addr Gs Y 0 K)] at hmono
  exact ne_top_of_le_ne_top (hd₁.tau_ne_top (realized_addr Gs Y 0 K)) hmono

/-- **The clock increases strictly.**  Lemma 3.7 supplies, between two distinct
finite times, a time interior to a holding interval; that interval's contribution
is strictly larger at the later time. -/
theorem clock_strictMono (hcd : ChainData Gs Y w) (hd₁ : ClockData Gs Y w E₁)
    (hd₂ : ClockData Gs Y w E₂) {s t : ℝ≥0∞} (hst : s < t) (ht : t ≠ ⊤) :
    clock Gs Y w E₁ E₂ s < clock Gs Y w E₁ E₂ t := by
  obtain ⟨ρ, hsρ, hρt, η, hη, hlo, hhi⟩ :=
    exists_inOpenInterval_between hcd hd₂ hst ht
  have hfin : tau Gs Y w E₂ η ≠ ⊤ := hd₂.tau_ne_top hη
  have hstop : clock Gs Y w E₁ E₂ s ≠ ⊤ := clock_ne_top hcd hd₁ hd₂ (ne_top_of_lt hst)
  show ∑' a, (realizedSet Gs Y).indicator (clockTerm Gs Y w E₁ E₂ s) a
      < ∑' a, (realizedSet Gs Y).indicator (clockTerm Gs Y w E₁ E₂ t) a
  refine ENNReal.tsum_lt_tsum (i := η) hstop
    (indicator_mono fun a => clockTerm_mono hst.le a) ?_
  rw [Set.indicator_of_mem (show η ∈ realizedSet Gs Y from hη),
    Set.indicator_of_mem (show η ∈ realizedSet Gs Y from hη)]
  show ENNReal.ofReal (E₁ η / E₂ η) * min (holding Gs Y w E₂ η) (s - tau Gs Y w E₂ η)
      < ENNReal.ofReal (E₁ η / E₂ η) * min (holding Gs Y w E₂ η) (t - tau Gs Y w E₂ η)
  refine ENNReal.mul_lt_mul_right (ofReal_ratio_ne_zero hd₁ hd₂ η) ENNReal.ofReal_ne_top ?_
  have h1 : ρ - tau Gs Y w E₂ η < holding Gs Y w E₂ η := by
    rw [ENNReal.sub_lt_iff_lt_right hfin hlo.le, add_comm]
    exact hhi
  calc min (holding Gs Y w E₂ η) (s - tau Gs Y w E₂ η)
      ≤ s - tau Gs Y w E₂ η := min_le_right _ _
    _ < ρ - tau Gs Y w E₂ η := tsub_lt_tsub_of_lt hfin hlo hsρ
    _ = min (holding Gs Y w E₂ η) (ρ - tau Gs Y w E₂ η) := (min_eq_right h1.le).symm
    _ ≤ min (holding Gs Y w E₂ η) (t - tau Gs Y w E₂ η) :=
        min_le_min le_rfl (tsub_le_tsub_right hρt.le _)

/-- **Holding intervals correspond.**  The clock maps the `E₂`-holding interval
of `η` into the `E₁`-holding interval of the same `η`. -/
theorem clock_mem_interval (hcd : ChainData Gs Y w) (hd₁ : ClockData Gs Y w E₁)
    (hd₂ : ClockData Gs Y w E₂) {η : ℕ →₀ ℕ} {t : ℝ≥0∞}
    (hI : InInterval Gs Y w E₂ η t) :
    InInterval Gs Y w E₁ η (clock Gs Y w E₁ E₂ t) := by
  have hη : Realized Gs Y η := hI.1
  have h1 : tau Gs Y w E₂ η ≤ t := hI.2.1
  have h2' : t < tau Gs Y w E₂ η + holding Gs Y w E₂ η := by
    rw [← hcd.tau_succ (E := E₂) hη]; exact hI.2.2
  have hval := clock_of_inInterval hcd hd₁ hd₂ hI
  refine ⟨hη, ?_, ?_⟩
  · rw [hval]
    exact le_self_add
  · rw [hval, hcd.tau_succ (E := E₁) hη, ← ofReal_ratio_mul_holding hcd hd₁ hd₂ η]
    refine ENNReal.add_lt_add_left (hd₁.tau_ne_top hη) ?_
    refine ENNReal.mul_lt_mul_right (ofReal_ratio_ne_zero hd₁ hd₂ η)
      ENNReal.ofReal_ne_top ?_
    rw [ENNReal.sub_lt_iff_lt_right (hd₂.tau_ne_top hη) h1, add_comm]
    exact h2'

/-- **Gaps correspond.**  A time lying in no `E₂`-holding interval is carried to
a time lying in no `E₁`-holding interval. -/
theorem clock_notMem (hcd : ChainData Gs Y w) (hd₁ : ClockData Gs Y w E₁)
    (hd₂ : ClockData Gs Y w E₂) {t : ℝ≥0∞} (ht : t ≠ ⊤)
    (hgap : ∀ η, ¬ InInterval Gs Y w E₂ η t) (η : ℕ →₀ ℕ) :
    ¬ InInterval Gs Y w E₁ η (clock Gs Y w E₁ E₂ t) := by
  rintro ⟨hη, h1, h2⟩
  rcases le_or_gt (tau Gs Y w E₂ η) t with hle | hlt
  · have hsucc : tau Gs Y w E₂ (succ Gs Y η) ≤ t := by
      by_contra hc
      exact hgap η ⟨hη, hle, not_le.mp hc⟩
    have hmono : clock Gs Y w E₁ E₂ (tau Gs Y w E₂ (succ Gs Y η))
        ≤ clock Gs Y w E₁ E₂ t := clock_mono hsucc
    rw [clock_tau hcd hd₁ hd₂ (hcd.realized_succ hη)] at hmono
    exact absurd h2 (not_lt.2 hmono)
  · have hs := clock_strictMono hcd hd₁ hd₂ hlt (hd₂.tau_ne_top hη)
    rw [clock_tau hcd hd₁ hd₂ hη] at hs
    exact absurd h1 (not_le.2 hs)

/-! ### The two clocks are mutually inverse -/

/-- A sum of `E₁`-holding times over a set whose successors' `E₁`-clocks all stay
below `y` is at most `y`: every finite subsum is dominated by one clock value. -/
theorem tsum_indicator_holding_le (hcd : ChainData Gs Y w) {S : Set (ℕ →₀ ℕ)}
    (hS : ∀ a ∈ S, Realized Gs Y a) {y : ℝ≥0∞}
    (hy : ∀ b ∈ S, tau Gs Y w E₁ (succ Gs Y b) ≤ y) :
    ∑' a, S.indicator (holding Gs Y w E₁) a ≤ y := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun F => ?_
  by_cases hF : (F.filter (fun a => a ∈ S)).Nonempty
  · obtain ⟨b, hbF, hbmax⟩ :=
      Finset.exists_max_image (F.filter (fun a => a ∈ S)) (fun a => toLex a) hF
    have hbS : b ∈ S := (Finset.mem_filter.1 hbF).2
    have hstep : ∀ a ∈ F, S.indicator (holding Gs Y w E₁) a
        ≤ (below Gs Y (succ Gs Y b)).indicator (holding Gs Y w E₁) a := by
      intro a haF
      by_cases haS : a ∈ S
      · have hmem : a ∈ below Gs Y (succ Gs Y b) :=
          ⟨hS a haS, lt_of_le_of_lt (hbmax a (Finset.mem_filter.2 ⟨haF, haS⟩))
            (hcd.lt_succ (hS b hbS))⟩
        rw [Set.indicator_of_mem haS, Set.indicator_of_mem hmem]
      · rw [Set.indicator_of_notMem haS]
        exact zero_le
    calc ∑ a ∈ F, S.indicator (holding Gs Y w E₁) a
        ≤ ∑ a ∈ F, (below Gs Y (succ Gs Y b)).indicator (holding Gs Y w E₁) a :=
          Finset.sum_le_sum hstep
      _ ≤ ∑' a, (below Gs Y (succ Gs Y b)).indicator (holding Gs Y w E₁) a :=
          ENNReal.sum_le_tsum F
      _ = tau Gs Y w E₁ (succ Gs Y b) := rfl
      _ ≤ y := hy b hbS
  · have hzero : ∀ a ∈ F, S.indicator (holding Gs Y w E₁) a = 0 := fun a haF =>
      Set.indicator_of_notMem (fun haS => hF ⟨a, Finset.mem_filter.2 ⟨haF, haS⟩⟩) _
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero]
    exact zero_le

/-- **The two clocks are mutually inverse.** -/
theorem clock_clock (hcd : ChainData Gs Y w) (hd₁ : ClockData Gs Y w E₁)
    (hd₂ : ClockData Gs Y w E₂) {y : ℝ≥0∞} (hy : y ≠ ⊤) :
    clock Gs Y w E₁ E₂ (clock Gs Y w E₂ E₁ y) = y := by
  by_cases hex : ∃ η, InInterval Gs Y w E₁ η y
  · obtain ⟨η, hI⟩ := hex
    have hIz : InInterval Gs Y w E₂ η (clock Gs Y w E₂ E₁ y) :=
      clock_mem_interval hcd hd₂ hd₁ hI
    have hzval : clock Gs Y w E₂ E₁ y
        = tau Gs Y w E₂ η + ENNReal.ofReal (E₂ η / E₁ η) * (y - tau Gs Y w E₁ η) :=
      clock_of_inInterval hcd hd₂ hd₁ hI
    have hsub : clock Gs Y w E₂ E₁ y - tau Gs Y w E₂ η
        = ENNReal.ofReal (E₂ η / E₁ η) * (y - tau Gs Y w E₁ η) := by
      rw [hzval, ENNReal.add_sub_cancel_left (hd₂.tau_ne_top hI.1)]
    rw [clock_of_inInterval hcd hd₁ hd₂ hIz, hsub, ← mul_assoc,
      ofReal_ratio_mul_ofReal_ratio hd₁ hd₂ η, one_mul,
      add_tsub_cancel_of_le hI.2.1]
  · push_neg at hex
    have hgz : ∀ η, ¬ InInterval Gs Y w E₂ η (clock Gs Y w E₂ E₁ y) :=
      clock_notMem hcd hd₂ hd₁ hy hex
    have hSy : ∀ b ∈ {a : ℕ →₀ ℕ | Realized Gs Y a ∧
        tau Gs Y w E₂ (succ Gs Y a) ≤ clock Gs Y w E₂ E₁ y},
        tau Gs Y w E₁ (succ Gs Y b) ≤ y := by
      rintro b ⟨hb, hbz⟩
      by_contra hc
      have hlt : y < tau Gs Y w E₁ (succ Gs Y b) := not_le.mp hc
      have hsm := clock_strictMono hcd hd₂ hd₁ hlt
        (hd₁.tau_ne_top (hcd.realized_succ hb))
      rw [clock_tau hcd hd₂ hd₁ (hcd.realized_succ hb)] at hsm
      exact absurd hbz (not_le.2 hsm)
    have hle : clock Gs Y w E₁ E₂ (clock Gs Y w E₂ E₁ y) ≤ y := by
      have hcl : clock Gs Y w E₁ E₂ (clock Gs Y w E₂ E₁ y)
          = ∑' a, (realizedSet Gs Y).indicator
              (clockTerm Gs Y w E₁ E₂ (clock Gs Y w E₂ E₁ y)) a := rfl
      rw [hcl]
      refine le_trans (ENNReal.tsum_le_tsum fun a => ?_)
        (tsum_indicator_holding_le hcd (fun a ha => ha.1) hSy)
      by_cases hr : Realized Gs Y a
      · rw [Set.indicator_of_mem (show a ∈ realizedSet Gs Y from hr)]
        rcases le_or_gt (clock Gs Y w E₂ E₁ y) (tau Gs Y w E₂ a) with hlea | hgta
        · rw [clockTerm_eq_zero hlea]
          exact zero_le
        · have hsuc : tau Gs Y w E₂ (succ Gs Y a) ≤ clock Gs Y w E₂ E₁ y := by
            by_contra hc
            exact hgz a ⟨hr, hgta.le, not_le.mp hc⟩
          rw [Set.indicator_of_mem
            (show a ∈ {a : ℕ →₀ ℕ | Realized Gs Y a ∧
              tau Gs Y w E₂ (succ Gs Y a) ≤ clock Gs Y w E₂ E₁ y} from ⟨hr, hsuc⟩)]
          refine le_of_eq (clockTerm_eq_holding hcd hd₁ hd₂ hr ?_)
          rw [← hcd.tau_succ (E := E₂) hr]
          exact hsuc
      · rw [Set.indicator_of_notMem (show a ∉ realizedSet Gs Y from hr)]
        exact zero_le
    refine le_antisymm hle ?_
    by_contra hcon
    have hlt : clock Gs Y w E₁ E₂ (clock Gs Y w E₂ E₁ y) < y := not_le.mp hcon
    obtain ⟨ρ, h1, h2, η, hη, hlo, hhi⟩ :=
      exists_inOpenInterval_between hcd hd₁ hlt hy
    have hρsucc : ρ < tau Gs Y w E₁ (succ Gs Y η) := by
      rw [hcd.tau_succ (E := E₁) hη]; exact hhi
    have hyη : tau Gs Y w E₁ (succ Gs Y η) ≤ y := by
      by_contra hc
      exact hex η ⟨hη, (hlo.trans h2).le, not_le.mp hc⟩
    have hmono₁ : clock Gs Y w E₂ E₁ (tau Gs Y w E₁ (succ Gs Y η))
        ≤ clock Gs Y w E₂ E₁ y := clock_mono hyη
    rw [clock_tau hcd hd₂ hd₁ (hcd.realized_succ hη)] at hmono₁
    have hmono₂ : clock Gs Y w E₁ E₂ (tau Gs Y w E₂ (succ Gs Y η))
        ≤ clock Gs Y w E₁ E₂ (clock Gs Y w E₂ E₁ y) := clock_mono hmono₁
    rw [clock_tau hcd hd₁ hd₂ (hcd.realized_succ hη)] at hmono₂
    exact absurd (hmono₂.trans_lt (h1.trans hρsucc)) (lt_irrefl _)

/-! ## The homeomorphism -/

theorem coe_timeChange (hcd : ChainData Gs Y w) (hd₁ : ClockData Gs Y w E₁)
    (hd₂ : ClockData Gs Y w E₂) (t : ℝ≥0) :
    (timeChange Gs Y w E₁ E₂ t : ℝ≥0∞) = clock Gs Y w E₁ E₂ (t : ℝ≥0∞) :=
  ENNReal.coe_toNNReal (clock_ne_top hcd hd₁ hd₂ ENNReal.coe_ne_top)

theorem strictMono_timeChange (hcd : ChainData Gs Y w) (hd₁ : ClockData Gs Y w E₁)
    (hd₂ : ClockData Gs Y w E₂) : StrictMono (timeChange Gs Y w E₁ E₂) := by
  intro s t hst
  rw [← ENNReal.coe_lt_coe, coe_timeChange hcd hd₁ hd₂, coe_timeChange hcd hd₁ hd₂]
  exact clock_strictMono hcd hd₁ hd₂ (by exact_mod_cast hst) ENNReal.coe_ne_top

theorem timeChange_timeChange (hcd : ChainData Gs Y w) (hd₁ : ClockData Gs Y w E₁)
    (hd₂ : ClockData Gs Y w E₂) (y : ℝ≥0) :
    timeChange Gs Y w E₁ E₂ (timeChange Gs Y w E₂ E₁ y) = y := by
  rw [← ENNReal.coe_inj, coe_timeChange hcd hd₁ hd₂, coe_timeChange hcd hd₂ hd₁]
  exact clock_clock hcd hd₁ hd₂ ENNReal.coe_ne_top

theorem surjective_timeChange (hcd : ChainData Gs Y w) (hd₁ : ClockData Gs Y w E₁)
    (hd₂ : ClockData Gs Y w E₂) : Function.Surjective (timeChange Gs Y w E₁ E₂) :=
  fun y => ⟨timeChange Gs Y w E₂ E₁ y, timeChange_timeChange hcd hd₁ hd₂ y⟩

theorem timeChange_zero (hcd : ChainData Gs Y w) (hd₁ : ClockData Gs Y w E₁)
    (hd₂ : ClockData Gs Y w E₂) : timeChange Gs Y w E₁ E₂ 0 = 0 := by
  have hcl : clock Gs Y w E₁ E₂ (tau Gs Y w E₂ 0) = 0 := by
    rw [clock_tau hcd hd₁ hd₂ (realized_zero Gs Y), PathProperties.tau_zero]
  have h0 : ((0 : ℝ≥0) : ℝ≥0∞) = tau Gs Y w E₂ 0 := by
    rw [PathProperties.tau_zero, ENNReal.coe_zero]
  show (clock Gs Y w E₁ E₂ ((0 : ℝ≥0) : ℝ≥0∞)).toNNReal = 0
  rw [h0, hcl, ENNReal.toNNReal_zero]

/-- **The main pathwise identity.**  The `E₂`-process read at time `t` is the
`E₁`-process read at the time-changed time — at *every* time, including the times
lying in no holding interval, where both are `∞`. -/
theorem X_eq_X_timeChange (hcd : ChainData Gs Y w) (hd₁ : ClockData Gs Y w E₁)
    (hd₂ : ClockData Gs Y w E₂) (t : ℝ≥0) :
    X Gs Y w E₂ t = X Gs Y w E₁ (timeChange Gs Y w E₁ E₂ t) := by
  by_cases hex : ∃ η, InInterval Gs Y w E₂ η (t : ℝ≥0∞)
  · obtain ⟨η, hI⟩ := hex
    have hIz : InInterval Gs Y w E₁ η (clock Gs Y w E₁ E₂ (t : ℝ≥0∞)) :=
      clock_mem_interval hcd hd₁ hd₂ hI
    have hIz' : InInterval Gs Y w E₁ η ((timeChange Gs Y w E₁ E₂ t : ℝ≥0) : ℝ≥0∞) := by
      rw [coe_timeChange hcd hd₁ hd₂]
      exact hIz
    rw [hcd.consistent.X_eq_of_inInterval Gs Y w E₂ hcd.monotone hcd.cover hI,
      hcd.consistent.X_eq_of_inInterval Gs Y w E₁ hcd.monotone hcd.cover hIz']
  · have hex' : ∀ η, ¬ InInterval Gs Y w E₂ η (t : ℝ≥0∞) := not_exists.1 hex
    have hgap := clock_notMem hcd hd₁ hd₂ (t := (t : ℝ≥0∞)) ENNReal.coe_ne_top hex'
    have hgap' : ¬ ∃ η, InInterval Gs Y w E₁ η
        ((timeChange Gs Y w E₁ E₂ t : ℝ≥0) : ℝ≥0∞) := by
      refine not_exists.2 fun η => ?_
      rw [coe_timeChange hcd hd₁ hd₂]
      exact hgap η
    rw [(X_eq_none_iff Gs Y w E₂ t).2 hex,
      (X_eq_none_iff Gs Y w E₁ (timeChange Gs Y w E₁ E₂ t)).2 hgap']

/-- **Two holding families on one chain give a homeomorphic time change.** -/
theorem isHomeomorphicTimeChange_X (hcd : ChainData Gs Y w) (hd₁ : ClockData Gs Y w E₁)
    (hd₂ : ClockData Gs Y w E₂) :
    AreaClocks.IsHomeomorphicTimeChange (X Gs Y w E₂) (X Gs Y w E₁) := by
  have hsm := strictMono_timeChange hcd hd₁ hd₂
  have hsurj := surjective_timeChange hcd hd₁ hd₂
  refine ⟨(hsm.orderIsoOfSurjective (timeChange Gs Y w E₁ E₂) hsurj).toHomeomorph,
    ?_, ?_, fun t => ?_⟩
  · simp only [OrderIso.coe_toHomeomorph, StrictMono.coe_orderIsoOfSurjective]
    exact hsm
  · simp only [OrderIso.coe_toHomeomorph, StrictMono.coe_orderIsoOfSurjective]
    exact timeChange_zero hcd hd₁ hd₂
  · simp only [OrderIso.coe_toHomeomorph, StrictMono.coe_orderIsoOfSurjective]
    exact X_eq_X_timeChange hcd hd₁ hd₂ t

end ReflectedGMS.HoldingTimeChange
