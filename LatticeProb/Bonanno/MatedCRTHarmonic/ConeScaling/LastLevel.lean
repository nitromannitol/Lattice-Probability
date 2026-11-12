/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module MatedCRTHarmonic.ConeScaling.LastLevel at commit fdb5cad; only the module paths of local imports are changed.
   Declarations, examples and checks that the copied results do not use are omitted. -/
import LatticeProb.Bonanno.MatedCRTHarmonic.CellScaling.ConeDefs
import LatticeProb.Bonanno.QuantumZipper.Proofs.LQG.WedgeMeasurable
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-!
# The last-level time and the radial re-centring map of the quantum cone

Deterministic layer of DMS Proposition 4.13(i). For a continuous path `w : ℝ → ℝ`
(with `CellScaling.coneRadial` parametrized by `w t = h_{e^{-t}}(0)`, so that
`Y_w(s) := w(−s) + Q s` is `h_{e^s}(0) + Q s`, i.e. `CellScaling.coneLogRadial`):

* `lastLevel Q y w = sup {s | w(−s) + Q s = y}`: the logarithm of the cone scale `R_b`
  (`CellScaling.coneScale`) at `y = γ⁻¹ log b`;
* `radShift Q y w t = w(t − L) + Q L − y` with `L = lastLevel Q y w`: the radial part of
  `h_b = h(R_b ·) + Q log R_b − γ⁻¹ log b`, so `Y_{radShift w}(s) = Y_w(L + s) − y`.

Proved here: measurability of `lastLevel` and `radShift` on `C(ℝ, ℝ)` (via a two-sided version
of QuantumZipper's `WedgeMeas.measurable_lastZero`: `measurable_sSup_zeroSet`), and the
deterministic identities used for the law when `y > 0`: on "good"
paths (`Y_w(0) = 0`, `Y_w > 0` on `(0, ∞)`) `radShift Q 0 w = w`
(`radShift_zero_of_good`), and `radShift Q y (radShift Q (−y) w) = w` for every `y`
(`radShift_radShift_neg`). Own elementary arguments.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace MatedCRTHarmonic.ConeScaling

open QuantumZipper.WedgeMeas

/-! ### Measurability of the supremum of the zero set of a continuous family -/

/-- The zero set has an element `> c` iff it has one in a compact window `[c + 1/(n+1), …]`. -/
theorem exists_zero_gt_iff_zeroIn (g : ℝ → ℝ) (c : ℝ) :
    (∃ s ∈ {s | g s = 0}, c < s) ↔
      ∃ n : ℕ, ZeroIn g (c + 1 / ((n : ℝ) + 1)) (c + 1 / ((n : ℝ) + 1) + n + 1) := by
  constructor
  · rintro ⟨s, hs0, hcs⟩
    obtain ⟨n1, hn1⟩ := exists_nat_one_div_lt (sub_pos.2 hcs)
    obtain ⟨n2, hn2⟩ := exists_nat_ge (s - c)
    refine ⟨max n1 n2, s, ⟨?_, ?_⟩, hs0⟩
    · have h0 : (n1 : ℝ) ≤ (max n1 n2 : ℕ) := by exact_mod_cast le_max_left n1 n2
      have : 1 / ((max n1 n2 : ℕ) + 1 : ℝ) ≤ 1 / ((n1 : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      linarith
    · have h1 : (n2 : ℝ) ≤ (max n1 n2 : ℕ) := by exact_mod_cast le_max_right n1 n2
      have : (0 : ℝ) < 1 / ((max n1 n2 : ℕ) + 1 : ℝ) := by positivity
      linarith
  · rintro ⟨n, s, ⟨hs1, -⟩, hs0⟩
    have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    exact ⟨s, hs0, by linarith⟩

/-- The (two-sided) zero set is nonempty iff it meets some `[−(N+1), N+1]`. -/
theorem zeroSet_nonempty_iff (g : ℝ → ℝ) :
    ({s | g s = 0} : Set ℝ).Nonempty ↔ ∃ N : ℕ, ZeroIn g (-((N : ℝ) + 1)) ((N : ℝ) + 1) := by
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨N, hN⟩ := exists_nat_ge |s|
    refine ⟨N, s, ⟨?_, ?_⟩, hs⟩
    · have := neg_abs_le s; linarith
    · have := le_abs_self s; linarith
  · rintro ⟨N, s, -, hs⟩
    exact ⟨s, hs⟩

/-- The (two-sided) zero set is bounded above iff it misses every `[N, N + n + 1]` for some `N`. -/
theorem zeroSet_bddAbove_iff (g : ℝ → ℝ) :
    BddAbove ({s | g s = 0} : Set ℝ) ↔ ∃ N : ℕ, ∀ n : ℕ, ¬ ZeroIn g N (N + n + 1) := by
  constructor
  · rintro ⟨M, hM⟩
    refine ⟨⌈M⌉₊ + 1, fun n => ?_⟩
    rintro ⟨s, ⟨hs1, -⟩, hs0⟩
    have h1 := hM hs0
    have h2 := Nat.le_ceil M
    push_cast at hs1
    linarith
  · rintro ⟨N, hN⟩
    refine ⟨N, fun s hs => ?_⟩
    by_contra h
    push Not at h
    obtain ⟨n, hn⟩ := exists_nat_ge (s - N)
    exact hN n ⟨s, ⟨h.le, by linarith⟩, hs⟩

/-- `c < sSup Z` in terms of countably many window conditions (with `Real.sSup`'s junk value `0`). -/
theorem lt_sSup_zeroSet_iff (g : ℝ → ℝ) (c : ℝ) :
    c < sSup ({s | g s = 0} : Set ℝ) ↔
      (({s | g s = 0} : Set ℝ).Nonempty ∧ BddAbove ({s | g s = 0} : Set ℝ) ∧
          ∃ s ∈ {s | g s = 0}, c < s) ∨
        ((¬ ({s | g s = 0} : Set ℝ).Nonempty ∨ ¬ BddAbove ({s | g s = 0} : Set ℝ)) ∧ c < 0) := by
  set Z : Set ℝ := {s | g s = 0}
  by_cases hne : Z.Nonempty
  · by_cases hb : BddAbove Z
    · rw [lt_csSup_iff hb hne]
      simp only [hne, hb, true_and, not_true_eq_false, false_and, or_false]
    · rw [Real.sSup_of_not_bddAbove hb]
      simp only [hb, false_and, and_false, false_or, not_false_eq_true, or_true, true_and]
  · rw [not_nonempty_iff_eq_empty.1 hne, Real.sSup_empty]
    simp

/-- **Measurability of the last zero of a continuous family** (two-sided version of QuantumZipper's
`WedgeMeas.measurable_lastZero`): if every `f ω` is continuous and every `ω ↦ f ω s` is measurable,
then `ω ↦ sSup {s | f ω s = 0}` is measurable. -/
theorem measurable_sSup_zeroSet {Ω : Type*} [MeasurableSpace Ω] {f : Ω → ℝ → ℝ}
    (hc : ∀ ω, Continuous (f ω)) (hm : ∀ s, Measurable fun ω => f ω s) :
    Measurable fun ω => sSup ({s | f ω s = 0} : Set ℝ) := by
  refine measurable_of_Ioi fun c => ?_
  have hne : MeasurableSet {ω | ({s | f ω s = 0} : Set ℝ).Nonempty} := by
    simp_rw [zeroSet_nonempty_iff]
    exact measurableSet_setOfPred.2 (Measurable.exists fun N =>
      measurable_zeroIn hc hm (by linarith))
  have hbdd : MeasurableSet {ω | BddAbove ({s | f ω s = 0} : Set ℝ)} := by
    simp_rw [zeroSet_bddAbove_iff]
    exact measurableSet_setOfPred.2 (Measurable.exists fun N => Measurable.forall fun n =>
      (measurable_zeroIn hc hm (by linarith)).not)
  have hgt : MeasurableSet {ω | ∃ s ∈ ({s | f ω s = 0} : Set ℝ), c < s} := by
    simp_rw [exists_zero_gt_iff_zeroIn]
    exact measurableSet_setOfPred.2 (Measurable.exists fun n =>
      measurable_zeroIn hc hm (by linarith))
  have e : (fun ω => sSup ({s | f ω s = 0} : Set ℝ)) ⁻¹' Ioi c =
      ({ω | ({s | f ω s = 0} : Set ℝ).Nonempty} ∩
          {ω | BddAbove ({s | f ω s = 0} : Set ℝ)} ∩
          {ω | ∃ s ∈ ({s | f ω s = 0} : Set ℝ), c < s}) ∪
        (({ω | ({s | f ω s = 0} : Set ℝ).Nonempty}ᶜ ∪
            {ω | BddAbove ({s | f ω s = 0} : Set ℝ)}ᶜ) ∩ {_ω | c < 0}) := by
    ext ω
    simp only [mem_preimage, mem_Ioi, lt_sSup_zeroSet_iff, mem_union, mem_inter_iff,
      mem_ofPred_eq, mem_compl_iff, and_assoc]
  rw [e]
  exact ((hne.inter hbdd).inter hgt).union
    ((hne.compl.union hbdd.compl).inter (MeasurableSet.const _))

/-! ### The last-level time and the radial re-centring map -/

/-- `L_y(w) = sup {s | w(−s) + Q s = y}` ( with `w = coneRadial`, `y = γ⁻¹ log b`). -/
def lastLevel (Q y : ℝ) (w : C(ℝ, ℝ)) : ℝ := sSup {s : ℝ | w (-s) + Q * s = y}

/-- The radial re-centring `t ↦ w(t − L) + Q L − y`, `L = lastLevel Q y w`. -/
def radShift (Q y : ℝ) (w : C(ℝ, ℝ)) : C(ℝ, ℝ) :=
  ⟨fun t => w (t - lastLevel Q y w) + Q * lastLevel Q y w - y, by fun_prop⟩

@[simp] lemma radShift_apply (Q y : ℝ) (w : C(ℝ, ℝ)) (t : ℝ) :
    radShift Q y w t = w (t - lastLevel Q y w) + Q * lastLevel Q y w - y := rfl

theorem measurable_lastLevel (Q y : ℝ) : Measurable (lastLevel Q y) := by
  have e : lastLevel Q y = fun w : C(ℝ, ℝ) => sSup {s : ℝ | (w (-s) + Q * s - y) = 0} := by
    funext w
    simp only [lastLevel, sub_eq_zero]
  rw [e]
  refine measurable_sSup_zeroSet (f := fun (w : C(ℝ, ℝ)) (s : ℝ) => w (-s) + Q * s - y)
    (fun w => by fun_prop) fun s => ?_
  exact ((ContinuousMap.measurable_eval (-s)).add_const _).sub_const _

theorem measurable_radShift (Q y : ℝ) : Measurable (radShift Q y) := by
  refine ContinuousMap.measurable_iff_eval.2 fun t => ?_
  have hev : Measurable fun p : C(ℝ, ℝ) × ℝ => p.1 p.2 := continuous_eval.measurable
  have hL := measurable_lastLevel Q y
  exact ((hev.comp (measurable_id.prodMk (measurable_const.sub hL))).add
    (hL.const_mul Q)).sub_const y

/-! ### Deterministic identities on good paths -/

/-- A path is **good** for the cone: `Y_w(0) = 0` and `Y_w(s) > 0` for `s > 0`, where
`Y_w(s) = w(−s) + Q s` (DMS Rem 4.4: after its last zero the radial process stays positive). -/
def IsGoodRadial (Q : ℝ) (w : C(ℝ, ℝ)) : Prop :=
  w 0 = 0 ∧ ∀ s : ℝ, 0 < s → 0 < w (-s) + Q * s

/-- On a good path the zero level is last attained at `0`. -/
theorem isGreatest_zeroLevel {Q : ℝ} {w : C(ℝ, ℝ)} (hw : IsGoodRadial Q w) :
    IsGreatest {s : ℝ | w (-s) + Q * s = 0} 0 := by
  refine ⟨by simp [hw.1], fun s hs => ?_⟩
  by_contra h
  push Not at h
  have := hw.2 s h
  rw [show w (-s) + Q * s = 0 from hs] at this
  exact lt_irrefl _ this

theorem lastLevel_zero_of_good {Q : ℝ} {w : C(ℝ, ℝ)} (hw : IsGoodRadial Q w) :
    lastLevel Q 0 w = 0 :=
  (isGreatest_zeroLevel hw).csSup_eq

/-- `R_1 = 1`: on a good path the re-centring at level `0` is the identity. -/
theorem radShift_zero_of_good {Q : ℝ} {w : C(ℝ, ℝ)} (hw : IsGoodRadial Q w) :
    radShift Q 0 w = w := by
  ext t
  simp [lastLevel_zero_of_good hw]

/-- **The involution**: on a good path, re-centring at `−y`
and then at `y` gives back the path (whatever the value of `L_{−y}`: the zero level of the shifted
path is last attained at `−L_{−y}`). -/
theorem radShift_radShift_neg (Q y : ℝ) {w : C(ℝ, ℝ)} (hw : IsGoodRadial Q w) :
    radShift Q y (radShift Q (-y) w) = w := by
  set ℓ := lastLevel Q (-y) w with hℓ
  have hY : ∀ s, radShift Q (-y) w (-s) + Q * s = (w (-(s + ℓ)) + Q * (s + ℓ)) + y := by
    intro s
    simp only [radShift_apply, ← hℓ]
    ring_nf
  have hL : lastLevel Q y (radShift Q (-y) w) = -ℓ := by
    unfold lastLevel
    refine IsGreatest.csSup_eq ⟨?_, fun s hs => ?_⟩
    · show radShift Q (-y) w (-(-ℓ)) + Q * (-ℓ) = y
      rw [hY]
      simp [hw.1]
    · have hs' : w (-(s + ℓ)) + Q * (s + ℓ) = 0 := by
        have : radShift Q (-y) w (-s) + Q * s = y := hs
        rw [hY] at this
        linarith
      have := (isGreatest_zeroLevel hw).2 hs'
      linarith
  ext t
  rw [radShift_apply, hL, radShift_apply, ← hℓ]
  ring_nf

end MatedCRTHarmonic.ConeScaling
