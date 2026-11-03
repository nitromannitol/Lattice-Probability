/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.Lift at commit 31e7483; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Blueprint.M2Defs
import LatticeProb.Bonanno.QuantumZipper.Proofs.Complex.TopoDegree

/-!
# Log-cover lifts: positive Jordan lifts, angle lifts, `WeaklyRightOf` (DEC-D (a), D-D1)

Decision D-D1 (`decisions/DEC-D.md` (a)) defines leftmost geodesics literally, following
Miller–Sheffield, *An axiomatic characterization of the Brownian map*, arXiv:1506.03806,
Prop. 2.2 (`mapmaking_final.tex` l. 619: "furthest counterclockwise when lifted … to the universal
cover"), through lifts by `w ↦ z + e^w`. The current `Blueprint/CONFDefs.lean` still carries the
older one-sided-limit reading, so DEC-D's definitions (exact shapes of DEC-D (a), (b)) live here in
the sub-namespace `LQGMetric.CONF.DD`, with the same names. They are *not* equivalent to the
Blueprint ones (DEC-D (a), finding 1); the Blueprint edit is the orchestrator's.

This file: the definitions, and the elementary lift facts used by all CONF §2 nodes:
existence of angle lifts of a path avoiding `z` (via `exists_lift_exp`, QuantumZipper
`Proofs/Complex/TopoDegree.lean`), uniqueness up to `2πℤ` and on intervals, integer-period shifts
of positive Jordan lifts, and existence/uniqueness of positions on a lifted Jordan curve.
Own elementary proofs (standard covering-space facts; no published proof needed).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set

namespace LQGMetric.CONF.DD

open LQGMetric.Blueprint

/-! ## DEC-D definitions -/

/-- `(φ, θ)` is a positive Jordan lift of `Γ` around `z` (DEC-D (a)) -/
def IsPosJordanLift (Γ : Set ℂ) (z : ℂ) (φ : ℝ → ℂ) (θ : ℝ → ℝ) : Prop :=
  Continuous φ ∧ (∀ t, φ (t + 2 * Real.pi) = φ t) ∧ InjOn φ (Ico 0 (2 * Real.pi)) ∧
    range φ = Γ ∧ Continuous θ ∧ (∀ t, θ (t + 2 * Real.pi) = θ t + 2 * Real.pi) ∧
      ∀ t, φ t - z = (‖φ t - z‖ : ℂ) * Complex.exp ((θ t : ℂ) * Complex.I)

/-- a positively oriented Jordan parametrization (DEC-D (a)) -/
def IsPosJordanParam (Γ : Set ℂ) (z : ℂ) (φ : ℝ → ℂ) : Prop := ∃ θ, IsPosJordanLift Γ z φ θ

/-- `α` is a continuous angle lift of `P − z` on `[a, b]` (DEC-D (a)) -/
def IsAngleLift (z : ℂ) (P : ℝ → ℂ) (a b : ℝ) (α : ℝ → ℝ) : Prop :=
  ContinuousOn α (Icc a b) ∧ ∀ u ∈ Icc a b,
    P u - z = (‖P u - z‖ : ℂ) * Complex.exp ((α u : ℂ) * Complex.I)

/-- `Q` lies weakly to the right of `P` (D-D1, DV-CONF-LM1) -/
def WeaklyRightOf (D : ContMetric) (z : ℂ) (s : ℝ) (Q P : ℝ → ℂ) : Prop :=
  ∀ t ∈ Ioo 0 s, ∀ (φ : ℝ → ℂ) (θ : ℝ → ℝ),
    IsPosJordanLift (frontier (filledBall D z t)) z φ θ →
    ∀ α β : ℝ → ℝ, IsAngleLift z P t s α → IsAngleLift z Q t s β → α s = β s →
      ∀ u v : ℝ, φ u = P t → θ u = α t → φ v = Q t → θ v = β t → v ≤ u

/-- leftmost (`left = true`) / rightmost geodesic (D-D1) -/
def IsSideGeod (left : Bool) (D : ContMetric) (z : ℂ) (s : ℝ) (y : ℂ) (P : ℝ → ℂ) : Prop :=
  y ∈ frontier (filledBall D z s) ∧ IsGeodesicL D P s z y ∧
    ∀ Q, IsGeodesicL D Q s z y →
      if left then WeaklyRightOf D z s Q P else WeaklyRightOf D z s P Q

/-- leftmost geodesic (D-D1) -/
def IsLeftmostGeod (D : ContMetric) (z : ℂ) (s : ℝ) (y : ℂ) (P : ℝ → ℂ) : Prop :=
  IsSideGeod true D z s y P

/-- **TOPO-ORD** (D-D2, DV-CONF-AN2; deterministic) -/
def TopoOrd : Prop :=
  ∀ (K₁ K₂ : Set ℂ) (z : ℂ), IsCompact K₁ → IsCompact K₂ → z ∈ interior K₁ →
    K₁ ⊆ interior K₂ → IsConnected K₁ᶜ → IsConnected K₂ᶜ →
    ∀ (φ₁ : ℝ → ℂ) (θ₁ : ℝ → ℝ) (φ₂ : ℝ → ℂ) (θ₂ : ℝ → ℝ),
      IsPosJordanLift (frontier K₁) z φ₁ θ₁ → IsPosJordanLift (frontier K₂) z φ₂ θ₂ →
    ∀ (P Q : ℝ → ℂ) (a b : ℝ) (α β : ℝ → ℝ), a ≤ b →
      ContinuousOn P (Icc a b) → ContinuousOn Q (Icc a b) →
      MapsTo P (Icc a b) (K₂ \ interior K₁) → MapsTo Q (Icc a b) (K₂ \ interior K₁) →
      IsAngleLift z P a b α → IsAngleLift z Q a b β →
    ∀ u₁ u₂ v₁ v₂ : ℝ, φ₁ u₁ = P a → θ₁ u₁ = α a → φ₁ u₂ = Q a → θ₁ u₂ = β a →
      φ₂ v₁ = P b → θ₂ v₁ = α b → φ₂ v₂ = Q b → θ₂ v₂ = β b →
      u₁ < u₂ → v₂ ≤ v₁ → ∃ t ∈ Icc a b, ∃ t' ∈ Icc a b, P t = Q t' ∧ α t = β t'

/-! ## Angles of a nonzero complex number -/

/-- `w = ‖w‖ e^{ia}` -/
def IsAngle (w : ℂ) (a : ℝ) : Prop := w = (‖w‖ : ℂ) * Complex.exp ((a : ℂ) * Complex.I)

/-- two angles of a nonzero number differ by an element of `2πℤ` -/
theorem isAngle_sub {w : ℂ} (hw : w ≠ 0) {a b : ℝ} (ha : IsAngle w a) (hb : IsAngle w b) :
    ∃ n : ℤ, a - b = n * (2 * Real.pi) := by
  have hn : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hw
  have he : Complex.exp ((a : ℂ) * Complex.I) = Complex.exp ((b : ℂ) * Complex.I) :=
    mul_left_cancel₀ hn (ha.symm.trans hb)
  have h1 : Complex.exp (((a - b : ℝ) : ℂ) * Complex.I) = 1 := by
    rw [Complex.ofReal_sub, sub_mul, Complex.exp_sub, he, div_self (Complex.exp_ne_zero _)]
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h1
  refine ⟨n, ?_⟩
  have h3 : (((a - b : ℝ)) : ℂ) = ((n * (2 * Real.pi) : ℝ) : ℂ) := by
    apply mul_right_cancel₀ Complex.I_ne_zero; rw [hn]; push_cast; ring
  exact_mod_cast h3

/-- angles are stable under `2πℤ` shifts -/
theorem isAngle_add_int {w : ℂ} {a : ℝ} (ha : IsAngle w a) (n : ℤ) :
    IsAngle w (a + n * (2 * Real.pi)) := by
  unfold IsAngle at *
  conv_lhs => rw [ha]
  congr 1
  rw [show (((a + n * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) =
    (a : ℂ) * Complex.I + n * (2 * Real.pi * Complex.I) by push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-! ## Angle lifts -/

/-- existence of an angle lift of a path avoiding `z` on `[a, b]` (via QZ `exists_lift_exp`) -/
theorem exists_angleLift {z : ℂ} {P : ℝ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hP : ContinuousOn P (Icc a b)) (hz : ∀ u ∈ Icc a b, P u ≠ z) :
    ∃ α : ℝ → ℝ, IsAngleLift z P a b α := by
  set e : unitInterval → ℝ := fun τ => a + (τ : ℝ) * (b - a) with he
  have heI : ∀ τ, e τ ∈ Icc a b := fun τ => by
    have h0 := τ.2.1; have h1 := τ.2.2
    constructor <;> nlinarith
  have hec : Continuous e := by fun_prop
  let γ : C(unitInterval, ℂ) :=
    ⟨fun τ => P (e τ) - z, (hP.comp_continuous hec heI).sub continuous_const⟩
  obtain ⟨L, hL⟩ := QuantumZipper.CA.Topo.exists_lift_exp γ
    (fun τ => sub_ne_zero.2 (hz _ (heI τ)))
  set g : ℝ → unitInterval := fun u => projIcc 0 1 zero_le_one ((u - a) / (b - a))
  have hgc : Continuous g := continuous_projIcc.comp (by fun_prop)
  refine ⟨fun u => (L (g u)).im, (Complex.continuous_im.comp (L.2.comp hgc)).continuousOn,
    fun u hu => ?_⟩
  have heg : e (g u) = u := by
    rcases hab.lt_or_eq with hlt | heq
    · have h01 : (u - a) / (b - a) ∈ Icc (0 : ℝ) 1 := by
        constructor
        · exact div_nonneg (by linarith [hu.1]) (by linarith)
        · rw [div_le_one (by linarith)]; linarith [hu.2]
      simp only [he, g, projIcc_of_mem _ h01]
      field_simp
      ring
    · have : u = a := le_antisymm (heq ▸ hu.2) hu.1
      simp only [he]; rw [← heq, sub_self, mul_zero, add_zero, this]
  have h := hL (g u)
  simp only [γ, ContinuousMap.coe_mk, heg] at h
  rw [← h, Complex.norm_exp, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp

/-- two angle lifts of a path avoiding `z` on `[a, b]` that agree at one point agree on `[a, b]` -/
theorem angleLift_eqOn {z : ℂ} {P : ℝ → ℂ} {a b : ℝ} {α β : ℝ → ℝ}
    (hα : IsAngleLift z P a b α) (hβ : IsAngleLift z P a b β) (hz : ∀ u ∈ Icc a b, P u ≠ z)
    {c : ℝ} (hc : c ∈ Icc a b) (hαβ : α c = β c) : EqOn α β (Icc a b) := by
  have h2 : (2 * Real.pi) ≠ 0 := by positivity
  have hmaps : MapsTo (fun u => (α u - β u) / (2 * Real.pi)) (Icc a b)
      (range ((↑) : ℤ → ℝ)) := by
    intro u hu
    obtain ⟨n, hn⟩ := isAngle_sub (sub_ne_zero.2 (hz u hu)) (hα.2 u hu) (hβ.2 u hu)
    exact ⟨n, by simp only [hn, mul_div_cancel_right₀ _ h2]⟩
  intro u hu
  have hcon : (α u - β u) / (2 * Real.pi) = (α c - β c) / (2 * Real.pi) :=
    isPreconnected_Icc.constant_of_mapsTo
      Int.isClosedEmbedding_coe_real.isInducing.isDiscrete_range
      ((hα.1.sub hβ.1).div_const _) hmaps hu hc
  rw [hαβ, sub_self, zero_div, div_eq_zero_iff] at hcon
  rcases hcon with h | h
  · linarith
  · exact absurd h h2

/-- restriction of an angle lift to a subinterval -/
theorem IsAngleLift.mono {z : ℂ} {P : ℝ → ℂ} {a b c d : ℝ} {α : ℝ → ℝ}
    (hα : IsAngleLift z P a b α) (hsub : Icc c d ⊆ Icc a b) : IsAngleLift z P c d α :=
  ⟨hα.1.mono hsub, fun u hu => hα.2 u (hsub hu)⟩

/-- shifting an angle lift by `2πn` -/
theorem IsAngleLift.add_int {z : ℂ} {P : ℝ → ℂ} {a b : ℝ} {α : ℝ → ℝ}
    (hα : IsAngleLift z P a b α) (n : ℤ) :
    IsAngleLift z P a b (fun u => α u + n * (2 * Real.pi)) :=
  ⟨hα.1.add continuousOn_const, fun u hu => isAngle_add_int (hα.2 u hu) n⟩

/-- gluing two continuous functions on `[a, b]` and `[b, c]` -/
theorem continuousOn_glue {f g : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c)
    (hf : ContinuousOn f (Icc a b)) (hg : ContinuousOn g (Icc b c)) (hfg : f b = g b) :
    ContinuousOn (fun u => if u ≤ b then f u else g u) (Icc a c) := by
  rw [← Icc_union_Icc_eq_Icc hab hbc]
  refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Icc
  · exact hf.congr fun u hu => by rw [if_pos hu.2]
  · refine hg.congr fun u hu => ?_
    by_cases h : u ≤ b
    · rw [if_pos h, le_antisymm h hu.1, hfg]
    · rw [if_neg h]

/-! ## Positive Jordan lifts: integer periods and positions -/

section Pos
variable {Γ : Set ℂ} {z : ℂ} {φ : ℝ → ℂ} {θ : ℝ → ℝ}

theorem IsPosJordanLift.phi_add_int (h : IsPosJordanLift Γ z φ θ) (t : ℝ) (n : ℤ) :
    φ (t + n * (2 * Real.pi)) = φ t := by
  induction n using Int.induction_on generalizing t with
  | zero => simp
  | succ k ih => rw [← ih t]; push_cast; rw [add_one_mul, ← add_assoc, h.2.1]
  | pred k ih =>
    rw [← ih t]; push_cast
    have := h.2.1 (t + (-(k : ℝ) - 1) * (2 * Real.pi))
    rw [← this]; congr 1; ring

theorem IsPosJordanLift.theta_add_int (h : IsPosJordanLift Γ z φ θ) (t : ℝ) (n : ℤ) :
    θ (t + n * (2 * Real.pi)) = θ t + n * (2 * Real.pi) := by
  induction n using Int.induction_on generalizing t with
  | zero => simp
  | succ k ih =>
    push_cast
    rw [add_one_mul, ← add_assoc, h.2.2.2.2.2.1]
    have := ih t; push_cast at this; rw [this]; ring
  | pred k ih =>
    push_cast
    have h1 := h.2.2.2.2.2.1 (t + (-(k : ℝ) - 1) * (2 * Real.pi))
    have h2 := ih t; push_cast at h2
    rw [show t + (-(k : ℝ) - 1) * (2 * Real.pi) + 2 * Real.pi = t + -(k : ℝ) * (2 * Real.pi) by
      ring, h2] at h1
    linarith

/-- a point of `Γ ∖ {z}` with a prescribed angle has a position on the lifted curve -/
theorem IsPosJordanLift.exists_pos (h : IsPosJordanLift Γ z φ θ) {p : ℂ} (hp : p ∈ Γ)
    (hpz : p ≠ z) {a : ℝ} (ha : IsAngle (p - z) a) : ∃ u, φ u = p ∧ θ u = a := by
  rw [← h.2.2.2.1] at hp
  obtain ⟨u₀, rfl⟩ := hp
  obtain ⟨n, hn⟩ := isAngle_sub (sub_ne_zero.2 hpz) ha (h.2.2.2.2.2.2 u₀)
  exact ⟨u₀ + n * (2 * Real.pi), h.phi_add_int u₀ n, by rw [h.theta_add_int]; linarith⟩

/-- positions are unique: `φ u = φ v` and `θ u = θ v` force `u = v` -/
theorem IsPosJordanLift.pos_unique (h : IsPosJordanLift Γ z φ θ) {u v : ℝ} (hφ : φ u = φ v)
    (hθ : θ u = θ v) : u = v := by
  have h2 : (0 : ℝ) < 2 * Real.pi := by positivity
  set m := ⌊u / (2 * Real.pi)⌋
  set n := ⌊v / (2 * Real.pi)⌋
  have hred : ∀ x : ℝ, x - ⌊x / (2 * Real.pi)⌋ * (2 * Real.pi) ∈ Ico 0 (2 * Real.pi) := by
    intro x
    have h1 := Int.floor_le (x / (2 * Real.pi))
    have h3 := Int.lt_floor_add_one (x / (2 * Real.pi))
    rw [le_div_iff₀ h2] at h1
    rw [div_lt_iff₀ h2] at h3
    constructor <;> nlinarith
  have hu' := h.phi_add_int (u - m * (2 * Real.pi)) m
  have hv' := h.phi_add_int (v - n * (2 * Real.pi)) n
  simp only [sub_add_cancel] at hu' hv'
  have heq : u - m * (2 * Real.pi) = v - n * (2 * Real.pi) :=
    h.2.2.1 (hred u) (hred v) (by
      show φ (u - m * (2 * Real.pi)) = φ (v - n * (2 * Real.pi))
      rw [← hu', ← hv', hφ])
  have hθu := h.theta_add_int (u - m * (2 * Real.pi)) m
  have hθv := h.theta_add_int (v - n * (2 * Real.pi)) n
  simp only [sub_add_cancel] at hθu hθv
  rw [heq] at hθu
  have hmn : (m : ℝ) * (2 * Real.pi) = n * (2 * Real.pi) := by linarith
  linarith

end Pos

end LQGMetric.CONF.DD
