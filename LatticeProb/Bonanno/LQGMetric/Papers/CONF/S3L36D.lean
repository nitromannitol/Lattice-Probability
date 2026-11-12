/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3L36D at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.CONF.S3L36C

/-!
# CONF Lemma 3.6, Step 1 objects and property A

Gwynne–Miller, *Confluence of geodesics in LQG*, arXiv:1905.00381 (CONF),
`literature/src/1905.00381/confluence-final.tex`, Lemma 3.6 (C:1308–1448), decision D108.

Step 1 (C:1339–1361):
* `conf36Grid m x` : the grid point `z ∈ mℤ²` with `x − z ∈ [0,m)²` (C:1341: "`z ∈ (ε𝕣/4)ℤ²`
  with `B_{ε𝕣}(x) ⊆ B_{2ε𝕣}(z)`"; here `|x − z| < 2m = ε𝕣/2`);
* `conf36T δ r z B` : the squares of `𝒮^z_{δr}(𝔸_{3r,4r}(z))` meeting `B`, so that
  `Ũ^r = confU r δ z (conf36T δ r z 𝓑^•_τ)` (CONF (3.18), C:1344);
* `conf36Rho` : the radii `ρ̃^n` (CONF (3.19), C:1350), with random base radius `e = ε𝕣`
  and random centre `z`;
* `conf36Gt`, `conf36G` : the events `G̃^n` (CONF (3.22), C:1414, with the event (3.9′) of D108 (b)
  in place of the diameter event, and the a.s. event `conf36Conn` that `𝓑^•_τ` meets
  `𝔸_{3r,4r}(z)` or lies in `cl B_{3r}(z)`, see below) and `G^ε_x = ⋃_{n ≤ ⌊η log ε⁻¹⌋} G̃^n`
  (CONF (3.20), C:1362).

Property A (Step 2, C:1388–1410): `conf36_propA`, from `conf36_propA_core` (S3L36C), the comparison
`ρ̃^n ≤ ρ^n_{ε𝕣}(z)` (CONF (3.21) first display, C:1352–1355; `conf36Rho_le_confRho`) and the
definition of `R^ε_𝕣(𝓑^•_τ)`.

`conf36Conn` is a deviation: CONF uses (C:1393) that `𝔸_{3ρ̃,4ρ̃}(z)` meets `𝓑^•_τ`, which needs
`𝓑^•_τ` connected; this holds when `D_h` is a length metric (a.s., Axiom I), not surely, and
property A is a sure statement. Adding the a.s. event to `G̃^n` does not change the conditional
probabilities in property B.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace LQGMetric.CONF

open Blueprint

/-! ## Deterministic objects -/

/-- the grid point `⌊x/m⌋ m` of `mℤ²` -/
def conf36Grid (m : ℝ) (x : ℂ) : ℂ := ⟨⌊x.re / m⌋ * m, ⌊x.im / m⌋ * m⟩

theorem conf36Grid_mem (m : ℝ) (x : ℂ) : conf36Grid m x ∈ gridPts m :=
  ⟨⌊x.re / m⌋, ⌊x.im / m⌋, rfl⟩

theorem conf36Grid_norm_lt {m : ℝ} (hm : 0 < m) (x : ℂ) : ‖x - conf36Grid m x‖ < 2 * m := by
  have a1 := Int.floor_le (x.re / m)
  have a2 := Int.lt_floor_add_one (x.re / m)
  have b1 := Int.floor_le (x.im / m)
  have b2 := Int.lt_floor_add_one (x.im / m)
  rw [le_div_iff₀ hm] at a1 b1
  rw [div_lt_iff₀ hm] at a2 b2
  have hre : |(x - conf36Grid m x).re| < m := by
    simp only [Complex.sub_re, conf36Grid]; rw [abs_lt]; constructor <;> linarith
  have him : |(x - conf36Grid m x).im| < m := by
    simp only [Complex.sub_im, conf36Grid]; rw [abs_lt]; constructor <;> linarith
  linarith [Complex.norm_le_abs_re_add_abs_im (x - conf36Grid m x)]

/-- a finite box containing all indices of `𝒮^z_{δr}(𝔸_{3r,4r}(z))` (as `sqBox` of
`S3L35B4`) -/
def conf36Box (δ : ℝ) : Finset (ℤ × ℤ) :=
  Finset.Icc (-⌈4 / δ⌉ - 1) ⌈4 / δ⌉ ×ˢ Finset.Icc (-⌈4 / δ⌉ - 1) ⌈4 / δ⌉

theorem conf36_int_mem_box {δ r x : ℝ} (hδ : 0 < δ) (hr : 0 < r) {k : ℤ} (hx : |x| < 4 * r)
    (h1 : k * (δ * r) ≤ x) (h2 : x ≤ (k + 1) * (δ * r)) :
    k ∈ Finset.Icc (-⌈4 / δ⌉ - 1) ⌈4 / δ⌉ := by
  rw [abs_lt] at hx
  have hc := Int.le_ceil (4 / δ)
  have hk1 : (k : ℝ) * δ < 4 := by nlinarith
  have hk2 : -4 < ((k : ℝ) + 1) * δ := by nlinarith
  have e1 : (k : ℝ) < 4 / δ := by rw [lt_div_iff₀ hδ]; linarith
  have e2 : -(4 / δ) < (k : ℝ) + 1 := by
    have e : -(4 / δ) = (-4) / δ := by ring
    rw [e, div_lt_iff₀ hδ]; linarith
  rw [Finset.mem_Icc]
  constructor
  · have : ((-⌈4 / δ⌉ - 1 : ℤ) : ℝ) < k + 1 := by push_cast; linarith
    have : (-⌈4 / δ⌉ - 1 : ℤ) < k + 1 := by exact_mod_cast this
    omega
  · have : (k : ℝ) < ⌈4 / δ⌉ := by linarith
    have : k < ⌈4 / δ⌉ := by exact_mod_cast this
    omega

theorem conf36_mem_box {δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r) (z : ℂ) {k : ℤ × ℤ}
    (hk : k ∈ confSqIdx (δ * r) z (annulus z (3 * r) (4 * r))) : k ∈ conf36Box δ := by
  obtain ⟨w, ⟨h1, h2, h3, h4⟩, -, hw⟩ := hk
  have hre : |w.re - z.re| < 4 * r :=
    lt_of_le_of_lt (by rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _) hw
  have him : |w.im - z.im| < 4 * r :=
    lt_of_le_of_lt (by rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _) hw
  exact Finset.mem_product.2 ⟨conf36_int_mem_box hδ hr hre (by linarith) (by linarith),
    conf36_int_mem_box hδ hr him (by linarith) (by linarith)⟩

section ClassicalT
open Classical

/-- the squares of `𝒮^z_{δr}(𝔸_{3r,4r}(z))` meeting `B` (CONF (3.18)) -/
def conf36T (δ r : ℝ) (z : ℂ) (B : Set ℂ) : Finset (ℤ × ℤ) :=
  (conf36Box δ).filter fun k =>
    k ∈ confSqIdx (δ * r) z (annulus z (3 * r) (4 * r)) ∧ (confSq (δ * r) z k ∩ B).Nonempty

theorem conf36T_sub {δ r : ℝ} {z : ℂ} {B : Set ℂ} {k : ℤ × ℤ} (hk : k ∈ conf36T δ r z B) :
    k ∈ confSqIdx (δ * r) z (annulus z (3 * r) (4 * r)) := (Finset.mem_filter.1 hk).2.1

theorem conf36T_meets {δ r : ℝ} {z : ℂ} {B : Set ℂ} {k : ℤ × ℤ} (hk : k ∈ conf36T δ r z B) :
    (confSq (δ * r) z k ∩ B).Nonempty := (Finset.mem_filter.1 hk).2.2

theorem conf36T_cov {δ r : ℝ} (hδ : 0 < δ) (hr : 0 < r) {z : ℂ} {B : Set ℂ} {k : ℤ × ℤ}
    (hk : k ∈ confSqIdx (δ * r) z (annulus z (3 * r) (4 * r)))
    (hB : (confSq (δ * r) z k ∩ B).Nonempty) : k ∈ conf36T δ r z B :=
  Finset.mem_filter.2 ⟨conf36_mem_box hδ hr z hk, hk, hB⟩

end ClassicalT

/-- the a.s. connectivity event used at C:1393 -/
def conf36Conn (B : Set ℂ) (r : ℝ) (z : ℂ) : Prop :=
  (B ∩ (annulus z (3 * r) (4 * r) : Set ℂ)).Nonempty ∨ B ⊆ closedBall z (3 * r)

/-! ## The random radii `ρ̃^n` and the events `G̃^n`, `G^ε_x` -/

section Random
variable {Ω : Type} [MeasurableSpace Ω]

/-- `ρ̃^0 := e`, `ρ̃^n := inf {r ≥ 6ρ̃^{n−1} : r ∈ 2^ℤ e, E^{Ũ^r}_r(z) occurs}` (CONF (3.19)),
with random base radius `e ω = ε 𝕣` and centre `zf ω`, `Ũ^r` built from `Bf ω = 𝓑^•_τ` -/
def conf36Rho (ξ : ℝ) (cc : ℝ → ℝ) (D : DistC → ContMetric) (P : Measure Ω) (h : Ω → DistC)
    (p : CONFParams) (e : Ω → ℝ) (zf : Ω → ℂ) (Bf : Ω → Set ℂ) : ℕ → Ω → ℝ≥0∞
  | 0 => fun ω => ENNReal.ofReal (e ω)
  | n + 1 => fun ω => ⨅ (k : ℤ) (_ : 6 * conf36Rho ξ cc D P h p e zf Bf n ω ≤
      ENNReal.ofReal ((2 : ℝ) ^ k * e ω))
      (_ : ω ∈ confEU ξ cc D P h p ((2 : ℝ) ^ k * e ω) (zf ω)
        (conf36T p.δ ((2 : ℝ) ^ k * e ω) (zf ω) (Bf ω))),
      ENNReal.ofReal ((2 : ℝ) ^ k * e ω)

/-- `G̃^n` (CONF (3.22) with (3.9′), D108 (b)): `ρ̃^n = 2^k e` is attained, `E^{Ũ}_{ρ̃^n}(z)`,
the `G^U`-type event `Fat` (S3L36In; D108's (3.9′) via `conf36FatW`) for `Ũ^{ρ̃^n}`, and the
connectivity event; or `ρ̃^n = ∞` (CONF tacitly assumes
`ρ̃^n < ∞`; on `{ρ̃^n = ∞}`, `R^ε_𝕣(𝓑^•_τ) = ∞` and property A is vacuous) -/
def conf36Gt (Fat : ContMetric → ℝ → ℝ → ℂ → Finset (ℤ × ℤ) → Prop) (ξ : ℝ) (cc : ℝ → ℝ)
    (D : DistC → ContMetric) (P : Measure Ω) (h : Ω → DistC)
    (p : CONFParams) (e : Ω → ℝ) (zf : Ω → ℂ) (Bf : Ω → Set ℂ) (n : ℕ) : Set Ω :=
  {ω | conf36Rho ξ cc D P h p e zf Bf n ω = ⊤ ∨ ∃ k : ℤ, conf36Rho ξ cc D P h p e zf Bf n ω = ENNReal.ofReal ((2 : ℝ) ^ k * e ω) ∧
    ω ∈ confEU ξ cc D P h p ((2 : ℝ) ^ k * e ω) (zf ω)
      (conf36T p.δ ((2 : ℝ) ^ k * e ω) (zf ω) (Bf ω)) ∧
    Fat (D (h ω)) (scaleFac ξ cc (h ω) ((2 : ℝ) ^ k * e ω) (zf ω)) ((2 : ℝ) ^ k * e ω) (zf ω)
      (conf36T p.δ ((2 : ℝ) ^ k * e ω) (zf ω) (Bf ω)) ∧
    conf36Conn (Bf ω) ((2 : ℝ) ^ k * e ω) (zf ω)}

/-- `G^ε_x := ⋃_{n ∈ [1, ⌊η log ε⁻¹⌋]} G̃^n` (CONF (3.20)) -/
def conf36G (Fat : ContMetric → ℝ → ℝ → ℂ → Finset (ℤ × ℤ) → Prop) (ξ : ℝ) (cc : ℝ → ℝ)
    (D : DistC → ContMetric) (P : Measure Ω) (h : Ω → DistC)
    (p : CONFParams) (ε e : Ω → ℝ) (zf : Ω → ℂ) (Bf : Ω → Set ℂ) : Set Ω :=
  {ω | ∃ n : ℕ, 1 ≤ n ∧ n ≤ confN p (ε ω) ∧ ω ∈ conf36Gt Fat ξ cc D P h p e zf Bf n}

variable {ξ : ℝ} {cc : ℝ → ℝ} {D : DistC → ContMetric} {P : Measure Ω} {h : Ω → DistC}
  {p : CONFParams} {e : Ω → ℝ} {zf : Ω → ℂ} {Bf : Ω → Set ℂ}

theorem conf36Rho_le_succ (n : ℕ) (ω : Ω) :
    6 * conf36Rho ξ cc D P h p e zf Bf n ω ≤ conf36Rho ξ cc D P h p e zf Bf (n + 1) ω :=
  le_iInf fun _ => le_iInf fun hk => le_iInf fun _ => hk

theorem conf36Rho_mono (ω : Ω) : Monotone fun n => conf36Rho ξ cc D P h p e zf Bf n ω := by
  refine monotone_nat_of_le_succ fun n => le_trans ?_ (conf36Rho_le_succ n ω)
  calc conf36Rho ξ cc D P h p e zf Bf n ω = 1 * conf36Rho ξ cc D P h p e zf Bf n ω := (one_mul _).symm
    _ ≤ 6 * _ := by gcongr; norm_num

theorem conf36Rho_ge (n : ℕ) (ω : Ω) :
    ENNReal.ofReal (e ω) ≤ conf36Rho ξ cc D P h p e zf Bf n ω :=
  conf36Rho_mono (ξ := ξ) (cc := cc) (D := D) (P := P) (h := h) (p := p) (zf := zf) (Bf := Bf)
    ω (Nat.zero_le n)

/-- `ρ̃^n ≤ ρ^n_e(z)` (CONF C:1352–1355: `E_r(z) ⊆ E^{Ũ^r}_r(z)`) -/
theorem conf36Rho_le_confRho (ω : Ω) :
    ∀ n, conf36Rho ξ cc D P h p e zf Bf n ω ≤ confRho ξ cc D P h p (e ω) (zf ω) n ω := by
  intro n
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    refine le_iInf fun k => le_iInf fun hk => le_iInf fun hE => ?_
    refine iInf_le_of_le k (iInf_le_of_le ((by gcongr : 6 * conf36Rho ξ cc D P h p e zf Bf n ω ≤
      6 * confRho ξ cc D P h p (e ω) (zf ω) n ω).trans hk)
      (iInf_le_of_le ?_ le_rfl))
    exact mem_iInter₂.1 hE _ fun k' hk' => conf36T_sub hk'

end Random

end LQGMetric.CONF
