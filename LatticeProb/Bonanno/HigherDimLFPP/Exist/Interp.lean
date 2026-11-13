/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module HigherDimLFPP.Exist.Interp at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.HigherDimLFPP.Paths.Compare
import Mathlib.Topology.PartitionOfUnity

/-!
# Finite interpolation of fields and the log-distance functional (packet P-X5, T2 input)

Source: planning audit HA5, Details D2 (2) ("Interpolation") and finding G11; DGZ
arXiv:2310.03996, proof of Lemma 2.7 (discretization of the field).

HA5 D2 interpolates the field from the grid `2^{-k} ℤ^d` by multilinear (tent) weights.  The proof
of D2 uses only four properties of the weights, so we work with an arbitrary finite partition of
unity of small mesh, which Mathlib provides directly (`PartitionOfUnity.exists_isSubordinate`): an
`InterpScheme d K δ` consists of finitely many nodes `pt i ∈ K` and continuous weights `w i ≥ 0`
with `∑ᵢ w i = 1` on `K` and `w i z ≠ 0 → dist z (pt i) < δ`.  For `u : Fin n → ℝ`,
`S.interp u = ∑ᵢ w i · u i` is continuous, and on `K`:

* `abs_interp_sub_interp_le`: `|S.interp u - S.interp u'| ≤ ‖u - u'‖_∞` (convex combination);
* `abs_interp_le`: `|S.interp u| ≤ M` if all `|u i| ≤ M`;
* `abs_interp_comp_sub_le`: `|S.interp (f ∘ pt) - f| ≤ η` if `f` oscillates by at most `η` on
  `δ`-close pairs of `K` (the modulus of continuity of HA5 D2 (2)).

With the weight comparison of internal distances (`abs_log_lfppDistOn_sub_le`, P-X1), the
log-distance of the interpolated field, `logDistInterp S ξ V x y u = log D^ξ_V(x, y)(S.interp u)`
for `V ⊆ K`, `x ∈ V`, is `|ξ|`-Lipschitz in `u` for the sup norm (`lipschitzWith_logDistInterp`,
HA5 D2 (3)), is within `|ξ| η` of the log-distance of `f` at `u = f ∘ pt`
(`abs_logDistInterp_sub_le`, D2 (4)), and is bounded by `|log D^ξ_V(x,y)(0)| + |ξ| M`
(`abs_logDistInterp_le`, domination in D2 (4)).

`exists_interpScheme`: such a scheme exists for every compact `K` and `δ > 0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter Metric

namespace HigherDimLFPP

namespace Conc

variable {d : ℕ}

/-- A finite **interpolation scheme** of mesh `δ` on `K ⊆ ℝ^d`: nodes `pt i ∈ K` and continuous
weights `w i ≥ 0` forming a partition of unity on `K`, with `w i z ≠ 0` only for
`dist z (pt i) < δ`. -/
structure InterpScheme (d : ℕ) (K : Set (Rd d)) (δ : ℝ) where
  /-- The number of nodes. -/
  n : ℕ
  /-- The nodes. -/
  pt : Fin n → Rd d
  pt_mem : ∀ i, pt i ∈ K
  /-- The weights. -/
  w : Fin n → Rd d → ℝ
  continuous_w : ∀ i, Continuous (w i)
  w_nonneg : ∀ i z, 0 ≤ w i z
  sum_w : ∀ z ∈ K, ∑ i, w i z = 1
  dist_lt : ∀ i z, w i z ≠ 0 → dist z (pt i) < δ

/-- **Existence of interpolation schemes** of every mesh on a compact set (a finite cover by
`δ`-balls and a subordinate partition of unity). -/
theorem exists_interpScheme {K : Set (Rd d)} (hK : IsCompact K) {δ : ℝ} (hδ : 0 < δ) :
    Nonempty (InterpScheme d K δ) := by
  classical
  obtain ⟨t, htK, htfin, hcover⟩ := finite_cover_balls_of_compact hK hδ
  have : Fintype t := htfin.fintype
  set e : t ≃ Fin (Fintype.card t) := Fintype.equivFin t
  set pt : Fin (Fintype.card t) → Rd d := fun i => (e.symm i : Rd d) with hpt
  have hU : K ⊆ ⋃ i, ball (pt i) δ := by
    intro z hz
    obtain ⟨g, hg, hzg⟩ := mem_iUnion₂.1 (hcover hz)
    refine mem_iUnion.2 ⟨e ⟨g, hg⟩, ?_⟩
    simp only [hpt, Equiv.symm_apply_apply]
    exact hzg
  obtain ⟨f, hf⟩ := PartitionOfUnity.exists_isSubordinate hK.isClosed (fun i => ball (pt i) δ)
    (fun _ => isOpen_ball) hU
  refine ⟨⟨Fintype.card t, pt, fun i => htK (e.symm i).2, fun i z => f i z,
    fun i => (f i).continuous, fun i z => f.nonneg i z, fun z hz => ?_, fun i z hz => ?_⟩⟩
  · have h := f.sum_eq_one hz
    rwa [finsum_eq_sum_of_fintype] at h
  · have h1 : z ∈ tsupport (f i) := subset_tsupport _ (Function.mem_support.2 hz)
    exact mem_ball.1 (hf i h1)

namespace InterpScheme

variable {K : Set (Rd d)} {δ : ℝ} (S : InterpScheme d K δ)

/-- The interpolated field `z ↦ ∑ᵢ w i z · u i`. -/
def interp (u : Fin S.n → ℝ) (z : Rd d) : ℝ := ∑ i, S.w i z * u i

theorem continuous_interp (u : Fin S.n → ℝ) : Continuous (S.interp u) :=
  continuous_finsetSum _ fun i _ => (S.continuous_w i).mul continuous_const

/-- On `K` a convex combination is controlled by the largest coefficient. -/
theorem abs_sum_w_mul_le {z : Rd d} (hz : z ∈ K) {c : Fin S.n → ℝ} {M : ℝ}
    (hc : ∀ i, S.w i z ≠ 0 → |c i| ≤ M) : |∑ i, S.w i z * c i| ≤ M := by
  calc |∑ i, S.w i z * c i| ≤ ∑ i, |S.w i z * c i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, S.w i z * M := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul, abs_of_nonneg (S.w_nonneg i z)]
        by_cases hi : S.w i z = 0
        · rw [hi, zero_mul, zero_mul]
        · exact mul_le_mul_of_nonneg_left (hc i hi) (S.w_nonneg i z)
    _ = M := by rw [← Finset.sum_mul, S.sum_w z hz, one_mul]

/-- `|S.interp u - S.interp u'| ≤ ‖u - u'‖_∞` on `K`. -/
theorem abs_interp_sub_interp_le {z : Rd d} (hz : z ∈ K) (u u' : Fin S.n → ℝ) :
    |S.interp u z - S.interp u' z| ≤ dist u u' := by
  have e : S.interp u z - S.interp u' z = ∑ i, S.w i z * (u i - u' i) := by
    simp only [interp, mul_sub, Finset.sum_sub_distrib]
  rw [e]
  refine S.abs_sum_w_mul_le hz fun i _ => ?_
  rw [← Real.dist_eq]
  exact dist_le_pi_dist u u' i

/-- `|S.interp u| ≤ M` on `K` if all `|u i| ≤ M`. -/
theorem abs_interp_le {z : Rd d} (hz : z ∈ K) {u : Fin S.n → ℝ} {M : ℝ}
    (hM : ∀ i, |u i| ≤ M) : |S.interp u z| ≤ M :=
  S.abs_sum_w_mul_le hz fun i _ => hM i

/-- **Interpolation error**: if `|f (pt i) - f z| ≤ η` whenever `z ∈ K` and
`dist z (pt i) < δ`, then `|S.interp (f ∘ pt) z - f z| ≤ η` on `K`. -/
theorem abs_interp_comp_sub_le {f : Rd d → ℝ} {η : ℝ}
    (hη : ∀ i, ∀ z ∈ K, dist z (S.pt i) < δ → |f (S.pt i) - f z| ≤ η) {z : Rd d}
    (hz : z ∈ K) : |S.interp (fun i => f (S.pt i)) z - f z| ≤ η := by
  have e : S.interp (fun i => f (S.pt i)) z - f z = ∑ i, S.w i z * (f (S.pt i) - f z) := by
    simp only [interp, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, S.sum_w z hz,
      one_mul]
  rw [e]
  exact S.abs_sum_w_mul_le hz fun i hi => hη i z hz (S.dist_lt i z hi)

end InterpScheme

/-! ### The log-distance of interpolated fields -/

section LogDist

variable {K : Set (Rd d)} {δ : ℝ}

/-- `log D^ξ_V(x, y)` of the interpolated field `S.interp u`. -/
def logDistInterp (S : InterpScheme d K δ) (ξ : ℝ) (V : Set (Rd d)) (x y : Rd d)
    (u : Fin S.n → ℝ) : ℝ :=
  Real.log (lfppDistOn ξ (S.interp u) V x y)

variable (S : InterpScheme d K δ) (ξ : ℝ) {V : Set (Rd d)} {x : Rd d}

/-- **Lipschitz property** (HA5 D2 (3)): for `V ⊆ K` and `x ∈ V`, `u ↦ log D^ξ_V(x,y)(S.interp u)`
is `|ξ|`-Lipschitz for the sup norm. -/
theorem lipschitzWith_logDistInterp (hVK : V ⊆ K) (hx : x ∈ V) (y : Rd d) :
    LipschitzWith ‖ξ‖₊ (logDistInterp S ξ V x y) := by
  refine LipschitzWith.of_dist_le_mul fun u u' => ?_
  rw [Real.dist_eq, coe_nnnorm, Real.norm_eq_abs]
  exact abs_log_lfppDistOn_sub_le (S.continuous_interp u) (S.continuous_interp u') hx
    fun _z hz => S.abs_interp_sub_interp_le (hVK hz) u u'

/-- **Approximation** (HA5 D2 (4)): if `f` is continuous and oscillates by at most `η` on
`δ`-close pairs of `K`, then the log-distances of `f` and of its interpolation differ by at most
`|ξ| η`. -/
theorem abs_logDistInterp_sub_le (hVK : V ⊆ K) (hx : x ∈ V) (y : Rd d) {f : Rd d → ℝ}
    (hf : Continuous f) {η : ℝ}
    (hη : ∀ i, ∀ z ∈ K, dist z (S.pt i) < δ → |f (S.pt i) - f z| ≤ η) :
    |logDistInterp S ξ V x y (fun i => f (S.pt i)) - Real.log (lfppDistOn ξ f V x y)| ≤
      |ξ| * η :=
  abs_log_lfppDistOn_sub_le (S.continuous_interp _) hf hx
    fun _z hz => S.abs_interp_comp_sub_le hη (hVK hz)

/-- `|log D^ξ_V(x,y)(φ)| ≤ |log D^ξ_V(x,y)(0)| + |ξ| M` if `φ` is continuous and `|φ| ≤ M` on
`V ∋ x`. -/
theorem abs_log_lfppDistOn_le_of_abs_le (hx : x ∈ V) (y : Rd d) {φ : Rd d → ℝ}
    (hφ : Continuous φ) {M : ℝ} (hM : ∀ z ∈ V, |φ z| ≤ M) :
    |Real.log (lfppDistOn ξ φ V x y)| ≤
      |Real.log (lfppDistOn ξ (fun _ => 0) V x y)| + |ξ| * M := by
  have h := abs_log_lfppDistOn_sub_le (ζ := ξ) (y := y) hφ continuous_const hx
    (M := M) fun z hz => by rw [sub_zero]; exact hM z hz
  have h2 := abs_sub_abs_le_abs_sub (Real.log (lfppDistOn ξ φ V x y))
    (Real.log (lfppDistOn ξ (fun _ => 0) V x y))
  linarith

/-- **Domination** (HA5 D2 (4)): if all `|u i| ≤ M`, then
`|log D^ξ_V(x,y)(S.interp u)| ≤ |log D^ξ_V(x,y)(0)| + |ξ| M`. -/
theorem abs_logDistInterp_le (hVK : V ⊆ K) (hx : x ∈ V) (y : Rd d) {u : Fin S.n → ℝ} {M : ℝ}
    (hM : ∀ i, |u i| ≤ M) :
    |logDistInterp S ξ V x y u| ≤ |Real.log (lfppDistOn ξ (fun _ => 0) V x y)| + |ξ| * M :=
  abs_log_lfppDistOn_le_of_abs_le ξ hx y (S.continuous_interp u)
    fun _z hz => S.abs_interp_le (hVK hz) hM

end LogDist

end Conc

end HigherDimLFPP
