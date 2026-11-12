/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Geom58P2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom58P1
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom58Win2

/-!
# GM Lemma 5.8: the end paths `L̂_x`, `L̂_y` (task P2-M2L58c)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, proof of
Lemma 5.8, Step 2 (l. 3080–3086). GM leave the paths implicit; own explicit construction
(`handoff/P2-M2L58.md`). With `ρ₁ = 1.1r`, `ρ₀ = 1.25r`, `ρ_m = 1.75r`:

* `legL r R T θx` (GM's `L̂_x`, from `x = 2r e^{iθx}` to `z_0 − 2R`, `z_0 = T + i√(r² − T²)`):
  stub `[T − 5R, T − 2R] × {Im z_0}`, vertical at `Re = T − 5R` up to the circle `ρ₁`, radial
  `ρ₁ → ρ₀` at angle `γa`, arc of radius `ρ₀` from `γa` to `θx`, radial `ρ₀ → 2r` at `θx`;
* `legR r R T' θy` (GM's `L̂_y`, from `z_{m−1} + 2R` to `y = 2r e^{iθy}`): stub
  `[T' + 2R, T' + 5R] × {Im z_{m−1}}`, vertical at `Re = T' + 5R`, radial `ρ₁ → ρ_m` at `γb`, arc of
  radius `ρ_m` between `γb` and `θy`, radial `ρ_m → 2r` at `θy`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Real

namespace LQGMetric.GM

/-- the angle where the left vertical meets the circle `1.1 r` -/
def gA (r R T : ℝ) : ℝ := arccos ((T - 5 * R) / (11 / 10 * r))

/-- the angle where the right vertical meets the circle `1.1 r` -/
def gB (r R T' : ℝ) : ℝ := arccos ((T' + 5 * R) / (11 / 10 * r))

/-- GM's `L̂_x` -/
def legL (r R T θx : ℝ) : Set ℂ :=
  hSeg (Real.sqrt (r ^ 2 - T ^ 2)) (T - 5 * R) (T - 2 * R) ∪
    vSeg (T - 5 * R) (Real.sqrt (r ^ 2 - T ^ 2))
      (Real.sqrt ((11 / 10 * r) ^ 2 - (T - 5 * R) ^ 2)) ∪
    radSet (gA r R T) (11 / 10 * r) (5 / 4 * r) ∪ arcSet (5 / 4 * r) (gA r R T) θx ∪
    radSet θx (5 / 4 * r) (2 * r)

/-- GM's `L̂_y` -/
def legR (r R T' θy : ℝ) : Set ℂ :=
  hSeg (Real.sqrt (r ^ 2 - T' ^ 2)) (T' + 2 * R) (T' + 5 * R) ∪
    vSeg (T' + 5 * R) (Real.sqrt (r ^ 2 - T' ^ 2))
      (Real.sqrt ((11 / 10 * r) ^ 2 - (T' + 5 * R) ^ 2)) ∪
    radSet (gB r R T') (11 / 10 * r) (7 / 4 * r) ∪
    arcSet (7 / 4 * r) (min (gB r R T') θy) (max (gB r R T') θy) ∪ radSet θy (7 / 4 * r) (2 * r)

lemma isCompact_legL (r R T θx : ℝ) : IsCompact (legL r R T θx) :=
  ((((isCompact_hSeg _ _ _).union (isCompact_vSeg _ _ _)).union (isCompact_radSet _ _ _)).union
    (isCompact_arcSet _ _ _)).union (isCompact_radSet _ _ _)

lemma isCompact_legR (r R T' θy : ℝ) : IsCompact (legR r R T' θy) :=
  ((((isCompact_hSeg _ _ _).union (isCompact_vSeg _ _ _)).union (isCompact_radSet _ _ _)).union
    (isCompact_arcSet _ _ _)).union (isCompact_radSet _ _ _)

/-- the top of the vertical at `Re = t` is the foot of the radial -/
lemma vtop_eq {r t : ℝ} (hr : 0 < r) (ht : |t| ≤ r / 2) :
    (⟨t, Real.sqrt ((11 / 10 * r) ^ 2 - t ^ 2)⟩ : ℂ) = polPt (11 / 10 * r)
      (arccos (t / (11 / 10 * r))) :=
  (polPt_arccos (by positivity) (by linarith)).symm

lemma mem_radSet_of {θ ρ₁ ρ₂ s : ℝ} (h1 : ρ₁ ≤ s) (h2 : s ≤ ρ₂) : polPt s θ ∈ radSet θ ρ₁ ρ₂ :=
  ⟨s, ⟨h1, h2⟩, rfl⟩

lemma mem_arcSet_of {ρ θ₁ θ₂ φ : ℝ} (h1 : θ₁ ≤ φ) (h2 : φ ≤ θ₂) : polPt ρ φ ∈ arcSet ρ θ₁ θ₂ :=
  ⟨φ, ⟨h1, h2⟩, rfl⟩

lemma isConnected_legL {r R T θx : ℝ} (hr : 0 < r) (hR : 0 < R) (hT : |T - 5 * R| ≤ r / 2)
    (hθ : gA r R T ≤ θx) : IsConnected (legL r R T θx) := by
  have e := vtop_eq hr hT
  refine (((((isConnected_hSeg _ (by linarith)).union ?_ (isConnected_vSeg _ _ _)).union ?_
    (isConnected_radSet _ (by linarith))).union ?_ (isConnected_arcSet _ hθ)).union ?_
    (isConnected_radSet _ (by linarith)))
  · exact ⟨⟨T - 5 * R, Real.sqrt (r ^ 2 - T ^ 2)⟩, mem_hSeg.2 ⟨rfl, le_rfl, by simp; linarith⟩,
      mem_vSeg.2 ⟨rfl, min_le_left _ _, le_max_left _ _⟩⟩
  · refine ⟨polPt (11 / 10 * r) (gA r R T), Or.inr ?_, mem_radSet_of le_rfl (by linarith)⟩
    rw [gA, ← e]; exact mem_vSeg.2 ⟨rfl, min_le_right _ _, le_max_right _ _⟩
  · exact ⟨polPt (5 / 4 * r) (gA r R T), Or.inr (mem_radSet_of (by linarith) le_rfl),
      mem_arcSet_of le_rfl hθ⟩
  · exact ⟨polPt (5 / 4 * r) θx, Or.inr (mem_arcSet_of hθ le_rfl),
      mem_radSet_of le_rfl (by linarith)⟩

lemma isConnected_legR {r R T' θy : ℝ} (hr : 0 < r) (hR : 0 < R) (hT : |T' + 5 * R| ≤ r / 2) :
    IsConnected (legR r R T' θy) := by
  have e := vtop_eq hr hT
  refine (((((isConnected_hSeg _ (by linarith)).union ?_ (isConnected_vSeg _ _ _)).union ?_
    (isConnected_radSet _ (by linarith))).union ?_ (isConnected_arcSet _ min_le_max)).union ?_
    (isConnected_radSet _ (by linarith)))
  · exact ⟨⟨T' + 5 * R, Real.sqrt (r ^ 2 - T' ^ 2)⟩, mem_hSeg.2 ⟨rfl, by simp; linarith, le_rfl⟩,
      mem_vSeg.2 ⟨rfl, min_le_left _ _, le_max_left _ _⟩⟩
  · refine ⟨polPt (11 / 10 * r) (gB r R T'), Or.inr ?_, mem_radSet_of le_rfl (by linarith)⟩
    rw [gB, ← e]; exact mem_vSeg.2 ⟨rfl, min_le_right _ _, le_max_right _ _⟩
  · exact ⟨polPt (7 / 4 * r) (gB r R T'), Or.inr (mem_radSet_of (by linarith) le_rfl),
      mem_arcSet_of (min_le_left _ _) (le_max_left _ _)⟩
  · exact ⟨polPt (7 / 4 * r) θy, Or.inr (mem_arcSet_of (min_le_right _ _) (le_max_right _ _)),
      mem_radSet_of le_rfl (by linarith)⟩

/-! ## Norms of the inner pieces -/

lemma sq_diff_le {t T R r : ℝ} (hR : 0 ≤ R) (h1 : |t - T| ≤ 5 * R) (ht : |t| ≤ r / 2)
    (hT : |T| ≤ r / 2) : t ^ 2 - T ^ 2 ≤ 5 * R * r := by
  have e : t ^ 2 - T ^ 2 = (t - T) * (t + T) := by ring
  have h2 : |t + T| ≤ r := (abs_add_le t T).trans (by linarith)
  rw [e]
  calc (t - T) * (t + T) ≤ |(t - T) * (t + T)| := le_abs_self _
    _ = |t - T| * |t + T| := abs_mul _ _
    _ ≤ 5 * R * r := mul_le_mul h1 h2 (abs_nonneg _) (by positivity)

lemma norm_ge_of_sq {p : ℂ} {a : ℝ} (ha : 0 ≤ a) (h : a ^ 2 ≤ ‖p‖ ^ 2) : a ≤ ‖p‖ :=
  (pow_le_pow_iff_left₀ ha (norm_nonneg p) two_ne_zero).1 h

lemma norm_le_of_sq {p : ℂ} {a : ℝ} (ha : 0 ≤ a) (h : ‖p‖ ^ 2 ≤ a ^ 2) : ‖p‖ ≤ a :=
  (pow_le_pow_iff_left₀ (norm_nonneg p) ha two_ne_zero).1 h

/-- a stub point `t + i√(r² − T²)` with `|t − T| ≤ 5R` -/
lemma norm_stub {r R T : ℝ} {p : ℂ} (hr : 0 < r) (hR : 0 ≤ R) (hRr : 500 * R ≤ r)
    (hT : |T| ≤ r / 2) (ht : |p.re| ≤ r / 2) (h1 : |p.re - T| ≤ 5 * R)
    (him : p.im = Real.sqrt (r ^ 2 - T ^ 2)) : r / 2 ≤ ‖p‖ ∧ ‖p‖ ≤ 11 / 10 * r := by
  have hT2 : T ^ 2 ≤ r ^ 2 / 4 := by nlinarith [sq_abs T, abs_nonneg T]
  have hd := sq_diff_le hR h1 ht hT
  have hn : ‖p‖ ^ 2 = p.re ^ 2 + (r ^ 2 - T ^ 2) := by
    rw [norm_sq_eq_re_im, him, Real.sq_sqrt (by nlinarith)]
  constructor
  · exact norm_ge_of_sq (by linarith) (by nlinarith [sq_nonneg p.re])
  · exact norm_le_of_sq (by linarith) (by nlinarith)

/-- a point of the vertical `Re = u` between heights `√(r² − T²)` and `√(1.21 r² − u²)` -/
lemma norm_vert {r R T u : ℝ} {p : ℂ} (hr : 0 < r) (hR : 0 ≤ R) (hRr : 500 * R ≤ r)
    (hT : |T| ≤ r / 2) (hu : |u| ≤ r / 2) (h1 : |u - T| ≤ 5 * R) (hre : p.re = u)
    (him : p.im ∈ uIcc (Real.sqrt (r ^ 2 - T ^ 2)) (Real.sqrt ((11 / 10 * r) ^ 2 - u ^ 2))) :
    r / 2 ≤ ‖p‖ ∧ ‖p‖ ≤ 11 / 10 * r := by
  have hT2 : T ^ 2 ≤ r ^ 2 / 4 := by nlinarith [sq_abs T, abs_nonneg T]
  have hu2 : u ^ 2 ≤ r ^ 2 / 4 := by nlinarith [sq_abs u, abs_nonneg u]
  have hd := sq_diff_le hR h1 hu hT
  have hle : Real.sqrt (r ^ 2 - T ^ 2) ≤ Real.sqrt ((11 / 10 * r) ^ 2 - u ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith)
  rw [uIcc_of_le hle] at him
  obtain ⟨hlo, hhi⟩ := him
  have hs1 := Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ r ^ 2 - T ^ 2)
  have hs2 := Real.sq_sqrt (by nlinarith : (0 : ℝ) ≤ (11 / 10 * r) ^ 2 - u ^ 2)
  have h0 := Real.sqrt_nonneg (r ^ 2 - T ^ 2)
  have hn := norm_sq_eq_re_im p
  rw [hre] at hn
  have e1 : (r ^ 2 - T ^ 2) ≤ p.im ^ 2 := by rw [← hs1]; nlinarith
  have e2 : p.im ^ 2 ≤ (11 / 10 * r) ^ 2 - u ^ 2 := by rw [← hs2]; nlinarith
  constructor
  · exact norm_ge_of_sq (by linarith) (by nlinarith [sq_nonneg u])
  · exact norm_le_of_sq (by linarith) (by nlinarith)

end LQGMetric.GM
