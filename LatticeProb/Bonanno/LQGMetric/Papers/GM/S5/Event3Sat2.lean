/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Event3Sat2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Event3Sat1
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Geom58Data

/-!
# GM Lemma 5.9, deterministic part II: `E_r` is determined by `h|_{𝔸_{r/4,4r}(0)}`
(task P2-M2M4, D83 P4b)

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`, proof of
Lemma 5.9 (l. 3293–3302): "conditions 4–9 depend only on the internal metrics of `D_h` restricted to
`𝔸_{r/4,4r}(0)` (the sets `U_r^{x,y}`, `W_r^x` and `𝔸_{r,4r}(0)` lie in `𝔸_{r/4,4r}(0)`), condition
10 on `h|_{𝔸_{r/4,3r}(0)}`, and the event of Lemma 5.8 as in Lemma 5.7".

`eventE_saturated`: for two fields whose metrics `D`, `D̃` are boundedly compact length metrics with
`c_* D ≤ D̃ ≤ C_* D`, with the same internal metrics `D(·,·;𝔸)`, `D̃(·,·;𝔸)` on
`𝔸 = 𝔸_{r/4,4r}(0)`, the same `𝔠_r e^{ξ h_r(0)}` and the same `(h, φ)_∇`, `φ ∈ 𝓖_r`, membership
in `E_r` transfers. Geometry: `U_r^{x,y}` lies within `2ε₀r` of `cl 𝔸_{r/2,2r}(0)`
(`IsSquareTube`), `W_r^x` within `2θr` of `[x, (3/2 − θ)x]` (`norm_of_mem_lineTube`), the balls
`B_{5ρr}(u)` of condition (1) lie in `𝔸`. Setwise distances between spheres in `𝔸` are infima of
internal distances (`setDist_spheres_eq_internal`), lengths of paths in `𝔸` are lengths for the
internal metric (`lenFun_internal`). Own elementary verification of the inclusions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint MetricGeometry

/-- points of the closure of a square tube over `X ⊆ {a ≤ |w| ≤ b}` (side `s`) have modulus in
`[a − 2s, b + 2s]` -/
lemma norm_of_mem_closure_squareTube {V : Set ℂ} {s a b : ℝ} {X : Set ℂ}
    (hV : IsSquareTube V s X) (hX : ∀ w ∈ X, a ≤ ‖w‖ ∧ ‖w‖ ≤ b) {p : ℂ} (hp : p ∈ closure V) :
    a - 2 * s ≤ ‖p‖ ∧ ‖p‖ ≤ b + 2 * s := by
  obtain ⟨F, hF, rfl⟩ := hV
  have hK : IsClosed (⋃ m ∈ F, gridSquare s m) :=
    isClosed_biUnion_finset fun m _ => isClosed_gridSquare s m
  have hp' := (closure_mono interior_subset).trans hK.closure_subset hp
  obtain ⟨m, hm, hpm⟩ := mem_iUnion₂.1 hp'
  obtain ⟨c, hcm, hcX⟩ := hF hm
  have hd := L58Data.dist_le_of_mem_sq hpm hcm
  rw [dist_eq_norm] at hd
  have h1 := norm_sub_norm_le p c
  have h2 := norm_sub_norm_le c p
  rw [norm_sub_rev] at h2
  have := hX c hcX
  constructor <;> linarith

/-- points of `W_r^x(θ)` (`|x| = 2r`) have modulus in `[2r − 2θr, 3r]` -/
lemma norm_of_mem_lineTube {θ r : ℝ} (hr : 0 < r) (hθ0 : 0 ≤ θ) (hθ : θ ≤ 1 / 2) {x : ℂ}
    (hx : ‖x‖ = 2 * r) {p : ℂ} (hp : p ∈ lineTube θ r x) :
    2 * r - 2 * (θ * r) ≤ ‖p‖ ∧ ‖p‖ ≤ 3 * r := by
  obtain ⟨m, hm, hpm⟩ := mem_iUnion₂.1 (interior_subset hp)
  obtain ⟨c, hcm, hcX⟩ := hm
  have hd := L58Data.dist_le_of_mem_sq hpm hcm
  rw [dist_eq_norm] at hd
  rw [segment_eq_image] at hcX
  obtain ⟨t, ht, rfl⟩ := hcX
  have hc : (1 - t) • x + t • (((3 / 2 - θ : ℝ) : ℂ) * x) = ((1 + t * (1 / 2 - θ) : ℝ) : ℂ) * x := by
    simp only [Complex.real_smul]; push_cast; ring
  have hco : 0 ≤ 1 + t * (1 / 2 - θ) := by nlinarith [ht.1]
  have hn : ‖(1 - t) • x + t • (((3 / 2 - θ : ℝ) : ℂ) * x)‖ = (1 + t * (1 / 2 - θ)) * (2 * r) := by
    rw [hc, norm_mul, Complex.norm_real, Real.norm_of_nonneg hco, hx]
  have h1 := norm_sub_norm_le p ((1 - t) • x + t • (((3 / 2 - θ : ℝ) : ℂ) * x))
  have h2 := norm_sub_norm_le ((1 - t) • x + t • (((3 / 2 - θ : ℝ) : ℂ) * x)) p
  rw [norm_sub_rev] at h2
  rw [hn] at h1 h2
  have e1 : 0 ≤ t * (1 / 2 - θ) := mul_nonneg ht.1 (by linarith)
  have e2 : t * (1 / 2 - θ) ≤ 1 / 2 - θ := by nlinarith [ht.2]
  constructor <;> nlinarith

/-- **GM Lemma 5.9, deterministic core** (l. 3293–3302): `E_r` is determined by the internal
metrics of `𝔸_{r/4,4r}(0)`, the scale `𝔠_r e^{ξ h_r(0)}` and the pairings `(h, φ)_∇`, `φ ∈ 𝓖_r` -/
theorem eventE_saturated {D D' : DistC → ContMetric} {S : EData} {U : ℂ → ℂ → Set ℂ}
    {fb gb : Set ℂ → TestC} {r : ℝ} (hr : 0 < r) (hS : S.Ranges) (hcs : 0 < S.cs)
    (hCs : S.cs ≤ S.Cs) (hU : IsTubeFam S U r) {g₁ g₂ : DistC}
    (l1 : D g₁ ∈ LocalEvent.lenSet) (l1' : D' g₁ ∈ LocalEvent.lenSet)
    (l2 : D g₂ ∈ LocalEvent.lenSet) (l2' : D' g₂ ∈ LocalEvent.lenSet)
    (rat1 : BilipAt D D' S.cs S.Cs g₁) (rat2 : BilipAt D D' S.cs S.Cs g₂)
    (e : (D g₁).internal (annulus 0 (r / 4) (4 * r)) = (D g₂).internal (annulus 0 (r / 4) (4 * r)))
    (e' : (D' g₁).internal (annulus 0 (r / 4) (4 * r)) =
      (D' g₂).internal (annulus 0 (r / 4) (4 * r)))
    (hsf : scaleFac S.ξ S.c g₂ r 0 = scaleFac S.ξ S.c g₁ r 0)
    (hdir : ∀ φ ∈ bumpFam S U fb gb r, dirInner g₂ φ = dirInner g₁ φ)
    (h1 : g₁ ∈ eventE D D' S U fb gb r) : g₂ ∈ eventE D D' S U fb gb r := by
  obtain ⟨-, -, hb, hρ, hε, -, hζ, -, hθ, -⟩ := hS
  set A : Set ℂ := (annulus 0 (r / 4) (4 * r) : Set ℂ) with hAdef
  have hA : IsOpen A := (annulus 0 (r / 4) (4 * r)).isOpen
  have memA : ∀ w : ℂ, r / 4 < ‖w‖ → ‖w‖ < 4 * r → w ∈ A := fun w h1 h2 => by
    show r / 4 < ‖w - 0‖ ∧ ‖w - 0‖ < 4 * r
    rw [sub_zero]; exact ⟨h1, h2⟩
  have hε' : S.ε₀ < 1 / 10000 := by linarith [hε.2, hb.2]
  -- the closures of the tubes, and their `2ζr`-neighbourhoods, lie in `𝔸`
  have hclU : ∀ x ∈ sphere (0 : ℂ) (2 * r), ∀ y ∈ sphere (0 : ℂ) (2 * r), S.δ * r ≤ ‖x - y‖ →
      ∀ p ∈ closure (U x y), r / 2 - 2 * (S.ε₀ * r) ≤ ‖p‖ ∧ ‖p‖ ≤ 2 * r + 2 * (S.ε₀ * r) :=
    fun x hx y hy hxy p hp =>
      norm_of_mem_closure_squareTube (hU x hx y hy hxy).2.2.2.1 (fun w hw => hw) hp
  have hUA : ∀ x ∈ sphere (0 : ℂ) (2 * r), ∀ y ∈ sphere (0 : ℂ) (2 * r), S.δ * r ≤ ‖x - y‖ →
      U x y ⊆ A := fun x hx y hy hxy p hp => by
    have := hclU x hx y hy hxy p (subset_closure hp)
    exact memA p (by nlinarith [this.1, hε.1]) (by nlinarith [this.2, hε.1])
  have hthA : ∀ x ∈ sphere (0 : ℂ) (2 * r), ∀ y ∈ sphere (0 : ℂ) (2 * r), S.δ * r ≤ ‖x - y‖ →
      thickening (2 * S.ζ * r) (frontier (U x y)) ⊆ A := fun x hx y hy hxy q hq => by
    obtain ⟨p, hp, hqp⟩ := mem_thickening_iff.1 hq
    have := hclU x hx y hy hxy p (frontier_subset_closure hp)
    rw [dist_eq_norm] at hqp
    have h1 := norm_sub_norm_le q p
    have h2 := norm_sub_norm_le p q
    rw [norm_sub_rev] at h2
    have hζ' : S.ζ < 1 / 10000 := by linarith [hζ.2]
    exact memA q (by nlinarith [this.1, hε.1, hζ.1]) (by nlinarith [this.2, hε.1, hζ.1])
  have hBA : ∀ w ∈ (annulus 0 ((1 - 4 * S.ρ) * r) ((1 + 4 * S.ρ) * r) : Set ℂ),
      ball w (5 * S.ρ * r) ⊆ A := fun w hw q hq => by
    have hw' : (1 - 4 * S.ρ) * r < ‖w‖ ∧ ‖w‖ < (1 + 4 * S.ρ) * r := by
      have := hw; simp only [annulus, TopologicalSpace.Opens.coe_mk, mem_ofPred_eq, sub_zero] at this
      exact this
    rw [mem_ball, dist_eq_norm] at hq
    have h1 := norm_sub_norm_le q w
    have h2 := norm_sub_norm_le w q
    rw [norm_sub_rev] at h2
    exact memA q (by nlinarith [hρ.2]) (by nlinarith [hρ.2])
  have hLA : ∀ x ∈ sphere (0 : ℂ) (2 * r), lineTube S.θ r x ⊆ A := fun x hx p hp => by
    have := norm_of_mem_lineTube hr hθ.1.le (by linarith [hθ.2, hζ.2, hε.2, hb.2])
      (mem_sphere_zero_iff_norm.1 hx) hp
    exact memA p (by nlinarith [this.1, hθ.2, hζ.2, hε.2, hb.2]) (by linarith [this.2])
  have h14A : (annulus 0 r (4 * r) : Set ℂ) ⊆ A := fun w hw => by
    have hw' : r < ‖w - 0‖ ∧ ‖w - 0‖ < 4 * r := hw
    rw [sub_zero] at hw'
    exact memA w (by linarith [hw'.1]) hw'.2
  have eI : ∀ V ⊆ A, (D g₂).internal V = (D g₁).internal V := fun V hV =>
    (internal_eq_of_internal_eq hV e).symm
  have hsd : setDist (D g₂) (sphere 0 (2 * r)) (sphere 0 (3 * r)) =
      setDist (D g₁) (sphere 0 (2 * r)) (sphere 0 (3 * r)) := by
    have hsub : ∀ w : ℂ, 2 * r ≤ ‖w - 0‖ → ‖w - 0‖ ≤ 3 * r → w ∈ A := fun w h1 h2 => by
      rw [sub_zero] at h1 h2; exact memA w (by linarith) (by linarith)
    rw [setDist_spheres_eq_internal _ (isLen_of_mem l2) (by linarith) hsub,
      setDist_spheres_eq_internal _ (isLen_of_mem l1) (by linarith) hsub, e]
  have hρr : 0 < S.ρ * r := mul_pos hρ.1 hr
  obtain ⟨hL, h4, h5, h6, h7, h8, h9, h10⟩ := h1
  refine ⟨linkEvent_saturated hρr hcs hCs hA hUA hBA l1 l1' l2 l2' rat1 rat2 e e' hL, ?_⟩
  show (let sf := scaleFac S.ξ S.c g₂ r 0; _)
  intro sf
  refine ⟨fun x hx y hy hxy => ?_, fun x hx y hy hxy => ?_,
    fun x hx y hy hxy P s t hst hP hPth hdiam => ?_, fun z₁ hz₁ z₂ hz₂ hz => ?_,
    fun x hx => ?_, fun x hx => ?_, fun φ hφ => ?_⟩
  · simp only [sf, hsf]; rw [eI _ h14A, hsd]; exact h4 x hx y hy hxy
  · have := h5 x hx y hy hxy
    simp only [sf, hsf]
    rw [internalDiam] at this ⊢
    rw [eI _ (hUA x hx y hy hxy)]; exact this
  · have hmaps : MapsTo P (Icc s t) A := fun τ hτ => hthA x hx y hy hxy (hPth ⟨τ, hτ, rfl⟩)
    simp only [sf, hsf]
    rw [← lenFun_internal (D g₂) hP hmaps, ← e, lenFun_internal (D g₁) hP hmaps]
    exact h6 x hx y hy hxy P s t hst hP hPth hdiam
  · simp only [sf, hsf]; rw [← e]; exact h7 z₁ hz₁ z₂ hz₂ hz
  · simp only [sf, hsf]; rw [eI _ h14A]; exact h8 x hx
  · have := h9 x hx
    simp only [sf, hsf]
    rw [internalDiam] at this ⊢
    rw [eI _ (hLA x hx)]; exact this
  · rw [hdir φ hφ]; exact h10 φ hφ

end LQGMetric.GM
