/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.GM.S5.Shortcut2Pts at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Shortcut2Eq541
import LatticeProb.Bonanno.LQGMetric.Papers.GM.S5.Shortcut2Bump

/-!
# GM §5.5: Lemma 5.15 and Lemma 5.11 at given points of `O_u`, `O_v`

GM = Gwynne–Miller, arXiv:1905.00383, `literature/src/1905.00383/uniqueness-final.tex`
(task P2-M2M2, WP-M2m, row 16 of `blueprint/M2.md`).

`gm_L5_15_pts`: GM Lemma 5.15 (`lem-internal-geo0`, l. 3463–3511) and the proof of Lemma 5.11
(l. 3513–3550) at points `p ∈ O_u`, `q ∈ O_v`, where `u, v` are the points of `linkEvent` for
`(x, y)` and `φ = φ_r^{x,y}`: `p, q ∈ B_{3r/2}(0)`, `|p − q| ≥ (b − 40ε₀)r` (l. 3496–3497),
(5.41) and (5.46). The remaining step of GM's proof of Lemma 5.15 is that the `D_{h−φ}`-geodesic
`P^φ` visits `O_u` and then `O_v` (GM Lemma 5.14 and l. 3477–3489); with it, `s` and `t` are the
times of these visits.

Hypotheses beyond GM's: `hpos : 2c_*⁻¹C_*η < 1` (GM's (5.15) is meaningless otherwise; missing in
`EtaChoice`) and `hη3 : 1 + 3η ≤ C_*/c_*` (repair of GM's l. 3505, see `Shortcut2Eq541.lean`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric
open scoped ENNReal

namespace LQGMetric.GM
open Blueprint

/-- **GM Lemma 5.15 + (5.46)** at points `p ∈ O_u`, `q ∈ O_v`. -/
theorem gm_L5_15_pts {D D' : DistC → ContMetric} {c₂ : ℝ} {S : EData} (hS : S.Ranges)
    (hcs : 0 < S.cs) (hc₁ : S.cs < S.c₁) (hcC : S.cs < S.Cs)
    (hηc : EtaChoice S.cs S.Cs S.c₁ c₂ S.η) (hpos : 2 * S.cs⁻¹ * S.Cs * S.η < 1)
    (hη3 : 1 + 3 * S.η ≤ S.Cs / S.cs) {r : ℝ} (hr : 0 < r) {U : ℂ → ℂ → Set ℂ}
    {fb gb : Set ℂ → TestC} (hU : IsTubeFam S U r) (hB : IsBumpChoice S U fb gb r) {g : DistC}
    {x y : ℂ} (hx : x ∈ sphere (0 : ℂ) (2 * r)) (hy : y ∈ sphere (0 : ℂ) (2 * r))
    (hxy : S.δ * r ≤ ‖x - y‖)
    (hlen : (D g).IsLength) (hlen' : (D' g).IsLength)
    (hW : ∀ a b : ℂ, ENNReal.ofReal ((D (subTest g (bumpPhi S U fb gb r x y))).1 (a, b)) =
      weylScale S.ξ (-testCont (bumpPhi S U fb gb r x y)) (D g) a b)
    (hW' : ∀ a b : ℂ, ENNReal.ofReal ((D' (subTest g (bumpPhi S U fb gb r x y))).1 (a, b)) =
      weylScale S.ξ (-testCont (bumpPhi S U fb gb r x y)) (D' g) a b)
    (hbl₀ : BilipAt D D' S.cs S.Cs g)
    (hbl₁ : BilipAt D D' S.cs S.Cs (subTest g (bumpPhi S U fb gb r x y)))
    {u v : ℂ} (hu : u ∈ (annulus 0 ((1 - 4 * S.ρ) * r) ((1 + 4 * S.ρ) * r) : Set ℂ))
    (hv : v ∈ (annulus 0 ((1 - 4 * S.ρ) * r) ((1 + 4 * S.ρ) * r) : Set ℂ))
    (h1 : S.b * r ≤ ‖u - v‖) (h2 : (D' g).1 (u, v) ≤ S.c₁ * (D g).1 (u, v))
    (h3 : ENNReal.ofReal ((D' g).1 (u, v)) ≤
      ENNReal.ofReal ((S.cs / S.Cs) ^ 2) * setDist (D' g) {u} (sphere u (4 * S.ρ * r)))
    (h4 : UniqueGeodIn (D' g) u v (U x y))
    (h3u : ∀ w ∈ nearComp (U x y) (20 * S.ε₀ * r) u,
      (D' g).internal (U x y) u w ≤ ENNReal.ofReal (S.η * (D' g).1 (u, v)))
    (h3v : ∀ w ∈ nearComp (U x y) (20 * S.ε₀ * r) v,
      (D' g).internal (U x y) v w ≤ ENNReal.ofReal (S.η * (D' g).1 (u, v)))
    {p q : ℂ} (hp : p ∈ nearComp (U x y) (20 * S.ε₀ * r) u)
    (hq : q ∈ nearComp (U x y) (20 * S.ε₀ * r) v) :
    p ∈ ball (0 : ℂ) (3 / 2 * r) ∧ q ∈ ball (0 : ℂ) (3 / 2 * r) ∧
      (S.b - 40 * S.ε₀) * r ≤ ‖p - q‖ ∧
      (D' (subTest g (bumpPhi S U fb gb r x y))).1 (p, q) ≤
        c₂ * (D (subTest g (bumpPhi S U fb gb r x y))).1 (p, q) ∧
      ENNReal.ofReal ((D' (subTest g (bumpPhi S U fb gb r x y))).1 (p, q)) ≤
        ENNReal.ofReal (S.cs / S.Cs) *
          setDist (D' (subTest g (bumpPhi S U fb gb r x y))) {p} (sphere 0 (3 * r)) := by
  have hS' := hS
  obtain ⟨-, -, hb, hρ, hε, -⟩ := hS
  obtain ⟨hUo, -, -, -, -, -⟩ := hU x hx y hy hxy
  -- positions
  have hu' : ‖u‖ < (1 + 4 * S.ρ) * r := by simpa using hu.2
  have hv' : ‖v‖ < (1 + 4 * S.ρ) * r := by simpa using hv.2
  have hpb : ‖p - u‖ < 20 * S.ε₀ * r := by
    have := (connectedComponentIn_subset _ _ hp).2
    rwa [mem_ball, dist_eq_norm] at this
  have hqb : ‖q - v‖ < 20 * S.ε₀ * r := by
    have := (connectedComponentIn_subset _ _ hq).2
    rwa [mem_ball, dist_eq_norm] at this
  have hεs : S.ε₀ < 1 / 10000 := by have := hε.2; have := hb.2; linarith
  have hpn := norm_le_norm_add_norm_sub' p u
  have hqn := norm_le_norm_add_norm_sub' q v
  have hεr : S.ε₀ * r < 1 / 10000 * r := mul_lt_mul_of_pos_right hεs hr
  have hρr : S.ρ * r < 1 / 100 * r := mul_lt_mul_of_pos_right hρ.2 hr
  have hpB : p ∈ ball (0 : ℂ) (3 / 2 * r) := by
    rw [mem_ball, dist_zero_right]; nlinarith
  have hqB : q ∈ ball (0 : ℂ) (3 / 2 * r) := by
    rw [mem_ball, dist_zero_right]; nlinarith
  have hsep : (S.b - 40 * S.ε₀) * r ≤ ‖p - q‖ := by
    have e : u - v = (u - p) + (p - q) + (q - v) := by ring
    have := norm_add₃_le (a := u - p) (b := p - q) (c := q - v)
    rw [← e, norm_sub_rev u p] at this
    nlinarith
  -- the Weyl exponent bounds
  have hR : 0 < 4 * S.ρ * r := by have := hρ.1; positivity
  have hball := weylExp_ge_inner_m2m2 hS' hr hB hx hy hxy
    (ball_subset_inner_m2m2 (r := r) hS' hu')
  have hUb := weylExp_le_on_U_m2m2 hS' hB hx hy hxy
  have huv : u ≠ v := by
    intro h; rw [h, sub_self, norm_zero] at h1; nlinarith [hb.1]
  have hbl₀' : ∀ a b : ℂ, S.cs * (D g).1 (a, b) ≤ (D' g).1 (a, b) ∧
      (D' g).1 (a, b) ≤ S.Cs * (D g).1 (a, b) := hbl₀
  refine ⟨hpB, hqB, hsep, ?_, ?_⟩
  · exact gm_L5_11_uv hW hW' hlen hlen' hcs hcC hc₁ hηc hpos hbl₀' hbl₁ hUo hR huv h2 h3 h4
      (h3u p hp) (h3v q hq) hball hUb
  · refine gm_eq541 hW' hlen' hcs hcC hηc.1.le hη3 hUo hR huv (fun w hw => ?_) h3 h4
      (h3u p hp) (h3v q hq) hball hUb
    rw [mem_sphere, dist_zero_right] at hw
    have := norm_sub_norm_le w u
    nlinarith

end LQGMetric.GM
