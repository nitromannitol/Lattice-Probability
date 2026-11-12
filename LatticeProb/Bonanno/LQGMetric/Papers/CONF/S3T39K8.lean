/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.CONF.S3T39K8 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Topo.ArcDisconnect
import LatticeProb.Bonanno.LQGMetric.Complex.JordanMapCurve

/-!
# CONF Theorem 3.9, packet J6d, node O2: chains of rational balls

Gwynne–Miller, *Confluence of geodesics in LQG* (arXiv:1905.00381), `confluence-final.tex`,
C:1586 (the centres `x_{k,i}` and the event that `B_{ε_k 𝕣}(x_{k,i})` disconnects `I_k^i` from
`∞`). For the Effros-measurability of these objects (node O2 of P2-T39K5) the uncountable path
quantifier of `DisconnectsFromInfty` is replaced by countable data: finite chains of rational
balls whose closures avoid `K ∪ B̄_a(c)`.

* `k8G p l p'`: the list `l` of rational balls is a chain from `p` to `p'`;
* `k8G_trans`, `k8G_symm`, **`k8G_joinedIn`** (a chain inside `O` gives a path in `O`),
  **`k8_preconn`** (two points of a preconnected set covered by admissible balls are joined by an
  admissible chain; `IsPreconnected.induction₂'`);
* `k8Good K c a b`: the closure of the ball `b` avoids `K ∪ B̄_a(c)`, in a form that only uses hit
  events of `K` (`k8Good_subset`, `k8_exists_good`).

Own elementary argument (CONF gives none; standard chain-of-balls description of connectivity in
open sets).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric Filter Topology

namespace LQGMetric.CONF

/-- a rational ball: centre `(b.1, b.2.1)`, radius `b.2.2` -/
abbrev K8B := ℚ × ℚ × ℚ

def k8C (b : K8B) : ℂ := ⟨(b.1 : ℝ), (b.2.1 : ℝ)⟩

def k8R (b : K8B) : ℝ := (b.2.2 : ℝ)

/-- the open ball of `b` -/
def k8Ball (b : K8B) : Set ℂ := ball (k8C b) (k8R b)

/-- `l` is a chain of balls from `p` to `p'` -/
def k8G : ℂ → List K8B → ℂ → Prop
  | _, [], _ => False
  | p, b :: l, p' => p ∈ k8Ball b ∧ (p' ∈ k8Ball b ∨ ∃ z ∈ k8Ball b, k8G z l p')

theorem k8G_single {p p' : ℂ} {b : K8B} (hp : p ∈ k8Ball b) (hp' : p' ∈ k8Ball b) :
    k8G p [b] p' := ⟨hp, Or.inl hp'⟩

theorem k8G_trans {p z p' : ℂ} {l l' : List K8B} (h₁ : k8G p l z) (h₂ : k8G z l' p') :
    ∃ l'' : List K8B, (∀ b ∈ l'', b ∈ l ∨ b ∈ l') ∧ k8G p l'' p' := by
  induction l generalizing p with
  | nil => exact h₁.elim
  | cons b l ih =>
    obtain ⟨hp, hz | ⟨z₁, hz₁, h₁'⟩⟩ := h₁
    · refine ⟨b :: l', fun b' hb' => ?_, hp, Or.inr ⟨z, hz, h₂⟩⟩
      rcases List.mem_cons.1 hb' with rfl | hb'
      · exact Or.inl List.mem_cons_self
      · exact Or.inr hb'
    · obtain ⟨l'', hl'', h''⟩ := ih h₁'
      refine ⟨b :: l'', fun b' hb' => ?_, hp, Or.inr ⟨z₁, hz₁, h''⟩⟩
      rcases List.mem_cons.1 hb' with rfl | hb'
      · exact Or.inl List.mem_cons_self
      · rcases hl'' b' hb' with h | h
        · exact Or.inl (List.mem_cons_of_mem _ h)
        · exact Or.inr h

/-- **a chain of balls inside `O` gives a path in `O`** -/
theorem k8G_joinedIn {O : Set ℂ} {p p' : ℂ} {l : List K8B} (hl : ∀ b ∈ l, k8Ball b ⊆ O)
    (h : k8G p l p') : JoinedIn O p p' := by
  induction l generalizing p with
  | nil => exact h.elim
  | cons b l ih =>
    have hb : k8Ball b ⊆ O := hl b List.mem_cons_self
    have hconv : ∀ u ∈ k8Ball b, ∀ v ∈ k8Ball b, JoinedIn O u v := fun u hu v hv =>
      ((convex_ball _ _).isPathConnected ⟨u, hu⟩).joinedIn u hu v hv |>.mono hb
    obtain ⟨hp, hp' | ⟨z, hz, h'⟩⟩ := h
    · exact hconv p hp p' hp'
    · exact (hconv p hp z hz).trans (ih (fun b' hb' => hl b' (List.mem_cons_of_mem _ hb')) h')

/-- **two points of a preconnected set covered by admissible balls are joined by an admissible
chain** -/
theorem k8_preconn {s : Set ℂ} (hs : IsPreconnected s) (Gd : K8B → Prop)
    (hcov : ∀ x ∈ s, ∃ b, Gd b ∧ x ∈ k8Ball b) {x y : ℂ} (hx : x ∈ s) (hy : y ∈ s) :
    ∃ l : List K8B, (∀ b ∈ l, Gd b) ∧ k8G x l y := by
  refine hs.induction₂' (fun u v => ∃ l : List K8B, (∀ b ∈ l, Gd b) ∧ k8G u l v)
    (fun u hu => ?_) (fun u v w _ _ _ ⟨l₁, hl₁, h₁⟩ ⟨l₂, hl₂, h₂⟩ => ?_) hx hy
  · obtain ⟨b, hb, hub⟩ := hcov u hu
    have : ∀ᶠ v in 𝓝[s] u, v ∈ k8Ball b :=
      mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hub)
    filter_upwards [this] with v hv
    exact ⟨⟨[b], by simpa using hb, k8G_single hub hv⟩, ⟨[b], by simpa using hb, k8G_single hv hub⟩⟩
  · obtain ⟨l'', hl'', h''⟩ := k8G_trans h₁ h₂
    exact ⟨l'', fun b hb => (hl'' b hb).elim (hl₁ b) (hl₂ b), h''⟩

/-- the ball `b` has closure avoiding `K ∪ B̄_a(c)` (stated through hit events of `K`) -/
def k8Good (K : Set ℂ) (c : ℂ) (a : ℝ) (b : K8B) : Prop :=
  0 < k8R b ∧ (∃ j : ℕ, ¬ (K ∩ ball (k8C b) (k8R b + 1 / ((j : ℝ) + 1))).Nonempty) ∧
    k8R b + a < dist (k8C b) c

theorem k8Good_subset {K : Set ℂ} {c : ℂ} {a : ℝ} {b : K8B} (hb : k8Good K c a b) :
    k8Ball b ⊆ (K ∪ closedBall c a)ᶜ := by
  obtain ⟨-, ⟨j, hj⟩, hd⟩ := hb
  intro w hw
  rw [k8Ball, mem_ball] at hw
  simp only [mem_compl_iff, mem_union, mem_closedBall, not_or, not_le]
  refine ⟨fun hwK => hj ⟨w, hwK, ?_⟩, ?_⟩
  · rw [mem_ball]
    have : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
    linarith
  · have := dist_triangle (k8C b) w c
    rw [dist_comm] at hw
    linarith

/-- rational approximation of a complex number -/
theorem k8_exists_rat (x : ℂ) {ε : ℝ} (hε : 0 < ε) : ∃ q : ℚ × ℚ,
    dist (⟨(q.1 : ℝ), (q.2 : ℝ)⟩ : ℂ) x < ε := by
  obtain ⟨r₁, h₁, h₁'⟩ := exists_rat_btwn (show x.re - ε / 2 < x.re by linarith)
  obtain ⟨r₂, h₂, h₂'⟩ := exists_rat_btwn (show x.im - ε / 2 < x.im by linarith)
  refine ⟨(r₁, r₂), ?_⟩
  rw [dist_eq_norm]
  refine (Complex.norm_le_abs_re_add_abs_im _).trans_lt ?_
  simp only [Complex.sub_re, Complex.sub_im]
  rw [abs_of_neg (by linarith), abs_of_neg (by linarith)]
  linarith

/-- **admissible balls around points of the open set `(K ∪ B̄_a(c))ᶜ`**, of any small radius -/
theorem k8_exists_good {K : Set ℂ} (hK : IsClosed K) {c : ℂ} {a : ℝ} {x : ℂ} (hxK : x ∉ K)
    (hxc : a < dist x c) {ε' : ℝ} (hε' : 0 < ε') :
    ∃ b, k8Good K c a b ∧ x ∈ k8Ball b ∧ k8R b < ε' := by
  obtain ⟨ε₀, hε₀, hε₀K⟩ := Metric.isOpen_iff.1 hK.isOpen_compl x hxK
  set ε := min (min ε₀ (dist x c - a)) ε' with hεdef
  have hε : 0 < ε := lt_min (lt_min hε₀ (by linarith)) hε'
  have hε1 : ε ≤ ε₀ := (min_le_left _ _).trans (min_le_left _ _)
  have hε2 : ε ≤ dist x c - a := (min_le_left _ _).trans (min_le_right _ _)
  have hε3 : ε ≤ ε' := min_le_right _ _
  obtain ⟨q, hq⟩ := k8_exists_rat x (show 0 < ε / 8 by linarith)
  obtain ⟨ρ, hρ₁, hρ₂⟩ := exists_rat_btwn (show ε / 8 < ε / 4 by linarith)
  obtain ⟨j, hj⟩ := exists_nat_one_div_lt (show 0 < ε / 4 by linarith)
  set b : K8B := (q.1, q.2, ρ)
  have hC : k8C b = ⟨(q.1 : ℝ), (q.2 : ℝ)⟩ := rfl
  have hR : k8R b = ρ := rfl
  refine ⟨b, ⟨by rw [hR]; linarith, ⟨j, ?_⟩, ?_⟩, ?_, by rw [hR]; linarith⟩
  · rintro ⟨w, hwK, hw⟩
    refine hε₀K ?_ hwK
    rw [mem_ball] at hw ⊢
    have := dist_triangle w (k8C b) x
    rw [hC] at this hw; rw [hR] at hw
    linarith
  · rw [hR, hC]
    have := dist_triangle x (⟨(q.1 : ℝ), (q.2 : ℝ)⟩ : ℂ) c
    rw [dist_comm] at hq
    linarith
  · rw [k8Ball, mem_ball, hC, hR, dist_comm]; linarith

end LQGMetric.CONF
