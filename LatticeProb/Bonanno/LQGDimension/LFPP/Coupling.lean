/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGDimension.LFPP.Coupling at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGDimension.LFPP.CouplingAux3
import LatticeProb.Bonanno.LQGDimension.LFPP.CouplingAux4
import LatticeProb.Bonanno.LQGDimension.Gaussian.Basic

/-!
# Node `C36` (`Draft.CouplingAtPoints`): the coupling (3.6) at finitely many points

We prove `Blueprint.Draft.CouplingAtPoints` with the constant `C_ρ = Cb ρ`.

Strategy (deterministic Hilbert-space computation plus Gram gluing, all in finite dimensions).

1. **Joint kernel** (`CouplingAux3`).  On indices `(s, false)` (band field `G_{ε,ρ}(s)`) and
   `(s, true)` (circle average `h_ε(s)`) the kernel `Kc ε ρ i j = ∫_0^∞ P_t(i,j) dt/t` pairs, at
   each scale `t`, the signed measures `1_{(ε,ρ]}(t) δ_s` and `σ_{s,ε} - σ_{0,1}` against the
   Gaussian kernel `e^{-|x-y|²/(4t²)}`.  Writing that kernel as a Fourier integral against the
   standard Gaussian on `ℂ ≅ ℝ²` makes `Kc` positive semidefinite (`Kc_psd`).  Its band block
   is `bandCov` (`Kc_ff`), and by the heat-kernel (Frullani) representation of `-log` together
   with the circle averages `⨍ log|x - ·| = log max(r, |x - c|)` its circle block is
   `gffCircleCov` (`Kc_tt`).
2. **Uniform bound** (`Kc_diag_bound`).  `‖k_s - b_s‖² = ∫_0^∞ Q_t dt/t` with `Q_t` bounded
   on `(0, ε]` by the circle self-pairings (controlled by the heat representation of
   `log ε`), on `(ε, ρ]` by `ε²/t² +` a unit-circle term, and on `(ρ, ∞)` by `C_ρ/t²`
   (zero mass).
3. **Gluing** (`CouplingAux4.glue`).  Realise `Kc` by Gram vectors (`exists_gram_of_psdOn`), and
   transport the given band realisation `w` onto the band vectors by a linear isometry of an
   ambient Euclidean space (`LinearIsometry.extend`).
-/

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace LQGDimension

open Coupling

/-- **Node `C36`: the coupling (3.6) at finitely many points.** -/
theorem couplingAtPoints : Blueprint.Draft.CouplingAtPoints := by
  intro ρ _hρ
  refine ⟨Cb ρ, fun ε hε S hS d₁ w hw => ?_⟩
  obtain ⟨hε0, hερ⟩ := hε
  classical
  set F : Finset (ℂ × Bool) := S ×ˢ Finset.univ with hF
  obtain ⟨x, hx⟩ := exists_gram_of_psdOn F (Kc ε ρ) (Kc_psd ρ hε0 F)
  have hmem : ∀ s ∈ S, ∀ b : Bool, (s, b) ∈ F := fun s hs b =>
    Finset.mem_product.2 ⟨hs, Finset.mem_univ _⟩
  obtain ⟨d, ι, J, hιJ⟩ := glue S w (fun s => x (s, false)) (fun s hs s' hs' => by
    rw [hw s hs s' hs', hx _ (hmem s hs false) _ (hmem s' hs' false), Kc_ff hε0 hερ.le])
  refine ⟨d, ι, fun s => J (x (s, true)), fun s hs s' hs' => ?_, fun s hs => ?_⟩
  · rw [LinearIsometry.inner_map_map, hx _ (hmem s hs true) _ (hmem s' hs' true), Kc_tt ρ hε0]
  · rw [hιJ s hs, ← map_sub, LinearIsometry.norm_map, norm_sub_sq_real,
      ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
      hx _ (hmem s hs true) _ (hmem s hs true), hx _ (hmem s hs true) _ (hmem s hs false),
      hx _ (hmem s hs false) _ (hmem s hs false), Kc_comm ε ρ (s, true) (s, false)]
    have := Kc_diag_bound hε0 hερ s (hS s hs)
    linarith

end LQGDimension
