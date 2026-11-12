/- Adapted from Leonardo Bonanno's lean-formalizations (https://github.com/leobon12/lean-formalizations),
   source module LQGMetric.Papers.DZZ.S5L53H2 at commit fdb5cad; only the module paths of local imports are changed. -/
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53H1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5WallSim1
import LatticeProb.Bonanno.LQGMetric.Papers.DZZ.S5L53F2

/-!
# DZZ Lemma 5.3, the `d_i` comparison, part 2: the chain at one scale (P2-DZZ53H)

DZZ arXiv:1807.00422, `LBM_LGDarXiv.tex`, l. 2380–2385: with high probability
`d_i ≤ e^{(log δ⁻¹)^{0.92}} D̃^{(i)} ≤ e^{(log δ⁻¹)^{0.94}} exp{E log D̃_δ(u,v)}`.
Here `d_i = D'^{K_i}_δ(w_i, w_{i+1})`, `K_i = 𝕍̃_{w_i,w_{i+1}}`, `K = 𝕍̃_{u,v}`, and the steps are
(`l53h_di_chain`, for one `δ`, explicit scales):

1. P3.2 lower half (DZZ l. 1159–1169) in the form of its two ingredients: (eq-280318b)
   (`approxLGDIn_mono`) and the ball cover (DZZ l. 1164–1168, `L32BallCoverOn`, proved for
   cells meeting a closed wall: `l32BallCoverIn_dzzMuIn`):
   `d_i ≤ D'^{K_i}_{p32Up δ₁} ≤ 4 D^{K_i}_{δ₁}(w_i, w_{i+1})` once `p32Up δ₁ ≤ δ`
   (this avoids the walled Lemma 3.5 at the non-dyadic wall `K_i`; see the module doc of S5L53H3);
2. the similarity coupling `θ' : B̄₀ → K_i` (lem-scaling-coupling, l. 611–624; `l53h_tail`):
   `D^{K_i}_{δ₁}(w_i, w_{i+1}) ≼ D^{B̄₀}_{δ_a}(p₁, p₂)`, `δ_a = δ₁ e^{−λ}/‖a'‖`;
3. Corollary 3.9 at the dyadic wall `B̄₀` (l. 1235–1244): `D^{B̄₀}_{δ_a} ≤ F D^{B̄₀}_{δ_b}`;
4. the similarity coupling `θ : B̄₀ → K`: `D^{B̄₀}_{δ_b}(p₁, p₂) ≼ D^K_δ(u, v)`, `δ_b = δe^{λ}/‖a‖`.
Here `≼` is the comparison of tails up to `C e^{−λ²/C}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal

namespace LQGMetric
namespace DZZ

open WhiteNoise DyBox

lemma l53h_p₁_mem : (⟨5 / 16, 3 / 8⟩ : ℂ) ∈ wsimB₀.closedBox := by
  rw [wsimB₀_eq_tildeBox]; exact mem_tildeBox_left _ _

lemma l53h_p₂_mem : (⟨7 / 16, 3 / 8⟩ : ℂ) ∈ wsimB₀.closedBox := by
  rw [wsimB₀_eq_tildeBox]; exact mem_tildeBox_right _ _

lemma l53hA_norm_pos {u v : ℂ} (huv : u ≠ v) : 0 < ‖l53hA u v‖ :=
  norm_pos_iff.2 (l53hA_ne huv)

/-- `P A ≤ P Bᶜ + P C` when `A ∩ B ⊆ C`. -/
lemma l53h_split {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {A B C : Set Ω}
    (h : ∀ ω, ω ∈ B → ω ∈ A → ω ∈ C) : P A ≤ P Bᶜ + P C := by
  have hsub : A ⊆ Bᶜ ∪ C := fun ω hω => by
    by_cases hb : ω ∈ B
    · exact Or.inr (h ω hb hω)
    · exact Or.inl hb
  exact (measure_mono hsub).trans (measure_union_le _ _)

/-- **The `d_i` chain at one scale** (DZZ l. 2380–2385). -/
theorem l53h_di_chain {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {W : WNSpace → Ω → ℝ}
    (hW : IsWhiteNoise P W) {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) {u v : ℂ} (hu : u ∈ dzzVbar)
    (hv : v ∈ dzzVbar) (huv : u ≠ v) {i : ℕ} (hi : i < 9) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ lam : ℝ, 0 ≤ lam → ∀ δ δ₁ : ℝ, 0 < δ → 0 < δ₁ →
      p32Up δ₁ ≤ δ → ∀ F R : ℝ, 0 ≤ F → 0 ≤ R →
      P {ω | ENNReal.ofReal (4 * (F * R)) <
          ((approxLGDIn (tildeBox (l53W u v i) (l53W u v (i + 1))) γ W δ (l53W u v i)
            (l53W u v (i + 1)) ω : ℕ∞) : ℝ≥0∞)} ≤
        P {ω | ∀ x ∈ dzzV, ∀ y ∈ dzzV,
            approxLGDOn (cellsMeeting (tildeBox (l53W u v i) (l53W u v (i + 1)))) γ W
              (p32Up δ₁) x y ω ≤
            4 * lgdDZZ (dzzWall (tildeBox (l53W u v i) (l53W u v (i + 1))) (dzzMuIn γ W ω))
              δ₁ x y}ᶜ +
        ENNReal.ofReal (C₁ * Real.exp (-lam ^ 2 / C₁)) +
        P {ω | ¬ ((lgdDZZ (dzzWall wsimB₀.closedBox (dzzMuIn γ W ω))
              (δ₁ * Real.exp (-lam) / (‖l53hA u v‖ / 9)) ⟨5 / 16, 3 / 8⟩ ⟨7 / 16, 3 / 8⟩ : ℕ∞) :
                ℝ≥0∞) ≤
            ((lgdDZZ (dzzWall wsimB₀.closedBox (dzzMuIn γ W ω)) (δ * Real.exp lam / ‖l53hA u v‖)
              ⟨5 / 16, 3 / 8⟩ ⟨7 / 16, 3 / 8⟩ : ℕ∞) : ℝ≥0∞) * ENNReal.ofReal F} +
        ENNReal.ofReal (C₂ * Real.exp (-lam ^ 2 / C₂)) +
        P {ω | ENNReal.ofReal R <
          ((lgdDZZ (dzzWall (tildeBox u v) (dzzMuIn γ W ω)) δ u v : ℕ∞) : ℝ≥0∞)} := by
  set x := l53W u v i with hxdef
  set y := l53W u v (i + 1) with hydef
  have hx : x ∈ dzzVbar := l53W_mem_dzzVbar hu hv (by omega)
  have hy : y ∈ dzzVbar := l53W_mem_dzzVbar hu hv (by omega)
  have hxy : x ≠ y := l53W_ne huv i
  have hxV : x ∈ dzzV := (tildeBox_subset_dzzVXi hx hy hxy (mem_tildeBox_left x y)).1
  have hyV : y ∈ dzzV := (tildeBox_subset_dzzVXi hx hy hxy (mem_tildeBox_right x y)).1
  set a' := l53hA x y with ha'def
  set b' := l53hB x y with hb'def
  set a := l53hA u v with hadef
  set b := l53hB u v with hbdef
  have hna' : ‖a'‖ = ‖a‖ / 9 := l53hA_w_norm u v i
  have hapos : 0 < ‖a‖ := l53hA_norm_pos huv
  obtain ⟨C₁, hC₁, ht₁⟩ := l53h_tail hW hγ hγ2 (l53hA_ne hxy) (l53hA_norm_le hx hy)
    (by rw [l53h_sim_image hxy]; exact tildeBox_subset_dzzVXi hx hy hxy)
  obtain ⟨C₂, hC₂, ht₂⟩ := l53h_tail hW hγ hγ2 (l53hA_ne huv) (l53hA_norm_le hu hv)
    (by rw [l53h_sim_image huv]; exact tildeBox_subset_dzzVXi hu hv huv)
  refine ⟨C₁, C₂, hC₁, hC₂, fun lam hlam δ δ₁ hδ hδ₁ hup F R hF hR => ?_⟩
  set p₁ : ℂ := ⟨5 / 16, 3 / 8⟩
  set p₂ : ℂ := ⟨7 / 16, 3 / 8⟩
  set δa := δ₁ * Real.exp (-lam) / (‖a‖ / 9) with hδa
  set δb := δ * Real.exp lam / ‖a‖ with hδb
  have hδa0 : 0 < δa := by positivity
  have hδb0 : 0 < δb := by positivity
  -- step 1: (eq-280318b) and the ball cover
  have s1 : P {ω | ENNReal.ofReal (4 * (F * R)) <
        ((approxLGDIn (tildeBox x y) γ W δ x y ω : ℕ∞) : ℝ≥0∞)} ≤
      P {ω | ∀ x ∈ dzzV, ∀ y ∈ dzzV,
            approxLGDOn (cellsMeeting (tildeBox (l53W u v i) (l53W u v (i + 1)))) γ W
              (p32Up δ₁) x y ω ≤
            4 * lgdDZZ (dzzWall (tildeBox (l53W u v i) (l53W u v (i + 1))) (dzzMuIn γ W ω))
              δ₁ x y}ᶜ +
        P {ω | ENNReal.ofReal (F * R) <
          ((lgdDZZ (dzzWall (tildeBox x y) (dzzMuIn γ W ω)) δ₁ x y : ℕ∞) : ℝ≥0∞)} := by
    refine l53h_split fun ω hB hA => ?_
    simp only [mem_ofPred_eq] at hA hB ⊢
    by_contra hc
    push Not at hc
    refine absurd hA (not_lt.2 ?_)
    have h1 : approxLGDIn (tildeBox x y) γ W δ x y ω ≤
        4 * lgdDZZ (dzzWall (tildeBox x y) (dzzMuIn γ W ω)) δ₁ x y :=
      (approxLGDIn_mono _ γ W (p32Up_pos hδ₁).le hup x y ω).trans (hB x hxV y hyV)
    calc ((approxLGDIn (tildeBox x y) γ W δ x y ω : ℕ∞) : ℝ≥0∞)
        ≤ ((4 * lgdDZZ (dzzWall (tildeBox x y) (dzzMuIn γ W ω)) δ₁ x y : ℕ∞) : ℝ≥0∞) :=
          ENat.toENNReal_le.2 h1
      _ = 4 * ((lgdDZZ (dzzWall (tildeBox x y) (dzzMuIn γ W ω)) δ₁ x y : ℕ∞) : ℝ≥0∞) := by
          rw [ENat.toENNReal_mul]; rfl
      _ ≤ 4 * ENNReal.ofReal (F * R) := by gcongr
      _ = ENNReal.ofReal (4 * (F * R)) := by
          rw [ENNReal.ofReal_mul (p := 4) (by norm_num)]; norm_num
  -- step 2: the coupling `θ' : B̄₀ → K_i`
  have s2 := (ht₁ lam hlam p₁ l53h_p₁_mem p₂ l53h_p₂_mem δa hδa0 (ENNReal.ofReal (F * R))).1
  have e2 : ‖a'‖ * δa * Real.exp lam = δ₁ := by
    rw [hna', hδa]; field_simp; rw [← Real.exp_add]; simp
  rw [e2, l53h_sim_image hxy, l53h_sim_p₁, l53h_sim_p₂] at s2
  -- step 3: Corollary 3.9 at `B̄₀`
  have s3 : P {ω | ENNReal.ofReal (F * R) <
        ((lgdDZZ (dzzWall wsimB₀.closedBox (dzzMuIn γ W ω)) δa p₁ p₂ : ℕ∞) : ℝ≥0∞)} ≤
      P {ω | ¬ ((lgdDZZ (dzzWall wsimB₀.closedBox (dzzMuIn γ W ω)) δa p₁ p₂ : ℕ∞) : ℝ≥0∞) ≤
            ((lgdDZZ (dzzWall wsimB₀.closedBox (dzzMuIn γ W ω)) δb p₁ p₂ : ℕ∞) : ℝ≥0∞) *
              ENNReal.ofReal F} +
        P {ω | ENNReal.ofReal R <
          ((lgdDZZ (dzzWall wsimB₀.closedBox (dzzMuIn γ W ω)) δb p₁ p₂ : ℕ∞) : ℝ≥0∞)} := by
    have := l53h_split (P := P) (A := {ω | ENNReal.ofReal (F * R) <
        ((lgdDZZ (dzzWall wsimB₀.closedBox (dzzMuIn γ W ω)) δa p₁ p₂ : ℕ∞) : ℝ≥0∞)})
      (B := {ω | ((lgdDZZ (dzzWall wsimB₀.closedBox (dzzMuIn γ W ω)) δa p₁ p₂ : ℕ∞) : ℝ≥0∞) ≤
            ((lgdDZZ (dzzWall wsimB₀.closedBox (dzzMuIn γ W ω)) δb p₁ p₂ : ℕ∞) : ℝ≥0∞) *
              ENNReal.ofReal F})
      (C := {ω | ENNReal.ofReal R <
          ((lgdDZZ (dzzWall wsimB₀.closedBox (dzzMuIn γ W ω)) δb p₁ p₂ : ℕ∞) : ℝ≥0∞)})
      (fun ω hB hA => by
        simp only [mem_ofPred_eq] at hA hB ⊢
        by_contra hc
        push Not at hc
        refine absurd hA (not_lt.2 (hB.trans ?_))
        calc _ ≤ ENNReal.ofReal R * ENNReal.ofReal F := by gcongr
          _ = ENNReal.ofReal (F * R) := by rw [← ENNReal.ofReal_mul hR, mul_comm])
    simpa only [compl_ofPred] using this
  -- step 4: the coupling `θ : B̄₀ → K`
  have s4 := (ht₂ lam hlam p₁ l53h_p₁_mem p₂ l53h_p₂_mem δb hδb0 (ENNReal.ofReal R)).2
  have e4 : ‖a‖ * δb * Real.exp (-lam) = δ := by
    rw [hδb]; field_simp; rw [← Real.exp_add]; simp
  rw [e4, l53h_sim_image huv, l53h_sim_p₁, l53h_sim_p₂] at s4
  calc _ ≤ _ := s1
    _ ≤ _ := add_le_add le_rfl (s2.trans (add_le_add le_rfl (s3.trans (add_le_add le_rfl s4))))
    _ = _ := by ring

end DZZ
end LQGMetric
