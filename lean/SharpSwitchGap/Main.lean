import SharpSwitchGap.SharpAssembly
import SharpSwitchGap.SharpComparison
import OAI.Probability.SwitchChain.SwitchTV

namespace SharpSwitchGap

noncomputable section
open scoped BigOperators RealInnerProductSpace
open OAI.Problem315 PairResampling
attribute [local instance] Classical.propDecidable

theorem twice_variance_le_generator {n : ℕ} {d : Fin n → ℕ}
    (hn : 3 ≤ n) (hgraph : Graphical n d) (f : GraphState n d → ℝ) :
    2 * uniformVariance n d f ≤
      ⟪WithLp.toLp 2 f, generator n d (WithLp.toLp 2 f)⟫ / (stateCount n d : ℝ) := by
  let : Nonempty (GraphState n d) := hgraph
  have hN : (0 : ℝ) < (stateCount n d : ℝ) := by
    exact_mod_cast (show 0 < stateCount n d by
      simpa only [stateCount, allGraphStates, Finset.card_univ] using
        (Fintype.card_pos (α := GraphState n d)))
  let v : StateSpace n d := WithLp.toLp 2 f
  let c : ℝ := uniformAverage n d f
  let k : StateSpace n d := WithLp.toLp 2 (fun _ : GraphState n d => c)
  let x : StateSpace n d := v - k
  have hx : (∑ G : GraphState n d, x G) = 0 := by
    simp only [x, v, k, PiLp.sub_apply]
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    change (∑ G : GraphState n d, f G) - (Fintype.card (GraphState n d) : ℝ) *
      ((∑ G : GraphState n d, f G) / (stateCount n d : ℝ)) = 0
    have hcard : (Fintype.card (GraphState n d) : ℝ) = stateCount n d := rfl
    rw [hcard]
    field_simp
    ring
  have hk : generator n d k = 0 := generator_constant c
  have hgen : generator n d x = generator n d v := by
    change generator n d (v - k) = generator n d v
    rw [map_sub, hk, sub_zero]
  have horth : ⟪k, generator n d v⟫ = 0 := by
    have h := generator_isSymmetric (n := n) (d := d) k v
    change ⟪generator n d k, v⟫ = ⟪k, generator n d v⟫ at h
    rw [hk, inner_zero_left] at h
    exact h.symm
  have henergy : ⟪x, generator n d x⟫ = ⟪v, generator n d v⟫ := by
    rw [hgen]
    change ⟪v - k, generator n d v⟫ = _
    rw [inner_sub_left, horth, sub_zero]
  have hnorm : ‖x‖ ^ 2 = ∑ G ∈ allGraphStates n d, (f G - c) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, state_inner]
    simp only [x, v, k, PiLp.sub_apply, allGraphStates, pow_two]
  have hp := SharpAssembly.centered_poincare hn x hx
  rw [henergy, hnorm] at hp
  change 2 * ((∑ G ∈ allGraphStates n d, (f G - c) ^ 2) / (stateCount n d : ℝ)) ≤
    ⟪v, generator n d v⟫ / (stateCount n d : ℝ)
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right hp (le_of_lt hN)

theorem twice_variance_le_laplacian {n : ℕ} {d : Fin n → ℕ}
    (hn : 3 ≤ n) (hgraph : Graphical n d) (f : GraphState n d → ℝ) :
    2 * uniformVariance n d f ≤ uniformInner n d f (switchLaplacian n d f) := by
  apply (twice_variance_le_generator hn hgraph f).trans
  exact div_le_div_of_nonneg_right
    (SharpComparison.generator_le_laplacian (WithLp.toLp 2 f)) (Nat.cast_nonneg _)

theorem switch_chain_gap :
    ∀ (n : Nat) (d : Fin n → Nat), 4 ≤ n → (∀ v, d v ≤ n - 1) →
      Graphical n d → 1 < stateCount n d →
      hasSpectralGapAtLeast n d ((1 : ℝ) / (6 * (Nat.choose n 4 : ℝ))) := by
  intro n d hn _hd hgraph _hmany f
  have hc : (0 : ℝ) < (Nat.choose n 4 : ℝ) := by exact_mod_cast Nat.choose_pos hn
  have hd6 : (0 : ℝ) < 6 * (Nat.choose n 4 : ℝ) := by positivity
  have hd12 : (0 : ℝ) < 12 * (Nat.choose n 4 : ℝ) := by positivity
  rw [dirichletEnergy_eq_switchLaplacian (fun G => switchKernel_row_sum hn G)]
  rw [div_mul_eq_mul_div, one_mul]
  apply (div_le_div_iff₀ hd6 hd12).mpr
  have h := mul_le_mul_of_nonneg_right
    (twice_variance_le_laplacian (by omega) hgraph f) hd6.le
  nlinarith only [h]

theorem switch_chain_tv_bound :
    ∀ (n : Nat) (d : Fin n → Nat), 4 ≤ n → (∀ v, d v ≤ n - 1) →
      Graphical n d → 1 < stateCount n d → ∀ (t : Nat) (G : GraphState n d),
      tvDistanceFrom n d t G ≤ Real.sqrt (stateCount n d : ℝ) / 2 *
        Real.exp (- (t : ℝ) / (6 * (Nat.choose n 4 : ℝ))) := by
  intro n d hn hd hgraph hmany t G
  have hrows : ∀ G : GraphState n d, ∑ H, switchKernel n d G H = 1 := by
    intro H
    simpa only [allGraphStates] using switchKernel_row_sum hn H
  have hc : (1 : ℝ) ≤ (Nat.choose n 4 : ℝ) := by exact_mod_cast Nat.choose_pos hn
  have hden : (1 : ℝ) ≤ 6 * (Nat.choose n 4 : ℝ) :=
    one_le_mul_of_one_le_of_one_le (by norm_num) hc
  have hγ : (1 : ℝ) / (6 * (Nat.choose n 4 : ℝ)) ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hden
  have h := switch_tv_bound_of_gap n d hrows hγ (switch_chain_gap n d hn hd hgraph hmany) t G
  convert h using 1
  congr 2
  ring

end
end SharpSwitchGap
