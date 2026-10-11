import SharpSwitchGap.JohnsonTransport
import OAI.Probability.SwitchChain.PairLocalComparison
import OAI.Probability.SwitchChain.PairSwitchComparison

/- Graph transfer of h_a ≤ J_a/2, using upstream's exact pair-switch multiplicity.
The fiber/proposal injection follows PairLocalComparison at the pinned commit. -/

namespace SharpSwitchGap.SharpComparison

noncomputable section
open scoped BigOperators RealInnerProductSpace
open OAI.Problem315 PairFiber PairResampling
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

theorem pair_comparison (i j : Fin n) (hij : i ≠ j) (f : StateSpace n d) :
    ⟪f, fluctuation n d {i,j} f⟫ ≤ (1 / 2 : ℝ) *
      ∑ G : GraphState n d, f G * pairSwitchLaplacian n d {i,j} (fun H => f H) G := by
  let E : GraphState n d → ℝ := fun H =>
    ∑ p ∈ allProposals n,
      if ({i,j} : Finset (Fin n)) ∈ SwitchPairFiber.crossingPairs p then
        (f H - f (proposalState H p)) ^ 2 else 0
  have hlocal (G : GraphState n d) :
      (∑ T : Assignment G.val i j,
        (f ((stateFiberEquiv G i j hij).symm T).val - expectation n d {i,j} f G) ^ 2) ≤
        (1 / 4 : ℝ) * ∑ T : Assignment G.val i j, E ((stateFiberEquiv G i j hij).symm T).val := by
    let R : Assignment G.val i j → GraphState n d :=
      fun T => ((stateFiberEquiv G i j hij).symm T).val
    have hcard : Fintype.card (Assignment G.val i j) =
        Nat.choose (singletonSet G.val i j).card (leftSet G.val i j).card := by
      rw [← Nat.card_eq_fintype_card]
      exact assignment_natCard G.val i j
    have hmean := expectation_eq_assignment_average G i j hij f
    rw [← hcard] at hmean
    have hvar := Johnson.variance_le_swaps (assignmentSliceEquiv G.val i j)
      (fun T => f (R T))
    rw [← hmean] at hvar
    apply hvar.trans
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Finset.sum_le_sum
    intro T _
    exact assignment_swap_squared_differences_le_proposals G i j hij T (fun H => f H)
  have h := inner_fluctuation_le_of_assignment_sum_bound i j hij f E (1/4) hlocal
  calc
    _ ≤ (1 / 4 : ℝ) * ∑ G : GraphState n d, E G := h
    _ = _ := by
      rw [PairSquaredEnergy.pairSwitchLaplacian_energy]
      dsimp only [E]
      ring

theorem generator_le_laplacian (f : StateSpace n d) :
    ⟪f, generator n d f⟫ ≤
      ∑ G : GraphState n d, f G * switchLaplacian n d (fun H => f H) G := by
  have hlocal : ∀ a ∈ pairs n,
      ⟪f, fluctuation n d a f⟫ ≤ (1 / 2 : ℝ) *
        ∑ G : GraphState n d, f G * pairSwitchLaplacian n d a (fun H => f H) G := by
    intro a ha
    obtain ⟨i,j,hij,rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp ha).2
    exact pair_comparison i j hij f
  rw [generator_apply, inner_sum]
  apply (Finset.sum_le_sum hlocal).trans_eq
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  simp only [pairs, sum_pairSwitchLaplacian]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro G _
  ring

end
end SharpSwitchGap.SharpComparison
