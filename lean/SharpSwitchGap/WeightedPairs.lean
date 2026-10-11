import SharpSwitchGap.WeightedCell
import SharpSwitchGap.WeightedGlobalBudget

namespace SharpSwitchGap.WeightedPairs

noncomputable section
open scoped BigOperators RealInnerProductSpace
open OAI.Problem315 PairResampling
open WeightedError WeightedFiberBudget
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

def pairError (a b : Finset (Fin n)) (f : StateSpace n d) : StateSpace n d :=
  if ha : a.card = 2 then
    weightedRightPair (CrossToggle.first ⟨a,ha⟩) (CrossToggle.second ⟨a,ha⟩) b f
  else 0

theorem pairError_of_pair (a b : Finset (Fin n)) (ha : a.card = 2) (f : StateSpace n d) :
    pairError a b f = weightedRightPair
      (CrossToggle.first ⟨a,ha⟩) (CrossToggle.second ⟨a,ha⟩) b f := by
  simp only [pairError, dite_eq_left ha]

theorem pairError_zero (a b : Finset (Fin n)) (hab : ¬ Disjoint a b) (f : StateSpace n d) :
    pairError a b f = 0 := by
  by_cases ha : a.card = 2
  · rw [pairError_of_pair a b ha]
    apply weightedRightPair_zero
    rwa [← CrossToggle.pair_eq ⟨a,ha⟩]
  · simp only [pairError, dite_eq_right ha]

theorem sum_disjoint_error (a : Finset (Fin n)) (f : StateSpace n d) :
    (∑ b ∈ pairs n, if Disjoint a b then ‖pairError a b f‖ ^ 2 else 0) =
      ∑ b ∈ pairs n, ‖pairError a b f‖ ^ 2 := by
  apply Finset.sum_congr rfl
  intro b _
  by_cases hab : Disjoint a b
  · rw [ite_eq_left hab]
  · rw [ite_eq_right hab, pairError_zero a b hab]
    simp

theorem pair_budget (a : Finset (Fin n)) (ha : a ∈ pairs n) (f : StateSpace n d) :
    (∑ b ∈ pairs n, ‖pairError a b f‖ ^ 2) + ‖fluctuation n d a f‖ ^ 2 ≤
      ∑ b ∈ pairs n, ‖CrossToggle.gain a b f‖ ^ 2 := by
  have hca : a.card = 2 := (Finset.mem_powersetCard.mp ha).2
  let A : CrossToggle.VertexPair n := ⟨a,hca⟩
  have h := pair_budget_named (CrossToggle.first A) (CrossToggle.second A)
    (CrossToggle.first_ne_second A) f
  rw [← CrossToggle.pair_eq A] at h
  simpa only [pairError_of_pair a _ hca] using h

theorem interaction (f : StateSpace n d)
    (a : Finset (Fin n)) (ha : a ∈ pairs n)
    (b : Finset (Fin n)) (hb : b ∈ pairs n) (hab : Disjoint a b) :
    2 * ‖CrossToggle.gain a b f‖ ^ 2 - ‖pairError a b f‖ ^ 2 - ‖pairError b a f‖ ^ 2 ≤
      2 * ⟪fluctuation n d a f, fluctuation n d b f⟫ := by
  have hca : a.card = 2 := (Finset.mem_powersetCard.mp ha).2
  have hcb : b.card = 2 := (Finset.mem_powersetCard.mp hb).2
  let A : CrossToggle.VertexPair n := ⟨a,hca⟩
  let B : CrossToggle.VertexPair n := ⟨b,hcb⟩
  have hA : a = {CrossToggle.first A,CrossToggle.second A} := CrossToggle.pair_eq A
  have hB : b = {CrossToggle.first B,CrossToggle.second B} := CrossToggle.pair_eq B
  have hfour := CrossToggle.endpoints_distinct A B hab
  have hg : CrossToggle.gain (d := d) a b = SwitchFlip.projection (CrossToggle.crossProposal
      (CrossToggle.first A) (CrossToggle.second A) (CrossToggle.first B) (CrossToggle.second B) hfour) := by
    rw [CrossToggle.gain_of_pairs a b hca hcb]
    exact CrossToggle.pairProjection_of_disjoint A B hab
  have hR : pairError a b f = weightedProjection
      (CrossToggle.first A) (CrossToggle.second A) (CrossToggle.first B) (CrossToggle.second B) f := by
    rw [pairError_of_pair a b hca, hB]
    exact weightedRightPair_pair _ _ _ _ (CrossToggle.first_ne_second A) (CrossToggle.first_ne_second B) f
  have hS : pairError b a f = weightedProjection
      (CrossToggle.first B) (CrossToggle.second B) (CrossToggle.first A) (CrossToggle.second A) f := by
    rw [pairError_of_pair b a hcb, hA]
    exact weightedRightPair_pair _ _ _ _ (CrossToggle.first_ne_second B) (CrossToggle.first_ne_second A) f
  rw [hg,hR,hS]
  have h := WeightedCell.actual_named_interaction _ _ _ _ hfour f
  rw [← norm_sq, ← norm_sq] at h
  simpa only [← hA, ← hB] using h

end
end SharpSwitchGap.WeightedPairs
