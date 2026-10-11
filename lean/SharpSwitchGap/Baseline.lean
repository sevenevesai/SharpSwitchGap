import OAI.Probability.SwitchChain.Main
import SharpSwitchGap.Main
import SharpSwitchGap.Statement

/-
B0: the three types below are verbatim from the pinned Comparator target,
with local theorem names. The definitions are imported from the unmodified
solution and compared against the Comparator by sync_vendor.py.
Upstream: openai-math#131, adc7f1241b42e322a6451854ab7e4b4c146bf78a, Apache-2.0.
The B4 contracts below separately check the sharp endpoints against Statement.lean.
-/

namespace SharpSwitchGap.Baseline

open OAI.Problem315

theorem comparator_main :
    ∀ (n : Nat) (d : Fin n → Nat), 4 ≤ n → (∀ v, d v ≤ n - 1) → Graphical n d → ((∃ h : (∃ t : Nat, MixedAt n d t), mixingTime n d h ≤ 2 * n ^ 8) ∧ (stateCount n d = 1 → (MixedAt n d 0 ∧ ∀ h : (∃ t : Nat, MixedAt n d t), mixingTime n d h = 0)) ∧ (1 < stateCount n d → hasSpectralGapAtLeast n d ((1 : ℝ) / (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ))))) := by
  exact switch_chain_main

theorem comparator_tv_bound :
    ∀ (n : Nat) (d : Fin n → Nat), 4 ≤ n → (∀ v, d v ≤ n - 1) → Graphical n d → 1 < stateCount n d → ∀ (t : Nat) (G : GraphState n d), tvDistanceFrom n d t G ≤ Real.sqrt (stateCount n d : ℝ) / 2 * Real.exp (- (t : ℝ) / (24 * (n : ℝ) ^ 2 * (Nat.choose n 4 : ℝ))) := by
  exact OAI.Problem315.switch_chain_tv_bound

theorem comparator_connectivity :
    ∀ (n : Nat) (d : Fin n → Nat), 4 ≤ n → (∀ v, d v ≤ n - 1) → Graphical n d → ∀ G H : GraphState n d, Relation.ReflTransGen (SwitchStep n d) G H := by
  exact switch_connectivity

theorem sharp_gap : Statement.switch_chain_gap := SharpSwitchGap.switch_chain_gap

theorem sharp_tv_bound : Statement.switch_chain_tv_bound := SharpSwitchGap.switch_chain_tv_bound

end SharpSwitchGap.Baseline

#print axioms OAI.Problem315.switch_chain_main
#print axioms OAI.Problem315.switch_chain_tv_bound
#print axioms OAI.Problem315.switch_connectivity
