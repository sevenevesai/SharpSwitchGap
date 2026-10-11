import OAI.Probability.SwitchChain.Definitions

/- Comparator-style contracts. This file imports only the pinned definitions;
the proofs and their auxiliary operators are checked against it in Baseline.lean. -/

namespace SharpSwitchGap.Statement

open OAI.Problem315

def switch_chain_gap : Prop :=
  ∀ (n : Nat) (d : Fin n → Nat), 4 ≤ n → (∀ v, d v ≤ n - 1) →
    Graphical n d → 1 < stateCount n d →
    hasSpectralGapAtLeast n d ((1 : ℝ) / (6 * (Nat.choose n 4 : ℝ)))

def switch_chain_tv_bound : Prop :=
  ∀ (n : Nat) (d : Fin n → Nat), 4 ≤ n → (∀ v, d v ≤ n - 1) →
    Graphical n d → 1 < stateCount n d → ∀ (t : Nat) (G : GraphState n d),
    tvDistanceFrom n d t G ≤ Real.sqrt (stateCount n d : ℝ) / 2 *
      Real.exp (- (t : ℝ) / (6 * (Nat.choose n 4 : ℝ)))

end SharpSwitchGap.Statement
