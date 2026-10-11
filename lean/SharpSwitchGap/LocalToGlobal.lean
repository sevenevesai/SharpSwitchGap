import OAI.Probability.SwitchChain.PairAggregation

namespace SharpSwitchGap.LocalToGlobal

open scoped BigOperators
open OAI.Problem315
variable {V : Type*} [DecidableEq V]

/-- The same counting identity serves Johnson (γ = 3/2) and graph pairs (γ = 1).
The ordered disjoint sum is retained, rather than discarded as in the upstream bound. -/
theorem square_lower_bound (s : Finset V) (hs : 3 ≤ s.card)
    (h : Finset V → ℝ) (B : Finset V → Finset V → ℝ) (γ : ℝ)
    (hdiag : ∀ a ∈ s.powersetCard 2, B a a = h a)
    (htriple : ∀ T ∈ s.powersetCard 3,
      γ * (∑ a ∈ T.powersetCard 2, h a) ≤
        ∑ a ∈ T.powersetCard 2, ∑ b ∈ T.powersetCard 2, B a b) :
    (γ * (s.card - 2 : ℕ) - (s.card - 3 : ℕ)) * (∑ a ∈ s.powersetCard 2, h a) +
      (∑ a ∈ s.powersetCard 2, ∑ b ∈ s.powersetCard 2,
        if Disjoint a b then B a b else 0) ≤
      ∑ a ∈ s.powersetCard 2, ∑ b ∈ s.powersetCard 2, B a b := by
  classical
  have ht : ∀ T ∈ s.powersetCard 3,
      γ * (∑ a ∈ s.powersetCard 2, if a ⊆ T then h a else 0) ≤
        ∑ a ∈ s.powersetCard 2, ∑ b ∈ s.powersetCard 2,
          if a ⊆ T ∧ b ⊆ T then B a b else 0 := by
    intro T hT
    have hTs := (Finset.mem_powersetCard.mp hT).1
    rw [PairAggregation.pairSum_restrict s T hTs,
      PairAggregation.local_quadratic_restrict s T hTs]
    exact htriple T hT
  have hsum := Finset.sum_le_sum ht
  rw [← Finset.mul_sum, PairAggregation.sum_pair_terms_over_triples,
    PairAggregation.triple_expansion s hs,
    Finset.sum_congr rfl hdiag] at hsum
  nlinarith only [hsum]

end SharpSwitchGap.LocalToGlobal
