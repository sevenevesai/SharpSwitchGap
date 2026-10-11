import OAI.Probability.SwitchChain.SliceOperatorComparison
import SharpSwitchGap.WeightedGram
import SharpSwitchGap.WeightedScalars

/- B1 partial: the weighted inequality on the actual upstream equality-image
range. The proof follows SliceOperatorComparison.operator_comparison_nontrivial
but reserves one unit of energy. WeightedSlice.lean handles the centered complement
using JohnsonGap.lean. -/

namespace SharpSwitchGap.WeightedSliceRange

noncomputable section
open scoped BigOperators RealInnerProductSpace
open OAI.Problem315
open SliceNormalized SliceSynthesis SliceCoefficients

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem weighted_on_range (q : ℕ) (hN : 3 ≤ Fintype.card V)
    (hq0 : 0 < q) (hqN : q < Fintype.card V) (c : Coeff V) :
    let B := synthesis (column (V := V) q)
    SliceMoments.equalMean (Finset.univ : Finset V) q *
        ‖LinearMap.adjoint B (B c)‖ ^ 2 + ‖B c‖ ^ 2 ≤
      ⟪B c, SliceEuclideanGenerator.generator q (B c)⟫ := by
  let : Nontrivial V := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  let p := SliceMoments.equalMean (Finset.univ : Finset V) q
  have hp : 0 < p := SliceImageNorm.equalMean_pos hN q
  have hp1 := SliceImageNorm.equalMean_lt_one (by omega : 2 ≤ Fintype.card V) q hq0 hqN
  obtain ⟨b, d, hgram⟩ := SliceGramProfile.exists_normalized_orbit_entries
    (V := V) q hqN.le hp hp1
  let μ₁ : ℝ := 1 + ((Fintype.card V : ℝ) - 4) * b - ((Fintype.card V : ℝ) - 3) * d
  let μ₂ : ℝ := if 4 ≤ Fintype.card V then 1 - 2 * b + d else 0
  have hμ₁ : μ₁ = SliceImageNorm.linearGramScalar (α := V) q :=
    linear_orbit_scalar_eq q hN hq0 hqN b d hgram
  have hNR : (3 : ℝ) ≤ Fintype.card V := by exact_mod_cast hN
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq0
  have hqr : q + 1 ≤ Fintype.card V := by omega
  have hqrR : (q : ℝ) + 1 ≤ Fintype.card V := by exact_mod_cast hqr
  have hrR : (1 : ℝ) ≤ (Fintype.card V : ℝ) - q := by linarith
  have hsum : (q : ℝ) + ((Fintype.card V : ℝ) - q) = Fintype.card V := by ring
  have hden : (Fintype.card V : ℝ) - 2 ≠ 0 := by linarith
  have hμ₁pos : 0 ≤ μ₁ := by
    rw [hμ₁]
    unfold SliceImageNorm.linearGramScalar
    apply div_nonneg (sq_nonneg _)
    exact mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hp.le
  have hweighted₁ : p * μ₁ =
      ((Fintype.card V : ℝ) - 2 * q) ^ 2 / (2 * ((Fintype.card V : ℝ) - 2)) := by
    rw [hμ₁]
    change p * ((2 * (q : ℝ) - (Fintype.card V : ℝ)) ^ 2 /
      (2 * ((Fintype.card V : ℝ) - 2) * p)) = _
    field_simp
    ring
  have hb₁ : p * μ₁ + 1 ≤ (Fintype.card V : ℝ) / 2 := by
    rw [hweighted₁]
    have h := WeightedScalars.linear_slack_nonneg
      (Fintype.card V : ℝ) q ((Fintype.card V : ℝ) - q) hNR hqR hrR hsum
    linarith
  have hpbound : p ≤ ((Fintype.card V : ℝ) - 2) / Fintype.card V := by
    simpa only [p, SliceMoments.equalMean, Finset.card_univ] using
      WeightedScalars.equality_probability_le (Fintype.card V : ℝ)
        q ((Fintype.card V : ℝ) - q) (by linarith) hqR hrR hsum
  have hb₂ : p * μ₂ + 1 ≤ (Fintype.card V : ℝ) - 1 := by
    dsimp only [μ₂]
    split_ifs with h4
    · have hconstant := constant_relation_of_orbit_entries
        (column q) b d (column_diag q) (column_total q (by omega)) hgram
      have hbase := SliceGram.degree_two_eigenvalue_le
        (Fintype.card V : ℝ) b d μ₁ (1 - 2 * b + d)
        (by exact_mod_cast h4) hconstant rfl rfl hμ₁pos
      exact WeightedScalars.weighted_quadratic_bound
        (Fintype.card V : ℝ) p (1 - 2 * b + d) (by exact_mod_cast h4) hp.le hpbound hbase
    · simp only [mul_zero, zero_add]
      linarith
  refine WeightedGram.range_bound (E := Space V q) (F := Coeff V)
    (synthesis (column q)) (SliceEuclideanGenerator.generator q) p μ₁ μ₂
    ((Fintype.card V : ℝ) / 2) ((Fintype.card V : ℝ) - 1) hb₁ hb₂ ?_ c
  intro c
  obtain ⟨u, v, hu, hvrow, hvsym, hvdiag, hdec, horth⟩ :=
    exists_synthesis_decomposition hN (column q) (column_symmetric q)
      (column_diag q) (column_total q (by omega)) c
  refine ⟨ofMatrix (linearPair u), ofMatrix v, hdec, horth, ?_, ?_, ?_, ?_⟩
  · exact gram_linear_of_orbit_entries (column q) 1 b d (column_diag q) hgram u hu
  · by_cases h4 : 4 ≤ Fintype.card V
    · simpa only [μ₂, ite_eq_left h4] using gram_rowZero_of_orbit_entries
        (column q) 1 b d (column_diag q) hgram v hvsym hvdiag hvrow
    · have hv := rowZero_eq_zero_of_card_le_three (by omega) v hvrow hvsym hvdiag
      subst v
      simp [ofMatrix, synthesis, μ₂, h4]
  · exact generator_synthesis_linear q u hu
  · exact generator_synthesis_rowZero q v hvrow hvsym hvdiag

end
end SharpSwitchGap.WeightedSliceRange

#print axioms SharpSwitchGap.WeightedSliceRange.weighted_on_range
