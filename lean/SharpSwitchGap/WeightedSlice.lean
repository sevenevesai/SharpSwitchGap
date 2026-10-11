import SharpSwitchGap.WeightedSliceRange
import SharpSwitchGap.JohnsonGap

/- Weighted slice comparison, using the local-to-global Johnson bound. -/

namespace SharpSwitchGap.WeightedSlice

noncomputable section
open scoped BigOperators RealInnerProductSpace
open OAI.Problem315
open SliceNormalized SliceSynthesis SliceCoefficients

variable {V : Type*} [Fintype V] [DecidableEq V]

def centered (q : ℕ) : Submodule ℝ (Space V q) where
  carrier := {f | ∑ S, f S = 0}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg
    change (∑ S, (f S + g S)) = 0
    rw [Finset.sum_add_distrib, hf, hg, add_zero]
  smul_mem' := by
    intro a f hf
    change (∑ S, a * f S) = 0
    rw [← Finset.mul_sum, hf, mul_zero]

theorem raw_centered (q : ℕ) (hq : q ≤ Fintype.card V) (i j : V) :
    raw q i j ∈ centered (V := V) q := by
  change (∑ S : State V q, raw q i j S) = 0
  by_cases hij : i = j
  · subst j
    simp
  · have h := SliceMoments.average_centeredEqual (Finset.univ : Finset V) q
      (by simpa using hq) i j (Finset.mem_univ i) (Finset.mem_univ j) hij
    have hden : (((Finset.univ : Finset V).card.choose q : ℕ) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by simpa using hq)).ne'
    unfold SliceMoments.average at h
    have hs := (div_eq_zero_iff.mp h).resolve_right hden
    change (∑ S : State V q,
      if i = j then 0 else SliceMoments.centeredEqual Finset.univ q i j S.val) = 0
    simp only [hij, ite_false]
    rw [Finset.sum_coe_sort ((Finset.univ : Finset V).powersetCard q)
      (SliceMoments.centeredEqual Finset.univ q i j)]
    exact hs

theorem range_centered (q : ℕ) (hq : q ≤ Fintype.card V) :
    LinearMap.range (synthesis (column (V := V) q)) ≤ centered q := by
  rintro f ⟨c, rfl⟩
  change (∑ i, ∑ j, c (i, j) • column q i j) ∈ centered q
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro j _
  apply Submodule.smul_mem
  exact (centered q).smul_mem _ (raw_centered q hq i j)

theorem range_invariant (q : ℕ) (hN : 3 ≤ Fintype.card V)
    (f : Space V q) (hf : f ∈ LinearMap.range (synthesis (column q))) :
    SliceEuclideanGenerator.generator q f ∈ LinearMap.range (synthesis (column q)) := by
  obtain ⟨c, rfl⟩ := hf
  obtain ⟨u, v, hu, hvrow, hvsym, hvdiag, hdec, _⟩ :=
    exists_synthesis_decomposition hN (column q) (column_symmetric q)
      (column_diag q) (column_total q (by omega)) c
  rw [hdec, map_add, generator_synthesis_linear q u hu,
    generator_synthesis_rowZero q v hvrow hvsym hvdiag]
  exact Submodule.add_mem _
    (Submodule.smul_mem _ _ (LinearMap.mem_range_self _ _))
    (Submodule.smul_mem _ _ (LinearMap.mem_range_self _ _))

/-- One unit of G-energy on the centered complement of the equality-image range. -/
def ResidualJohnsonBound (V : Type*) [Fintype V] [DecidableEq V] (q : ℕ) : Prop :=
  ∀ f : Space V q, f ∈ centered q →
    f ∈ (LinearMap.range (synthesis (column q)))ᗮ →
    ‖f‖ ^ 2 ≤ ⟪f, SliceEuclideanGenerator.generator q f⟫

theorem residual_johnson_bound (q : ℕ) : ResidualJohnsonBound V q := by
  intro f hf _
  exact Johnson.unit_poincare q f hf

theorem weighted_of_residual (q : ℕ) (hN : 3 ≤ Fintype.card V)
    (hq0 : 0 < q) (hqN : q < Fintype.card V)
    (hresidual : ResidualJohnsonBound V q)
    (f : Space V q) (hf : ∑ S, f S = 0) :
    let B := synthesis (column (V := V) q)
    SliceMoments.equalMean (Finset.univ : Finset V) q *
      ⟪f, B (LinearMap.adjoint B f)⟫ + ‖f‖ ^ 2 ≤
      ⟪f, SliceEuclideanGenerator.generator q f⟫ := by
  exact WeightedGram.extend_from_range (E := Space V q) (F := Coeff V)
    (synthesis (column q)) (SliceEuclideanGenerator.generator q)
    (SliceEuclideanGenerator.generator_symmetric q) (centered q)
    (SliceMoments.equalMean (Finset.univ : Finset V) q)
    (range_centered (V := V) q hqN.le) (range_invariant (V := V) q hN)
      (WeightedSliceRange.weighted_on_range (V := V) q hN hq0 hqN) hresidual f hf

/-- All slice sizes; boundary columns vanish, including N = 2, q = 1. -/
theorem weighted_centered (q : ℕ) (hq : q ≤ Fintype.card V)
    (f : Space V q) (hf : ∑ S, f S = 0) :
    let B := synthesis (column (V := V) q)
    SliceMoments.equalMean (Finset.univ : Finset V) q *
      ⟪f, B (LinearMap.adjoint B f)⟫ + ‖f‖ ^ 2 ≤
      ⟪f, SliceEuclideanGenerator.generator q f⟫ := by
  by_cases hb : q = 0 ∨ q = Fintype.card V ∨ Fintype.card V ≤ 2
  · have hz : synthesis (column (V := V) q) = 0 := by
      ext c S
      simp [synthesis, column_eq_zero_of_boundary q hq hb]
    simp only [hz, LinearMap.zero_apply, inner_zero_right, mul_zero, zero_add]
    exact Johnson.unit_poincare q f hf
  · exact weighted_of_residual q (by omega) (by omega) (by omega)
      (residual_johnson_bound q) f hf

end
end SharpSwitchGap.WeightedSlice

#print axioms SharpSwitchGap.WeightedSlice.weighted_of_residual
