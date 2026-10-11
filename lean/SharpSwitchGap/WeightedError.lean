import SharpSwitchGap.GraphCellCompression

namespace SharpSwitchGap.WeightedError

noncomputable section
open scoped BigOperators RealInnerProductSpace
open OAI.Problem315 PairResampling DisjointEncoding DisjointMarginal GraphCellWeights
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {d : Fin n → ℕ}

def weightedProjection (i j k l : Fin n) (f : StateSpace n d) : StateSpace n d :=
  WithLp.toLp 2 (fun G => Real.sqrt (fiberWeight i j G) * PairEquality.projection i j k l f G)

theorem norm_sq (i j k l : Fin n) (f : StateSpace n d) :
    ‖weightedProjection i j k l f‖ ^ 2 =
      ∑ G, fiberWeight i j G * (PairEquality.projection i j k l f G) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, state_inner]
  apply Finset.sum_congr rfl
  intro G _
  change (Real.sqrt (fiberWeight i j G) * PairEquality.projection i j k l f G) *
    (Real.sqrt (fiberWeight i j G) * PairEquality.projection i j k l f G) = _
  rw [← sq, mul_pow, Real.sq_sqrt (fiberWeight_nonneg i j G)]

theorem restrictCell_commute (i j k l : Fin n) (C : GraphState n d → Prop)
    (hC : CellInvariant {i,j} C) (f : StateSpace n d) :
    weightedProjection i j k l (restrictCell C f) = restrictCell C (weightedProjection i j k l f) := by
  unfold weightedProjection
  rw [PairEquality.projection_restrictCell i j k l C hC]
  ext G
  by_cases h : C G <;> simp [restrictCell_apply,h]

theorem norm_sq_eq_weighted_form (i j k l : Fin n) (hij : i ≠ j) (f : StateSpace n d) :
    ‖weightedProjection i j k l f‖ ^ 2 =
      ⟪f, WithLp.toLp 2 (fun G => fiberWeight i j G * PairEquality.projection i j k l f G)⟫ := by
  let w : StateSpace n d := WithLp.toLp 2 (fiberWeight i j)
  have hw : w ∈ fiberSpace n d {i,j} := fun _ _ h => fiberWeight_constant i j hij h
  have hr := PairEquality.multiply_mem_equalitySpace i j k l w
    (PairEquality.projection i j k l f) hw
    ((PairEquality.equalitySpace i j k l).starProjection_apply_mem f)
  have hfix := (PairEquality.projection_eq_self_iff i j k l _).mpr hr
  calc
    _ = ⟪PairEquality.projection i j k l f,
        PairEquality.multiply w (PairEquality.projection i j k l f)⟫ := by
      rw [norm_sq, state_inner]
      apply Finset.sum_congr rfl
      intro G _
      change _ = PairEquality.projection i j k l f G *
        (fiberWeight i j G * PairEquality.projection i j k l f G)
      ring
    _ = _ := by
      have h := PairEquality.projection_isSymmetric (d := d) i j k l f
        (PairEquality.multiply w (PairEquality.projection i j k l f))
      change ⟪PairEquality.projection i j k l f, _⟫ =
        ⟪f, PairEquality.projection i j k l (PairEquality.multiply w
          (PairEquality.projection i j k l f))⟫ at h
      rw [hfix] at h
      exact h

theorem cell_norm_sq (e : Fin 4 ↪ Fin n) (G : GraphState n d)
    (i j k l : Fin n) (f : StateSpace n d) (a : ℝ)
    (ha : ∀ H : StateCell e G, fiberWeight i j H.val * PairEquality.projection i j k l f H.val =
      a * PairEquality.projection i j k l f H.val) :
    ‖crossCellRestriction e G (weightedProjection i j k l f)‖ ^ 2 =
      a * ‖crossCellRestriction e G (PairEquality.projection i j k l f)‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    IndependentCell.inner_eq_sum, IndependentCell.inner_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  obtain ⟨H,rfl⟩ := (stateCellCrossEquiv e G).surjective z
  simp only [crossCellRestriction_apply_equiv]
  change (Real.sqrt (fiberWeight i j H.val) * PairEquality.projection i j k l f H.val) *
      (Real.sqrt (fiberWeight i j H.val) * PairEquality.projection i j k l f H.val) =
    a * (PairEquality.projection i j k l f H.val * PairEquality.projection i j k l f H.val)
  rw [← sq, mul_pow, Real.sq_sqrt (fiberWeight_nonneg i j H.val), pow_two, ← mul_assoc, ha H]
  ring

end
end SharpSwitchGap.WeightedError
