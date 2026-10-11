import OAI.Probability.SwitchChain.CrossCellConditionalExpectation
import OAI.Probability.SwitchChain.IndependentCell

namespace SharpSwitchGap.CellWeights

noncomputable section
open scoped BigOperators RealInnerProductSpace
open OAI.Problem315 CrossCellMoments
variable {α β : Type*} [Fintype α] [Fintype β]

def weight (r : α → Fin 3) : ℝ :=
  CrossCovariance.rightSliceAverage (fun _ : α => 1) (offCenter r) 0 (offCenter r)

def rowProbability (r : α → Fin 3) (c : β → Fin 3) : ℝ :=
  average 2 r c (fun x _ => offCenter r x)

def colProbability (r : α → Fin 3) (c : β → Fin 3) : ℝ :=
  average 2 r c (fun _ y => offCenter c y)

theorem flag_conditionalLeft (r : α → Fin 3) (c : β → Fin 3) (y : β) :
    conditionalLeft 2 r c y (offCenter r) =
      weight r * (1 - offCenter c y) := by
  classical
  rw [conditionalLeft_two]
  by_cases hc : c y = 1
  · simp [offCenter, hc, weight]
  · have hz : (∑ x : α, (1 : ℝ) * (2 - 1 - offCenter r x) * offCenter r x) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      rcases offCenter_boolean r x with h | h <;> norm_num [h]
    simp only [offCenter, hc, ite_false, sub_self, mul_zero]
    change CrossCovariance.rightSliceAverage (fun _ : α => 1) (offCenter r) 1
      (offCenter r) = 0
    unfold CrossCovariance.rightSliceAverage
    rw [hz, zero_div]

theorem flag_conditionalRight (r : α → Fin 3) (c : β → Fin 3) (x : α) :
    conditionalRight 2 r c x (offCenter c) =
      weight c * (1 - offCenter r x) := by
  rw [conditionalRight_two, ← conditionalLeft_two c r x]
  exact flag_conditionalLeft c r x

theorem flag_conditionalLeft_of_two (s : ℕ) (hs : s = 2)
    (r : α → Fin 3) (c : β → Fin 3) (y : β) :
    conditionalLeft s r c y (offCenter r) = weight r * (1 - offCenter c y) := by
  subst s
  exact flag_conditionalLeft r c y

theorem flag_conditionalRight_of_two (s : ℕ) (hs : s = 2)
    (r : α → Fin 3) (c : β → Fin 3) (x : α) :
    conditionalRight s r c x (offCenter c) = weight c * (1 - offCenter r x) := by
  subst s
  exact flag_conditionalRight r c x

theorem weight_eq_probability_ratio (r : α → Fin 3) (c : β → Fin 3)
    (z : Cell 2 r c) (hz : c z.val.2.2 = 1) :
    weight r = rowProbability r c / (1 - colProbability r c) := by
  classical
  let Ω := Cell 2 r c
  let v : EuclideanSpace ℝ Ω := WithLp.toLp 2 (fun w => offCenter r w.val.2.1)
  have hsum := IndependentCell.sum_expectation (secondPartition 2 r c) v
  dsimp only [v, Ω] at hsum
  simp_rw [expectation_second_left_apply, flag_conditionalLeft] at hsum
  rw [← Finset.mul_sum, Finset.sum_sub_distrib] at hsum
  simp only [Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one] at hsum
  have hlt : (∑ w : Ω, offCenter c w.val.2.2) < (Fintype.card Ω : ℝ) := by
    have h := Finset.sum_lt_sum
      (s := (Finset.univ : Finset Ω)) (f := fun w => offCenter c w.val.2.2)
      (g := fun _ => (1 : ℝ)) (fun w _ => by
        rcases offCenter_boolean c w.val.2.2 with h | h <;> simp [h])
      ⟨z, Finset.mem_univ z, by simp [offCenter, hz]⟩
    simpa using h
  have hnonneg : 0 ≤ ∑ w : Ω, offCenter c w.val.2.2 := by
    apply Finset.sum_nonneg
    intro w _
    rcases offCenter_boolean c w.val.2.2 with h | h <;> simp [h]
  have hM : (0 : ℝ) < Fintype.card Ω := lt_of_le_of_lt hnonneg hlt
  have hden : 1 - colProbability r c ≠ 0 := by
    unfold colProbability average
    have hdiv : (∑ w : Ω, offCenter c w.val.2.2) / (Fintype.card Ω : ℝ) < 1 :=
      (div_lt_one hM).mpr hlt
    linarith
  apply (eq_div_iff hden).mpr
  unfold rowProbability colProbability average
  apply (eq_div_iff hM.ne').mpr
  have hdivide : weight r *
      (1 - (∑ w : Ω, offCenter c w.val.2.2) / (Fintype.card Ω : ℝ)) *
      (Fintype.card Ω : ℝ) =
      weight r * ((Fintype.card Ω : ℝ) - ∑ w : Ω, offCenter c w.val.2.2) := by
    field_simp
  rw [hdivide]
  exact hsum

def transposeEquiv (r : α → Fin 3) (c : β → Fin 3) : Cell 2 r c ≃ Cell 2 c r where
  toFun z := ⟨(fun i j => z.val.1 j i, z.val.2.2, z.val.2.1), by
    refine ⟨?_,z.property.2.2,z.property.2.1⟩
    have he : CrossBlock.total (fun i j => z.val.1 j i) = CrossBlock.total z.val.1 := by
      unfold CrossBlock.total CrossBlock.row
      exact Finset.sum_comm
    exact he.trans z.property.1⟩
  invFun z := ⟨(fun i j => z.val.1 j i, z.val.2.2, z.val.2.1), by
    refine ⟨?_,z.property.2.2,z.property.2.1⟩
    have he : CrossBlock.total (fun i j => z.val.1 j i) = CrossBlock.total z.val.1 := by
      unfold CrossBlock.total CrossBlock.row
      exact Finset.sum_comm
    exact he.trans z.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem rowProbability_swap (r : α → Fin 3) (c : β → Fin 3) :
    rowProbability c r = colProbability r c := by
  unfold rowProbability colProbability average
  rw [← Fintype.card_congr (transposeEquiv r c)]
  congr 1
  exact ((transposeEquiv r c).sum_comp (fun z => offCenter c z.val.2.1)).symm

theorem right_weight_eq_probability_ratio (r : α → Fin 3) (c : β → Fin 3)
    (z : Cell 2 r c) (hz : r z.val.2.1 = 1) :
    weight c = colProbability r c / (1 - rowProbability r c) := by
  have h := weight_eq_probability_ratio c r (transposeEquiv r c z) hz
  rwa [rowProbability_swap r c, ← rowProbability_swap c r] at h

theorem weight_nonneg (r : α → Fin 3) : 0 ≤ weight r := by
  unfold weight CrossCovariance.rightSliceAverage
  apply div_nonneg
  · apply Finset.sum_nonneg
    intro x _
    rcases offCenter_boolean r x with h | h <;> norm_num [h]
  · apply Finset.sum_nonneg
    intro x _
    rcases offCenter_boolean r x with h | h <;> norm_num [h]

theorem weight_le_one (r : α → Fin 3) : weight r ≤ 1 := by
  unfold weight CrossCovariance.rightSliceAverage
  have hn : 0 ≤ ∑ x : α, (1 : ℝ) * (2 - 0 - offCenter r x) := by
    apply Finset.sum_nonneg
    intro x _
    rcases offCenter_boolean r x with h | h <;> norm_num [h]
  have hle : (∑ x : α, (1 : ℝ) * (2 - 0 - offCenter r x) * offCenter r x) ≤
      ∑ x : α, (1 : ℝ) * (2 - 0 - offCenter r x) := by
    apply Finset.sum_le_sum
    intro x _
    rcases offCenter_boolean r x with h | h <;> norm_num [h]
  rcases eq_or_lt_of_le hn with he | he
  · rw [← he, div_zero]
    norm_num
  · exact (div_le_one he).mpr hle

theorem probabilities_strict (r : α → Fin 3) (c : β → Fin 3)
    (hr : ∃ z : Cell 2 r c, r z.val.2.1 ≠ 1)
    (hc : ∃ z : Cell 2 r c, c z.val.2.2 ≠ 1) :
    0 < rowProbability r c ∧ 0 < colProbability r c ∧
      rowProbability r c + colProbability r c < 1 := by
  classical
  obtain ⟨w,hw⟩ := exists_center_of_both_offCenter r c hr hc
  let : Nonempty (Cell 2 r c) := ⟨w⟩
  have hM : (0 : ℝ) < Fintype.card (Cell 2 r c) := by
    exact_mod_cast Fintype.card_pos (α := Cell 2 r c)
  have hn (p : α → Fin 3) (x : α) : 0 ≤ offCenter p x := by
    rcases offCenter_boolean p x with h | h <;> simp [h]
  have hn' (p : β → Fin 3) (x : β) : 0 ≤ offCenter p x := by
    rcases offCenter_boolean p x with h | h <;> simp [h]
  refine ⟨div_pos ?_ hM, div_pos ?_ hM, ?_⟩
  · obtain ⟨z,hz⟩ := hr
    exact Finset.sum_pos' (fun x _ => hn r x.val.2.1)
      ⟨z, Finset.mem_univ z, by simp [offCenter, hz]⟩
  · obtain ⟨z,hz⟩ := hc
    exact Finset.sum_pos' (fun x _ => hn' c x.val.2.2)
      ⟨z, Finset.mem_univ z, by simp [offCenter, hz]⟩
  · have hlt : (∑ z : Cell 2 r c, (offCenter r z.val.2.1 + offCenter c z.val.2.2)) <
        (Fintype.card (Cell 2 r c) : ℝ) := by
      have h := Finset.sum_lt_sum (s := (Finset.univ : Finset (Cell 2 r c)))
        (f := fun z : Cell 2 r c => offCenter r z.val.2.1 + offCenter c z.val.2.2)
        (g := fun _ => (1 : ℝ)) (fun z _ => by
          by_cases hz : r z.val.2.1 = 1
          · simp only [offCenter, hz, ite_true, zero_add]
            split_ifs <;> norm_num
          · simp [offCenter, hz, offCenter_disjoint r c z hz])
        ⟨w, Finset.mem_univ w, by simp [offCenter, hw.1, hw.2]⟩
      simpa using h
    unfold rowProbability colProbability average
    rw [← add_div, ← Finset.sum_add_distrib]
    exact (div_lt_one hM).mpr hlt

end
end SharpSwitchGap.CellWeights
