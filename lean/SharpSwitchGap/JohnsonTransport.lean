import SharpSwitchGap.JohnsonGap
import OAI.Probability.SwitchChain.SliceCardEncoding
import OAI.Probability.SwitchChain.SlicePathComparison

namespace SharpSwitchGap.Johnson

noncomputable section
open scoped BigOperators RealInnerProductSpace
open OAI.Problem315 SliceEuclideanGenerator
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem sum_swap_support (F : Finset V → ℝ) :
    (∑ σ ∈ SlicePathComparison.swaps (α := V), F σ.support) =
      ∑ s ∈ (Finset.univ : Finset V).powersetCard 2, F s := by
  classical
  apply Finset.sum_bij (fun σ _ => σ.support)
  · intro σ hσ
    obtain ⟨a,b,hab,rfl⟩ := SlicePathComparison.mem_swaps σ |>.mp hσ
    simp [Equiv.Perm.support_swap, hab]
  · intro σ hσ τ hτ he
    obtain ⟨a,b,hab,rfl⟩ := SlicePathComparison.mem_swaps σ |>.mp hσ
    obtain ⟨c,d,hcd,rfl⟩ := SlicePathComparison.mem_swaps τ |>.mp hτ
    rw [Equiv.Perm.support_swap hab, Equiv.Perm.support_swap hcd] at he
    have hp : ({a,b} : Set V) = {c,d} := by
      simpa using congrArg (fun s : Finset V => (s : Set V)) he
    rcases Set.pair_eq_pair_iff.mp hp with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · rfl
    · exact Equiv.swap_comm _ _
  · intro s hs
    obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hs).2
    exact ⟨Equiv.swap a b, (SlicePathComparison.mem_swaps _).mpr ⟨a,b,hab,rfl⟩,
      Equiv.Perm.support_swap hab⟩
  · intro σ _
    rfl

theorem generator_energy_swaps (q : ℕ) (f : Space V q) :
    ⟪f, generator q f⟫ = (1 / 4 : ℝ) *
      ∑ σ ∈ SlicePathComparison.swaps (α := V), ∑ S, (f S - f (relabel q σ S)) ^ 2 := by
  rw [← edge_sum_eq_generator, LinearMap.sum_apply, inner_sum, ← sum_swap_support]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  obtain ⟨a,b,hab,rfl⟩ := SlicePathComparison.mem_swaps σ |>.mp hσ
  rw [Equiv.Perm.support_swap hab, edge_pair q a b hab, exchange_apply,
    inner_smul_right, move_energy, EuclideanSpace.real_norm_sq_eq]
  simp only [PiLp.sub_apply, moveOperator_apply, swapState]
  ring

theorem variance_le_swaps {q : ℕ} {Ω : Type*} [Fintype Ω]
    (e : Ω ≃ SlicePermutationAction.Slice V q) (f : Ω → ℝ) :
    (∑ s, (f s - (∑ t, f t) / (Fintype.card Ω : ℝ)) ^ 2) ≤
      (1 / 4 : ℝ) * ∑ s, ∑ σ ∈ SlicePathComparison.swaps,
        (f s - f (e.symm (SlicePermutationAction.relabel σ (e s)))) ^ 2 := by
  let e' := e.trans (SliceNormalized.cardSliceEquiv q).symm
  let g : Space V q := WithLp.toLp 2 (fun S => f (e'.symm S))
  have h := variance_le_energy q g
  rw [generator_energy_swaps, Finset.sum_comm] at h
  have hmean : (∑ S, g S) = ∑ s, f s := e'.symm.sum_comp f
  have hcard : Fintype.card (State V q) = Fintype.card Ω := Fintype.card_congr e'.symm
  rw [hmean, hcard] at h
  have hmove (σ : Equiv.Perm V) (S : State V q) :
      e'.symm (relabel q σ S) = e.symm (SlicePermutationAction.relabel σ (e (e'.symm S))) := by
    change e.symm (SliceNormalized.cardSliceEquiv q (relabel q σ S)) = _
    rw [SliceNormalized.cardSliceEquiv_relabel]
    simp [e']
  simp only [g, hmove] at h
  have hl := e'.symm.sum_comp
    (fun s => (f s - (∑ t, f t) / (Fintype.card Ω : ℝ)) ^ 2)
  have hr := e'.symm.sum_comp
    (fun s => ∑ σ ∈ SlicePathComparison.swaps,
      (f s - f (e.symm (SlicePermutationAction.relabel σ (e s)))) ^ 2)
  rw [hl, hr] at h
  exact h

end
end SharpSwitchGap.Johnson
