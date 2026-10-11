import OAI.Probability.SwitchChain.SliceEuclideanGenerator
import OAI.Probability.SwitchChain.PairAggregation
import OAI.Probability.SwitchChain.UnorderedPairSums

/- Local-to-global Johnson estimate. The edge operator is (I - swap)/2,
so the sum of edges is the pinned slice generator J/2. -/

namespace SharpSwitchGap.Johnson

noncomputable section
open scoped BigOperators RealInnerProductSpace
open OAI.Problem315 SliceEuclideanGenerator
variable {V : Type*} [Fintype V] [DecidableEq V]
abbrev Space (V : Type*) [Fintype V] (q : ℕ) := EuclideanSpace ℝ (State V q)

@[simp] theorem mem_swapState (q : ℕ) (a b x : V) (S : State V q) :
    x ∈ (swapState q a b S).val ↔ Equiv.swap a b x ∈ S.val := by
  change x ∈ S.val.image (Equiv.swap a b) ↔ _
  constructor
  · intro hx
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hx
    simpa only [← hxy, Equiv.swap_apply_self] using hy
  · intro hx
    exact Finset.mem_image.mpr ⟨Equiv.swap a b x, hx, Equiv.swap_apply_self a b x⟩

theorem swapState_fixed (q : ℕ) (a b : V) (S : State V q)
    (h : a ∈ S.val ↔ b ∈ S.val) : swapState q a b S = S := by
  apply Subtype.ext
  ext x
  by_cases ha : x = a <;> by_cases hb : x = b <;>
    simp_all [Equiv.swap_apply_def]

theorem triple_orbit (q : ℕ) (a b c : V) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (S : State V q) (f : State V q → ℝ) :
    f S + f (swapState q a b (swapState q b c S)) +
      f (swapState q b c (swapState q a b S)) =
      f (swapState q a b S) + f (swapState q a c S) + f (swapState q b c S) := by
  by_cases hmem : a ∈ S.val ↔ b ∈ S.val
  · have hfix := swapState_fixed q a b S hmem
    have he : swapState q a b (swapState q b c S) = swapState q a c S := by
      apply Subtype.ext
      ext x
      by_cases hxa : x = a <;> by_cases hxb : x = b <;> by_cases hxc : x = c <;>
        simp_all [Equiv.swap_apply_def]
    rw [he, hfix]
  · by_cases hmem' : b ∈ S.val ↔ c ∈ S.val
    · have hfix := swapState_fixed q b c S hmem'
      have he : swapState q b c (swapState q a b S) = swapState q a c S := by
        apply Subtype.ext
        ext x
        by_cases hxa : x = a <;> by_cases hxb : x = b <;> by_cases hxc : x = c <;>
          simp_all [Equiv.swap_apply_def, Ne.symm hab, Ne.symm hac, Ne.symm hbc]
      rw [he, hfix]
      ring
    · have hmem'' : a ∈ S.val ↔ c ∈ S.val := by tauto
      have hfix := swapState_fixed q a c S hmem''
      have he : swapState q a b (swapState q b c S) = swapState q b c S := by
        apply Subtype.ext
        ext x
        by_cases hxa : x = a <;> by_cases hxb : x = b <;> by_cases hxc : x = c <;>
          simp_all [Equiv.swap_apply_def, Ne.symm hab, Ne.symm hac, Ne.symm hbc]
      have he' : swapState q b c (swapState q a b S) = swapState q a b S := by
        apply Subtype.ext
        ext x
        by_cases hxa : x = a <;> by_cases hxb : x = b <;> by_cases hxc : x = c <;>
          simp_all [Equiv.swap_apply_def, Ne.symm hab, Ne.symm hac, Ne.symm hbc]
      rw [he, he', hfix]
      ring

theorem swap_braid (q : ℕ) (a b c : V) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (S : State V q) :
    swapState q a b (swapState q b c S) = swapState q a c (swapState q a b S) := by
  apply Subtype.ext
  ext x
  by_cases hxa : x = a <;> by_cases hxb : x = b <;> by_cases hxc : x = c <;>
    simp_all [Equiv.swap_apply_def, Ne.symm hab, Ne.symm hac, Ne.symm hbc]

@[simp] theorem swapState_comm (q : ℕ) (a b : V) :
    swapState q b a = swapState q a b := by
  unfold swapState
  rw [Equiv.swap_comm]

def exchange (q : ℕ) (a b : V) : Space V q →ₗ[ℝ] Space V q :=
  (1 / 2 : ℝ) • (LinearMap.id - moveOperator q a b)

@[simp] theorem exchange_apply (q : ℕ) (a b : V) (f : Space V q) :
    exchange q a b f = (1 / 2 : ℝ) • (f - moveOperator q a b f) := rfl

theorem exchange_symmetric (q : ℕ) (a b : V) :
    (exchange q a b).IsSymmetric :=
  (LinearMap.IsSymmetric.id.sub (moveOperator_symmetric q a b)).smul (by simp)

theorem exchange_idempotent (q : ℕ) (a b : V) (f : Space V q) :
    exchange q a b (exchange q a b f) = exchange q a b f := by
  simp only [exchange_apply, map_smul, map_sub, moveOperator_twice]
  module

theorem exchange_energy (q : ℕ) (a b : V) (f : Space V q) :
    ⟪f, exchange q a b f⟫ = ‖exchange q a b f‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, exchange_symmetric,
    exchange_idempotent]

theorem triple_square (q : ℕ) (a b c : V) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (f : Space V q) :
    let T := exchange q a b + exchange q a c + exchange q b c
    T (T f) = (3 / 2 : ℝ) • T f := by
  dsimp only
  ext S
  have h := triple_orbit q a b c hab hac hbc S (fun S => f S)
  have h₁ := swap_braid q a b c hab hac hbc S
  have h₂ := swap_braid q b a c hab.symm hbc hac S
  have h₃ := swap_braid q a c b hac hab hbc.symm S
  have h₄ := swap_braid q c a b hac.symm hbc.symm hab S
  simp only [swapState_comm] at h₂ h₃ h₄
  simp only [LinearMap.add_apply, exchange_apply, PiLp.add_apply,
    PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul, moveOperator_apply,
    swapState_twice]
  simp only [← h₁, h₂, h₃, ← h₄]
  linarith

def edge (q : ℕ) (s : Finset V) : Space V q →ₗ[ℝ] Space V q :=
  (1 / 4 : ℝ) • ∑ a ∈ s, ∑ b ∈ s, (LinearMap.id - moveOperator q a b)

@[simp] theorem moveOperator_self (q : ℕ) (a : V) :
    moveOperator q a a = LinearMap.id (R := ℝ) (M := Space V q) := by
  ext f S
  change f (swapState q a a S) = f S
  rw [swapState_fixed q a a S Iff.rfl]

theorem edge_pair (q : ℕ) (a b : V) (hab : a ≠ b) :
    edge q {a,b} = exchange q a b := by
  have hc : moveOperator q b a = moveOperator q a b := by
    ext f S
    simp only [moveOperator_apply, swapState_comm]
  ext f S
  simp [edge, hab, hc, exchange, PiLp.smul_apply, PiLp.sub_apply,
    PiLp.add_apply]
  ring

omit [Fintype V] in
theorem triple_pairs (a b c : V) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ({a,b,c} : Finset V).powersetCard 2 = {{a,b},{a,c},{b,c}} := by
  rw [show (2 : ℕ) = 1 + 1 from rfl,
    Finset.powersetCard_succ_insert (by simp [hab, hac])]
  have hp : ({b,c} : Finset V).card = 2 := by simp [hbc]
  change (Finset.powersetCard 2 {b,c}) ∪ _ = _
  rw [← hp, Finset.powersetCard_self]
  simp only [Finset.powersetCard_one, Finset.map_insert, Finset.map_singleton,
    Function.Embedding.coeFn_mk, Finset.image_insert, Finset.image_singleton,
    Finset.singleton_union]
  ext u
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem edge_symmetric (q : ℕ) (s : Finset V) : (edge q s).IsSymmetric := by
  apply LinearMap.IsSymmetric.smul (by simp)
  apply LinearMap.isSymmetric_sum
  intro a _
  apply LinearMap.isSymmetric_sum
  intro b _
  exact LinearMap.IsSymmetric.id.sub (moveOperator_symmetric q a b)

theorem edge_energy (q : ℕ) (s : Finset V) (hs : s.card = 2) (f : Space V q) :
    ⟪f, edge q s f⟫ = ‖edge q s f‖ ^ 2 := by
  obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hs
  rw [edge_pair q a b hab, exchange_energy]

theorem edge_sum_eq_generator (q : ℕ) :
    (∑ s ∈ (Finset.univ : Finset V).powersetCard 2, edge q s) = generator q := by
  ext f S
  have h := UnorderedPairSums.sum_ordered_eq_two_mul
    (fun s : Finset V => edge q s f S)
  have he (a b : V) : (if a ≠ b then edge q {a,b} f S else 0) =
      (f S - f (swapState q a b S)) / 2 := by
    by_cases hab : a = b
    · subst b
      simp [swapState_fixed q a a S Iff.rfl]
    · rw [ite_eq_left hab, edge_pair q a b hab]
      simp only [exchange_apply, PiLp.smul_apply, PiLp.sub_apply,
        smul_eq_mul, moveOperator_apply]
      ring
  simp_rw [he, ← Finset.sum_div] at h
  simp only [LinearMap.sum_apply, WithLp.ofLp_sum, Finset.sum_apply, generator_apply]
  linarith

theorem edge_triple_square (q : ℕ) (T : Finset V) (hT : T.card = 3)
    (f : Space V q) :
    let A := ∑ s ∈ T.powersetCard 2, edge q s
    A (A f) = (3 / 2 : ℝ) • A f := by
  obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := Finset.card_eq_three.mp hT
  have habac : ({a,b} : Finset V) ≠ {a,c} := by
    intro h
    have hb : b ∈ ({a,c} : Finset V) := h ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
    simp [hab.symm, hbc] at hb
  have habbc : ({a,b} : Finset V) ≠ {b,c} := by
    intro h
    have ha : a ∈ ({b,c} : Finset V) := h ▸ Finset.mem_insert_self a {b}
    simp [hab, hac] at ha
  have hacbc : ({a,c} : Finset V) ≠ {b,c} := by
    intro h
    have ha : a ∈ ({b,c} : Finset V) := h ▸ Finset.mem_insert_self a {c}
    simp [hab, hac] at ha
  rw [triple_pairs a b c hab hac hbc]
  simpa [habac, habbc, hacbc, edge_pair q a b hab, edge_pair q a c hac,
    edge_pair q b c hbc, add_assoc] using triple_square q a b c hab hac hbc f

theorem exchange_commutes (q : ℕ) (a b c d : V)
    (h : Disjoint ({a,b} : Finset V) {c,d}) (f : Space V q) :
    exchange q a b (exchange q c d f) = exchange q c d (exchange q a b f) := by
  have hdist : a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d := by
    simpa [Finset.disjoint_left, and_assoc] using h
  obtain ⟨hac,had,hbc,hbd⟩ := hdist
  have he (S : State V q) :
      swapState q a b (swapState q c d S) = swapState q c d (swapState q a b S) := by
    apply Subtype.ext
    ext x
    by_cases ha : x = a <;> by_cases hb : x = b <;>
      by_cases hc : x = c <;> by_cases hd : x = d <;>
      simp_all [Equiv.swap_apply_def, Ne.symm hac, Ne.symm had, Ne.symm hbc, Ne.symm hbd]
  ext S
  simp only [exchange_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul,
    moveOperator_apply, he]
  ring

theorem disjoint_nonneg (q : ℕ) (s t : Finset V) (hs : s.card = 2)
    (ht : t.card = 2) (hd : Disjoint s t) (f : Space V q) :
    0 ≤ ⟪edge q s f, edge q t f⟫ := by
  obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hs
  obtain ⟨c,d,hcd,rfl⟩ := Finset.card_eq_two.mp ht
  rw [edge_pair q a b hab, edge_pair q c d hcd]
  have he : ⟪exchange q a b f, exchange q c d f⟫ =
      ‖exchange q c d (exchange q a b f)‖ ^ 2 := by
    calc
      _ = ⟪exchange q a b (exchange q a b f), exchange q c d f⟫ := by
        rw [exchange_idempotent]
      _ = ⟪exchange q a b f, exchange q a b (exchange q c d f)⟫ :=
        exchange_symmetric q a b _ _
      _ = _ := by rw [exchange_commutes q a b c d hd, exchange_energy]
  rw [he]
  positivity

end
end SharpSwitchGap.Johnson
