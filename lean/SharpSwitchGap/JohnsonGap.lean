import SharpSwitchGap.JohnsonLocal
import SharpSwitchGap.LocalToGlobal
import OAI.Probability.SwitchChain.SpectralFromSquare
import OAI.Probability.SwitchChain.SlicePermutationAction

namespace SharpSwitchGap.Johnson

noncomputable section
open scoped BigOperators RealInnerProductSpace
open OAI.Problem315 SliceEuclideanGenerator
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem generator_square_ge (q : ℕ) (hN : 3 ≤ Fintype.card V) (f : Space V q) :
    (Fintype.card V : ℝ) / 2 * ⟪f, generator q f⟫ ≤
      ⟪generator q f, generator q f⟫ := by
  let s := (Finset.univ : Finset V)
  let h := fun a => ⟪f, edge q a f⟫
  let B := fun a b => ⟪edge q a f, edge q b f⟫
  have hdiag : ∀ a ∈ s.powersetCard 2, B a a = h a := by
    intro a ha
    dsimp [B, h]
    rw [real_inner_self_eq_norm_sq, edge_energy q a (Finset.mem_powersetCard.mp ha).2]
  have ht : ∀ T ∈ s.powersetCard 3,
      (3 / 2 : ℝ) * (∑ a ∈ T.powersetCard 2, h a) ≤
        ∑ a ∈ T.powersetCard 2, ∑ b ∈ T.powersetCard 2, B a b := by
    intro T hT
    let A := ∑ a ∈ T.powersetCard 2, edge q a
    have hs : A.IsSymmetric := LinearMap.isSymmetric_sum _
      (fun a _ => edge_symmetric q a)
    have he : ⟪A f, A f⟫ = (3 / 2 : ℝ) * ⟪f, A f⟫ := by
      rw [hs, edge_triple_square q T (Finset.mem_powersetCard.mp hT).2,
        inner_smul_right]
    simp only [A, LinearMap.sum_apply] at he
    simp only [sum_inner] at he
    simp only [inner_sum] at he
    exact he.ge
  have hd : 0 ≤ ∑ a ∈ s.powersetCard 2, ∑ b ∈ s.powersetCard 2,
      if Disjoint a b then B a b else 0 := by
    apply Finset.sum_nonneg
    intro a ha
    apply Finset.sum_nonneg
    intro b hb
    split_ifs with hd
    · exact disjoint_nonneg q a b (Finset.mem_powersetCard.mp ha).2
        (Finset.mem_powersetCard.mp hb).2 hd f
    · rfl
  have hg := LocalToGlobal.square_lower_bound s (by simpa [s] using hN)
    h B (3/2) hdiag ht
  have hc : (3 / 2 : ℝ) * (s.card - 2 : ℕ) - (s.card - 3 : ℕ) =
      (Fintype.card V : ℝ) / 2 := by
    simp only [s, Finset.card_univ]
    rw [Nat.cast_sub (by omega : 2 ≤ Fintype.card V),
      Nat.cast_sub hN]
    norm_num
    ring
  rw [hc] at hg
  have hg' := le_trans (le_add_of_nonneg_right hd) hg
  simpa only [h, B, ← inner_sum, ← sum_inner, ← LinearMap.sum_apply,
    s, edge_sum_eq_generator] using hg'

theorem generator_kernel_constant (q : ℕ) (f : Space V q) (hf : generator q f = 0)
    (S T : State V q) : f S = f T := by
  have henergy := generator_energy q f
  rw [hf, inner_zero_right] at henergy
  have hsum : (∑ a : V, ∑ b : V, ‖f - moveOperator q a b f‖ ^ 2) = 0 := by
    linarith
  have hmove (a b : V) : moveOperator q a b f = f := by
    have ha := (Finset.sum_eq_zero_iff_of_nonneg
      (fun a (_ : a ∈ (Finset.univ : Finset V)) =>
        Finset.sum_nonneg (fun b _ => sq_nonneg ‖f - moveOperator q a b f‖))).mp hsum a
      (Finset.mem_univ a)
    have hb := (Finset.sum_eq_zero_iff_of_nonneg
      (fun b (_ : b ∈ (Finset.univ : Finset V)) =>
        sq_nonneg ‖f - moveOperator q a b f‖)).mp ha b (Finset.mem_univ b)
    exact (sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hb))).symm
  have hswap (a b : V) (U : State V q) : f (swapState q a b U) = f U :=
    congrArg (fun g : Space V q => g U) (hmove a b)
  have hrel (σ : Equiv.Perm V) : ∀ U : State V q, f (relabel q σ U) = f U := by
    induction σ using Equiv.Perm.swap_induction_on with
    | one =>
      intro U
      have he : relabel q 1 U = U := by apply Subtype.ext; simp
      rw [he]
    | swap_mul σ a b hab ih =>
      intro U
      have he : relabel q (Equiv.swap a b * σ) U =
          swapState q a b (relabel q σ U) := by
        apply Subtype.ext
        simp [swapState, Finset.image_image, Function.comp_def]
      rw [he, hswap, ih]
  obtain ⟨σ,hσ⟩ := SlicePermutationAction.exists_perm_map_eq S.val T.val
    ((Finset.mem_powersetCard.mp S.property).2.trans
      (Finset.mem_powersetCard.mp T.property).2.symm)
  have he : relabel q σ S = T := by
    apply Subtype.ext
    simpa [Finset.map_eq_image] using hσ
  rw [← he, hrel]

theorem centered_orthogonal_kernel (q : ℕ) (f : Space V q) (hf : ∑ S, f S = 0)
    (g : Space V q) (hg : generator q g = 0) : ⟪g, f⟫ = 0 := by
  by_cases hne : Nonempty (State V q)
  · let S := Classical.choice hne
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    simp_rw [generator_kernel_constant q g hg _ S]
    rw [← Finset.sum_mul, hf, zero_mul]
  · have : IsEmpty (State V q) := not_nonempty_iff.mp hne
    simp [PiLp.inner_apply]

theorem centered_poincare (q : ℕ) (hN : 3 ≤ Fintype.card V)
    (f : Space V q) (hf : ∑ S, f S = 0) :
    (Fintype.card V : ℝ) / 2 * ‖f‖ ^ 2 ≤ ⟪f, generator q f⟫ := by
  let r : ℝ := (Fintype.card V : ℝ) / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have ht := Analytic.norm_sq_le_inner_of_square_ge
    (r⁻¹ • generator (α := V) q)
    ((generator_symmetric q).smul (by simp))
    (fun x => by
      simp only [LinearMap.smul_apply, inner_smul_right]
      exact mul_nonneg (inv_nonneg.mpr hr.le) (generator_positive q x))
    (fun x => by
      simp only [LinearMap.smul_apply, inner_smul_right, inner_smul_left,
        RCLike.conj_to_real]
      have hx := generator_square_ge q hN x
      dsimp only [r] at hr ⊢
      field_simp
      nlinarith [hx]) f
    (fun g hg => centered_orthogonal_kernel q f hf g
      ((smul_eq_zero.mp hg).resolve_left (inv_ne_zero hr.ne')))
  simp only [LinearMap.smul_apply, inner_smul_right] at ht
  calc
    r * ‖f‖ ^ 2 ≤ r * (r⁻¹ * ⟪f, generator q f⟫) :=
      mul_le_mul_of_nonneg_left ht hr.le
    _ = _ := by rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]

theorem generator_two_idempotent (q : ℕ) (hN : Fintype.card V = 2)
    (f : Space V q) : generator q (generator q f) = generator q f := by
  have hcard : (Finset.univ : Finset V).card = 2 := by simpa using hN
  have hp : (Finset.univ : Finset V).powersetCard 2 = {Finset.univ} := by
    rw [← hcard, Finset.powersetCard_self]
  obtain ⟨a,b,hab,hu⟩ := Finset.card_eq_two.mp hcard
  have hg := edge_sum_eq_generator (V := V) q
  rw [hp, Finset.sum_singleton, hu, edge_pair q a b hab] at hg
  rw [← hg]
  exact exchange_idempotent q a b f

/-- One unit of energy, including the two-label and singleton/empty slices. -/
theorem unit_poincare (q : ℕ) (f : Space V q) (hf : ∑ S, f S = 0) :
    ‖f‖ ^ 2 ≤ ⟪f, generator q f⟫ := by
  by_cases hN : 3 ≤ Fintype.card V
  · have h := centered_poincare q hN f hf
    have hNR : (3 : ℝ) ≤ Fintype.card V := by exact_mod_cast hN
    nlinarith [sq_nonneg ‖f‖]
  · by_cases hN₂ : Fintype.card V = 2
    · apply Analytic.norm_sq_le_inner_of_square_ge (generator q)
        (generator_symmetric q) (generator_positive q) _ f
        (centered_orthogonal_kernel q f hf)
      intro x
      rw [generator_symmetric, generator_two_idempotent q hN₂]
    · have : Subsingleton V := Fintype.card_le_one_iff_subsingleton.mp (by omega)
      have hm (a b : V) : moveOperator q a b = LinearMap.id (R := ℝ) (M := Space V q) := by
        rw [Subsingleton.elim b a, moveOperator_self]
      have hz : generator q f = 0 := by simp [generator, hm]
      have he := centered_orthogonal_kernel q f hf f hz
      rw [real_inner_self_eq_norm_sq] at he
      simp [he, hz]

theorem generator_constant (q : ℕ) (c : ℝ) :
    generator (α := V) q (WithLp.toLp 2 (fun _ => c)) = 0 := by
  ext S
  simp

theorem variance_le_energy (q : ℕ) (f : Space V q) :
    (∑ S, (f S - (∑ T, f T) / (Fintype.card (State V q) : ℝ)) ^ 2) ≤
      ⟪f, generator q f⟫ := by
  by_cases hne : Nonempty (State V q)
  · let := hne
    let c := (∑ S, f S) / (Fintype.card (State V q) : ℝ)
    let k : Space V q := WithLp.toLp 2 (fun _ => c)
    let x := f - k
    have hc : (Fintype.card (State V q) : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_pos (α := State V q)).ne'
    have hx : ∑ S, x S = 0 := by
      simp only [x, k, PiLp.sub_apply, Finset.sum_sub_distrib,
        Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      change (∑ S, f S) - (Fintype.card (State V q) : ℝ) * c = 0
      dsimp [c]
      field_simp
      ring
    have hk : generator q k = 0 := generator_constant q c
    have hgen : generator q x = generator q f := by
      simp only [x, map_sub, hk, sub_zero]
    have horth : ⟪k, generator q f⟫ = 0 := by
      rw [← generator_symmetric, hk, inner_zero_left]
    have h := unit_poincare q x hx
    rw [hgen, show ⟪x, generator q f⟫ = ⟪f, generator q f⟫ by
      simp only [x, inner_sub_left, horth, sub_zero]] at h
    simpa only [EuclideanSpace.real_norm_sq_eq, x, k, PiLp.sub_apply,
      WithLp.toLp_ofLp] using h
  · have : IsEmpty (State V q) := not_nonempty_iff.mp hne
    simp [PiLp.inner_apply]

end
end SharpSwitchGap.Johnson
