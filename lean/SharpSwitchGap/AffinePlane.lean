import SharpSwitchGap.WeightedCentering

namespace SharpSwitchGap.WeightedInteraction

noncomputable section
open scoped RealInnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem composition_of_affine_images
    (P Q : E →ₗ[ℝ] E) (hPs : P.IsSymmetric) (hQs : Q.IsSymmetric)
    (e u v : E) (c : ℝ)
    (hee : ⟪e,e⟫ = 1) (huu : ⟪u,u⟫ = 1) (hvv : ⟪v,v⟫ = 1)
    (hue : ⟪u,e⟫ = 0) (hve : ⟪v,e⟫ = 0) (huv : ⟪u,v⟫ = c)
    (hPe : P e = e) (hQe : Q e = e) (hPu : P u = u) (hQv : Q v = v)
    (hPQ : ∀ z, ∃ a b : ℝ, P (Q z) = a • e + b • u)
    (hQP : ∀ z, ∃ a b : ℝ, Q (P z) = a • e + b • v) :
    (∀ z, P (Q z) = ⟪z,e⟫ • e + (c * ⟪z,v⟫) • u) ∧
    P v = c • u ∧ Q u = c • v := by
  have hev : ⟪e,v⟫ = 0 := by rw [real_inner_comm, hve]
  have heu : ⟪e,u⟫ = 0 := by rw [real_inner_comm, hue]
  obtain ⟨a,b,hab⟩ := hQP u
  rw [hPu] at hab
  have ha : a = 0 := by
    have h := congrArg (fun z => ⟪z,e⟫) hab
    rw [hQs, hQe, hue] at h
    simpa only [inner_add_left, real_inner_smul_left, hee, hve,
      mul_one, mul_zero, add_zero] using h.symm
  have hb : b = c := by
    have h := congrArg (fun z => ⟪z,v⟫) hab
    rw [hQs, hQv, huv] at h
    simpa only [inner_add_left, real_inner_smul_left, hev, hvv,
      mul_one, mul_zero, zero_add] using h.symm
  have hQu : Q u = c • v := by simpa [ha,hb] using hab
  have hcomp (z : E) : P (Q z) = ⟪z,e⟫ • e + (c * ⟪z,v⟫) • u := by
    obtain ⟨a,b,hab⟩ := hPQ z
    have ha : a = ⟪z,e⟫ := by
      have h := congrArg (fun w => ⟪w,e⟫) hab
      rw [hPs, hPe, hQs, hQe] at h
      simpa only [inner_add_left, real_inner_smul_left, hee, hue,
        mul_one, mul_zero, add_zero] using h.symm
    have hb : b = c * ⟪z,v⟫ := by
      have h := congrArg (fun w => ⟪w,u⟫) hab
      rw [hPs, hPu, hQs, hQu, real_inner_smul_right] at h
      simpa only [inner_add_left, real_inner_smul_left, heu, huu,
        mul_one, mul_zero, zero_add] using h.symm
    simpa [ha,hb] using hab
  refine ⟨hcomp, ?_, hQu⟩
  simpa only [hQv, hve, hvv, mul_one, zero_smul, zero_add] using hcomp v

theorem disjoint_interaction_of_affine_images
    (P Q G R S : E →ₗ[ℝ] E)
    (hPs : P.IsSymmetric) (hQs : Q.IsSymmetric) (hGs : G.IsSymmetric)
    (hRs : R.IsSymmetric) (hSs : S.IsSymmetric)
    (hPi : ∀ z, P (P z) = P z) (hQi : ∀ z, Q (Q z) = Q z)
    (hGi : ∀ z, G (G z) = G z)
    (e u v : E) (c α β : ℝ) (hc : c ^ 2 < 1) (hc0 : c ≤ 0)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hfactor : α * β = c ^ 2)
    (hee : ⟪e,e⟫ = 1) (huu : ⟪u,u⟫ = 1) (hvv : ⟪v,v⟫ = 1)
    (hue : ⟪u,e⟫ = 0) (hve : ⟪v,e⟫ = 0) (huv : ⟪u,v⟫ = c)
    (hPe : P e = e) (hQe : Q e = e) (hPu : P u = u) (hQv : Q v = v)
    (hPQ : ∀ z, ∃ a b : ℝ, P (Q z) = a • e + b • u)
    (hQP : ∀ z, ∃ a b : ℝ, Q (P z) = a • e + b • v)
    (hRe : R e = 0) (hSe : S e = 0)
    (hGP : ∀ z, G (P z) = 0) (hGQ : ∀ z, G (Q z) = 0)
    (hRline : R (v - P v) = v - P v)
    (hSline : S (u - Q u) = u - Q u) (f : E) :
    2 * ‖G f‖ ^ 2 - α * ‖R f‖ ^ 2 - β * ‖S f‖ ^ 2 ≤
      2 * ⟪f - P f, f - Q f⟫ := by
  obtain ⟨hcomp,hPv,hQu⟩ := composition_of_affine_images P Q hPs hQs e u v c
    hee huu hvv hue hve huv hPe hQe hPu hQv hPQ hQP
  apply disjoint_interaction_with_constants P Q G R S hPs hQs hGs hRs hSs hPi hQi hGi
    e u v c α β hc hc0 hα hβ hfactor hee huu hvv hue hve hPe hQe hPu hQv
    ?_ (by rw [← hPe]; exact hGP e) hRe hSe hGP hGQ
    (by simpa only [hPv] using hRline) (by simpa only [hQu] using hSline) f
  intro z w
  rw [hPs, hcomp, inner_add_right, real_inner_smul_right, real_inner_smul_right]
  ring

end
end SharpSwitchGap.WeightedInteraction
