import OAI.Probability.SwitchChain.FiniteCellProjection
import OAI.Probability.SwitchChain.CellProjectionTransport

namespace SharpSwitchGap

noncomputable section
open scoped BigOperators RealInnerProductSpace

structure Compression (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] where
  restrict : E →ₗ[ℝ] F
  extend : F →ₗ[ℝ] E
  restrict_extend : ∀ f, restrict (extend f) = f
  adjoint : ∀ f g, ⟪restrict f,g⟫ = ⟪f,extend g⟫

namespace Compression
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def compress (C : Compression E F) (A : E →ₗ[ℝ] E) : F →ₗ[ℝ] F :=
  C.restrict.comp (A.comp C.extend)

def Commutes (C : Compression E F) (A : E →ₗ[ℝ] E) : Prop :=
  ∀ f, A (C.extend (C.restrict f)) = C.extend (C.restrict (A f))

theorem intertwine (C : Compression E F) (A : E →ₗ[ℝ] E) (hA : C.Commutes A) (f : E) :
    C.compress A (C.restrict f) = C.restrict (A f) := by
  change C.restrict (A (C.extend (C.restrict f))) = _
  rw [hA, C.restrict_extend]

theorem extend_compress (C : Compression E F) (A : E →ₗ[ℝ] E)
    (hA : C.Commutes A) (f : F) : C.extend (C.compress A f) = A (C.extend f) := by
  have h := hA (C.extend f)
  rw [C.restrict_extend] at h
  exact h.symm

theorem symmetric (C : Compression E F) (A : E →ₗ[ℝ] E) (hA : A.IsSymmetric) :
    (C.compress A).IsSymmetric := by
  intro f g
  change ⟪C.restrict (A (C.extend f)),g⟫ = ⟪f,C.restrict (A (C.extend g))⟫
  calc
    _ = ⟪A (C.extend f), C.extend g⟫ := C.adjoint _ _
    _ = ⟪C.extend f, A (C.extend g)⟫ := hA _ _
    _ = ⟪A (C.extend g), C.extend f⟫ := by rw [real_inner_comm]
    _ = ⟪C.restrict (A (C.extend g)), f⟫ := (C.adjoint _ _).symm
    _ = _ := by rw [real_inner_comm]

theorem idempotent (C : Compression E F) (A : E →ₗ[ℝ] E)
    (hA : C.Commutes A) (hi : ∀ f, A (A f) = A f) (f : F) :
    C.compress A (C.compress A f) = C.compress A f := by
  change C.restrict (A (C.extend (C.compress A f))) = _
  rw [C.extend_compress A hA, hi]
  rfl

theorem kills (C : Compression E F) (A B : E →ₗ[ℝ] E)
    (hB : C.Commutes B) (hAB : ∀ f, A (B f) = 0) (f : F) :
    C.compress A (C.compress B f) = 0 := by
  change C.restrict (A (C.extend (C.compress B f))) = _
  rw [C.extend_compress B hB, hAB, map_zero]

theorem fixes (C : Compression E F) (A : E →ₗ[ℝ] E)
    (hA : C.Commutes A) (f : E) (hf : A f = f) :
    C.compress A (C.restrict f) = C.restrict f := by
  rw [C.intertwine A hA, hf]

theorem extend_inner (C : Compression E F) (f g : F) :
    ⟪C.extend f,C.extend g⟫ = ⟪f,g⟫ := by
  rw [← C.adjoint, C.restrict_extend]

theorem error_range (C : Compression E F) (P Q R : E →ₗ[ℝ] E)
    (hP : C.Commutes P) (hQ : C.Commutes Q) (hR : C.Commutes R)
    (h : ∀ z, R (Q (P z) - P (Q (P z))) = Q (P z) - P (Q (P z))) (z : F) :
    C.compress R (C.compress Q (C.compress P z) -
      C.compress P (C.compress Q (C.compress P z))) =
      C.compress Q (C.compress P z) - C.compress P (C.compress Q (C.compress P z)) := by
  have hh := congrArg C.restrict (h (C.extend z))
  simpa only [← C.intertwine R hR, map_sub, ← C.intertwine P hP,
    ← C.intertwine Q hQ, C.restrict_extend] using hh

open OAI.Problem315
attribute [local instance] Classical.propDecidable

def pullLinear {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ] (e : Ω ≃ Ξ) :
    EuclideanSpace ℝ Ξ →ₗ[ℝ] EuclideanSpace ℝ Ω where
  toFun := CellProjectionTransport.pull e
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def ofEquiv {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (p : Ω → Prop) (e : {x // p x} ≃ Ξ) :
    Compression (EuclideanSpace ℝ Ω) (EuclideanSpace ℝ Ξ) where
  restrict := (pullLinear e.symm).comp (FiniteCellProjection.restrict p)
  extend := (FiniteCellProjection.extend p).comp (pullLinear e)
  restrict_extend f := by
    change CellProjectionTransport.pull e.symm
      (FiniteCellProjection.restrict p (FiniteCellProjection.extend p _)) = f
    rw [FiniteCellProjection.restrict_extend]
    change CellProjectionTransport.pull e.symm (CellProjectionTransport.pull e f) = f
    exact CellProjectionTransport.pull_symm e.symm f
  adjoint f g := by
    change ⟪CellProjectionTransport.pull e.symm (FiniteCellProjection.restrict p f),g⟫ =
      ⟪f,FiniteCellProjection.extend p (CellProjectionTransport.pull e g)⟫
    rw [← FiniteCellProjection.inner_restrict]
    have h := CellProjectionTransport.inner_pull e
      (CellProjectionTransport.pull e.symm (FiniteCellProjection.restrict p f)) g
    rw [CellProjectionTransport.pull_symm] at h
    exact h.symm

end Compression
end
end SharpSwitchGap
