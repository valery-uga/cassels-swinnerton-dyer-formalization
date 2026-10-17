import PfaffianDescent.ActualFieldPointCanonicalInverseTwistTensor
import PfaffianDescent.ActualOriginalPositiveTwoNativeJetEmbedding
import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-! SOURCE ONLY / UNVERIFIED. The LITERAL tensor-negative-two quotient
uses the canonical inverse pairing, not the intermediate derived-frame
source map. Its native-jet compatibility with the accepted positive-two
untwisting still requires the global fiber pairing/coherence comparison. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

section
variable {K : Type u} [Field K]
  (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
  (P : closedPoints (hypersurface p hp))
local notation "κ" => CommRingCat.carrier (Scheme.residueField (hypersurface p hp) (Subtype.val P))
local notation "rP" => Scheme.fromSpecResidueField (hypersurface p hp) (Subtype.val P)
local notation "E" => ModuleCat.carrier (ActualOriginalPositiveTwoFiber p hp P)
local notation "W" => ModuleCat.carrier
  (Functor.obj (moduleSpecΓFunctor (R := CommRingCat.of κ))
    (Functor.obj (Scheme.Modules.pullback rP) (schemeRelativeDifferentials (hypersurfaceToBase p hp))))
local notation "B" => ModuleCat.carrier
  (ActualFieldPointNegativeTwistFiber (K := K) (L := κ) (equationIdeal p hp) rP 2)

/-- Actual canonical positive-negative insertion at the SAME original
point and the SAME original relative differential sheaf. -/
def actualOriginalCanonicalTensorNegativeTwoSourceEquiv : W ≃ₗ[κ] E ⊗[κ] B :=
  actualFieldPointCanonicalInverseTwistTensorEquiv (K := K) (L := κ)
    (equationIdeal p hp) rP (schemeRelativeDifferentials (hypersurfaceToBase p hp)) 2

/-- Literal q tensor id on the actual negative-two line fiber. -/
def actualOriginalCanonicalTensorNegativeTwoQuotient
    {N : Type u} [AddCommGroup N] [Module κ N] (q : E →ₗ[κ] N) :
    W →ₗ[κ] N ⊗[κ] B :=
  (TensorProduct.map q (LinearMap.id : B →ₗ[κ] B)).comp
    (actualOriginalCanonicalTensorNegativeTwoSourceEquiv p hp P).toLinearMap

theorem actualOriginalCanonicalTensorNegativeTwoQuotient_surjective
    {N : Type u} [AddCommGroup N] [Module κ N] (q : E →ₗ[κ] N)
    (hq : Function.Surjective q) :
    Function.Surjective (actualOriginalCanonicalTensorNegativeTwoQuotient p hp P q) :=
  (TensorProduct.map_surjective (g := q)
    (g' := (LinearMap.id : B →ₗ[κ] B)) hq (fun x => ⟨x, rfl⟩)).comp
    (actualOriginalCanonicalTensorNegativeTwoSourceEquiv p hp P).surjective

/-- Tensoring with the actual negative fiber preserves the target line;
the target identification is internally derived and does not identify the
canonical source map with the intermediate source map. -/
theorem actualOriginalCanonicalTensorNegativeTwoTarget_finrank_one
    {N : Type u} [AddCommGroup N] [Module κ N] (hN : Module.finrank κ N = 1) :
    Module.finrank κ (N ⊗[κ] B) = 1 := by
  let e : N ⊗[κ] B ≃ₗ[κ] N :=
    TensorProduct.congr (LinearEquiv.refl κ N)
      (actualFieldPointNegativeTwistFiberEquiv (K := K) (L := κ)
        (equationIdeal p hp) rP 2) ≪≫ₗ TensorProduct.rid κ N
  exact e.finrank_eq.trans hN

end
end PfaffianDescent
