import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCubicSupportFinite
import PfaffianDescent.VoisinDegreeElevenSerreIncidenceFiniteIsoFieldPoint
import Mathlib.Algebra.Field.Equiv

/-! # Canonical actual retained-support coefficient field and unchanged degree -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceCubicSupport_coefficient_field_degree
    {K L F : Type u} [Field K] [Field L] [Field F] [Algebra K L] [Algebra K F]
    [Module.Finite K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (i : Spec (.of L) ⟶ hypersurface p hp)
    (hi : i ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L)))
    (hfield : IsField (L ⊗[K] F)) :
    let D := pullback
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp) i
    let q := pullback.fst
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp) i ≫
      hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))
    letI : IsFinite q := serreIncidenceCubicSupport_finite p hp i hi
    letI := finiteSchemeCoefficientAlgebra q
    IsField Γ(D, ⊤) ∧ Module.finrank F Γ(D, ⊤) = Module.finrank K L := by
  let D := pullback
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp) i
  let q := pullback.fst
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp) i ≫
    hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))
  letI : IsFinite q := serreIncidenceCubicSupport_finite p hp i hi
  letI := finiteSchemeCoefficientAlgebra q
  letI : Field (L ⊗[K] F) := hfield.toField
  letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := L) (B := F)
  let e := serreIncidenceFiniteIsoFieldPointEquiv q
    (serreIncidenceCubicSupportPullbackIso (F := F) p hp i hi)
    (serreIncidenceCubicSupportPullbackIso_toField (F := F) p hp i hi)
  refine ⟨MulEquiv.isField hfield e.toRingEquiv.toMulEquiv, ?_⟩
  rw [e.toLinearEquiv.finrank_eq]
  exact serreIncidenceSupportTensorRight_finrank

end PfaffianDescent
