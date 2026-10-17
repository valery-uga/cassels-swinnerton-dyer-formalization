import PfaffianDescent.VoisinDegreeElevenSerreIncidenceCubicSupportPullback

/-! # Actual finiteness of the entire retained cubic support -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
namespace PfaffianDescent
open ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceCubicSupport_finite
    {K L F : Type u} [Field K] [Field L] [Field F] [Algebra K L] [Algebra K F]
    [Module.Finite K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (i : Spec (.of L) ⟶ hypersurface p hp)
    (hi : i ≫ hypersurfaceToBase p hp = Spec.map (CommRingCat.ofHom (algebraMap K L))) :
    IsFinite (pullback.fst
      (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp) i ≫
      hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F))) := by
  letI := Algebra.TensorProduct.rightAlgebra (R := K) (A := L) (B := F)
  letI : Module.Finite F (L ⊗[K] F) := serreIncidenceSupportTensorRight_finite
  letI : IsFinite (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := K) (A := L) (B := F)).toRingHom)) :=
    (IsFinite.SpecMap_iff _).mpr (by
      change (algebraMap F (L ⊗[K] F)).Finite
      rw [RingHom.finite_algebraMap]
      infer_instance)
  let e := serreIncidenceCubicSupportPullbackIso (F := F) p hp i hi
  rw [← e.inv_hom_id_assoc (pullback.fst
    (cubicPointTraceFieldBaseChangeCubicCoefficientMap (algebraMap K F) p hp) i ≫
    hypersurfaceToBase (p.map (algebraMap K F)) (hp.map (algebraMap K F)))]
  rw [serreIncidenceCubicSupportPullbackIso_toField]
  infer_instance

end PfaffianDescent
