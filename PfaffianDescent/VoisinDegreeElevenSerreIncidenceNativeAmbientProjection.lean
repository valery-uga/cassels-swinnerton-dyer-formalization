import PfaffianDescent.VoisinDegreeElevenSerreIncidenceNativeAmbientChart

/-! # Exact projections of actual relative section projective spaces and charts -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

@[reassoc]
theorem serreIncidenceNativeAmbientProjectiveIso_hom_fst
    {K : Type u} [CommRing K] {B : Scheme.{u}} [IsAffine B]
    (b : B ⟶ Spec (.of K)) :
    (serreIncidenceNativeAmbientProjectiveIso b).hom ≫
      pullback.fst b (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K))) =
    toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) Γ(B, ⊤))) ≫ B.isoSpec.inv := by
  have h := congrArg (fun q => q ≫ B.isoSpec.inv)
    (projectiveBaseChangeIso_hom_snd (affineFunctionHom b)
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K))
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) Γ(B, ⊤))) (by simp))
  simpa only [serreIncidenceNativeAmbientProjectiveIso, Iso.trans_hom, asIso_hom,
    Category.assoc, pullback.map, pullback.lift_fst, pullback.lift_fst_assoc,
    pullbackSymmetry_hom_comp_fst, pullbackSymmetry_hom_comp_fst_assoc] using h

@[reassoc]
theorem serreIncidenceNativeAmbientProjectiveIso_hom_snd
    {K : Type u} [CommRing K] {B : Scheme.{u}} [IsAffine B]
    (b : B ⟶ Spec (.of K)) :
    (serreIncidenceNativeAmbientProjectiveIso b).hom ≫
      pullback.snd b (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K))) =
    projectiveCoefficientMap (affineFunctionHom b)
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) K))
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 9) Γ(B, ⊤))) (by simp) := by
  simp [serreIncidenceNativeAmbientProjectiveIso, pullback.map, Category.assoc,
    projectiveBaseChangeIso_hom_fst]

end PfaffianDescent
