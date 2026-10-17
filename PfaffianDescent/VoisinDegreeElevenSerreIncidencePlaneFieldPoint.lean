import PfaffianDescent.VoisinDegreeElevenSerreIncidencePlaneBaseChange
import PfaffianDescent.VoisinFixedLinearSystemUniversalFamily

/-! # The actual plane frame over every actual field-valued configuration -/
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem serreIncidenceAffineFieldPoint_spec
    {F : Type u} [Field F] {B : Scheme.{u}} [IsAffine B]
    (c : Spec (.of F) ⟶ B) :
    Spec.map (CommRingCat.ofHom (fieldPointΓevaluation c)) ≫ B.isoSpec.inv = c := by
  have hβ : CommRingCat.ofHom (fieldPointΓevaluation c) =
      c.appTop ≫ (Scheme.ΓSpecIso (.of F)).hom := by
    ext x
    exact fieldPointΓevaluation_eq_appTop c x
  rw [hβ, Spec.map_comp, SpecMap_ΓSpecIso_hom, ← Scheme.toSpecΓ_naturality,
    Category.assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]

def serreIncidencePlaneFieldPointIso
    {F : Type u} [Field F] {B I : Scheme.{u}} [IsAffine B]
    (π : I ⟶ B)
    (e : scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) Γ(B, ⊤))) ≅ I)
    (he : e.hom ≫ π = toBase (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 3) Γ(B, ⊤))) ≫ B.isoSpec.inv)
    (c : Spec (.of F) ⟶ B) :
    scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)) ≅ pullback π c :=
  serreIncidencePlaneBaseChangeIso B.isoSpec.symm π e he (fieldPointΓevaluation c) c
    (serreIncidenceAffineFieldPoint_spec c)

@[reassoc]
theorem serreIncidencePlaneFieldPointIso_frame
    {F : Type u} [Field F] {B I : Scheme.{u}} [IsAffine B]
    (π : I ⟶ B)
    (e : scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) Γ(B, ⊤))) ≅ I)
    (he : e.hom ≫ π = toBase (⊥ : HomogeneousIdeal
      (homogeneousSubmodule (Fin 3) Γ(B, ⊤))) ≫ B.isoSpec.inv)
    (c : Spec (.of F) ⟶ B) :
    (serreIncidencePlaneFieldPointIso π e he c).hom ≫ pullback.fst π c ≫ π =
      toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 3) F)) ≫ c :=
  serreIncidencePlaneBaseChangeIso_frame B.isoSpec.symm π e he
    (fieldPointΓevaluation c) c (serreIncidenceAffineFieldPoint_spec c)

end PfaffianDescent
