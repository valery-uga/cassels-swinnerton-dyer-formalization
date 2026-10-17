import PfaffianDescent.CubicPointCompatibleQuadraticResidue
import PfaffianDescent.VoisinMixedTwistLocal
import PfaffianDescent.CanonicalPointRestriction

/-! # Actual homogeneous-section insertion into the mixed pairing -/
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct
namespace PfaffianDescent.ProjectiveNegativeTwist
universe u
variable {A σ : Type u} [CommRing A] [SetLike σ A]
  [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

set_option backward.isDefEq.respectTransparency false in
/-- Inserting the actual global section of a quadratic into the mixed tensor
pairing is exactly the actual negative-twist multiplication morphism. -/
theorem cubicPointQuadraticRestrictionHomogeneous_insertion
    (q : 𝒜 2) :
    (schemeModuleTensorUnitLeftIso (sheafOfModules 𝒜 3)).inv ≫
      schemeModuleTensorMap
        ((positiveSheafOfModules 𝒜 2).unitHomEquiv.symm
          (positiveGlobalSectionOfHomogeneous 𝒜 2 q))
        (𝟙 (sheafOfModules 𝒜 3)) ≫
      positiveNegativeDifferencePairing 𝒜 2 3 (by omega) =
    mulHomogeneous 𝒜 q 1 := by
  let a := (positiveSheafOfModules 𝒜 2).unitHomEquiv.symm
    (positiveGlobalSectionOfHomogeneous 𝒜 2 q)
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (Proj 𝒜).ringCatSheaf.obj)
  have hunit : (schemeModuleTensorUnitLeftIso (sheafOfModules 𝒜 3)).hom =
      (adj.homEquiv _ _).symm
        (schemeModuleTensorUnitLeftRawIso (sheafOfModules 𝒜 3)).hom := by
    rw [Adjunction.homEquiv_counit]
    rfl
  have hraw :
      PresheafOfModules.Monoidal.tensorHom a.val
        (𝟙 (modulePresheaf 𝒜 3)) ≫
        positiveNegativeDifferencePairingPresheaf 𝒜 2 3 (by omega) =
      (schemeModuleTensorUnitLeftRawIso (sheafOfModules 𝒜 3)).hom ≫
        (mulHomogeneous 𝒜 q 1).val := by
    ext1 V
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro r y
    apply Subtype.ext
    funext z
    change ((r.1 z).val *
      (PresheafOfModules.sections.eval (positiveGlobalSectionOfHomogeneous 𝒜 2 q) V).1 z) *
        y.1 z =
      algebraMap A (PositiveFiber 𝒜 z.1) (q : A) * ((r.1 z).val * y.1 z)
    have hq :
        (PresheafOfModules.sections.eval (positiveGlobalSectionOfHomogeneous 𝒜 2 q) V).1 z =
        algebraMap A (PositiveFiber 𝒜 z.1) (q : A) := by
      rfl
    rw [hq]
    ring
  have h : schemeModuleTensorMap a (𝟙 (sheafOfModules 𝒜 3)) ≫
        positiveNegativeDifferencePairing 𝒜 2 3 (by omega) =
      (schemeModuleTensorUnitLeftIso (sheafOfModules 𝒜 3)).hom ≫
        mulHomogeneous 𝒜 q 1 := by
    rw [schemeModuleTensorMap_eq_sheafification]
    apply (adj.homEquiv _ _).injective
    erw [adj.homEquiv_naturality_left]
    have hpair : (adj.homEquiv _ _ )
        (positiveNegativeDifferencePairing 𝒜 2 3 (by omega)) =
        positiveNegativeDifferencePairingPresheaf 𝒜 2 3 (by omega) :=
      (adj.homEquiv _ _).apply_symm_apply _
    rw [hpair]
    erw [adj.homEquiv_naturality_right]
    rw [hunit, Equiv.apply_symm_apply]
    exact hraw
  change (schemeModuleTensorUnitLeftIso (sheafOfModules 𝒜 3)).inv ≫
    schemeModuleTensorMap a (𝟙 (sheafOfModules 𝒜 3)) ≫
    positiveNegativeDifferencePairing 𝒜 2 3 (by omega) = _
  rw [h]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The representing morphism of an actual global section maps the canonical
unit stalk generator to its actual germ. -/
theorem cubicPointQuadraticRestriction_section_germ
    {X : Scheme.{u}} (P : X.Modules) (s : P.sections) (x : X) :
    (schemeModuleStalkModuleFunctor X x).map (P.unitHomEquiv.symm s)
      ((schemeModuleUnitStalkIso X x).inv 1) =
    P.presheaf.germ ⊤ x trivial (PresheafOfModules.sections.eval s (op ⊤)) := by
  have hunit : (schemeModuleUnitStalkIso X x).inv 1 =
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf).presheaf.germ ⊤ x trivial (1 : Γ(X, ⊤)) := by
    apply (ConcreteCategory.bijective_of_isIso (schemeModuleUnitStalkIso X x).hom).1
    rw [Iso.inv_hom_id_apply]
    change 1 = schemeModuleSectionStalkCoordinateAddHom ⊤ x trivial (SheafOfModules.unit X.ringCatSheaf)
      (schemeModuleUnitStalkIso X x) (1 : Γ(X, ⊤))
    rw [schemeModuleSectionStalkCoordinateAddHom_unit]
    simp
  rw [hunit, schemeModuleStalkModuleFunctor_map_germ]
  congr 1
  change (P.unitHomEquiv (P.unitHomEquiv.symm s)).val (op ⊤) = s.val (op ⊤)
  rw [Equiv.apply_symm_apply]

end PfaffianDescent.ProjectiveNegativeTwist
