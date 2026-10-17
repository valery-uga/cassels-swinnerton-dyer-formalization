import PfaffianDescent.VoisinGenericResidueChartLift
import PfaffianDescent.VoisinQuadraticMinorOpenChart

/-! Generic evaluation of regular functions on an integral chart is injective. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory
open AllCharacteristics.UniversalHomogeneous

universe u

theorem integralScheme_genericGammaEvaluation_injective
    (U : Scheme.{u}) [IsIntegral U] :
    Function.Injective (U.Γevaluation (genericPoint U)).hom := by
  letI : Nonempty (⊤ : U.Opens) :=
    ⟨⟨Classical.choice (inferInstance : Nonempty U), trivial⟩⟩
  haveI : IsSimpleRing (U.presheaf.stalk (genericPoint U)) := inferInstance
  exact (U.residue (genericPoint U)).hom.injective.comp
    (U.germToFunctionField_injective ⊤)

/-- The actual ordered generic residue point evaluates the affine chart's
global sections injectively. -/
theorem openImmersion_genericResidueLift_appTop_injective
    {U O : Scheme.{u}} [IsIntegral U] [IsIntegral O]
    (i : U ⟶ O) [IsOpenImmersion i] :
    Function.Injective
      ((openImmersion_genericResidueLift i).appTop.hom) := by
  let F := O.residueField (i (genericPoint U))
  let s : Spec (.of F) ⟶ U := openImmersion_genericResidueLift i
  let x : Spec (.of F) := IsLocalRing.closedPoint F
  have hsx : s x = genericPoint U := by
    change (Spec.map (asIso (i.residueFieldMap (genericPoint U))).inv ≫
      U.fromSpecResidueField (genericPoint U)) x = genericPoint U
    exact U.fromSpecResidueField_apply (genericPoint U) _
  intro a b hab
  have hnat_a := Scheme.Γevaluation_naturality_apply s x a
  have hnat_b := Scheme.Γevaluation_naturality_apply s x b
  have hres :
      (s.residueFieldMap x).hom
          (U.Γevaluation (s x) a) =
        (s.residueFieldMap x).hom
          (U.Γevaluation (s x) b) := by
    rw [hnat_a, hnat_b, hab]
  have heval := (s.residueFieldMap x).hom.injective hres
  rw [hsx] at heval
  exact integralScheme_genericGammaEvaluation_injective U
    heval

theorem openImmersion_genericResidueLift_sectionEvaluation_injective
    {U O : Scheme.{u}} [IsIntegral U] [IsIntegral O]
    (i : U ⟶ O) [IsOpenImmersion i] :
    let F := O.residueField (i (genericPoint U))
    let s := openImmersion_genericResidueLift i
    Function.Injective
      ((Scheme.ΓSpecIso (.of F)).hom.hom.comp s.appTop.hom) := by
  dsimp only
  let F := O.residueField (i (genericPoint U))
  have hΓ : Function.Injective (Scheme.ΓSpecIso (.of F)).hom.hom := by
    intro a b hab
    have h := congrArg (Scheme.ΓSpecIso (.of F)).inv.hom hab
    simpa only [← CommRingCat.comp_apply, Iso.hom_inv_id,
      CategoryTheory.ConcreteCategory.id_apply] using h
  exact hΓ.comp (openImmersion_genericResidueLift_appTop_injective i)

theorem openImmersion_genericSelectedPointLift_injective
    {U O : Scheme.{u}} [IsIntegral U] [IsIntegral O]
    (i : U ⟶ O) [IsOpenImmersion i]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (x : Fin 8 → Fin 4 → Γ(U, ⊤))
    (hm :
      let F := O.residueField (i (genericPoint U))
      let s := openImmersion_genericResidueLift i
      let f : Γ(U, ⊤) →+* F :=
        (Scheme.ΓSpecIso (.of F)).hom.hom.comp s.appTop.hom
      IsUnit (eightPointQuadraticEvaluationMinor (R := F) m
        (fun k j => f (x k j))).det) :
    let F := O.residueField (i (genericPoint U))
    let s := openImmersion_genericResidueLift i
    let f : Γ(U, ⊤) →+* F :=
      (Scheme.ΓSpecIso (.of F)).hom.hom.comp s.appTop.hom
    Function.Injective (quadraticMinorSelectedPointLift m x f hm) := by
  dsimp only at hm ⊢
  exact quadraticMinorSelectedPointLift_injective m x _ hm
    (openImmersion_genericResidueLift_sectionEvaluation_injective i)

/-- A nonzero determinant on the integral chart becomes a unit at its
actual ordered generic residue-field point. -/
theorem openImmersion_genericQuadraticMinor_isUnit
    {U O : Scheme.{u}} [IsIntegral U] [IsIntegral O]
    (i : U ⟶ O) [IsOpenImmersion i]
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (x : Fin 8 → Fin 4 → Γ(U, ⊤))
    (hdet : quadraticMinorDet m x ≠ 0) :
    let F := O.residueField (i (genericPoint U))
    let s := openImmersion_genericResidueLift i
    let f : Γ(U, ⊤) →+* F :=
      (Scheme.ΓSpecIso (.of F)).hom.hom.comp s.appTop.hom
    IsUnit (eightPointQuadraticEvaluationMinor (R := F) m
      (fun k j => f (x k j))).det := by
  dsimp only
  let F := O.residueField (i (genericPoint U))
  let s := openImmersion_genericResidueLift i
  let f : Γ(U, ⊤) →+* F :=
    (Scheme.ΓSpecIso (.of F)).hom.hom.comp s.appTop.hom
  have hmap : (eightPointQuadraticEvaluationMinor (R := F) m
      (fun k j => f (x k j))).det = f (quadraticMinorDet m x) := by
    change (eightPointQuadraticEvaluationMinor (R := F) m
      (fun k j => f (x k j))).det =
        f (eightPointQuadraticEvaluationMinor m x).det
    rw [RingHom.map_det, RingHom.mapMatrix_apply,
      eightPointQuadraticEvaluationMinor_map]
  rw [hmap]
  apply isUnit_iff_ne_zero.mpr
  simpa only [map_zero] using
    ((openImmersion_genericResidueLift_sectionEvaluation_injective i).ne_iff.mpr
      hdet)

end PfaffianDescent
