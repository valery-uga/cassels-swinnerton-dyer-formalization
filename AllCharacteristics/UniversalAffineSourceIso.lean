import AllCharacteristics.UniversalAffineSourceField
import AllCharacteristics.Unirationality
import AllCharacteristics.FunctionFieldRationalMapDominance
import Mathlib.Algebra.MvPolynomial.Equiv

namespace AllCharacteristics

open AlgebraicGeometry CategoryTheory MvPolynomial
open scoped AlgebraicGeometry

universe u

/-- The nine independent variables in the source, indexed as six plus three. -/
noncomputable def kollarUniversalParameterIndexEquiv :
    ULift.{u} (Fin 9) ≃ (Fin 2 × Fin 3) ⊕ Fin 3 :=
  Fintype.equivOfCardEq (by simp)

/-- The iterated coefficient ring is literally the polynomial algebra on
nine variables over the original ground field. -/
noncomputable def kollarUniversalParameterPolynomialEquiv
    (k : Type u) [Field k] :
    MvPolynomial (ULift.{u} (Fin 9)) k ≃ₐ[k] KollarUniversalParameterRing k :=
  (MvPolynomial.renameEquiv k kollarUniversalParameterIndexEquiv).trans
    (MvPolynomial.sumAlgEquiv k (Fin 2 × Fin 3) (Fin 3))

/-- The actual universal source is affine nine-space over the original field. -/
noncomputable def kollarUniversalSourceAffineIso
    (k : Type u) [Field k] :
    AffineSpace (ULift.{u} (Fin 9)) (Spec (.of k)) ≅
      Spec (.of (KollarUniversalParameterRing k)) :=
  AffineSpace.SpecIso _ (.of k) ≪≫
    Scheme.Spec.mapIso
      (kollarUniversalParameterPolynomialEquiv k).toRingEquiv.toCommRingCatIso.symm.op

set_option backward.isDefEq.respectTransparency.types false in
/-- This isomorphism retains the original ground-field structure map. -/
theorem kollarUniversalSourceAffineIso_over
    (k : Type u) [Field k] :
    (kollarUniversalSourceAffineIso k).hom ≫ kollarUniversalSourceToBase k =
      (AffineSpace (ULift.{u} (Fin 9)) (Spec (.of k)) ↘ Spec (.of k)) := by
  let E := kollarUniversalParameterPolynomialEquiv k
  let c : k →+* KollarUniversalParameterRing k :=
    (MvPolynomial.C : MvPolynomial (Fin 3) k →+* KollarUniversalParameterRing k).comp
      MvPolynomial.C
  have hcoeff : E.symm.toRingHom.comp c = MvPolynomial.C := by
    apply RingHom.ext
    intro r
    exact E.symm.commutes r
  have hcat : CommRingCat.ofHom c ≫
      CommRingCat.ofHom E.symm.toRingHom = CommRingCat.ofHom MvPolynomial.C := by
    exact CommRingCat.hom_ext hcoeff
  unfold kollarUniversalSourceAffineIso kollarUniversalSourceToBase
  simp only [Iso.trans_hom, Scheme.Spec.mapIso_hom, Category.assoc]
  change (AffineSpace.SpecIso (ULift.{u} (Fin 9)) (.of k)).hom ≫
    Spec.map (CommRingCat.ofHom E.symm.toRingHom) ≫ Spec.map (CommRingCat.ofHom c) = _
  rw [← Spec.map_comp, hcat]
  have hi := AffineSpace.SpecIso_inv_over (n := ULift.{u} (Fin 9)) (CommRingCat.of k)
  calc
    _ = (AffineSpace.SpecIso (ULift.{u} (Fin 9)) (.of k)).hom ≫
        (AffineSpace.SpecIso (ULift.{u} (Fin 9)) (.of k)).inv ≫
          (AffineSpace (ULift.{u} (Fin 9)) (Spec (.of k)) ↘ Spec (.of k)) := by rw [hi]
    _ = _ := Iso.hom_inv_id_assoc _ _

end AllCharacteristics

namespace AlgebraicGeometry

open CategoryTheory

universe u

/-- The actual stalk homomorphism on function fields supplied by a scheme
isomorphism. -/
noncomputable def Scheme.isoFunctionFieldRingHom
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (e : X ≅ Y) :
    Y.functionField →+* X.functionField := by
  have hgen : e.hom (genericPoint X) = genericPoint Y :=
    genericPoint_eq_of_isOpenImmersion e.hom
  exact ((Y.presheaf.stalkCongr (.of_eq hgen.symm)).hom ≫
    e.hom.stalkMap (genericPoint X)).hom

/-- The function-field homomorphism commutes with the actual generic-point
morphisms of the schemes. -/
theorem Scheme.isoFunctionFieldRingHom_spec
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y] (e : X ≅ Y) :
    Spec.map (CommRingCat.ofHom (Scheme.isoFunctionFieldRingHom e)) ≫
      Y.fromSpecStalk (genericPoint Y) = X.fromSpecStalk (genericPoint X) ≫ e.hom := by
  have hgen : e.hom (genericPoint X) = genericPoint Y :=
    genericPoint_eq_of_isOpenImmersion e.hom
  unfold Scheme.isoFunctionFieldRingHom
  change Spec.map ((Y.presheaf.stalkCongr (.of_eq hgen.symm)).hom ≫
    e.hom.stalkMap (genericPoint X)) ≫ Y.fromSpecStalk (genericPoint Y) = _
  rw [Spec.map_comp, Category.assoc]
  have hcongr : Spec.map (Y.presheaf.stalkCongr (.of_eq hgen.symm)).hom ≫
      Y.fromSpecStalk (genericPoint Y) = Y.fromSpecStalk (e.hom (genericPoint X)) := by
    rw [TopCat.Presheaf.stalkCongr_hom]
    exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk _
  rw [hcongr]
  exact Scheme.SpecMap_stalkMap_fromSpecStalk e.hom

end AlgebraicGeometry

namespace AllCharacteristics.HomogeneousProjective

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

set_option backward.isDefEq.respectTransparency.types false in
/-- A generic-valued point over a source scheme actually isomorphic to
affine space produces unirationality in the standard affine-source sense.
All function-field transport and coefficient compatibility are constructed. -/
theorem isUnirationalOver_of_affineIso_genericFieldPoint
    {k : Type u} [Field k] {S Y : Scheme.{u}} [IsIntegral S]
    (s : S ⟶ Spec (.of k)) (y : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType y] [IrreducibleSpace Y]
    (n : ℕ) (e : AffineSpace (ULift.{u} (Fin n)) (Spec (.of k)) ≅ S)
    (he : e.hom ≫ s =
      (AffineSpace (ULift.{u} (Fin n)) (Spec (.of k)) ↘ Spec (.of k)))
    (q : Spec S.functionField ⟶ Y)
    (hq : q ≫ y = S.fromSpecStalk (genericPoint S) ≫ s)
    (hgeneric : q (genericPoint (Spec S.functionField)) = genericPoint Y) :
    IsUnirationalOver k Y y := by
  let A := AffineSpace (ULift.{u} (Fin n)) (Spec (.of k))
  let a : A ⟶ Spec (.of k) := A ↘ Spec (.of k)
  let φ : S.functionField ⟶ A.functionField :=
    CommRingCat.ofHom (Scheme.isoFunctionFieldRingHom e)
  let qA : Spec A.functionField ⟶ Y := Spec.map φ ≫ q
  have hφ : Spec.map φ ≫ S.fromSpecStalk (genericPoint S) =
      A.fromSpecStalk (genericPoint A) ≫ e.hom :=
    Scheme.isoFunctionFieldRingHom_spec e
  have hqA : qA ≫ y = A.fromSpecStalk (genericPoint A) ≫ a := by
    dsimp only [qA]
    rw [Category.assoc, hq, ← Category.assoc, hφ, Category.assoc, he]
  letI : Unique (Spec S.functionField) :=
    inferInstanceAs (Unique (Spec (.of S.functionField)))
  have hgA : qA (genericPoint (Spec A.functionField)) = genericPoint Y := by
    change q ((Spec.map φ)
      (genericPoint (Spec A.functionField))) = genericPoint Y
    have hpoint : (Spec.map φ)
        (genericPoint (Spec A.functionField)) = genericPoint (Spec S.functionField) :=
      Subsingleton.elim _ _
    rw [hpoint]
    exact hgeneric
  obtain ⟨f, hfdom, hfbase⟩ := dominant_rationalMap_of_functionField_map a y qA hqA hgA
  exact ⟨n, f, hfdom, hfbase⟩

end AllCharacteristics.HomogeneousProjective
