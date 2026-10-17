import PfaffianDescent.FormalCoproductOverCech
import PfaffianDescent.SheafModulePushforwardExact

/-!
# Section representers of formal coproducts on an over-site

Restriction to the site over `X` carries a coproduct of section representers
to the corresponding coproduct of locally represented sheaves.  This file
packages that comparison naturally in the formal coproduct.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace PfaffianDescent

universe u

variable {C : Type u} [SmallCategory C] [HasFiniteProducts C]
variable {J : GrothendieckTopology C}
variable (R : Sheaf J RingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The explicit coproduct form of the section-representer comparison. -/
noncomputable def overSectionRepresenterFormalCoproductIsoExplicit (X : C)
    (Q : FormalCoproduct.{u} C) :
    (∐ fun i : Q.I =>
      (sectionRepresenterFunctor (R.over X)).obj ((Over.star X).obj (Q.obj i))) ≅
      (SheafOfModules.overFunctor R X).obj
        (∐ fun i : Q.I => (sectionRepresenterFunctor R).obj (Q.obj i)) := by
  letI : (SheafOfModules.overFunctor R X).IsLeftAdjoint :=
    (SheafOfModules.overPushforwardOverAdj (R := R) X).isLeftAdjoint
  exact Sigma.mapIso (fun i => overSectionRepresenterIso R X (Q.obj i)) ≪≫
    (PreservesCoproduct.iso (SheafOfModules.overFunctor R X)
      (fun i : Q.I => (sectionRepresenterFunctor R).obj (Q.obj i))).symm

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
lemma sectionRepresenter_ι_overSectionRepresenterFormalCoproductIsoExplicit_hom
    (X : C) (Q : FormalCoproduct.{u} C) (i : Q.I) :
    Sigma.ι (fun j : Q.I =>
        (sectionRepresenterFunctor (R.over X)).obj ((Over.star X).obj (Q.obj j))) i ≫
      (overSectionRepresenterFormalCoproductIsoExplicit R X Q).hom =
    (overSectionRepresenterIso R X (Q.obj i)).hom ≫
      (SheafOfModules.overFunctor R X).map
        (Sigma.ι (fun j : Q.I => (sectionRepresenterFunctor R).obj (Q.obj j)) i) := by
  letI : (SheafOfModules.overFunctor R X).IsLeftAdjoint :=
    (SheafOfModules.overPushforwardOverAdj (R := R) X).isLeftAdjoint
  dsimp only [overSectionRepresenterFormalCoproductIsoExplicit]
  simp only [Iso.trans_hom, Sigma.ι_mapIso_hom_assoc]
  change
    (overSectionRepresenterIso R X (Q.obj i)).hom ≫
      Sigma.ι (fun j : Q.I =>
        (SheafOfModules.overFunctor R X).obj ((sectionRepresenterFunctor R).obj (Q.obj j))) i ≫
      (PreservesCoproduct.iso (SheafOfModules.overFunctor R X)
        (fun j : Q.I => (sectionRepresenterFunctor R).obj (Q.obj j))).inv =
    (overSectionRepresenterIso R X (Q.obj i)).hom ≫
      (SheafOfModules.overFunctor R X).map
        (Sigma.ι (fun j : Q.I => (sectionRepresenterFunctor R).obj (Q.obj j)) i)
  rw [PreservesCoproduct.inv_hom, ι_comp_sigmaComparison]

set_option backward.isDefEq.respectTransparency false in
lemma overSectionRepresenterFormalCoproductIsoExplicit_hom_naturality (X : C)
    {Q Q' : FormalCoproduct.{u} C} (q : Q ⟶ Q') :
    (Sigma.desc (fun i : Q.I =>
        (sectionRepresenterFunctor (R.over X)).map ((Over.star X).map (q.φ i)) ≫
          Sigma.ι (fun j : Q'.I =>
            (sectionRepresenterFunctor (R.over X)).obj ((Over.star X).obj (Q'.obj j))) (q.f i))) ≫
      (overSectionRepresenterFormalCoproductIsoExplicit R X Q').hom =
    (overSectionRepresenterFormalCoproductIsoExplicit R X Q).hom ≫
      (SheafOfModules.overFunctor R X).map
        (Sigma.desc (fun i : Q.I =>
          (sectionRepresenterFunctor R).map (q.φ i) ≫
            Sigma.ι (fun j : Q'.I => (sectionRepresenterFunctor R).obj (Q'.obj j)) (q.f i))) := by
  letI : (SheafOfModules.overFunctor R X).IsLeftAdjoint :=
    (SheafOfModules.overPushforwardOverAdj (R := R) X).isLeftAdjoint
  apply Sigma.hom_ext
  intro i
  rw [Sigma.ι_desc_assoc]
  rw [sectionRepresenter_ι_overSectionRepresenterFormalCoproductIsoExplicit_hom_assoc]
  rw [Category.assoc]
  rw [sectionRepresenter_ι_overSectionRepresenterFormalCoproductIsoExplicit_hom]
  rw [← Category.assoc]
  rw [overSectionRepresenterIso_hom_naturality]
  rw [Category.assoc, ← Functor.map_comp]
  rw [← Functor.map_comp]
  rw [Sigma.ι_desc]

/-- The section-representer comparison extended componentwise to formal
coproducts. -/
noncomputable def overSectionRepresenterFormalCoproductIso (X : C)
    (Q : FormalCoproduct.{u} C) :
    (sectionRepresenterFormalCoproductFunctor (R.over X)).obj
        ((FormalCoproduct.mapFunctor (Over.star X)).obj Q) ≅
      (SheafOfModules.overFunctor R X).obj
        ((sectionRepresenterFormalCoproductFunctor R).obj Q) :=
  overSectionRepresenterFormalCoproductIsoExplicit R X Q

set_option backward.isDefEq.respectTransparency false in
lemma overSectionRepresenterFormalCoproductIso_hom_naturality (X : C)
    {Q Q' : FormalCoproduct.{u} C} (q : Q ⟶ Q') :
    (sectionRepresenterFormalCoproductFunctor (R.over X)).map
        ((FormalCoproduct.mapFunctor (Over.star X)).map q) ≫
      (overSectionRepresenterFormalCoproductIso R X Q').hom =
    (overSectionRepresenterFormalCoproductIso R X Q).hom ≫
      (SheafOfModules.overFunctor R X).map
        ((sectionRepresenterFormalCoproductFunctor R).map q) := by
  change
    (Sigma.desc (fun i : Q.I =>
        (sectionRepresenterFunctor (R.over X)).map ((Over.star X).map (q.φ i)) ≫
          Sigma.ι (fun j : Q'.I =>
            (sectionRepresenterFunctor (R.over X)).obj ((Over.star X).obj (Q'.obj j))) (q.f i))) ≫
      (overSectionRepresenterFormalCoproductIsoExplicit R X Q').hom =
    (overSectionRepresenterFormalCoproductIsoExplicit R X Q).hom ≫
      (SheafOfModules.overFunctor R X).map
        (Sigma.desc (fun i : Q.I =>
          (sectionRepresenterFunctor R).map (q.φ i) ≫
            Sigma.ι (fun j : Q'.I => (sectionRepresenterFunctor R).obj (Q'.obj j)) (q.f i)))
  exact overSectionRepresenterFormalCoproductIsoExplicit_hom_naturality R X q

/-- Naturality of the over-site comparison after extension to formal
coproducts. -/
noncomputable def overSectionRepresenterFormalCoproductNatIso (X : C) :
    FormalCoproduct.mapFunctor (Over.star X) ⋙
        sectionRepresenterFormalCoproductFunctor (R.over X) ≅
      sectionRepresenterFormalCoproductFunctor R ⋙
        SheafOfModules.overFunctor R X :=
  NatIso.ofComponents
    (fun Q => overSectionRepresenterFormalCoproductIso R X Q)
    (fun q => overSectionRepresenterFormalCoproductIso_hom_naturality R X q)

/-- The full simplicial over-site comparison for the section-representer
Cech object. -/
noncomputable def overSectionRepresenterCechNatIso
    [HasFiniteLimits C] (X : C) {ι : Type u} (U : ι → C) :
    letI : HasFiniteProducts (Over X) :=
      CategoryTheory.Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks
    sectionRepresenterCechSimplicial (R.over X)
        (fun i => (Over.star X).obj (U i)) ≅
      sectionRepresenterCechSimplicial R U ⋙
        SheafOfModules.overFunctor R X := by
  letI : HasFiniteProducts (Over X) :=
    CategoryTheory.Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks
  let Q := FormalCoproduct.mk ι U
  change
    ((FormalCoproduct.mapFunctor (Over.star X)).obj Q).cech ⋙
        sectionRepresenterFormalCoproductFunctor (R.over X) ≅
      (Q.cech ⋙ sectionRepresenterFormalCoproductFunctor R) ⋙
        SheafOfModules.overFunctor R X
  exact
    Functor.isoWhiskerRight (formalCoproductStarCechIso X Q).symm
        (sectionRepresenterFormalCoproductFunctor (R.over X)) ≪≫
      Functor.isoWhiskerLeft Q.cech
        (overSectionRepresenterFormalCoproductNatIso R X) ≪≫
      (Functor.associator Q.cech
        (sectionRepresenterFormalCoproductFunctor R)
        (SheafOfModules.overFunctor R X)).symm

/-- Restriction to an over-site is additive on morphisms. -/
noncomputable def overFunctorAdditive (X : C) :
    (SheafOfModules.overFunctor R X).Additive where
  map_add := by
    intro M N f g
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- An additive functor commutes with the alternating-face-map complex, with
identity comparison maps in every chain degree. -/
noncomputable def alternatingFaceMapComplexWhiskerIso
    {A : Type u} [Category A] [Preadditive A]
    {B : Type u} [Category B] [Preadditive B]
    (F : A ⥤ B) [F.Additive] (X : SimplicialObject A) :
    AlgebraicTopology.AlternatingFaceMapComplex.obj
        (((SimplicialObject.whiskering A B).obj F).obj X) ≅
      (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (AlgebraicTopology.AlternatingFaceMapComplex.obj X) := by
  refine HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) ?_
  rintro i j hij
  subst i
  dsimp only [Iso.refl_hom]
  rw [Category.id_comp, Category.comp_id]
  rw [Functor.mapHomologicalComplex_obj_d]
  change F.map (((AlgebraicTopology.alternatingFaceMapComplex A).obj X).d
      (j + 1) j) =
    ((AlgebraicTopology.alternatingFaceMapComplex B).obj
      (((SimplicialObject.whiskering A B).obj F).obj X)).d (j + 1) j
  rw [AlgebraicTopology.alternatingFaceMapComplex_obj_d,
    AlgebraicTopology.alternatingFaceMapComplex_obj_d]
  dsimp only [AlgebraicTopology.AlternatingFaceMapComplex.objD,
    SimplicialObject.whiskering]
  rw [Functor.map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [Functor.map_zsmul]
  rfl

/-- The corresponding comparison of alternating Cech chain complexes. -/
noncomputable def overSectionRepresenterCechChainIso
    [HasFiniteLimits C] (X : C) {ι : Type u} (U : ι → C) :
    letI : HasFiniteProducts (Over X) :=
      CategoryTheory.Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks
    sectionRepresenterCechChain (R.over X)
        (fun i => (Over.star X).obj (U i)) ≅
      ((SheafOfModules.overFunctor R X).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj (sectionRepresenterCechChain R U) := by
  letI : HasFiniteProducts (Over X) :=
    CategoryTheory.Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks
  letI : (SheafOfModules.overFunctor R X).IsLeftAdjoint :=
    (SheafOfModules.overPushforwardOverAdj (R := R) X).isLeftAdjoint
  letI : PreservesFiniteLimits (SheafOfModules.overFunctor R X) :=
    SheafOfModules.overFunctor_preservesFiniteLimits R X
  letI := overFunctorAdditive R X
  exact
    (AlgebraicTopology.alternatingFaceMapComplex
      (SheafOfModules (R.over X))).mapIso
        (overSectionRepresenterCechNatIso R X U) ≪≫
      alternatingFaceMapComplexWhiskerIso
        (SheafOfModules.overFunctor R X)
        (sectionRepresenterCechSimplicial R U)

set_option backward.isDefEq.respectTransparency false in
@[simp]
lemma overSectionRepresenterCechChainIso_hom_f
    [HasFiniteLimits C] (X : C) {ι : Type u} (U : ι → C) (n : ℕ) :
    letI : HasFiniteProducts (Over X) :=
      CategoryTheory.Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks
    (overSectionRepresenterCechChainIso R X U).hom.f n =
      (overSectionRepresenterCechNatIso R X U).hom.app
        (op (SimplexCategory.mk n)) := by
  letI : HasFiniteProducts (Over X) :=
    CategoryTheory.Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks
  dsimp [overSectionRepresenterCechChainIso,
    alternatingFaceMapComplexWhiskerIso]
  exact Category.comp_id _

end PfaffianDescent
