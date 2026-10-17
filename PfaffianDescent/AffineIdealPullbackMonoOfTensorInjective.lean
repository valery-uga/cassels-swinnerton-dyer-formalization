import PfaffianDescent.AffineGammaPushforward
import PfaffianDescent.AffineQCAcyclicity

/-!
# Affine ideal pullback from a tensor injection

Flatness of the coefficient-change map is stronger than necessary for
preserving the inclusion of an affine quotient ideal. The actual condition
is injectivity of its tensor-extended ideal inclusion. This file connects
that algebraic condition to the canonical pullback of the actual ideal
sheaf of the quotient closed immersion.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u

set_option backward.isDefEq.respectTransparency false in
private lemma affineQuotientIdealModulePullback_tensor_comm
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (I : Ideal A) :
    letI : Algebra A B := g.toAlgebra
    ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).mapIso
        (affineQuotientIdealTildeClosedImmersionModuleIso I).symm ≪≫
      affineIdealTildePullbackIso g I).hom ≫
        (tilde.functor (CommRingCat.of B)).map
          (ModuleCat.ofHom (idealBaseChangeLinearMap g I)) ≫
        (affineGlobalSectionsUnitTildeIso (A := B)).hom =
      (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).map
        (IdealSheafDataModule.closedImmersionModuleToUnit
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) ≫
        affineAmbientPullbackComparison g := by
  letI : Algebra A B := g.toAlgebra
  let P := Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))
  let FA := tilde.functor (CommRingCat.of A)
  let FB := tilde.functor (CommRingCat.of B)
  let eA := affineQuotientIdealTildeClosedImmersionModuleIso I
  let eT := affineIdealTildePullbackIso g I
  let e := P.mapIso eA.symm ≪≫ eT
  let uA := affineGlobalSectionsUnitTildeIso (A := A)
  let uB := affineGlobalSectionsUnitTildeIso (A := B)
  let r := (TensorProduct.AlgebraTensorModule.rid A B B).toModuleIso
  let jA := IdealSheafDataModule.closedImmersionModuleToUnit
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
  let m := ModuleCat.ofHom (idealBaseChangeLinearMap g I)
  have hA : eA.inv ≫ FA.map (ModuleCat.ofHom I.subtype) =
      jA ≫ uA.inv := by
    have h := affineQuotientIdealTildeClosedImmersionModuleIso_hom_toUnit I
    change eA.hom ≫ jA = FA.map (ModuleCat.ofHom I.subtype) ≫ uA.hom at h
    calc
      eA.inv ≫ FA.map (ModuleCat.ofHom I.subtype) =
          eA.inv ≫ (FA.map (ModuleCat.ofHom I.subtype) ≫ uA.hom) ≫ uA.inv := by
            simp [Category.assoc]
      _ = eA.inv ≫ (eA.hom ≫ jA) ≫ uA.inv := by rw [h]
      _ = jA ≫ uA.inv := by simp [Category.assoc]
  have hT : eT.hom ≫
      FB.map ((ModuleCat.extendScalars g).map (ModuleCat.ofHom I.subtype)) =
      P.map (FA.map (ModuleCat.ofHom I.subtype)) ≫
        ((affineTildePullbackNatIso (CommRingCat.ofHom g)).app
          (ModuleCat.of A A)).hom :=
    affineIdealTildePullbackIso_naturality_subtype g I
  have hr : FB.map ((ModuleCat.extendScalars g).map
        (ModuleCat.ofHom I.subtype)) ≫ FB.map r.hom = FB.map m := by
    exact (FB.map_comp _ _).symm.trans
      (congrArg (fun f => FB.map f)
        (affineExtendScalarsIdealSubtype_rid g I))
  have hcomm : e.hom ≫ FB.map m ≫ uB.hom =
      P.map jA ≫ affineAmbientPullbackComparison g := by
    change (P.mapIso eA.symm ≪≫ eT).hom ≫ FB.map m ≫ uB.hom =
      P.map jA ≫ (P.map uA.inv ≫
        ((affineTildePullbackNatIso (CommRingCat.ofHom g)).app
          (ModuleCat.of A A)).hom ≫ FB.map r.hom ≫ uB.hom)
    simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
    rw [← hr]
    simp only [← Category.assoc]
    rw [Category.assoc (P.map (Iso.symm eA).hom) eT.hom
      (FB.map ((ModuleCat.extendScalars g).map (ModuleCat.ofHom I.subtype)))]
    rw [hT]
    rw [← Category.assoc (P.map (Iso.symm eA).hom)
      (P.map (FA.map (ModuleCat.ofHom I.subtype)))
      ((affineTildePullbackNatIso (CommRingCat.ofHom g)).app
        (ModuleCat.of A A)).hom]
    rw [← P.map_comp (Iso.symm eA).hom (FA.map (ModuleCat.ofHom I.subtype))]
    change (Iso.symm eA).hom ≫ FA.map (ModuleCat.ofHom I.subtype) =
      jA ≫ uA.inv at hA
    rw [hA]
    simp only [P.map_comp, Category.assoc]
  exact hcomm

private lemma ideal_baseChange_module_mono
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (I : Ideal A)
    (hinj : letI : Algebra A B := g.toAlgebra
      Function.Injective (idealBaseChangeLinearMap g I)) :
    letI : Algebra A B := g.toAlgebra
    Mono (ModuleCat.ofHom (idealBaseChangeLinearMap g I)) := by
  letI : Algebra A B := g.toAlgebra
  exact (ModuleCat.mono_iff_injective _).mpr hinj

private lemma tilde_ideal_baseChange_mono
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (I : Ideal A)
    (hinj : letI : Algebra A B := g.toAlgebra
      Function.Injective (idealBaseChangeLinearMap g I)) :
    letI : Algebra A B := g.toAlgebra
    Mono ((tilde.functor (CommRingCat.of B)).map
      (ModuleCat.ofHom (idealBaseChangeLinearMap g I))) := by
  letI : Algebra A B := g.toAlgebra
  let m := ModuleCat.ofHom (idealBaseChangeLinearMap g I)
  haveI : Mono m := ideal_baseChange_module_mono g I hinj
  exact tilde_map_mono (R := CommRingCat.of B) m

/-- Injectivity of the tensor-extended affine ideal inclusion implies that
the canonical pullback of the actual ideal sheaf inclusion is monic. -/
theorem affineQuotientIdealModulePullback_mono_of_tensor_injective
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (I : Ideal A)
    (hinj : letI : Algebra A B := g.toAlgebra
      Function.Injective (idealBaseChangeLinearMap g I)) :
    Mono ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).map
      (IdealSheafDataModule.closedImmersionModuleToUnit
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))) := by
  letI : Algebra A B := g.toAlgebra
  let P := Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))
  let FB := tilde.functor (CommRingCat.of B)
  let e := P.mapIso (affineQuotientIdealTildeClosedImmersionModuleIso I).symm ≪≫
    affineIdealTildePullbackIso g I
  let uB := affineGlobalSectionsUnitTildeIso (A := B)
  let jA := IdealSheafDataModule.closedImmersionModuleToUnit
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
  let m := ModuleCat.ofHom (idealBaseChangeLinearMap g I)
  have hcomm : e.hom ≫ FB.map m ≫ uB.hom =
      P.map jA ≫ affineAmbientPullbackComparison g :=
    affineQuotientIdealModulePullback_tensor_comm g I
  haveI : Mono (FB.map m) := tilde_ideal_baseChange_mono g I hinj
  have hm : Mono (e.hom ≫ FB.map m ≫ uB.hom) := by
    exact mono_comp' e.isIso_hom.mono_of_iso
      (mono_comp' (by infer_instance) uB.isIso_hom.mono_of_iso)
  have h₁ : Mono (P.map jA ≫ affineAmbientPullbackComparison g) :=
    hcomm ▸ hm
  exact mono_of_mono_fac (f := affineAmbientPullbackComparison g)
    (g := P.map jA) rfl

end PfaffianDescent
