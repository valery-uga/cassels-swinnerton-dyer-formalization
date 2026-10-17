import PfaffianDescent.RegularPrincipalIdealBaseChange
import PfaffianDescent.FlatAffineActualIdealModule
import PfaffianDescent.AffineGammaPushforward
import PfaffianDescent.RelativeClosedImmersionIdealBaseChange
import PfaffianDescent.AffineClosedImmersionIdealKernel

/-!
# Nonflat base change of a regular-principal affine ideal sheaf

The regular-principal equation and its image being non-zero-divisors
replace flatness of the base-change ring map in the affine sheaf
comparison.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

universe u

/-- The affine `tilde` sheaf of the tensor-extended regular-principal
ideal is the `tilde` sheaf of the actual base-changed quotient kernel. -/
noncomputable def regularPrincipalQuotientKernelTildeIso
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (z : A) (hz : IsRegular z)
    (hgz : IsRegular (g z)) :
    letI : Algebra A B := g.toAlgebra
    let I := Ideal.span ({z} : Set A)
    (tilde.functor (CommRingCat.of B)).obj
      (ModuleCat.of B (B ⊗[A] I)) ≅
    (tilde.functor (CommRingCat.of B)).obj
      (ModuleCat.of B
        (RingHom.ker (Algebra.TensorProduct.includeLeft
          (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom)) := by
  letI : Algebra A B := g.toAlgebra
  let I := Ideal.span ({z} : Set A)
  let e := regularPrincipalQuotientKernelBaseChangeLinearEquiv g z hz hgz
  let m := ModuleCat.ofHom e.toLinearMap
  haveI : IsIso m :=
    (ConcreteCategory.isIso_iff_bijective m).mpr e.bijective
  exact (tilde.functor (CommRingCat.of B)).mapIso (asIso m)

/-- The nonflat affine sheaf comparison respects the canonical
inclusions into the ambient affine structure sheaf. -/
theorem regularPrincipalQuotientKernelTildeIso_hom_subtype
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (z : A) (hz : IsRegular z)
    (hgz : IsRegular (g z)) :
    letI : Algebra A B := g.toAlgebra
    let I := Ideal.span ({z} : Set A)
    let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
      (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
    (regularPrincipalQuotientKernelTildeIso g z hz hgz).hom ≫
      (tilde.functor (CommRingCat.of B)).map (ModuleCat.ofHom K.subtype) =
    (tilde.functor (CommRingCat.of B)).map
      (ModuleCat.ofHom (idealBaseChangeLinearMap g I)) := by
  letI : Algebra A B := g.toAlgebra
  let I := Ideal.span ({z} : Set A)
  let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
    (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
  let F := tilde.functor (CommRingCat.of B)
  let e := regularPrincipalQuotientKernelBaseChangeLinearEquiv g z hz hgz
  let m := ModuleCat.ofHom e.toLinearMap
  have hm : m ≫ ModuleCat.ofHom K.subtype =
      ModuleCat.ofHom (idealBaseChangeLinearMap g I) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul b x =>
        exact (regularPrincipalQuotientKernelBaseChangeLinearEquiv_tmul
          g z hz hgz b x).trans
          (idealBaseChangeLinearMap_tmul g I b x).symm
    | add x y hx hy => simp only [map_add, hx, hy]
  change F.map m ≫ F.map (ModuleCat.ofHom K.subtype) =
    F.map (ModuleCat.ofHom (idealBaseChangeLinearMap g I))
  rw [← F.map_comp, hm]

/-- On an arbitrary coefficient change preserving regularity, the
tensor-extended affine ideal sheaf is the actual closed-immersion
ideal module of the base-changed quotient. -/
noncomputable def regularPrincipalTensorActualIdealModuleIso
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (z : A) (hz : IsRegular z)
    (hgz : IsRegular (g z)) :
    letI : Algebra A B := g.toAlgebra
    let I := Ideal.span ({z} : Set A)
    let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
      (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
    (tilde.functor (CommRingCat.of B)).obj
      (ModuleCat.of B (B ⊗[A] I)) ≅
    IdealSheafDataModule.closedImmersionModule
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))) := by
  letI : Algebra A B := g.toAlgebra
  let I := Ideal.span ({z} : Set A)
  let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
    (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
  exact regularPrincipalQuotientKernelTildeIso g z hz hgz ≪≫
    affineQuotientIdealTildeClosedImmersionModuleIso K

/-- The affine ideal comparison carries the tensor multiplication map to
the actual inclusion into the structure sheaf. -/
theorem regularPrincipalTensorActualIdealModuleIso_hom_toUnit
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (z : A) (hz : IsRegular z)
    (hgz : IsRegular (g z)) :
    letI : Algebra A B := g.toAlgebra
    let I := Ideal.span ({z} : Set A)
    let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
      (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
    let φ := CommRingCat.ofHom (Ideal.Quotient.mk K)
    (regularPrincipalTensorActualIdealModuleIso g z hz hgz).hom ≫
      IdealSheafDataModule.closedImmersionModuleToUnit (Spec.map φ) =
      (tilde.functor (CommRingCat.of B)).map
        (ModuleCat.ofHom (idealBaseChangeLinearMap g I)) ≫
          (affineGlobalSectionsUnitTildeIso (A := B)).hom := by
  letI : Algebra A B := g.toAlgebra
  let I := Ideal.span ({z} : Set A)
  let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
    (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
  let φ := CommRingCat.ofHom (Ideal.Quotient.mk K)
  let F := tilde.functor (CommRingCat.of B)
  let e₁ := regularPrincipalQuotientKernelTildeIso g z hz hgz
  let e₂ := affineQuotientIdealTildeClosedImmersionModuleIso K
  let u := (affineGlobalSectionsUnitTildeIso (A := B)).hom
  let i := IdealSheafDataModule.closedImmersionModuleToUnit (Spec.map φ)
  have h₂ : e₂.hom ≫ i = F.map (ModuleCat.ofHom K.subtype) ≫ u :=
    affineQuotientIdealTildeClosedImmersionModuleIso_hom_toUnit K
  have h₁ : e₁.hom ≫ F.map (ModuleCat.ofHom K.subtype) =
      F.map (ModuleCat.ofHom (idealBaseChangeLinearMap g I)) :=
    regularPrincipalQuotientKernelTildeIso_hom_subtype g z hz hgz
  change (e₁.hom ≫ e₂.hom) ≫ i =
    F.map (ModuleCat.ofHom (idealBaseChangeLinearMap g I)) ≫ u
  calc
    (e₁.hom ≫ e₂.hom) ≫ i = e₁.hom ≫ (e₂.hom ≫ i) :=
      Category.assoc _ _ _
    _ = e₁.hom ≫ (F.map (ModuleCat.ofHom K.subtype) ≫ u) :=
      congrArg (fun h => e₁.hom ≫ h) h₂
    _ = (e₁.hom ≫ F.map (ModuleCat.ofHom K.subtype)) ≫ u :=
      (Category.assoc _ _ _).symm
    _ = _ := congrArg (fun h => h ≫ u) h₁

/-- The ideal module of a regular-principal affine quotient commutes
with an arbitrary base change preserving regularity of its equation. -/
noncomputable def regularPrincipalAffineIdealModulePullbackIso
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (z : A) (hz : IsRegular z)
    (hgz : IsRegular (g z)) :
    letI : Algebra A B := g.toAlgebra
    let I := Ideal.span ({z} : Set A)
    let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
      (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).obj
      (IdealSheafDataModule.closedImmersionModule
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) ≅
    IdealSheafDataModule.closedImmersionModule
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))) := by
  letI : Algebra A B := g.toAlgebra
  let I := Ideal.span ({z} : Set A)
  let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
    (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
  exact (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).mapIso
      (affineQuotientIdealTildeClosedImmersionModuleIso I).symm ≪≫
    affineIdealTildePullbackIso g I ≪≫
      regularPrincipalTensorActualIdealModuleIso g z hz hgz

set_option backward.isDefEq.respectTransparency false in
/-- The actual affine ideal-module base-change isomorphism respects its
inclusion into the ambient structure sheaf, using the explicit affine
ambient comparison. -/
lemma regularPrincipalAffineIdealModulePullbackIso_hom_toUnit
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (z : A) (hz : IsRegular z)
    (hgz : IsRegular (g z)) :
    letI : Algebra A B := g.toAlgebra
    let I := Ideal.span ({z} : Set A)
    let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
      (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
    (regularPrincipalAffineIdealModulePullbackIso g z hz hgz).hom ≫
      IdealSheafDataModule.closedImmersionModuleToUnit
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))) =
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).map
      (IdealSheafDataModule.closedImmersionModuleToUnit
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) ≫
      affineAmbientPullbackComparison g := by
  letI : Algebra A B := g.toAlgebra
  let I := Ideal.span ({z} : Set A)
  let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
    (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
  let P := Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))
  let FA := tilde.functor (CommRingCat.of A)
  let FB := tilde.functor (CommRingCat.of B)
  let eA := affineQuotientIdealTildeClosedImmersionModuleIso I
  let eT := affineIdealTildePullbackIso g I
  let eB := regularPrincipalTensorActualIdealModuleIso g z hz hgz
  let uA := affineGlobalSectionsUnitTildeIso (A := A)
  let uB := affineGlobalSectionsUnitTildeIso (A := B)
  let r := (TensorProduct.AlgebraTensorModule.rid A B B).toModuleIso
  let jA := IdealSheafDataModule.closedImmersionModuleToUnit
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
  let jB := IdealSheafDataModule.closedImmersionModuleToUnit
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)))
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
  have hB : eB.hom ≫ jB =
      FB.map (ModuleCat.ofHom (idealBaseChangeLinearMap g I)) ≫ uB.hom :=
    regularPrincipalTensorActualIdealModuleIso_hom_toUnit g z hz hgz
  have hT : eT.hom ≫
      FB.map ((ModuleCat.extendScalars g).map (ModuleCat.ofHom I.subtype)) =
      P.map (FA.map (ModuleCat.ofHom I.subtype)) ≫
        ((affineTildePullbackNatIso (CommRingCat.ofHom g)).app
          (ModuleCat.of A A)).hom :=
    affineIdealTildePullbackIso_naturality_subtype g I
  have hr : FB.map ((ModuleCat.extendScalars g).map
        (ModuleCat.ofHom I.subtype)) ≫ FB.map r.hom =
      FB.map (ModuleCat.ofHom (idealBaseChangeLinearMap g I)) := by
    exact (FB.map_comp _ _).symm.trans
      (congrArg (fun f => FB.map f)
        (affineExtendScalarsIdealSubtype_rid g I))
  change (P.mapIso eA.symm ≪≫ eT ≪≫ eB).hom ≫ jB =
    P.map jA ≫ (P.map uA.inv ≫
      ((affineTildePullbackNatIso (CommRingCat.ofHom g)).app
        (ModuleCat.of A A)).hom ≫ FB.map r.hom ≫ uB.hom)
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  rw [hB]
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

/-- The affine ideal-module base-change isomorphism commutes with the
canonical pullback map on ambient structure sheaves. -/
lemma regularPrincipalAffineIdealModulePullbackIso_hom_toCanonicalUnit
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (z : A) (hz : IsRegular z)
    (hgz : IsRegular (g z)) :
    letI : Algebra A B := g.toAlgebra
    let I := Ideal.span ({z} : Set A)
    let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
      (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
    (regularPrincipalAffineIdealModulePullbackIso g z hz hgz).hom ≫
      IdealSheafDataModule.closedImmersionModuleToUnit
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))) =
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).map
      (IdealSheafDataModule.closedImmersionModuleToUnit
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) ≫
      BundleSectionZeroLocus.pullbackUnitComparison
        (Spec.map (CommRingCat.ofHom g)) := by
  rw [← affineAmbientPullbackComparison_eq_pullbackUnitComparison]
  exact regularPrincipalAffineIdealModulePullbackIso_hom_toUnit g z hz hgz

/-- Regular-principal affine pullback preserves the monomorphism from the actual
closed-immersion ideal module into the structure sheaf. -/
lemma regularPrincipalAffineIdealModulePullback_mono
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (z : A) (hz : IsRegular z)
    (hgz : IsRegular (g z)) :
    let I := Ideal.span ({z} : Set A)
    Mono ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).map
      (IdealSheafDataModule.closedImmersionModuleToUnit
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))) := by
  letI : Algebra A B := g.toAlgebra
  let I := Ideal.span ({z} : Set A)
  let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
    (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
  have h := regularPrincipalAffineIdealModulePullbackIso_hom_toCanonicalUnit
    g z hz hgz
  haveI : Mono (IdealSheafDataModule.closedImmersionModuleToUnit
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)))) := by
    change Mono (IdealSheafDataModule.idealModuleToUnit _)
    infer_instance
  have hm : Mono
      ((regularPrincipalAffineIdealModulePullbackIso g z hz hgz).hom ≫
        IdealSheafDataModule.closedImmersionModuleToUnit
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)))) := by
    have h₁ : Mono (regularPrincipalAffineIdealModulePullbackIso g z hz hgz).hom := by
      exact mono_of_mono_fac
        (f := (regularPrincipalAffineIdealModulePullbackIso g z hz hgz).inv)
        (regularPrincipalAffineIdealModulePullbackIso g z hz hgz).hom_inv_id
    exact mono_comp' h₁ ‹Mono (IdealSheafDataModule.closedImmersionModuleToUnit _)›
  haveI : Mono
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).map
          (IdealSheafDataModule.closedImmersionModuleToUnit
            (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) ≫
        BundleSectionZeroLocus.pullbackUnitComparison
          (Spec.map (CommRingCat.ofHom g))) := by
    rw [← h]
    exact hm
  exact mono_of_mono_fac
    (f := BundleSectionZeroLocus.pullbackUnitComparison
      (Spec.map (CommRingCat.ofHom g))) rfl

/-- The canonical ideal-sheaf base-change map for a regular-principal
affine quotient is invertible after any ring map preserving regularity
of the defining equation. -/
theorem isIso_regularPrincipalAffineIdealBaseChangeHom
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (z : A) (hz : IsRegular z)
    (hgz : IsRegular (g z)) :
    let I := Ideal.span ({z} : Set A)
    letI : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
      IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of A) I
    IsIso (closedImmersionIdealBaseChangeHom
      (Spec.map (CommRingCat.ofHom g))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) := by
  let I := Ideal.span ({z} : Set A)
  letI : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) := by
    exact IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of A) I
  letI : Mono ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).map
      (IdealSheafDataModule.closedImmersionModuleToUnit
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))) :=
    regularPrincipalAffineIdealModulePullback_mono g z hz hgz
  exact isIso_closedImmersionIdealBaseChangeHom_of_pullback_mono _ _

/-- Two affine maps with the same ring-map kernel define the same ideal
sheaf on their common affine target. -/
theorem specMap_ker_eq_quotient_of_ker_eq
    {A C : Type u} [CommRing A] [CommRing C]
    (q : A →+* C) (I : Ideal A) (hker : RingHom.ker q = I) :
    (Spec.map (CommRingCat.ofHom q)).ker =
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker := by
  apply Scheme.IdealSheafData.ext_of_isAffine
  rw [specMap_ker_ideal_top (CommRingCat.of A) (CommRingCat.of C)
    (CommRingCat.ofHom q)]
  rw [specMap_ker_ideal_top (CommRingCat.of A) (CommRingCat.of (A ⧸ I))
    (CommRingCat.ofHom (Ideal.Quotient.mk I))]
  change (RingHom.ker q).comap _ =
    (RingHom.ker (Ideal.Quotient.mk I)).comap _
  rw [hker]
  simp

/-- Pullback preserves the ideal inclusion of a surjective affine map
whose kernel has a regular principal generator, after an arbitrary
ring change that preserves regularity of that generator. -/
theorem regularPrincipalSurjectiveAffineIdealModulePullback_mono
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (g : A →+* B) (q : A →+* C) (hq : Function.Surjective q)
    (z : A) (hz : IsRegular z) (hgz : IsRegular (g z))
    (hker : RingHom.ker q = Ideal.span ({z} : Set A)) :
    Mono ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).map
      (IdealSheafDataModule.closedImmersionModuleToUnit
        (Spec.map (CommRingCat.ofHom q)))) := by
  let i := Spec.map (CommRingCat.ofHom q)
  letI : IsClosedImmersion i :=
    IsClosedImmersion.spec_of_surjective _ hq
  have heq : i.ker =
      (Spec.map (CommRingCat.ofHom
        (Ideal.Quotient.mk (Ideal.span ({z} : Set A))))).ker :=
    specMap_ker_eq_quotient_of_ker_eq q _ hker
  change Mono ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).map
    (IdealSheafDataModule.idealModuleToUnit i.ker))
  rw [heq]
  exact regularPrincipalAffineIdealModulePullback_mono g z hz hgz

/-- The canonical ideal-sheaf base-change map is an isomorphism for any
surjective affine chart map with regular principal kernel, provided its
generator remains regular after the ring change. -/
theorem isIso_regularPrincipalSurjectiveAffineIdealBaseChangeHom
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (g : A →+* B) (q : A →+* C) (hq : Function.Surjective q)
    (z : A) (hz : IsRegular z) (hgz : IsRegular (g z))
    (hker : RingHom.ker q = Ideal.span ({z} : Set A)) :
    letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom q)) :=
      IsClosedImmersion.spec_of_surjective _ hq
    IsIso (closedImmersionIdealBaseChangeHom
      (Spec.map (CommRingCat.ofHom g))
      (Spec.map (CommRingCat.ofHom q))) := by
  letI : IsClosedImmersion (Spec.map (CommRingCat.ofHom q)) :=
    IsClosedImmersion.spec_of_surjective _ hq
  letI : Mono ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).map
      (IdealSheafDataModule.closedImmersionModuleToUnit
        (Spec.map (CommRingCat.ofHom q)))) :=
    regularPrincipalSurjectiveAffineIdealModulePullback_mono
      g q hq z hz hgz hker
  exact isIso_closedImmersionIdealBaseChangeHom_of_pullback_mono _ _

end PfaffianDescent
