import PfaffianDescent.AffineBaseChangeQuotientPresentation
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! Global sections of an affine pushforward are restriction of scalars. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

/-- The global sections of an affine pushforward agree with restriction
of scalars along the underlying ring map. -/
noncomputable def affineGammaPushforwardLinearEquiv
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : (Spec S).Modules) :
    (moduleSpecΓFunctor (R := R)).obj
      ((Scheme.Modules.pushforward (Spec.map φ)).obj M) ≃ₗ[R]
    (ModuleCat.restrictScalars φ.hom).obj
      ((moduleSpecΓFunctor (R := S)).obj M) := by
  refine
    { toFun := id
      invFun := id
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl
      map_add' := by intro x y; rfl
      map_smul' := ?_ }
  intro a x
  let y : M.presheaf.obj (.op ⊤) := x
  change ((Spec.map φ).appTop.hom ((Scheme.ΓSpecIso R).inv.hom a)) • y =
    ((Scheme.ΓSpecIso S).inv.hom (φ.hom a)) • y
  have h := congrArg (fun f : R ⟶ CommRingCat.of Γ(Spec S, ⊤) => f.hom a)
    (Scheme.ΓSpecIso_inv_naturality φ)
  exact congrArg (fun t : Γ(Spec S, ⊤) => t • y) h.symm

/-- The affine global-section/pushforward comparison is natural in the
module sheaf. -/
noncomputable def affineGammaPushforwardNatIso
    {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R) ≅
      moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom := by
  refine NatIso.ofComponents
    (fun M => (affineGammaPushforwardLinearEquiv φ M).toModuleIso) ?_
  intro M N f
  apply ModuleCat.hom_ext
  rfl

/-- On global sections, the canonical map from the structure sheaf to
its affine pushforward sends `a : A` to `g a : B`. -/
theorem affineCanonicalUnitGlobalSections
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (a : A) :
    let f := Spec.map (CommRingCat.ofHom g)
    let q := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
    (affineGlobalSectionsUnitLinearEquiv (A := B))
      ((affineGammaPushforwardLinearEquiv (CommRingCat.ofHom g)
        (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf))
        ((moduleSpecΓFunctor (R := CommRingCat.of A)).map q
          ((affineGlobalSectionsUnitLinearEquiv (A := A)).symm a))) = g a := by
  let f := Spec.map (CommRingCat.ofHom g)
  let q := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  change (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom
      (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a)) = g a
  have h := congrArg
    (fun ψ : CommRingCat.of A ⟶ CommRingCat.of Γ(Spec (CommRingCat.of B), ⊤) =>
      ψ.hom a)
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  change (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (g a) =
    f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom a) at h
  rw [h.symm]
  simp

/-- The scalar-extension adjunction unit, followed by contraction of
`B ⊗[A] A`, is the original ring map `A → B`. -/
theorem affineScalarExtensionUnit_rid
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (a : A) :
    letI : Algebra A B := g.toAlgebra
    (TensorProduct.AlgebraTensorModule.rid A B B)
      (((ModuleCat.extendRestrictScalarsAdj g).unit.app
        (ModuleCat.of A A)) a) = g a := by
  letI : Algebra A B := g.toAlgebra
  change (TensorProduct.AlgebraTensorModule.rid A B B)
      ((1 : B) ⊗ₜ[A] a) = g a
  simp only [TensorProduct.AlgebraTensorModule.rid_tmul, one_smul,
    Algebra.smul_def, mul_one]
  rfl

/-- The canonical affine structure-sheaf map and the scalar-extension
unit give the same `A`-linear map after identifying the source and
target global sections with `A` and `B`. -/
theorem affineCanonicalUnit_eq_scalarExtensionUnit_onGamma
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) :
    letI : Algebra A B := g.toAlgebra
    let f := Spec.map (CommRingCat.ofHom g)
    let q := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
    (affineGlobalSectionsUnitLinearEquiv (A := A)).symm.toModuleIso.hom ≫
      (moduleSpecΓFunctor (R := CommRingCat.of A)).map q ≫
      ((affineGammaPushforwardNatIso (CommRingCat.ofHom g)).app
        (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf)).hom ≫
      (ModuleCat.restrictScalars g).map
        (affineGlobalSectionsUnitLinearEquiv (A := B)).toModuleIso.hom =
    ((ModuleCat.extendRestrictScalarsAdj g).unit.app (ModuleCat.of A A)) ≫
      (ModuleCat.restrictScalars g).map
        (TensorProduct.AlgebraTensorModule.rid A B B).toModuleIso.hom := by
  letI : Algebra A B := g.toAlgebra
  let f := Spec.map (CommRingCat.ofHom g)
  let q := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change (affineGlobalSectionsUnitLinearEquiv (A := B))
      ((affineGammaPushforwardLinearEquiv (CommRingCat.ofHom g)
        (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf))
        ((moduleSpecΓFunctor (R := CommRingCat.of A)).map q
          ((affineGlobalSectionsUnitLinearEquiv (A := A)).symm a))) =
    (TensorProduct.AlgebraTensorModule.rid A B B)
      (((ModuleCat.extendRestrictScalarsAdj g).unit.app
        (ModuleCat.of A A)) a)
  exact (affineCanonicalUnitGlobalSections g a).trans
    (affineScalarExtensionUnit_rid g a).symm

/-- Under the scheme-module pullback/pushforward adjunction, the
canonical pullback map on structure sheaves corresponds to the
canonical map from the structure sheaf to its pushforward. -/
theorem affineCanonicalPullbackUnit_adjunct
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) :
    let f := Spec.map (CommRingCat.ofHom g)
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      (BundleSectionZeroLocus.pullbackUnitComparison f) =
        SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
  let f := Spec.map (CommRingCat.ofHom g)
  letI : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  change (SheafOfModules.pullbackPushforwardAdjunction
    f.toRingCatSheafHom).homEquiv _ _
      (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) = _
  exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    f.toRingCatSheafHom

/-- The same adjunction identity with its source written as `tilde A`. -/
theorem affineCanonicalPullbackUnit_adjunct_tilde
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) :
    let f := Spec.map (CommRingCat.ofHom g)
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv
      ((tilde.functor (CommRingCat.of A)).obj (ModuleCat.of A A))
      (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf)
      (BundleSectionZeroLocus.pullbackUnitComparison f) =
        SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
  exact affineCanonicalPullbackUnit_adjunct g

set_option backward.isDefEq.respectTransparency false in
/-- Passing the canonical affine structure-sheaf pushforward map
through the `tilde` adjunction gives the map on global sections
preceded by the inverse `A ≃ Γ(𝒪_{Spec A})`. -/
theorem affineCanonicalUnit_tildeAdjunct
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) :
    let f := Spec.map (CommRingCat.ofHom g)
    let q := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
    (tilde.adjunction (R := CommRingCat.of A)).homEquiv _ _ q =
      (affineGlobalSectionsUnitLinearEquiv (A := A)).symm.toModuleIso.hom ≫
        (moduleSpecΓFunctor (R := CommRingCat.of A)).map q := by
  let f := Spec.map (CommRingCat.ofHom g)
  let q := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  dsimp only
  rw [Adjunction.homEquiv_unit]
  rw [affineGlobalSectionsUnitLinearEquiv_symm_eq_tildeAdjunctionUnit]
  rfl

private theorem compAdjunction_homEquiv_apply
    {C D E : Type*} [Category C] [Category D] [Category E]
    {F : C ⥤ D} {G : D ⥤ C} {H : D ⥤ E} {J : E ⥤ D}
    (a : F ⊣ G) (b : H ⊣ J) (X : C) (Y : E)
    (f : (F ⋙ H).obj X ⟶ Y) :
    (a.comp b).homEquiv X Y f =
      a.homEquiv X (J.obj Y) (b.homEquiv (F.obj X) Y f) := by
  simp only [Adjunction.comp_homEquiv, Equiv.trans_apply]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The composite `tilde`/pullback adjunction sends the canonical
pullback-unit map to the canonical map on affine global sections. -/
theorem affineCanonicalUnit_compositeAdjunct
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) :
    let f := Spec.map (CommRingCat.ofHom g)
    let q := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
    let adj₁ := (tilde.adjunction (R := CommRingCat.of A)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f)
    adj₁.homEquiv _ _ (BundleSectionZeroLocus.pullbackUnitComparison f) =
      (affineGlobalSectionsUnitLinearEquiv (A := A)).symm.toModuleIso.hom ≫
        (moduleSpecΓFunctor (R := CommRingCat.of A)).map q := by
  let f := Spec.map (CommRingCat.ofHom g)
  let q := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  dsimp only
  rw [compAdjunction_homEquiv_apply]
  rw [affineCanonicalPullbackUnit_adjunct_tilde g]
  exact affineCanonicalUnit_tildeAdjunct g

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- After identifying global sections of affine pushforward with
restriction of scalars, the canonical pullback-unit map has the
expected `A → B` adjunct. -/
theorem affineCanonicalUnit_affineAdjunct
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) :
    let φ := CommRingCat.ofHom g
    let f := Spec.map φ
    let O := SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf
    let q := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
    let adj₁ := (tilde.adjunction (R := CommRingCat.of A)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f)
    (adj₁.ofNatIsoRight (affineGammaPushforwardNatIso φ)).homEquiv _ _
      (BundleSectionZeroLocus.pullbackUnitComparison f) =
      (affineGlobalSectionsUnitLinearEquiv (A := A)).symm.toModuleIso.hom ≫
        (moduleSpecΓFunctor (R := CommRingCat.of A)).map q ≫
        ((affineGammaPushforwardNatIso φ).app O).hom := by
  dsimp only
  rw [Adjunction.homEquiv_ofNatIsoRight_apply]
  rw [affineCanonicalUnit_compositeAdjunct g]
  rfl

/-- Pulling back a `tilde` module along a map of affine spectra agrees
naturally with extending scalars before applying `tilde`. -/
noncomputable def affineTildePullbackNatIso
    {R S : CommRingCat.{u}} (φ : R ⟶ S) :
    tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map φ) ≅
      ModuleCat.extendScalars φ.hom ⋙ tilde.functor S := by
  let adj₁ :
      tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map φ) ⊣
        Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R) :=
    (tilde.adjunction (R := R)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))
  let adj₂ :
      ModuleCat.extendScalars φ.hom ⋙ tilde.functor S ⊣
        moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom :=
    (ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R := S))
  exact Adjunction.leftAdjointUniq
    (adj₁.ofNatIsoRight (affineGammaPushforwardNatIso φ)) adj₂

/-- The affine pullback-of-`tilde` isomorphism is characterized by
the unit of the scalar-extension/`tilde` composite adjunction. -/
theorem affineTildePullbackNatIso_homEquiv
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : ModuleCat R) :
    let adj₁ :
      tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map φ) ⊣
        Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R) :=
      (tilde.adjunction (R := R)).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))
    let adj₂ :
      ModuleCat.extendScalars φ.hom ⋙ tilde.functor S ⊣
        moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom :=
      (ModuleCat.extendRestrictScalarsAdj φ.hom).comp
        (tilde.adjunction (R := S))
    (adj₁.ofNatIsoRight (affineGammaPushforwardNatIso φ)).homEquiv _ _
      ((affineTildePullbackNatIso φ).hom.app M) = adj₂.unit.app M := by
  dsimp only
  exact Adjunction.homEquiv_leftAdjointUniq_hom_app _ _ M

/-- The adjunct of the affine `tilde` pullback isomorphism followed by
any target sheaf map is the scalar-extension composite unit followed
by that map on affine global sections. -/
theorem affineTildePullbackNatIso_homEquiv_comp
    {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : ModuleCat R)
    {N : (Spec S).Modules}
    (h : (tilde.functor S).obj ((ModuleCat.extendScalars φ.hom).obj M) ⟶ N) :
    let adj₁ :
      tilde.functor R ⋙ Scheme.Modules.pullback (Spec.map φ) ⊣
        Scheme.Modules.pushforward (Spec.map φ) ⋙ moduleSpecΓFunctor (R := R) :=
      (tilde.adjunction (R := R)).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))
    let adj₂ :
      ModuleCat.extendScalars φ.hom ⋙ tilde.functor S ⊣
        moduleSpecΓFunctor (R := S) ⋙ ModuleCat.restrictScalars φ.hom :=
      (ModuleCat.extendRestrictScalarsAdj φ.hom).comp
        (tilde.adjunction (R := S))
    (adj₁.ofNatIsoRight (affineGammaPushforwardNatIso φ)).homEquiv _ _
      (((affineTildePullbackNatIso φ).app M).hom ≫ h) =
        adj₂.unit.app M ≫
          (moduleSpecΓFunctor (R := S) ⋙
            ModuleCat.restrictScalars φ.hom).map h := by
  let adj₁ := (tilde.adjunction (R := R)).comp
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))
  let adj₂ := (ModuleCat.extendRestrictScalarsAdj φ.hom).comp
    (tilde.adjunction (R := S))
  dsimp only
  rw [Adjunction.homEquiv_naturality_right]
  have hc := affineTildePullbackNatIso_homEquiv φ M
  change ((adj₁.ofNatIsoRight (affineGammaPushforwardNatIso φ)).homEquiv _ _)
      (((affineTildePullbackNatIso φ).app M).hom) = adj₂.unit.app M at hc
  rw [hc]

/-- Tensor contraction on `tilde(B ⊗[A] A)`, followed by the affine
identification with the structure sheaf of `Spec B`. -/
noncomputable def affineAmbientTargetMap
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) :
    letI : Algebra A B := g.toAlgebra
    (tilde.functor (CommRingCat.of B)).obj
      (ModuleCat.of B (B ⊗[A] A)) ⟶
        SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf := by
  letI : Algebra A B := g.toAlgebra
  exact (tilde.functor (CommRingCat.of B)).map
      (TensorProduct.AlgebraTensorModule.rid A B B).toModuleIso.hom ≫
    (affineGlobalSectionsUnitTildeIso (A := B)).hom

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The `tilde` adjunct of tensor contraction followed by the affine
structure-sheaf identification is tensor contraction followed by the
inverse global-sections identification. -/
theorem affineTildeAmbientTarget_tildeAdjunct
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) :
    letI : Algebra A B := g.toAlgebra
    let r := (TensorProduct.AlgebraTensorModule.rid A B B).toModuleIso
    let h := (tilde.functor (CommRingCat.of B)).map r.hom ≫
      (affineGlobalSectionsUnitTildeIso (A := B)).hom
    (tilde.adjunction (R := CommRingCat.of B)).homEquiv _ _ h =
      r.hom ≫
        (affineGlobalSectionsUnitLinearEquiv (A := B)).symm.toModuleIso.hom := by
  letI : Algebra A B := g.toAlgebra
  let r := (TensorProduct.AlgebraTensorModule.rid A B B).toModuleIso
  let h := (tilde.functor (CommRingCat.of B)).map r.hom ≫
    (affineGlobalSectionsUnitTildeIso (A := B)).hom
  dsimp only
  rw [Adjunction.homEquiv_naturality_left]
  rw [Adjunction.homEquiv_unit]
  rw [affineGlobalSectionsUnitTildeIso_eq_tildeSelf]
  simp only [tildeSelf, Iso.refl_hom, Functor.map_id, Category.comp_id]
  rw [affineGlobalSectionsUnitLinearEquiv_symm_eq_tildeAdjunctionUnit]
  rfl

/-- The same adjunct formula with the target map bundled as a named
definition, keeping later composite-adjunction expressions small. -/
theorem affineAmbientTargetMap_tildeAdjunct
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) :
    letI : Algebra A B := g.toAlgebra
    (tilde.adjunction (R := CommRingCat.of B)).homEquiv _ _
      (affineAmbientTargetMap g) =
        (TensorProduct.AlgebraTensorModule.rid A B B).toModuleIso.hom ≫
          (affineGlobalSectionsUnitLinearEquiv (A := B)).symm.toModuleIso.hom := by
  exact affineTildeAmbientTarget_tildeAdjunct g

/-- The ambient target adjunct with source in the precise form
required by scalar extension. -/
theorem affineAmbientTargetMap_tildeAdjunct_extend
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) :
    letI : Algebra A B := g.toAlgebra
    (tilde.adjunction (R := CommRingCat.of B)).homEquiv
      ((ModuleCat.extendScalars g).obj (ModuleCat.of A A))
      (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf)
      (affineAmbientTargetMap g) =
        (TensorProduct.AlgebraTensorModule.rid A B B).toModuleIso.hom ≫
          (affineGlobalSectionsUnitLinearEquiv (A := B)).symm.toModuleIso.hom := by
  exact affineAmbientTargetMap_tildeAdjunct g

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The scalar/`tilde` composite adjunct of the named ambient target
map is the scalar-extension adjunct of tensor contraction followed
by the inverse global-sections identification. -/
theorem affineAmbientTargetMap_compositeAdjunct
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) :
    letI : Algebra A B := g.toAlgebra
    (((ModuleCat.extendRestrictScalarsAdj g).comp
      (tilde.adjunction (R := CommRingCat.of B))).homEquiv
        (ModuleCat.of A A)
        (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf))
        (affineAmbientTargetMap g) =
      (ModuleCat.extendRestrictScalarsAdj g).homEquiv
        (ModuleCat.of A A)
        ((moduleSpecΓFunctor (R := CommRingCat.of B)).obj
          (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf))
        ((TensorProduct.AlgebraTensorModule.rid A B B).toModuleIso.hom ≫
          (affineGlobalSectionsUnitLinearEquiv (A := B)).symm.toModuleIso.hom) := by
  letI : Algebra A B := g.toAlgebra
  rw [compAdjunction_homEquiv_apply]
  rw [affineAmbientTargetMap_tildeAdjunct_extend g]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Composing the scalar-extension adjunct with the forward affine
global-sections equivalence cancels its inverse and leaves tensor
contraction. -/
theorem affineScalarAdjunct_cancelUnitGamma
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) :
    letI : Algebra A B := g.toAlgebra
    let r := (TensorProduct.AlgebraTensorModule.rid A B B).toModuleIso
    let e := (affineGlobalSectionsUnitLinearEquiv (A := B)).toModuleIso
    (ModuleCat.extendRestrictScalarsAdj g).homEquiv
      (ModuleCat.of A A)
      ((moduleSpecΓFunctor (R := CommRingCat.of B)).obj
        (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf))
      (r.hom ≫ e.inv) ≫
        (ModuleCat.restrictScalars g).map e.hom =
      (ModuleCat.extendRestrictScalarsAdj g).unit.app (ModuleCat.of A A) ≫
        (ModuleCat.restrictScalars g).map r.hom := by
  letI : Algebra A B := g.toAlgebra
  let r := (TensorProduct.AlgebraTensorModule.rid A B B).toModuleIso
  let e := (affineGlobalSectionsUnitLinearEquiv (A := B)).toModuleIso
  dsimp only
  rw [Adjunction.homEquiv_unit]
  simp only [Functor.map_comp, Category.assoc]
  change (ModuleCat.extendRestrictScalarsAdj g).unit.app (ModuleCat.of A A) ≫
      (ModuleCat.restrictScalars g).map r.hom ≫
        (ModuleCat.restrictScalars g).map e.inv ≫
          (ModuleCat.restrictScalars g).map e.hom =
    (ModuleCat.extendRestrictScalarsAdj g).unit.app (ModuleCat.of A A) ≫
      (ModuleCat.restrictScalars g).map r.hom
  rw [← (ModuleCat.restrictScalars g).map_comp e.inv e.hom]
  simp

/-- The ambient target map has exactly the scalar-extension unit as
its composite adjunct once the target global sections are identified
with `B`. -/
theorem affineAmbientTargetMap_compositeAdjunct_cancelGamma
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) :
    letI : Algebra A B := g.toAlgebra
    (((ModuleCat.extendRestrictScalarsAdj g).comp
      (tilde.adjunction (R := CommRingCat.of B))).homEquiv
        (ModuleCat.of A A)
        (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf))
        (affineAmbientTargetMap g) ≫
      (ModuleCat.restrictScalars g).map
        (affineGlobalSectionsUnitLinearEquiv (A := B)).toModuleIso.hom =
    (ModuleCat.extendRestrictScalarsAdj g).unit.app (ModuleCat.of A A) ≫
      (ModuleCat.restrictScalars g).map
        (TensorProduct.AlgebraTensorModule.rid A B B).toModuleIso.hom := by
  letI : Algebra A B := g.toAlgebra
  rw [affineAmbientTargetMap_compositeAdjunct g]
  exact affineScalarAdjunct_cancelUnitGamma g

/-- The affine `tilde` pullback comparison at the free rank-one
module, followed by the ambient target map. -/
noncomputable def affineTildeAmbientComparison
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).obj
      ((tilde.functor (CommRingCat.of A)).obj (ModuleCat.of A A)) ⟶
        SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf := by
  exact ((affineTildePullbackNatIso (CommRingCat.ofHom g)).app
      (ModuleCat.of A A)).hom ≫ affineAmbientTargetMap g

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The adjunct of the named affine ambient comparison is the
scalar/`tilde` unit followed by the ambient target map on global
sections. -/
theorem affineTildeAmbientComparison_adjunct
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) :
    let φ := CommRingCat.ofHom g
    let f := Spec.map φ
    let O := SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf
    let adj₁ := (tilde.adjunction (R := CommRingCat.of A)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f)
    let adj₂ := (ModuleCat.extendRestrictScalarsAdj g).comp
      (tilde.adjunction (R := CommRingCat.of B))
    (adj₁.ofNatIsoRight (affineGammaPushforwardNatIso φ)).homEquiv
      (ModuleCat.of A A) O (affineTildeAmbientComparison g) =
    adj₂.unit.app (ModuleCat.of A A) ≫
      (moduleSpecΓFunctor (R := CommRingCat.of B) ⋙
        ModuleCat.restrictScalars g).map (affineAmbientTargetMap g) := by
  dsimp only
  unfold affineTildeAmbientComparison
  exact affineTildePullbackNatIso_homEquiv_comp
    (CommRingCat.ofHom g) (ModuleCat.of A A) (affineAmbientTargetMap g)

/-- The canonical pullback-unit map, expressed as an `A`-linear
adjunct after identifying affine pushforward global sections. -/
noncomputable def affineCanonicalUnitAdjunct
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) :
    ModuleCat.of A A ⟶
      (ModuleCat.restrictScalars g).obj
        ((moduleSpecΓFunctor (R := CommRingCat.of B)).obj
          (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf)) := by
  let φ := CommRingCat.ofHom g
  let f := Spec.map φ
  let O := SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf
  let q := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  exact (affineGlobalSectionsUnitLinearEquiv (A := A)).symm.toModuleIso.hom ≫
    (moduleSpecΓFunctor (R := CommRingCat.of A)).map q ≫
      ((affineGammaPushforwardNatIso φ).app O).hom

/-- The explicit affine ambient comparison, expressed in the same
`A`-linear adjunct Hom-set. -/
noncomputable def affineExplicitUnitAdjunct
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) :
    ModuleCat.of A A ⟶
      (ModuleCat.restrictScalars g).obj
        ((moduleSpecΓFunctor (R := CommRingCat.of B)).obj
          (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf)) := by
  let φ := CommRingCat.ofHom g
  let f := Spec.map φ
  let O := SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf
  let adj₁ := (tilde.adjunction (R := CommRingCat.of A)).comp
    (Scheme.Modules.pullbackPushforwardAdjunction f)
  exact (adj₁.ofNatIsoRight (affineGammaPushforwardNatIso φ)).homEquiv _ _
    (affineTildeAmbientComparison g)

/-- Convert the target affine global sections from `Γ(𝒪_{Spec B})`
to the ring `B`, viewed with restricted `A`-scalars. -/
noncomputable def affineTargetGammaToB
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) :
    (ModuleCat.restrictScalars g).obj
      ((moduleSpecΓFunctor (R := CommRingCat.of B)).obj
        (SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf)) ⟶
    (ModuleCat.restrictScalars g).obj (ModuleCat.of B B) :=
  (ModuleCat.restrictScalars g).map
    (affineGlobalSectionsUnitLinearEquiv (A := B)).toModuleIso.hom

/-- The scalar-extension unit at `A` followed by tensor contraction
`B ⊗[A] A ≃ B`. -/
noncomputable def affineScalarUnitContract
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) :
    ModuleCat.of A A ⟶
      (ModuleCat.restrictScalars g).obj (ModuleCat.of B B) := by
  letI : Algebra A B := g.toAlgebra
  exact (ModuleCat.extendRestrictScalarsAdj g).unit.app (ModuleCat.of A A) ≫
    (ModuleCat.restrictScalars g).map
      (TensorProduct.AlgebraTensorModule.rid A B B).toModuleIso.hom

/-- The canonical unit adjunct becomes the scalar-extension unit
after converting target affine global sections to `B`. -/
theorem affineCanonicalUnitAdjunct_comp_targetGammaToB
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) :
    affineCanonicalUnitAdjunct g ≫ affineTargetGammaToB g =
      affineScalarUnitContract g := by
  letI : Algebra A B := g.toAlgebra
  exact affineCanonicalUnit_eq_scalarExtensionUnit_onGamma g

/-- The explicit unit adjunct becomes the same scalar-extension unit
after converting target affine global sections to `B`. -/
theorem affineExplicitUnitAdjunct_comp_targetGammaToB
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) :
    affineExplicitUnitAdjunct g ≫ affineTargetGammaToB g =
      affineScalarUnitContract g := by
  letI : Algebra A B := g.toAlgebra
  rw [affineExplicitUnitAdjunct]
  rw [affineTildeAmbientComparison_adjunct g]
  exact affineAmbientTargetMap_compositeAdjunct_cancelGamma g

/-- The canonical and explicit affine ambient comparisons have the
same adjunct: both become the same scalar-extension unit under the
invertible target global-sections identification. -/
theorem affineCanonicalUnitAdjunct_eq_explicit
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) :
    affineCanonicalUnitAdjunct g = affineExplicitUnitAdjunct g := by
  let e := (affineGlobalSectionsUnitLinearEquiv (A := B)).toModuleIso
  have h : IsIso (affineTargetGammaToB g) :=
    ((ModuleCat.restrictScalars g).mapIso e).isIso_hom
  letI := h
  apply (cancel_mono (affineTargetGammaToB g)).1
  exact (affineCanonicalUnitAdjunct_comp_targetGammaToB g).trans
    (affineExplicitUnitAdjunct_comp_targetGammaToB g).symm

/-- On affine spectra, the `tilde` pullback comparison at the free
rank-one module, followed by tensor contraction, is Mathlib's
canonical pullback map on structure sheaves. -/
theorem affineTildeAmbientComparison_eq_pullbackUnitComparison
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) :
    affineTildeAmbientComparison g =
      BundleSectionZeroLocus.pullbackUnitComparison
        (Spec.map (CommRingCat.ofHom g)) := by
  let φ := CommRingCat.ofHom g
  let f := Spec.map φ
  let O := SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf
  let adj₁ := (tilde.adjunction (R := CommRingCat.of A)).comp
    (Scheme.Modules.pullbackPushforwardAdjunction f)
  let adj := adj₁.ofNatIsoRight (affineGammaPushforwardNatIso φ)
  apply (adj.homEquiv (ModuleCat.of A A) O).injective
  rw [affineCanonicalUnit_affineAdjunct g]
  change affineExplicitUnitAdjunct g = affineCanonicalUnitAdjunct g
  exact (affineCanonicalUnitAdjunct_eq_explicit g).symm

/-- For an affine ring map, the pullback of the `tilde` sheaf of an ideal
is the `tilde` sheaf of its scalar extension. -/
noncomputable def affineIdealTildePullbackIso
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (I : Ideal A) :
    letI : Algebra A B := g.toAlgebra
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).obj
      ((tilde.functor (CommRingCat.of A)).obj (ModuleCat.of A I)) ≅
        (tilde.functor (CommRingCat.of B)).obj
          (ModuleCat.of B (B ⊗[A] I)) := by
  letI : Algebra A B := g.toAlgebra
  exact (affineTildePullbackNatIso (CommRingCat.ofHom g)).app (ModuleCat.of A I)

/-- The affine pullback-of-`tilde` comparison is natural with respect to
the inclusion of an ideal into the ambient ring. -/
theorem affineIdealTildePullbackIso_naturality_subtype
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (I : Ideal A) :
    (affineIdealTildePullbackIso g I).hom ≫
        (tilde.functor (CommRingCat.of B)).map
          ((ModuleCat.extendScalars (CommRingCat.ofHom g).hom).map
            (ModuleCat.ofHom I.subtype)) =
      (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).map
          ((tilde.functor (CommRingCat.of A)).map
            (ModuleCat.ofHom I.subtype)) ≫
        ((affineTildePullbackNatIso (CommRingCat.ofHom g)).app
          (ModuleCat.of A A)).hom := by
  exact ((affineTildePullbackNatIso (CommRingCat.ofHom g)).hom.naturality
    (ModuleCat.ofHom I.subtype)).symm

/-- Extending the ideal inclusion and contracting the ambient tensor
product sends `b ⊗ x` to `b * g x`. -/
theorem affineExtendScalarsIdealSubtype_rid
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (I : Ideal A) :
    letI : Algebra A B := g.toAlgebra
    (ModuleCat.extendScalars g).map (ModuleCat.ofHom I.subtype) ≫
      (TensorProduct.AlgebraTensorModule.rid A B B).toModuleIso.hom =
        ModuleCat.ofHom (idealBaseChangeLinearMap g I) := by
  letI : Algebra A B := g.toAlgebra
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  induction x using TensorProduct.induction_on with
  | zero =>
      exact (ModuleCat.Hom.hom
        ((ModuleCat.extendScalars g).map (ModuleCat.ofHom I.subtype) ≫
          (TensorProduct.AlgebraTensorModule.rid A B B).toModuleIso.hom)).map_zero.trans
        ((ModuleCat.Hom.hom (ModuleCat.ofHom (idealBaseChangeLinearMap g I))).map_zero).symm
  | tmul b y =>
      change (TensorProduct.AlgebraTensorModule.rid A B B)
          ((ModuleCat.extendScalars g).map (ModuleCat.ofHom I.subtype) (b ⊗ₜ[A] y)) =
        idealBaseChangeLinearMap g I (b ⊗ₜ[A] y)
      rfl
  | add x y hx hy =>
      calc
        _ = (ModuleCat.Hom.hom
              ((ModuleCat.extendScalars g).map (ModuleCat.ofHom I.subtype) ≫
                (TensorProduct.AlgebraTensorModule.rid A B B).toModuleIso.hom)) x +
            (ModuleCat.Hom.hom
              ((ModuleCat.extendScalars g).map (ModuleCat.ofHom I.subtype) ≫
                (TensorProduct.AlgebraTensorModule.rid A B B).toModuleIso.hom)) y :=
          (ModuleCat.Hom.hom
            ((ModuleCat.extendScalars g).map (ModuleCat.ofHom I.subtype) ≫
              (TensorProduct.AlgebraTensorModule.rid A B B).toModuleIso.hom)).map_add x y
        _ = _ := by rw [hx, hy]
        _ = _ := by
          exact (ModuleCat.Hom.hom
            (ModuleCat.ofHom (idealBaseChangeLinearMap g I))).map_add x y |>.symm

/-- Flat affine base change identifies the pullback of the actual
closed-immersion ideal module with the actual ideal module of the
base-changed quotient presentation. -/
noncomputable def flatAffineClosedImmersionIdealModulePullbackIso
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (hg : g.Flat) (I : Ideal A) :
    letI : Algebra A B := g.toAlgebra
    let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
      (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).obj
      (IdealSheafDataModule.closedImmersionModule
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) ≅
    IdealSheafDataModule.closedImmersionModule
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))) := by
  letI : Algebra A B := g.toAlgebra
  let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
    (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
  exact (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).mapIso
      (affineQuotientIdealTildeClosedImmersionModuleIso I).symm ≪≫
    affineIdealTildePullbackIso g I ≪≫
      flatBaseChangeTensorActualIdealModuleIso g hg I

/-- The ambient comparison supplied by the affine `tilde` pullback
isomorphism, followed by contraction of `B ⊗[A] A` and the affine
description of the structure sheaf. -/
noncomputable def affineAmbientPullbackComparison
    {A B : Type u} [CommRing A] [CommRing B] (g : A →+* B) :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).obj
      (SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf) ⟶
        SheafOfModules.unit (Spec (CommRingCat.of B)).ringCatSheaf := by
  letI : Algebra A B := g.toAlgebra
  exact (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).map
      (affineGlobalSectionsUnitTildeIso (A := A)).inv ≫
    ((affineTildePullbackNatIso (CommRingCat.ofHom g)).app
      (ModuleCat.of A A)).hom ≫
    (tilde.functor (CommRingCat.of B)).map
      (TensorProduct.AlgebraTensorModule.rid A B B).toModuleIso.hom ≫
    (affineGlobalSectionsUnitTildeIso (A := B)).hom

/-- On affine spectra the explicitly constructed ambient comparison agrees
with its version based directly on the `tilde` sheaf. -/
theorem affineAmbientPullbackComparison_eq_tildeAmbientComparison
    {A B : Type u} [CommRing A] [CommRing B] (g : A →+* B) :
    affineAmbientPullbackComparison g =
      affineTildeAmbientComparison g := by
  letI : Algebra A B := g.toAlgebra
  have hA : (affineGlobalSectionsUnitTildeIso (A := A)).inv = 𝟙 _ := by
    rw [affineGlobalSectionsUnitTildeIso_eq_tildeSelf]
    rfl
  unfold affineAmbientPullbackComparison affineTildeAmbientComparison
    affineAmbientTargetMap
  rw [hA]
  let P := Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))
  let O := SheafOfModules.unit (Spec (CommRingCat.of A)).ringCatSheaf
  let t := ((affineTildePullbackNatIso (CommRingCat.ofHom g)).app
      (ModuleCat.of A A)).hom ≫ affineAmbientTargetMap g
  change P.map (𝟙 O) ≫ t = t
  exact (congrArg (fun f : P.obj O ⟶ P.obj O => f ≫ t)
    (P.map_id O)).trans (Category.id_comp t)

/-- The explicit affine ambient map used for ideal-module base change is
Mathlib's canonical pullback map on structure sheaves. -/
theorem affineAmbientPullbackComparison_eq_pullbackUnitComparison
    {A B : Type u} [CommRing A] [CommRing B] (g : A →+* B) :
    affineAmbientPullbackComparison g =
      BundleSectionZeroLocus.pullbackUnitComparison
        (Spec.map (CommRingCat.ofHom g)) := by
  rw [affineAmbientPullbackComparison_eq_tildeAmbientComparison,
    affineTildeAmbientComparison_eq_pullbackUnitComparison]

/-- The explicit ambient affine comparison is an isomorphism. -/
theorem isIso_affineAmbientPullbackComparison
    {A B : Type u} [CommRing A] [CommRing B] (g : A →+* B) :
    IsIso (affineAmbientPullbackComparison g) := by
  letI : Algebra A B := g.toAlgebra
  have h₁ : IsIso ((Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom g))).map
      (affineGlobalSectionsUnitTildeIso (A := A)).inv) :=
    ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).mapIso
      (affineGlobalSectionsUnitTildeIso (A := A)).symm).isIso_hom
  have h₂ : IsIso (((affineTildePullbackNatIso
      (CommRingCat.ofHom g)).app (ModuleCat.of A A)).hom) := inferInstance
  have h₃ : IsIso ((tilde.functor (CommRingCat.of B)).map
      (TensorProduct.AlgebraTensorModule.rid A B B).toModuleIso.hom) := inferInstance
  have h₄ : IsIso (affineGlobalSectionsUnitTildeIso (A := B)).hom :=
    (affineGlobalSectionsUnitTildeIso (A := B)).isIso_hom
  unfold affineAmbientPullbackComparison
  exact IsIso.comp_isIso' h₁
    (IsIso.comp_isIso' h₂ (IsIso.comp_isIso' h₃ h₄))

set_option backward.isDefEq.respectTransparency false in
/-- The actual affine ideal-module base-change isomorphism respects its
inclusion into the ambient structure sheaf, using the explicit affine
ambient comparison. -/
lemma flatAffineClosedImmersionIdealModulePullbackIso_hom_toUnit
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (hg : g.Flat) (I : Ideal A) :
    letI : Algebra A B := g.toAlgebra
    let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
      (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
    (flatAffineClosedImmersionIdealModulePullbackIso g hg I).hom ≫
      IdealSheafDataModule.closedImmersionModuleToUnit
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))) =
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).map
      (IdealSheafDataModule.closedImmersionModuleToUnit
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) ≫
      affineAmbientPullbackComparison g := by
  letI : Algebra A B := g.toAlgebra
  let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
    (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
  let P := Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))
  let FA := tilde.functor (CommRingCat.of A)
  let FB := tilde.functor (CommRingCat.of B)
  let eA := affineQuotientIdealTildeClosedImmersionModuleIso I
  let eT := affineIdealTildePullbackIso g I
  let eB := flatBaseChangeTensorActualIdealModuleIso g hg I
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
    flatBaseChangeTensorActualIdealModuleIso_hom_toUnit g hg I
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
lemma flatAffineClosedImmersionIdealModulePullbackIso_hom_toCanonicalUnit
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (hg : g.Flat) (I : Ideal A) :
    letI : Algebra A B := g.toAlgebra
    let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
      (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
    (flatAffineClosedImmersionIdealModulePullbackIso g hg I).hom ≫
      IdealSheafDataModule.closedImmersionModuleToUnit
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))) =
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).map
      (IdealSheafDataModule.closedImmersionModuleToUnit
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) ≫
      BundleSectionZeroLocus.pullbackUnitComparison
        (Spec.map (CommRingCat.ofHom g)) := by
  rw [← affineAmbientPullbackComparison_eq_pullbackUnitComparison]
  exact flatAffineClosedImmersionIdealModulePullbackIso_hom_toUnit g hg I

/-- Flat affine pullback preserves the monomorphism from the actual
closed-immersion ideal module into the structure sheaf. -/
lemma flatAffineClosedImmersionIdealModulePullback_mono
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (hg : g.Flat) (I : Ideal A) :
    Mono ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).map
      (IdealSheafDataModule.closedImmersionModuleToUnit
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))) := by
  letI : Algebra A B := g.toAlgebra
  let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
    (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
  have h := flatAffineClosedImmersionIdealModulePullbackIso_hom_toCanonicalUnit
    g hg I
  haveI : Mono (IdealSheafDataModule.closedImmersionModuleToUnit
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)))) := by
    change Mono (IdealSheafDataModule.idealModuleToUnit _)
    infer_instance
  have hm : Mono
      ((flatAffineClosedImmersionIdealModulePullbackIso g hg I).hom ≫
        IdealSheafDataModule.closedImmersionModuleToUnit
          (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K)))) := by
    have h₁ : Mono (flatAffineClosedImmersionIdealModulePullbackIso g hg I).hom := by
      exact mono_of_mono_fac
        (f := (flatAffineClosedImmersionIdealModulePullbackIso g hg I).inv)
        (flatAffineClosedImmersionIdealModulePullbackIso g hg I).hom_inv_id
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

/-- Flat affine pullback preserves the actual ideal inclusion of any
closed immersion into an affine scheme. The closed immersion is
presented as a quotient immersion up to source isomorphism. -/
theorem flatAffineClosedImmersionIdealModulePullback_mono_of_closed
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (hg : g.Flat)
    {Z : Scheme.{u}} (i : Z ⟶ Spec (CommRingCat.of A))
    [IsClosedImmersion i] :
    Mono ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).map
      (IdealSheafDataModule.closedImmersionModuleToUnit i)) := by
  obtain ⟨I, e, hi⟩ :=
    (IsClosedImmersion.Spec_iff (R := CommRingCat.of A) (f := i)).mp inferInstance
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have hk : (e.hom ≫ q).ker = q.ker :=
    Scheme.Hom.ker_comp_of_isIso e.hom q
  rw [hi]
  change Mono ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).map
    (IdealSheafDataModule.idealModuleToUnit (e.hom ≫ q).ker))
  rw [hk]
  exact flatAffineClosedImmersionIdealModulePullback_mono g hg I

/-- Transport of the actual ideal-module sheaf along an equality of
ideal-sheaf data. -/
noncomputable def idealModuleTransport
    {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I = J) :
    IdealSheafDataModule.idealModule I ≅
      IdealSheafDataModule.idealModule J :=
  eqToIso (congrArg IdealSheafDataModule.idealModule h)

/-- Ideal-module transport is the identity for reflexive equality. -/
theorem idealModuleTransport_refl
    {X : Scheme.{u}} (I : X.IdealSheafData) :
    idealModuleTransport (Eq.refl I) =
      Iso.refl (IdealSheafDataModule.idealModule I) := by
  rfl

/-- Ideal-module transports compose as the underlying equalities do;
this is the cocycle law needed on overlaps of affine charts. -/
theorem idealModuleTransport_trans
    {X : Scheme.{u}} {I J K : X.IdealSheafData}
    (h : I = J) (k : J = K) :
    idealModuleTransport (h.trans k) =
      idealModuleTransport h ≪≫ idealModuleTransport k := by
  cases h
  cases k
  simp [idealModuleTransport]

theorem idealModuleTransport_hom_toUnit
    {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I = J) :
    (idealModuleTransport h).hom ≫
      IdealSheafDataModule.idealModuleToUnit J =
        IdealSheafDataModule.idealModuleToUnit I := by
  cases h
  simp [idealModuleTransport]

theorem idealModuleTransport_inv_toUnit
    {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I = J) :
    (idealModuleTransport h).inv ≫
      IdealSheafDataModule.idealModuleToUnit I =
        IdealSheafDataModule.idealModuleToUnit J := by
  cases h
  simp [idealModuleTransport]

/-- An inclusion square remains commutative when the target ideal
module is transported along equality of ideal-sheaf data. -/
theorem idealModuleTransport_trans_hom_toUnit
    {X : Scheme.{u}} {I J : X.IdealSheafData} (h : I = J)
    {M : SheafOfModules X.ringCatSheaf}
    (e : M ≅ IdealSheafDataModule.idealModule I)
    (v : M ⟶ SheafOfModules.unit X.ringCatSheaf)
    (he : e.hom ≫ IdealSheafDataModule.idealModuleToUnit I = v) :
    (e ≪≫ idealModuleTransport h).hom ≫
      IdealSheafDataModule.idealModuleToUnit J = v := by
  rw [Iso.trans_hom, Category.assoc, idealModuleTransport_hom_toUnit h]
  exact he

/-- Iterated pullback of ideal-sheaf data yields the same actual ideal
module as pullback along the composite scheme morphism. -/
noncomputable def idealModuleComapCompIso
    {X Y Z : Scheme.{u}} (I : Z.IdealSheafData)
    (f : Y ⟶ Z) (g : X ⟶ Y) :
    IdealSheafDataModule.idealModule ((I.comap f).comap g) ≅
      IdealSheafDataModule.idealModule (I.comap (g ≫ f)) :=
  idealModuleTransport (I.comap_comp g f).symm



/-- Changing the source of a closed immersion by an isomorphism leaves
its actual ideal-module sheaf unchanged. -/
noncomputable def closedImmersionModuleSourceIso
    {X Z Z' : Scheme.{u}} (e : Z ≅ Z') (i : Z' ⟶ X) :
    IdealSheafDataModule.closedImmersionModule (e.hom ≫ i) ≅
      IdealSheafDataModule.closedImmersionModule i := by
  exact idealModuleTransport (Scheme.Hom.ker_comp_of_isIso e.hom i)


/-- The quotient presentation and the first projection of the literal
fibre product define the same ideal-sheaf data on `Spec B`. -/
theorem affineFibreProductIdealDataEq
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (I : Ideal A) :
    letI : Algebra A B := g.toAlgebra
    let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
      (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))).ker =
      (pullback.fst (Spec.map (CommRingCat.ofHom g))
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).ker := by
  letI : Algebra A B := g.toAlgebra
  let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
    (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
  let e := affineBaseChangedClosedImmersionSpecIso g I
  let q := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))
  calc
    q.ker = (e.hom ≫ q).ker :=
      (Scheme.Hom.ker_comp_of_isIso e.hom q).symm
    _ = (pullback.fst (Spec.map (CommRingCat.ofHom g))
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).ker := by
      rw [affineBaseChangedClosedImmersionSpecIso_hom_fst g I]

/-- The pullback of the actual affine quotient ideal module is the
ideal module of the first projection of the literal fibre product. -/
noncomputable def flatAffineFibreProductIdealModulePullbackIso
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (hg : g.Flat) (I : Ideal A) :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).obj
      (IdealSheafDataModule.closedImmersionModule
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) ≅
    IdealSheafDataModule.closedImmersionModule
      (pullback.fst (Spec.map (CommRingCat.ofHom g))
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) := by
  letI : Algebra A B := g.toAlgebra
  let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
    (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
  exact flatAffineClosedImmersionIdealModulePullbackIso g hg I ≪≫
    idealModuleTransport (affineFibreProductIdealDataEq g I)

/-- The ideal data of the literal affine fibre product is the global
ideal-sheaf-data pullback of the original closed immersion. -/
theorem affineFibreProductIdealData_eq_comap
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (I : Ideal A) :
    (pullback.fst (Spec.map (CommRingCat.ofHom g))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).ker =
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.comap
      (Spec.map (CommRingCat.ofHom g)) := by
  letI : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
    IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom (Ideal.Quotient.mk I)) Ideal.Quotient.mk_surjective
  exact Scheme.IdealSheafData.ker_fst_of_isClosedImmersion
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
    (Spec.map (CommRingCat.ofHom g))

/-- The affine quotient presentation has exactly the pulled-back
ideal-sheaf data, connecting the affine calculation to global `comap`. -/
theorem affineQuotientIdealData_eq_comap
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (I : Ideal A) :
    letI : Algebra A B := g.toAlgebra
    let K : Ideal B := RingHom.ker (Algebra.TensorProduct.includeLeft
      (R := A) (S := A) (A := B) (B := A ⧸ I)).toRingHom
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk K))).ker =
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.comap
      (Spec.map (CommRingCat.ofHom g)) := by
  exact (affineFibreProductIdealDataEq g I).trans
    (affineFibreProductIdealData_eq_comap g I)

/-- On affine spectra, flat pullback of the actual ideal module agrees
with the actual module of Mathlib's globally defined ideal-data `comap`. -/
noncomputable def flatAffineIdealDataComapModulePullbackIso
    {A B : Type u} [CommRing A] [CommRing B]
    (g : A →+* B) (hg : g.Flat) (I : Ideal A) :
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom g))).obj
      (IdealSheafDataModule.closedImmersionModule
        (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))) ≅
    IdealSheafDataModule.idealModule
      ((Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))).ker.comap
        (Spec.map (CommRingCat.ofHom g))) := by
  letI : Algebra A B := g.toAlgebra
  exact flatAffineClosedImmersionIdealModulePullbackIso g hg I ≪≫
    idealModuleTransport (affineQuotientIdealData_eq_comap g I)




end PfaffianDescent
