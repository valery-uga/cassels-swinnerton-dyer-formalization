import PfaffianDescent.FiniteProductModuleDecomposition
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-!
# The structure sheaf of an affine finite product

The regular module of a finite product ring splits into its coordinate
modules.  Applying the affine `tilde` functor gives the corresponding
finite-biproduct decomposition of the structure sheaf.  This is the sheaf
decomposition on the split finite scheme needed in Voisin's argument.
-/

namespace PfaffianDescent

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

universe u

variable {J : Type u} [Fintype J] (R : J → Type u) [∀ i, CommRing (R i)]

set_option backward.isDefEq.respectTransparency false in
/-- The structure sheaf on the spectrum of a finite product is the finite
biproduct of the affine sheaves associated to its coordinate modules. -/
noncomputable def productCoordinateTildeBiproductIsoUnit :
    (⨁ fun i ↦ tilde (productCoordinateModule R i)) ≅
      SheafOfModules.unit.{u} (Spec (.of (∀ i, R i))).ringCatSheaf := by
  let F := tilde.functor (.of (∀ i, R i))
  letI : F.IsLeftAdjoint :=
    AlgebraicGeometry.instIsLeftAdjointModuleCatCarrierModulesSpecOfFunctor
      (R := .of (∀ i, R i))
  let H : IsColimit <|
      F.mapCocone (biproduct.bicone
        (fun i ↦ productCoordinateModule R i)).toCocone :=
    isColimitOfPreserves F
      (biproduct.isColimit (fun i ↦ productCoordinateModule R i))
  letI diagramIso :
      Discrete.functor (fun i ↦ productCoordinateModule R i) ⋙ F ≅
        Discrete.functor (fun i ↦ F.obj (productCoordinateModule R i)) :=
    Discrete.natIso (fun _ ↦ Iso.refl _)
  let e : F.obj (⨁ fun i ↦ productCoordinateModule R i) ≅
      (⨁ fun i ↦ F.obj (productCoordinateModule R i)) :=
    IsColimit.coconePointUniqueUpToIso
      ((IsColimit.precomposeHomEquiv diagramIso.symm _).symm H)
      (biproduct.isColimit
        (fun i ↦ F.obj (productCoordinateModule R i)))
  exact
    e.symm ≪≫
      F.mapIso (productCoordinateBiproductIsoRegular R) ≪≫
      tildeSelf

/-- The point-sheaf on the `i`th affine factor, pushed to the spectrum of
the product ring. -/
noncomputable abbrev productCoordinatePointPushforward (i : J) :
    (Spec (.of (∀ j, R j))).Modules :=
  (Scheme.Modules.pushforward
    (Spec.map (CommRingCat.ofHom (Pi.evalRingHom R i)))).obj
      (SheafOfModules.unit.{u} (Spec (.of (R i))).ringCatSheaf)

/-- Global sections of the coordinate point-pushforward are its coordinate
module over the product ring. -/
noncomputable def productCoordinateGlobalSectionsLinearEquiv (i : J) :
    productCoordinateModule R i ≃ₗ[(∀ j, R j)]
      (modulesSpecToSheaf.obj
        (productCoordinatePointPushforward R i)).presheaf.obj (.op ⊤) where
  toFun := (Scheme.ΓSpecIso (.of (R i))).inv
  invFun := (Scheme.ΓSpecIso (.of (R i))).hom
  left_inv := (Scheme.ΓSpecIso (.of (R i))).inv_hom_id_apply
  right_inv := (Scheme.ΓSpecIso (.of (R i))).hom_inv_id_apply
  map_add' := map_add _
  map_smul' b x := by
    change (Scheme.ΓSpecIso (.of (R i))).inv
      (b i * (show R i from x)) = _
    rw [map_mul]
    congr 1
    exact congrArg
      (fun f : CommRingCat.of (∀ j, R j) ⟶
          Γ(Spec (.of (R i)), ⊤) ↦ f b)
      (Scheme.ΓSpecIso_inv_naturality
        (CommRingCat.ofHom (Pi.evalRingHom R i)))

set_option backward.isDefEq.respectTransparency false in
/-- The affine sheaf of a coordinate module is the pushforward of the
structure sheaf from that coordinate point. -/
noncomputable def productCoordinateTildeIsoPointPushforward (i : J) :
    tilde (productCoordinateModule R i) ≅
      productCoordinatePointPushforward R i := by
  let M := productCoordinatePointPushforward R i
  letI : IsIso (Scheme.Modules.fromTildeΓ
      (R := .of (R i))
      (SheafOfModules.unit.{u} (Spec (.of (R i))).ringCatSheaf)) :=
    isIso_fromTildeΓ_iff.mpr ⟨_, ⟨tildeSelf⟩⟩
  letI : IsIso (Scheme.Modules.fromTildeΓ
      (R := .of (∀ j, R j)) M) :=
    isIso_fromTildeΓ_pushforward
      (CommRingCat.ofHom (Pi.evalRingHom R i))
      (SheafOfModules.unit.{u} (Spec (.of (R i))).ringCatSheaf)
  exact
    (tilde.functor (.of (∀ j, R j))).mapIso
      (LinearEquiv.toModuleIso
        (productCoordinateGlobalSectionsLinearEquiv R i)) ≪≫
      asIso (Scheme.Modules.fromTildeΓ
        (R := .of (∀ j, R j)) M)

/-- The structure sheaf on the split affine finite scheme is the finite
biproduct of the structure sheaves of its coordinate points, each pushed
forward along the corresponding affine point inclusion. -/
noncomputable def productCoordinatePointPushforwardBiproductIsoUnit :
    (⨁ fun i ↦ productCoordinatePointPushforward R i) ≅
      SheafOfModules.unit.{u} (Spec (.of (∀ i, R i))).ringCatSheaf :=
  (biproduct.mapIso
    (fun i ↦ productCoordinateTildeIsoPointPushforward R i)).symm ≪≫
    productCoordinateTildeBiproductIsoUnit R

/-- The `i`th affine coordinate point of the spectrum of a product ring. -/
noncomputable abbrev productCoordinateSpecMap (i : J) :
    Spec (.of (R i)) ⟶ Spec (.of (∀ j, R j)) :=
  Spec.map (CommRingCat.ofHom (Pi.evalRingHom R i))

/-- Every coordinate point of a product ring is a closed subscheme: the
coordinate evaluation map on rings is surjective. -/
noncomputable instance productCoordinateSpecMap_isClosedImmersion (i : J) :
    IsClosedImmersion (productCoordinateSpecMap R i) :=
  IsClosedImmersion.spec_of_surjective _ (Function.surjective_eval i)

/-- A coordinate point-sheaf pushed all the way to an ambient scheme. -/
noncomputable abbrev productCoordinatePointPushforwardToAmbient
    {X : Scheme.{u}} (j : Spec (.of (∀ k, R k)) ⟶ X) (i : J) : X.Modules :=
  (Scheme.Modules.pushforward (productCoordinateSpecMap R i ≫ j)).obj
    (SheafOfModules.unit.{u} (Spec (.of (R i))).ringCatSheaf)

set_option backward.isDefEq.respectTransparency false in
/-- Pushing a split finite affine scheme into an ambient scheme carries its
structure sheaf to the finite biproduct of the pushed-forward coordinate
point sheaves. -/
noncomputable def productCoordinatePointPushforwardToAmbientBiproductIso
    {X : Scheme.{u}} (j : Spec (.of (∀ k, R k)) ⟶ X) :
    (⨁ fun i ↦ productCoordinatePointPushforwardToAmbient R j i) ≅
      (Scheme.Modules.pushforward j).obj
        (SheafOfModules.unit.{u}
          (Spec (.of (∀ i, R i))).ringCatSheaf) := by
  let F := Scheme.Modules.pushforward j
  let coordinate : J → (Spec (.of (∀ k, R k))).Modules :=
    fun i ↦ productCoordinatePointPushforward R i
  letI : PreservesLimit (Discrete.functor coordinate) F := inferInstance
  letI : PreservesBiproduct coordinate F :=
    preservesBiproduct_of_preservesProduct F
  let pointIso : ∀ i,
      productCoordinatePointPushforwardToAmbient R j i ≅
        F.obj (coordinate i) := fun i ↦
    ((Scheme.Modules.pushforwardComp
      (productCoordinateSpecMap R i) j).app
        (SheafOfModules.unit.{u}
          (Spec (.of (R i))).ringCatSheaf)).symm
  exact
    biproduct.mapIso pointIso ≪≫
      (F.mapBiproduct coordinate).symm ≪≫
      F.mapIso (productCoordinatePointPushforwardBiproductIsoUnit R)

end PfaffianDescent
