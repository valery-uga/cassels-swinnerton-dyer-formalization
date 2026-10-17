import PfaffianDescent.NativeOpenPullbackUnitScalar
import PfaffianDescent.SchemeModuleGlobalSectionsBaseEq

/-! SOURCE ONLY. Normalization preserves SAME whole section maps and
canonical original base-field actions. No geometric image premise is used. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory BundleSectionZeroLocus
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] isIso_pullbackUnitComparison

private noncomputable instance nativeNormalizedHZeroAddCommGroup
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (M : X.Modules) :
    AddCommGroup (SchemeModuleGlobalSectionsOver p M) :=
  instAddCommGroupSchemeModuleGlobalSectionsOver (K := K) (X := X) p M

private noncomputable instance nativeNormalizedHZeroModule
    {K : Type u} [Field K] {X : Scheme.{u}} (p : X ⟶ Spec (.of K)) (M : X.Modules) :
    Module K (SchemeModuleGlobalSectionsOver p M) :=
  instModuleSchemeModuleGlobalSectionsOver (K := K) (X := X) p M

/-- Direct normalized pullback followed by its native composition Iso is
the iterated normalized pullback of the SAME whole section map. -/
theorem nativeNormalizedPullbackSectionMap_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)
    (s : SheafOfModules.unit Z.ringCatSheaf ⟶ M) :
    inv (pullbackUnitComparison (f ≫ g)) ≫
      (Scheme.Modules.pullback (f ≫ g)).map s ≫
      (Scheme.Modules.pullbackComp f g).inv.app M =
    inv (pullbackUnitComparison f) ≫
      (Scheme.Modules.pullback f).map
        (inv (pullbackUnitComparison g) ≫ (Scheme.Modules.pullback g).map s) := by
  let O := SheafOfModules.unit Z.ringCatSheaf
  let E := Scheme.Modules.pullbackComp f g
  have hn : (Scheme.Modules.pullback (f ≫ g)).map s ≫ E.inv.app M =
      E.inv.app O ≫ (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map s) :=
    E.inv.naturality s
  have hu := pullbackUnitComparison_inverse_comp_of_comp f g
    (isIso_pullbackUnitComparison f) (isIso_pullbackUnitComparison g)
    (isIso_pullbackUnitComparison (f ≫ g)) (pullbackUnitComparison_comp f g)
  calc
    _ = inv (pullbackUnitComparison (f ≫ g)) ≫ E.inv.app O ≫
        (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map s) := by rw [hn]
    _ = inv (pullbackUnitComparison f) ≫
        (Scheme.Modules.pullback f).map (inv (pullbackUnitComparison g)) ≫
        (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map s) := by
      rw [← Category.assoc, hu, Category.assoc]
    _ = _ := by rw [Functor.map_comp]

/-- The SAME identity after an arbitrary actual coefficient morphism.
This is structural naturality; actual graded adjuncts provide the image law. -/
theorem nativeNormalizedPullbackSectionMap_comp_coefficient
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) (N : Y.Modules)
    (s : SheafOfModules.unit Z.ringCatSheaf ⟶ M)
    (e : (Scheme.Modules.pullback g).obj M ⟶ N) :
    inv (pullbackUnitComparison (f ≫ g)) ≫
      (Scheme.Modules.pullback (f ≫ g)).map s ≫
      (Scheme.Modules.pullbackComp f g).inv.app M ≫ (Scheme.Modules.pullback f).map e =
    inv (pullbackUnitComparison f) ≫ (Scheme.Modules.pullback f).map
      (inv (pullbackUnitComparison g) ≫ (Scheme.Modules.pullback g).map s ≫ e) := by
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun z => z ≫ (Scheme.Modules.pullback f).map e)
      (nativeNormalizedPullbackSectionMap_comp f g M s)

/-- Genuine normalized pullback is linear for the SAME actual composed
structure morphism; scalars are ordinary pullbacks of base constants. -/
def nativeNormalizedPullbackGlobalSectionLinearMap
    {K : Type u} [Field K] {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (p : Y ⟶ Spec (.of K)) (M : Y.Modules) :
    SchemeModuleGlobalSectionsOver p M →ₗ[K]
      SchemeModuleGlobalSectionsOver (f ≫ p) ((Scheme.Modules.pullback f).obj M) where
  toFun s := inv (pullbackUnitComparison f) ≫ (Scheme.Modules.pullback f).map s
  map_add' s t := by
    change inv (pullbackUnitComparison f) ≫ (Scheme.Modules.pullback f).map (s + t) = _
    rw [Functor.map_add, Preadditive.comp_add]
  map_smul' c s := by
    let q := pullbackUnitComparison f
    letI : IsIso q := isIso_pullbackUnitComparison f
    let a := schemeModuleConstantEndomorphism p c
    have ha : inv q ≫ (Scheme.Modules.pullback f).map a ≫ q =
        schemeModuleConstantEndomorphism (f ≫ p) c := by
      exact (pullbackUnitEndomorphism_eq_nativeRestrict f a).trans
        ((restrictUnitEndomorphismOfRegularFunction_eq_appTop f (affineFunctionHom p c)).trans
          (congrArg unitEndomorphismOfRegularFunction
            (DFunLike.congr_fun (affineFunctionHom_comp f p).symm c)))
    change inv q ≫ (Scheme.Modules.pullback f).map (a ≫ s) =
      schemeModuleConstantEndomorphism (f ≫ p) c ≫
        inv q ≫ (Scheme.Modules.pullback f).map s
    rw [Functor.map_comp, ← ha]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]

end PfaffianDescent
