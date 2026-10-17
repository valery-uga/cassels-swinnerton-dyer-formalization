import PfaffianDescent.ActualFieldPointLineAdjoint
import PfaffianDescent.ActualSchemePullbackCompHomEquiv

/- SOURCE ONLY / UNVERIFIED. Exact point quotient and composite adjunction
square under ANY actual chart-source Iso. This is a generic transport helper;
the actual cubic caller derives its chart-source Iso internally. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

variable {L : Type u} [Field L] {Y X : Scheme.{u}}
    (qU : Spec (.of L) ⟶ Y) (i : Y ⟶ X) (M : X.Modules) (N : Y.Modules)
    (e : (Scheme.Modules.pullback i).obj M ≅ N)
    (ell : (moduleSpecΓFunctor (R := .of L)).obj
      ((Scheme.Modules.pullback (qU ≫ i)).obj M) →ₗ[L] L)

def actualFieldPointLine_chartPointHom :
    (Scheme.Modules.pullback qU).obj N ⟶ SheafOfModules.unit (Spec (.of L)).ringCatSheaf :=
  (Scheme.Modules.pullback qU).map e.inv ≫
    (Scheme.Modules.pullbackComp qU i).hom.app M ≫
      actualFieldPointModuleLineHom ((Scheme.Modules.pullback (qU ≫ i)).obj M) ell

def actualFieldPointLine_chartFunctional :
    (moduleSpecΓFunctor (R := .of L)).obj ((Scheme.Modules.pullback qU).obj N) →ₗ[L] L :=
  (affineGlobalSectionsUnitLinearEquiv (A := L)).toLinearMap.comp
    ((moduleSpecΓFunctor (R := .of L)).map
      (actualFieldPointLine_chartPointHom qU i M N e ell)).hom

theorem actualFieldPointLine_chartFunctional_surjective
    (hell : Function.Surjective ell) :
    Function.Surjective (actualFieldPointLine_chartFunctional qU i M N e ell) := by
  let F := moduleSpecΓFunctor (R := CommRingCat.of L)
  let a := (Scheme.Modules.pullback qU).map e.inv ≫
    (Scheme.Modules.pullbackComp qU i).hom.app M
  letI : IsIso a := by dsimp only [a]; infer_instance
  have ha : Function.Surjective (F.map a) := (ConcreteCategory.bijective_of_isIso _).2
  have hb : Function.Surjective (F.map
      (actualFieldPointModuleLineHom ((Scheme.Modules.pullback (qU ≫ i)).obj M) ell)) := by
    rw [actualFieldPointModuleLineHom_gamma]
    exact (affineGlobalSectionsUnitLinearEquiv (A := L)).symm.surjective.comp hell
  change Function.Surjective ((affineGlobalSectionsUnitLinearEquiv (A := L)).toLinearMap.comp
    (F.map (a ≫ actualFieldPointModuleLineHom _ ell)).hom)
  rw [Functor.map_comp]
  exact (affineGlobalSectionsUnitLinearEquiv (A := L)).surjective.comp (hb.comp ha)

theorem actualFieldPointLine_chartFunctional_pointHom :
    actualFieldPointModuleLineHom ((Scheme.Modules.pullback qU).obj N)
      (actualFieldPointLine_chartFunctional qU i M N e ell) =
        actualFieldPointLine_chartPointHom qU i M N e ell := by
  apply actualFieldPointModuleGamma_fullyFaithful.map_injective
  rw [actualFieldPointModuleLineHom_gamma]
  apply ModuleCat.hom_ext
  ext w
  exact (affineGlobalSectionsUnitLinearEquiv (A := L)).symm_apply_apply _

theorem actualFieldPointLine_chartFunctional_composite_pointHom :
    (Scheme.Modules.pullbackComp qU i).inv.app M ≫
      (Scheme.Modules.pullback qU).map e.hom ≫
        actualFieldPointModuleLineHom ((Scheme.Modules.pullback qU).obj N)
          (actualFieldPointLine_chartFunctional qU i M N e ell) =
      actualFieldPointModuleLineHom ((Scheme.Modules.pullback (qU ≫ i)).obj M) ell := by
  rw [actualFieldPointLine_chartFunctional_pointHom]
  have he : (Scheme.Modules.pullback qU).map e.hom ≫ (Scheme.Modules.pullback qU).map e.inv = 𝟙 _ := by
    rw [← Functor.map_comp, e.hom_inv_id, Functor.map_id]
  calc
    _ = (Scheme.Modules.pullbackComp qU i).inv.app M ≫
      ((Scheme.Modules.pullback qU).map e.hom ≫ (Scheme.Modules.pullback qU).map e.inv) ≫
        (Scheme.Modules.pullbackComp qU i).hom.app M ≫
          actualFieldPointModuleLineHom ((Scheme.Modules.pullback (qU ≫ i)).obj M) ell := by
      simp only [actualFieldPointLine_chartPointHom, Category.assoc]
    _ = _ := by rw [he]; simp

/-- Actual native point line and genuine global adjoint have the precise
composite pushforward square, proved from the actual adjunction units. -/
theorem actualFieldPointLine_chartFunctional_adjoint_square :
    actualFieldPointLineAdjoint (qU ≫ i) M ell =
      (Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv M N e.hom ≫
        (Scheme.Modules.pushforward i).map
          (actualFieldPointLineAdjoint qU N
            (actualFieldPointLine_chartFunctional qU i M N e ell)) ≫
              (Scheme.Modules.pushforwardComp qU i).hom.app
                (SheafOfModules.unit (Spec (.of L)).ringCatSheaf) := by
  have h := actualSchemePullbackComp_homEquiv qU i M N
    (SheafOfModules.unit (Spec (.of L)).ringCatSheaf) e.hom
      (actualFieldPointModuleLineHom ((Scheme.Modules.pullback qU).obj N)
        (actualFieldPointLine_chartFunctional qU i M N e ell))
  rw [actualFieldPointLine_chartFunctional_composite_pointHom] at h
  exact h

end PfaffianDescent
