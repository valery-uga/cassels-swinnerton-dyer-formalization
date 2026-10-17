import PfaffianDescent.ActualFieldPointLineAdjoint
import PfaffianDescent.ActualAffineQuotientPointClassSurjective

/- SOURCE ONLY / UNVERIFIED. Literal Gamma of the actual affine sheaf
adjoint is surjective for the ACTUAL quotient ring and every tilde module. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

theorem actualAffineQuotientFieldPointLineAdjoint_gamma_surjective
    {R L : Type u} [CommRing R] [Field L]
    (rho : R →+* L) (hquot : Function.Surjective rho) (M : ModuleCat R)
    (ell : (moduleSpecΓFunctor (R := CommRingCat.of L)).obj
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom rho))).obj
        ((tilde.functor (CommRingCat.of R)).obj M)) →ₗ[L] L)
    (hell : Function.Surjective ell) :
    Function.Surjective ((moduleSpecΓFunctor (R := CommRingCat.of R)).map
      (actualFieldPointLineAdjoint (Spec.map (CommRingCat.ofHom rho))
        ((tilde.functor (CommRingCat.of R)).obj M) ell)) := by
  let phi := CommRingCat.ofHom rho
  let q := Spec.map phi
  let O := SheafOfModules.unit (Spec (.of L)).ringCatSheaf
  let U := (Scheme.Modules.pullback q).obj ((tilde.functor (.of R)).obj M)
  let psi := actualFieldPointModuleLineHom U ell
  let t := actualFieldPointLineAdjoint q ((tilde.functor (.of R)).obj M) ell
  let F := moduleSpecΓFunctor (R := CommRingCat.of R)
  let E := affineGammaPushforwardLinearEquiv phi O
  let eta := (tilde.adjunction (R := CommRingCat.of R)).unit.app M
  let adj := ((tilde.adjunction (R := CommRingCat.of R)).comp
    (Scheme.Modules.pullbackPushforwardAdjunction q)).ofNatIsoRight
      (affineGammaPushforwardNatIso phi)
  have hCalc : eta ≫ F.map t ≫ E.toModuleIso.hom =
      adj.unit.app M ≫ (ModuleCat.restrictScalars rho).map
        ((moduleSpecΓFunctor (R := CommRingCat.of L)).map psi) := by
    calc
      _ = adj.homEquiv M O psi := by
        dsimp only [adj]
        rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv,
          Equiv.trans_apply, Adjunction.homEquiv_unit]
        rfl
      _ = _ := by rw [Adjunction.homEquiv_unit]; rfl
  have hApply (m : M) : E (F.map t (eta m)) =
      (moduleSpecΓFunctor (R := CommRingCat.of L)).map psi
        (affineTildeActualPointClass phi M m) :=
    ConcreteCategory.congr_hom hCalc m
  have hPsi : Function.Surjective ((moduleSpecΓFunctor (R := .of L)).map psi) := by
    rw [actualFieldPointModuleLineHom_gamma]
    exact (affineGlobalSectionsUnitLinearEquiv (A := L)).symm.surjective.comp hell
  have hPoint := actualAffineQuotientPointClass_surjective phi hquot M
  intro y
  obtain ⟨w, hw⟩ := hPsi (E y)
  obtain ⟨m, hm⟩ := hPoint w
  refine ⟨eta m, E.injective ?_⟩
  rw [hApply, hm, hw]

end PfaffianDescent
