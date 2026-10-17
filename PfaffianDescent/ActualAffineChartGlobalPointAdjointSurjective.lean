import PfaffianDescent.ActualFieldPointLineChartSourceIso
import PfaffianDescent.ActualOpenPullbackAdjunctionChartIso
import PfaffianDescent.ActualAffineQuotientPointAdjointGamma

/- SOURCE ONLY / UNVERIFIED. Genuine global adjoint is surjective on the
actual chart image. Generic source-Iso input is discharged at actual cubic. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

theorem actualAffineChartGlobalPointLineAdjoint_app_surjective
    {R L : Type u} [CommRing R] [Field L] {X : Scheme.{u}}
    (i : Spec (.of R) ⟶ X) [IsOpenImmersion i]
    (rho : R →+* L) (hquot : Function.Surjective rho)
    (M : X.Modules) (A : ModuleCat R)
    (e : (Scheme.Modules.pullback i).obj M ≅ (tilde.functor (.of R)).obj A)
    (ell : (moduleSpecΓFunctor (R := .of L)).obj
      ((Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom rho) ≫ i)).obj M) →ₗ[L] L)
    (hell : Function.Surjective ell) :
    Function.Surjective ((actualFieldPointLineAdjoint
      (Spec.map (CommRingCat.ofHom rho) ≫ i) M ell).app (i ''ᵁ ⊤)) := by
  let qU := Spec.map (CommRingCat.ofHom rho)
  let N := (tilde.functor (.of R)).obj A
  let O := SheafOfModules.unit (Spec (.of L)).ringCatSheaf
  let V := i ''ᵁ ⊤
  let ellU := actualFieldPointLine_chartFunctional qU i M N e ell
  have hellU : Function.Surjective ellU :=
    actualFieldPointLine_chartFunctional_surjective qU i M N e ell hell
  let a := (Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv M N e.hom
  let b := actualFieldPointLineAdjoint qU N ellU
  let c := (Scheme.Modules.pushforwardComp qU i).hom.app O
  letI : IsIso (a.app V) := actualOpenPullbackAdjunction_chartIso_app_isIso i M N e
  have ha : Function.Surjective (a.app V) := (ConcreteCategory.bijective_of_isIso _).2
  have hb : Function.Surjective (((Scheme.Modules.pushforward i).map b).app V) := by
    change Function.Surjective (b.app (i ⁻¹ᵁ V))
    rw [i.preimage_image_eq]
    exact actualAffineQuotientFieldPointLineAdjoint_gamma_surjective rho hquot A ellU hellU
  have hc : Function.Surjective (c.app V) := (ConcreteCategory.bijective_of_isIso _).2
  rw [actualFieldPointLine_chartFunctional_adjoint_square]
  change Function.Surjective (fun m => c.app V (((Scheme.Modules.pushforward i).map b).app V (a.app V m)))
  exact hc.comp (hb.comp ha)

end PfaffianDescent
