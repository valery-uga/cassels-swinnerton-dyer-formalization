import PfaffianDescent.CorayCartierIntrinsicNormalCechH1
import PfaffianDescent.CoraySelectedComponentActualCubicHomResolution

/-! SAME selected minimal component and SAME original K actions: actual
intrinsic-candidate H1 and actual ambient-pushforward H1 are linearly
equivalent by the original affine-cover/section transport. No dualizing,
Serre perfectness or canonical right-adjoint Ext-map identification.
SOURCE ONLY / UNVERIFIED. Root owns all compiler checks. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Original smooth-cubic and actual selected-minimal-component geometry
construct the K-linear H1 comparison of the native coefficient D. Native
quasicoherence, affine-cover Ext vanishing and all HasExt infrastructure
are internal; the intrinsic field action is independently toBase C. -/
def selectedProjectiveMinimalComponent_actualCubicIntrinsicH1CechLinearEquiv
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes) :
    let hCp : p ∈ C.toIdeal := hCmin.le (by
      rw [projectiveIntersectionIdeal_toIdeal]
      exact Ideal.subset_span (Set.mem_insert p {q}))
    let i := PfaffianDescent.homogeneousFixedCurveToCubic p hp C hCp
    letI : IsClosedImmersion i :=
      PfaffianDescent.homogeneousFixedCurveToCubic_closedImmersion p hp C hCp
    let W := sheafOfModules (grading (equationIdeal p hp)) 1
    let D := schemeModuleTensor ((Scheme.Modules.pullback i).obj W)
      (SchemeModuleInternalHom.dual (actualClosedImmersionConormalModule i))
    letI : EnoughInjectives (hypersurface p hp).Modules :=
      sheafOfModules_enoughInjectives (hypersurface p hp).ringCatSheaf
    letI : HasExt.{u} (hypersurface p hp).Modules :=
      CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} (hypersurface p hp).Modules
    letI : EnoughInjectives (scheme C).Modules :=
      sheafOfModules_enoughInjectives (scheme C).ringCatSheaf
    letI : HasExt.{u} (scheme C).Modules :=
      CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} (scheme C).Modules
    letI : Linear K (hypersurface p hp).Modules :=
      schemeModulesLinearOver (hypersurfaceToBase p hp)
    letI : Linear K (scheme C).Modules := schemeModulesLinearOver (toBase C)
    schemeModuleCohomology (hypersurface p hp) ((Scheme.Modules.pushforward i).obj D) 1 ≃ₗ[K]
      schemeModuleCohomology (scheme C) D 1 := by
  let hCp : p ∈ C.toIdeal := hCmin.le (by
    rw [projectiveIntersectionIdeal_toIdeal]
    exact Ideal.subset_span (Set.mem_insert p {q}))
  let i := PfaffianDescent.homogeneousFixedCurveToCubic p hp C hCp
  let X := hypersurface p hp
  let pi := hypersurfaceToBase p hp
  let W := sheafOfModules (grading (equationIdeal p hp)) 1
  let D := schemeModuleTensor ((Scheme.Modules.pullback i).obj W)
    (SchemeModuleInternalHom.dual (actualClosedImmersionConormalModule i))
  letI : IsClosedImmersion i :=
    PfaffianDescent.homogeneousFixedCurveToCubic_closedImmersion p hp C hCp
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : HasExt.{u} X.Modules :=
    CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
  letI : EnoughInjectives (scheme C).Modules :=
    sheafOfModules_enoughInjectives (scheme C).ringCatSheaf
  letI : HasExt.{u} (scheme C).Modules :=
    CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} (scheme C).Modules
  letI : LocallyOfFiniteType pi := inferInstance
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian pi
  letI : LocallyOfFiniteType (toBase C) := inferInstance
  letI : IsLocallyNoetherian (scheme C) :=
    LocallyOfFiniteType.isLocallyNoetherian (toBase C)
  let H := selectedProjectiveMinimalComponent_actualRegularPrincipalImmersion
    p q hp hp0 n hq hnot C hCmin
  let hW : schemeModuleLocallyRankOne W := cubicIntrinsicNegativeOne_locallyRankOne p hp
  let P : (scheme C ⟶ Spec (CommRingCat.of K)) → Type _ := fun rho =>
    letI : Linear K X.Modules := schemeModulesLinearOver pi
    letI : Linear K (scheme C).Modules := schemeModulesLinearOver rho
    schemeModuleCohomology X ((Scheme.Modules.pushforward i).obj D) 1 ≃ₗ[K]
      schemeModuleCohomology (scheme C) D 1
  have hP : P (i ≫ pi) := by
    exact PfaffianDescent.Coray.RegularPrincipalImmersion.actualIntrinsicNormal_cohomologyOneCechLinearEquiv pi i H W hW
  have hbase : i ≫ pi = toBase C := by
    change schemeQuotientMap (equationIdeal p hp) C
      (equationIdeal_le_homogeneousIdeal_of_mem hp hCp) ≫ toBase (equationIdeal p hp) = toBase C
    exact schemeQuotientMap_toBase (equationIdeal p hp) C
      (equationIdeal_le_homogeneousIdeal_of_mem hp hCp)
  change P (toBase C)
  exact Eq.mp (congrArg P hbase) hP

end PfaffianDescent.Coray
end
