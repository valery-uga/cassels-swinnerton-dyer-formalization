import PfaffianDescent.CorayOwnCartierResidueSequence
import PfaffianDescent.CoraySelectedComponentActualRegularPrincipalImmersion
import PfaffianDescent.VoisinHypersurfacePositiveTwistLocal
import PfaffianDescent.VoisinCubicSurfaceVanishing
import PfaffianDescent.CubicCanonicalCohomologyTrace

/-!
Actual Cartier residue trace for the OWN selected component of the original
smooth cubic. O(-1) charts, regular equations, ideal exactness and the
Laurent-normalized surface trace are all internal. The literal quotient
tensor is retained: no dualizing identification or perfectness is asserted.
SOURCE ONLY / UNVERIFIED; root owns compiler and acceptance checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian MvPolynomial TopologicalSpace
open AllCharacteristics AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The original intrinsic O(-1) on the cubic is locally rank one by its
actual standard coordinate trivializations. Smoothness is not needed. -/
theorem cubicIntrinsicNegativeOne_locallyRankOne
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) :
    schemeModuleLocallyRankOne (sheafOfModules (grading (equationIdeal p hp)) 1) := by
  intro x
  have hx : x ∈ ⨆ j : Fin 4, quotientCoordinateOpen (equationIdeal p hp) j := by
    rw [quotientCoordinateOpen_iSup]
    trivial
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx
  exact ⟨quotientCoordinateOpen (equationIdeal p hp) j, hj,
    ⟨overFunctorIsoUnit_of_restrictIsoUnit _
      (quotientCoordinateNegativeTwistUnitIso_all (equationIdeal p hp) j 1)⟩⟩

/-- A constructed additive residue trace for the SAME selected component,
on the actual quotient of O(-1) tensor its OWN inverse ideal. All geometry
and the surface trace are derived internally; no desired duality is input. -/
def selectedProjectiveMinimalComponent_actualCubicResidueTrace
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes)
    [HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) K)).Modules]
    [HasExt.{u} (hypersurface p hp).Modules] :
    let hCp : p ∈ C.toIdeal := hCmin.le (by
      rw [projectiveIntersectionIdeal_toIdeal]
      exact Ideal.subset_span (Set.mem_insert p {q}))
    let i := PfaffianDescent.homogeneousFixedCurveToCubic p hp C hCp
    letI : IsClosedImmersion i :=
      PfaffianDescent.homogeneousFixedCurveToCubic_closedImmersion p hp C hCp
    let H := selectedProjectiveMinimalComponent_actualRegularPrincipalImmersion
      p q hp hp0 n hq hnot C hCmin
    let W := sheafOfModules (grading (equationIdeal p hp)) 1
    schemeModuleCohomology (hypersurface p hp)
      (H.actualCartierResidueSequence W).X₃ 1 →+ K := by
  let hCp : p ∈ C.toIdeal := hCmin.le (by
    rw [projectiveIntersectionIdeal_toIdeal]
    exact Ideal.subset_span (Set.mem_insert p {q}))
  let i := PfaffianDescent.homogeneousFixedCurveToCubic p hp C hCp
  letI : IsClosedImmersion i :=
    PfaffianDescent.homogeneousFixedCurveToCubic_closedImmersion p hp C hCp
  let H := selectedProjectiveMinimalComponent_actualRegularPrincipalImmersion
    p q hp hp0 n hq hnot C hCmin
  let W := sheafOfModules (grading (equationIdeal p hp)) 1
  letI : (equationIdeal p hp).toIdeal.IsPrime :=
    principalIdeal_prime_of_smooth_homogeneous_cubic p hp hp0
  letI : IsDomain (CoordinateRing (equationIdeal p hp)) := inferInstance
  let intrinsicExt : HasExt.{u} (Proj (grading (equationIdeal p hp))).Modules :=
    ‹HasExt.{u} (hypersurface p hp).Modules›
  let tau := @cubicIntrinsicNegativeOneCohomologyTwoTraceEquiv K
    (inferInstance : Field K) p hp hp0
    (inferInstance : IsDomain (CoordinateRing (equationIdeal p hp)))
    ‹HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) K)).Modules› intrinsicExt
  exact H.actualCartierResidueTrace W (cubicIntrinsicNegativeOne_locallyRankOne p hp)
    tau.toAddMonoidHom

end PfaffianDescent.Coray
end
