import PfaffianDescent.CorayOwnGlobalConormalRankOne
import PfaffianDescent.CoraySelectedComponentActualRegularPrincipalImmersion

/-!
The actual selected minimal component's OWN conormal, its OWN O-linear
dual normal module and canonical invertible pairing. Regular equations and
all local unit charts are constructed from the original smooth cubic and
actual minimal component; none is a premise. No genus/adjunction is claimed.
SOURCE ONLY / UNVERIFIED. Root owns all compiler and acceptance checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Actual normal data on the SAME selected component over the ORIGINAL
coefficient field. There is no CharZero, geometric-integrality, conormal
rank, pairing, vanishing, genus or numerical-intersection premise. -/
theorem selectedProjectiveMinimalComponent_actualConormalNormalModuleData
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
    let N := actualClosedImmersionConormalModule i
    schemeModuleLocallyRankOne N ∧
      schemeModuleLocallyRankOne (SchemeModuleInternalHom.dual N) ∧
      IsIso (SchemeModuleInternalHom.dualEvaluation N) := by
  let hCp : p ∈ C.toIdeal := hCmin.le (by
    rw [projectiveIntersectionIdeal_toIdeal]
    exact Ideal.subset_span (Set.mem_insert p {q}))
  let i := PfaffianDescent.homogeneousFixedCurveToCubic p hp C hCp
  letI : IsClosedImmersion i :=
    PfaffianDescent.homogeneousFixedCurveToCubic_closedImmersion p hp C hCp
  let H : PfaffianDescent.RegularPrincipalImmersion i :=
    selectedProjectiveMinimalComponent_actualRegularPrincipalImmersion
      p q hp hp0 n hq hnot C hCmin
  exact ⟨H.actualConormal_locallyRankOne, H.actualNormal_locallyRankOne,
    H.actualConormalNormalEvaluation_isIso⟩

end PfaffianDescent.Coray
end
