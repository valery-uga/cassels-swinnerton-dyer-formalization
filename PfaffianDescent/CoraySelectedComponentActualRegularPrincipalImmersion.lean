import PfaffianDescent.CoraySelectedComponentNativeCubicChartHeight
import PfaffianDescent.CorayRegularLocalHeightOnePrimePrincipal

/-!
# Actual selected component is a regular principal immersion on the smooth cubic

Every local equation is derived in the OWN native cubic-chart localization.
No chart height, generator, factoriality or Cartier conclusion is an input.
This does not prove adjunction, Hodge, a genus bound or a Riemann--Roch bound.
SOURCE ONLY / UNVERIFIED; root owns all compiler and audit checks.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- An actual homogeneous minimal component of the selected p/q curve has
a genuine regular principal immersion in the original smooth cubic surface.
The p-membership proof is constructed from the original minimal-prime input. -/
noncomputable def selectedProjectiveMinimalComponent_actualRegularPrincipalImmersion
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (hCmin : C.toIdeal ∈ (projectiveIntersectionIdeal p q hp hq).toIdeal.minimalPrimes) :
    let hCp : p ∈ C.toIdeal := hCmin.le (by
      rw [projectiveIntersectionIdeal_toIdeal]
      exact Ideal.subset_span (Set.mem_insert p {q}))
    PfaffianDescent.RegularPrincipalImmersion
      (PfaffianDescent.homogeneousFixedCurveToCubic p hp C hCp) := by
  let hCp : p ∈ C.toIdeal := hCmin.le (by
    rw [projectiveIntersectionIdeal_toIdeal]
    exact Ideal.subset_span (Set.mem_insert p {q}))
  have hkernel := selectedProjectiveMinimalComponent_nativeCubicChartKernel_top_or_heightOne
    p q hp hp0 n hq hnot C hCmin hCp
  apply PfaffianDescent.smoothCubic_fixedCurve_regularPrincipalImmersion_of_closedCurvePointsPrincipal
    p hp hp0 C hCp hkernel
  intro j Q _ hPQ
  let P := PfaffianDescent.fixedCurveCubicChartKernel p hp C hCp j
  rcases hkernel j with htop | ⟨hprime, hheight⟩
  · have hQtop : Q = ⊤ := top_unique (htop ▸ hPQ)
    exact False.elim ((show Q.IsPrime from inferInstance).ne_top hQtop)
  · letI : P.IsPrime := hprime
    obtain ⟨z, _, hz⟩ := smoothCubic_chartHeightOnePrime_localized_regularPrincipal
      p hp hp0 j P Q hPQ hheight
    rw [hz]
    infer_instance

end PfaffianDescent.Coray
