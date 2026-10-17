import PfaffianDescent.CorayProjectiveNormalizationAdditiveSingularityDegree
import PfaffianDescent.CorayProjectiveGeometricallyIntegralNormalizationDefectBound
import Lean.Elab.Tactic.Omega

/-! SOURCE ONLY / UNVERIFIED. Genuine GI boundary consequence for the SAME
original point and original K. A disjoint reduced degree-three cycle on the
ACTUAL curve is GIVEN; its construction is not concluded or assumed hiddenly.
No H0(normalization)=K or desired defect/genus inequality is a premise.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace AllCharacteristics
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem boundary_degree_add_three_contradiction
    (d g delta genus : ℕ) (hd : d = g)
    (hlower : d + 3 ≤ delta) (hupper : genus + delta ≤ g) : False := by
  omega

/-- At d=G_n, the OWN original point is regular if the ACTUAL curve has a
GIVEN disjoint reduced degree-three cycle all of whose support points are
singular. If P were singular too, D3 would give d+3<=global defect, while
actual GI constants/full-sigma cohomology give genus+global defect<=G_n.
The support cycle and its singularity are explicit natural hypotheses. -/
theorem projectiveIntersection_geometricallyIntegral_originalClosedPoint_isRegularLocalRing_at_boundary_of_singular_reducedDegreeThree
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [GeometricallyIntegral (toBase (projectiveIntersectionIdeal p q hp hq))]
    (P : closedPoints (scheme (projectiveIntersectionIdeal p q hp hq)))
    (hPdegree : (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1 =
      1 + 3 * n * (n - 1) / 2)
    (z : EffectiveZeroCycle (scheme (projectiveIntersectionIdeal p q hp hq)))
    (hred : ∀ Q ∈ z.support, z Q = 1)
    (hzdegree : EffectiveZeroCycle.degree (toBase (projectiveIntersectionIdeal p q hp hq)) z = 3)
    (hdisjoint : P ∉ z.support)
    (hzsing : ∀ Q ∈ z.support, ¬ IsRegularLocalRing
      ((scheme (projectiveIntersectionIdeal p q hp hq)).presheaf.stalk Q.1)) :
    IsRegularLocalRing ((scheme (projectiveIntersectionIdeal p q hp hq)).presheaf.stalk P.1) := by
  classical
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  let pi := toBase I
  letI : IsIntegral X := GeometricallyIntegral.isIntegral_of_subsingleton pi
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let Q := genericNormalizationQuotientSheaf X
  letI : EnoughInjectives X.Modules := sheafOfModules_enoughInjectives X.ringCatSheaf
  letI : HasExt.{u} X.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} X.Modules
  letI : EnoughInjectives N.Modules := sheafOfModules_enoughInjectives N.ringCatSheaf
  letI : HasExt.{u} N.Modules := CategoryTheory.hasExt_of_enoughInjectives.{u, u, u + 1} N.Modules
  letI : Linear K X.Modules := schemeModulesLinearOver pi
  letI : Linear K N.Modules := schemeModulesLinearOver (ν ≫ pi)
  by_contra hPsing
  have hlower := projectiveIntersection_genericNormalization_nonregular_point_add_reduced_degreeThree_le_globalDefect
    p q hp hp0 n hq hnot P z hred hzdegree hdisjoint hPsing hzsing
  have htop := (schemeModuleGlobalSectionsLinearEquivOpenTop pi Q).finrank_eq
  have hupper := projectiveIntersection_geometricallyIntegral_genericNormalization_cohomology_one_add_globalQuotient_finrank_le
    p q hp hp0 n hn hq hnot
  dsimp only [I, X, pi, N, ν, Q] at hlower htop hupper ⊢
  have hlowerTop := hlower.trans_eq htop
  exact boundary_degree_add_three_contradiction _ _ _ _ hPdegree hlowerTop hupper

/-- Without a singularity hypothesis on the given degree-three support,
the exact boundary consequence is a regular original P OR a regular support
point. It does not assert regularity of P alone or construct the support. -/
theorem projectiveIntersection_geometricallyIntegral_boundary_exists_regular_originalPoint_or_reducedDegreeThreeSupport
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n)
    (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [GeometricallyIntegral (toBase (projectiveIntersectionIdeal p q hp hq))]
    (P : closedPoints (scheme (projectiveIntersectionIdeal p q hp hq)))
    (hPdegree : (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1 =
      1 + 3 * n * (n - 1) / 2)
    (z : EffectiveZeroCycle (scheme (projectiveIntersectionIdeal p q hp hq)))
    (hred : ∀ Q ∈ z.support, z Q = 1)
    (hzdegree : EffectiveZeroCycle.degree (toBase (projectiveIntersectionIdeal p q hp hq)) z = 3)
    (hdisjoint : P ∉ z.support) :
    IsRegularLocalRing ((scheme (projectiveIntersectionIdeal p q hp hq)).presheaf.stalk P.1) ∨
      ∃ Q ∈ z.support, IsRegularLocalRing
        ((scheme (projectiveIntersectionIdeal p q hp hq)).presheaf.stalk Q.1) := by
  classical
  by_cases hP : IsRegularLocalRing
      ((scheme (projectiveIntersectionIdeal p q hp hq)).presheaf.stalk P.1)
  · exact Or.inl hP
  · apply Or.inr
    by_contra hnone
    have hzsing : ∀ Q ∈ z.support, ¬ IsRegularLocalRing
        ((scheme (projectiveIntersectionIdeal p q hp hq)).presheaf.stalk Q.1) := by
      intro Q hQ hregular
      exact hnone ⟨Q, hQ, hregular⟩
    exact hP
      (projectiveIntersection_geometricallyIntegral_originalClosedPoint_isRegularLocalRing_at_boundary_of_singular_reducedDegreeThree
        p q hp hp0 n hn hq hnot P hPdegree z hred hzdegree hdisjoint hzsing)

end PfaffianDescent.Coray
