import PfaffianDescent.CorayNormalizationDistinctSingularityContribution
import PfaffianDescent.CorayOriginalRegularClosedPointNormalizationLift
import PfaffianDescent.CorayGlobalNormalizationSupportClosed
import PfaffianDescent.CorayProjectiveGlobalNormalizationSupport
import PfaffianDescent.SchemeModuleGlobalSectionsTop
import AllCharacteristics.CycleDegrees

/-! SOURCE ONLY / UNVERIFIED. Actual projective D3: the SAME quotient gets
one distinct native stalk contribution per original singular closed point.
The reduced degree-three boundary support is disjoint from the original P.
No GI, H0(normalization)=K, desired inequality, or section existence is assumed.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace AllCharacteristics
open AllCharacteristics.HomogeneousProjective
open scoped BigOperators
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- On the actual integral selected intersection, a finite set of distinct
singular original points contributes the SUM of its full original degrees.
Actual support finiteness/closedness, local dimension, finite normalization,
actual native stalk comparison and actual global germs are all derived. -/
theorem projectiveIntersection_genericNormalization_distinct_nonregular_residueSum_le_globalDefect
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (D : Finset (closedPoints (scheme (projectiveIntersectionIdeal p q hp hq))))
    (hsing : ∀ P ∈ D, ¬ IsRegularLocalRing
      ((scheme (projectiveIntersectionIdeal p q hp hq)).presheaf.stalk P.1)) :
    ∑ P ∈ D, (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1 ≤
      Module.finrank K (SchemeModuleGlobalSectionsOver
        (toBase (projectiveIntersectionIdeal p q hp hq))
        (genericNormalizationQuotientSheaf (scheme (projectiveIntersectionIdeal p q hp hq)))) := by
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  let pi := toBase I
  let Q := genericNormalizationQuotientSheaf X
  have hfinite := projectiveIntersection_genericNormalizationQuotient_stalkSupport_finite
    p q hp hp0 n hq hnot
  have hclosed := projectiveIntersection_genericNormalizationQuotient_stalkSupport_isClosed
    p q hp hp0 n hq hnot
  have hdim (P : closedPoints X) : ringKrullDim (X.presheaf.stalk P.1) ≤ 1 :=
    projectiveIntersection_original_stalk_ringKrullDim_le_one p q hp hp0 n hq hnot P.1
  have hsum := genericNormalizationQuotient_distinct_nonregular_residueSum_le_globalDefect
    X pi hfinite hclosed hdim D hsing
  exact hsum.trans (schemeModuleGlobalSectionsLinearEquivOpenTop pi Q).finrank_eq.symm.le

/-- Distinctness of P and the reduced cycle's support makes the degree
contributions ADDITIVE. The degree-three datum is an actual reduced cycle,
not three individually repeated lower bounds for one global vector space. -/
theorem projectiveIntersection_genericNormalization_nonregular_point_add_reduced_degreeThree_le_globalDefect
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))]
    (P : closedPoints (scheme (projectiveIntersectionIdeal p q hp hq)))
    (z : EffectiveZeroCycle (scheme (projectiveIntersectionIdeal p q hp hq)))
    (hred : ∀ Q ∈ z.support, z Q = 1)
    (hdegree : EffectiveZeroCycle.degree (toBase (projectiveIntersectionIdeal p q hp hq)) z = 3)
    (hdisjoint : P ∉ z.support)
    (hPsing : ¬ IsRegularLocalRing
      ((scheme (projectiveIntersectionIdeal p q hp hq)).presheaf.stalk P.1))
    (hzsing : ∀ Q ∈ z.support, ¬ IsRegularLocalRing
      ((scheme (projectiveIntersectionIdeal p q hp hq)).presheaf.stalk Q.1)) :
    (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree P.1 + 3 ≤
      Module.finrank K (SchemeModuleGlobalSectionsOver
        (toBase (projectiveIntersectionIdeal p q hp hq))
        (genericNormalizationQuotientSheaf (scheme (projectiveIntersectionIdeal p q hp hq)))) := by
  classical
  have hsum := projectiveIntersection_genericNormalization_distinct_nonregular_residueSum_le_globalDefect
    p q hp hp0 n hq hnot (insert P z.support) (by
      intro Q hQ
      rcases Finset.mem_insert.mp hQ with hQP | hQz
      · subst Q
        exact hPsing
      · exact hzsing Q hQz)
  have hzdegree : ∑ Q ∈ z.support,
      (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree Q.1 = 3 := by
    calc
      ∑ Q ∈ z.support, (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree Q.1 =
          ∑ Q ∈ z.support, z Q *
            (toBase (projectiveIntersectionIdeal p q hp hq)).residueDegree Q.1 := by
        apply Finset.sum_congr rfl
        intro Q hQ
        rw [hred Q hQ, one_mul]
      _ = EffectiveZeroCycle.degree (toBase (projectiveIntersectionIdeal p q hp hq)) z := rfl
      _ = 3 := hdegree
  rw [Finset.sum_insert hdisjoint, hzdegree] at hsum
  exact hsum

end PfaffianDescent.Coray
