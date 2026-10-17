import PfaffianDescent.CorayOriginalRegularClosedPointNormalizationLift
import AllCharacteristics.CycleDegreeAssembly

/-! Lift an ACTUAL original-curve cycle supported on its regular locus.
The SAME canonical normalization points and their own residue maps/degrees
are constructed by accepted L2. The original coefficients are retained,
including nonreduced section multiplicities; no desired degree premise.
This is not a producer of regular hyperplane support. SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory AllCharacteristics TopologicalSpace
open AllCharacteristics.HomogeneousProjective
open scoped BigOperators
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Construct an injective lift of the actual finite support and retain
every actual residue-field isomorphism and FULL original-K degree. The
explicit lifted effective cycle uses EXACTLY the original multiplicities.
Only regularity of the given support is input; no normalization point,
residue-degree-one, replacement cycle or degree certificate is supplied. -/
theorem projectiveIntersection_genericNormalization_regularSupportedCycle_exists_degree_preserving_lift
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    ∀ z : EffectiveZeroCycle X,
      (∀ P ∈ z.support, IsRegularLocalRing (X.presheaf.stalk P.1)) →
      ∃ Q : z.support → closedPoints N,
        Function.Injective Q ∧
        (∀ P : z.support,
          nu (Q P).1 = P.1.1 ∧ IsIso (nu.residueFieldMap (Q P).1) ∧
          nu.residueDegree (Q P).1 = 1 ∧
          (nu ≫ toBase I).residueDegree (Q P).1 = (toBase I).residueDegree P.1.1) ∧
        EffectiveZeroCycle.degree (nu ≫ toBase I)
            (∑ P : z.support, z P.1 • Finsupp.single (Q P) 1) =
          EffectiveZeroCycle.degree (toBase I) z := by
  classical
  intro I X N nu z hregular
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  have hlift (P : z.support) : ∃ R : closedPoints N,
      nu R.1 = P.1.1 ∧ IsIso (nu.residueFieldMap R.1) ∧
      nu.residueDegree R.1 = 1 ∧
      (nu ≫ toBase I).residueDegree R.1 = (toBase I).residueDegree P.1.1 :=
    projectiveIntersection_genericNormalization_regularClosedPoint_exists_degree_preserving_lift
      p q hp hp0 n hq hnot P.1 (hregular P.1 P.2)
  let Q : z.support → closedPoints N := fun P => Classical.choose (hlift P)
  have hmaps (P : z.support) := Classical.choose_spec (hlift P)
  have hQ : Function.Injective Q := by
    intro P R h
    apply Subtype.ext
    apply Subtype.ext
    exact (hmaps P).1.symm.trans
      ((congrArg (fun A : closedPoints N => nu A.1) h).trans (hmaps R).1)
  refine ⟨Q, hQ, hmaps, ?_⟩
  have hsingle (P : z.support) :
      EffectiveZeroCycle.degree (nu ≫ toBase I) (Finsupp.single (Q P) 1) =
        (toBase I).residueDegree P.1.1 := by
    unfold EffectiveZeroCycle.degree
    rw [Finsupp.sum_single_index (by simp)]
    simpa only [one_mul] using (hmaps P).2.2.2
  rw [← EffectiveZeroCycle.degreeLinearMap_apply, map_sum]
  simp only [map_smul, EffectiveZeroCycle.degreeLinearMap_apply, hsingle, smul_eq_mul]
  exact Finset.sum_coe_sort z.support (fun P => z P * (toBase I).residueDegree P.1)

end PfaffianDescent.Coray
