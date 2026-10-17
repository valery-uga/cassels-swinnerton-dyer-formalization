import PfaffianDescent.NormalizedProjectiveQuotientFactor
import PfaffianDescent.ProjectiveClosedPointCoordinates
import AllCharacteristics.ClosedPointAlgebra
import AllCharacteristics.ClosedImmersionCyclePushforward
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic

/-!
# An actual homogeneous minimal component through the same original closed point

This is the first genuine component construction in Coray branch B. Starting
from any actual closed point of any projective homogeneous quotient, it chooses
an actual homogeneous minimal prime inside the original normalized evaluation
kernel, constructs the same residue point on that component, and proves its
original-base degree is preserved by the canonical closed immersion.

No reducedness of the whole section, geometric integrality, regularity,
field-of-definition/orbit, degree/genus bound, or degree reduction is asserted.
SOURCE ONLY / UNVERIFIED: root alone compiles and audits.
-/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Minimality makes the prime over a homogeneous ideal equal its homogeneous
core; thus an actual prime containing I produces a genuine homogeneous minimal
prime of I below it, with no supplied component. -/
theorem homogeneousMinimalPrime_exists_le_prime
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (J : Ideal (MvPolynomial (Fin 4) K)) [J.IsPrime]
    (hIJ : I.toIdeal ≤ J) :
    ∃ C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K),
      C.toIdeal ∈ I.toIdeal.minimalPrimes ∧
      I.toIdeal ≤ C.toIdeal ∧ C.toIdeal ≤ J ∧ C.toIdeal.IsPrime := by
  obtain ⟨P, hP, hPJ⟩ := Ideal.exists_minimalPrimes_le hIJ
  let C := P.homogeneousCore (homogeneousSubmodule (Fin 4) K)
  have hCprime : C.toIdeal.IsPrime := hP.1.1.homogeneousCore
  have hIC : I.toIdeal ≤ C.toIdeal := by
    exact I.isHomogeneous.toIdeal_homogeneousCore_eq_self.symm.trans_le
      (Ideal.homogeneousCore_mono _ hP.1.2)
  have hCP : C.toIdeal ≤ P := Ideal.toIdeal_homogeneousCore_le _ _
  have hPC : P ≤ C.toIdeal := hP.2 ⟨hCprime, hIC⟩ hCP
  have hEq : C.toIdeal = P := le_antisymm hCP hPC
  refine ⟨C, ?_, hIC, hCP.trans hPJ, hCprime⟩
  rw [hEq]
  exact hP

/-- An actual ORIGINAL closed point constructs an actual homogeneous minimal
component carrying that SAME point. The canonical immersion has residue-field
isomorphism there and preserves the original K residue degree. This works for
a reducible or nonreduced whole section and does not supply geometric
integrality or regularity of either curve. -/
theorem homogeneousProjective_originalClosedPoint_exists_minimalComponent
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (P : closedPoints (scheme I)) :
    ∃ (C : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
      (hIC : I.toIdeal ≤ C.toIdeal),
      C.toIdeal ∈ I.toIdeal.minimalPrimes ∧ C.toIdeal.IsPrime ∧
      ∃ Q : closedPoints (scheme C),
        schemeQuotientMap I C hIC Q.1 = P.1 ∧
        IsIso ((schemeQuotientMap I C hIC).residueFieldMap Q.1) ∧
        (toBase C).residueDegree Q.1 = (toBase I).residueDegree P.1 := by
  classical
  let X := scheme I
  let L := X.residueField P.1
  letI := pointAlgebra (toBase I) P.1
  letI hClosed : IsClosedImmersion (X.fromSpecResidueField P.1) :=
    isClosed_singleton_iff_isClosedImmersion.mp P.2
  obtain ⟨j, g, _hgs, hgbase, hgpoint⟩ :=
    @PfaffianDescent.closed_projective_point_chart K (X.residueField P.1)
      (inferInstance : Field K) (Scheme.instFieldCarrierResidueField X P.1)
      (AllCharacteristics.pointAlgebra (toBase I) P.1) (Fin 4) I
      (X.fromSpecResidueField P.1) hClosed
      (AllCharacteristics.pointAlgebra_spec (toBase I) P.1).symm
  let x : Fin 4 → L := fun i => g (chartCoordinate I j i)
  let e : MvPolynomial (Fin 4) K →+* L := eval₂Hom (algebraMap K L) x
  let J := RingHom.ker e
  letI : J.IsPrime := RingHom.ker_isPrime e
  have hIJ : I.toIdeal ≤ J := by
    intro a ha
    have hz := congrArg g (eval₂_chartCoordinate_eq_zero_of_mem I j a ha)
    rw [hom_eval₂, hgbase, map_zero] at hz
    exact hz
  obtain ⟨C, hCmin, hIC, hCJ, hCprime⟩ :=
    homogeneousMinimalPrime_exists_le_prime I J hIJ
  have heI : ∀ a ∈ I.toIdeal, e a = 0 := fun a ha => hIJ ha
  have heC : ∀ a ∈ C.toIdeal, e a = 0 := fun a ha => hCJ ha
  let z : CoordinateRing I := coordinate I j
  have hz : z ∈ grading I 1 := coordinate_mem I j
  have hxj : x j = 1 := by
    change g (chartCoordinate I j j) = 1
    rw [chartCoordinate_self, map_one]
  have hzOneI : (Ideal.Quotient.lift I.toIdeal e heI) z = 1 := by
    change e (MvPolynomial.X j) = 1
    simpa only [e, eval₂Hom_X'] using hxj
  have hzOneC : (Ideal.Quotient.lift C.toIdeal e heC)
      (gradedQuotientMap I C hIC z) = 1 := by
    change e (MvPolynomial.X j) = 1
    simpa only [e, eval₂Hom_X'] using hxj
  let r : Spec (.of L) ⟶ scheme C := linearNormalizedPointAt C x heC
    (gradedQuotientMap I C hIC z) ((gradedQuotientMap I C hIC).map_mem hz) hzOneC
  let i := schemeQuotientMap I C hIC
  letI : IsClosedImmersion i := schemeQuotientMap_closedImmersion I C hIC
  have hfactor : r ≫ i = X.fromSpecResidueField P.1 := by
    have hquotient := linearNormalizedPointAt_comp_schemeQuotientMap I C hIC
      x heI heC z hz hzOneI hzOneC
    change r ≫ i = linearNormalizedPointAt I x heI z hz hzOneI at hquotient
    rw [hquotient]
    change Spec.map (CommRingCat.ofHom
      (linearNormalizedPointChartMapAt I x heI z hz hzOneI)) ≫ chartι I j = _
    have hmaps : linearNormalizedPointChartMapAt I x heI z hz hzOneI = g := by
      symm
      apply linearNormalizedPointChartMapAt_eq_of_base_and_coordinates
        I x heI z hz hzOneI g
      · exact hgbase
      · intro k
        rfl
    rw [hmaps]
    exact hgpoint
  letI : IsClosedImmersion (r ≫ i) := hfactor.symm ▸ inferInstance
  letI : IsClosedImmersion r := IsClosedImmersion.of_comp r i
  let b : Spec (.of L) := IsLocalRing.closedPoint L
  let Q : closedPoints (scheme C) := ⟨r b, by
    change IsClosed ({r b} : Set (scheme C))
    rw [← Set.image_singleton]
    exact r.isClosedMap _ isClosed_singleton⟩
  have hpoint : i Q.1 = P.1 := by
    change (r ≫ i) b = P.1
    rw [hfactor]
    exact Scheme.fromSpecResidueField_apply (X := X) P.1 b
  letI : IsIso (i.residueFieldMap Q.1) := isIso_residueFieldMap_of_surjectiveOnStalks i Q.1
  refine ⟨C, hIC, hCmin, hCprime, Q, hpoint, inferInstance, ?_⟩
  have hd := residueDegree_comp_of_residueFieldMap_isIso i (toBase I) Q.1
  rw [schemeQuotientMap_toBase, hpoint] at hd
  exact hd

end PfaffianDescent.Coray
