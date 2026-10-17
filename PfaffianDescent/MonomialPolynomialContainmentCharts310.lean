import PfaffianDescent.PolynomialContainmentQuotient295
import PfaffianDescent.PolynomialContainmentCompatibility310
import PfaffianDescent.MonomialCoefficientGluedBase300

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory
universe u

/-- Assemble the native quotient/filter equivalence at ordinary ring and
predicate parameters, before the original cyclic coefficient quotient is inserted. -/
private def nativeQuotientContainmentAlgHomEquiv310
    (R C A : Type u) [CommRing R] [CommRing C] [CommRing A]
    [Algebra R C] [Algebra R A] (I : Ideal C) (P : (C →ₐ[R] A) → Prop)
    (h : ∀ q : C →ₐ[R] A, I ≤ RingHom.ker q.toRingHom ↔ P q) :
    (C ⧸ I →ₐ[R] A) ≃ {q : C →ₐ[R] A // P q} :=
  (quotientAlgHomKernelEquiv295 R C I A).trans (Equiv.subtypeEquivRight h)

/-- The original fixed-R polynomial is unchanged by scalar specialization. -/
lemma nativePolynomialCoefficientMap_ground310
    {R C A : Type u} [CommRing R] [CommRing C] [CommRing A]
    [Algebra R C] [Algebra R A] {m : ℕ} (q : C →ₐ[R] A) (p : MvPolynomial (Fin m) R) :
    MvPolynomial.map q.toRingHom (MvPolynomial.map (algebraMap R C) p) =
      MvPolynomial.map (algebraMap R A) p := by
  have hq : q.toRingHom.comp (algebraMap R C) = algebraMap R A := by
    apply RingHom.ext
    intro r
    exact q.commutes r
  rw [MvPolynomial.map_map, hq]

variable (R : Type u) [CommRing R] (m n : ℕ)

/-- The literal original universal cyclic matrix point on the actual H chart. -/
def monomialUniversalCoefficientPoint310 (i : MonomialCoefficientChartIndex300 m n) :
    CyclicCommutingMatrixPoint283 m n i.monomials i.zeroIndex
      (A := UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex) :=
  cyclicCoefficientPoint283 (A := UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex)
    R m n i.monomials i.zeroIndex
    (AlgHom.id R (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Arbitrary coefficient points specialize the same original universal matrices. -/
lemma monomialUniversalCoefficientPoint_specialize310
    {A : Type u} [CommRing A] [Algebra R A]
    (i : MonomialCoefficientChartIndex300 m n)
    (q : UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex →ₐ[R] A) :
    cyclicMatrixPointMap287 i.monomials i.zeroIndex q.toRingHom
        (monomialUniversalCoefficientPoint310 R m n i) =
      cyclicCoefficientPoint283 R m n i.monomials i.zeroIndex q := by
  have h := cyclicCoefficientPoint_map287 (A := UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex) (E := A) i.monomials i.zeroIndex R
    (AlgHom.id R (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex)) q
  rw [AlgHom.comp_id] at h
  exact h.symm

/-- Exact finite equations291 on the original coefficient chart impose p=0
in the entire original universal quotient. -/
abbrev monomialPolynomialContainmentCoefficientIdeal310
    (p : MvPolynomial (Fin m) R) (i : MonomialCoefficientChartIndex300 m n) :
    Ideal (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex) :=
  cyclicPolynomialContainmentIdeal291 i.monomials i.zeroIndex
    (monomialUniversalCoefficientPoint310 R m n i)
    (MvPolynomial.map
      (algebraMap R (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex)) p)

lemma monomialPolynomialContainmentCoefficientIdeal_fg310
    (p : MvPolynomial (Fin m) R) (i : MonomialCoefficientChartIndex300 m n) :
    (monomialPolynomialContainmentCoefficientIdeal310 R m n p i).FG :=
  cyclicPolynomialContainmentIdeal_fg291 i.monomials i.zeroIndex _ _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Images of the original finite equations are the finite equations of the
actual specialized point, with the same original polynomial over R. -/
lemma monomialPolynomialContainmentCoefficientIdeal_image310
    {A : Type u} [CommRing A] [Algebra R A]
    (p : MvPolynomial (Fin m) R) (i : MonomialCoefficientChartIndex300 m n)
    (q : UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex →ₐ[R] A) :
    (monomialPolynomialContainmentCoefficientIdeal310 R m n p i).map q.toRingHom =
      cyclicPolynomialContainmentIdeal291 i.monomials i.zeroIndex
        (cyclicCoefficientPoint283 R m n i.monomials i.zeroIndex q)
        (MvPolynomial.map (algebraMap R A) p) := by
  have h := cyclicPolynomialContainmentIdeal_map310
    (A := UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex) (D := A)
    i.monomials i.zeroIndex (monomialUniversalCoefficientPoint310 R m n i) q.toRingHom
    (MvPolynomial.map (algebraMap R (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex)) p)
  rw [nativePolynomialCoefficientMap_ground310
    (C := UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex) (A := A) q p,
    monomialUniversalCoefficientPoint_specialize310 R m n i q] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Killing the coefficient equations is exactly containment of the original
polynomial in the actual whole ideal classified by287. -/
lemma monomialPolynomialContainmentCoefficientIdeal_le_ker_iff310
    {A : Type u} [CommRing A] [Algebra R A]
    (p : MvPolynomial (Fin m) R) (i : MonomialCoefficientChartIndex300 m n)
    (q : UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex →ₐ[R] A) :
    monomialPolynomialContainmentCoefficientIdeal310 R m n p i ≤ RingHom.ker q.toRingHom ↔
      MvPolynomial.map (algebraMap R A) p ∈
        (cyclicCoefficientWholeIdealChartEquiv287 (A := A)
          i.monomials i.zeroIndex R i.zero_eq q).val := by
  have h := cyclicPolynomialContainmentIdeal_le_ker_iff291
    i.monomials i.zeroIndex (monomialUniversalCoefficientPoint310 R m n i) q.toRingHom
    (MvPolynomial.map (algebraMap R (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex)) p)
  rw [nativePolynomialCoefficientMap_ground310
    (C := UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex) (A := A) q p,
    monomialUniversalCoefficientPoint_specialize310 R m n i q] at h
  exact h

/-- The actual closed coefficient quotient uses exactly those finite equations. -/
abbrev MonomialPolynomialContainmentCoefficientAlgebra310
    (p : MvPolynomial (Fin m) R) (i : MonomialCoefficientChartIndex300 m n) :=
  UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex ⧸
    monomialPolynomialContainmentCoefficientIdeal310 R m n p i

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Quotient maps classify actual coefficient points whose entire ideal
contains the same original polynomial. -/
def monomialPolynomialContainmentQuotientAlgHomEquiv310
    {A : Type u} [CommRing A] [Algebra R A]
    (p : MvPolynomial (Fin m) R) (i : MonomialCoefficientChartIndex300 m n) :=
  nativeQuotientContainmentAlgHomEquiv310 R
    (UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex)
    A (monomialPolynomialContainmentCoefficientIdeal310 R m n p i)
    (fun q => MvPolynomial.map (algebraMap R A) p ∈
      (cyclicCoefficientWholeIdealChartEquiv287 (A := A)
        i.monomials i.zeroIndex R i.zero_eq q).val)
    (fun q => monomialPolynomialContainmentCoefficientIdeal_le_ker_iff310 R m n p i q)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
lemma monomialPolynomialContainmentCoefficient_isClosedImmersion310
    (p : MvPolynomial (Fin m) R) (i : MonomialCoefficientChartIndex300 m n) :
    IsClosedImmersion (Spec.map (CommRingCat.ofHom
      (R := UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex)
      (S := MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)
      (Ideal.Quotient.mk (monomialPolynomialContainmentCoefficientIdeal310 R m n p i)))) :=
  IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom
      (R := UniversalCyclicCoefficientAlgebra282 R m n i.monomials i.zeroIndex)
      (S := MonomialPolynomialContainmentCoefficientAlgebra310 R m n p i)
      (Ideal.Quotient.mk (monomialPolynomialContainmentCoefficientIdeal310 R m n p i)))
    Ideal.Quotient.mk_surjective

end PfaffianDescent
end
