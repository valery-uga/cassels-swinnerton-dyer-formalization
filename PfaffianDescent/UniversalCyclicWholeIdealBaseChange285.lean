import PfaffianDescent.UniversalCyclicMatrixQuotient282
import PfaffianDescent.CyclicMatrixActionKernelBaseChange285
import Mathlib.RingTheory.FinitePresentation

noncomputable section
namespace PfaffianDescent
open MvPolynomial
universe u v
variable (R : Type u) [CommRing R] (m n : ℕ)
variable (B : Fin n → (Fin m →₀ ℕ)) (k : Fin n)

private def actualInferredUniversalGenerators285 :=
  cyclicActionKernel_eq_generatorIdeal285 (R := UniversalCyclicCoefficientAlgebra282 R m n B k) (m := m) (n := n)
    (universalCyclicPolynomialAction282 R m n B k)
    B k (universalCyclicPolynomialAction_monomial282 R m n B k)

private def actualOriginalUniversalGeneratorsProp285 : Prop :=
    universalCyclicWholeAmbientIdeal282 R m n B k =
      cyclicActionGeneratorIdeal285 (R := UniversalCyclicCoefficientAlgebra282 R m n B k) (m := m) (n := n)
        (universalCyclicPolynomialAction282 R m n B k) B k

private def actualOriginalUniversalGeneratorsConversion285 :
    actualOriginalUniversalGeneratorsProp285 R m n B k :=
  actualInferredUniversalGenerators285 R m n B k

lemma universalCyclicWholeAmbientIdeal_generators285 :
    universalCyclicWholeAmbientIdeal282 R m n B k =
      cyclicActionGeneratorIdeal285 (R := UniversalCyclicCoefficientAlgebra282 R m n B k) (m := m) (n := n)
        (universalCyclicPolynomialAction282 R m n B k) B k :=
  actualOriginalUniversalGeneratorsConversion285 R m n B k

private def actualInferredUniversalFinite285 :=
  cyclicActionKernel_fg285 (R := UniversalCyclicCoefficientAlgebra282 R m n B k) (m := m) (n := n)
    (universalCyclicPolynomialAction282 R m n B k)
    B k (universalCyclicPolynomialAction_monomial282 R m n B k)

private def actualOriginalUniversalFiniteProp285 : Prop :=
    (universalCyclicWholeAmbientIdeal282 R m n B k).FG

private def actualOriginalUniversalFiniteConversion285 :
    actualOriginalUniversalFiniteProp285 R m n B k :=
  actualInferredUniversalFinite285 R m n B k

lemma universalCyclicWholeAmbientIdeal_fg285 :
    (universalCyclicWholeAmbientIdeal282 R m n B k).FG :=
  actualOriginalUniversalFiniteConversion285 R m n B k

private theorem nativeCyclicKernelFinitePresentation285
    {A : Type u} [CommRing A] {m n : ℕ}
    (rho : MvPolynomial (Fin m) A →ₐ[A] Module.End A (Fin n → A))
    (h : (RingHom.ker rho.toRingHom).FG) :
    Algebra.FinitePresentation A (MvPolynomial (Fin m) A ⧸ RingHom.ker rho.toRingHom) :=
  Algebra.FinitePresentation.quotient h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def actualInferredUniversalPresentation285 :=
  nativeCyclicKernelFinitePresentation285
    (A := UniversalCyclicCoefficientAlgebra282 R m n B k) (m := m) (n := n)
    (universalCyclicPolynomialAction282 R m n B k)
    (actualInferredUniversalFinite285 R m n B k)

private def actualOriginalUniversalPresentationProp285 : Prop :=
    Algebra.FinitePresentation (UniversalCyclicCoefficientAlgebra282 R m n B k)
      (UniversalCyclicWholeAmbientQuotient282 R m n B k)

private def actualOriginalUniversalPresentationConversion285 :
    actualOriginalUniversalPresentationProp285 R m n B k :=
  actualInferredUniversalPresentation285 R m n B k

lemma universalCyclicWholeAmbientQuotient_finitePresentation285 :
    Algebra.FinitePresentation (UniversalCyclicCoefficientAlgebra282 R m n B k)
      (UniversalCyclicWholeAmbientQuotient282 R m n B k) :=
  actualOriginalUniversalPresentationConversion285 R m n B k

private def actualInferredUniversalBaseChange285
    {S : Type v} [CommRing S]
    (f : UniversalCyclicCoefficientAlgebra282 R m n B k →+* S) :=
  commutingMatrixActionKernel_mapped285
    (R := UniversalCyclicCoefficientAlgebra282 R m n B k) (S := S) (m := m) (n := n)
    (universalCyclicMultiplicationMatrix282 R m n B k)
    (universalCyclicMultiplicationMatrix_commute282 R m n B k) f B k
    (universalCyclicPolynomialAction_monomial282 R m n B k)

private def actualOriginalUniversalBaseChangeProp285
    {S : Type v} [CommRing S]
    (f : UniversalCyclicCoefficientAlgebra282 R m n B k →+* S) : Prop :=
    (universalCyclicWholeAmbientIdeal282 R m n B k).map (MvPolynomial.map f) =
      RingHom.ker (commutingMatrixPolynomialAction282
        (fun i => (universalCyclicMultiplicationMatrix282 R m n B k i).map f)
        (commutingMatrix_tuple_map_commute285
          (universalCyclicMultiplicationMatrix282 R m n B k)
          (universalCyclicMultiplicationMatrix_commute282 R m n B k) f)).toRingHom

private def actualOriginalUniversalBaseChangeConversion285
    {S : Type v} [CommRing S]
    (f : UniversalCyclicCoefficientAlgebra282 R m n B k →+* S) :
    actualOriginalUniversalBaseChangeProp285 R m n B k f :=
  actualInferredUniversalBaseChange285 R m n B k f

lemma universalCyclicWholeAmbientIdeal_baseChange285
    {S : Type v} [CommRing S]
    (f : UniversalCyclicCoefficientAlgebra282 R m n B k →+* S) :
    (universalCyclicWholeAmbientIdeal282 R m n B k).map (MvPolynomial.map f) =
      RingHom.ker (commutingMatrixPolynomialAction282
        (fun i => (universalCyclicMultiplicationMatrix282 R m n B k i).map f)
        (commutingMatrix_tuple_map_commute285
          (universalCyclicMultiplicationMatrix282 R m n B k)
          (universalCyclicMultiplicationMatrix_commute282 R m n B k) f)).toRingHom :=
  actualOriginalUniversalBaseChangeConversion285 R m n B k f

end PfaffianDescent
