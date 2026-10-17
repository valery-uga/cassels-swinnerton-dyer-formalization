import PfaffianDescent.VoisinSelectedCanonicalIntrinsicIdeal

/-! A compact carrier for selected/canonical eight-point comparisons. -/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Two labeled normalized eight-point families over one field whose
ambient projective points agree after changing coefficients. -/
structure EightPointNormalizedComparison
    {K Q F : Type u} [Field K] [Field Q] [Field F]
    [Algebra K F] [Algebra Q F]
    (f : K →+* Q)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Q)) where
  x : Fin 8 → Fin 4 → F
  y : Fin 8 → Fin 4 → F
  ellx : MvPolynomial (Fin 4) K
  hellx : ellx.IsHomogeneous 1
  hex : ∀ k, ∀ q ∈ (equationIdeal p hp).toIdeal,
    q.eval₂ (algebraMap K F) (x k) = 0
  hxOne : ∀ k, (Ideal.Quotient.lift (equationIdeal p hp).toIdeal
    (eval₂Hom (algebraMap K F) (x k)) (hex k))
      (Ideal.Quotient.mk (equationIdeal p hp).toIdeal ellx) = 1
  elly : MvPolynomial (Fin 4) Q
  helly : elly.IsHomogeneous 1
  hey : ∀ k, ∀ q ∈ I.toIdeal,
    q.eval₂ (algebraMap Q F) (y k) = 0
  hyOne : ∀ k, (Ideal.Quotient.lift I.toIdeal
    (eval₂Hom (algebraMap Q F) (y k)) (hey k))
      (Ideal.Quotient.mk I.toIdeal elly) = 1
  hpoint : ∀ k,
    (linearNormalizedPointAt I (y k) (hey k)
      (Ideal.Quotient.mk I.toIdeal elly)
      (polynomial_class_mem_grading I elly helly) (hyOne k) ≫
        quotientProjMap I) ≫ ambientCoefficientMap f =
    linearNormalizedPointAt (equationIdeal p hp) (x k) (hex k)
      (Ideal.Quotient.mk (equationIdeal p hp).toIdeal ellx)
      (polynomial_class_mem_grading (equationIdeal p hp) ellx hellx)
      (hxOne k) ≫ hypersurfaceToAmbient p hp

/-- Every packaged comparison gives equality of the intrinsic ideals for
any common homogeneous cubic over the residue field. -/
theorem EightPointNormalizedComparison.intrinsicIdeal_eq
    {K Q F : Type u} [Field K] [Field Q] [Field F]
    [Algebra K F] [Algebra Q F]
    (f : K →+* Q)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Q))
    (d : EightPointNormalizedComparison f p hp I)
    (pF : MvPolynomial (Fin 4) F) (hpF : pF.IsHomogeneous 3) :
    intrinsicEightPointTripleHomogeneousIdeal pF hpF d.y =
      intrinsicEightPointTripleHomogeneousIdeal pF hpF d.x :=
  selectedCanonical_intrinsicEightPointTripleHomogeneousIdeal_eq
    f p hp pF hpF d.x d.y d.ellx d.hellx d.hex d.hxOne
    I d.elly d.helly d.hey d.hyOne d.hpoint

/-- Build the comparison package when each selected and canonical point is
identified with the same labeled marked point. -/
noncomputable def EightPointNormalizedComparison.ofMarkedFamilies
    {K Q F : Type u} [Field K] [Field Q] [Field F]
    [Algebra K F] [Algebra Q F]
    (f : K →+* Q)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) Q))
    (x y : Fin 8 → Fin 4 → F)
    (ellx : MvPolynomial (Fin 4) K)
    (hellx : ellx.IsHomogeneous 1)
    (hex : ∀ k, ∀ q ∈ (equationIdeal p hp).toIdeal,
      q.eval₂ (algebraMap K F) (x k) = 0)
    (hxOne : ∀ k, (Ideal.Quotient.lift (equationIdeal p hp).toIdeal
      (eval₂Hom (algebraMap K F) (x k)) (hex k))
        (Ideal.Quotient.mk (equationIdeal p hp).toIdeal ellx) = 1)
    (elly : MvPolynomial (Fin 4) Q)
    (helly : elly.IsHomogeneous 1)
    (hey : ∀ k, ∀ q ∈ I.toIdeal,
      q.eval₂ (algebraMap Q F) (y k) = 0)
    (hyOne : ∀ k, (Ideal.Quotient.lift I.toIdeal
      (eval₂Hom (algebraMap Q F) (y k)) (hey k))
        (Ideal.Quotient.mk I.toIdeal elly) = 1)
    (marked : Fin 8 → (Spec (.of F) ⟶
      Proj (homogeneousSubmodule (Fin 4) K)))
    (hselected : ∀ k,
      linearNormalizedPointAt (equationIdeal p hp) (x k) (hex k)
        (Ideal.Quotient.mk (equationIdeal p hp).toIdeal ellx)
        (polynomial_class_mem_grading (equationIdeal p hp) ellx hellx)
        (hxOne k) ≫ hypersurfaceToAmbient p hp = marked k)
    (hcanonical : ∀ k,
      (linearNormalizedPointAt I (y k) (hey k)
        (Ideal.Quotient.mk I.toIdeal elly)
        (polynomial_class_mem_grading I elly helly) (hyOne k) ≫
          quotientProjMap I) ≫ ambientCoefficientMap f = marked k) :
    EightPointNormalizedComparison (F := F) f p hp I where
  x := x
  y := y
  ellx := ellx
  hellx := hellx
  hex := hex
  hxOne := hxOne
  elly := elly
  helly := helly
  hey := hey
  hyOne := hyOne
  hpoint k := (hcanonical k).trans (hselected k).symm

end PfaffianDescent
