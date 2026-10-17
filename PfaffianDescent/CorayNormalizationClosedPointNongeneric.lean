import PfaffianDescent.CorayProjectiveNormalizationStalkDimension
import AllCharacteristics.ClosedPolynomialDimension
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.Algebra.Field.Equiv
import Mathlib.AlgebraicGeometry.Morphisms.Integral

/-! Actual closed points of the SAME two-equation projective normalization
are nongeneric. The conclusion follows from genuine polynomial height and
the actual normalization map; no dimension, nongenericity or DVR certificate.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Two equations in actual affine three-space cannot have a field quotient:
a maximal polynomial ideal has height three, while this ideal has two generators. -/
theorem affineThreeSpace_pairQuotient_not_isField
    (f g : MvPolynomial (Fin 3) K) :
    ¬ IsField (MvPolynomial (Fin 3) K ⧸ Ideal.span ({f, g} : Set _)) := by
  classical
  let I := Ideal.span ({f, g} : Set (MvPolynomial (Fin 3) K))
  intro hfield
  letI : I.IsMaximal := Ideal.Quotient.maximal_of_isField I hfield
  have hheight : I.height = 3 := by
    simpa using maximalIdeal_height_mvPolynomial I
  have hminimal : I ∈ I.minimalPrimes := by
    rw [Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton I
  have hminimal' : I ∈ (Ideal.span
      (({f, g} : Finset (MvPolynomial (Fin 3) K)) : Set _)).minimalPrimes := by
    simpa [I] using hminimal
  have hle := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hminimal'
  have hcard : ({f, g} : Finset (MvPolynomial (Fin 3) K)).card ≤ 2 :=
    (Finset.card_insert_le f {g}).trans (by simp)
  have hleTwo : I.height ≤ 2 := hle.trans (by exact_mod_cast hcard)
  rw [hheight] at hleTwo
  norm_num at hleTwo

/-- The SAME nonempty integral two-equation projective scheme has more than
one point. A hypothetical singleton makes its actual nonempty coordinate
chart a field, contradicting the literal two-equation affine presentation. -/
theorem projectiveIntersection_not_subsingleton
    (p q : MvPolynomial (Fin 4) K) {a b : ℕ}
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b)
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    ¬ Subsingleton (scheme (projectiveIntersectionIdeal p q hp hq)) := by
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  intro hsingle
  letI : Subsingleton X := hsingle
  obtain ⟨j, z, _hz⟩ := exists_coordinate_chart I (genericPoint X)
  let C := Spec (.of (ChartRing I j))
  letI : Nonempty C := ⟨z⟩
  letI : IsIntegral C := isIntegral_of_isOpenImmersion (chartι I j)
  letI : Subsingleton C := ⟨fun s t =>
    (chartι I j).isOpenEmbedding.injective (Subsingleton.elim _ _)⟩
  have hsections : IsField Γ(C, ⊤) := isField_of_isIntegral_of_subsingleton C
  have hchart : IsField (ChartRing I j) :=
    MulEquiv.isField hsections
      (Scheme.ΓSpecIso (.of (ChartRing I j))).symm.commRingCatIsoToRingEquiv.toMulEquiv
  have hpair : IsField
      (affineCurveRing (normalizedAffineEquation j p) (normalizedAffineEquation j q)) :=
    MulEquiv.isField hchart
      (projectiveIntersection_chartRingEquiv p q hp hq j).symm.toMulEquiv
  exact affineThreeSpace_pairQuotient_not_isField _ _ hpair

/-- The ACTUAL normalization of the actual integral generic-point map is
surjective. Its integral map has closed range containing the original generic
point via the literal toNormalization/fromNormalization composition. -/
theorem integralGenericNormalization_fromNormalization_surjective
    (X : Scheme.{u}) [IsIntegral X] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    Surjective (X.fromSpecStalk (genericPoint X)).fromNormalization := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let f := X.fromSpecStalk (genericPoint X)
  let ν := f.fromNormalization
  let z := IsLocalRing.closedPoint (X.presheaf.stalk (genericPoint X))
  have hgeneric : genericPoint X ∈ Set.range ν := by
    refine ⟨f.toNormalization z, ?_⟩
    change (f.toNormalization ≫ f.fromNormalization) z = genericPoint X
    rw [Scheme.Hom.toNormalization_fromNormalization]
    exact Scheme.fromSpecStalk_closedPoint
  have hclosed : IsClosed (Set.range ν) := ν.isClosedMap.isClosed_range
  have hall : Set.univ ⊆ Set.range ν := by
    rw [← genericPoint_spec X]
    exact closure_minimal (Set.singleton_subset_iff.mpr hgeneric) hclosed
  exact ⟨fun x => hall (Set.mem_univ x)⟩

/-- EVERY actual closed point of the SAME canonical normalization is
nongeneric. A closed generic point would make the integral normalization
a singleton, hence its actual surjective image a singleton, contradicting
the internally proved actual two-equation chart obstruction. -/
theorem projectiveIntersection_genericNormalization_closedPoint_ne_generic
    (p q : MvPolynomial (Fin 4) K) {a b : ℕ}
    (hp : p.IsHomogeneous a) (hq : q.IsHomogeneous b)
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let X := scheme (projectiveIntersectionIdeal p q hp hq)
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    ∀ P : closedPoints N, P.1 ≠ genericPoint N := by
  dsimp only
  let X := scheme (projectiveIntersectionIdeal p q hp hq)
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let ν := (X.fromSpecStalk (genericPoint X)).fromNormalization
  intro P hP
  have hclosed : IsClosed ({genericPoint N} : Set N) := by simpa [hP] using P.2
  have hall : (Set.univ : Set N) = {genericPoint N} :=
    (genericPoint_spec N).symm.trans hclosed.closure_eq
  letI : Subsingleton N := ⟨fun s t => by
    have hs : s = genericPoint N := Set.mem_singleton_iff.mp (hall ▸ Set.mem_univ s)
    have ht : t = genericPoint N := Set.mem_singleton_iff.mp (hall ▸ Set.mem_univ t)
    exact hs.trans ht.symm⟩
  have hsurj : Function.Surjective ν :=
    (integralGenericNormalization_fromNormalization_surjective X).surj
  letI : Subsingleton X := ⟨fun s t => by
    obtain ⟨s', rfl⟩ := hsurj s
    obtain ⟨t', rfl⟩ := hsurj t
    exact congrArg ν (Subsingleton.elim s' t')⟩
  exact projectiveIntersection_not_subsingleton p q hp hq inferInstance

end PfaffianDescent.Coray
