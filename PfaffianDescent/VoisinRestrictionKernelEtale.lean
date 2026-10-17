import PfaffianDescent.VoisinRestrictionKernelUniversalFamily
import PfaffianDescent.VoisinSingularFiberEtale
import PfaffianDescent.FiniteCoordinateBaseChange

/-!
# Restriction-kernel cubics giving étale intersections

This file connects properness of the actual restriction-kernel singular
locus to the geometric endpoint needed in Voisin's degree-ten construction.
Once properness is supplied, both the generic member and, over an infinite
field, a member over the original field factor through normalized parameter
charts and have étale intersection with the two fixed cubics.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics HomogeneousProjective
open scoped TensorProduct

universe u

section

variable {K A : Type u} [Field K] [CommRing A] [Algebra K A]
  [FiniteDimensional K A]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Coordinates indexing a basis of the complete cubic restriction kernel. -/
abbrev cubicRestrictionKernelParameterIndex (x : Fin 4 → A) :=
  Fin (finrank K
    (LinearMap.ker (homogeneousSectionRestriction (K := K) x 3)))

/-- The zero homogeneous ideal defining the source projective parameter
space of the complete restriction kernel. -/
noncomputable abbrev cubicRestrictionKernelParameterIdeal (x : Fin 4 → A) :
    HomogeneousIdeal
      (homogeneousSubmodule
        (cubicRestrictionKernelParameterIndex (K := K) x) K) :=
  ⊥

/-- The projective parameter space of the complete cubic restriction kernel. -/
noncomputable abbrev cubicRestrictionKernelParameterSpace (x : Fin 4 → A) :
    Scheme.{u} :=
  scheme (cubicRestrictionKernelParameterIdeal (K := K) x)

/-- One normalized affine chart of the restriction-kernel parameter space. -/
abbrev cubicRestrictionKernelParameterChartRing
    (x : Fin 4 → A)
    (i : cubicRestrictionKernelParameterIndex (K := K) x) :=
  ChartRing (cubicRestrictionKernelParameterIdeal (K := K) x) i

/-- The coefficient-field map carried by a field-valued normalized
restriction-kernel parameter chart. -/
noncomputable def cubicRestrictionKernelSpecializedBaseMap
    {L : Type u} [Field L]
    (x : Fin 4 → A)
    (i : cubicRestrictionKernelParameterIndex (K := K) x)
    (g : cubicRestrictionKernelParameterChartRing (K := K) x i →+* L) :
    K →+* L :=
  g.comp (chartBaseMap (cubicRestrictionKernelParameterIdeal (K := K) x) i)

/-- The cubic obtained by evaluating the universal restriction-kernel member
at a field-valued normalized parameter-chart point. -/
noncomputable def cubicRestrictionKernelSpecializedCubic
    {L : Type u} [Field L]
    (x : Fin 4 → A)
    (i : cubicRestrictionKernelParameterIndex (K := K) x)
    (g : cubicRestrictionKernelParameterChartRing (K := K) x i →+* L) :
    MvPolynomial (Fin 4) L :=
  ((tripleCompleteIntersectionUniversalCubic
    (cubicRestrictionKernelFrame (K := K) x)).map
      (tripleCompleteIntersectionParameterChartCoefficientMap (K := K) i)).map g

theorem cubicRestrictionKernelSpecializedCubic_isHomogeneous
    {L : Type u} [Field L]
    (x : Fin 4 → A)
    (i : cubicRestrictionKernelParameterIndex (K := K) x)
    (g : cubicRestrictionKernelParameterChartRing (K := K) x i →+* L) :
    (cubicRestrictionKernelSpecializedCubic (K := K) x i g).IsHomogeneous 3 :=
  ((tripleCompleteIntersectionUniversalCubic_isHomogeneous
    (cubicRestrictionKernelFrame (K := K) x)).map _).map g

/-- A ground-field specialization whose chart base map is the identity is an
actual cubic equation through the original finite homogeneous datum. -/
theorem cubicRestrictionKernelSpecializedCubic_eval_eq_zero_of_baseMap_eq_id
    (x : Fin 4 → A)
    (i : cubicRestrictionKernelParameterIndex (K := K) x)
    (g : cubicRestrictionKernelParameterChartRing (K := K) x i →+* K)
    (hgbase : cubicRestrictionKernelSpecializedBaseMap (K := K) x i g =
      RingHom.id K) :
    (cubicRestrictionKernelSpecializedCubic (K := K) x i g).eval₂
      (algebraMap K A) x = 0 := by
  let f := cubicRestrictionKernelSpecializedBaseMap (K := K) x i g
  let c : cubicRestrictionKernelParameterIndex (K := K) x → K :=
    fun k => g (chartCoordinate
      (cubicRestrictionKernelParameterIdeal (K := K) x) i k)
  have hframe : ∀ j : cubicRestrictionKernelParameterIndex (K := K) x,
      ((cubicRestrictionKernelFrame (K := K) x j).1.map f).eval₂
        (algebraMap K A) x = 0 := by
    intro j
    rw [show f = RingHom.id K from hgbase, MvPolynomial.map_id]
    exact cubicRestrictionKernelFrame_vanishes (K := K) x j
  unfold cubicRestrictionKernelSpecializedCubic
  rw [MvPolynomial.map_map,
    tripleCompleteIntersectionParameterChartCoefficientMap_comp,
    tripleCompleteIntersectionUniversalCubic_map]
  simp only [eval₂_sum, eval₂_mul, eval₂_C]
  apply Finset.sum_eq_zero
  intro j hj
  rw [show g (chartCoordinate
      (cubicRestrictionKernelParameterIdeal (K := K) x) i j) = c j by rfl,
    show g.comp (chartBaseMap
      (cubicRestrictionKernelParameterIdeal (K := K) x) i) = f by rfl,
    hframe j, mul_zero]

/-- After any field-valued parameter specialization, the selected cubic
continues to vanish on the scalar extension of the original finite datum. -/
theorem cubicRestrictionKernelSpecializedCubic_eval_tensor_eq_zero
    {L : Type u} [Field L]
    (x : Fin 4 → A)
    (i : cubicRestrictionKernelParameterIndex (K := K) x)
    (g : cubicRestrictionKernelParameterChartRing (K := K) x i →+* L) :
    letI : Algebra K L :=
      (cubicRestrictionKernelSpecializedBaseMap (K := K) x i g).toAlgebra
    (cubicRestrictionKernelSpecializedCubic (K := K) x i g).eval₂
      (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A)
      (fun k => Algebra.TensorProduct.includeRight (x k)) = 0 := by
  let f := cubicRestrictionKernelSpecializedBaseMap (K := K) x i g
  letI : Algebra K L := f.toAlgebra
  let c : cubicRestrictionKernelParameterIndex (K := K) x → L :=
    fun k => g (chartCoordinate
      (cubicRestrictionKernelParameterIdeal (K := K) x) i k)
  have hframe : ∀ j : cubicRestrictionKernelParameterIndex (K := K) x,
      ((cubicRestrictionKernelFrame (K := K) x j).1.map f).eval₂
        (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A)
        (fun k => Algebra.TensorProduct.includeRight (x k)) = 0 := by
    intro j
    exact map_eval₂_tensorCoordinates_eq_zero (K := K) (L := L) x
      (cubicRestrictionKernelFrame (K := K) x j).1
      (cubicRestrictionKernelFrame_vanishes (K := K) x j)
  change (cubicRestrictionKernelSpecializedCubic (K := K) x i g).eval₂
    (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A)
    (fun k => Algebra.TensorProduct.includeRight (x k)) = 0
  unfold cubicRestrictionKernelSpecializedCubic
  rw [MvPolynomial.map_map,
    tripleCompleteIntersectionParameterChartCoefficientMap_comp,
    tripleCompleteIntersectionUniversalCubic_map]
  simp only [eval₂_sum, eval₂_mul, eval₂_C]
  apply Finset.sum_eq_zero
  intro j hj
  rw [show g (chartCoordinate
      (cubicRestrictionKernelParameterIdeal (K := K) x) i j) = c j by rfl,
    show g.comp (chartBaseMap
      (cubicRestrictionKernelParameterIdeal (K := K) x) i) = f by rfl,
    hframe j, mul_zero]

/-- The algebraic coordinate data needed by the retained finite-subscheme
chart survives any field-valued specialization of the restriction-kernel
parameter chart: the tensor coordinates generate, the two fixed equations
still vanish, and the selected cubic vanishes as well. -/
theorem cubicRestrictionKernelSpecializedFiniteCoordinateFacts
    {L : Type u} [Field L]
    (x : Fin 4 → A)
    (hgen : Function.Surjective (eval₂Hom (algebraMap K A) x))
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.eval₂ (algebraMap K A) x = 0)
    (hq : q.eval₂ (algebraMap K A) x = 0)
    (i : cubicRestrictionKernelParameterIndex (K := K) x)
    (g : cubicRestrictionKernelParameterChartRing (K := K) x i →+* L) :
    letI : Algebra K L :=
      (cubicRestrictionKernelSpecializedBaseMap (K := K) x i g).toAlgebra
    Function.Surjective
        (eval₂Hom
          (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A)
          (fun k => Algebra.TensorProduct.includeRight (x k))) ∧
      (p.map (cubicRestrictionKernelSpecializedBaseMap (K := K) x i g)).eval₂
          (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A)
          (fun k => Algebra.TensorProduct.includeRight (x k)) = 0 ∧
      (q.map (cubicRestrictionKernelSpecializedBaseMap (K := K) x i g)).eval₂
          (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A)
          (fun k => Algebra.TensorProduct.includeRight (x k)) = 0 ∧
      (cubicRestrictionKernelSpecializedCubic (K := K) x i g).eval₂
          (Algebra.TensorProduct.includeLeftRingHom : L →+* L ⊗[K] A)
          (fun k => Algebra.TensorProduct.includeRight (x k)) = 0 := by
  let f := cubicRestrictionKernelSpecializedBaseMap (K := K) x i g
  letI : Algebra K L := f.toAlgebra
  refine ⟨eval₂Hom_tensorCoordinates_surjective x hgen, ?_, ?_, ?_⟩
  · exact map_eval₂_tensorCoordinates_eq_zero (K := K) (L := L) x p hp
  · exact map_eval₂_tensorCoordinates_eq_zero (K := K) (L := L) x q hq
  · exact cubicRestrictionKernelSpecializedCubic_eval_tensor_eq_zero
      (K := K) x i g

/-- The coefficient-field homomorphism underlying the generic point of the
restriction-kernel parameter space.  Defining it from the actual composite
to `Spec K` makes the required base-compatibility statement tautological. -/
noncomputable def cubicRestrictionKernelGenericBaseMap
    (x : Fin 4 → A)
    [IsIntegral (cubicRestrictionKernelParameterSpace (K := K) x)] :
    K →+* (cubicRestrictionKernelParameterSpace (K := K) x).functionField :=
  (Spec.preimage
    ((cubicRestrictionKernelParameterSpace (K := K) x).fromSpecStalk
      (genericPoint (cubicRestrictionKernelParameterSpace (K := K) x)) ≫
      toBase (cubicRestrictionKernelParameterIdeal (K := K) x))).hom

theorem cubicRestrictionKernelGenericPoint_toBase
    (x : Fin 4 → A)
    [IsIntegral (cubicRestrictionKernelParameterSpace (K := K) x)] :
    (cubicRestrictionKernelParameterSpace (K := K) x).fromSpecStalk
        (genericPoint (cubicRestrictionKernelParameterSpace (K := K) x)) ≫
      toBase (cubicRestrictionKernelParameterIdeal (K := K) x) =
      Spec.map (CommRingCat.ofHom
        (cubicRestrictionKernelGenericBaseMap (K := K) x)) := by
  exact (Spec.map_preimage _).symm

/-- Properness of the actual restriction-kernel singular locus gives a
normalized generic parameter chart whose specialized cubic is nonzero and
whose three-cubic intersection is étale. -/
theorem
    exists_genericRestrictionKernel_parameterChart_etale_of_singularLocus_ne_univ
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (x : Fin 4 → A)
    [IsIntegral (cubicRestrictionKernelParameterSpace (K := K) x)]
    (hproper :
      tripleCompleteIntersectionRestrictionKernelSingularParameterLocus
        p q hp hq x ≠ Set.univ) :
    ∃ (i : cubicRestrictionKernelParameterIndex (K := K) x)
      (g : cubicRestrictionKernelParameterChartRing (K := K) x i →+*
        (cubicRestrictionKernelParameterSpace (K := K) x).functionField),
      cubicRestrictionKernelSpecializedBaseMap (K := K) x i g =
          cubicRestrictionKernelGenericBaseMap (K := K) x ∧
      Spec.map (CommRingCat.ofHom g) ≫
          chartι (cubicRestrictionKernelParameterIdeal (K := K) x) i =
        (cubicRestrictionKernelParameterSpace (K := K) x).fromSpecStalk
          (genericPoint (cubicRestrictionKernelParameterSpace (K := K) x)) ∧
      cubicRestrictionKernelSpecializedCubic (K := K) x i g ≠ 0 ∧
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal
        (p.map (cubicRestrictionKernelSpecializedBaseMap (K := K) x i g))
        (q.map (cubicRestrictionKernelSpecializedBaseMap (K := K) x i g))
        (cubicRestrictionKernelSpecializedCubic (K := K) x i g)
        (hp.map _)
        (hq.map _)
        (cubicRestrictionKernelSpecializedCubic_isHomogeneous
          (K := K) x i g))) := by
  let T := cubicRestrictionKernelParameterSpace (K := K) x
  let t : Spec (.of T.functionField) ⟶ T :=
    T.fromSpecStalk (genericPoint T)
  have hgood : t (IsLocalRing.closedPoint T.functionField) ∉
      tripleCompleteIntersectionUniversalSingularParameterLocus
        p q hp hq (cubicRestrictionKernelFrame (K := K) x) := by
    exact
      genericFunctionField_closedPoint_avoids_tripleCompleteIntersectionRestrictionKernelSingularParameterLocus
        p q hp hq x hproper
  obtain ⟨i, g, hgbase, hgt, hetale⟩ :=
    exists_parameterChartHom_etale_of_fieldPoint_not_mem_singularParameterLocus
      (cubicRestrictionKernelGenericBaseMap (K := K) x)
      p q hp hq (cubicRestrictionKernelFrame (K := K) x) t
      (cubicRestrictionKernelGenericPoint_toBase (K := K) x) hgood
  refine ⟨i, g, hgbase, hgt, ?_, hetale⟩
  exact tripleCompleteIntersectionUniversalCubic_parameterChart_map_ne_zero
    (cubicRestrictionKernelFrame (K := K) x)
    (cubicRestrictionKernelFrame_linearIndependent (K := K) x) i g

/-- Over an infinite field, properness of the restriction-kernel singular
locus produces a nonzero cubic over the original field, through the original
finite datum, whose intersection with the two fixed cubics is étale. -/
theorem
    exists_groundFieldRestrictionKernel_parameterChart_etale_of_singularLocus_ne_univ
    [Infinite K]
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (x : Fin 4 → A)
    (hproper :
      tripleCompleteIntersectionRestrictionKernelSingularParameterLocus
        p q hp hq x ≠ Set.univ) :
    ∃ (i : cubicRestrictionKernelParameterIndex (K := K) x)
      (g : cubicRestrictionKernelParameterChartRing (K := K) x i →+* K),
      cubicRestrictionKernelSpecializedBaseMap (K := K) x i g =
          RingHom.id K ∧
      cubicRestrictionKernelSpecializedCubic (K := K) x i g ≠ 0 ∧
      (cubicRestrictionKernelSpecializedCubic (K := K) x i g).eval₂
          (algebraMap K A) x = 0 ∧
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal
        p q
        (cubicRestrictionKernelSpecializedCubic (K := K) x i g)
        hp hq
        (cubicRestrictionKernelSpecializedCubic_isHomogeneous
          (K := K) x i g))) := by
  obtain ⟨i, g, hgbase, hetale⟩ :=
    exists_groundField_parameterChartHom_etale_of_singularParameterLocus_ne_univ
      p q hp hq (cubicRestrictionKernelFrame (K := K) x) hproper
  have hnonzero : cubicRestrictionKernelSpecializedCubic (K := K) x i g ≠ 0 :=
    tripleCompleteIntersectionUniversalCubic_parameterChart_map_ne_zero
      (cubicRestrictionKernelFrame (K := K) x)
      (cubicRestrictionKernelFrame_linearIndependent (K := K) x) i g
  have hvanish :
      (cubicRestrictionKernelSpecializedCubic (K := K) x i g).eval₂
        (algebraMap K A) x = 0 :=
    cubicRestrictionKernelSpecializedCubic_eval_eq_zero_of_baseMap_eq_id
      (K := K) x i g hgbase
  refine ⟨i, g, hgbase, hnonzero, hvanish, ?_⟩
  change Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal
    (p.map (cubicRestrictionKernelSpecializedBaseMap (K := K) x i g))
    (q.map (cubicRestrictionKernelSpecializedBaseMap (K := K) x i g))
    (cubicRestrictionKernelSpecializedCubic (K := K) x i g)
    (hp.map _)
    (hq.map _)
    (cubicRestrictionKernelSpecializedCubic_isHomogeneous
      (K := K) x i g))) at hetale
  unfold cubicRestrictionKernelSpecializedBaseMap at hetale
  rw [hgbase] at hetale
  have hIdeal :
      tripleCompleteIntersectionHomogeneousIdeal
          (p.map (RingHom.id K)) (q.map (RingHom.id K))
          (cubicRestrictionKernelSpecializedCubic (K := K) x i g)
          (hp.map _) (hq.map _)
          (cubicRestrictionKernelSpecializedCubic_isHomogeneous
            (K := K) x i g) =
        tripleCompleteIntersectionHomogeneousIdeal p q
          (cubicRestrictionKernelSpecializedCubic (K := K) x i g)
          hp hq
          (cubicRestrictionKernelSpecializedCubic_isHomogeneous
            (K := K) x i g) := by
    apply HomogeneousIdeal.ext
    simp only [tripleCompleteIntersectionHomogeneousIdeal_toIdeal,
      MvPolynomial.map_id]
  rw [hIdeal] at hetale
  exact hetale

end

end PfaffianDescent
