import PfaffianDescent.VoisinProjectiveLinearSystem
import PfaffianDescent.VoisinVeryAmpleQuadraticSections

/-!
# Generic length-eight fixed-component contradictions

This file joins the generic finite-incidence theorem for eight points to the
two numerical branches in Voisin's proof of `leeffective`.  Once a proposed
fixed or moving divisor system is represented by a homogeneous polynomial
submodule and its universal incidence contains the generic configuration,
the incidence theorem supplies at least nine sections.  The meeting branch
then contradicts the proper fixed-plus-moving dimension bound, while the
disjoint branch contradicts two-point separation by quadrics.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics AllCharacteristics.UniversalHomogeneous
open HomogeneousProjective

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A nonempty subset of a finite index set that is invariant under every
permutation contains every index.  This is the finite combinatorial part of
Voisin's symmetric-group argument: once one generic marked point lies on a
fixed component, permutation symmetry forces every marked point to lie there. -/
theorem fixedSupport_eq_univ_of_perm_invariant
    {n : ℕ} (S : Set (Fin n))
    (hS : ∀ e : Equiv.Perm (Fin n), e '' S = S)
    (hne : S.Nonempty) : S = Set.univ := by
  apply Set.eq_univ_of_forall
  intro j
  obtain ⟨i, hi⟩ := hne
  let e : Equiv.Perm (Fin n) := Equiv.swap i j
  have hej : e i = j := by
    simp [e]
  rw [← hS e]
  exact ⟨i, hi, hej⟩

/-- Pointwise-equivariant form of the preceding symmetric-support lemma.
In applications a fixed-component predicate is naturally transported along
each reindexing map; this version avoids first packaging that transport as an
equality of image sets. -/
theorem fixedSupport_eq_univ_of_perm_pointwise_invariant
    {n : ℕ} (S : Set (Fin n))
    (hS : ∀ e : Equiv.Perm (Fin n), ∀ i, i ∈ S ↔ e i ∈ S)
    (hne : S.Nonempty) : S = Set.univ := by
  apply Set.eq_univ_of_forall
  intro j
  obtain ⟨i, hi⟩ := hne
  have h := (hS (Equiv.swap i j) i).mp hi
  simpa using h

/-- The generic unordered length-eight configuration lies in the image of
the universal incidence family of an independently framed homogeneous
system.  This packages the scheme-theoretic formulation of “some member of
the system contains all eight generic points.” -/
noncomputable def GenericEightConfigurationInHomogeneousFrameIncidence
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (d : ℕ) {m n : ℕ}
    (e : Fin m ≃ Monomials (Fin 4) d)
    (q : Fin n → homogeneousSubmodule (Fin 4) K d)
    (hqliq : LinearIndependent K q)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme] : Prop :=
  (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
    (hypersurfaceToBase cubic hcubic) 8).toScheme.fromSpecStalk
    (genericPoint
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme)
    (IsLocalRing.closedPoint
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme.functionField) ∈
    projectiveConfigurationQuotientMap (grading (equationIdeal cubic hcubic))
      (hypersurfaceToBase cubic hcubic) 8 ''
      projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
        (orderedFamilyConfigurationOver (hypersurfaceToBase cubic hcubic) 8).hom
        (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
        (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
          (grading (equationIdeal cubic hcubic)) _
          (hypersurfaceToBase cubic hcubic) hsep 8
          (hypersurfaceToAmbient cubic hcubic) i)
        (homogeneousFrameToParameters d e q hqliq)

/-- A framed system containing the generic eight-point configuration has at
least nine sections. -/
theorem nine_le_finrank_of_genericEightConfigurationInHomogeneousFrameIncidence
    {K : Type u} [Field K] [IsAlgClosed K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (hcubic_ne : cubic ≠ 0)
    (hcubic_prime : (Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    {d m n : ℕ} (hd : 0 < d)
    (W : Submodule K (MvPolynomial (Fin 4) K)) [FiniteDimensional K W]
    (hhom : ∀ z ∈ W, z.IsHomogeneous d)
    (hseparate : ∀ z ∈ W,
      z ∈ Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K)) → z = 0)
    (qW : Fin n → W) (q : Fin n → homogeneousSubmodule (Fin 4) K d)
    (hq : ∀ j, (qW j : MvPolynomial (Fin 4) K) = (q j).1)
    (hqli : LinearIndependent K qW) (hqliq : LinearIndependent K q)
    (hn : Module.finrank K W = n)
    (e : Fin m ≃ Monomials (Fin 4) d)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hlft : LocallyOfFiniteType (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme]
    (hinc : GenericEightConfigurationInHomogeneousFrameIncidence
      cubic hcubic d e q hqliq) :
    9 ≤ Module.finrank K W := by
  apply nine_le_finrank_of_generic_eight_cubicConfigurationQuotientHomogeneousFrameFiniteIncidence
    cubic hcubic hcubic_ne hcubic_prime hd W hhom hseparate
      qW q hq hqli hqliq hn e
  simpa only [GenericEightConfigurationInHomogeneousFrameIncidence] using hinc

/-- A homogeneous system of at most eight sections cannot contain the generic
length-eight configuration.  This is the incidence-exclusion form of the
genericity step in Voisin's fixed-component argument: once a proposed fixed
or moving system is packaged as a homogeneous frame, its common-curve witness
contradicts this theorem directly. -/
theorem not_genericEightConfigurationInHomogeneousFrameIncidence_of_finrank_le_eight
    {K : Type u} [Field K] [IsAlgClosed K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (hcubic_ne : cubic ≠ 0)
    (hcubic_prime : (Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    {d m n : ℕ} (hd : 0 < d)
    (W : Submodule K (MvPolynomial (Fin 4) K)) [FiniteDimensional K W]
    (hhom : ∀ z ∈ W, z.IsHomogeneous d)
    (hseparate : ∀ z ∈ W,
      z ∈ Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K)) → z = 0)
    (hdim : Module.finrank K W ≤ 8)
    (qW : Fin n → W) (q : Fin n → homogeneousSubmodule (Fin 4) K d)
    (hq : ∀ j, (qW j : MvPolynomial (Fin 4) K) = (q j).1)
    (hqli : LinearIndependent K qW) (hqliq : LinearIndependent K q)
    (hn : Module.finrank K W = n)
    (e : Fin m ≃ Monomials (Fin 4) d)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hlft : LocallyOfFiniteType (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme] :
    ¬ GenericEightConfigurationInHomogeneousFrameIncidence
      cubic hcubic d e q hqliq := by
  intro hinc
  have hnine : 9 ≤ Module.finrank K W :=
    nine_le_finrank_of_genericEightConfigurationInHomogeneousFrameIncidence
      cubic hcubic hcubic_ne hcubic_prime hd W hhom hseparate
        qW q hq hqli hqliq hn e hinc
  omega

/-- Meeting branch of Voisin's fixed-component argument.  Generic incidence
gives nine fixed-part sections; a moving pencil and properness of the
fixed-plus-moving family then exceed the ten quadratic sections of a cubic
surface. -/
theorem cubicSurface_degreeEight_fixedComponent_meets_genericIncidence_contradiction
    {K : Type u} [Field K] [IsAlgClosed K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (hcubic_ne : cubic ≠ 0)
    (hcubic_prime : (Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    {d m n : ℕ} (hd : 0 < d)
    (fixed : Submodule K (MvPolynomial (Fin 4) K)) [FiniteDimensional K fixed]
    (hhom : ∀ z ∈ fixed, z.IsHomogeneous d)
    (hseparate : ∀ z ∈ fixed,
      z ∈ Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K)) → z = 0)
    (qW : Fin n → fixed) (q : Fin n → homogeneousSubmodule (Fin 4) K d)
    (hq : ∀ j, (qW j : MvPolynomial (Fin 4) K) = (q j).1)
    (hqli : LinearIndependent K qW) (hqliq : LinearIndependent K q)
    (hn : Module.finrank K fixed = n)
    (e : Fin m ≃ Monomials (Fin 4) d)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hlft : LocallyOfFiniteType (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme]
    (hinc : GenericEightConfigurationInHomogeneousFrameIncidence
      cubic hcubic d e q hqliq)
    (movingDim : ℕ) (hpencil : 2 ≤ movingDim)
    (hproper : Module.finrank K fixed + movingDim ≤
      Module.finrank K (grading (equationIdeal cubic hcubic) 2)) : False := by
  have hgeneric : 9 ≤ Module.finrank K fixed :=
    nine_le_finrank_of_genericEightConfigurationInHomogeneousFrameIncidence
      cubic hcubic hcubic_ne hcubic_prime hd fixed hhom hseparate
        qW q hq hqli hqliq hn e hinc
  exact voisin_degreeEight_fixedComponent_meets_numerical_contradiction
    cubic hcubic hcubic_ne (Module.finrank K fixed) movingDim
      hgeneric hpencil hproper

/-- Disjoint branch of Voisin's fixed-component argument.  Generic incidence
forces at least nine moving quadratic sections, whereas vanishing at two
distinct points of the fixed curve bounds the same system by eight. -/
theorem cubicSurface_degreeEight_fixedComponent_disjoint_genericIncidence_contradiction
    {K : Type u} [Field K] [IsAlgClosed K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (hcubic_ne : cubic ≠ 0)
    (hcubic_prime : (Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    (moving : Submodule K (MvPolynomial (Fin 4) K))
    [FiniteDimensional K moving]
    (hhom : ∀ z ∈ moving, z.IsHomogeneous 2)
    (hseparate : ∀ z ∈ moving,
      z ∈ Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K)) → z = 0)
    {m n : ℕ}
    (qW : Fin n → moving) (q : Fin n → homogeneousSubmodule (Fin 4) K 2)
    (hq : ∀ j, (qW j : MvPolynomial (Fin 4) K) = (q j).1)
    (hqli : LinearIndependent K qW) (hqliq : LinearIndependent K q)
    (hn : Module.finrank K moving = n)
    (e : Fin m ≃ Monomials (Fin 4) 2)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hlft : LocallyOfFiniteType (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme]
    (hinc : GenericEightConfigurationInHomogeneousFrameIncidence
      cubic hcubic 2 e q hqliq)
    (x y : cubicSurfaceAffinePoints cubic)
    (hdir : ∀ a : K, y.1 ≠ a • x.1)
    (hvan : ∀ r : moving,
      MvPolynomial.aeval x.1 r.1 = 0 ∧
      MvPolynomial.aeval y.1 r.1 = 0) : False := by
  have hnine : 9 ≤ Module.finrank K moving :=
    nine_le_finrank_of_genericEightConfigurationInHomogeneousFrameIncidence
      cubic hcubic hcubic_ne hcubic_prime (by decide) moving hhom hseparate
        qW q hq hqli hqliq hn e hinc
  have height : Module.finrank K moving ≤ 8 :=
    homogeneousQuadraticPolynomialSubmodule_finrank_le_eight_of_pointwise_vanishing
      cubic x y hdir moving hhom hvan
  omega

end PfaffianDescent
