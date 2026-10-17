import PfaffianDescent.VoisinProjectiveLinearSystem
import PfaffianDescent.FiniteSchemeAlgebra
import PfaffianDescent.FiniteSubschemeCompleteIntersection
import PfaffianDescent.ProjectiveChartUniversalIncidence
import PfaffianDescent.HomogeneousFrameCoordinateParameter
import AllCharacteristics.GenericPointDominance
import AllCharacteristics.ProjectiveConfigurationGenericSplitFiber
import AllCharacteristics.VoisinGenericCubicConfiguration
import AllCharacteristics.OrderedConfigurationFieldPoints

/-!
# Ordered lifts of the generic eight-point configuration

The unordered generic configuration is the object used by Voisin's
specialization argument.  Quadratic evaluation is easiest to inspect after
passing to an ordered splitting field.  This file supplies that passage while
retaining the already proved avoidance of finite projective-incidence loci.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-- There are ten quadratic monomials in four variables. -/
theorem quadraticMonomials_card :
    Fintype.card (Monomials (Fin 4) 2) = 10 := by
  have hdim : Module.finrank ℚ
      (MvPolynomial.homogeneousSubmodule (Fin 4) ℚ 2) =
      Fintype.card (Monomials (Fin 4) 2) := by
    rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
    exact Module.finrank_eq_card_basis
      (MvPolynomial.basisRestrictSupport ℚ {a | a.degree = 2})
  rw [← hdim, four_variable_homogeneous_finrank]
  decide

/-- The first eight elements of a fixed enumeration of the ten quadratic
monomials.  Unlike a field-dependent finite basis, these exponent vectors
are unchanged by coefficient extension. -/
noncomputable def quadraticEightMonomialEmbedding :
    Fin 8 ↪ Monomials (Fin 4) 2 :=
  let e : Fin (Fintype.card (Monomials (Fin 4) 2)) ≃
      Monomials (Fin 4) 2 := (Fintype.equivFin _).symm
  let j : Fin 8 ↪ Fin (Fintype.card (Monomials (Fin 4) 2)) :=
    ⟨fun i ↦ Fin.cast quadraticMonomials_card.symm
        (Fin.castLE (by decide : 8 ≤ 10) i), by
      intro i k hik
      exact Fin.castLE_injective _ (Fin.cast_injective _ hik)⟩
  j.trans e.toEmbedding

/-- A fixed eight-element monomial frame of homogeneous quadrics in four
variables.  The full quadratic space has dimension ten. -/
noncomputable def quadraticEightFrame (K : Type u) [Field K] :
    Fin 8 → homogeneousSubmodule (Fin 4) K 2 :=
  fun i ↦ ⟨MvPolynomial.monomial (quadraticEightMonomialEmbedding i).1 1,
    MvPolynomial.isHomogeneous_monomial 1
      (quadraticEightMonomialEmbedding i).2⟩

/-- The explicit quadratic frame commutes with every extension of its
coefficient field. -/
theorem quadraticEightFrame_map
    {K L : Type u} [Field K] [Field L] (f : K →+* L) (i : Fin 8) :
    MvPolynomial.map f (quadraticEightFrame K i).1 =
      (quadraticEightFrame L i).1 := by
  simp [quadraticEightFrame]

/-- Linear combinations in the explicit quadratic frame commute with
extension of the coefficient field. -/
theorem quadraticEightFrameCombination_map
    {K L : Type u} [Field K] [Field L] (f : K →+* L) (c : Fin 8 → K) :
    MvPolynomial.map f
        (homogeneousFrameMap 2 (quadraticEightFrame K) c).1 =
      (homogeneousFrameMap 2 (quadraticEightFrame L) (fun i ↦ f (c i))).1 := by
  simp only [homogeneousFrameMap, Fintype.linearCombination_apply]
  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul,
    map_mul, MvPolynomial.map_C, quadraticEightFrame_map]

/-- The fixed eight-quadratic frame is linearly independent. -/
theorem quadraticEightFrame_linearIndependent (K : Type u) [Field K] :
    LinearIndependent K (quadraticEightFrame K) := by
  apply LinearIndependent.of_comp
    (Submodule.subtype (homogeneousSubmodule (Fin 4) K 2))
  let e : Fin 8 ↪ (Fin 4 →₀ ℕ) :=
    ⟨fun i ↦ (quadraticEightMonomialEmbedding i).1, by
      intro i j hij
      apply quadraticEightMonomialEmbedding.injective
      exact Subtype.ext hij⟩
  have h := (MvPolynomial.basisMonomials (Fin 4) K).linearIndependent.comp
    e e.injective
  change LinearIndependent K
    (fun i ↦ MvPolynomial.monomial (e i) (1 : K))
  exact h

/-- The same fixed frame, forgetting the proof of homogeneity. -/
noncomputable def quadraticEightPolynomialFrame (K : Type u) [Field K] :
    Fin 8 → MvPolynomial (Fin 4) K :=
  fun i ↦ (quadraticEightFrame K i).1

/-- Forgetting homogeneity preserves independence of the fixed frame. -/
theorem quadraticEightPolynomialFrame_linearIndependent
    (K : Type u) [Field K] :
    LinearIndependent K (quadraticEightPolynomialFrame K) := by
  have h := (quadraticEightFrame_linearIndependent K).map'
    (Submodule.subtype (homogeneousSubmodule (Fin 4) K 2))
    (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  change LinearIndependent K
    (fun i ↦ ((quadraticEightFrame K i :
      homogeneousSubmodule (Fin 4) K 2) : MvPolynomial (Fin 4) K))
  exact h

/-- The fixed eight-dimensional polynomial subsystem used to test generic
quadratic evaluation. -/
noncomputable def quadraticEightPolynomialSubmodule
    (K : Type u) [Field K] : Submodule K (MvPolynomial (Fin 4) K) :=
  Submodule.span K (Set.range (quadraticEightPolynomialFrame K))

/-- The fixed quadratic subsystem has dimension exactly eight. -/
theorem quadraticEightPolynomialSubmodule_finrank
    (K : Type u) [Field K] :
    finrank K (quadraticEightPolynomialSubmodule K) = 8 := by
  rw [quadraticEightPolynomialSubmodule,
    finrank_span_eq_card (quadraticEightPolynomialFrame_linearIndependent K)]
  decide

/-- Every member of the fixed subsystem is homogeneous of degree two. -/
theorem quadraticEightPolynomialSubmodule_isHomogeneous
    (K : Type u) [Field K] (q : MvPolynomial (Fin 4) K)
    (hq : q ∈ quadraticEightPolynomialSubmodule K) :
    q.IsHomogeneous 2 := by
  rw [quadraticEightPolynomialSubmodule] at hq
  refine Submodule.span_induction
    (p := fun q _ ↦ q.IsHomogeneous 2) ?_
    (isHomogeneous_zero (Fin 4) K 2) ?_ ?_ hq
  · intro x hx
    obtain ⟨i, rfl⟩ := hx
    exact (quadraticEightFrame K i).2
  · intro x y _ _ hx hy
    exact hx.add hy
  · intro a x _ hx
    rw [MvPolynomial.smul_eq_C_mul]
    exact hx.C_mul a

/-- If the canonical eight-dimensional frame is detected injectively by a
length-eight coordinate algebra, then restriction of all quadrics to that
algebra is surjective.  This is the equal-dimension step following the
projective-incidence argument. -/
theorem quadraticSectionRestriction_surjective_of_quadraticEightFrame_injective
    {K A : Type u} [Field K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A]
    (x : Fin 4 → A) (hA : finrank K A = 8)
    (hinj : Function.Injective
      ((homogeneousSectionRestriction (K := K) x 2).comp
        (homogeneousFrameMap 2 (quadraticEightFrame K)))) :
    Function.Surjective (homogeneousSectionRestriction (K := K) x 2) := by
  let g := (homogeneousSectionRestriction (K := K) x 2).comp
    (homogeneousFrameMap 2 (quadraticEightFrame K))
  have hdim : finrank K (Fin 8 → K) = finrank K A := by
    rw [Module.finrank_pi_fintype, Module.finrank_self, hA]
    simp
  have hsurj : Function.Surjective g :=
    (LinearEquiv.ofInjectiveOfFinrankEq g hinj hdim).surjective
  intro a
  obtain ⟨c, hc⟩ := hsurj a
  exact ⟨homogeneousFrameMap 2 (quadraticEightFrame K) c, hc⟩

/-- Detection of the canonical quadratic frame at eight geometric points
implies injectivity of its restriction to the original finite coordinate
algebra.  The geometric points are expressed as algebra maps into one field,
so this is the algebraic bridge from split point evaluations back to the
unsplit length-eight algebra. -/
theorem quadraticEightFrame_restriction_injective_of_embedding_evaluations
    {K A L : Type u} [Field K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A] [Field L] [Algebra K L]
    (x : Fin 4 → A) (φ : Fin 8 → A →ₐ[K] L)
    (hdetect : ∀ c : Fin 8 → K,
      (∀ i, MvPolynomial.eval₂ (algebraMap K L)
        (fun j ↦ φ i (x j))
        (homogeneousFrameMap 2 (quadraticEightFrame K) c).1 = 0) →
      c = 0) :
    Function.Injective
      ((homogeneousSectionRestriction (K := K) x 2).comp
        (homogeneousFrameMap 2 (quadraticEightFrame K))) := by
  let g := (homogeneousSectionRestriction (K := K) x 2).comp
    (homogeneousFrameMap 2 (quadraticEightFrame K))
  intro c d hcd
  apply sub_eq_zero.mp
  apply hdetect (c - d)
  intro i
  let q := homogeneousFrameMap 2 (quadraticEightFrame K) (c - d)
  have hgzero : g (c - d) = 0 := by
    rw [map_sub, hcd, sub_self]
  have heval := MvPolynomial.hom_eval₂ q.1 (algebraMap K A)
    (φ i).toRingHom x
  have hcomp : (φ i).toRingHom.comp (algebraMap K A) = algebraMap K L := by
    ext a
    exact (φ i).commutes a
  rw [hcomp] at heval
  calc
    MvPolynomial.eval₂ (algebraMap K L) (fun j ↦ φ i (x j)) q.1 =
        φ i (MvPolynomial.eval₂ (algebraMap K A) x q.1) := heval.symm
    _ = φ i (g (c - d)) := by rfl
    _ = 0 := by rw [hgzero, map_zero]

/-- If the eight split geometric evaluations detect every ground-field
combination of the canonical frame, then all quadratic sections restrict
surjectively to the original rank-eight coordinate algebra. -/
theorem quadraticSectionRestriction_surjective_of_embedding_evaluations
    {K A L : Type u} [Field K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A] [Field L] [Algebra K L]
    (x : Fin 4 → A) (hA : finrank K A = 8)
    (φ : Fin 8 → A →ₐ[K] L)
    (hdetect : ∀ c : Fin 8 → K,
      (∀ i, MvPolynomial.eval₂ (algebraMap K L)
        (fun j ↦ φ i (x j))
        (homogeneousFrameMap 2 (quadraticEightFrame K) c).1 = 0) →
      c = 0) :
    Function.Surjective (homogeneousSectionRestriction (K := K) x 2) := by
  apply quadraticSectionRestriction_surjective_of_quadraticEightFrame_injective x hA
  exact quadraticEightFrame_restriction_injective_of_embedding_evaluations
    x φ hdetect

/-- A degree-two homogeneous polynomial cannot be a nonzero multiple of a
degree-three homogeneous equation.  This version applies directly to the
fixed eight-dimensional subsystem below. -/
theorem homogeneousQuadratic_separate_cubic_equation
    {K : Type u} [Field K]
    (cubic q : MvPolynomial (Fin 4) K)
    (hcubic : cubic.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (hmem : q ∈ Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K))) :
    q = 0 := by
  have hspanPair :
      q ∈ Ideal.span ({cubic, (0 : MvPolynomial (Fin 4) K)} : Set _) := by
    simpa using hmem
  obtain ⟨a, ha⟩ := homogeneous_mem_span_succ_degree_pair_eq_smul
    (d := 2) hcubic (MvPolynomial.isHomogeneous_zero (Fin 4) K 2) hq hspanPair
  rw [ha, smul_zero]

/-- The generic unordered length-eight configuration admits an ordered lift
over a residue-field extension, and every such chosen lift retains avoidance
of a fixed homogeneous frame of dimension at most eight.

This is the carrier-to-field-valued bridge needed to turn the existing
projective-incidence theorem into injectivity of evaluation on an
eight-dimensional quadratic subsystem. -/
theorem exists_orderedPointOver_genericEight_avoids_homogeneousFrameFiniteIncidence
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
    let O := (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left
    let Q := (projectiveConfigurationQuotientOpen
      (grading (equationIdeal cubic hcubic))
      (hypersurfaceToBase cubic hcubic) 8).toScheme
    let π := projectiveConfigurationQuotientMap
      (grading (equationIdeal cubic hcubic))
      (hypersurfaceToBase cubic hcubic) 8
    let η := Q.fromSpecStalk (genericPoint Q)
      (IsLocalRing.closedPoint Q.functionField)
    let bad := projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
      (orderedFamilyConfigurationOver
        (hypersurfaceToBase cubic hcubic) 8).hom
      (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
      (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
        (grading (equationIdeal cubic hcubic)) _
        (hypersurfaceToBase cubic hcubic) hsep 8
        (hypersurfaceToAmbient cubic hcubic) i)
      (homogeneousFrameToParameters d e q hqliq)
    ∃ z : O, π z = η ∧ z ∉ bad := by
  dsimp only
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase cubic hcubic) 8).left
  let Q := (projectiveConfigurationQuotientOpen
    (grading (equationIdeal cubic hcubic))
    (hypersurfaceToBase cubic hcubic) 8).toScheme
  let π := projectiveConfigurationQuotientMap
    (grading (equationIdeal cubic hcubic))
    (hypersurfaceToBase cubic hcubic) 8
  let η := Q.fromSpecStalk (genericPoint Q)
    (IsLocalRing.closedPoint Q.functionField)
  let bad := projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) d
    (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).hom
    (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)))
    (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
      (grading (equationIdeal cubic hcubic)) _
      (hypersurfaceToBase cubic hcubic) hsep 8
      (hypersurfaceToAmbient cubic hcubic) i)
    (homogeneousFrameToParameters d e q hqliq)
  have hav : η ∉ π '' bad := by
    exact
      genericFunctionField_closedPoint_avoids_eight_cubicConfigurationQuotientHomogeneousFrameFiniteIncidence_of_submodule_evaluation
        cubic hcubic hcubic_ne hcubic_prime hd W hhom hseparate hdim
          qW q hq hqli hqliq hn e
  letI : Surjective π := by
    dsimp only [π]
    exact surjective_projectiveConfigurationQuotientMap
      (grading (equationIdeal cubic hcubic))
      (hypersurfaceToBase cubic hcubic) 8
  obtain ⟨z, hz⟩ := π.surjective η
  refine ⟨z, hz, ?_⟩
  intro hr
  apply hav
  exact ⟨z, hr, hz⟩

/-- The ordered lift of the generic eight-point configuration avoids the
finite incidence locus of the canonical eight-dimensional subsystem of
quadrics.  This removes all auxiliary choices from the incidence statement
used in the quadratic-evaluation argument. -/
theorem exists_orderedPointOver_genericEight_avoids_quadraticEightFiniteIncidence
    {K : Type u} [Field K] [IsAlgClosed K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (hcubic_ne : cubic ≠ 0)
    (hcubic_prime : (Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme] :
    let O := (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left
    let Q := (projectiveConfigurationQuotientOpen
      (grading (equationIdeal cubic hcubic))
      (hypersurfaceToBase cubic hcubic) 8).toScheme
    let π := projectiveConfigurationQuotientMap
      (grading (equationIdeal cubic hcubic))
      (hypersurfaceToBase cubic hcubic) 8
    let η := Q.fromSpecStalk (genericPoint Q)
      (IsLocalRing.closedPoint Q.functionField)
    let e : Fin (Fintype.card (Monomials (Fin 4) 2)) ≃ Monomials (Fin 4) 2 :=
      (Fintype.equivFin _).symm
    let bad := projectiveUniversalFiniteIncidenceBadLocus K (Fin 4) 2
      (orderedFamilyConfigurationOver
        (hypersurfaceToBase cubic hcubic) 8).hom
      (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 8) K)))
      (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
        (grading (equationIdeal cubic hcubic)) _
        (hypersurfaceToBase cubic hcubic) hsep 8
        (hypersurfaceToAmbient cubic hcubic) i)
      (homogeneousFrameToParameters 2 e (quadraticEightFrame K)
        (quadraticEightFrame_linearIndependent K))
    ∃ z : O, π z = η ∧ z ∉ bad := by
  dsimp only
  let W := quadraticEightPolynomialSubmodule K
  let qW : Fin 8 → W := fun i ↦
    ⟨quadraticEightPolynomialFrame K i,
      Submodule.subset_span (Set.mem_range_self i)⟩
  have hqW : ∀ i, (qW i : MvPolynomial (Fin 4) K) =
      (quadraticEightFrame K i).1 := by
    intro i
    rfl
  have hqWli : LinearIndependent K qW := by
    apply LinearIndependent.of_comp W.subtype
    change LinearIndependent K (quadraticEightPolynomialFrame K)
    exact quadraticEightPolynomialFrame_linearIndependent K
  letI : FiniteDimensional K W := Module.Finite.of_fg
    (Submodule.fg_span (Set.finite_range (quadraticEightPolynomialFrame K)))
  apply
    exists_orderedPointOver_genericEight_avoids_homogeneousFrameFiniteIncidence
      cubic hcubic hcubic_ne hcubic_prime (d := 2) (by decide) W
      (quadraticEightPolynomialSubmodule_isHomogeneous K)
      (fun z hz hmem ↦ homogeneousQuadratic_separate_cubic_equation cubic z hcubic
        (quadraticEightPolynomialSubmodule_isHomogeneous K z hz) hmem)
      (by rw [quadraticEightPolynomialSubmodule_finrank])
      qW (quadraticEightFrame K) hqW hqWli
      (quadraticEightFrame_linearIndependent K)
      (quadraticEightPolynomialSubmodule_finrank K)
      ((Fintype.equivFin (Monomials (Fin 4) 2)).symm)

/-- The residue field of an ordered lift over the generic unordered
configuration receives the configuration function field. -/
noncomputable def quadraticOrderedLiftFunctionFieldHom
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme]
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left)
    (hz : projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8 z =
      ((projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme))
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme.functionField)) :
    (projectiveConfigurationQuotientOpen
      (grading (equationIdeal cubic hcubic))
      (hypersurfaceToBase cubic hcubic) 8).toScheme.functionField →+*
      (orderedFamilyConfigurationOver
        (hypersurfaceToBase cubic hcubic) 8).left.residueField z := by
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase cubic hcubic) 8).left
  let Q := (projectiveConfigurationQuotientOpen
    (grading (equationIdeal cubic hcubic))
    (hypersurfaceToBase cubic hcubic) 8).toScheme
  let π := projectiveConfigurationQuotientMap
    (grading (equationIdeal cubic hcubic))
    (hypersurfaceToBase cubic hcubic) 8
  let r := O.fromSpecResidueField z
  have hc : (r ≫ π) (IsLocalRing.closedPoint (O.residueField z)) =
      genericPoint Q := by
    change π (r (IsLocalRing.closedPoint (O.residueField z))) = genericPoint Q
    have hr : r (IsLocalRing.closedPoint (O.residueField z)) = z := by
      exact Scheme.fromSpecResidueField_apply z _
    exact (congrArg π hr).trans (hz.trans Scheme.fromSpecStalk_closedPoint)
  exact Q.genericFieldPointRingHom (r ≫ π) hc

/-- The induced function-field homomorphism factors the ordered residue point
through the canonical generic-point morphism. -/
lemma quadraticOrderedLiftFunctionFieldHom_spec
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme]
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left)
    (hz : projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8 z =
      ((projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme))
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme.functionField)) :
    Spec.map (CommRingCat.ofHom
        (quadraticOrderedLiftFunctionFieldHom cubic hcubic z hz)) ≫
      (projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme) =
      (orderedFamilyConfigurationOver
          (hypersurfaceToBase cubic hcubic) 8).left.fromSpecResidueField z ≫
        projectiveConfigurationQuotientMap
          (grading (equationIdeal cubic hcubic))
          (hypersurfaceToBase cubic hcubic) 8 := by
  unfold quadraticOrderedLiftFunctionFieldHom
  apply Scheme.genericFieldPointRingHom_spec

/-- The `i`th label of an ordered generic lift gives a point of the actual
generic rank-eight finite scheme over the ordered residue field. -/
noncomputable def quadraticOrderedLiftComponentPoint
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme]
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left)
    (hz : projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8 z =
      ((projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme))
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme.functionField))
    (i : Fin 8) :
    Spec (.of ((orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left.residueField z)) ⟶
      (projectiveConfigurationGenericFiniteSubscheme
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).val.subscheme := by
  letI : IsSeparated
      (show Proj (grading (equationIdeal cubic hcubic)) ⟶ Spec (.of K) from
        toBase (equationIdeal cubic hcubic)) := hsep
  letI : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (toBase (equationIdeal cubic hcubic)) 8).toScheme := hint
  exact projectiveConfigurationOrderedGenericComponentPoint
    (grading (equationIdeal cubic hcubic))
    (toBase (equationIdeal cubic hcubic)) 8
    ((orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left.fromSpecResidueField z)
    (quadraticOrderedLiftFunctionFieldHom cubic hcubic z hz)
    (quadraticOrderedLiftFunctionFieldHom_spec cubic hcubic z hz) i

/-- The actual generic finite-scheme component has the ambient projective
point prescribed by its label in the ordered configuration. -/
lemma quadraticOrderedLiftComponentPoint_toAmbientProjective
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 8)]
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left)
    (hz : projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8 z =
      ((projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme))
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme.functionField))
    (i : Fin 8) :
    quadraticOrderedLiftComponentPoint cubic hcubic z hz i ≫
      cubicConfigurationGenericAmbientMap cubic hcubic 8 =
    (orderedFamilyConfigurationOver
        (hypersurfaceToBase cubic hcubic) 8).left.fromSpecResidueField z ≫
      @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
        (grading (equationIdeal cubic hcubic)) _
        (hypersurfaceToBase cubic hcubic) hsep 8
        (hypersurfaceToAmbient cubic hcubic) i := by
  letI : IsSeparated
      (show Proj (grading (equationIdeal cubic hcubic)) ⟶ Spec (.of K) from
        toBase (equationIdeal cubic hcubic)) := hsep
  letI : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (toBase (equationIdeal cubic hcubic)) 8).toScheme := hint
  have hpoint := projectiveConfigurationOrderedGenericComponentPoint_toAmbientProjective
    (grading (equationIdeal cubic hcubic)) (toBase (equationIdeal cubic hcubic)) 8
    ((orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left.fromSpecResidueField z)
    (quadraticOrderedLiftFunctionFieldHom cubic hcubic z hz)
    (quadraticOrderedLiftFunctionFieldHom_spec cubic hcubic z hz) i
  have hpoint' := congrArg
    (fun t ↦ t ≫ hypersurfaceToAmbient cubic hcubic) hpoint
  unfold quadraticOrderedLiftComponentPoint
  exact hpoint'

/-- The labeled component point transported to the coefficient-changed
generic cubic used by the residual construction.  Its source field is the
same ordered residue field, while its target is now the finite subscheme on
the literal coefficient-changed cubic equation. -/
noncomputable def quadraticOrderedLiftCoefficientChangedComponentPoint
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 8)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 8).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap cubic hcubic 8 ≫
        cubicConfigurationToBase cubic hcubic 8)
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left)
    (hz : projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8 z =
      ((projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme))
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme.functionField))
    (i : Fin 8) :
    Spec (.of ((orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left.residueField z)) ⟶
      (cubicConfigurationGenericFiniteSubscheme
        cubic hcubic 8 a ha).val.subscheme :=
  quadraticOrderedLiftComponentPoint cubic hcubic z hz i ≫
    (cubicConfigurationGenericFiniteSubschemeIsoGeneric
      cubic hcubic 8 a ha).inv

/-- Transporting a labeled component to the coefficient-changed cubic does
not alter its morphism to the original ambient projective space. -/
lemma quadraticOrderedLiftCoefficientChangedComponentPoint_toGenericAmbient
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 8)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 8).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap cubic hcubic 8 ≫
        cubicConfigurationToBase cubic hcubic 8)
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left)
    (hz : projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8 z =
      ((projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme))
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme.functionField))
    (i : Fin 8) :
    quadraticOrderedLiftCoefficientChangedComponentPoint
        cubic hcubic a ha z hz i ≫
      cubicConfigurationCoefficientChangedAmbientMap cubic hcubic 8 a ha =
    quadraticOrderedLiftComponentPoint cubic hcubic z hz i ≫
      cubicConfigurationGenericAmbientMap cubic hcubic 8 := by
  have hambient :=
    @cubicConfigurationGenericFiniteSubschemeIsoGeneric_inv_ambientMap
      K _ cubic 3 hcubic 8 hbase hsep a ha
  unfold quadraticOrderedLiftCoefficientChangedComponentPoint
  calc
    (quadraticOrderedLiftComponentPoint cubic hcubic z hz i ≫
          (cubicConfigurationGenericFiniteSubschemeIsoGeneric
            cubic hcubic 8 a ha).inv) ≫
        cubicConfigurationCoefficientChangedAmbientMap cubic hcubic 8 a ha =
      quadraticOrderedLiftComponentPoint cubic hcubic z hz i ≫
        ((cubicConfigurationGenericFiniteSubschemeIsoGeneric
            cubic hcubic 8 a ha).inv ≫
          cubicConfigurationCoefficientChangedAmbientMap
            cubic hcubic 8 a ha) :=
      Category.assoc _ _ _
    _ = _ := congrArg
      (fun t ↦ quadraticOrderedLiftComponentPoint cubic hcubic z hz i ≫ t)
      hambient

/-- The transported component on the literal coefficient-changed cubic is
the marked ambient projective point of the ordered generic configuration. -/
lemma quadraticOrderedLiftCoefficientChangedComponentPoint_toAmbientProjective
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 8)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 8).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap cubic hcubic 8 ≫
        cubicConfigurationToBase cubic hcubic 8)
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left)
    (hz : projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8 z =
      ((projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme))
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme.functionField))
    (i : Fin 8) :
    quadraticOrderedLiftCoefficientChangedComponentPoint
        cubic hcubic a ha z hz i ≫
      cubicConfigurationCoefficientChangedAmbientMap cubic hcubic 8 a ha =
    (orderedFamilyConfigurationOver
        (hypersurfaceToBase cubic hcubic) 8).left.fromSpecResidueField z ≫
      @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
        (grading (equationIdeal cubic hcubic)) _
        (hypersurfaceToBase cubic hcubic) hsep 8
        (hypersurfaceToAmbient cubic hcubic) i := by
  calc
    _ = quadraticOrderedLiftComponentPoint cubic hcubic z hz i ≫
        cubicConfigurationGenericAmbientMap cubic hcubic 8 :=
      quadraticOrderedLiftCoefficientChangedComponentPoint_toGenericAmbient
        cubic hcubic a ha z hz i
    _ = _ := quadraticOrderedLiftComponentPoint_toAmbientProjective
      cubic hcubic z hz i

/-- The transported components remain pairwise distinct: their ambient
images are the distinct labels of the ordered configuration. -/
theorem quadraticOrderedLiftCoefficientChangedComponentPoint_injective
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 8)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 8).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap cubic hcubic 8 ≫
        cubicConfigurationToBase cubic hcubic 8)
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left)
    (hz : projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8 z =
      ((projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme))
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme.functionField)) :
    Function.Injective (fun i : Fin 8 =>
      quadraticOrderedLiftCoefficientChangedComponentPoint
        cubic hcubic a ha z hz i) := by
  intro i j hij
  have h := congrArg
    (fun q => q ≫ cubicConfigurationCoefficientChangedAmbientMap
      cubic hcubic 8 a ha) hij
  rw [quadraticOrderedLiftCoefficientChangedComponentPoint_toAmbientProjective
      cubic hcubic a ha z hz i,
    quadraticOrderedLiftCoefficientChangedComponentPoint_toAmbientProjective
      cubic hcubic a ha z hz j] at h
  have hmark := orderedConfigurationFieldPoint_coordinates_comp_injective
    (hypersurfaceToBase cubic hcubic) 8
    (hypersurfaceToAmbient cubic hcubic)
    ((orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left.fromSpecResidueField z)
  unfold orderedConfigurationProjectivePoint at h
  exact hmark h

/-- Each labeled component point lies over the function-field embedding
associated to the ordered lift. -/
lemma quadraticOrderedLiftComponentPoint_toBase
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme]
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left)
    (hz : projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8 z =
      ((projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme))
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme.functionField))
    (i : Fin 8) :
    quadraticOrderedLiftComponentPoint cubic hcubic z hz i ≫
        (projectiveConfigurationGenericFiniteSubscheme
          (grading (equationIdeal cubic hcubic))
          (hypersurfaceToBase cubic hcubic) 8).val.subschemeι ≫
        pullback.snd
          (pullback.snd (hypersurfaceToBase cubic hcubic)
            (projectiveConfigurationQuotientToBase
              (grading (equationIdeal cubic hcubic))
              (hypersurfaceToBase cubic hcubic) 8))
          ((projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme.fromSpecStalk
              (genericPoint (projectiveConfigurationQuotientOpen
                (grading (equationIdeal cubic hcubic))
                (hypersurfaceToBase cubic hcubic) 8).toScheme)) =
      Spec.map (CommRingCat.ofHom
        (quadraticOrderedLiftFunctionFieldHom cubic hcubic z hz)) := by
  letI : IsSeparated
      (show Proj (grading (equationIdeal cubic hcubic)) ⟶ Spec (.of K) from
        toBase (equationIdeal cubic hcubic)) := hsep
  letI : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (toBase (equationIdeal cubic hcubic)) 8).toScheme := hint
  unfold quadraticOrderedLiftComponentPoint
  exact projectiveConfigurationOrderedGenericComponentPoint_toBase
    (grading (equationIdeal cubic hcubic))
    (toBase (equationIdeal cubic hcubic)) 8
    ((orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left.fromSpecResidueField z)
    (quadraticOrderedLiftFunctionFieldHom cubic hcubic z hz)
    (quadraticOrderedLiftFunctionFieldHom_spec cubic hcubic z hz) i

/-- A labeled component transported to the coefficient-changed cubic remains
over the same configuration-function-field embedding. -/
lemma quadraticOrderedLiftCoefficientChangedComponentPoint_toBase
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 8)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 8).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap cubic hcubic 8 ≫
        cubicConfigurationToBase cubic hcubic 8)
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left)
    (hz : projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8 z =
      ((projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme))
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme.functionField))
    (i : Fin 8) :
    quadraticOrderedLiftCoefficientChangedComponentPoint
        cubic hcubic a ha z hz i ≫
      cubicConfigurationCoefficientChangedBaseMap cubic hcubic 8 a ha =
    Spec.map (CommRingCat.ofHom
      (quadraticOrderedLiftFunctionFieldHom cubic hcubic z hz)) := by
  have htransport :=
    @cubicConfigurationGenericFiniteSubschemeIsoGeneric_inv_toBase
      K _ cubic 3 hcubic 8 hbase hsep a ha
  have hpoint := quadraticOrderedLiftComponentPoint_toBase
    cubic hcubic z hz i
  have hpoint' :
      quadraticOrderedLiftComponentPoint cubic hcubic z hz i ≫
        cubicConfigurationGenericFiniteBaseMap cubic hcubic 8 =
      Spec.map (CommRingCat.ofHom
        (quadraticOrderedLiftFunctionFieldHom cubic hcubic z hz)) := hpoint
  unfold quadraticOrderedLiftCoefficientChangedComponentPoint
  have htransported :
      (quadraticOrderedLiftComponentPoint cubic hcubic z hz i ≫
          (cubicConfigurationGenericFiniteSubschemeIsoGeneric
            cubic hcubic 8 a ha).inv) ≫
        cubicConfigurationCoefficientChangedBaseMap cubic hcubic 8 a ha =
      quadraticOrderedLiftComponentPoint cubic hcubic z hz i ≫
        cubicConfigurationGenericFiniteBaseMap cubic hcubic 8 := by
    calc
      (quadraticOrderedLiftComponentPoint cubic hcubic z hz i ≫
            (cubicConfigurationGenericFiniteSubschemeIsoGeneric
              cubic hcubic 8 a ha).inv) ≫
          cubicConfigurationCoefficientChangedBaseMap cubic hcubic 8 a ha =
        quadraticOrderedLiftComponentPoint cubic hcubic z hz i ≫
          ((cubicConfigurationGenericFiniteSubschemeIsoGeneric
              cubic hcubic 8 a ha).inv ≫
            cubicConfigurationCoefficientChangedBaseMap
              cubic hcubic 8 a ha) := Category.assoc _ _ _
      _ = _ := congrArg
        (fun t ↦ quadraticOrderedLiftComponentPoint cubic hcubic z hz i ≫ t)
        htransport
  exact htransported.trans hpoint'

/-- Pullback of global functions along the `i`th labeled component gives an
algebra embedding candidate from the generic rank-eight coordinate algebra
to the ordered lift's residue field. -/
noncomputable def quadraticOrderedLiftComponentAlgHom
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme]
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left)
    (hz : projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8 z =
      ((projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme))
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme.functionField))
    (i : Fin 8) :
    let f := toBase (equationIdeal cubic hcubic)
    letI : IsSeparated f := hsep
    let Q := (projectiveConfigurationQuotientOpen
      (grading (equationIdeal cubic hcubic)) f 8).toScheme
    letI : IsIntegral Q := hint
    let O := (orderedFamilyConfigurationOver f 8).left
    let D := projectiveConfigurationGenericFiniteSubscheme
      (grading (equationIdeal cubic hcubic)) f 8
    let pD := D.val.subschemeι ≫
      pullback.snd
        (pullback.snd f (projectiveConfigurationQuotientToBase
          (grading (equationIdeal cubic hcubic)) f 8))
        (Q.fromSpecStalk (genericPoint Q))
    let b := quadraticOrderedLiftFunctionFieldHom cubic hcubic z hz
    letI : IsFinite pD := D.property.1
    letI := finiteSchemeCoefficientAlgebra pD
    letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
    Γ(D.val.subscheme, ⊤) →ₐ[Q.functionField] O.residueField z := by
  dsimp only
  letI : IsSeparated
      (show Proj (grading (equationIdeal cubic hcubic)) ⟶ Spec (.of K) from
        toBase (equationIdeal cubic hcubic)) := hsep
  letI : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (toBase (equationIdeal cubic hcubic)) 8).toScheme := hint
  let f := toBase (equationIdeal cubic hcubic)
  let Q := (projectiveConfigurationQuotientOpen
    (grading (equationIdeal cubic hcubic)) f 8).toScheme
  let O := (orderedFamilyConfigurationOver f 8).left
  let D := projectiveConfigurationGenericFiniteSubscheme
    (grading (equationIdeal cubic hcubic)) f 8
  let pD := D.val.subschemeι ≫
    pullback.snd
      (pullback.snd f (projectiveConfigurationQuotientToBase
        (grading (equationIdeal cubic hcubic)) f 8))
      (Q.fromSpecStalk (genericPoint Q))
  let b := quadraticOrderedLiftFunctionFieldHom cubic hcubic z hz
  letI : IsFinite pD := D.property.1
  letI := finiteSchemeCoefficientAlgebra pD
  letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
  exact finiteSchemePointAlgHom pD
    (quadraticOrderedLiftComponentPoint cubic hcubic z hz i) b
    (quadraticOrderedLiftComponentPoint_toBase cubic hcubic z hz i)

/-- Pullback of global functions along the transported labeled component,
now on the literal coefficient-changed cubic. -/
noncomputable def quadraticOrderedLiftCoefficientChangedComponentAlgHom
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 8)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 8).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap cubic hcubic 8 ≫
        cubicConfigurationToBase cubic hcubic 8)
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left)
    (hz : projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8 z =
      ((projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme))
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme.functionField))
    (i : Fin 8) :
    let Q := cubicConfigurationBase cubic hcubic 8
    let O := (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left
    let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 8 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap
      cubic hcubic 8 a ha
    let b := quadraticOrderedLiftFunctionFieldHom cubic hcubic z hz
    letI : IsFinite pD := D.property.1
    letI := finiteSchemeCoefficientAlgebra pD
    letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
    Γ(D.val.subscheme, ⊤) →ₐ[Q.functionField] O.residueField z := by
  dsimp only
  let Q := cubicConfigurationBase cubic hcubic 8
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase cubic hcubic) 8).left
  let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 8 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 8 a ha
  let b := quadraticOrderedLiftFunctionFieldHom cubic hcubic z hz
  letI : IsFinite pD := D.property.1
  letI := finiteSchemeCoefficientAlgebra pD
  letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
  exact finiteSchemePointAlgHom pD
    (quadraticOrderedLiftCoefficientChangedComponentPoint
      cubic hcubic a ha z hz i) b
    (quadraticOrderedLiftCoefficientChangedComponentPoint_toBase
      cubic hcubic a ha z hz i)

/-- The algebra map of a transported labeled component recovers that
component after the canonical affine presentation and any later morphism. -/
lemma quadraticOrderedLiftCoefficientChangedComponentAlgHom_spec_comp
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 8)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 8).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap cubic hcubic 8 ≫
        cubicConfigurationToBase cubic hcubic 8)
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left)
    (hz : projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8 z =
      ((projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme))
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme.functionField))
    (i : Fin 8) {Y : Scheme.{u}}
    (j : (cubicConfigurationGenericFiniteSubscheme
      cubic hcubic 8 a ha).val.subscheme ⟶ Y) :
    let Q := cubicConfigurationBase cubic hcubic 8
    let O := (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left
    let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 8 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap
      cubic hcubic 8 a ha
    let b := quadraticOrderedLiftFunctionFieldHom cubic hcubic z hz
    letI : IsFinite pD := D.property.1
    letI := finiteSchemeCoefficientAlgebra pD
    letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
    letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
    Spec.map (CommRingCat.ofHom
        (quadraticOrderedLiftCoefficientChangedComponentAlgHom
          cubic hcubic a ha z hz i).toRingHom) ≫
      D.val.subscheme.isoSpec.inv ≫ j =
    quadraticOrderedLiftCoefficientChangedComponentPoint
      cubic hcubic a ha z hz i ≫ j := by
  dsimp only
  let Q := cubicConfigurationBase cubic hcubic 8
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase cubic hcubic) 8).left
  let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 8 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 8 a ha
  let b := quadraticOrderedLiftFunctionFieldHom cubic hcubic z hz
  letI : IsFinite pD := D.property.1
  letI := finiteSchemeCoefficientAlgebra pD
  letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
  unfold quadraticOrderedLiftCoefficientChangedComponentAlgHom
  exact finiteSchemePointAlgHom_spec_comp pD
    (quadraticOrderedLiftCoefficientChangedComponentPoint
      cubic hcubic a ha z hz i) b
    (quadraticOrderedLiftCoefficientChangedComponentPoint_toBase
      cubic hcubic a ha z hz i) j

/-- Any affine presentation of the transported finite scheme that recovers
its ambient immersion evaluates a labeled component at the corresponding
ordered marked projective point. -/
lemma quadraticOrderedLiftCoefficientChangedComponentAlgHom_chart_toMarkedPoint
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 8)]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 8).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap cubic hcubic 8 ≫
        cubicConfigurationToBase cubic hcubic 8)
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left)
    (hz : projectiveConfigurationQuotientMap
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8 z =
      ((projectiveConfigurationQuotientOpen
        (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme.fromSpecStalk
          (genericPoint (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme))
        (IsLocalRing.closedPoint
          (projectiveConfigurationQuotientOpen
            (grading (equationIdeal cubic hcubic))
            (hypersurfaceToBase cubic hcubic) 8).toScheme.functionField))
    (i : Fin 8)
    (c : Spec (.of Γ((cubicConfigurationGenericFiniteSubscheme
      cubic hcubic 8 a ha).val.subscheme, ⊤)) ⟶
        Proj (MvPolynomial.homogeneousSubmodule (Fin 4) K)) :
    let Q := cubicConfigurationBase cubic hcubic 8
    let O := (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left
    let p' := cubic.map a.hom
    let hp' := hcubic.map a.hom
    let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 8 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap
      cubic hcubic 8 a ha
    let b := quadraticOrderedLiftFunctionFieldHom cubic hcubic z hz
    letI : IsFinite pD := D.property.1
    letI := finiteSchemeCoefficientAlgebra pD
    letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
    letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
    c = D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι ≫
          hypersurfaceToAmbient p' hp' ≫ ambientCoefficientMap a.hom →
      Spec.map (CommRingCat.ofHom
          (quadraticOrderedLiftCoefficientChangedComponentAlgHom
            cubic hcubic a ha z hz i).toRingHom) ≫ c =
        (orderedFamilyConfigurationOver
            (hypersurfaceToBase cubic hcubic) 8).left.fromSpecResidueField z ≫
          @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
            (grading (equationIdeal cubic hcubic)) _
            (hypersurfaceToBase cubic hcubic) hsep 8
            (hypersurfaceToAmbient cubic hcubic) i := by
  dsimp only
  let Q := cubicConfigurationBase cubic hcubic 8
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase cubic hcubic) 8).left
  let p' := cubic.map a.hom
  let hp' := hcubic.map a.hom
  let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 8 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 8 a ha
  let b := quadraticOrderedLiftFunctionFieldHom cubic hcubic z hz
  letI : IsFinite pD := D.property.1
  letI := finiteSchemeCoefficientAlgebra pD
  letI : Algebra Q.functionField (O.residueField z) := b.toAlgebra
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
  intro hc
  let j := D.val.subschemeι ≫ hypersurfaceToAmbient p' hp' ≫
    ambientCoefficientMap a.hom
  have hrecover := finiteSchemePointAlgHom_spec_comp_of_eq pD
    (quadraticOrderedLiftCoefficientChangedComponentPoint
      cubic hcubic a ha z hz i) b
    (quadraticOrderedLiftCoefficientChangedComponentPoint_toBase
      cubic hcubic a ha z hz i) j c hc
  have hmarked :=
    quadraticOrderedLiftCoefficientChangedComponentPoint_toAmbientProjective
      cubic hcubic a ha z hz i
  exact hrecover.trans hmarked

/-- The coefficient-changed generic rank-eight datum admits a normalized
projective chart retaining its actual immersion into the cubic. -/
theorem exists_cubicConfigurationGenericEight_normalizedChart
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hbase : IsIntegral (cubicConfigurationBase cubic hcubic 8)]
    [hinfinite : Infinite (cubicConfigurationBase cubic hcubic 8).functionField]
    (a : CommRingCat.of K ⟶ CommRingCat.of
      (cubicConfigurationBase cubic hcubic 8).functionField)
    (ha : Spec.map a =
      cubicConfigurationGenericBaseMap cubic hcubic 8 ≫
        cubicConfigurationToBase cubic hcubic 8) :
    let Q := cubicConfigurationBase cubic hcubic 8
    let p' := cubic.map a.hom
    let hp' := hcubic.map a.hom
    let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 8 a ha
    let pD := cubicConfigurationCoefficientChangedBaseMap
      cubic hcubic 8 a ha
    letI : IsFinite pD := D.property.1
    letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
    letI := finiteSchemeCoefficientAlgebra pD
    ∃ (w : CoordinateRing (equationIdeal p' hp'))
      (hw : w ∈ grading (equationIdeal p' hp') 1)
      (x : Fin 4 → Γ(D.val.subscheme, ⊤))
      (he : ∀ q ∈ (equationIdeal p' hp').toIdeal,
        (eval₂Hom (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) x) q = 0)
      (hwOne : (Ideal.Quotient.lift (equationIdeal p' hp').toIdeal
        (eval₂Hom (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) x) he) w = 1),
      Function.Surjective
          (eval₂Hom (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) x) ∧
      p'.eval₂ (algebraMap Q.functionField Γ(D.val.subscheme, ⊤)) x = 0 ∧
      linearNormalizedPointAt (equationIdeal p' hp') x he w hw hwOne =
        D.val.subscheme.isoSpec.inv ≫ D.val.subschemeι := by
  dsimp only
  let p' := cubic.map a.hom
  let hp' := hcubic.map a.hom
  let D := cubicConfigurationGenericFiniteSubscheme cubic hcubic 8 a ha
  let pD := cubicConfigurationCoefficientChangedBaseMap cubic hcubic 8 a ha
  letI : IsFinite pD := D.property.1
  letI : IsFinite
      (D.val.subschemeι ≫ hypersurfaceToBase p' hp') := D.property.1
  letI : IsAffine D.val.subscheme := isAffine_of_isAffineHom pD
  letI := finiteSchemeCoefficientAlgebra pD
  exact cubicFiniteSubscheme_normalized_chart p' hp' D.val.subschemeι

/-- At an ordered configuration point, there is no common residue-field
equation from the canonical eight-dimensional quadratic subsystem.  The
statement is intrinsic: a putative projective equation parameter and its
eight universal-family incidence lifts are ruled out simultaneously. -/
def QuadraticEightNoCommonResidueFieldEquationAt
    {K : Type u} [Field K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    (z : (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left) : Prop :=
  let O := (orderedFamilyConfigurationOver
    (hypersurfaceToBase cubic hcubic) 8).left
  let T := projectiveLinearSystemParameters (K := K) (τ := Fin 8)
  let tBase := toBase
    (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 8) K))
  let e : Fin (Fintype.card (Monomials (Fin 4) 2)) ≃ Monomials (Fin 4) 2 :=
    (Fintype.equivFin _).symm
  let marked := fun i =>
    @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
      (grading (equationIdeal cubic hcubic)) _
      (hypersurfaceToBase cubic hcubic) hsep 8
      (hypersurfaceToAmbient cubic hcubic) i
  let frame := homogeneousFrameToParameters 2 e (quadraticEightFrame K)
    (quadraticEightFrame_linearIndependent K)
  ¬ ∃ (t : Spec (.of (O.residueField z)) ⟶ T)
    (q : Fin 8 → (Spec (.of (O.residueField z)) ⟶
      projectiveUniversalFamily K (Fin 4) 2))
    (hbase : O.fromSpecResidueField z ≫
      (orderedFamilyConfigurationOver
        (hypersurfaceToBase cubic hcubic) 8).hom = t ≫ tBase),
    ∀ i, q i ≫ projectiveUniversalIncidence K (Fin 4) 2 =
      pullback.lift (O.fromSpecResidueField z) t hbase ≫
        projectiveUniversalFiniteIncidenceParameterMap K (Fin 4) 2
          (orderedFamilyConfigurationOver
            (hypersurfaceToBase cubic hcubic) 8).hom
          tBase marked frame i

/-- Above the generic unordered eight-point configuration, one can choose an
ordered residue-field realization on which no nonzero equation in the fixed
eight-dimensional quadratic subsystem vanishes at all eight marked points. -/
theorem exists_orderedPointOver_genericEight_with_noCommonQuadraticEightEquation
    {K : Type u} [Field K] [IsAlgClosed K]
    (cubic : MvPolynomial (Fin 4) K) (hcubic : cubic.IsHomogeneous 3)
    (hcubic_ne : cubic ≠ 0)
    (hcubic_prime : (Ideal.span ({cubic} : Set (MvPolynomial (Fin 4) K))).IsPrime)
    [hsep : IsSeparated (hypersurfaceToBase cubic hcubic)]
    [hint : IsIntegral
      (projectiveConfigurationQuotientOpen (grading (equationIdeal cubic hcubic))
        (hypersurfaceToBase cubic hcubic) 8).toScheme] :
    let O := (orderedFamilyConfigurationOver
      (hypersurfaceToBase cubic hcubic) 8).left
    let Q := (projectiveConfigurationQuotientOpen
      (grading (equationIdeal cubic hcubic))
      (hypersurfaceToBase cubic hcubic) 8).toScheme
    let π := projectiveConfigurationQuotientMap
      (grading (equationIdeal cubic hcubic))
      (hypersurfaceToBase cubic hcubic) 8
    let η := Q.fromSpecStalk (genericPoint Q)
      (IsLocalRing.closedPoint Q.functionField)
    ∃ z : O, π z = η ∧
      QuadraticEightNoCommonResidueFieldEquationAt cubic hcubic z := by
  dsimp only
  obtain ⟨z, hzπ, hzbad⟩ :=
    exists_orderedPointOver_genericEight_avoids_quadraticEightFiniteIncidence
      cubic hcubic hcubic_ne hcubic_prime
  refine ⟨z, hzπ, ?_⟩
  unfold QuadraticEightNoCommonResidueFieldEquationAt
  dsimp only
  exact
    not_exists_common_residueFieldPoints_of_not_mem_projectiveUniversalFiniteIncidenceBadLocus
      K (Fin 4) 2
      (orderedFamilyConfigurationOver
        (hypersurfaceToBase cubic hcubic) 8).hom
      (toBase (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 8) K)))
      (fun i => @orderedConfigurationProjectivePoint K _ (Fin 4) _ _ _ _ _
        (grading (equationIdeal cubic hcubic)) _
        (hypersurfaceToBase cubic hcubic) hsep 8
        (hypersurfaceToAmbient cubic hcubic) i)
      (homogeneousFrameToParameters 2
        ((Fintype.equivFin (Monomials (Fin 4) 2)).symm)
        (quadraticEightFrame K) (quadraticEightFrame_linearIndependent K)) hzbad

end PfaffianDescent
