import PfaffianDescent.VoisinFiniteAlgebraPencilProjectiveDescent
import PfaffianDescent.VoisinSplitQuadraticMinorFromComponentSpan

/-!
# Unordered projective intersection from a rank-eight algebra

The rank-eight hypothesis supplies the two independent vanishing quadrics
needed for the ordered/unordered ideal and projective comparisons.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open CategoryTheory.Limits
open AllCharacteristics.UniversalHomogeneous
open AllCharacteristics.HomogeneousProjective

universe u

/-- A rank-eight finite coordinate algebra with a jointly detecting ordered
splitting and a selected full-rank minor has an unordered cubic--quadratic
ideal whose scalar extension is the intrinsic ordered intersection ideal. -/
theorem exists_rankEight_intrinsicTripleIdeal_idealMap
    {K A L : Type u} [Field K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A] [Field L] [Algebra K L]
    (x : Fin 4 → A) (hA : Module.finrank K A = 8)
    (φ : Fin 8 → A →ₐ[K] L)
    (hφ : Function.Injective (fun t : A => fun i => φ i t))
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (hminor : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun i j => φ i (x j))).det)
    (p : MvPolynomial (Fin 4) K) :
    ∃ q : Fin 2 → homogeneousSubmodule (Fin 4) K 2,
      intrinsicEightPointTripleIdeal
        (p.map (algebraMap K L)) (fun i j => φ i (x j)) =
      (Ideal.span (insert p (Set.range (fun i : Fin 2 => (q i).1)))).map
        (MvPolynomial.map (algebraMap K L)) := by
  obtain ⟨q, hq, hzero⟩ :=
    exists_rankEight_independentVanishingHomogeneousQuadrics x hA
  exact ⟨q, quadraticHomogeneousPair_intrinsicTripleIdeal_eq_idealMap
    φ hφ x q hq hzero m hminor p⟩

/-- The same rank-eight data gives an unordered projective family whose
splitting-field pullback is the intrinsic ordered intersection. -/
theorem exists_rankEight_intrinsicProjectiveBaseChangeIso
    {K A L : Type u} [Field K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A] [Field L] [Algebra K L]
    (x : Fin 4 → A) (hA : Module.finrank K A = 8)
    (φ : Fin 8 → A →ₐ[K] L)
    (hφ : Function.Injective (fun t : A => fun i => φ i t))
    (m : Fin 8 ↪ Monomials (Fin 4) 2)
    (hminor : IsUnit (eightPointQuadraticEvaluationMinor m
      (fun i j => φ i (x j))).det)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) :
    ∃ q : Fin 2 → homogeneousSubmodule (Fin 4) K 2,
      Nonempty (scheme (intrinsicEightPointTripleHomogeneousIdeal
        (p.map (algebraMap K L)) (hp.map (algebraMap K L))
        (fun i j => φ i (x j))) ≅
      pullback (relativeTripleIntersectionToBase
        p (q 0).1 (q 1).1 hp (q 0).2 (q 1).2)
        (Spec.map (CommRingCat.ofHom (algebraMap K L)))) := by
  obtain ⟨q, hq, hzero⟩ :=
    exists_rankEight_independentVanishingHomogeneousQuadrics x hA
  exact ⟨q, ⟨quadraticHomogeneousPair_intrinsicProjectiveBaseChangeIso
    φ hφ x q hq hzero m hminor p hp⟩⟩

/-- If the ordered component evaluations span the split rank-eight
coordinate space, the full-rank minor can be selected rather than assumed. -/
theorem exists_rankEight_intrinsicProjectiveBaseChangeIso_of_componentSpan
    {K A L : Type u} [Field K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A] [Field L] [Algebra K L]
    (x : Fin 4 → A) (hA : Module.finrank K A = 8)
    (φ : Fin 8 → A →ₐ[K] L)
    (hφ : Function.Injective (fun t : A => fun i => φ i t))
    (hquad : Function.Surjective
      (homogeneousSectionRestriction (K := K) x 2))
    (hcomponents : Submodule.span L
      (Set.range (fun t : A => fun i : Fin 8 => φ i t)) = ⊤)
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) :
    ∃ (m : Fin 8 ↪ Monomials (Fin 4) 2)
      (q : Fin 2 → homogeneousSubmodule (Fin 4) K 2),
      Nonempty (scheme (intrinsicEightPointTripleHomogeneousIdeal
        (p.map (algebraMap K L)) (hp.map (algebraMap K L))
        (fun i j => φ i (x j))) ≅
      pullback (relativeTripleIntersectionToBase
        p (q 0).1 (q 1).1 hp (q 0).2 (q 1).2)
        (Spec.map (CommRingCat.ofHom (algebraMap K L)))) := by
  obtain ⟨m, hm⟩ :=
    exists_unit_eightPointQuadraticEvaluationMinor_of_componentSpan
      φ x hquad hcomponents
  obtain ⟨q, hq⟩ := exists_rankEight_intrinsicProjectiveBaseChangeIso
    x hA φ hφ m hm p hp
  exact ⟨m, q, hq⟩

/-- For distinct ordered components, Artin independence supplies the split
component spanning needed to choose the quadratic minor automatically. -/
theorem exists_rankEight_intrinsicProjectiveBaseChangeIso_of_distinctComponents
    {K A L : Type u} [Field K] [CommRing A] [Algebra K A]
    [FiniteDimensional K A] [Field L] [Algebra K L]
    (x : Fin 4 → A) (hA : Module.finrank K A = 8)
    (φ : Fin 8 → A →ₐ[K] L)
    (hφ : Function.Injective (fun t : A => fun i => φ i t))
    (hdistinct : Function.Injective φ)
    (hquad : Function.Surjective
      (homogeneousSectionRestriction (K := K) x 2))
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) :
    ∃ (m : Fin 8 ↪ Monomials (Fin 4) 2)
      (q : Fin 2 → homogeneousSubmodule (Fin 4) K 2),
      Nonempty (scheme (intrinsicEightPointTripleHomogeneousIdeal
        (p.map (algebraMap K L)) (hp.map (algebraMap K L))
        (fun i j => φ i (x j))) ≅
      pullback (relativeTripleIntersectionToBase
        p (q 0).1 (q 1).1 hp (q 0).2 (q 1).2)
        (Spec.map (CommRingCat.ofHom (algebraMap K L)))) := by
  exact exists_rankEight_intrinsicProjectiveBaseChangeIso_of_componentSpan
    x hA φ hφ hquad (componentSpan_eq_top_of_injective φ hdistinct) p hp

end PfaffianDescent
