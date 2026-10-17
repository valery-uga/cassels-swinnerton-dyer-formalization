import PfaffianDescent.VoisinQuadraticJacobianUniversalFamily
import PfaffianDescent.ProjectiveSpaceRationalOpen

/-!
# From an empty cubic--quadric--quadric singular fiber to étaleness

The mixed-degree universal singular family supplies the Bertini parameter
space needed in Voisin's final degree-eight residual construction.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics HomogeneousProjective

universe u

section

variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- An empty simultaneous-singularity fiber of the universal family makes
the corresponding specialized three-cubic intersection étale. -/
theorem
    etale_cubicTwoQuadric_toBase_of_isEmpty_universalSingularChartFiber
    {L : Type u} [Field L] {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2)
    (i : Fin n)
    (g : ChartRing
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i →+* L)
    (hempty : IsEmpty (scheme
      (cubicTwoQuadricUniversalSingularChartFiberIdeal
        p q hp hq v i g))) :
    Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (p.map (g.comp (chartBaseMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)))
      (q.map (g.comp (chartBaseMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)))
      (((cubicTwoQuadricUniversalQuadric v).map
        (cubicTwoQuadricParameterChartCoefficientMap (K := K) i)).map g)
      (hp.map _)
      (hq.map _)
      ((cubicTwoQuadricUniversalQuadric_isHomogeneous v).map _ |>.map g))) := by
  apply etale_cubicTwoQuadric_toBase_of_isEmpty_singularScheme
  simpa only [cubicTwoQuadricUniversalSingularChartFiberIdeal] using hempty

/-- A field-valued parameter outside the global simultaneous-singularity
locus factors through a normalized parameter chart, and its specialized
three-cubic intersection is étale. -/
theorem
    exists_cubicTwoQuadric_parameterChartHom_etale_of_fieldPoint_not_mem_singularParameterLocus
    {L : Type u} [Field L] {n : ℕ}
    (f : K →+* L)
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2)
    (t : Spec (.of L) ⟶
      projectiveLinearSystemParameters (K := K) (τ := Fin n))
    (ht : t ≫ toBase
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) =
        Spec.map (CommRingCat.ofHom f))
    (hgood : t (IsLocalRing.closedPoint L) ∉
      cubicTwoQuadricUniversalSingularParameterLocus
        p q hp hq v) :
    ∃ (i : Fin n)
      (g : ChartRing
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i →+* L),
      g.comp (chartBaseMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i) = f ∧
      Spec.map (CommRingCat.ofHom g) ≫
        chartι (⊥ : HomogeneousIdeal
          (homogeneousSubmodule (Fin n) K)) i = t ∧
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal
        (p.map (g.comp (chartBaseMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)))
        (q.map (g.comp (chartBaseMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)))
        (((cubicTwoQuadricUniversalQuadric v).map
          (cubicTwoQuadricParameterChartCoefficientMap (K := K) i)).map g)
        (hp.map _)
        (hq.map _)
        ((cubicTwoQuadricUniversalQuadric_isHomogeneous v).map _ |>.map g))) := by
  obtain ⟨i, g, hgbase, hgt, hempty⟩ :=
    exists_cubicTwoQuadric_parameterChartHom_empty_singularFiber_of_fieldPoint_not_mem_singularParameterLocus
      f p q hp hq v t ht hgood
  exact ⟨i, g, hgbase, hgt,
    etale_cubicTwoQuadric_toBase_of_isEmpty_universalSingularChartFiber
      p q hp hq v i g hempty⟩

/-- Over an infinite ground field, properness of the universal singular-member
locus supplies a normalized parameter-chart point over the ground field
itself whose specialized three-cubic intersection is étale. -/
theorem
    exists_groundField_cubicTwoQuadric_parameterChartHom_etale_of_singularParameterLocus_ne_univ
    [Infinite K] {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 2)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 2)
    (hproper : cubicTwoQuadricUniversalSingularParameterLocus
      p q hp hq v ≠ Set.univ) :
    ∃ (i : Fin n)
      (g : ChartRing
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i →+* K),
      g.comp (chartBaseMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i) =
          RingHom.id K ∧
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal
        (p.map (g.comp (chartBaseMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)))
        (q.map (g.comp (chartBaseMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)))
        (((cubicTwoQuadricUniversalQuadric v).map
          (cubicTwoQuadricParameterChartCoefficientMap (K := K) i)).map g)
        (hp.map _)
        (hq.map _)
        ((cubicTwoQuadricUniversalQuadric_isHomogeneous v).map _ |>.map g))) := by
  classical
  let U : Scheme.Opens
      (projectiveLinearSystemParameters (K := K) (τ := Fin n)) :=
    ⟨cubicTwoQuadricUniversalNonsingularParameterLocus p q hp hq v,
      isOpen_cubicTwoQuadricUniversalNonsingularParameterLocus
        p q hp hq v⟩
  obtain ⟨x, hx⟩ :=
    (Set.ne_univ_iff_exists_notMem
      (cubicTwoQuadricUniversalSingularParameterLocus
        p q hp hq v)).mp hproper
  have hxU : x ∈ (U : Set
      (projectiveLinearSystemParameters (K := K) (τ := Fin n))) := by
    simpa [U,
      cubicTwoQuadricUniversalSingularParameterLocus,
      Set.mem_compl_iff] using hx
  obtain ⟨s, hs⟩ :=
    nonempty_open_projectiveSpace_has_rational_section U ⟨x, hxU⟩
  let t : Spec (.of K) ⟶
      projectiveLinearSystemParameters (K := K) (τ := Fin n) := s ≫ U.ι
  have ht : t ≫ toBase
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) =
        Spec.map (CommRingCat.ofHom (RingHom.id K)) := by
    change t ≫ toBase
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) =
        Spec.map (𝟙 (CommRingCat.of K))
    rw [Spec.map_id]
    exact hs
  have hgood : t (IsLocalRing.closedPoint K) ∉
      cubicTwoQuadricUniversalSingularParameterLocus
        p q hp hq v := by
    change U.ι (s (IsLocalRing.closedPoint K)) ∉
      cubicTwoQuadricUniversalSingularParameterLocus
        p q hp hq v
    have hsU : U.ι (s (IsLocalRing.closedPoint K)) ∈ (U : Set
        (projectiveLinearSystemParameters (K := K) (τ := Fin n))) :=
      (s (IsLocalRing.closedPoint K)).property
    simpa [U,
      cubicTwoQuadricUniversalSingularParameterLocus,
      Set.mem_compl_iff] using hsU
  obtain ⟨i, g, hgbase, _hgt, hetale⟩ :=
    exists_cubicTwoQuadric_parameterChartHom_etale_of_fieldPoint_not_mem_singularParameterLocus
      (RingHom.id K) p q hp hq v t ht hgood
  exact ⟨i, g, hgbase, hetale⟩

end

end PfaffianDescent
