import PfaffianDescent.VoisinLocalPointIntersectionFlat
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Flatness of the explicit projective two-cubic intersection

Flatness on the standard quotient charts descends to the actual projective
scheme via their affine open cover. The previous local-point theorem then
gives a flat explicit projective model at every local point of Voisin's
nontrivial moving-cubic parameter family.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
open AllCharacteristics.UniversalHomogeneous

universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Flat quotient-chart maps over a coefficient ring imply flatness of the
actual projective quotient scheme's structure morphism. -/
theorem flat_toBase_of_flat_quotientCharts
    {T : Type u} [CommRing T]
    (I J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) T))
    (hIJ : I.toIdeal ≤ J.toIdeal)
    (hflat : ∀ i : Fin 4,
      ((chartQuotientMap I J hIJ i).comp (chartBaseMap I i)).Flat) :
    Flat (toBase J) := by
  have : IsZariskiLocalAtSource (@AlgebraicGeometry.Flat.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Flat)
  apply (IsZariskiLocalAtSource.iff_of_openCover (P := @AlgebraicGeometry.Flat.{u})
    (coordinateOpenCover J).openCover).mpr
  intro i
  change Fin 4 at i
  change Flat (chartι J i ≫ toBase J)
  rw [chartι_toBase, Flat.SpecMap_iff]
  rw [← chartQuotientMap_chartBaseMap I J hIJ i]
  exact hflat i

/-- The explicit projective intersection of a fixed cubic and a moving
cubic is flat over a local coefficient ring if the moving cubic is regular
on the fixed cubic's residue-field coordinate ring. -/
theorem fixedCubic_projectiveIntersection_flat_of_residue_regular
    {K T : Type u} [Field K] [CommRing T] [Algebra K T]
    [IsLocalRing T]
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3)
    (p : MvPolynomial (Fin 4) T) (hp : p.IsHomogeneous 3)
    (hreg : IsRegular (Ideal.Quotient.mk
      (equationIdeal (a.map (algebraMap K (IsLocalRing.ResidueField T)))
        (ha.map (algebraMap K (IsLocalRing.ResidueField T)))).toIdeal
      (p.map (algebraMap T (IsLocalRing.ResidueField T))))) :
    let J := equationIdeal (a.map (algebraMap K T))
      (ha.map (algebraMap K T))
    Flat (toBase (J ⊔ equationIdeal p hp)) := by
  let J := equationIdeal (a.map (algebraMap K T))
    (ha.map (algebraMap K T))
  apply flat_toBase_of_flat_quotientCharts J
    (J ⊔ equationIdeal p hp)
    (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left)
  intro i
  exact fixedCubicIntersectionChart_flat_of_residue_regular
    a ha p hp hreg i

/-- Every local point of Voisin's actual nontrivial parameter family has a
normalized equation whose explicit projective two-cubic intersection is
flat over the local coefficient ring. -/
theorem flatGradedNontrivialOpen_localPoint_projectiveIntersection_flat
    {K R T : Type u} [Field K] [CommRing R] [IsDomain R]
    [IsNoetherianRing R] [Algebra K R]
    [CommRing T] [IsLocalRing T] [Algebra R T]
    [Algebra K T] [IsScalarTower K R T]
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) R))
    [Module.Flat R (CoordinateRing J)]
    (r q : ℕ) (e : Fin (r + q) ≃ Monomials (Fin 4) 3)
    (hRank : ∀ x : PrimeSpectrum R,
      Module.rankAtStalk (grading J 3) x = q)
    (a : MvPolynomial (Fin 4) K) (ha : a.IsHomogeneous 3) (ha0 : a ≠ 0)
    [Smooth (hypersurfaceToBase
      (a.map (algebraMap K (IsLocalRing.ResidueField T)))
      (ha.map (algebraMap K (IsLocalRing.ResidueField T))))]
    (n : Spec (.of T) ⟶
      flatGradedProjectiveFamilyNontrivialOpen J r q e hRank a ha ha0)
    (hn : n ≫ flatGradedProjectiveFamilyNontrivialOpenToBase
        J r q e hRank a ha ha0 =
      Spec.map (CommRingCat.ofHom (algebraMap R T))) :
    ∃ (j : Monomials (Fin 4) 3)
      (f : ParameterChartRing K (Fin 4) 3 j →+* T),
      Spec.map (CommRingCat.ofHom f) ≫ parameterChartι K (Fin 4) 3 j =
        n ≫ flatGradedNontrivialOpenToGlobalParameters
          a ha J r q e hRank ha0 ∧
      let p := (normalizedForm K (Fin 4) 3 j).map f
      let hp := (normalizedForm_isHomogeneous K (Fin 4) 3 j).map f
      let Jₐ := equationIdeal (a.map (algebraMap K T))
        (ha.map (algebraMap K T))
      Flat (toBase (Jₐ ⊔ equationIdeal p hp)) := by
  obtain ⟨p, hp, j, hj, f, hf, hcharts⟩ :=
    flatGradedNontrivialOpen_localPoint_intersectionCharts_flat
      J r q e hRank a ha ha0 n hn
  refine ⟨j, f, hf, ?_⟩
  let pₜ := (normalizedForm K (Fin 4) 3 j).map f
  let hpₜ := (normalizedForm_isHomogeneous K (Fin 4) 3 j).map f
  let Jₐ := equationIdeal (a.map (algebraMap K T))
    (ha.map (algebraMap K T))
  apply flat_toBase_of_flat_quotientCharts Jₐ
    (Jₐ ⊔ equationIdeal pₜ hpₜ)
    (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left)
  exact hcharts

end PfaffianDescent
