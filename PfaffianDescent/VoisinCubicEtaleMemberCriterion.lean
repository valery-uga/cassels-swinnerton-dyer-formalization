import PfaffianDescent.VoisinEtaleJacobianConverse
import PfaffianDescent.VoisinSingularFiberEtale
import PfaffianDescent.VoisinDegreeTenRestrictionKernelEtale

/-!
# An étale member certifies properness of the three-cubic bad locus

This is the cubic analogue of the quadratic criterion. It makes a selected
étale complete intersection a concrete witness that the universal singular
parameter locus is proper. Constructing such a member remains geometric work.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics HomogeneousProjective

universe u

variable {K : Type u} [Field K]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The complete-intersection ideal is contained in its simultaneous
Jacobian singular ideal. -/
theorem tripleCubic_intersectionIdeal_le_singularIdeal
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (hr : r.IsHomogeneous 3) :
    (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr).toIdeal ≤
      (tripleCompleteIntersectionSingularHomogeneousIdeal p q r hp hq hr).toIdeal := by
  rw [tripleCompleteIntersectionHomogeneousIdeal_toIdeal,
    tripleCompleteIntersectionIdeal,
    tripleCompleteIntersectionSingularHomogeneousIdeal_toIdeal,
    tripleCompleteIntersectionSingularIdeal, Ideal.span_le]
  intro s hs
  apply Ideal.subset_span
  exact Or.inl hs

/-- An étale three-cubic projective complete intersection has empty
simultaneous Jacobian singular scheme. -/
theorem tripleCubic_singularScheme_isEmpty_of_etale
    (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (hr : r.IsHomogeneous 3)
    (hEtale : Etale
      (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    IsEmpty (scheme
      (tripleCompleteIntersectionSingularHomogeneousIdeal p q r hp hq hr)) := by
  let J := tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr
  let I := tripleCompleteIntersectionSingularHomogeneousIdeal p q r hp hq hr
  have hJI : J.toIdeal ≤ I.toIdeal :=
    tripleCubic_intersectionIdeal_le_singularIdeal p q r hp hq hr
  have hunit : ∀ j : Fin 4,
      IsUnit (tripleCompleteIntersectionChartJacobian p q r hp hq hr j) :=
    (tripleCompleteIntersection_etale_iff_chartJacobian_isUnit
      p q r hp hq hr).mp hEtale
  refine ⟨fun s => ?_⟩
  obtain ⟨j, y, _hy⟩ := exists_coordinate_chart I s
  let F := tripleCompleteIntersectionChartJacobianPolynomial p q r j
  have hFmem : F ∈ I.toIdeal := by
    change F ∈ tripleCompleteIntersectionSingularIdeal p q r
    apply Ideal.subset_span
    exact Or.inr ⟨j, rfl⟩
  have hzero : F.eval₂ (chartBaseMap I j) (chartCoordinate I j) = 0 :=
    eval₂_chartCoordinate_eq_zero_of_mem I j F hFmem
  have hunitI : IsUnit (F.eval₂ (chartBaseMap I j) (chartCoordinate I j)) := by
    rw [← chartQuotientMap_eval₂ J I hJI j F]
    exact (hunit j).map (chartQuotientMap J I hJI j)
  letI : Nontrivial (ChartRing I j) := PrimeSpectrum.nontrivial y
  exact not_isUnit_zero (hzero ▸ hunitI)

/-- Étaleness of a field-valued member empties its specialized singular
fiber in the common projective parameter family. -/
theorem tripleCubic_universalSingularChartFiber_isEmpty_of_etale
    {L : Type u} [Field L] {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3)
    (i : Fin n)
    (g : ChartRing
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i →+* L)
    (hEtale : Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (p.map (g.comp (chartBaseMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)))
      (q.map (g.comp (chartBaseMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)))
      (((tripleCompleteIntersectionUniversalCubic v).map
        (tripleCompleteIntersectionParameterChartCoefficientMap (K := K) i)).map g)
      (hp.map _) (hq.map _)
      ((tripleCompleteIntersectionUniversalCubic_isHomogeneous v).map _ |>.map g)))) :
    IsEmpty (scheme (tripleCompleteIntersectionUniversalSingularChartFiberIdeal
      p q hp hq v i g)) := by
  exact tripleCubic_singularScheme_isEmpty_of_etale
    (p.map (g.comp (chartBaseMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)))
    (q.map (g.comp (chartBaseMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)))
    (((tripleCompleteIntersectionUniversalCubic v).map
      (tripleCompleteIntersectionParameterChartCoefficientMap (K := K) i)).map g)
    (hp.map _) (hq.map _)
    ((tripleCompleteIntersectionUniversalCubic_isHomogeneous v).map _ |>.map g)
    hEtale

/-- An étale field-valued member makes the three-cubic singular parameter
locus proper. -/
theorem tripleCubic_universalSingularParameterLocus_ne_univ_of_etale_fiber
    {L : Type u} [Field L] {n : ℕ}
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3)
    (i : Fin n)
    (g : ChartRing
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i →+* L)
    (hEtale : Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal
      (p.map (g.comp (chartBaseMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)))
      (q.map (g.comp (chartBaseMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)))
      (((tripleCompleteIntersectionUniversalCubic v).map
        (tripleCompleteIntersectionParameterChartCoefficientMap (K := K) i)).map g)
      (hp.map _) (hq.map _)
      ((tripleCompleteIntersectionUniversalCubic_isHomogeneous v).map _ |>.map g)))) :
    tripleCompleteIntersectionUniversalSingularParameterLocus
      p q hp hq v ≠ Set.univ := by
  have hEmpty := tripleCubic_universalSingularChartFiber_isEmpty_of_etale
    p q hp hq v i g hEtale
  exact tripleCompleteIntersectionUniversalSingularParameterLocus_ne_univ_of_fiber_isEmpty
    p q hp hq v i g (fun z => isEmptyElim z)

/-- Specializing the universal cubic at normalized coefficient coordinates
reproduces the corresponding linear combination of the frame. -/
theorem tripleCubic_universalCubic_specialize_normalizedCoordinates
    {n : ℕ} (v : Fin n → homogeneousSubmodule (Fin 4) K 3)
    (c : Fin n → K) (i : Fin n)
    (g : ChartRing
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i →+* K)
    (hgbase : g.comp (chartBaseMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i) =
        RingHom.id K)
    (hgcoord : ∀ j : Fin n,
      g (chartCoordinate
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i j) = c j) :
    ((tripleCompleteIntersectionUniversalCubic v).map
      (tripleCompleteIntersectionParameterChartCoefficientMap (K := K) i)).map g =
        ∑ j, C (c j) * (v j).1 := by
  rw [MvPolynomial.map_map,
    tripleCompleteIntersectionParameterChartCoefficientMap_comp i g]
  have hcomp :
      MvPolynomial.eval₂Hom
        (g.comp (chartBaseMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i))
        (fun j => g (chartCoordinate
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i j)) =
        MvPolynomial.eval₂Hom (RingHom.id K) c := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simpa [hgbase]
    · intro j
      simpa using hgcoord j
  rw [hcomp, tripleCompleteIntersectionUniversalCubic_map]
  apply Finset.sum_congr rfl
  intro j _
  rw [MvPolynomial.map_id]

/-- One étale member of a ground-field framed cubic system proves that the
actual projective singular-member locus is proper. -/
theorem tripleCubic_universalSingularParameterLocus_ne_univ_of_etale_member
    {n : ℕ} (p q r : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (hr : r.IsHomogeneous 3)
    (v : Fin n → homogeneousSubmodule (Fin 4) K 3)
    (c : Fin n → K) (i : Fin n) (hci : c i = 1)
    (hrc : r = ∑ j, C (c j) * (v j).1)
    (hEtale : Etale
      (toBase (tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr))) :
    tripleCompleteIntersectionUniversalSingularParameterLocus
      p q hp hq v ≠ Set.univ := by
  obtain ⟨g, hgbase, hgcoord⟩ :=
    exists_quadraticParameterChartHom_of_normalizedCoordinates c i hci
  have hpoly :
      ((tripleCompleteIntersectionUniversalCubic v).map
        (tripleCompleteIntersectionParameterChartCoefficientMap (K := K) i)).map g = r := by
    rw [tripleCubic_universalCubic_specialize_normalizedCoordinates
      v c i g hgbase hgcoord]
    exact hrc.symm
  have hpmap :
      p.map (g.comp (chartBaseMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)) = p := by
    rw [hgbase]
    exact MvPolynomial.map_id p
  have hqmap :
      q.map (g.comp (chartBaseMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)) = q := by
    rw [hgbase]
    exact MvPolynomial.map_id q
  have hEtaleFiber :
      Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal
        (p.map (g.comp (chartBaseMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)))
        (q.map (g.comp (chartBaseMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)))
        (((tripleCompleteIntersectionUniversalCubic v).map
          (tripleCompleteIntersectionParameterChartCoefficientMap (K := K) i)).map g)
        (hp.map _) (hq.map _)
        ((tripleCompleteIntersectionUniversalCubic_isHomogeneous v).map _ |>.map g))) := by
    have hIdeal :
        tripleCompleteIntersectionHomogeneousIdeal
          (p.map (g.comp (chartBaseMap
            (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)))
          (q.map (g.comp (chartBaseMap
            (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin n) K)) i)))
          (((tripleCompleteIntersectionUniversalCubic v).map
            (tripleCompleteIntersectionParameterChartCoefficientMap (K := K) i)).map g)
          (hp.map _) (hq.map _)
          ((tripleCompleteIntersectionUniversalCubic_isHomogeneous v).map _ |>.map g) =
        tripleCompleteIntersectionHomogeneousIdeal p q r hp hq hr := by
      apply HomogeneousIdeal.ext
      simp only [tripleCompleteIntersectionHomogeneousIdeal_toIdeal,
        tripleCompleteIntersectionIdeal, hpmap, hqmap, hpoly]
    rw [hIdeal]
    exact hEtale
  exact tripleCubic_universalSingularParameterLocus_ne_univ_of_etale_fiber
    p q hp hq v i g hEtaleFiber

/-- An étale intersection with one member of the canonical cubic
restriction-kernel basis proves the actual degree-ten bad locus proper. -/
theorem tripleCubic_restrictionKernelSingularParameterLocus_ne_univ_of_etale_basis_member
    {A : Type u} [CommRing A] [Algebra K A] [FiniteDimensional K A]
    (p q : MvPolynomial (Fin 4) K)
    (hp : p.IsHomogeneous 3) (hq : q.IsHomogeneous 3)
    (x : Fin 4 → A)
    (i : Fin (finrank K
      (LinearMap.ker (homogeneousSectionRestriction (K := K) x 3))))
    (hEtale : Etale (toBase (tripleCompleteIntersectionHomogeneousIdeal
      p q (cubicRestrictionKernelFrame (K := K) x i).1
      hp hq (cubicRestrictionKernelFrame (K := K) x i).2))) :
    tripleCompleteIntersectionRestrictionKernelSingularParameterLocus
      p q hp hq x ≠ Set.univ := by
  let v := cubicRestrictionKernelFrame (K := K) x
  let c : Fin (finrank K
      (LinearMap.ker (homogeneousSectionRestriction (K := K) x 3))) → K :=
    fun j => if j = i then 1 else 0
  have hci : c i = 1 := by simp [c]
  have hrepr : (v i).1 = ∑ j, C (c j) * (v j).1 := by
    classical
    simp [c]
  exact tripleCubic_universalSingularParameterLocus_ne_univ_of_etale_member
    p q (v i).1 hp hq (v i).2 v c i hci hrepr hEtale

end PfaffianDescent
