import PfaffianDescent.LinearHypersurfaceSection
import PfaffianDescent.ProjectiveSurjectionImage

namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
section
variable {K : Type u} [CommRing K] {m n d : ℕ}
attribute [local instance] MvPolynomial.gradedAlgebra
variable (M : Matrix (Fin m) (Fin n) K) (N : Matrix (Fin n) (Fin m) K) (hNM : N*M = 1)
    (f : MvPolynomial (Fin m) K) (hf : f.IsHomogeneous d)

/-- The linear equations expressing membership in the parametrized subspace. -/
noncomputable def linearSectionRelation (i : Fin m) : MvPolynomial (Fin m) K :=
  X i - rectangularSubstitution N (rectangularLinearCoordinate M i)

lemma linearSectionRelation_homogeneous (i : Fin m) :
    (linearSectionRelation M N i).IsHomogeneous 1 :=
  (isHomogeneous_X K i).sub
    (rectangularSubstitution_homogeneous N (rectangularLinearCoordinate_homogeneous M i))

/-- A point of the cubic lies in the actual linear-section image exactly when
its homogeneous prime contains the linear equations of that subspace. -/
theorem linearHypersurfaceSectionι_mem_range_iff (x : hypersurface f hf) :
    x ∈ Set.range (linearHypersurfaceSectionι M N hNM f hf) ↔
      ∀ i, Ideal.Quotient.mk (equationIdeal f hf).toIdeal (linearSectionRelation M N i) ∈
        x.asHomogeneousIdeal.toIdeal := by
  let I := equationIdeal f hf
  let J := equationIdeal (rectangularSubstitution M f) (rectangularSubstitution_homogeneous M hf)
  let G := polynomialQuotientGradingMap I J (rectangularSubstitution M)
    (linearSection_ideal_le M f hf) (fun _ _ hp => rectangularSubstitution_homogeneous M hp)
  have hG : Function.Surjective G := polynomialQuotientGradingMap_surjective _ _ _ _ _
    (rectangularSubstitution_surjective M N hNM)
  let x₀ : Proj (grading I) := x
  change x₀ ∈ Set.range (Proj.map G (gradedSurjective_irrelevant_le G hG)) ↔
    ∀ i, Ideal.Quotient.mk I.toIdeal (linearSectionRelation M N i) ∈ x₀.asHomogeneousIdeal.toIdeal
  rw [projectiveMap_mem_range_iff G hG]
  have hcomp : (rectangularSubstitution M).comp (rectangularSubstitution N) = AlgHom.id K _ := by
    rw [rectangularSubstitution_comp, hNM, rectangularSubstitution_one]
  constructor
  · intro hx i
    apply hx
    change Ideal.Quotient.mk J.toIdeal (rectangularSubstitution M (linearSectionRelation M N i)) = 0
    have he := AlgHom.congr_fun hcomp (rectangularLinearCoordinate M i)
    change rectangularSubstitution M (rectangularSubstitution N (rectangularLinearCoordinate M i)) =
      rectangularLinearCoordinate M i at he
    rw [linearSectionRelation, map_sub, rectangularSubstitution_X, he, sub_self, map_zero]
  · intro hx
    let P := x₀.asHomogeneousIdeal.toIdeal
    let k : MvPolynomial (Fin m) K →ₐ[K] (CoordinateRing I ⧸ P) :=
      (Ideal.Quotient.mkₐ K P).comp (Ideal.Quotient.mkₐ K I.toIdeal)
    let t := k.comp (rectangularSubstitution N)
    have ht : t.comp (rectangularSubstitution M) = k := by
      apply MvPolynomial.algHom_ext
      intro i
      have hi : k (linearSectionRelation M N i) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (hx i)
      change k (X i - rectangularSubstitution N (rectangularLinearCoordinate M i)) = 0 at hi
      rw [map_sub, sub_eq_zero] at hi
      change k (rectangularSubstitution N (rectangularSubstitution M (X i))) = k (X i)
      rw [rectangularSubstitution_X]
      exact hi.symm
    have hkf : k f = 0 := by
      change Ideal.Quotient.mk P (Ideal.Quotient.mk I.toIdeal f) = 0
      have hz : Ideal.Quotient.mk I.toIdeal f = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (show f ∈ I.toIdeal from
          Ideal.subset_span (Set.mem_singleton f))
      rw [hz, map_zero]
    have hJ : J.toIdeal ≤ RingHom.ker t.toRingHom := by
      change Ideal.span {rectangularSubstitution M f} ≤ _
      apply Ideal.span_le.mpr
      intro p hp
      obtain rfl := Set.mem_singleton_iff.mp hp
      change t (rectangularSubstitution M f) = 0
      exact (AlgHom.congr_fun ht f).trans hkf
    intro a ha
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
    change Ideal.Quotient.mk J.toIdeal (rectangularSubstitution M p) = 0 at ha
    have hz : t (rectangularSubstitution M p) = 0 :=
      hJ (Ideal.Quotient.eq_zero_iff_mem.mp ha)
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact (AlgHom.congr_fun ht p).symm.trans hz

end
end PfaffianDescent
