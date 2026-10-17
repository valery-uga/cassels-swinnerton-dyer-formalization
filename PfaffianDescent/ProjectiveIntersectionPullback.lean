import PfaffianDescent.ProjectiveIntersectionChartPresentation

/-!
# Projective scheme intersections as pullbacks

The homogeneous ideal sum presents the global scheme-theoretic
intersection. We glue the actual affine chart pullback squares using
the exact inverse-image formulas for homogeneous quotient morphisms.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem isPullback_projectiveIntersection
    (I J : HomogeneousIdeal (homogeneousSubmodule σ R)) :
    IsPullback
      (schemeQuotientMap I (I ⊔ J)
        (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left))
      (schemeQuotientMap J (I ⊔ J)
        (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_right))
      (schemeQuotientMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule σ R)) I (by exact bot_le))
      (schemeQuotientMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule σ R)) J (by exact bot_le)) := by
  apply Scheme.isPullback_of_openCover _ _ _ _ (coordinateOpenCover I).openCover
  intro j
  change σ at j
  change IsPullback
    (pullback.snd (schemeQuotientMap I (I ⊔ J)
      (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left)) (chartι I j))
    (pullback.fst (schemeQuotientMap I (I ⊔ J)
      (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left)) (chartι I j) ≫
      schemeQuotientMap J (I ⊔ J)
        (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_right))
    (chartι I j ≫ schemeQuotientMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule σ R)) I (by exact bot_le))
    (schemeQuotientMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule σ R)) J (by exact bot_le))
  let hI : I.toIdeal ≤ (I ⊔ J).toIdeal := by
    rw [HomogeneousIdeal.toIdeal_sup]
    exact le_sup_left
  let hJ : J.toIdeal ≤ (I ⊔ J).toIdeal := by
    rw [HomogeneousIdeal.toIdeal_sup]
    exact le_sup_right
  have hc := (isPullback_schemeQuotientMap_chart I (I ⊔ J) hI j).flip
  have hb := isPullback_projectiveIntersectionChart I J j
  have hj := isPullback_schemeQuotientMap_chart
    (⊥ : HomogeneousIdeal (homogeneousSubmodule σ R)) J (by exact bot_le) j
  have hlocal := hb.paste_vert hj
  rw [← chartι_schemeQuotientMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule σ R)) I (by exact bot_le) j,
    ← chartι_schemeQuotientMap J (I ⊔ J) hJ j] at hlocal
  apply hlocal.of_iso hc.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simpa only [Iso.refl_hom, Category.comp_id] using hc.isoPullback_hom_snd.symm
  · simpa only [Iso.refl_hom, Category.comp_id, Category.assoc] using
      congrArg (fun a ↦ a ≫ schemeQuotientMap J (I ⊔ J) hJ)
        hc.isoPullback_hom_fst.symm
  · simp
  · simp

/-- The projective scheme defined by the sum of two homogeneous ideals is
canonically the fibre product of their closed subschemes inside the same
ambient projective scheme. -/
noncomputable def projectiveIntersectionIso
    (I J : HomogeneousIdeal (homogeneousSubmodule σ R)) :
    scheme (I ⊔ J) ≅
      pullback
        (schemeQuotientMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule σ R)) I (by exact bot_le))
        (schemeQuotientMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule σ R)) J (by exact bot_le)) :=
  (isPullback_projectiveIntersection I J).isoPullback

theorem projectiveIntersectionIso_hom_fst
    (I J : HomogeneousIdeal (homogeneousSubmodule σ R)) :
    (projectiveIntersectionIso I J).hom ≫
      pullback.fst
        (schemeQuotientMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule σ R)) I (by exact bot_le))
        (schemeQuotientMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule σ R)) J (by exact bot_le)) =
      schemeQuotientMap I (I ⊔ J)
        (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left) :=
  (isPullback_projectiveIntersection I J).isoPullback_hom_fst

theorem projectiveIntersectionIso_hom_snd
    (I J : HomogeneousIdeal (homogeneousSubmodule σ R)) :
    (projectiveIntersectionIso I J).hom ≫
      pullback.snd
        (schemeQuotientMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule σ R)) I (by exact bot_le))
        (schemeQuotientMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule σ R)) J (by exact bot_le)) =
      schemeQuotientMap J (I ⊔ J)
        (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_right) :=
  (isPullback_projectiveIntersection I J).isoPullback_hom_snd

end PfaffianDescent
