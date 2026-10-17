import PfaffianDescent.ProjectiveIntersectionPullback
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The zero homogeneous quotient is ambient projective space

The coordinate ring obtained by quotienting the homogeneous polynomial
ring by the zero ideal is the original polynomial ring. The equivalence
preserves grading and therefore identifies their projective schemes.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

private noncomputable abbrev zeroHomogeneousIdeal :
    HomogeneousIdeal (homogeneousSubmodule σ R) := ⊥

noncomputable def bottomCoordinateEquiv :
    CoordinateRing (zeroHomogeneousIdeal (R := R) (σ := σ)) ≃+*
      MvPolynomial σ R :=
  (Ideal.quotEquivOfEq (HomogeneousIdeal.toIdeal_bot
    (𝒜 := homogeneousSubmodule σ R))).trans
    (RingEquiv.quotientBot (MvPolynomial σ R))

theorem bottomCoordinateEquiv_mk (p : MvPolynomial σ R) :
    bottomCoordinateEquiv (R := R) (σ := σ)
      (Ideal.Quotient.mk (zeroHomogeneousIdeal (R := R) (σ := σ)).toIdeal p) = p := by
  simp only [bottomCoordinateEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, RingEquiv.quotientBot_mk]

noncomputable def bottomGradedInverse :
    grading (zeroHomogeneousIdeal (R := R) (σ := σ)) →+*ᵍ
      homogeneousSubmodule σ R where
  __ := (bottomCoordinateEquiv (R := R) (σ := σ)).toRingHom
  map_mem := by
    intro n x hx
    obtain ⟨p, hp, rfl⟩ := hx
    change bottomCoordinateEquiv (R := R) (σ := σ)
      (Ideal.Quotient.mk (zeroHomogeneousIdeal (R := R) (σ := σ)).toIdeal p) ∈
        homogeneousSubmodule σ R n
    rw [bottomCoordinateEquiv_mk]
    exact hp

theorem bottomGradedInverse_comp_quotient :
    (bottomGradedInverse (R := R) (σ := σ)).comp
      (quotientGradedRingHom (zeroHomogeneousIdeal (R := R) (σ := σ))) =
        GradedRingHom.id (homogeneousSubmodule σ R) := by
  apply GradedRingHom.ext
  intro p
  exact bottomCoordinateEquiv_mk p

theorem quotient_comp_bottomGradedInverse :
    (quotientGradedRingHom (zeroHomogeneousIdeal (R := R) (σ := σ))).comp
      (bottomGradedInverse (R := R) (σ := σ)) =
        GradedRingHom.id (grading (zeroHomogeneousIdeal (R := R) (σ := σ))) := by
  apply GradedRingHom.ext
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.Quotient.mk (zeroHomogeneousIdeal (R := R) (σ := σ)).toIdeal
    (bottomCoordinateEquiv (R := R) (σ := σ)
      (Ideal.Quotient.mk (zeroHomogeneousIdeal (R := R) (σ := σ)).toIdeal p)) = _
  rw [bottomCoordinateEquiv_mk]
  rfl

private theorem bottomGradedInverse_surjective :
    Function.Surjective (bottomGradedInverse (R := R) (σ := σ)) := by
  intro p
  refine ⟨(quotientGradedRingHom
    (zeroHomogeneousIdeal (R := R) (σ := σ))) p, ?_⟩
  exact DFunLike.congr_fun (bottomGradedInverse_comp_quotient (R := R) (σ := σ)) p

/-- The Proj of the zero homogeneous quotient is canonically ordinary
ambient projective space. -/
noncomputable def ambientBottomProjectiveIso :
    scheme (zeroHomogeneousIdeal (R := R) (σ := σ)) ≅
      Proj (homogeneousSubmodule σ R) := by
  let F := quotientGradedRingHom
    (zeroHomogeneousIdeal (R := R) (σ := σ))
  let G := bottomGradedInverse (R := R) (σ := σ)
  let hF := irrelevant_le_map_quotientGradedRingHom
    (zeroHomogeneousIdeal (R := R) (σ := σ))
  let hG := gradedSurjective_irrelevant_le G
    (bottomGradedInverse_surjective (R := R) (σ := σ))
  refine ⟨quotientProjMap _, Proj.map G hG, ?_, ?_⟩
  · change Proj.map F hF ≫ Proj.map G hG = 𝟙 _
    rw [← Proj.map_comp G F hG hF]
    simp only [F, G, quotient_comp_bottomGradedInverse]
    exact Proj.map_id
  · change Proj.map G hG ≫ Proj.map F hF = 𝟙 _
    rw [← Proj.map_comp F G hF hG]
    simp only [F, G, bottomGradedInverse_comp_quotient]
    exact Proj.map_id

theorem ambientBottomProjectiveIso_hom :
    (ambientBottomProjectiveIso (R := R) (σ := σ)).hom =
      quotientProjMap (zeroHomogeneousIdeal (R := R) (σ := σ)) :=
  rfl

/-- A projective homogeneous ideal sum is a scheme-theoretic
intersection inside ordinary ambient projective space. -/
theorem isPullback_projectiveIntersectionAmbient
    (I J : HomogeneousIdeal (homogeneousSubmodule σ R)) :
    IsPullback
      (schemeQuotientMap I (I ⊔ J)
        (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left))
      (schemeQuotientMap J (I ⊔ J)
        (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_right))
      (quotientProjMap I) (quotientProjMap J) := by
  apply (isPullback_projectiveIntersection I J).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (ambientBottomProjectiveIso (R := R) (σ := σ))
  · simp
  · simp
  · simpa only [Iso.refl_hom, Category.id_comp, ambientBottomProjectiveIso_hom] using
      schemeQuotientMap_comp_quotientProjMap
        (zeroHomogeneousIdeal (R := R) (σ := σ)) I (by exact bot_le)
  · simpa only [Iso.refl_hom, Category.id_comp, ambientBottomProjectiveIso_hom] using
      schemeQuotientMap_comp_quotientProjMap
        (zeroHomogeneousIdeal (R := R) (σ := σ)) J (by exact bot_le)

noncomputable def projectiveIntersectionAmbientIso
    (I J : HomogeneousIdeal (homogeneousSubmodule σ R)) :
    scheme (I ⊔ J) ≅ pullback (quotientProjMap I) (quotientProjMap J) :=
  (isPullback_projectiveIntersectionAmbient I J).isoPullback

theorem projectiveIntersectionAmbientIso_hom_fst
    (I J : HomogeneousIdeal (homogeneousSubmodule σ R)) :
    (projectiveIntersectionAmbientIso I J).hom ≫
      pullback.fst (quotientProjMap I) (quotientProjMap J) =
        schemeQuotientMap I (I ⊔ J)
          (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left) :=
  (isPullback_projectiveIntersectionAmbient I J).isoPullback_hom_fst

theorem projectiveIntersectionAmbientIso_hom_snd
    (I J : HomogeneousIdeal (homogeneousSubmodule σ R)) :
    (projectiveIntersectionAmbientIso I J).hom ≫
      pullback.snd (quotientProjMap I) (quotientProjMap J) =
        schemeQuotientMap J (I ⊔ J)
          (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_right) :=
  (isPullback_projectiveIntersectionAmbient I J).isoPullback_hom_snd

/-- The scheme cut out by two homogeneous equations is their actual
scheme-theoretic intersection in ambient projective space. -/
noncomputable def twoHypersurfaceIntersectionAmbientIso
    (p q : MvPolynomial σ R) {d e : ℕ}
    (hp : p.IsHomogeneous d) (hq : q.IsHomogeneous e) :
    scheme (equationIdeal p hp ⊔ equationIdeal q hq) ≅
      pullback (hypersurfaceToAmbient p hp) (hypersurfaceToAmbient q hq) :=
  projectiveIntersectionAmbientIso (equationIdeal p hp) (equationIdeal q hq)

end PfaffianDescent
