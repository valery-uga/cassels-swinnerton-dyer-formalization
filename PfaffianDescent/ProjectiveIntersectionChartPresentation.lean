import PfaffianDescent.QuotientSupPushout
import AllCharacteristics.AffineChartPresentation
import PfaffianDescent.HomogeneousQuotientMap
import PfaffianDescent.QuotientChartKernel
import PfaffianDescent.SurjectiveQuotientPushout

/-!
# Polynomial presentations of projective intersection charts

The chart presentation of a sum of homogeneous ideals is the sum of the
individual chart-presentation ideals. Thus the corresponding polynomial
quotient rings form an affine pushout, and their spectra form a pullback.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem chartPresentationIdeal_sup
    (I J : HomogeneousIdeal (homogeneousSubmodule σ R)) (j : σ) :
    chartPresentationIdeal (I ⊔ J) j =
      chartPresentationIdeal I j ⊔ chartPresentationIdeal J j := by
  simp only [chartPresentationIdeal, HomogeneousIdeal.toIdeal_sup]
  ac_rfl

/-- On an actual affine chart of projective space, the equations of the
scheme-theoretic intersection have exactly the sum of the two quotient-map
kernels. -/
theorem chartQuotientMap_ker_sup
    (I J : HomogeneousIdeal (homogeneousSubmodule σ R)) (j : σ) :
    RingHom.ker (chartQuotientMap (⊥ : HomogeneousIdeal (homogeneousSubmodule σ R))
      (I ⊔ J) (by exact bot_le) j) =
      RingHom.ker (chartQuotientMap (⊥ : HomogeneousIdeal (homogeneousSubmodule σ R))
        I (by exact bot_le) j) ⊔
      RingHom.ker (chartQuotientMap (⊥ : HomogeneousIdeal (homogeneousSubmodule σ R))
        J (by exact bot_le) j) := by
  rw [chartQuotientMap_ker_eq_presentationImage,
    chartQuotientMap_ker_eq_presentationImage,
    chartQuotientMap_ker_eq_presentationImage,
    chartPresentationIdeal_sup, Ideal.map_sup]

/-- The actual coordinate chart of a projective scheme-theoretic
intersection is the pushout of the two quotient-chart rings over the
ambient projective chart ring. -/
theorem isPushout_projectiveIntersectionChart
    (I J : HomogeneousIdeal (homogeneousSubmodule σ R)) (j : σ) :
    IsPushout
      (CommRingCat.ofHom (chartQuotientMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule σ R)) I (by exact bot_le) j))
      (CommRingCat.ofHom (chartQuotientMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule σ R)) J (by exact bot_le) j))
      (CommRingCat.ofHom (chartQuotientMap I (I ⊔ J)
        (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left) j))
      (CommRingCat.ofHom (chartQuotientMap J (I ⊔ J)
        (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_right) j)) := by
  let f := chartQuotientMap
    (⊥ : HomogeneousIdeal (homogeneousSubmodule σ R)) I (by exact bot_le) j
  let g := chartQuotientMap
    (⊥ : HomogeneousIdeal (homogeneousSubmodule σ R)) J (by exact bot_le) j
  let l := chartQuotientMap I (I ⊔ J)
    (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left) j
  let r := chartQuotientMap J (I ⊔ J)
    (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_right) j
  have hc : l.comp f = r.comp g := by
    calc
      l.comp f = chartQuotientMap
          (⊥ : HomogeneousIdeal (homogeneousSubmodule σ R))
          (I ⊔ J) (by exact bot_le) j :=
        chartQuotientMap_comp _ _ _ _ _ _ _
      _ = r.comp g := (chartQuotientMap_comp _ _ _ _ _ _ _).symm
  have hk : RingHom.ker (l.comp f) = RingHom.ker f ⊔ RingHom.ker g := by
    rw [show l.comp f = chartQuotientMap
      (⊥ : HomogeneousIdeal (homogeneousSubmodule σ R))
      (I ⊔ J) (by exact bot_le) j from
        chartQuotientMap_comp _ _ _ _ _ _ _]
    exact chartQuotientMap_ker_sup I J j
  exact isPushout_of_surjective_ker_sup f g l r
    (chartQuotientMap_surjective _ _ _ j)
    (chartQuotientMap_surjective _ _ _ j)
    (chartQuotientMap_surjective _ _ _ j) hc hk

/-- The standard affine chart of the projective intersection is the
scheme-theoretic fibre product of the corresponding actual affine charts. -/
theorem isPullback_projectiveIntersectionChart
    (I J : HomogeneousIdeal (homogeneousSubmodule σ R)) (j : σ) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (chartQuotientMap I (I ⊔ J)
        (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left) j)))
      (Spec.map (CommRingCat.ofHom (chartQuotientMap J (I ⊔ J)
        (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_right) j)))
      (Spec.map (CommRingCat.ofHom (chartQuotientMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule σ R)) I (by exact bot_le) j)))
      (Spec.map (CommRingCat.ofHom (chartQuotientMap
        (⊥ : HomogeneousIdeal (homogeneousSubmodule σ R)) J (by exact bot_le) j))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _
    (isPushout_projectiveIntersectionChart I J j)

/-- Passing from polynomial chart presentations to actual projective
charts commutes with a homogeneous quotient. -/
theorem chartPresentationEquiv_natural
    (I J : HomogeneousIdeal (homogeneousSubmodule σ R))
    (hIJ : I.toIdeal ≤ J.toIdeal) (j : σ) :
    (chartPresentationEquiv J j).toRingHom.comp
        (Ideal.Quotient.factor
          (show chartPresentationIdeal I j ≤ chartPresentationIdeal J j by
            exact sup_le_sup_right hIJ _)) =
      (chartQuotientMap I J hIJ j).comp
        (chartPresentationEquiv I j).toRingHom := by
  apply RingHom.ext
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [RingHom.comp_apply, Ideal.Quotient.factor_mk]
  exact (chartQuotientMap_eval₂ I J hIJ j p).symm

/-- The polynomial quotient presentations of two projective closed
subschemes intersect by an actual affine fibre product on each standard
coordinate chart. -/
theorem isPullback_spec_chartPresentationSup
    (I J : HomogeneousIdeal (homogeneousSubmodule σ R)) (j : σ) :
    IsPullback
      (Spec.map (quotientSupFromLeft (chartPresentationIdeal I j)
        (chartPresentationIdeal J j)))
      (Spec.map (quotientSupFromRight (chartPresentationIdeal I j)
        (chartPresentationIdeal J j)))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (chartPresentationIdeal I j))))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (chartPresentationIdeal J j)))) :=
  isPullback_spec_quotientSup (chartPresentationIdeal I j)
    (chartPresentationIdeal J j)

end PfaffianDescent
