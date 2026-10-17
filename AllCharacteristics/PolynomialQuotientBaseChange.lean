import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Coefficient base change of polynomial quotients

Mapping the coefficients and the defining ideal produces a categorical
pushout of rings, and hence the actual pullback of affine schemes. No
flatness, finiteness, or surjectivity assumption is needed on the coefficient
map.
-/

open MvPolynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AllCharacteristics
namespace PolynomialQuotient
universe u
variable {R S : Type u} {σ : Type} [CommRing R] [CommRing S]

/-- Coefficients in a polynomial quotient. -/
noncomputable def baseMap (I : Ideal (MvPolynomial σ R)) : R →+* MvPolynomial σ R ⧸ I :=
  (Ideal.Quotient.mk I).comp C

/-- The quotient map induced by a change of coefficients. -/
noncomputable def coefficientMap (f : R →+* S) (I : Ideal (MvPolynomial σ R)) :
    (MvPolynomial σ R ⧸ I) →+* (MvPolynomial σ S ⧸ I.map (MvPolynomial.map f)) :=
  Ideal.quotientMap _ (MvPolynomial.map f) (Ideal.le_comap_map)

/-- Coefficient change maps the class of a polynomial to the class of its
coefficient image. -/
theorem coefficientMap_mk (f : R →+* S) (I : Ideal (MvPolynomial σ R))
    (p : MvPolynomial σ R) :
    coefficientMap f I (Ideal.Quotient.mk I p) =
      Ideal.Quotient.mk (I.map (MvPolynomial.map f)) (p.map f) :=
  Ideal.quotientMap_mk

/-- The square of coefficient maps and polynomial quotients commutes. -/
theorem coefficientMap_baseMap (f : R →+* S) (I : Ideal (MvPolynomial σ R)) :
    (coefficientMap f I).comp (baseMap I) =
      (baseMap (I.map (MvPolynomial.map f))).comp f := by
  ext r
  change coefficientMap f I (Ideal.Quotient.mk I (C r)) = _
  rw [coefficientMap_mk, map_C]
  rfl

/-- Polynomial evaluation over the changed coefficients agrees with an
existing homomorphism on the original quotient. -/
theorem eval_map_of_compatible {T : Type u} [CommRing T]
    (f : R →+* S) (I : Ideal (MvPolynomial σ R))
    (a : (MvPolynomial σ R ⧸ I) →+* T) (b : S →+* T)
    (h : a.comp (baseMap I) = b.comp f) (p : MvPolynomial σ R) :
    (p.map f).eval₂ b (fun i ↦ a (Ideal.Quotient.mk I (X i))) =
      a (Ideal.Quotient.mk I p) := by
  have he : (eval₂Hom b (fun i ↦ a (Ideal.Quotient.mk I (X i)))).comp
      (MvPolynomial.map f) = a.comp (Ideal.Quotient.mk I) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, map_C, eval₂Hom_C]
      exact (DFunLike.congr_fun h r).symm
    · intro i
      simp only [RingHom.comp_apply, map_X, eval₂Hom_X']
  exact DFunLike.congr_fun he p

/-- A compatible pair of homomorphisms descends to the quotient after
coefficient change. -/
noncomputable def desc {T : Type u} [CommRing T]
    (f : R →+* S) (I : Ideal (MvPolynomial σ R))
    (a : (MvPolynomial σ R ⧸ I) →+* T) (b : S →+* T)
    (h : a.comp (baseMap I) = b.comp f) :
    (MvPolynomial σ S ⧸ I.map (MvPolynomial.map f)) →+* T :=
  Ideal.Quotient.lift _ (eval₂Hom b (fun i ↦ a (Ideal.Quotient.mk I (X i)))) (by
    change I.map (MvPolynomial.map f) ≤
      RingHom.ker (eval₂Hom b (fun i ↦ a (Ideal.Quotient.mk I (X i))))
    apply Ideal.map_le_iff_le_comap.mpr
    intro p hp
    change (p.map f).eval₂ b (fun i ↦ a (Ideal.Quotient.mk I (X i))) = 0
    rw [eval_map_of_compatible f I a b h, Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero])

/-- The descended homomorphism agrees with the original quotient map. -/
theorem desc_coefficientMap {T : Type u} [CommRing T]
    (f : R →+* S) (I : Ideal (MvPolynomial σ R))
    (a : (MvPolynomial σ R ⧸ I) →+* T) (b : S →+* T)
    (h : a.comp (baseMap I) = b.comp f) :
    (desc f I a b h).comp (coefficientMap f I) = a := by
  apply RingHom.ext
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  change desc f I a b h (coefficientMap f I (Ideal.Quotient.mk I p)) = _
  rw [coefficientMap_mk]
  exact eval_map_of_compatible f I a b h p

/-- The descended homomorphism agrees with the new coefficient map. -/
theorem desc_baseMap {T : Type u} [CommRing T]
    (f : R →+* S) (I : Ideal (MvPolynomial σ R))
    (a : (MvPolynomial σ R ⧸ I) →+* T) (b : S →+* T)
    (h : a.comp (baseMap I) = b.comp f) :
    (desc f I a b h).comp (baseMap (I.map (MvPolynomial.map f))) = b := by
  ext s
  exact eval₂_C b (fun i ↦ a (Ideal.Quotient.mk I (X i))) s

/-- The two inclusions determine a homomorphism out of the changed quotient. -/
theorem hom_ext {T : Type u} [CommRing T]
    (f : R →+* S) (I : Ideal (MvPolynomial σ R))
    (a b : (MvPolynomial σ S ⧸ I.map (MvPolynomial.map f)) →+* T)
    (h₁ : a.comp (coefficientMap f I) = b.comp (coefficientMap f I))
    (h₂ : a.comp (baseMap (I.map (MvPolynomial.map f))) =
      b.comp (baseMap (I.map (MvPolynomial.map f)))) : a = b := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro s
    exact DFunLike.congr_fun h₂ s
  · intro i
    have h := DFunLike.congr_fun h₁ (Ideal.Quotient.mk I (X i))
    simpa only [RingHom.comp_apply, coefficientMap_mk, map_X] using h

/-- Polynomial quotient formation commutes with every coefficient change as
an actual categorical pushout of rings. -/
theorem isPushout (f : R →+* S) (I : Ideal (MvPolynomial σ R)) :
    IsPushout (CommRingCat.ofHom (baseMap I)) (CommRingCat.ofHom f)
      (CommRingCat.ofHom (coefficientMap f I))
      (CommRingCat.ofHom (baseMap (I.map (MvPolynomial.map f)))) where
  w := CommRingCat.hom_ext (coefficientMap_baseMap f I)
  isColimit' := ⟨PushoutCocone.isColimitAux' _ (fun c ↦ by
    have hc : c.inl.hom.comp (baseMap I) = c.inr.hom.comp f :=
      congrArg CommRingCat.Hom.hom c.condition
    refine ⟨CommRingCat.ofHom (desc f I c.inl.hom c.inr.hom hc), ?_, ?_, ?_⟩
    · exact CommRingCat.hom_ext (desc_coefficientMap f I c.inl.hom c.inr.hom hc)
    · exact CommRingCat.hom_ext (desc_baseMap f I c.inl.hom c.inr.hom hc)
    · intro m hm₁ hm₂
      apply CommRingCat.hom_ext
      apply hom_ext f I
      · exact (congrArg CommRingCat.Hom.hom hm₁).trans
          (desc_coefficientMap f I c.inl.hom c.inr.hom hc).symm
      · exact (congrArg CommRingCat.Hom.hom hm₂).trans
          (desc_baseMap f I c.inl.hom c.inr.hom hc).symm)⟩

/-- The spectrum of the coefficient-changed quotient is the actual affine
scheme base change. -/
theorem isPullback_spec (f : R →+* S) (I : Ideal (MvPolynomial σ R)) :
    IsPullback (Spec.map (CommRingCat.ofHom (coefficientMap f I)))
      (Spec.map (CommRingCat.ofHom (baseMap (I.map (MvPolynomial.map f)))))
      (Spec.map (CommRingCat.ofHom (baseMap I))) (Spec.map (CommRingCat.ofHom f)) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout f I)

end PolynomialQuotient
end AllCharacteristics
