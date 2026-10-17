import PfaffianDescent.AmbientBottomProjectiveIso
import AllCharacteristics.AmbientProjectiveBaseChange
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono

/-!
# The base-changed ambient projective space inside the ordinary product

The coefficient-changed projective space is the pullback over the original
coefficient spectrum. Its natural map to the ordinary product of projective
space and the new coefficient spectrum is a monomorphism. Consequently,
intersections over this base-changed ambient space remain intersections
after both maps are composed with its product embedding.
-/

namespace PfaffianDescent

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u

/-- Postcomposing the two maps into a pullback base by a monomorphism
does not change the pullback square. -/
theorem IsPullback.postcomp_mono
    {P X Y Z W : Scheme.{u}}
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback a b f g) (i : Z ⟶ W) [Mono i] :
    IsPullback a b (f ≫ i) (g ≫ i) :=
  IsPullback.of_isLimit
    (PullbackCone.isLimitOfCompMono f g i (PullbackCone.mk a b h.w) h.isLimit)

variable {K S : Type u} [CommRing K] [CommRing S]
  (b : K →+* S) (σ : Type)
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The ambient projective coefficient base change, viewed in the ordinary
product rather than the fibre product over `Spec K`. -/
noncomputable def ambientCoefficientToProduct :
    Proj (homogeneousSubmodule σ S) ⟶
      Proj (homogeneousSubmodule σ K) ⨯ Spec (.of S) :=
  prod.lift (ambientCoefficientMap (σ := σ) b)
    (ambientToBase (R := S) (σ := σ))

instance ambientCoefficientToProduct_mono :
    Mono (ambientCoefficientToProduct b σ) := by
  let h := isPullback_ambientCoefficientMap (σ := σ) b
  let e := h.isoPullback
  have he : ambientCoefficientToProduct b σ =
      e.hom ≫ prod.lift
        (pullback.fst (ambientToBase (R := K) (σ := σ))
          (Spec.map (CommRingCat.ofHom b)))
        (pullback.snd (ambientToBase (R := K) (σ := σ))
          (Spec.map (CommRingCat.ofHom b))) := by
    apply prod.hom_ext
    · simpa only [ambientCoefficientToProduct, Category.assoc, prod.lift_fst] using
        h.isoPullback_hom_fst.symm
    · simpa only [ambientCoefficientToProduct, Category.assoc, prod.lift_snd] using
        h.isoPullback_hom_snd.symm
  rw [he]
  infer_instance

theorem quotientProjMap_comp_ambientCoefficientToProduct
    (I : HomogeneousIdeal (homogeneousSubmodule σ S)) :
    quotientProjMap I ≫ ambientCoefficientToProduct b σ =
      prod.lift
        (quotientProjMap I ≫ ambientCoefficientMap (σ := σ) b)
        (toBase I) := by
  apply prod.hom_ext
  · simp only [Category.assoc, ambientCoefficientToProduct, prod.lift_fst]
  · simp only [Category.assoc, ambientCoefficientToProduct, prod.lift_snd]
    exact quotientProjMap_toBase I

/-- A projective intersection remains a pullback when both closed
subschemes are regarded inside the ordinary product of the original
ambient projective space and the new coefficient spectrum. -/
theorem isPullback_projectiveIntersectionCoefficientProduct
    (I J : HomogeneousIdeal (homogeneousSubmodule σ S)) :
    IsPullback
      (schemeQuotientMap I (I ⊔ J)
        (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left))
      (schemeQuotientMap J (I ⊔ J)
        (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_right))
      (prod.lift
        (quotientProjMap I ≫ ambientCoefficientMap (σ := σ) b)
        (toBase I))
      (prod.lift
        (quotientProjMap J ≫ ambientCoefficientMap (σ := σ) b)
        (toBase J)) := by
  rw [← quotientProjMap_comp_ambientCoefficientToProduct b σ I,
    ← quotientProjMap_comp_ambientCoefficientToProduct b σ J]
  exact PfaffianDescent.IsPullback.postcomp_mono
    (isPullback_projectiveIntersectionAmbient I J)
    (ambientCoefficientToProduct b σ)

noncomputable def projectiveIntersectionCoefficientProductIso
    (I J : HomogeneousIdeal (homogeneousSubmodule σ S)) :
    scheme (I ⊔ J) ≅
      pullback
        (prod.lift
          (quotientProjMap I ≫ ambientCoefficientMap (σ := σ) b)
          (toBase I))
        (prod.lift
          (quotientProjMap J ≫ ambientCoefficientMap (σ := σ) b)
          (toBase J)) :=
  (isPullback_projectiveIntersectionCoefficientProduct b σ I J).isoPullback

/-- The inverse intersection comparison projects to the first closed
subscheme by its canonical homogeneous quotient map. -/
theorem projectiveIntersectionCoefficientProductIso_inv_fst
    (I J : HomogeneousIdeal (homogeneousSubmodule σ S)) :
    (projectiveIntersectionCoefficientProductIso b σ I J).inv ≫
      schemeQuotientMap I (I ⊔ J)
        (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left) =
      pullback.fst
        (prod.lift
          (quotientProjMap I ≫ ambientCoefficientMap (σ := σ) b)
          (toBase I))
        (prod.lift
          (quotientProjMap J ≫ ambientCoefficientMap (σ := σ) b)
          (toBase J)) := by
  let e := projectiveIntersectionCoefficientProductIso b σ I J
  have h := congrArg (fun g => e.inv ≫ g)
    (isPullback_projectiveIntersectionCoefficientProduct b σ I J).isoPullback_hom_fst
  simpa only [e, projectiveIntersectionCoefficientProductIso,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp] using h.symm

/-- The concrete projective-intersection comparison respects the map to
the coefficient spectrum. -/
theorem projectiveIntersectionCoefficientProductIso_hom_toBase
    (I J : HomogeneousIdeal (homogeneousSubmodule σ S)) :
    (projectiveIntersectionCoefficientProductIso b σ I J).hom ≫
      pullback.fst
        (prod.lift
          (quotientProjMap I ≫ ambientCoefficientMap (σ := σ) b)
          (toBase I))
        (prod.lift
          (quotientProjMap J ≫ ambientCoefficientMap (σ := σ) b)
          (toBase J)) ≫ toBase I =
      toBase (I ⊔ J) := by
  calc
    _ = schemeQuotientMap I (I ⊔ J)
          (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left) ≫
        toBase I := by
          simpa only [projectiveIntersectionCoefficientProductIso,
            Category.assoc] using
            congrArg (· ≫ toBase I)
              ((isPullback_projectiveIntersectionCoefficientProduct b σ I J).isoPullback_hom_fst)
    _ = _ := schemeQuotientMap_toBase I (I ⊔ J)
      (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left)

/-- The inverse comparison also preserves the coefficient-spectrum map. -/
theorem projectiveIntersectionCoefficientProductIso_inv_toBase
    (I J : HomogeneousIdeal (homogeneousSubmodule σ S)) :
    (projectiveIntersectionCoefficientProductIso b σ I J).inv ≫
      toBase (I ⊔ J) =
      pullback.fst
        (prod.lift
          (quotientProjMap I ≫ ambientCoefficientMap (σ := σ) b)
          (toBase I))
        (prod.lift
          (quotientProjMap J ≫ ambientCoefficientMap (σ := σ) b)
          (toBase J)) ≫ toBase I := by
  let e := projectiveIntersectionCoefficientProductIso b σ I J
  have h := congrArg (fun g => e.inv ≫ g)
    (projectiveIntersectionCoefficientProductIso_hom_toBase b σ I J).symm
  simpa only [e, ← Category.assoc, Iso.inv_hom_id,
    Category.id_comp] using h

/-- Two concrete hypersurfaces over `S` intersect in the projective
scheme of their summed equations even when embedded into ambient
projective space over `K` times `Spec S`. -/
noncomputable def twoHypersurfaceCoefficientProductIso
    (p q : MvPolynomial σ S) {d e : ℕ}
    (hp : p.IsHomogeneous d) (hq : q.IsHomogeneous e) :
    scheme (equationIdeal p hp ⊔ equationIdeal q hq) ≅
      pullback
        (prod.lift
          (hypersurfaceToAmbient p hp ≫ ambientCoefficientMap (σ := σ) b)
          (hypersurfaceToBase p hp))
        (prod.lift
          (hypersurfaceToAmbient q hq ≫ ambientCoefficientMap (σ := σ) b)
          (hypersurfaceToBase q hq)) :=
  projectiveIntersectionCoefficientProductIso b σ
    (equationIdeal p hp) (equationIdeal q hq)

end PfaffianDescent
