import AllCharacteristics.ProjectiveSmoothClassifyingMap
import AllCharacteristics.FiniteSubschemeFromImmersion

/-!
# Finite subschemes on the actual universal smooth hypersurface

A smooth field equation has a coefficient-independent point of the projective
smooth parameter space. Its hypersurface identifies with the fiber used by
the relative subscheme functor. Every finite flat embedded subscheme of a
specified rank therefore supplies an actual datum on that universal fiber,
with the original embedded scheme and its field structure map preserved.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Opposite
namespace AllCharacteristics
namespace UniversalHomogeneous
open HomogeneousProjective
universe u
variable {R k : Type u} [CommRing R] [IsNoetherianRing R] [Field k]
variable {σ : Type} [Finite σ] {d : ℕ}
variable (p : MvPolynomial σ k) (hp : p.IsHomogeneous d) (hne : p ≠ 0) (b : R →+* k)
variable [Smooth (hypersurfaceToBase p hp)]

/-- The original hypersurface is the universal fiber with the orientation
used by the relative subscheme functor. -/
noncomputable def projectiveSmoothClassifyingOverFiberIso :
    hypersurface p hp ≅
      (relativeFamilyFunctor (projectiveSmoothFamilyToBase R σ d)).obj
        (Over.mk (projectiveSmoothClassifyingMap p hp hne b)) :=
  by
    change hypersurface p hp ≅ pullback (projectiveSmoothClassifyingMap p hp hne b)
      (projectiveSmoothFamilyToBase R σ d)
    exact projectiveSmoothClassifyingFiberIso p hp hne b ≪≫
      pullbackSymmetry (projectiveSmoothFamilyToBase R σ d)
        (projectiveSmoothClassifyingMap p hp hne b)

/-- The oriented universal-fiber identification is over the coefficient field. -/
theorem projectiveSmoothClassifyingOverFiberIso_hom_fst :
    (projectiveSmoothClassifyingOverFiberIso p hp hne b).hom ≫
      (relativeFamilyProjection (projectiveSmoothFamilyToBase R σ d)).app
        (Over.mk (projectiveSmoothClassifyingMap p hp hne b)) = hypersurfaceToBase p hp := by
  change ((projectiveSmoothClassifyingFiberIso p hp hne b).hom ≫
    (pullbackSymmetry (projectiveSmoothFamilyToBase R σ d)
      (projectiveSmoothClassifyingMap p hp hne b)).hom) ≫
      pullback.fst (projectiveSmoothClassifyingMap p hp hne b)
        (projectiveSmoothFamilyToBase R σ d) = hypersurfaceToBase p hp
  rw [Category.assoc, pullbackSymmetry_hom_comp_fst,
    projectiveSmoothClassifyingFiberIso_hom_snd]

variable {Z : Scheme.{u}} (i : Z ⟶ hypersurface p hp) [hi : IsClosedImmersion i]
variable [hfin : IsFinite (i ≫ hypersurfaceToBase p hp)]
variable [hflat : Flat (i ≫ hypersurfaceToBase p hp)]
variable [hlfp : LocallyOfFinitePresentation (i ≫ hypersurfaceToBase p hp)]
variable (n : ℕ) (hn : ∀ s : Spec (.of k), (i ≫ hypersurfaceToBase p hp).finrank s = n)

/-- An embedded finite subscheme on a smooth equation defines a datum on the
actual pulled-back universal family, of exactly the original rank. -/
noncomputable def projectiveFiniteSubschemeParameter :
    (finiteSubschemeFunctor (projectiveSmoothFamilyToBase R σ d) n).obj
      (op (Over.mk (projectiveSmoothClassifyingMap p hp hne b))) := by
  let e := projectiveSmoothClassifyingOverFiberIso p hp hne b
  let q := (relativeFamilyProjection (projectiveSmoothFamilyToBase R σ d)).app
    (Over.mk (projectiveSmoothClassifyingMap p hp hne b))
  have hc : (i ≫ e.hom) ≫ q = i ≫ hypersurfaceToBase p hp := by
    rw [Category.assoc, projectiveSmoothClassifyingOverFiberIso_hom_fst]
    rfl
  have : IsFinite ((i ≫ e.hom) ≫ q) := by rw [hc]; exact hfin
  have : Flat ((i ≫ e.hom) ≫ q) := by rw [hc]; exact hflat
  have : LocallyOfFinitePresentation ((i ≫ e.hom) ≫ q) := by rw [hc]; exact hlfp
  exact finiteSubschemeDatumOfClosedImmersion (i ≫ e.hom) q n (by rw [hc]; exact hn)

/-- The universal datum is cut out by the kernel of the original immersion
transported to the universal fiber. -/
theorem projectiveFiniteSubschemeParameter_ideal :
    (projectiveFiniteSubschemeParameter p hp hne b i n hn).val =
      (i ≫ (projectiveSmoothClassifyingOverFiberIso p hp hne b).hom).ker := rfl

include hi

/-- The original finite subscheme is the actual closed subscheme of its
universal finite-subscheme datum. -/
noncomputable def projectiveFiniteSubschemeParameterIso :
    Z ≅ (projectiveFiniteSubschemeParameter p hp hne b i n hn).val.subscheme :=
  by
    change Z ≅ (i ≫ (projectiveSmoothClassifyingOverFiberIso p hp hne b).hom).image
    exact asIso (i ≫ (projectiveSmoothClassifyingOverFiberIso p hp hne b).hom).toImage

/-- The identification with the universal datum preserves the embedding. -/
theorem projectiveFiniteSubschemeParameterIso_hom_ι :
    (projectiveFiniteSubschemeParameterIso p hp hne b i n hn).hom ≫
      (projectiveFiniteSubschemeParameter p hp hne b i n hn).val.subschemeι =
        i ≫ (projectiveSmoothClassifyingOverFiberIso p hp hne b).hom :=
  (i ≫ (projectiveSmoothClassifyingOverFiberIso p hp hne b).hom).toImage_imageι

/-- The identification with the universal datum preserves the original
finite scheme's structure morphism to the coefficient field. -/
theorem projectiveFiniteSubschemeParameterIso_hom_toBase :
    (projectiveFiniteSubschemeParameterIso p hp hne b i n hn).hom ≫
      (projectiveFiniteSubschemeParameter p hp hne b i n hn).val.subschemeι ≫
        (relativeFamilyProjection (projectiveSmoothFamilyToBase R σ d)).app
          (Over.mk (projectiveSmoothClassifyingMap p hp hne b)) =
      i ≫ hypersurfaceToBase p hp := by
  rw [← Category.assoc, projectiveFiniteSubschemeParameterIso_hom_ι, Category.assoc,
    projectiveSmoothClassifyingOverFiberIso_hom_fst]
  rfl

end UniversalHomogeneous
end AllCharacteristics
