import AllCharacteristics.PowerSeriesPencilSpecifiedPoint
import AllCharacteristics.LaurentFiniteExtensionBasis

/-! SOURCE ONLY / UNVERIFIED. The actual generic point of the SAME L[[t]]
lift is valued in L((t)), over the actual k((t)) pencil fiber. The degree
identity and Module.Finite are internally derived by a coefficient basis. -/
noncomputable section
namespace AllCharacteristics
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits IsLocalRing
open HomogeneousProjective
universe u
variable {k L : Type u} [Field k] [Field L] [Algebra k L]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- This is an actual pullback fiber over k((t)), not a renamed polynomial
model or a fiber over a replacement extension field. -/
def prescribedLaurentPencilFiber
    (p g : MvPolynomial (Fin 4) k)
    (hp : p.IsHomogeneous 3) (hg : g.IsHomogeneous 3) : Scheme.{u} :=
  pullback (hypersurfaceToBase (prescribedPowerSeriesPencil p g)
    (prescribedPowerSeriesPencil_homogeneous hp hg))
    (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k) (LaurentSeries k))))

theorem prescribedLaurentPencil_generic_point_of_given_lift
    (p g : MvPolynomial (Fin 4) k)
    (hp : p.IsHomogeneous 3) (hg : g.IsHomogeneous 3)
    (s : Spec (.of (PowerSeries L)) ⟶ hypersurface
      (prescribedPowerSeriesPencil p g) (prescribedPowerSeriesPencil_homogeneous hp hg))
    (hs : s ≫ hypersurfaceToBase (prescribedPowerSeriesPencil p g)
        (prescribedPowerSeriesPencil_homogeneous hp hg) =
      Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k) (PowerSeries L)))) :
    ∃ y : Spec (.of (LaurentSeries L)) ⟶ prescribedLaurentPencilFiber p g hp hg,
      y ≫ pullback.fst (hypersurfaceToBase (prescribedPowerSeriesPencil p g)
          (prescribedPowerSeriesPencil_homogeneous hp hg))
          (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k) (LaurentSeries k)))) =
        Spec.map (CommRingCat.ofHom
          (algebraMap (PowerSeries L) (LaurentSeries L))) ≫ s ∧
      y ≫ pullback.snd (hypersurfaceToBase (prescribedPowerSeriesPencil p g)
          (prescribedPowerSeriesPencil_homogeneous hp hg))
          (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k) (LaurentSeries k)))) =
        Spec.map (CommRingCat.ofHom (laurentSeriesCoefficientMap (k := k) (L := L))) := by
  let a := Spec.map (CommRingCat.ofHom
    (algebraMap (PowerSeries L) (LaurentSeries L))) ≫ s
  let b := Spec.map (CommRingCat.ofHom (laurentSeriesCoefficientMap (k := k) (L := L)))
  have hcomm : a ≫ hypersurfaceToBase (prescribedPowerSeriesPencil p g)
        (prescribedPowerSeriesPencil_homogeneous hp hg) =
      b ≫ Spec.map (CommRingCat.ofHom
        (algebraMap (PowerSeries k) (LaurentSeries k))) := by
    dsimp only [a, b]
    rw [Category.assoc, hs, ← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun f : PowerSeries k →+* LaurentSeries L =>
      Spec.map (CommRingCat.ofHom f))
        (laurentSeriesCoefficientMap_comp_powerSeries (k := k) (L := L)).symm
  refine ⟨pullback.lift a b hcomm, ?_, ?_⟩
  · exact pullback.lift_fst _ _ _
  · exact pullback.lift_snd _ _ _

/-- Joint literal coefficient-field output: SAME prescribed L[[t]] lift,
SAME special reduction q, actual L((t)) generic point and degree [L:k].
Finiteness and degree are never substituted by a finite-free algebra witness. -/
theorem prescribedPowerLaurentPencil_lift_and_degree
    [Module.Finite k L]
    (p g : MvPolynomial (Fin 4) k)
    (hp : p.IsHomogeneous 3) (hg : g.IsHomogeneous 3)
    (q : Spec (.of L) ⟶ hypersurface (prescribedPowerSeriesPencil p g)
      (prescribedPowerSeriesPencil_homogeneous hp hg))
    (hq : q ≫ hypersurfaceToBase (prescribedPowerSeriesPencil p g)
        (prescribedPowerSeriesPencil_homogeneous hp hg) =
      Spec.map (CommRingCat.ofHom
        ((algebraMap k L).comp (PowerSeries.constantCoeff (R := k)))))
    (hsm : q (IsLocalRing.closedPoint L) ∈
      (hypersurfaceToBase (prescribedPowerSeriesPencil p g)
        (prescribedPowerSeriesPencil_homogeneous hp hg)).smoothLocus) :
    ∃ s : Spec (.of (PowerSeries L)) ⟶ hypersurface
        (prescribedPowerSeriesPencil p g) (prescribedPowerSeriesPencil_homogeneous hp hg),
      s ≫ hypersurfaceToBase (prescribedPowerSeriesPencil p g)
          (prescribedPowerSeriesPencil_homogeneous hp hg) =
        Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k) (PowerSeries L))) ∧
      Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := L))) ≫ s = q ∧
      ∃ y : Spec (.of (LaurentSeries L)) ⟶ prescribedLaurentPencilFiber p g hp hg,
        y ≫ pullback.fst (hypersurfaceToBase (prescribedPowerSeriesPencil p g)
            (prescribedPowerSeriesPencil_homogeneous hp hg))
            (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k) (LaurentSeries k)))) =
          Spec.map (CommRingCat.ofHom
            (algebraMap (PowerSeries L) (LaurentSeries L))) ≫ s ∧
        y ≫ pullback.snd (hypersurfaceToBase (prescribedPowerSeriesPencil p g)
            (prescribedPowerSeriesPencil_homogeneous hp hg))
            (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k) (LaurentSeries k)))) =
          Spec.map (CommRingCat.ofHom (laurentSeriesCoefficientMap (k := k) (L := L))) ∧
        Module.finrank (LaurentSeries k) (LaurentSeries L) = Module.finrank k L := by
  obtain ⟨s, hs, hred⟩ := prescribedPowerSeriesPencil_lift_given_smooth_point
    p g hp hg q hq hsm
  obtain ⟨y, hys, hy⟩ := prescribedLaurentPencil_generic_point_of_given_lift p g hp hg s hs
  exact ⟨s, hs, hred, y, hys, hy, finiteExtensionLaurent_finrank⟩

end AllCharacteristics
