import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualNativeSurfaceFibre
import PfaffianDescent.CubicClosedPointSerreFiniteZeroResidualArtinianFibreStalk

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
namespace PfaffianDescent
universe u
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra

theorem cubicClosedPointSerreFiniteZeroResidual_surface_open_fibre_stalk_regular_dim_two
    {K : Type u} [Field K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    {E T : Scheme.{u}} (k : E ⟶ Spec (.of K))
    (f : T ⟶ E) (j : T ⟶ pullback (hypersurfaceToBase p hp) k)
    [IsOpenImmersion j]
    (hj : j ≫ pullback.snd (hypersurfaceToBase p hp) k = f)
    (y : E) (x : f.fiber y) (hx : IsClosed ({x} : Set (f.fiber y))) :
    IsRegularLocalRing ((f.fiber y).presheaf.stalk x) ∧
      ringKrullDim ((f.fiber y).presheaf.stalk x) = 2 := by
  let g := pullback.snd (hypersurfaceToBase p hp) k
  let v : f.fiber y ⟶ g.fiber y := pullback.map f (E.fromSpecResidueField y)
    g (E.fromSpecResidueField y) j (𝟙 _) (𝟙 _) (by simpa [g] using hj.symm) (by simp)
  letI : IsOpenImmersion v := by dsimp [v]; infer_instance
  letI : Smooth g := by dsimp [g]; infer_instance
  have hvclosed : IsClosed ({v x} : Set (g.fiber y)) := by
    apply isClosed_singleton_of_isLocallyClosed_singleton
    rw [← Set.image_singleton]
    exact hx.isLocallyClosed.image v.isOpenEmbedding.isInducing
      v.isOpenEmbedding.isOpen_range.isLocallyClosed
  have hgeom := cubicClosedPointSerreFiniteZeroResidual_surface_fibre_stalk_regular_dim_two
    p hp hp0 k y (v x) hvclosed
  let e := (asIso (v.stalkMap x)).commRingCatIsoToRingEquiv
  constructor
  · letI := hgeom.1
    exact IsRegularLocalRing.of_ringEquiv e
  · exact (ringKrullDim_eq_of_ringEquiv e).symm.trans hgeom.2

end PfaffianDescent
