import AllCharacteristics.HomogeneousCubicJacobianImage
import PfaffianDescent.HomogeneousQuotientMap
import PfaffianDescent.VoisinCoordinateOnePDeriv

/-! SOURCE ONLY / UNVERIFIED. The necessary Jacobian direction is derived
from the actual smooth principal chart; no gradient certificate is assumed. -/
noncomputable section
namespace AllCharacteristics
open AlgebraicGeometry CategoryTheory MvPolynomial
open HomogeneousProjective PfaffianDescent
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
variable {k : Type u} [Field k]

/-- A NONZERO smooth cubic has empty actual equation-plus-partials Proj.
The nonzero assumption is essential: p=0 has smooth P3 but vanishing partials. -/
theorem smoothCubic_cubicJacobianScheme_isEmpty
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] :
    IsEmpty (scheme (cubicJacobianIdeal p hp)) := by
  classical
  refine ⟨fun x => ?_⟩
  let I := equationIdeal p hp
  let J := cubicJacobianIdeal p hp
  have hIJ : I.toIdeal ≤ J.toIdeal := equationIdeal_le_cubicJacobianIdeal p hp
  obtain ⟨j, y, hy⟩ := exists_coordinate_chart J x
  letI : Nontrivial (ChartRing J j) := (y : PrimeSpectrum (ChartRing J j)).nontrivial
  let q : ChartRing I j →+* ChartRing J j := chartQuotientMap I J hIJ j
  have hzero : ∀ a : Fin 4,
      q ((pderiv a p).eval₂ (chartBaseMap I j) (chartCoordinate I j)) = 0 := by
    intro a
    change chartQuotientMap I J hIJ j
      ((pderiv a p).eval₂ (chartBaseMap I j) (chartCoordinate I j)) = 0
    rw [chartQuotientMap_eval₂ I J hIJ j]
    exact eval₂_chartCoordinate_eq_zero_of_mem J j _
      (pderiv_mem_cubicJacobianIdeal p hp a)
  have hspan : Ideal.span (Set.range (fun a : Fin 4 =>
      (pderiv a p).eval₂ (chartBaseMap I j) (chartCoordinate I j))) = ⊤ :=
    smoothCubic_chartJacobian_top p hp hp0 j
  have hle : Ideal.span (Set.range (fun a : Fin 4 =>
      (pderiv a p).eval₂ (chartBaseMap I j) (chartCoordinate I j))) ≤ RingHom.ker q := by
    apply Ideal.span_le.mpr
    rintro a ⟨b, rfl⟩
    exact hzero b
  rw [hspan] at hle
  have hz := hle (show (1 : ChartRing I j) ∈ ⊤ from trivial)
  change q 1 = 0 at hz
  exact one_ne_zero (by simpa only [map_one] using hz)

end AllCharacteristics
