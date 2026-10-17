import PfaffianDescent.HomogeneousQuotientMap
import AllCharacteristics.AffineChartPresentation

/-!
# Kernels of projective quotient-chart maps

The polynomial presentation of each affine chart identifies the kernel of
a map induced by an inclusion of homogeneous ideals with the image of the
larger chart-presentation ideal. This is the algebraic bridge for restricting
a moving hypersurface equation to a fixed projective subscheme.
-/

namespace PfaffianDescent

open AlgebraicGeometry MvPolynomial
open AllCharacteristics.HomogeneousProjective

universe u
variable {R : Type u} {σ : Type} [CommRing R]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The quotient chart-map kernel is the image of the larger polynomial
chart-presentation ideal in the smaller chart ring. -/
theorem chartQuotientMap_ker_eq_presentationImage
    (I J : HomogeneousIdeal (homogeneousSubmodule σ R))
    (hIJ : I.toIdeal ≤ J.toIdeal) (j : σ) :
    RingHom.ker (chartQuotientMap I J hIJ j) =
      (chartPresentationIdeal J j).map
        (MvPolynomial.eval₂Hom (chartBaseMap I j) (chartCoordinate I j)) := by
  let f := chartQuotientMap I J hIJ j
  let evI := MvPolynomial.eval₂Hom (chartBaseMap I j) (chartCoordinate I j)
  let evJ := MvPolynomial.eval₂Hom (chartBaseMap J j) (chartCoordinate J j)
  have hcomp : f.comp evI = evJ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simpa only [RingHom.comp_apply, evI, evJ, MvPolynomial.eval₂Hom_C] using
        DFunLike.congr_fun (chartQuotientMap_chartBaseMap I J hIJ j) r
    · intro i
      simpa only [RingHom.comp_apply, evI, evJ, MvPolynomial.eval₂Hom_X'] using
        chartQuotientMap_chartCoordinate I J hIJ j i
  have hkerJ : RingHom.ker evJ = chartPresentationIdeal J j :=
    chartEvaluation_ker J j
  apply le_antisymm
  · intro x hx
    obtain ⟨P, rfl⟩ := eval₂_chartCoordinate_surjective I j x
    apply Ideal.mem_map_of_mem evI
    rw [← hkerJ]
    change evJ P = 0
    rw [← hcomp]
    exact hx
  · rw [Ideal.map_le_iff_le_comap]
    intro P hP
    change f (evI P) = 0
    rw [← RingHom.comp_apply, hcomp]
    have hPJ : P ∈ RingHom.ker evJ := by simpa only [hkerJ] using hP
    exact hPJ

/-- If the larger homogeneous ideal is obtained by adjoining one equation,
then that equation generates the kernel on every actual projective chart. -/
theorem chartQuotientMap_ker_eq_principal_of_ideal_eq_sup
    (I J : HomogeneousIdeal (homogeneousSubmodule σ R))
    (hIJ : I.toIdeal ≤ J.toIdeal)
    (p : MvPolynomial σ R)
    (hJ : J.toIdeal = I.toIdeal ⊔ Ideal.span ({p} : Set (MvPolynomial σ R)))
    (j : σ) :
    RingHom.ker (chartQuotientMap I J hIJ j) =
      Ideal.span ({p.eval₂ (chartBaseMap I j) (chartCoordinate I j)} :
        Set (ChartRing I j)) := by
  let evI := MvPolynomial.eval₂Hom (chartBaseMap I j) (chartCoordinate I j)
  have hchart : chartPresentationIdeal J j =
      chartPresentationIdeal I j ⊔ Ideal.span ({p} : Set (MvPolynomial σ R)) := by
    simp only [chartPresentationIdeal, hJ]
    ac_rfl
  have hzero : (chartPresentationIdeal I j).map evI = ⊥ := by
    apply (Ideal.map_eq_bot_iff_le_ker evI).mpr
    rw [chartEvaluation_ker]
  rw [chartQuotientMap_ker_eq_presentationImage, hchart, Ideal.map_sup,
    hzero, bot_sup_eq, Ideal.map_span, Set.image_singleton]
  rfl

/-- Intersecting a projective homogeneous subscheme with a hypersurface
adds exactly one normalized equation to each affine coordinate chart. -/
theorem chartQuotientMap_ker_eq_equation
    (I : HomogeneousIdeal (homogeneousSubmodule σ R))
    (p : MvPolynomial σ R) {d : ℕ} (hp : p.IsHomogeneous d) (j : σ) :
    RingHom.ker (chartQuotientMap I (I ⊔ equationIdeal p hp)
      (by rw [HomogeneousIdeal.toIdeal_sup]; exact le_sup_left) j) =
      Ideal.span ({p.eval₂ (chartBaseMap I j) (chartCoordinate I j)} :
        Set (ChartRing I j)) := by
  apply chartQuotientMap_ker_eq_principal_of_ideal_eq_sup
  rw [HomogeneousIdeal.toIdeal_sup]
  rfl

end PfaffianDescent
