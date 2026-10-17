import PfaffianDescent.CubicGroundKernelSerrePointDerivative
import PfaffianDescent.PolynomialProjectiveMap

/-! The actual jet residue points respect the original coefficient field. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicGroundKernelJetPoint_toBase
    {F L E : Type u} [Field F] [Field L] [Field E]
    [Algebra F L] [Algebra F E]
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) F)) (ell : grading I 1)
    (g : Away (grading I) (ell : CoordinateRing I) →+* L)
    (hbase : g.comp (AllCharacteristics.GradedChart.baseMap (grading I)
      (z := (ell : CoordinateRing I))) = algebraMap F L)
    (φ : Away (grading I) (ell : CoordinateRing I) →+* CubicSurfaceFirstJet E)
    (β : L →ₐ[F] E)
    (hres : cubicClosedPointSerreSurfaceJetCotangent_ringResidueMap φ = β.toRingHom.comp g) :
    cubicGroundKernelJetPoint I ell φ ≫ toBase I =
      Spec.map (CommRingCat.ofHom (algebraMap F E)) := by
  let ρ := cubicClosedPointSerreSurfaceJetCotangent_ringResidueMap φ
  let η := AllCharacteristics.GradedChart.baseMap (grading I)
    (z := (ell : CoordinateRing I))
  have hc : cubicClosedPointSerreSurfaceJetCotangent_linearChartMorphism I ell ≫ toBase I =
      Spec.map (CommRingCat.ofHom η) :=
    homogeneousChart_toBase I (ell : CoordinateRing I) ell.2 Nat.zero_lt_one
  have hcomp : ρ.comp
    (AllCharacteristics.GradedChart.baseMap (grading I)
      (z := (ell : CoordinateRing I))) = algebraMap F E := by
    apply RingHom.ext
    intro x
    have hx := RingHom.congr_fun hbase x
    have hrx := RingHom.congr_fun hres (η x)
    change ρ (η x) = algebraMap F E x
    rw [show ρ (η x) = β (g (η x)) from hrx]
    rw [show g (η x) = algebraMap F L x from hx]
    exact β.commutes x
  calc
    cubicGroundKernelJetPoint I ell φ ≫ toBase I =
        Spec.map (CommRingCat.ofHom ρ) ≫ Spec.map (CommRingCat.ofHom η) :=
      (Category.assoc _ _ _).trans
        (congrArg (fun t => Spec.map (CommRingCat.ofHom ρ) ≫ t) hc)
    _ = Spec.map (CommRingCat.ofHom (ρ.comp η)) := (Spec.map_comp _ _).symm
    _ = Spec.map (CommRingCat.ofHom (algebraMap F E)) :=
      congrArg (fun f => Spec.map (CommRingCat.ofHom f)) hcomp

end PfaffianDescent
