import PfaffianDescent.CubicGroundKernelSerreEvaluationSurjective
import PfaffianDescent.CubicElevenPointGroundChartDerivativeMaps

/-! Native normalized jets construct a surjective ACTUAL evaluation map
for the original Serre bundle at three actual degree-eleven components.
Neither evaluation rank nor a fibre comparison is an input. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization Module
open CategoryTheory.Abelian
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

theorem cubicElevenPoint_groundChart_exists_actualSerreEvaluation_surjective
    {F L E : Type u} [Field F] [Field L] [Field E]
    [Algebra F L] [Algebra F E] [FiniteDimensional F L]
    (P : MvPolynomial (Fin 4) F) (hP : P.IsHomogeneous 3) (hP0 : P ≠ 0)
    [Smooth (hypersurfaceToBase P hP)]
    [HasExt.{u} (Proj (homogeneousSubmodule (Fin 4) F)).Modules]
    [HasExt.{u} (hypersurface P hP).Modules]
    (j : Fin 4) (g : ChartRing (equationIdeal P hP) j →+* L)
    [IsClosedImmersion (Spec.map (CommRingCat.ofHom g))]
    [IsClosedImmersion (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion
      (equationIdeal P hP) ⟨coordinate (equationIdeal P hP) j,
        coordinate_mem (equationIdeal P hP) j⟩ g)]
    (hgb : g.comp (chartBaseMap (equationIdeal P hP) j) = algebraMap F L)
    (e : SerreExtensionData (hypersurface P hP)
      (closedImmersionIdealTwist
        (cubicClosedPointSerreSurfaceJetCotangent_linearChartClosedImmersion
          (equationIdeal P hP) ⟨coordinate (equationIdeal P hP) j,
            coordinate_mem (equationIdeal P hP) j⟩ g)
        (ProjectiveNegativeTwist.positiveSheafOfModules (grading (equationIdeal P hP)) 3)))
    (C : SerreExtensionData.SerreExtensionRankTwoAffineCover e)
    (α : Fin 11 → (L →ₐ[F] E))
    (y : Fin 11 → Fin 4 → E) (hnz : ∀ k, y k j ≠ 0)
    (hcoords : ∀ k r, α k (g (linearChartCoordinate (equationIdeal P hP)
        (coordinate (equationIdeal P hP) j) (coordinate_mem (equationIdeal P hP) j) r)) =
      (y k j)⁻¹ * y k r)
    (J : Fin 3 → Fin 4 → CubicSurfaceFirstJet E)
    (hresidue : ∀ k r, (J k r).fst = y (k.castAdd 8) r)
    (hzero : ∀ k, aeval (J k) (P.map (algebraMap F E)) = 0)
    (hfull : Function.Surjective (cubicElevenPointFullJetRestriction y J))
    (hL : finrank F L ≤ 11)
    (hmem : ∀ q, cubicHomogeneousChartRestriction (equationIdeal P hP)
        (coordinate (equationIdeal P hP) j) (coordinate_mem (equationIdeal P hP) j) g q = 0 →
      cubicElevenPointValueRestriction y
        (voisinDegreeTenSelectedAvoidance_mapCubicSection (L := E) q) = 0)
    (hker : finrank F (cubicHomogeneousChartRestriction (equationIdeal P hP)
      (coordinate (equationIdeal P hP) j) (coordinate_mem (equationIdeal P hP) j) g).ker = 9) :
    let I := equationIdeal P hP
    let ell : grading I 1 := ⟨coordinate I j, coordinate_mem I j⟩
    ∃ (φ : Fin 3 → (ChartRing I j →+* CubicSurfaceFirstJet E))
      (hres : ∀ k, cubicClosedPointSerreSurfaceJetCotangent_ringResidueMap (φ k) =
        (α (k.castAdd 8)).toRingHom.comp g),
      Function.Surjective (cubicGroundKernelJetSectionEvaluation I ell g hgb φ
        (fun k => α (k.castAdd 8)) hres e.E) ∧
      Function.Bijective (cubicGroundKernelSerrePointDerivative I ell g φ
        (fun k => (α (k.castAdd 8)).toRingHom) hres e.E e.projection) := by
  classical
  let R := cubicHomogeneousChartRestriction (equationIdeal P hP)
    (coordinate (equationIdeal P hP) j) (coordinate_mem (equationIdeal P hP) j) g
  letI : Module.Free F R.ker := Module.Free.of_divisionRing F R.ker
  letI : Module.Finite F R.ker := Module.finite_of_finrank_pos (by rw [hker]; decide)
  let B : Basis (Fin 9) F R.ker := (Module.finBasis F R.ker).reindex (finCongr hker)
  obtain ⟨φ, hres, hspan⟩ := cubicElevenPoint_groundChart_exists_derivativeMaps
    P hP j g hgb α y hnz hcoords J hresidue hzero hfull hL hmem
  refine ⟨φ, hres, ?_⟩
  exact cubicGroundKernelSerre_actualEvaluation_surjective_of_kernelDerivativeSpan
    P hP hP0 ⟨coordinate (equationIdeal P hP) j, coordinate_mem (equationIdeal P hP) j⟩
    g hgb e C B φ (fun k => α (k.castAdd 8)) hres (hspan B)

end PfaffianDescent
