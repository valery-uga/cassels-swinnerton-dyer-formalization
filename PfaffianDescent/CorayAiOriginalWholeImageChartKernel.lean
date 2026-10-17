import PfaffianDescent.CorayAiWholeImageOpenChartFullKernel

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace
open AllCharacteristics.HomogeneousProjective
open scoped PfaffianDescent.Coray
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- The actual anchor chart of SAME WHOLE original C has the quotient by
the ACTUAL stored original generic chart kernel. The full scheme image,
its original inclusion and the original native chart are all retained;
no reduced support or separately defined affine image is substituted. -/
theorem cubicThroughPointBasis_sameWholeImage_anchorChart_fullKernelQuotientIso001
    {K L : Type u} [Field K] [CommRing L] [Algebra K L]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] [IsIntegral (hypersurface p hp)]
    (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0)
    (j : Fin 4) [Nonempty (chartι (equationIdeal p hp) j).opensRange]
    {m : ℕ} (b : Module.Basis (Fin m) K (cubicThroughCoordinateSections p hp n y hpy))
    (a : Fin m) :
    let C := cubicThroughPointBasisEvaluationImage p hp hp0 n y hpy j b a
    let i := cubicThroughPointBasisEvaluationImageInclusion p hp hp0 n y hpy j b a
    let U := i ⁻¹ᵁ (chartι (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)) a).opensRange
    Nonempty (Γ(C, U) ≃+*
      (ChartRing (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)) a ⧸
        RingHom.ker (cubicThroughPointBasisGenericChartMap p hp hp0 n y hpy j b a))) := by
  let G := cubicThroughPointBasisGenericChartMap p hp hp0 n y hpy j b a
  let v := chartι (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K)) a
  letI : QuasiCompact (Spec.map (CommRingCat.ofHom G) ≫ v) :=
    cubicThroughPointBasisGenericPoint_quasiCompact p hp hp0 n y hpy j b a
  exact fieldPoint_wholeImage_openChart_fullKernelQuotientIso001
    (scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin m) K))) v G

end PfaffianDescent.Coray
