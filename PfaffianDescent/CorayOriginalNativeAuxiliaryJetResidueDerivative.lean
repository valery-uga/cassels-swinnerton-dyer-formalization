import PfaffianDescent.CorayOriginalNativeNormalizedDerivationJetDictionary

noncomputable section
namespace PfaffianDescent.Coray
open TensorProduct MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
open scoped PfaffianDescent.Coray
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

/-- A section through the SAME actual auxiliary algebra has zero residue
at every one of its actual original-K geometric evaluations. Therefore its
nonzero SAME native fulljet has nonzero tangent part, not merely residue. -/
theorem cubicThroughPointSection_throughActualAuxiliary_nonzeroNativeJet_snd_ne_zero001
    {K L A M : Type u} [Field K] [CommRing L] [CommRing A] [Field M]
    [Algebra K L] [Algebra K A] [Algebra K M]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3)
    (n : ℕ) (y : Fin 4 → L) (hpy : p.eval₂ (algebraMap K L) y = 0) (j : Fin 4)
    (hA : ChartRing (equationIdeal p hp) j →+* A)
    (hBaseA : hA.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K A)
    (sigma : A →ₐ[K] M) (v : Fin 2 → Fin 4 → M)
    (hpJ : p.eval₂ (algebraMap K (SurfacePlaneJet M))
      (surfacePlaneJetCoordinates (fun i => sigma (hA (chartCoordinate (equationIdeal p hp) j i))) v) = 0)
    (hAnchor : surfacePlaneJetCoordinates
      (fun i => sigma (hA (chartCoordinate (equationIdeal p hp) j i))) v j = 1)
    (s : cubicThroughCoordinateSections p hp n y hpy)
    (hsA : hA (cubicThroughPointChartEvaluation p hp n y hpy j s) = 0)
    (hsJet : cubicNormalizedFullJetChartMap p hp j
      (fun i => sigma (hA (chartCoordinate (equationIdeal p hp) j i))) v hpJ hAnchor
      (cubicThroughPointChartEvaluation p hp n y hpy j s) ≠ 0) :
    (cubicNormalizedFullJetChartMap p hp j
      (fun i => sigma (hA (chartCoordinate (equationIdeal p hp) j i))) v hpJ hAnchor
      (cubicThroughPointChartEvaluation p hp n y hpy j s)).snd ≠ 0 := by
  let g := sigma.toRingHom.comp hA
  have hBase : g.comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K M := by
    change (sigma.toRingHom.comp hA).comp (chartBaseMap (equationIdeal p hp) j) = algebraMap K M
    rw [RingHom.comp_assoc, hBaseA]
    exact sigma.comp_algebraMap
  let J := cubicNormalizedFullJetChartMap p hp j
    (fun i => sigma (hA (chartCoordinate (equationIdeal p hp) j i))) v hpJ hAnchor
    (cubicThroughPointChartEvaluation p hp n y hpy j s)
  have hFst : J.fst = 0 := by
    have h := cubicNormalizedFullJetChartMap_fst_eq001 p hp j g hBase v hpJ hAnchor
      (cubicThroughPointChartEvaluation p hp n y hpy j s)
    change J.fst = sigma (hA (cubicThroughPointChartEvaluation p hp n y hpy j s)) at h
    rw [hsA, map_zero] at h
    exact h
  intro hSnd
  apply hsJet
  apply TrivSqZeroExt.ext
  · exact hFst
  · exact hSnd

end PfaffianDescent.Coray
