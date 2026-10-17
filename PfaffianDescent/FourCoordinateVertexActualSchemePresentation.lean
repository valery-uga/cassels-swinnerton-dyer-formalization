import PfaffianDescent.FourTangentDualComponentAmbientSquare
import AllCharacteristics.FiniteSigmaSpec

/-! Universal geometric parametrization of four SUPPLIED length-two
components at the four coordinate vertices. Its actual product-dual
embedding is derived and retains the original coproduct immersion. -/

noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [IsAlgClosed K]
attribute [local instance] MvPolynomial.gradedAlgebra

theorem fourCoordinateVertex_actual_scheme_presentation
    (Z : Fin 4 → Scheme.{u})
    (i : ∀ r, Z r ⟶ scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)))
    [∀ r, IsClosedImmersion (i r)] [∀ r, IsFinite (i r ≫ toBase ⊥)]
    (hSupport : ∀ r, Set.range (i r) = {coordinateVertex (K := K) r})
    (hZ : ∀ r, AllCharacteristics.finiteSchemeRank (i r ≫ toBase ⊥) = 2) :
    ∃ (U : Fin 4 → Fin 4 → K)
      (e : (∐ Z) ≅ Spec (.of (QuarticNet.FourTangentDualAlgebra K))),
      (∀ r, U r r = 0) ∧ (∀ r, U r ≠ 0) ∧
      e.hom ≫ (QuarticNet.fourTangentDualToProjective U ≫ quotientProjMap ⊥) =
        Sigma.desc (fun r => i r ≫ quotientProjMap ⊥) := by
  classical
  have hEach (r : Fin 4) := coordinateVertex_lengthTwo_actual_tangent
    (i r) r (hSupport r) (hZ r)
  choose eRow U hDiag hNe hpoint using hEach
  letI : IsIso (sigmaSpec (fun _ : Fin 4 => CommRingCat.of (DualNumber K))) :=
    AllCharacteristics.isIso_sigmaSpec_const_finite (Fin 4) (DualNumber K)
  let e := Sigma.mapIso eRow ≪≫
    asIso (sigmaSpec (fun _ : Fin 4 => CommRingCat.of (DualNumber K)))
  refine ⟨U, e, hDiag, hNe, ?_⟩
  apply Sigma.hom_ext
  intro r
  calc
    Sigma.ι Z r ≫ e.hom ≫
        (QuarticNet.fourTangentDualToProjective U ≫ quotientProjMap ⊥) =
      (eRow r).hom ≫ Spec.map (CommRingCat.ofHom
        (Pi.evalRingHom (fun _ : Fin 4 => DualNumber K) r)) ≫
          QuarticNet.fourTangentDualToProjective U ≫ quotientProjMap ⊥ := by
      simp only [e, Iso.trans_hom, asIso_hom, Category.assoc]
      rw [← Category.assoc (Sigma.ι Z r), Sigma.ι_mapIso_hom]
      simp only [Category.assoc]
      rw [← Category.assoc
        (Sigma.ι (fun _ : Fin 4 => Spec (.of (DualNumber K))) r), ι_sigmaSpec]
    _ = (eRow r).hom ≫ ambientNormalizedCoordinateChartPoint (F := K)
        (fun s => TrivSqZeroExt.inl (coordinateVertexCoordinates (K := K) r s) +
          TrivSqZeroExt.inr (U r s)) r
        (by simp [coordinateVertexCoordinates, hDiag]) := by
      rw [QuarticNet.fourTangentDual_component_actual_ambient_square U hDiag r]
    _ = i r ≫ quotientProjMap ⊥ := hpoint r
    _ = Sigma.ι Z r ≫ Sigma.desc (fun r => i r ≫ quotientProjMap ⊥) := by
      rw [Sigma.ι_desc]

end PfaffianDescent
