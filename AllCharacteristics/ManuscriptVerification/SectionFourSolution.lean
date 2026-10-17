import PfaffianDescent.PerfectFieldOriginalH0SectionFourPointCaller
import AllCharacteristics.SectionFour
import PfaffianDescent.ActualP3IdealQuadraticFiniteNetDimension
import PfaffianDescent.SectionFourActualIdealHZeroPoint
import PfaffianDescent.FourCoordinateVertexSuppliedActualH0Literal
import PfaffianDescent.LiteralArithmeticH0SkewGeometricRepresentation
import PfaffianDescent.SingleSupportOriginalSuppliedFrameZeroEntryGeometry
import PfaffianDescent.PerfectFieldClosedQuarticOriginalTangentHZero

/-! Explicit full-type comparator declarations for the nine selected Section4 conclusions.
The types reuse project definitions; see verification/README.md for validation and trust scope.
The solution bodies delegate to accepted exported providers; replacing those bodies with sorry
produces a statement-completion challenge, not an independent-foundations reconstruction. -/

set_option linter.unusedVariables false

namespace PfaffianDescent.ManuscriptComparators
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- 4.1: `thm:4->1` (2-proofs.tex:574). -/
theorem claim_4_1 :
    ∀ {k : Type u} [Field k] [PerfectField k]
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3) (hF₀ : F ≠ 0)
    [Smooth (hypersurfaceToBase F hF)]
    (P : closedPoints (hypersurface F hF))
    (h4 : (hypersurfaceToBase F hF).residueDegree P.1 = 4),
    ∃ s : Spec (.of k) ⟶ hypersurface F hF,
          s ≫ hypersurfaceToBase F hF = 𝟙 _
    := @PfaffianDescent.perfectField_degree_four_originalHZero_graph_rational_section

end
end PfaffianDescent.ManuscriptComparators

namespace AllCharacteristics.ManuscriptComparators
noncomputable section
open AlgebraicGeometry CategoryTheory
open HomogeneousProjective PfaffianDescent Module
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] MvPolynomial.algebraMvPolynomial
universe u

/-- 4.2: `lem:net-of-quadrics` (2-proofs.tex:594). -/
theorem claim_4_2 :
    ∀ {k : Type u} [Field k]
    (F Q₁ Q₂ Q₃ : MvPolynomial (Fin 4) k)
    (hF : F.IsHomogeneous 3)
    (hQ₁ : Q₁.IsHomogeneous 2) (hQ₂ : Q₂.IsHomogeneous 2)
    (hQ₃ : Q₃.IsHomogeneous 2)
    [IsFinite (toBase
      (tripleCompleteIntersectionHomogeneousIdeal Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃))]
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface Q₁ hQ₁) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase Q₁ hQ₁)]
    (hker : (tripleCompleteIntersectionToHypersurface Q₁ Q₂ Q₃ hQ₁ hQ₂ hQ₃).ker ≤ i.ker)
    (hZ : finiteSchemeRank (i ≫ hypersurfaceToBase Q₁ hQ₁) = 8)
    (j : Z ⟶ hypersurface F hF)
    (hcompat : j ≫ hypersurfaceToAmbient F hF =
      i ≫ hypersurfaceToAmbient Q₁ hQ₁),
    ∃ H₁ H₂ H₃ : MvPolynomial (Fin 4) k,
          H₁.IsHomogeneous 1 ∧ H₂.IsHomogeneous 1 ∧ H₃.IsHomogeneous 1 ∧
            F = H₁ * Q₁ + H₂ * Q₂ + H₃ * Q₃
    := @AllCharacteristics.sectionFour_linear_quadric_decomposition_of_finite_nonempty_net

end
end AllCharacteristics.ManuscriptComparators

namespace PfaffianDescent.ManuscriptComparators
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- 4.3: `rem:h^0(I_Z)=3` (2-proofs.tex:619). -/
theorem claim_4_3 :
    ∀ {K : Type u} [Field K]
    (f g h : MvPolynomial (Fin 4) K)
    (hf : f.IsHomogeneous 2) (hg : g.IsHomogeneous 2) (hh : h.IsHomogeneous 2)
    [IsFinite (toBase (tripleCompleteIntersectionHomogeneousIdeal f g h hf hg hh))]
    {Z : Scheme.{u}} (i : Z ⟶ hypersurface f hf) [IsClosedImmersion i]
    [IsFinite (i ≫ hypersurfaceToBase f hf)]
    (hker : (tripleCompleteIntersectionToHypersurface f g h hf hg hh).ker ≤ i.ker)
    (hZ : AllCharacteristics.finiteSchemeRank (i ≫ hypersurfaceToBase f hf) = 8),
    Module.finrank K (SchemeModuleGlobalSectionsOver
          (ambientToBase (R := K) (σ := Fin 4))
          (closedImmersionIdealTwist (i ≫ hypersurfaceToAmbient f hf)
            (positiveSheafOfModules (homogeneousSubmodule (Fin 4) K) 2))) = 3
    := @PfaffianDescent.sectionFour_actual_ideal_quadratic_global_dimension_three_of_finite_net

end
end PfaffianDescent.ManuscriptComparators

namespace PfaffianDescent.ManuscriptComparators
noncomputable section
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- 4.4: `prop:existence-of-point` (2-proofs.tex:623). -/
theorem claim_4_4 :
    ∀ {K : Type u} [Field K]
    (F : MvPolynomial (Fin 4) K) (hF : F.IsHomogeneous 3)
    {Z : Scheme.{u}} (j : Z ⟶ hypersurface F hF) [IsClosedImmersion j]
    [IsFinite (j ≫ hypersurfaceToBase F hF)]
    (hZ : AllCharacteristics.finiteSchemeRank (j ≫ hypersurfaceToBase F hF) = 8)
    [IsFinite (toBase
      (p3ActualIdealQuadraticGlobalBaseIdeal (j ≫ hypersurfaceToAmbient F hF)))],
    ∃ s : Spec (.of K) ⟶ hypersurface F hF,
          s ≫ hypersurfaceToBase F hF = 𝟙 _
    := @PfaffianDescent.sectionFour_section_of_cubic_of_finite_actual_ideal_quadratic_global_base

end
end PfaffianDescent.ManuscriptComparators

namespace PfaffianDescent.ManuscriptComparators
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- 4.5: `lem:uij-skew-symmetric` (2-proofs.tex:654). -/
theorem claim_4_5 :
    ∀ {K : Type u} [Field K] [IsAlgClosed K] {Z : Scheme.{u}}
    (i : Z ⟶ scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)))
    [IsClosedImmersion i] [IsFinite (i ≫ toBase ⊥)]
    (Y : Fin 4 → Scheme.{u}) (c : ∀ r, Y r ⟶ Z) [∀ r, IsClosedImmersion (c r)]
    (hDisjoint : Pairwise fun r s => Disjoint (Set.range (c r)) (Set.range (c s)))
    (hSupport : ∀ r, Set.range (c r ≫ i) = {coordinateVertex (K := K) r})
    (hComponents : ∀ r, AllCharacteristics.finiteSchemeRank (c r ≫ (i ≫ toBase ⊥)) = 2)
    (hWhole : AllCharacteristics.finiteSchemeRank (i ≫ toBase ⊥) = 8)
    (U : Fin 4 → Fin 4 → K) (hdiag : ∀ r, U r r = 0)
    (eRow : ∀ r, Y r ≅ Spec (.of (DualNumber K)))
    (hpoint : ∀ r, (eRow r).hom ≫
      ambientNormalizedCoordinateChartPoint (F := K)
        (fun s => TrivSqZeroExt.inl (coordinateVertexCoordinates (K := K) r s) +
          TrivSqZeroExt.inr (U r s)) r
        (by simp [coordinateVertexCoordinates, hdiag]) =
          (c r ≫ i) ≫ quotientProjMap ⊥),
    3 ≤ finrank K (ActualP3IdealQuadraticHZero (i ≫ quotientProjMap ⊥)) ↔
          ∃ w : Fin 4 → K, w ≠ 0 ∧
            ∀ r s, r < s → w r * U r s = -(w s * U s r)
    := @PfaffianDescent.fourCoordinateVertex_whole_supplied_actual_H0_weighted_iff

end
end PfaffianDescent.ManuscriptComparators

namespace PfaffianDescent.ManuscriptComparators
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- 4.6: `lem:base-locus` (2-proofs.tex:707). -/
theorem claim_4_6 :
    ∀ {K : Type u} [Field K] [IsAlgClosed K] {Z : Scheme.{u}}
    (i : Z ⟶ scheme (⊥ : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K)))
    [IsClosedImmersion i] [IsFinite (i ≫ toBase ⊥)]
    (Y : Fin 4 → Scheme.{u}) (c : ∀ r, Y r ⟶ Z) [∀ r, IsClosedImmersion (c r)]
    (hDisjoint : Pairwise fun r s => Disjoint (Set.range (c r)) (Set.range (c s)))
    (hSupport : ∀ r, Set.range (c r ≫ i) = {coordinateVertex (K := K) r})
    (hComponents : ∀ r, AllCharacteristics.finiteSchemeRank (c r ≫ (i ≫ toBase ⊥)) = 2)
    (hWhole : AllCharacteristics.finiteSchemeRank (i ≫ toBase ⊥) = 8)
    (U : Fin 4 → Fin 4 → K) (hdiag : ∀ r, U r r = 0)
    (eRow : ∀ r, Y r ≅ Spec (.of (DualNumber K)))
    (hpoint : ∀ r, (eRow r).hom ≫
      ambientNormalizedCoordinateChartPoint (F := K)
        (fun s => TrivSqZeroExt.inl (coordinateVertexCoordinates (K := K) r s) +
          TrivSqZeroExt.inr (U r s)) r
        (by simp [coordinateVertexCoordinates, hdiag]) =
          (c r ≫ i) ≫ quotientProjMap ⊥)
    (hskew : ∀ r s, U r s = -U s r)
    (hnonzero : ∀ r s, r ≠ s → U r s ≠ 0),
    (∃ l : Z ⟶ scheme (p3ActualIdealQuadraticGlobalBaseIdeal (i ≫ quotientProjMap ⊥)),
          IsIso l ∧ l ≫ quotientProjMap
            (p3ActualIdealQuadraticGlobalBaseIdeal (i ≫ quotientProjMap ⊥)) =
              i ≫ quotientProjMap ⊥) ∨
          QuarticNet.GroundTwistedCubicPresentation
            (p3ActualIdealQuadraticGlobalBaseIdeal (i ≫ quotientProjMap ⊥))
    := @PfaffianDescent.fourCoordinateVertex_whole_supplied_actual_H0_fullBase_alternative

end
end PfaffianDescent.ManuscriptComparators

namespace PfaffianDescent.ManuscriptComparators
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics.HomogeneousProjective ProjectiveNegativeTwist
open QuarticNet
open scoped TensorProduct
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

/-- 4.7: `lem:uij=-uji` (2-proofs.tex:784). -/
theorem claim_4_7 :
    ∀ {k : Type u} [Field k] [PerfectField k] (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k))
    {Z : Scheme.{u}} (i : Z ⟶ scheme I) [IsClosedImmersion i]
    [IsFinite (i ≫ toBase I)] (P : closedPoints (scheme I))
    (hSupport : Set.range i = {P.1})
    (hP : (toBase I).residueDegree P.1 = 4)
    (hGeom : ProjectiveGeometricGeneralPosition I ((scheme I).fromSpecResidueField P.1))
    (hdim : 3 ≤ finrank k (ActualP3IdealQuadraticHZero (i ≫ quotientProjMap I)))
    (hZ : AllCharacteristics.finiteSchemeRank (i ≫ toBase I) = 8),
    ∃ (pi : Equiv.Perm (Fin 4))
          (B : Basis (Fin 4) (AlgebraicClosure k) (Fin 4 → AlgebraicClosure k))
          (U : Fin 4 → Fin 4 → AlgebraicClosure k)
          (S : pullback
            (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))
              (i ≫ toBase I) ≅ Spec (.of (FourTangentDualAlgebra (AlgebraicClosure k))))
          (Q : pullback
            (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))
              (i ≫ toBase I) ⟶ Proj (homogeneousSubmodule (Fin 4) (AlgebraicClosure k))),
          (∀ row, U row row = 0) ∧
          (∀ row col, U row col = -U col row) ∧
          (∀ row, ∃ col, U row col ≠ 0) ∧
          Q ≫ ambientCoefficientMap (algebraMap k (AlgebraicClosure k)) =
            pullback.snd
              (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))
                (i ≫ toBase I) ≫ i ≫ quotientProjMap I ∧
          Q ≫ ambientToBase (R := AlgebraicClosure k) =
            pullback.fst
              (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))
                (i ≫ toBase I) ∧
          S.inv ≫ Q ≫ ambientProjectiveRenameMap (K := AlgebraicClosure k) pi =
            fourTangentDualToProjective U ≫ quotientProjMap ⊥ ≫
              (linearCoordinateChangeAmbientIso (basisCoordinateMatrix B)
                (basisCoordinateMatrix_isUnit B)).inv ∧
          ∀ row, ∃ hrow : tangentDualPoint U row row = 1,
            Spec.map (CommRingCat.ofHom
              (Pi.evalRingHom (fun _ : Fin 4 => DualNumber (AlgebraicClosure k)) row)) ≫
              S.inv ≫ Q ≫ ambientProjectiveRenameMap (K := AlgebraicClosure k) pi =
            ambientNormalizedCoordinateChartPoint (F := AlgebraicClosure k)
              (tangentDualPoint U row) row hrow ≫
              (linearCoordinateChangeAmbientIso (basisCoordinateMatrix B)
                (basisCoordinateMatrix_isUnit B)).inv
    := @PfaffianDescent.singleSupport_actual_H0_skew_geometric_representation

end
end PfaffianDescent.ManuscriptComparators

namespace PfaffianDescent.ManuscriptComparators
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- 4.8: `prop:zero-off-diagonal` (2-proofs.tex:822). -/
theorem claim_4_8 :
    ∀ {k : Type u} [Field k] [PerfectField k] (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    {Z : Scheme.{u}} (i : Z ⟶ scheme (equationIdeal p hp)) [IsClosedImmersion i]
    [IsFinite (i ≫ toBase (equationIdeal p hp))] (P : closedPoints (scheme (equationIdeal p hp)))
    (hSupport : Set.range i = {P.1})
    (hP : (toBase (equationIdeal p hp)).residueDegree P.1 = 4)
    (hGeom : ProjectiveGeometricGeneralPosition (equationIdeal p hp) ((scheme (equationIdeal p hp)).fromSpecResidueField P.1)),
        letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase (equationIdeal p hp))
        letI := finiteSchemeCoefficientAlgebra (i ≫ toBase (equationIdeal p hp))
        letI := finiteSchemeCoefficient_finite (i ≫ toBase (equationIdeal p hp))
        letI := AllCharacteristics.pointAlgebra (toBase (equationIdeal p hp)) P.1
        letI := AllCharacteristics.closedPoint_moduleFinite (toBase (equationIdeal p hp)) P
        (AllCharacteristics.finiteSchemeRank (i ≫ toBase (equationIdeal p hp)) = 8) →
        ∃ (j : Fin 4) (x : Fin 4 → Γ(Z, ⊤)) (hxj : x j = 1)
          (eA : Γ(Z, ⊤) ≃ₐ[k] DualNumber ((scheme (equationIdeal p hp)).residueField P.1))
          (b : Basis (Fin 4) k ((scheme (equationIdeal p hp)).residueField P.1))
          (hbj : b j = 1)
          (v : Fin 4 → (scheme (equationIdeal p hp)).residueField P.1)
          (full : Fin 4 ≃ ((scheme (equationIdeal p hp)).residueField P.1 →ₐ[k] AlgebraicClosure k)),
          let K := AlgebraicClosure k
          let Q := pullback (Spec.map (CommRingCat.ofHom (algebraMap k K))) (i ≫ toBase (equationIdeal p hp))
          let eTensor := finiteSchemeActualFieldBaseChangeIso (K := K) (i ≫ toBase (equationIdeal p hp))
          let qt := ambientNormalizedCoordinateChartPoint (F := K)
            (fun m => (1 : K) ⊗ₜ[k] x m) j (tensor_coordinate_eq_one x j hxj)
          let qOriginal := eTensor.hom ≫ qt
          let cb := QuarticNet.conjugateBasis full b (QuarticNet.conjugate_basis_span b full)
          let U := QuarticNet.conjugateTangentMatrix full b v (QuarticNet.conjugate_basis_span b full)
          (v j = 0) ∧ (v ≠ 0) ∧
          (ambientNormalizedCoordinateChartPoint (F := k) x j hxj =
            Z.isoSpec.inv ≫ i ≫ quotientProjMap (equationIdeal p hp)) ∧
          (aeval (R := k) x p = 0) ∧
          (Function.Surjective (aeval (R := k) x)) ∧
          (∀ r, eA (x r) = (inl (b r) : DualNumber ((scheme (equationIdeal p hp)).residueField P.1)) + inr (v r)) ∧
          (qOriginal ≫ ambientCoefficientMap (algebraMap k K) =
            pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap k K))) (i ≫ toBase (equationIdeal p hp)) ≫
              i ≫ quotientProjMap (equationIdeal p hp)) ∧
          ∀ (supplied : Basis (Fin 4) K (Fin 4 → K))
            (hFrameSupport : Set.range (fun r =>
              (linearCoordinateChangeAmbientIso (QuarticNet.basisCoordinateMatrix supplied)
                (QuarticNet.basisCoordinateMatrix_isUnit supplied)).inv
                  (actualVertexAmbientPoint (K := K) r)) =
              Set.range (fun r => ambientNormalizedCoordinateChartPoint (F := K)
                (cb r) j (by
                  rw [QuarticNet.conjugateBasis_apply, hbj, map_one])
                (IsLocalRing.closedPoint K))),
          ∀ (Y : Fin 4 → Scheme.{u}) (c : ∀ r, Y r ⟶ Q) [∀ r, IsClosedImmersion (c r)],
          (Pairwise fun r s => Disjoint (Set.range (c r)) (Set.range (c s))) →
          (∀ r, Set.range (c r ≫ qOriginal) =
            {(linearCoordinateChangeAmbientIso (QuarticNet.basisCoordinateMatrix supplied)
              (QuarticNet.basisCoordinateMatrix_isUnit supplied)).inv
                (actualVertexAmbientPoint (K := K) r)}) →
          (∀ r, AllCharacteristics.finiteSchemeRank
            (c r ≫ pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap k K))) (i ≫ toBase (equationIdeal p hp))) = 2) →
          ∃ (rho : Equiv.Perm (Fin 4)) (hc : ∀ r, supplied r j ≠ 0)
            (canonicalE : ∀ r, Y r ≅ Spec (.of (DualNumber K)))
            (hWholeIso : IsIso (Sigma.desc c)),
            (∀ r, (canonicalE r).hom ≫ ambientNormalizedCoordinateChartPoint (F := K)
              (QuarticNet.tangentDualPoint U (rho r)) (rho r)
              (by simp [U, QuarticNet.tangentDualPoint, QuarticNet.conjugateTangentMatrix_diagonal]) ≫
              (linearCoordinateChangeAmbientIso (QuarticNet.basisCoordinateMatrix cb)
                (QuarticNet.basisCoordinateMatrix_isUnit cb)).inv = c r ≫ qOriginal) ∧
            ∀ (V : Fin 4 → Fin 4 → K) (hV : ∀ r, V r r = 0)
              (suppliedE : ∀ r, Y r ≅ Spec (.of (DualNumber K))),
            (∀ r, (suppliedE r).hom ≫ ambientNormalizedCoordinateChartPoint (F := K)
              (QuarticNet.tangentDualPoint V r) r (by simp [QuarticNet.tangentDualPoint, hV]) ≫
              (linearCoordinateChangeAmbientIso (QuarticNet.basisCoordinateMatrix supplied)
                (QuarticNet.basisCoordinateMatrix_isUnit supplied)).inv = c r ≫ qOriginal) →
            ∃ (epsilon : Fin 4 → K) (hepsilon : ∀ r, epsilon r ≠ 0),
              V = QuarticNet.suppliedFrameTangent U rho (fun r => supplied r j) epsilon ∧
              (∀ r, (suppliedE r).hom ≫ Spec.map (CommRingCat.ofHom
                (QuarticNet.dualNumberRescaleEquiv (epsilon r) (hepsilon r)).toRingHom) =
                (canonicalE r).hom) ∧
              (actualComponentProductDualIso Y suppliedE).hom ≫
                Spec.map (CommRingCat.ofHom
                  (QuarticNet.fourTangentDualRescaleEquiv epsilon hepsilon).toRingHom) =
                (actualComponentProductDualIso Y canonicalE).hom ∧
              (letI : IsIso (Sigma.desc c) := hWholeIso;
                (((asIso (Sigma.desc c)).symm ≪≫ actualComponentProductDualIso Y suppliedE).hom) ≫
                  Spec.map (CommRingCat.ofHom
                    (QuarticNet.fourTangentDualRescaleEquiv epsilon hepsilon).toRingHom) =
                  ((asIso (Sigma.desc c)).symm ≪≫ actualComponentProductDualIso Y canonicalE).hom) ∧
              ((∀ r s, V r s = -V s r) → (∃ r s, r ≠ s ∧ V r s = 0) →
                ∃ l : Fin 4 → K, (∀ r, l r ≠ 0) ∧
                  (∀ r s, QuarticNet.rescaleTangentDirections l U r s =
                    -QuarticNet.rescaleTangentDirections l U s r) ∧
                  (∃ r s, r ≠ s ∧ U r s = 0) ∧
                  OriginalEmbeddedZeroEntryGeometry p hp
                    (i ≫ quotientProjMap (equationIdeal p hp)) ∧
                  (∃ s : Spec (.of k) ⟶ hypersurface p hp,
                    s ≫ hypersurfaceToBase p hp = 𝟙 _))
    := @PfaffianDescent.singleSupport_originalZ_supplied_frame_epsilon_zero_entry_geometry

end
end PfaffianDescent.ManuscriptComparators

namespace PfaffianDescent.ManuscriptComparators
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial Module
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false

/-- 4.9: `prop:existence-of-Z` (2-proofs.tex:888). -/
theorem claim_4_9 :
    ∀ {K : Type u} [Field K] [PerfectField K]
    (p : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)]
    (x : closedPoints (hypersurface p hp))
    (h4 : (hypersurfaceToBase p hp).residueDegree x.1 = 4)
    (hspan : ProjectiveGeometricGeneralPosition (equationIdeal p hp)
      ((hypersurface p hp).fromSpecResidueField x.1)),
        letI := AllCharacteristics.pointAlgebra (hypersurfaceToBase p hp) x.1
        letI := AllCharacteristics.closedPoint_moduleFinite (hypersurfaceToBase p hp) x
        let L := (hypersurface p hp).residueField x.1
        letI : Module.Finite K (DualNumber L) := QuarticNet.dualNumber_moduleFinite
        ∃ q : Spec (.of (DualNumber L)) ⟶ hypersurface p hp,
          ∃ hq : IsClosedImmersion q,
            letI : IsClosedImmersion q := hq
            q ≫ hypersurfaceToBase p hp =
              Spec.map (CommRingCat.ofHom (algebraMap K (DualNumber L))) ∧
            Set.range q = {x.1} ∧
            Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom L L L).toRingHom) ≫ q =
              (hypersurface p hp).fromSpecResidueField x.1 ∧
            ∃ hfinite : IsFinite (q ≫ hypersurfaceToBase p hp),
              @AllCharacteristics.finiteSchemeRank K _ _ (q ≫ hypersurfaceToBase p hp) hfinite = 8 ∧
              (∃ (J : Type u) (_ : Fintype J), Fintype.card J = 4 ∧
                Nonempty (pullback (Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicClosure K))))
                  (q ≫ hypersurfaceToBase p hp) ≅
                  ∐ fun _ : J => Spec (.of (DualNumber (AlgebraicClosure K))))) ∧
              3 ≤ finrank K (SchemeModuleGlobalSectionsOver
                (ambientToBase (R := K) (σ := Fin 4))
                (closedImmersionIdealTwist
                  (q ≫ hypersurfaceToAmbient p hp)
                  (ProjectiveNegativeTwist.positiveSheafOfModules
                    (homogeneousSubmodule (Fin 4) K) 2)))
    := @PfaffianDescent.perfectField_closedQuarticPoint_exists_original_tangentSubscheme_actualHZero

end
end PfaffianDescent.ManuscriptComparators
