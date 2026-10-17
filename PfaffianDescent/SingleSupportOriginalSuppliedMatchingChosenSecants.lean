import PfaffianDescent.ActualChosenMatchingGroundSecant
import PfaffianDescent.SingleSupportOriginalSuppliedMatchingLineIdentification

/-! SOURCE ONLY / UNVERIFIED. Extend the existing supplied-frame theorem
with chosen ground secants, retaining its FULL original Z/i/P hypotheses,
original ambient squares and SAME canonical E in the complete line package.
No supplied ground secant, desired field or comparison is a primitive input. -/
noncomputable section
namespace PfaffianDescent
open Module MvPolynomial AlgebraicGeometry CategoryTheory CategoryTheory.Limits TrivSqZeroExt
open AllCharacteristics.HomogeneousProjective
open scoped TensorProduct
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

def OriginalMatchingQuadraticLinePairObjectsWithChosenSecants
    {k : Type u} [Field k]
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (B : Basis (Fin 4) (AlgebraicClosure k) (Fin 4 → AlgebraicClosure k)) : Prop :=
  ∃ E : IntermediateField k (AlgebraicClosure k), ∃ _ : FiniteDimensional k E,
    finrank k E = 2 ∧ IsGalois k E ∧
    E = IntermediateField.adjoin k (Set.range (fun m => B 0 m + B 1 m)) ∧
    ∃ P : Matrix (Fin 4) (Fin 4) E,
      P.map E.val.toRingHom = QuarticNet.matchingEdgeProjectorMatrix B ∧
      ∃ sigma : E ≃ₐ[k] E, sigma ≠ 1 ∧ sigma ^ 2 = 1 ∧
        P.map sigma.toRingHom = 1 - P ∧
        (QuarticNet.projectorLineIdeal P).toIdeal.map (MvPolynomial.map sigma.toRingHom) =
          (QuarticNet.projectorLineIdeal (1 - P)).toIdeal ∧
        (QuarticNet.projectorLineIdeal (1 - P)).toIdeal.map (MvPolynomial.map sigma.toRingHom) =
          (QuarticNet.projectorLineIdeal P).toIdeal ∧
        (∀ side : Bool,
          let I := QuarticNet.projectorLineIdeal (QuarticNet.matchingSideProjector P side)
          let I' := QuarticNet.projectorLineIdeal (QuarticNet.matchingSideProjector P (!side))
          ∃ hExchange : I.toIdeal.map (MvPolynomial.map sigma.toRingHom) = I'.toIdeal,
            IsPullback (projectiveCoefficientMap sigma.toRingHom I I' hExchange)
              (toBase I') (toBase I) (Spec.map (CommRingCat.ofHom sigma.toRingHom))) ∧
        (∀ side : Bool,
          ∃ e : scheme (QuarticNet.projectorLineIdeal
              (QuarticNet.matchingSideProjector P side)) ≅ Proj (homogeneousSubmodule (Fin 2) E),
            e.hom ≫ ambientToBase (R := E) (σ := Fin 2) =
              toBase (QuarticNet.projectorLineIdeal (QuarticNet.matchingSideProjector P side))) ∧
        (∀ side : Bool,
          ∃ c : scheme (QuarticNet.projectorLineIdeal
              (QuarticNet.matchingSideProjector P side)) ⟶
                hypersurface (MvPolynomial.map (algebraMap k E) F) (hF.map (algebraMap k E)),
            IsClosedImmersion c ∧
            c ≫ quotientProjMap (equationIdeal (MvPolynomial.map (algebraMap k E) F)
              (hF.map (algebraMap k E))) =
              quotientProjMap (QuarticNet.projectorLineIdeal (QuarticNet.matchingSideProjector P side))) ∧
        Disjoint (Set.range (quotientProjMap (QuarticNet.projectorLineIdeal P)))
          (Set.range (quotientProjMap (QuarticNet.projectorLineIdeal (1 - P)))) ∧
        (∀ side : Bool,
          let IE := QuarticNet.projectorLineIdeal (QuarticNet.matchingSideProjector P side)
          let IK := QuarticNet.projectorLineIdeal
            (QuarticNet.matchingSideProjector (QuarticNet.matchingEdgeProjectorMatrix B) side)
          ∃ hBC : IE.toIdeal.map (MvPolynomial.map E.val.toRingHom) = IK.toIdeal,
            IK.toIdeal = (QuarticNet.coordinateMatchingLineIdeal (K := AlgebraicClosure k) side).toIdeal.map
              (linearSubstitution (QuarticNet.basisCoordinateMatrix B)⁻¹).toRingHom ∧
            IsPullback (projectiveCoefficientMap E.val.toRingHom IE IK hBC)
              (toBase IK) (toBase IE) (Spec.map (CommRingCat.ofHom E.val.toRingHom))) ∧
        (∀ a : Spec (.of E) ⟶ scheme (QuarticNet.projectorLineIdeal P),
          a ≫ toBase (QuarticNet.projectorLineIdeal P) = 𝟙 _ →
            ActualChosenMatchingGroundSecantAt P sigma a) ∧
        ∃ J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k),
          J.toIdeal.map (MvPolynomial.map (algebraMap k E)) =
            (QuarticNet.matchingProjectorIntersectionIdeal P).toIdeal ∧
          J.toIdeal.map (MvPolynomial.map (algebraMap k (AlgebraicClosure k))) =
            (QuarticNet.coordinateMatchingUnionIdeal (K := AlgebraicClosure k)).toIdeal.map
              (linearSubstitution (QuarticNet.basisCoordinateMatrix B)⁻¹).toRingHom ∧
          ∃ cGround : scheme J ⟶ hypersurface F hF,
            IsClosedImmersion cGround ∧
            cGround ≫ quotientProjMap (equationIdeal F hF) = quotientProjMap J

def OriginalMatchingQuadraticLinePairOnSuppliedFrameWithChosenSecants
    {k : Type u} [Field k]
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (supplied : Basis (Fin 4) (AlgebraicClosure k) (Fin 4 → AlgebraicClosure k))
    (V : Fin 4 → Fin 4 → AlgebraicClosure k) : Prop :=
  ∃ pi : Equiv.Perm (Fin 4),
    (∀ r s, V (pi r) (pi s) ≠ 0 ↔ QuarticNet.coordinateMatchingAdj r s) ∧
    ∃ B : Basis (Fin 4) (AlgebraicClosure k) (Fin 4 → AlgebraicClosure k),
      OriginalMatchingQuadraticLinePairObjectsWithChosenSecants F hF B ∧
      ∀ side : Bool,
        (QuarticNet.coordinateMatchingLineIdeal (K := AlgebraicClosure k) side).toIdeal.map
          (linearSubstitution (QuarticNet.basisCoordinateMatrix
            (supplied.reindex pi.symm))⁻¹).toRingHom =
        (QuarticNet.projectorLineIdeal (QuarticNet.matchingSideProjector
          (QuarticNet.matchingEdgeProjectorMatrix B) side)).toIdeal


/-- Internal consequence of the already constructed full object package.
The SAME E/P/sigma witnesses are retained, including both original lines,
supplied ambient identifications and the original descended union. -/
theorem originalMatchingQuadraticLinePairObjects_add_chosen_groundSecants
    {k : Type u} [Field k]
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (B : Basis (Fin 4) (AlgebraicClosure k) (Fin 4 → AlgebraicClosure k))
    (h : OriginalMatchingQuadraticLinePairObjects F hF B) :
    OriginalMatchingQuadraticLinePairObjectsWithChosenSecants F hF B := by
  obtain ⟨E, hFD, hDeg, hGal, hE, P, hP, sigma, hNe, hSq, hEx,
    hLine, hOther, hSquares, hP1, hCubic, hDisjoint, hBC, hGroundUnion⟩ := h
  letI : FiniteDimensional k E := hFD
  exact ⟨E, hFD, hDeg, hGal, hE, P, hP, sigma, hNe, hSq, hEx,
    hLine, hOther, hSquares, hP1, hCubic, hDisjoint, hBC,
    fun a ha => actualChosenMatchingPoint_groundSecant hDeg P sigma hNe hEx a ha,
    hGroundUnion⟩

/-- The supplied frame's two exact ideals and SAME canonical quadratic field
are preserved; only the new secant construction is appended. -/
theorem originalSuppliedMatchingLinePair_add_chosen_groundSecants
    {k : Type u} [Field k]
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (supplied : Basis (Fin 4) (AlgebraicClosure k) (Fin 4 → AlgebraicClosure k))
    (V : Fin 4 → Fin 4 → AlgebraicClosure k)
    (h : OriginalMatchingQuadraticLinePairOnSuppliedFrame F hF supplied V) :
    OriginalMatchingQuadraticLinePairOnSuppliedFrameWithChosenSecants F hF supplied V := by
  obtain ⟨pi, hEdges, B, hObjects, hIdeals⟩ := h
  exact ⟨pi, hEdges, B,
    originalMatchingQuadraticLinePairObjects_add_chosen_groundSecants F hF B hObjects, hIdeals⟩

variable {k : Type u} [Field k] [PerfectField k]

set_option backward.isDefEq.respectTransparency false in
/-- Primitive caller for the SAME original finite closed rank-eight Z.
The stipulated supplied frame/component presentation, skewness and n=1
retain precisely the existing literal manuscript scope. The desired
quadratic lines, ground secants and comparisons are all conclusions. -/
theorem singleSupport_originalZ_supplied_matching_chosen_ground_secants
    (p : MvPolynomial (Fin 4) k) (hp : p.IsHomogeneous 3)
    {Z : Scheme.{u}} (i : Z ⟶ scheme (equationIdeal p hp)) [IsClosedImmersion i]
    [IsFinite (i ≫ toBase (equationIdeal p hp))] (P : closedPoints (scheme (equationIdeal p hp)))
    (hSupport : Set.range i = {P.1})
    (hP : (toBase (equationIdeal p hp)).residueDegree P.1 = 4)
    (hGeom : ProjectiveGeometricGeneralPosition (equationIdeal p hp) ((scheme (equationIdeal p hp)).fromSpecResidueField P.1)) :
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
      (∀ r, eA (x r) = inl (b r) + inr (v r)) ∧
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
      ∀ (V : Fin 4 → Fin 4 → K) (hV : ∀ r, V r r = 0)
        (suppliedE : ∀ r, Y r ≅ Spec (.of (DualNumber K))),
        (∀ r, (suppliedE r).hom ≫ ambientNormalizedCoordinateChartPoint (F := K)
          (QuarticNet.tangentDualPoint V r) r (by simp [QuarticNet.tangentDualPoint, hV]) ≫
          (linearCoordinateChangeAmbientIso (QuarticNet.basisCoordinateMatrix supplied)
            (QuarticNet.basisCoordinateMatrix_isUnit supplied)).inv = c r ≫ qOriginal) →
        (∀ r s, V r s = -V s r) → (∀ r, ∃! s, V r s ≠ 0) →
        OriginalMatchingQuadraticLinePairOnSuppliedFrameWithChosenSecants p hp supplied V := by
  classical
  dsimp only
  let I := equationIdeal p hp
  letI : IsAffine Z := isAffine_of_isAffineHom (i ≫ toBase I)
  letI := finiteSchemeCoefficientAlgebra (i ≫ toBase I)
  letI := finiteSchemeCoefficient_finite (i ≫ toBase I)
  letI := AllCharacteristics.pointAlgebra (toBase I) P.1
  letI := AllCharacteristics.closedPoint_moduleFinite (toBase I) P
  intro hZ
  obtain ⟨j, x, hxj, eA, b, hbj, v, full, hvj, hv, hOriginal,
    hFx, hgen, hcoords, hOriginalSquare, hFactory⟩ :=
    singleSupport_originalZ_supplied_matching_line_ideals p hp i P hSupport hP hGeom hZ
  refine ⟨j, x, hxj, eA, b, hbj, v, full, hvj, hv, hOriginal,
    hFx, hgen, hcoords, hOriginalSquare, ?_⟩
  intro supplied hFrameSupport Y c hClosed hDisjoint hComponentSupport hRank
    V hV suppliedE hSupplied hSkew hOne
  exact originalSuppliedMatchingLinePair_add_chosen_groundSecants p hp supplied V
    (@hFactory supplied hFrameSupport Y c hClosed hDisjoint hComponentSupport hRank
      V hV suppliedE hSupplied hSkew hOne)

end PfaffianDescent
