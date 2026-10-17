import PfaffianDescent.ActualMatchingGroundUnionInOriginalCubic
import PfaffianDescent.ActualMatchingQuadraticProjectorExchange
import PfaffianDescent.IntrinsicFullQuadraticSystem
import PfaffianDescent.QuarticZeroEntrySupportGraph

/-! SOURCE ONLY / UNVERIFIED. Stronger literal matching objects, not a
replacement rational-point proof. One internally derived quadratic E has
two disjoint actual P1-lines in the SAME original cubic, exchanged by its
nonidentity automorphism; exact original geometric ideals and Cartesian
base changes are outputs. No field/line/projector certificate is an input. -/
noncomputable section
namespace PfaffianDescent
open Module MvPolynomial AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

def OriginalMatchingQuadraticLinePairObjects
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
        ∃ J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) k),
          J.toIdeal.map (MvPolynomial.map (algebraMap k E)) =
            (QuarticNet.matchingProjectorIntersectionIdeal P).toIdeal ∧
          J.toIdeal.map (MvPolynomial.map (algebraMap k (AlgebraicClosure k))) =
            (QuarticNet.coordinateMatchingUnionIdeal (K := AlgebraicClosure k)).toIdeal.map
              (linearSubstitution (QuarticNet.basisCoordinateMatrix B)⁻¹).toRingHom ∧
          ∃ cGround : scheme J ⟶ hypersurface F hF,
            IsClosedImmersion cGround ∧
            cGround ≫ quotientProjMap (equationIdeal F hF) = quotientProjMap J

def OriginalMatchingQuadraticLineGeometry
    {k : Type u} [Field k] (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3) : Prop :=
  ∃ B : Basis (Fin 4) (AlgebraicClosure k) (Fin 4 → AlgebraicClosure k),
    OriginalMatchingQuadraticLinePairObjects F hF B

/-- The labelled geometric frame is the original conjugate frame: only a
vertex permutation is chosen, and its matching support is also retained. -/
def OriginalMatchingQuadraticLineGeometryAt
    {k : Type u} [Field k] (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (B : Basis (Fin 4) (AlgebraicClosure k) (Fin 4 → AlgebraicClosure k))
    (U : Fin 4 → Fin 4 → AlgebraicClosure k) : Prop :=
  ∃ pi : Equiv.Perm (Fin 4),
    (∀ r s, U (pi r) (pi s) ≠ 0 ↔ QuarticNet.coordinateMatchingAdj r s) ∧
    OriginalMatchingQuadraticLinePairObjects F hF (B.reindex pi.symm)

def OriginalEmbeddedZeroEntryQuadraticGeometry
    {k : Type u} [Field k] (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    {Z : Scheme.{u}} (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) k)) : Prop :=
  OriginalMatchingQuadraticLineGeometry F hF ∨
    IsFinite (toBase (intrinsicFullQuadraticBaseIdeal i))

namespace QuarticNet
variable {k L : Type u} [Field k] [PerfectField k] [Field L] [Algebra k L]

/-- The matching normal form is legitimate branch data. All field, line,
Galois, original cubic containment, and base-change objects are derived. -/
theorem originalMatchingBranch_actualQuadraticLinePair
    (full : Fin 4 ≃ (L →ₐ[k] AlgebraicClosure k)) (p v : Fin 4 → L)
    (hs : Submodule.span (AlgebraicClosure k) (Set.range (fun sigma : L →ₐ[k] AlgebraicClosure k =>
      fun m => sigma (p m))) = ⊤)
    (l : Fin 4 → AlgebraicClosure k) (hl : ∀ r, l r ≠ 0) (pi : Equiv.Perm (Fin 4))
    (a f : AlgebraicClosure k) (ha : a ≠ 0) (hf : f ≠ 0)
    (hU : tangentRelabel (rescaleTangentDirections l
      (conjugateTangentMatrix full p v hs)) pi = skewTangentDirections a 0 0 0 0 f)
    (F : MvPolynomial (Fin 4) k) (hF : F.IsHomogeneous 3)
    (hvan : ∀ r, aeval (tangentDualPoint (skewTangentDirections a 0 0 0 0 f) r)
      (linearSubstitution (basisCoordinateMatrix ((conjugateBasis full p hs).reindex pi.symm))
        (MvPolynomial.map (algebraMap k (AlgebraicClosure k)) F)) = 0) :
    OriginalMatchingQuadraticLinePairObjects F hF
      ((conjugateBasis full p hs).reindex pi.symm) := by
  classical
  let B := (conjugateBasis full p hs).reindex pi.symm
  obtain ⟨E, hFD, hdeg, hGal, hE, P, hP, hKernel, hOtherKernel,
      J, hJE, hJK, hUnion, hContain, cGround, hcGround, hAmbientGround⟩ :=
    actualMatching_ground_union_in_original_cubic full p v hs l hl pi a f ha hf hU F hF hvan
  letI : FiniteDimensional k E := hFD
  letI : IsGalois k E := hGal
  obtain ⟨sigma, hNe, hSquare, hExchange, hLineExchange, hOtherExchange⟩ :=
    actualMatching_quadratic_projector_exchange full p v hs l hl pi a f ha hU E hdeg P hP
  have hLines := intermediateMatchingBothLines_projectiveLine_isos E P B hP
  have hBaseChange := intermediateMatchingBothLines_original_baseChange E P B hP
  have hSchemeExchange : ∀ side : Bool,
      let I := projectorLineIdeal (matchingSideProjector P side)
      let I' := projectorLineIdeal (matchingSideProjector P (!side))
      ∃ hExchange : I.toIdeal.map (MvPolynomial.map sigma.toRingHom) = I'.toIdeal,
        IsPullback (projectiveCoefficientMap sigma.toRingHom I I' hExchange)
          (toBase I') (toBase I) (Spec.map (CommRingCat.ofHom sigma.toRingHom)) := by
    intro side
    cases side
    · exact ⟨hLineExchange, isPullback_projectiveCoefficientMap _ _ _ hLineExchange⟩
    · exact ⟨hOtherExchange, isPullback_projectiveCoefficientMap _ _ _ hOtherExchange⟩
  have hCubic : ∀ side : Bool,
      ∃ c : scheme (projectorLineIdeal (matchingSideProjector P side)) ⟶
          hypersurface (MvPolynomial.map (algebraMap k E) F) (hF.map (algebraMap k E)),
        IsClosedImmersion c ∧
        c ≫ quotientProjMap (equationIdeal (MvPolynomial.map (algebraMap k E) F)
          (hF.map (algebraMap k E))) =
          quotientProjMap (projectorLineIdeal (matchingSideProjector P side)) := by
    intro side
    let FE := MvPolynomial.map (algebraMap k E) F
    have hFJ : F ∈ J.toIdeal := hContain (Ideal.subset_span (by simp))
    have hFE : FE ∈ (matchingProjectorIntersectionIdeal P).toIdeal := by
      rw [← hJE]
      exact Ideal.mem_map_of_mem _ hFJ
    have hSide : FE ∈ (projectorLineIdeal (matchingSideProjector P side)).toIdeal := by
      cases side
      · exact hFE.1
      · exact hFE.2
    have hContainSide : (equationIdeal FE (hF.map (algebraMap k E))).toIdeal ≤
        (projectorLineIdeal (matchingSideProjector P side)).toIdeal := by
      apply Ideal.span_le.mpr
      rintro q rfl
      exact hSide
    let c := schemeQuotientMap (equationIdeal FE (hF.map (algebraMap k E)))
      (projectorLineIdeal (matchingSideProjector P side)) hContainSide
    have hc : IsClosedImmersion c :=
      schemeQuotientMap_closedImmersion (equationIdeal FE (hF.map (algebraMap k E)))
        (projectorLineIdeal (matchingSideProjector P side)) hContainSide
    exact ⟨c, hc, schemeQuotientMap_comp_quotientProjMap _ _ _⟩
  exact ⟨E, hFD, hdeg, hGal, hE, P, hP,
    sigma, hNe, hSquare, hExchange, hLineExchange, hOtherExchange,
    hSchemeExchange, hLines, hCubic, complementaryProjectorLines_disjoint P, hBaseChange,
    J, hJE, hUnion, cGround, hcGround, hAmbientGround⟩

end QuarticNet
end PfaffianDescent
