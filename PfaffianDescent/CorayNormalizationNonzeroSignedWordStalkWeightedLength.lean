import PfaffianDescent.SchemeModuleOriginalBaseWeightedStalk
import PfaffianDescent.CorayNormalizationNonzeroSignedWordStalkQuotient
import PfaffianDescent.CorayFiniteSchemeGenericNormalization

/-! Original-K weighted native local length for the SAME given nonzero
signed-word section. Finite normalization supplies finite type of the
original structure morphism, hence finite actual residue degree. The frame,
coefficient, original cokernel projection and DVR length come from the
actual previously constructed native quotient. No section-existence,
global decomposition, cycle-degree or normalization-constants claim.
SOURCE ONLY / UNVERIFIED. Root alone compiles. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Primitive original-K finite dimension and weighted local length for
the SAME actual cokernel and section, retaining its original projection.
No frame, Mono, DVR, residue comparison, finite-degree or length premise
is supplied; all arise from original geometric inputs. -/
theorem projectiveIntersection_genericNormalization_nonzeroSignedWordSection_stalkWeightedLength
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
    let pi := nu ≫ toBase I
    ∀ ops : List (closedPoints N × Bool),
      let W := schemeModuleIteratedSignedClosedPointTensor (SheafOfModules.unit N.ringCatSheaf) ops
      ∀ (s : W.val.obj (op ⊤)), s ≠ 0 → ∀ P : closedPoints N,
        let R := N.presheaf.stalk P.1
        letI : IsDiscreteValuationRing R :=
          projectiveIntersection_genericNormalization_nongeneric_stalk_isDVR p q hp hp0 n hq hnot P.1
            (projectiveIntersection_genericNormalization_closedPoint_ne_generic p q hp hq P)
        let F := schemeModuleStalkModuleFunctor N P.1
        let φ := schemeModuleTopSectionHom W s
        ∃ eW : F.obj W ≅ ModuleCat.of R R,
          let a := schemeModuleUnitHomStalkCoefficient W φ P.1 eW
          a ≠ 0 ∧
            F.map (cokernel.π φ) ≫
              (schemeModuleUnitHomStalkCokernelIsoPrincipalQuotient W φ P.1 eW).hom =
                eW.hom ≫ ModuleCat.ofHom (Algebra.linearMap R (R ⧸ Ideal.span ({a} : Set R))) ∧
            Module.length R (F.obj (cokernel φ)) = IsDiscreteValuationRing.addVal R a ∧
            IsFiniteLength R (F.obj (cokernel φ)) ∧
            Module.Finite K (SchemeModuleStalkOver pi (cokernel φ) P.1) ∧
            Module.finrank K (SchemeModuleStalkOver pi (cokernel φ) P.1) =
              (IsDiscreteValuationRing.addVal R a).toNat * pi.residueDegree P.1 := by
  classical
  dsimp only
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let pi := nu ≫ toBase I
  letI : LocallyOfFiniteType (toBase I) := inferInstance
  letI : IsFinite nu := integralScheme_genericNormalization_isFinite X (toBase I)
  letI : LocallyOfFiniteType pi := inferInstance
  intro ops
  let W := schemeModuleIteratedSignedClosedPointTensor (SheafOfModules.unit N.ringCatSheaf) ops
  intro s hs P
  let R := N.presheaf.stalk P.1
  letI : IsDiscreteValuationRing R :=
    projectiveIntersection_genericNormalization_nongeneric_stalk_isDVR p q hp hp0 n hq hnot P.1
      (projectiveIntersection_genericNormalization_closedPoint_ne_generic p q hp hq P)
  let F := schemeModuleStalkModuleFunctor N P.1
  let φ := schemeModuleTopSectionHom W s
  obtain ⟨eW, ha, hπ, hlen, hfinite⟩ :=
    projectiveIntersection_genericNormalization_nonzeroSignedWordSection_stalkPrincipalQuotient
      p q hp hp0 n hn hq hnot ops s hs P
  have hw := schemeModuleOriginalBaseStalk_finite_and_finrank pi (cokernel φ) P hfinite
  refine ⟨eW, ha, hπ, hlen, hfinite, hw.1, ?_⟩
  exact hw.2.trans (congrArg (fun d : ENat => d.toNat * pi.residueDegree P.1) hlen)

end PfaffianDescent.Coray
