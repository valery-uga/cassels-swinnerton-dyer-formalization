import PfaffianDescent.SchemeModuleFiniteClosedSupportOriginalBaseGerms
import PfaffianDescent.CorayNormalizationNonzeroSignedWordCokernelFiniteSupport
import PfaffianDescent.CorayNormalizationNonzeroSignedWordStalkWeightedLength
import PfaffianDescent.CorayFiniteSchemeGenericNormalization

/-! Primitive original-K global dimension of the SAME actual nonzero
signed-word section cokernel. Finite closed support and local finite length
are constructed by the original normalization producers. The actual
original-K germ-product equivalence supplies the global weighted sum.
Depends on UNVERIFIED weighted companion006/local caller003 and generic
finite-closed-support germ001. No new comparison/geometry premise.
SOURCE ONLY / UNVERIFIED. Root alone compiles. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AllCharacteristics.HomogeneousProjective
open scoped BigOperators
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Ordinary bounded finite-type assembly for the SAME original projection. -/
private theorem originalGenericNormalizationProjection_locallyOfFiniteType
    (X : Scheme.{u}) [IsIntegral X]
    (pi : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType pi] :
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    LocallyOfFiniteType ((X.fromSpecStalk (genericPoint X)).fromNormalization ≫ pi) := by
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  letI : IsFinite (X.fromSpecStalk (genericPoint X)).fromNormalization :=
    integralScheme_genericNormalization_isFinite X pi
  infer_instance

/-- Native finite length only, from the SAME actual primitive stalk quotient.
This helper does not elaborate unused K-finiteness or weighted outputs. -/
private theorem originalNonzeroSignedWordSection_nativeStalkFiniteLength
    (p q : MvPolynomial (Fin 4) K) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hn : 0 < n) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) K)))
    [IsIntegral (scheme (projectiveIntersectionIdeal p q hp hq))] :
    let I := projectiveIntersectionIdeal p q hp hq
    let X := scheme I
    letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
    let N := (X.fromSpecStalk (genericPoint X)).normalization
    ∀ ops : List (closedPoints N × Bool),
      let W := schemeModuleIteratedSignedClosedPointTensor (SheafOfModules.unit N.ringCatSheaf) ops
      ∀ (s : W.val.obj (op ⊤)), s ≠ 0 → ∀ P : closedPoints N,
        IsFiniteLength (N.presheaf.stalk P.1)
          ((schemeModuleStalkModuleFunctor N P.1).obj (cokernel (schemeModuleTopSectionHom W s))) := by
  classical
  intro I X N ops W s hs P
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  obtain ⟨_eW, _ha, _hπ, _hlen, hlocal⟩ :=
    projectiveIntersection_genericNormalization_nonzeroSignedWordSection_stalkPrincipalQuotient
      p q hp hp0 n hn hq hnot ops s hs P
  exact hlocal

/-- Bounded final assembly for actual original-K germs and weighted sections.
Its natural support/length inputs are discharged by the primitive caller. -/
private theorem originalBaseFiniteClosedSupport_germEquiv_and_weighted_finrank
    {Y : Scheme.{u}} (pi : Y ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType pi]
    (M : Y.Modules) (C : Set Y) (hC : C.Finite)
    (hclosed : ∀ x ∈ C, IsClosed ({x} : Set Y))
    (hsupport : schemeModuleStalkSupport M ⊆ C)
    (hlength : ∀ x : C, IsFiniteLength (Y.presheaf.stalk x.1)
      ((schemeModuleStalkModuleFunctor Y x.1).obj M)) :
    ∃ e : SchemeModuleOpenSectionsOver pi M ⊤ ≃ₗ[K]
        (∀ x : C, SchemeModuleStalkOver pi M x.1),
      (∀ (t : SchemeModuleOpenSectionsOver pi M ⊤) (x : C),
        e t x = (show SchemeModuleStalkOver pi M x.1 from
          (Scheme.Modules.presheaf (X := Y) M).germ ⊤ x.1 trivial t)) ∧
      Module.Finite K (SchemeModuleOpenSectionsOver pi M ⊤) ∧
      (letI : Fintype C := hC.fintype;
        Module.finrank K (SchemeModuleOpenSectionsOver pi M ⊤) =
          ∑ x : C, (Module.length (Y.presheaf.stalk x.1)
            ((schemeModuleStalkModuleFunctor Y x.1).obj M)).toNat * pi.residueDegree x.1) := by
  classical
  letI : Fintype C := hC.fintype
  let e := schemeModuleOriginalBaseTopGermsLinearEquiv pi M C hC hclosed hsupport
  obtain ⟨hground, hdim⟩ := schemeModuleOriginalBaseTopSections_finite_and_weighted_finrank
    pi M C hC hclosed hsupport hlength
  refine ⟨e, ?_, hground, hdim⟩
  intro t x
  exact schemeModuleOriginalBaseTopGermsLinearMap_apply pi M C t x

/-- The SAME original cokernel has finite original-K global sections;
its actual original germ map is a K-linear equivalence with its finitely
many support stalks, and dimension is the actual native-length weighted
sum. Every support/finite-length/finite-type input is derived internally.
The section is GIVEN nonzero; neither its existence nor normalization
constants equal to K, genus, or a signed-word numerical degree is asserted. -/
theorem projectiveIntersection_genericNormalization_nonzeroSignedWordSection_cokernel_topSections_finite_and_weighted_finrank
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
      ∀ (s : W.val.obj (op ⊤)), s ≠ 0 →
        let Q := cokernel (schemeModuleTopSectionHom W s)
        let C := schemeModuleStalkSupport Q
        ∃ hC : C.Finite,
          ∃ e : SchemeModuleOpenSectionsOver pi Q ⊤ ≃ₗ[K]
              (∀ x : C, SchemeModuleStalkOver pi Q x.1),
            (∀ (t : SchemeModuleOpenSectionsOver pi Q ⊤) (x : C),
              e t x = (show SchemeModuleStalkOver pi Q x.1 from
                (Scheme.Modules.presheaf (X := N) Q).germ ⊤ x.1 trivial t)) ∧
            Module.Finite K (SchemeModuleOpenSectionsOver pi Q ⊤) ∧
            (letI : Fintype C := hC.fintype;
              Module.finrank K (SchemeModuleOpenSectionsOver pi Q ⊤) =
                ∑ x : C, (Module.length (N.presheaf.stalk x.1)
                  ((schemeModuleStalkModuleFunctor N x.1).obj Q)).toNat *
                    pi.residueDegree x.1) := by
  classical
  intro I X N nu pi
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  letI : LocallyOfFiniteType (toBase I) := inferInstance
  letI : LocallyOfFiniteType pi := originalGenericNormalizationProjection_locallyOfFiniteType X (toBase I)
  intro ops W s hs Q C
  obtain ⟨_hclosed, hfinite, hpoints⟩ :=
    projectiveIntersection_genericNormalization_nonzeroSignedWordSection_cokernel_stalkSupport_finite_closed
      p q hp hp0 n hn hq hnot ops s hs
  have hlength (x : C) : IsFiniteLength (N.presheaf.stalk x.1)
      ((schemeModuleStalkModuleFunctor N x.1).obj Q) :=
    originalNonzeroSignedWordSection_nativeStalkFiniteLength p q hp hp0 n hn hq hnot ops s hs
      (show closedPoints N from ⟨x.1, hpoints x.1 x.2⟩)
  exact ⟨hfinite, originalBaseFiniteClosedSupport_germEquiv_and_weighted_finrank
    pi Q C hfinite hpoints Set.Subset.rfl hlength⟩

end PfaffianDescent.Coray
