import PfaffianDescent.SchemeModuleClosedPointCenteredStalkFieldRanges

/-! Primitive SAME-normalization centered positive/negative image alignment.
The actual affine regular generator is constructed internally once, then
its SAME irreducible germ controls both images on every common complement.
Original ideal, dual, normalization, inclusion and scalar maps are retained.
SOURCE ONLY / UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AllCharacteristics.HomogeneousProjective IdealSheafDataModule
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Assemble the actual affine witness at ordinary scheme types before
specializing to normalization. The input is actual regular-principal
geometry, not an image, uniformizer, valuation or comparison certificate. -/
private theorem centeredStalkFieldRanges_of_regularGenerator
    {X : Scheme.{u}} [IsIntegral X]
    (pi : X ⟶ Spec (CommRingCat.of K)) (P : closedPoints X)
    (hgen :
      let i := X.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      let M := (show X.Modules from closedImmersionModule i)
      ∃ V : X.affineOpens, P.1 ∈ V.1 ∧ ∃ m : M.val.obj (op V.1),
        let z : Γ(X, V.1) := (closedImmersionModuleToUnit i).val.app (op V.1) m
        IsRegular z ∧ i.ker.ideal V = Ideal.span ({z} : Set Γ(X, V.1))) :
    let i := X.fromSpecResidueField P.1
    letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
    let M := (show X.Modules from closedImmersionModule i)
    let D := SchemeModuleInternalHom.dual M
    letI := schemeModuleStalkModule M P.1
    letI := schemeModuleStalkModule D P.1
    ∃ (V : X.affineOpens) (hPV : P.1 ∈ V.1) (m : M.val.obj (op V.1)),
      let z : Γ(X, V.1) := (closedImmersionModuleToUnit i).val.app (op V.1) m
      let zP := X.presheaf.germ V.1 P.1 hPV z
      IsRegular z ∧ i.ker.ideal V = Ideal.span ({z} : Set Γ(X, V.1)) ∧
        IsLocalRing.maximalIdeal (X.presheaf.stalk P.1) =
          Ideal.span ({zP} : Set (X.presheaf.stalk P.1)) ∧
        Irreducible zP ∧
        ∀ (C : X.Opens) (hC : Nonempty C) (hPC : P.1 ∉ C),
          letI : Nonempty C := hC
          Set.range (schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi M C
            (schemeModuleClosedPointIdealOverCanonicalIso P C hPC) P.1) =
            Set.range (fun r : X.presheaf.stalk P.1 =>
              @HMul.hMul X.functionField X.functionField X.functionField inferInstance
                (algebraMap (X.presheaf.stalk P.1) X.functionField r)
                (algebraMap (X.presheaf.stalk P.1) X.functionField zP)) ∧
          Set.range (schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi D C
            (schemeModuleClosedPointDualOverCanonicalIso P C hPC) P.1) =
            Set.range (fun r : X.presheaf.stalk P.1 =>
              algebraMap (X.presheaf.stalk P.1) X.functionField r /
                algebraMap (X.presheaf.stalk P.1) X.functionField zP) := by
  dsimp only at hgen ⊢
  let i := X.fromSpecResidueField P.1
  letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
  let M := (show X.Modules from closedImmersionModule i)
  let D := SchemeModuleInternalHom.dual M
  letI := schemeModuleStalkModule M P.1
  letI := schemeModuleStalkModule D P.1
  obtain ⟨V, hPV, m, hreg, hprincipal⟩ := hgen
  refine ⟨V, hPV, m, hreg, hprincipal,
    closedPointIdeal_affineGenerator_germ_maximalIdeal X P V hPV m hprincipal,
    closedPointIdeal_affineRegularGenerator_germ_irreducible X P V hPV m hreg hprincipal, ?_⟩
  intro C hC hPC
  letI : Nonempty C := hC
  exact (schemeModuleClosedPointFixedComplement_centeredStalkFieldRanges
    pi P C hPC V hPV m hreg hprincipal).2

/-- Primitive original-K p/q normalization: choose an ACTUAL affine
regular ideal generator internally. Its SAME original irreducible germ
spans the maximal ideal and controls BOTH canonical point-factor stalk
images on EVERY nonempty common complement excluding P. No generator,
rank-one, nongenericity, DVR, image or valuation outcome is a premise. -/
theorem projectiveIntersection_genericNormalization_closedPoint_centeredStalkFieldRanges
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
    ∀ P : closedPoints N,
      let i := N.fromSpecResidueField P.1
      letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
      let M := (show N.Modules from closedImmersionModule i)
      let D := SchemeModuleInternalHom.dual M
      letI := schemeModuleStalkModule M P.1
      letI := schemeModuleStalkModule D P.1
      ∃ (V : N.affineOpens) (hPV : P.1 ∈ V.1) (m : M.val.obj (op V.1)),
        let z : Γ(N, V.1) := (closedImmersionModuleToUnit i).val.app (op V.1) m
        let zP := N.presheaf.germ V.1 P.1 hPV z
        IsRegular z ∧ i.ker.ideal V = Ideal.span ({z} : Set Γ(N, V.1)) ∧
          IsLocalRing.maximalIdeal (N.presheaf.stalk P.1) =
            Ideal.span ({zP} : Set (N.presheaf.stalk P.1)) ∧
          Irreducible zP ∧
          ∀ (C : N.Opens) (hC : Nonempty C) (hPC : P.1 ∉ C),
            letI : Nonempty C := hC
            Set.range (schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi M C
              (schemeModuleClosedPointIdealOverCanonicalIso P C hPC) P.1) =
              Set.range (fun r : N.presheaf.stalk P.1 =>
                @HMul.hMul N.functionField N.functionField N.functionField inferInstance
                  (algebraMap (N.presheaf.stalk P.1) N.functionField r)
                  (algebraMap (N.presheaf.stalk P.1) N.functionField zP)) ∧
            Set.range (schemeModuleFixedFrameStalkToFunctionFieldLinearMap pi D C
              (schemeModuleClosedPointDualOverCanonicalIso P C hPC) P.1) =
              Set.range (fun r : N.presheaf.stalk P.1 =>
                algebraMap (N.presheaf.stalk P.1) N.functionField r /
                  algebraMap (N.presheaf.stalk P.1) N.functionField zP) := by
  dsimp only
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let pi := nu ≫ toBase I
  intro P
  exact centeredStalkFieldRanges_of_regularGenerator pi P
    (projectiveIntersection_genericNormalization_closedPoint_ideal_affine_regularGenerator
      p q hp hp0 n hn hq hnot P)

end PfaffianDescent.Coray
