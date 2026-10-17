import PfaffianDescent.CorayNormalizationSignedPointTensorWordStalkRange
import PfaffianDescent.CorayNormalizationSignedPointTensorWordClosedPointReconstruction

/-! Actual global pole-condition image of the SAME normalization word.
Actual affine generators are chosen once at all closed points BEFORE any
word or rational function. Original stalk powers and actual global gluing
then characterize the SAME original-pi global field map. No outcome input.
SOURCE ONLY / UNVERIFIED; closed-point reconstruction is still pending. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open AllCharacteristics.HomogeneousProjective IdealSheafDataModule
universe u
variable {K : Type u} [Field K] [CharZero K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- SAME primitive p/q normalization: choose ACTUAL regular affine
point-ideal generators at every closed point ONCE, before all finite
signed words and rational functions. Membership in the ORIGINAL global
word-map image is then EXACTLY membership in each ORIGINAL local-ring
image scaled by the ORIGINAL generator germ to its signed local order.
No generator, comparison, local/global image, cover, finiteness, genus,
constants, effective-divisor or RR conclusion is assumed. -/
theorem projectiveIntersection_genericNormalization_signedPointTensorWord_globalPoleImage
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
    ∃ (V : closedPoints N → N.affineOpens) (hPV : ∀ P, P.1 ∈ (V P).1)
      (m : ∀ P : closedPoints N,
        let i := N.fromSpecResidueField P.1
        letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
        (closedImmersionModule i).val.obj (op (V P).1)),
      (∀ P : closedPoints N,
        let i := N.fromSpecResidueField P.1
        letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
        let z : Γ(N, (V P).1) := (closedImmersionModuleToUnit i).val.app (op (V P).1) (m P)
        let zP := N.presheaf.germ (V P).1 P.1 (hPV P) z
        IsRegular z ∧ i.ker.ideal (V P) = Ideal.span ({z} : Set Γ(N, (V P).1)) ∧ Irreducible zP) ∧
      ∀ (ops : List (closedPoints N × Bool)) (f : N.functionField),
        let hP : ∀ operation ∈ ops, operation.1.1 ≠ genericPoint N :=
          fun operation _ => projectiveIntersection_genericNormalization_closedPoint_ne_generic p q hp hq operation.1
        f ∈ Set.range (schemeModuleSignedPointTensorWordToFunctionFieldLinearMap pi ops hP) ↔
          ∀ P : closedPoints N,
            let i := N.fromSpecResidueField P.1
            letI : IsClosedImmersion i := isClosed_singleton_iff_isClosedImmersion.mp P.2
            let zP := N.presheaf.germ (V P).1 P.1 (hPV P)
              ((closedImmersionModuleToUnit i).val.app (op (V P).1) (m P))
            f ∈ Set.range (fun r : N.presheaf.stalk P.1 =>
              @HMul.hMul N.functionField N.functionField N.functionField inferInstance
                (algebraMap (N.presheaf.stalk P.1) N.functionField r)
                ((algebraMap (N.presheaf.stalk P.1) N.functionField zP) ^
                  schemeSignedPointTensorWordLocalOrder P ops)) := by
  classical
  dsimp only
  let I := projectiveIntersectionIdeal p q hp hq
  let X := scheme I
  letI : QuasiCompact (X.fromSpecStalk (genericPoint X)) := integralGenericPointMap_quasiCompact X
  let N := (X.fromSpecStalk (genericPoint X)).normalization
  let nu := (X.fromSpecStalk (genericPoint X)).fromNormalization
  let pi := nu ≫ toBase I
  have hlocal := projectiveIntersection_genericNormalization_signedPointTensorWord_stalkRange
    p q hp hp0 n hn hq hnot
  dsimp only at hlocal
  choose V hPV m hreg hprincipal hirred hword using hlocal
  refine ⟨V, hPV, m, ?_, ?_⟩
  · intro P
    exact ⟨hreg P, hprincipal P, hirred P⟩
  · intro ops f
    let hP : ∀ operation ∈ ops, operation.1.1 ≠ genericPoint N :=
      fun operation _ => projectiveIntersection_genericNormalization_closedPoint_ne_generic p q hp hq operation.1
    let C := schemeSignedPointTensorWordComplementOpen ops
    letI : Nonempty C := ⟨⟨genericPoint N,
      schemeSignedPointTensorWordComplementOpen_generic_mem ops hP⟩⟩
    let O := (show N.Modules from SheafOfModules.unit N.ringCatSheaf)
    let W := schemeModuleIteratedSignedClosedPointTensor O ops
    apply (projectiveIntersection_genericNormalization_signedPointTensorWord_globalRange_iff_closedPointStalkRange
      p q hp hp0 n hn hq hnot ops f).trans
    apply forall_congr'
    intro P
    letI := schemeModuleStalkModule W P.1
    exact (congrArg (fun S : Set N.functionField => f ∈ S) (hword P ops).2).to_iff

end PfaffianDescent.Coray
