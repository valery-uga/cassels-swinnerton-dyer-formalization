import PfaffianDescent.ProjectiveClosedPointCoordinates
import AllCharacteristics.ClosedPointAlgebra
import AllCharacteristics.ProjectiveBaseChange

noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial Module
open AllCharacteristics AllCharacteristics.HomogeneousProjective
universe u
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Recover the canonical residue homomorphism on a PRESCRIBED chart, with
surjectivity and the exact original-K action. No chart is reselected. -/
theorem closedProjectivePoint_fixedChart_canonicalResidueHom001
    (I : HomogeneousIdeal (homogeneousSubmodule (Fin 4) K))
    (A : closedPoints (scheme I)) (j : Fin 4)
    (hA : A.1 ∈ (chartι I j).opensRange) :
    letI := pointAlgebra (toBase I) A.1
    ∃ g : ChartRing I j →+* (scheme I).residueField A.1,
      Function.Surjective g ∧ g.comp (chartBaseMap I j) =
        algebraMap K ((scheme I).residueField A.1) ∧
      Spec.map (CommRingCat.ofHom g) ≫ chartι I j =
        (scheme I).fromSpecResidueField A.1 := by
  classical
  letI := pointAlgebra (toBase I) A.1
  let L := (scheme I).residueField A.1
  let q := (scheme I).fromSpecResidueField A.1
  letI : IsClosedImmersion q := isClosed_singleton_iff_isClosedImmersion.mp A.2
  have hq : q ≫ toBase I = Spec.map (CommRingCat.ofHom (algebraMap K L)) :=
    (pointAlgebra_spec (toBase I) A.1).symm
  have hrange : Set.range q ⊆ Set.range (chartι I j) := by
    rintro _ ⟨b, rfl⟩
    have hb : q b = A.1 := Scheme.fromSpecResidueField_apply A.1 b
    rw [hb]
    exact hA
  let qU := IsOpenImmersion.lift (chartι I j) q hrange
  have hU : qU ≫ chartι I j = q := IsOpenImmersion.lift_fac _ _ _
  letI : IsClosedImmersion (qU ≫ chartι I j) := hU.symm ▸ inferInstance
  letI : IsClosedImmersion qU := IsClosedImmersion.of_comp qU (chartι I j)
  let g := Spec.preimage qU
  have hg : Spec.map g = qU := Spec.map_preimage qU
  refine ⟨g.hom, AllCharacteristics.spec_preimage_surjective_of_closedImmersion qU, ?_, ?_⟩
  · have he : CommRingCat.ofHom (chartBaseMap I j) ≫ g =
        CommRingCat.ofHom (algebraMap K L) := by
      apply Spec.map_injective
      rw [Spec.map_comp, hg, ← chartι_toBase, ← Category.assoc, hU, hq]
    exact congrArg CommRingCat.Hom.hom he
  · exact (congrArg (· ≫ chartι I j) hg).trans hU

end PfaffianDescent.Coray
