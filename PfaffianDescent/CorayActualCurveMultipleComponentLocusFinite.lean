import PfaffianDescent.CorayNativeCurveComponentMultipleLocusFinite
import PfaffianDescent.CorayHomogeneousPrimeComponentGeometry
import PfaffianDescent.CorayHomogeneousProjectiveComponentBijection

/-! Actual homogeneous selected cubic/q curve: ALL component immersions and
all curve/Noetherian inputs are constructed from the literal equations. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory TopologicalSpace
open AllCharacteristics AllCharacteristics.HomogeneousProjective
open MvPolynomial
universe u
set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The native multiple-component locus of SAME J inside the actual smooth
cubic/q intersection is closed and finite. The whole J may be nonreduced;
no component list, intersection finiteness or desired support is supplied. -/
theorem selectedCubicCurve_actualMultipleComponentLocus_finite001
    {E : Type u} [Field E]
    (p q : MvPolynomial (Fin 4) E) (hp : p.IsHomogeneous 3) (hp0 : p ≠ 0)
    [Smooth (hypersurfaceToBase p hp)] (n : ℕ) (hq : q.IsHomogeneous n)
    (hnot : q ∉ Ideal.span ({p} : Set (MvPolynomial (Fin 4) E)))
    (J : HomogeneousIdeal (homogeneousSubmodule (Fin 4) E))
    (hIJ : (projectiveIntersectionIdeal p q hp hq).toIdeal ≤ J.toIdeal) :
    let e := homogeneousRelevantMinimalPrimesEquivProjectiveComponents J
    let D := fun z : irreducibleComponents (scheme J) => e.symm z
    let j := fun z : irreducibleComponents (scheme J) =>
      schemeQuotientMap J (D z).1 (D z).2.1.le
    let S := fun z => j z ⁻¹' (⋃ w, ⋃ (_ : w ≠ z), Set.range (j w))
    let Bad := ⋃ z, j z '' S z
    IsClosed Bad ∧ Bad.Finite ∧
      ∀ x ∉ Bad, ∃! z : irreducibleComponents (scheme J), x ∈ z.1 := by
  let e := homogeneousRelevantMinimalPrimesEquivProjectiveComponents J
  let D := fun z : irreducibleComponents (scheme J) => e.symm z
  let X := fun z : irreducibleComponents (scheme J) => scheme (D z).1
  let j := fun z : irreducibleComponents (scheme J) =>
    schemeQuotientMap J (D z).1 (D z).2.1.le
  letI : IsLocallyNoetherian (scheme J) :=
    LocallyOfFiniteType.isLocallyNoetherian (toBase J)
  letI : CompactSpace (scheme J) := QuasiCompact.compactSpace_of_compactSpace (toBase J)
  letI : IsNoetherian (scheme J) := ⟨⟩
  letI : Finite (irreducibleComponents (scheme J)) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  letI (z : irreducibleComponents (scheme J)) : IsIntegral (X z) :=
    (homogeneousMinimalPrime_projective_reducedComponent J (D z).1
      (D z).2.1 (D z).2.2).2.1
  letI (z : irreducibleComponents (scheme J)) : IsLocallyNoetherian (X z) :=
    LocallyOfFiniteType.isLocallyNoetherian (toBase (D z).1)
  letI (z : irreducibleComponents (scheme J)) : CompactSpace (X z) :=
    QuasiCompact.compactSpace_of_compactSpace (toBase (D z).1)
  letI (z : irreducibleComponents (scheme J)) : IsNoetherian (X z) := ⟨⟩
  have hClosed (z : irreducibleComponents (scheme J)) : IsClosedImmersion (j z) :=
    schemeQuotientMap_closedImmersion J (D z).1 (D z).2.1.le
  have hRange (z : irreducibleComponents (scheme J)) : z.1 = Set.range (j z) := by
    have h := congrArg Subtype.val (e.apply_symm_apply z)
    exact h.symm
  have hDim (z : irreducibleComponents (scheme J)) (x : X z) :
      Ring.DimensionLEOne ((X z).presheaf.stalk x) := by
    letI : Ring.KrullDimLE 1 ((X z).presheaf.stalk x) :=
      Ring.krullDimLE_iff.mpr
        (selectedProjectiveComponent_original_stalk_ringKrullDim_le_one
          p q hp hp0 n hq hnot (D z).1 (hIJ.trans (D z).2.1.le) x)
    exact ⟨fun {H} hHzero hHprime => hHprime.isMaximal_of_ne_bot hHzero⟩
  exact nativeIntegralCurveComponentCover_multipleLocus_finite001 X j hClosed
    (Equiv.refl _) hRange hDim

end PfaffianDescent.Coray
