import PfaffianDescent.IntrinsicFullQuadraticBaseDimensionInfinite

/-! In the finite branch the FULL quadratic base scheme is the original
length-eight subscheme itself, including its nonreduced structure. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory MvPolynomial
open AllCharacteristics.HomogeneousProjective
universe u
attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false in
theorem intrinsicFullQuadraticBase_originalLift_isIso
    {K : Type u} [Field K] [Infinite K] {Z : Scheme.{u}}
    (i : Z ⟶ Proj (homogeneousSubmodule (Fin 4) K))
    [IsClosedImmersion i] [IsFinite (i ≫ ambientToBase)]
    (hZ : AllCharacteristics.finiteSchemeRank (i ≫ ambientToBase) = 8)
    [IsFinite (toBase (intrinsicFullQuadraticBaseIdeal i))] :
    IsIso (IsClosedImmersion.lift (quotientProjMap (intrinsicFullQuadraticBaseIdeal i))
      i (intrinsicFullQuadraticBaseIdeal_ker_le i)) := by
  obtain ⟨q, hfinite, k, hk, hfac, _⟩ :=
    intrinsicFullQuadraticSystem_exists_finite_triple_iso i hZ
  letI := hk
  let T := intrinsicFullQuadraticTripleIdeal i q
  let B := intrinsicFullQuadraticBaseIdeal i
  have hTB : T.toIdeal ≤ B.toIdeal := by
    apply Ideal.span_le.mpr
    intro p hp
    rcases hp with rfl | rfl | rfl
    · exact Ideal.subset_span (q 0).property
    · exact Ideal.subset_span (q 1).property
    · exact Ideal.subset_span (q 2).property
  let r := schemeQuotientMap T B hTB
  let l := IsClosedImmersion.lift (quotientProjMap B) i
    (intrinsicFullQuadraticBaseIdeal_ker_le i)
  have hl : l ≫ quotientProjMap B = i := IsClosedImmersion.lift_fac _ _ _
  have hr : r ≫ quotientProjMap T = quotientProjMap B :=
    schemeQuotientMap_comp_quotientProjMap T B hTB
  have hcomp : l ≫ r = k := by
    apply (cancel_mono (quotientProjMap T)).mp
    rw [Category.assoc, hr, hl, hfac]
  letI : IsClosedImmersion r := schemeQuotientMap_closedImmersion T B hTB
  letI : Mono r := inferInstance
  have hleft : l ≫ (r ≫ inv k) = 𝟙 _ := by
    rw [← Category.assoc, hcomp, IsIso.hom_inv_id]
  have hright : (r ≫ inv k) ≫ l = 𝟙 _ := by
    apply (cancel_mono r).mp
    simp only [Category.assoc, Category.id_comp]
    rw [hcomp, IsIso.inv_hom_id, Category.comp_id]
  exact ⟨⟨r ≫ inv k, hleft, hright⟩⟩

end PfaffianDescent
