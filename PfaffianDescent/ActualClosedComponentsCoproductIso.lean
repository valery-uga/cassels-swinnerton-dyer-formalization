import PfaffianDescent.ProductDualClosedRankTwoFactorIso
import PfaffianDescent.ActualComponentEpsilonCoproductSquare
import AllCharacteristics.DisjointClosedUnion

/-! SOURCE ONLY, UNVERIFIED. Internal final assembly. Once the preceding
factory has constructed the SAME component isos over K, the actual closed
components/rank-eight map makes their coproduct the SAME original whole Q.
This base compatibility is derived from the preceding actual factor squares
when applied; it is not a paper-facing desired comparison certificate. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
universe u
variable {K : Type u} [Field K]

theorem actual_closed_components_canonicalCoproduct_isIso
    {Q : Scheme.{u}} (t : Q ⟶ Spec (.of K)) [IsFinite t]
    (Y : Fin 4 → Scheme.{u}) (c : ∀ r, Y r ⟶ Q) [∀ r, IsClosedImmersion (c r)]
    (hDisjoint : Pairwise fun r s => Disjoint (Set.range (c r)) (Set.range (c s)))
    (canonicalE : ∀ r, Y r ≅ Spec (.of (DualNumber K)))
    (hBase : ∀ r, (canonicalE r).hom ≫ actualDualToBase = c r ≫ t)
    (hWhole : AllCharacteristics.finiteSchemeRank t = 8) :
    IsIso (Sigma.desc c) := by
  let d := Sigma.desc c
  letI : IsClosedImmersion d := AllCharacteristics.isClosedImmersion_sigmaDesc_of_disjoint c hDisjoint
  let e := actualComponentProductDualIso Y canonicalE
  have hSourceBase : e.hom ≫ actualProductDualToBase = d ≫ t := by
    apply Sigma.hom_ext
    intro r
    rw [← Category.assoc, actualComponentProductDualIso_component]
    change (canonicalE r).hom ≫ actualProductDualFactor r ≫ actualProductDualToBase = _
    rw [actualProductDualFactor_toBase, hBase r]
    simp only [d, Category.assoc, Sigma.ι_desc_assoc]
  have hSource : AllCharacteristics.finiteSchemeRank (d ≫ t) = 8 := by
    rw [AllCharacteristics.finiteSchemeRank_eq_finrank, ← hSourceBase,
      Scheme.Hom.finrank_comp_left_of_isIso]
    unfold actualProductDualToBase
    rw [Scheme.Hom.finrank_SpecMap_algebraMap]
    have h := congrFun (Module.rankAtStalk_eq_finrank_of_free
      (R := K) (M := QuarticNet.FourTangentDualAlgebra K)) (IsLocalRing.closedPoint K)
    rw [h]
    exact QuarticNet.fourTangentDualAlgebra_finrank
  exact isIso_of_finite_closedImmersion_of_finiteSchemeRank_eq d t (hSource.trans hWhole.symm)

end PfaffianDescent
