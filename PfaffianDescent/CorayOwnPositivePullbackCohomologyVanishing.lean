import PfaffianDescent.CorayActualPositiveIdealTwistCohomologyVanishing
import PfaffianDescent.CorayCartierCanonicalProjectionFormula
import PfaffianDescent.ClosedImmersionCohomologyOneLinearInjection

/-! Intrinsic eventual H1 of the OWN actual pulled-back positive coefficient.
Canonical projection is derived, never assumed. Its pending producer is
explicit in the manifest. No exact-pullback claim or H0=K hypothesis.
SOURCE ONLY UNVERIFIED. -/
noncomputable section
namespace PfaffianDescent.Coray
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open ProjectiveNegativeTwist AllCharacteristics.HomogeneousProjective
open BundleSectionZeroLocus IdealSheafDataModule
universe u
set_option backward.isDefEq.respectTransparency false
variable {K : Type u} [Field K]
attribute [local instance] MvPolynomial.gradedAlgebra
local notation "PS" => homogeneousSubmodule (Fin 4) K

private theorem actualP3PositiveTwist_locallyRankOne
    (m : ℕ) (hm : 0 < m) :
    schemeModuleLocallyRankOne (positiveSheafOfModules PS m) := by
  intro x
  have hx : x ∈ (⨆ i : P3CoordinateIndex.{u}, p3StandardOpenLifted (K := K) i) := by
    rw [p3StandardOpenLifted_iSup K]
    trivial
  obtain ⟨i, hix⟩ := _root_.TopologicalSpace.Opens.mem_iSup.mp hx
  let U : (Proj PS).Opens := p3StandardOpenLifted (K := K) i
  let T : (Proj PS).Modules := positiveSheafOfModules PS m
  let O : (Proj PS).Modules := SheafOfModules.unit (Proj PS).ringCatSheaf
  let eT := overFunctorIsoUnit_of_restrictIsoUnit.{u}
    (X := Proj PS) (T := T) (p3StandardOpen (K := K) i.down)
    (p3PositiveTwistStandardOpenIsoUnit K i.down m hm)
  let eO := PfaffianDescent.SheafOfModules.overFunctor_globalUnitIso U (Iso.refl O)
  exact ⟨U, hix, ⟨eT ≪≫ eO.symm⟩⟩

/-- Eventual intrinsic H1 vanishing for the OWN actual restriction i^*O(m),
with i the original quotientProjMap I. The canonical projection formula and
closed-immersion H1 injection are derived from actual rank-one charts and
native exact pushforward. Original K actions come independently from the
ambient base and i followed by that base. No H0=K, finite H1 or desired
projection/cohomology certificate is supplied. -/
theorem homogeneousIdeal_eventually_ownPositivePullback_cohomology_one_subsingleton
    [hExtP : HasExt.{u} (Proj PS).Modules]
    (I : HomogeneousIdeal PS) [hExtC : HasExt.{u} (scheme I).Modules] :
    ∃ B : ℕ, ∀ m : ℕ, B ≤ m →
      Subsingleton (schemeModuleCohomology (scheme I)
        ((Scheme.Modules.pullback (quotientProjMap I)).obj
          (positiveSheafOfModules PS m)) 1) := by
  let P := Proj PS
  let C := scheme I
  let i := quotientProjMap I
  let pi := ambientToBase (R := K) (σ := Fin 4)
  letI : HasExt.{u} (SheafOfModules.{u} P.ringCatSheaf) := hExtP
  letI : HasExt.{u} (SheafOfModules.{u} C.ringCatSheaf) := hExtC
  letI : Linear K P.Modules := schemeModulesLinearOver pi
  letI : Linear K C.Modules := schemeModulesLinearOver (i ≫ pi)
  obtain ⟨B, hB⟩ :=
    homogeneousIdeal_eventually_actualTwistedQuotient_cohomology_one_subsingleton I
  refine ⟨max B 1, fun m hm => ?_⟩
  have hmB : B ≤ m := (Nat.le_max_left B 1).trans hm
  have hmpos : 0 < m := (Nat.lt_add_one 0).trans_le ((Nat.le_max_right B 1).trans hm)
  let T := positiveSheafOfModules PS m
  let M := (Scheme.Modules.pullback i).obj T
  let S := closedImmersionIdealTwistSequence i T
  letI : Subsingleton (schemeModuleCohomology P S.X₃ 1) := hB m hmB
  letI : IsIso (schemeModuleCanonicalFiberProjection i T) :=
    schemeModuleCanonicalFiberProjection_isIso_of_locallyRankOne i T
      (actualP3PositiveTwist_locallyRankOne m hmpos)
  let e : S.X₃ ≅ (Scheme.Modules.pushforward i).obj M :=
    @asIso _ _ _ _ (schemeModuleCanonicalFiberProjection i T)
      (schemeModuleCanonicalFiberProjection_isIso_of_locallyRankOne i T
        (actualP3PositiveTwist_locallyRankOne m hmpos))
  letI : Subsingleton (schemeModuleCohomology P ((Scheme.Modules.pushforward i).obj M) 1) :=
    schemeModuleCohomology_subsingleton_of_iso P e 1
  exact (closedImmersion_cohomologyOneLinearMap_injective pi i M).subsingleton

end PfaffianDescent.Coray
