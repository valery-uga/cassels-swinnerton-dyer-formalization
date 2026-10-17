import PfaffianDescent.FiniteClosedImmersionRank
import PfaffianDescent.FourTangentDualCoordinates
import AllCharacteristics.FiniteFlatCycle
import Mathlib.AlgebraicGeometry.Limits

/-! SOURCE ONLY, UNVERIFIED. Restrict an actual closed component to a clopen
factor of the real product-dual algebra. Equal finite rank proves the factor
map is an isomorphism; no source isomorphism is an input. -/
noncomputable section
namespace PfaffianDescent
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Module
universe u
variable {K : Type u} [Field K]

def actualProductDualFactor (r : Fin 4) :
    Spec (.of (DualNumber K)) ⟶ Spec (.of (QuarticNet.FourTangentDualAlgebra K)) :=
  Spec.map (CommRingCat.ofHom (Pi.evalRingHom (fun _ : Fin 4 => DualNumber K) r))

def actualProductDualToBase :
    Spec (.of (QuarticNet.FourTangentDualAlgebra K)) ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (QuarticNet.FourTangentDualAlgebra K)))

def actualDualToBase : Spec (.of (DualNumber K)) ⟶ Spec (.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (DualNumber K)))

instance (r : Fin 4) : IsOpenImmersion (actualProductDualFactor (K := K) r) := by
  unfold actualProductDualFactor
  infer_instance

instance (r : Fin 4) : IsClosedImmersion (actualProductDualFactor (K := K) r) := by
  unfold actualProductDualFactor
  exact IsClosedImmersion.spec_of_surjective _ (Function.surjective_eval _)

instance : IsFinite (actualProductDualToBase (K := K)) := by
  unfold actualProductDualToBase
  exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

instance : IsFinite (actualDualToBase (K := K)) := by
  letI : Module.Finite K (DualNumber K) := QuarticNet.dualNumber_moduleFinite (k := K) (L := K)
  unfold actualDualToBase
  exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

theorem actualProductDualFactor_toBase (r : Fin 4) :
    actualProductDualFactor (K := K) r ≫ actualProductDualToBase = actualDualToBase := by
  unfold actualProductDualFactor actualProductDualToBase actualDualToBase
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  rfl

theorem actualDualToBase_rank_two :
    AllCharacteristics.finiteSchemeRank (actualDualToBase (K := K)) = 2 := by
  letI : Module.Finite K (DualNumber K) := QuarticNet.dualNumber_moduleFinite (k := K) (L := K)
  rw [AllCharacteristics.finiteSchemeRank_eq_finrank]
  unfold actualDualToBase
  rw [Scheme.Hom.finrank_SpecMap_algebraMap]
  have h := congrFun (Module.rankAtStalk_eq_finrank_of_free (R := K) (M := DualNumber K))
    (IsLocalRing.closedPoint K)
  rw [h]
  change Module.finrank K (K × K) = 2
  simp [Module.finrank_prod]

theorem actualProductDual_closed_rankTwo_factor_iso
    {Y : Scheme.{u}}
    (j : Y ⟶ Spec (.of (QuarticNet.FourTangentDualAlgebra K))) [IsClosedImmersion j]
    (r : Fin 4)
    (hRange : Set.range j ⊆ Set.range (actualProductDualFactor (K := K) r))
    (hRank : AllCharacteristics.finiteSchemeRank (j ≫ actualProductDualToBase) = 2) :
    ∃ e : Y ≅ Spec (.of (DualNumber K)),
      e.hom ≫ actualProductDualFactor r = j := by
  let lift := IsOpenImmersion.lift (actualProductDualFactor (K := K) r) j hRange
  have hfac : lift ≫ actualProductDualFactor r = j := IsOpenImmersion.lift_fac _ _ _
  letI : IsClosedImmersion (lift ≫ actualProductDualFactor r) := hfac.symm ▸ inferInstance
  letI : IsClosedImmersion lift :=
    IsClosedImmersion.of_comp_isClosedImmersion lift (actualProductDualFactor r)
  have hBase : lift ≫ actualDualToBase = j ≫ actualProductDualToBase := by
    rw [← actualProductDualFactor_toBase r, ← Category.assoc, hfac]
  have hLiftRank : AllCharacteristics.finiteSchemeRank (lift ≫ actualDualToBase) = 2 := by
    simpa only [hBase] using hRank
  letI : IsIso lift := isIso_of_finite_closedImmersion_of_finiteSchemeRank_eq
    lift actualDualToBase (hLiftRank.trans actualDualToBase_rank_two.symm)
  exact ⟨asIso lift, hfac⟩

end PfaffianDescent
